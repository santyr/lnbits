import asyncio
import base64
import json
import os
import ssl
import uuid
from collections.abc import AsyncGenerator
from hashlib import sha256
from typing import Any
from urllib.parse import urlparse

import httpx
from bolt11 import Bolt11Exception
from bolt11.decode import decode
from loguru import logger

from lnbits.exceptions import UnsupportedError
from lnbits.helpers import normalize_endpoint
from lnbits.settings import settings
from lnbits.utils.crypto import random_secret_and_hash, verify_preimage

from .base import (
    InvoiceResponse,
    PaymentFailedStatus,
    PaymentPendingStatus,
    PaymentResponse,
    PaymentStatus,
    PaymentSuccessStatus,
    StatusResponse,
    Wallet,
)


class CLNRestWallet(Wallet):
    """
    Core Lightning REST wallet backend.

    This implementation intentionally stays close to the upstream LNbits
    CLNRestWallet while addressing:

    - Core Lightning msat response compatibility
    - description-hash invoices
    - preimage verification
    - correct waitanyinvoice semantics
    - listener bootstrap to prevent historical payment replay
    - payment reconciliation/idempotency
    - ambiguous "already paid" responses
    - improved CLN REST error reporting
    - safer TLS handling
    - current Core Lightning pay/renepay behavior

    LNbits internal payments are handled by LNbits core before pay_invoice()
    reaches the funding source. Payment reconciliation here is therefore for
    backend idempotency, retries, same-node payments created outside LNbits,
    and ambiguous Core Lightning responses.
    """

    def __init__(self):
        super().__init__()

        if not settings.clnrest_url:
            raise ValueError("Cannot initialize CLNRestWallet: missing CLNREST_URL")

        if not settings.clnrest_readonly_rune:
            raise ValueError(
                "Cannot initialize CLNRestWallet: missing CLNREST_READONLY_RUNE"
            )

        self.url = normalize_endpoint(settings.clnrest_url)

        if not settings.clnrest_nodeid:
            logger.info(
                "missing CLNREST_NODEID, but this is only needed for CLN v23.08"
            )

        self.base_headers = {
            "accept": "application/json",
            "User-Agent": settings.user_agent,
            "Content-Type": "application/json",
        }

        if settings.clnrest_nodeid is not None:
            self.base_headers["nodeid"] = settings.clnrest_nodeid

        self.readonly_headers = {
            **self.base_headers,
            "rune": settings.clnrest_readonly_rune,
        }

        self.invoice_headers = (
            {
                **self.base_headers,
                "rune": settings.clnrest_invoice_rune,
            }
            if settings.clnrest_invoice_rune
            else None
        )

        self.pay_headers = (
            {
                **self.base_headers,
                "rune": settings.clnrest_pay_rune,
            }
            if settings.clnrest_pay_rune
            else None
        )

        self.renepay_headers = (
            {
                **self.base_headers,
                "rune": settings.clnrest_renepay_rune,
            }
            if settings.clnrest_renepay_rune
            else None
        )

        if not self.invoice_headers:
            logger.warning(
                "Will be unable to create invoices without "
                "setting CLNREST_INVOICE_RUNE"
            )

        if not self.pay_headers:
            logger.warning(
                "CLNREST_PAY_RUNE is not configured. "
                "Will use renepay only if CLNREST_RENEPAY_RUNE is configured."
            )

        if self.renepay_headers:
            logger.warning(
                "CLNREST_RENEPAY_RUNE is configured. Core Lightning renepay "
                "is deprecated; pay will be preferred when available."
            )

        # Core Lightning pay errors that are known to be terminal.
        #
        # NOTE:
        # 201 ("Already paid") is deliberately NOT included.
        # That result is ambiguous from LNbits' perspective and must be
        # reconciled against listpays before deciding success/failure.
        self.pay_failure_error_codes = {
            -32602,  # invalid parameters / invalid bolt11
            203,     # permanent failure at destination
            205,     # unable to find route
            206,     # route too expensive
            207,     # invoice expired
            210,     # timed out without payment in progress
            401,     # authentication/rune failure
        }

        self.client = self._create_client()

        # A non-zero operator-provided value is treated as an explicit cursor.
        # If unset/zero, paid_invoices_stream() bootstraps to the highest
        # currently paid pay_index so historical invoices are not replayed.
        self.last_pay_index = int(settings.clnrest_last_pay_index or 0)
        self._listener_bootstrapped = False

    async def cleanup(self):
        try:
            await self.client.aclose()
        except RuntimeError as exc:
            logger.warning(f"Error closing wallet connection: {exc}")

    async def status(self) -> StatusResponse:
        try:
            logger.debug("REQUEST to /v1/listfunds")

            data = await self._rpc(
                "listfunds",
                headers=self.readonly_headers,
                timeout=15.0,
            )

            channels = data.get("channels", [])

            total_our_amount_msat = sum(
                _msat_to_int(channel.get("our_amount_msat"))
                for channel in channels
            )

            return StatusResponse(None, total_our_amount_msat)

        except httpx.ConnectTimeout as exc:
            logger.warning(f"CLN REST connect timeout: {exc}")
            return StatusResponse("Timed out connecting to CLN REST", 0)

        except httpx.ReadTimeout as exc:
            logger.warning(f"CLN REST read timeout: {exc}")
            return StatusResponse("CLN REST did not answer in time", 0)

        except httpx.ConnectError as exc:
            logger.warning(f"CLN REST connect error: {exc}")
            return StatusResponse("Cannot connect to CLN REST listener", 0)

        except httpx.HTTPStatusError as exc:
            error_message = self._format_http_error(exc)
            logger.warning(error_message)
            return StatusResponse(error_message, 0)

        except json.JSONDecodeError as exc:
            logger.warning(f"JSON decode error: {exc!s}")
            return StatusResponse(
                f"Failed to decode JSON response from {self.url}",
                0,
            )

        except Exception as exc:
            logger.warning(f"CLN REST status error: {exc}")
            return StatusResponse(
                f"Unable to connect to {self.url}: {exc}",
                0,
            )

    async def create_invoice(
        self,
        amount: int,
        memo: str | None = None,
        description_hash: bytes | None = None,
        unhashed_description: bytes | None = None,
        **kwargs,
    ) -> InvoiceResponse:
        if not self.invoice_headers:
            return InvoiceResponse(
                ok=False,
                error_message="Unable to invoice without an invoice rune",
            )

        if amount <= 0:
            return InvoiceResponse(
                ok=False,
                error_message="Invoice amount must be greater than zero",
            )

        if description_hash and not unhashed_description:
            raise UnsupportedError(
                "'description_hash' requires 'unhashed_description' "
                "for Core Lightning"
            )

        if kwargs.get("preimage"):
            preimage = str(kwargs["preimage"])
        else:
            preimage, _ = random_secret_and_hash()

        data: dict[str, Any] = {
            "amount_msat": int(amount * 1000),
            "label": _generate_label(),
            "preimage": preimage,
        }

        if unhashed_description:
            try:
                description = unhashed_description.decode("utf-8")
            except UnicodeDecodeError:
                return InvoiceResponse(
                    ok=False,
                    error_message="unhashed_description must contain valid UTF-8",
                )

            if description_hash:
                calculated_description_hash = sha256(
                    unhashed_description
                ).digest()

                if calculated_description_hash != description_hash:
                    logger.warning(
                        "description_hash does not match unhashed_description"
                    )
                    return InvoiceResponse(
                        ok=False,
                        error_message=(
                            "description_hash does not match "
                            "unhashed_description"
                        ),
                    )

            data["description"] = description
            data["deschashonly"] = True
        else:
            data["description"] = memo or ""

        if kwargs.get("expiry") is not None:
            data["expiry"] = int(kwargs["expiry"])

        try:
            response_data = await self._rpc(
                "invoice",
                payload=data,
                headers=self.invoice_headers,
            )

            payment_hash = response_data.get("payment_hash")
            bolt11 = response_data.get("bolt11")

            if not payment_hash or not bolt11:
                logger.warning(
                    "CLN invoice response missing payment_hash or bolt11"
                )
                return InvoiceResponse(
                    ok=False,
                    error_message="Server error: missing required invoice fields",
                )

            if not _preimage_matches(preimage, payment_hash):
                logger.error(
                    "CLN invoice response payment_hash does not match "
                    "the requested preimage"
                )
                return InvoiceResponse(
                    ok=False,
                    error_message=(
                        "Server error: invoice preimage does not match "
                        "payment_hash"
                    ),
                )

            return InvoiceResponse(
                ok=True,
                checking_id=payment_hash,
                payment_request=bolt11,
                preimage=preimage,
            )

        except httpx.HTTPStatusError as exc:
            error_message = self._format_http_error(exc)
            logger.warning(f"Error creating invoice: {error_message}")

            return InvoiceResponse(
                ok=False,
                error_message=error_message,
            )

        except json.JSONDecodeError as exc:
            logger.warning(f"Invalid invoice JSON response: {exc}")

            return InvoiceResponse(
                ok=False,
                error_message="Server error: invalid JSON response",
            )

        except Exception as exc:
            logger.warning(f"Error creating invoice: {exc}")

            return InvoiceResponse(
                ok=False,
                error_message=str(exc),
            )

    async def pay_invoice(
        self,
        bolt11: str,
        fee_limit_msat: int,
        **_,
    ) -> PaymentResponse:
        try:
            invoice = decode(bolt11)
        except Bolt11Exception as exc:
            return PaymentResponse(
                ok=False,
                error_message=str(exc),
            )

        if not invoice.amount_msat or invoice.amount_msat <= 0:
            return PaymentResponse(
                ok=False,
                error_message="0 amount invoices are not allowed",
            )

        payment_hash = invoice.payment_hash

        if not self.pay_headers and not self.renepay_headers:
            return PaymentResponse(
                ok=False,
                checking_id=payment_hash,
                error_message=(
                    "Unable to pay invoice without a pay or renepay rune"
                ),
            )

        # Reconcile before dispatching a payment.
        #
        # This is not LNbits internal-payment handling. LNbits core detects
        # those before this method is called.
        #
        # This protects against retries, server restarts, duplicate requests,
        # and an earlier payment whose response was lost.
        try:
            found, existing_status = await self._get_listpays_status(
                payment_hash
            )

            if found and existing_status.success:
                return PaymentResponse(
                    ok=True,
                    checking_id=payment_hash,
                    fee_msat=existing_status.fee_msat,
                    preimage=existing_status.preimage,
                )

            if found and existing_status.paid is None:
                return PaymentResponse(
                    ok=None,
                    checking_id=payment_hash,
                    fee_msat=existing_status.fee_msat,
                    preimage=existing_status.preimage,
                )

            # A previous failed attempt does not prevent CLN from retrying.
        except Exception as exc:
            logger.debug(
                f"Could not preflight listpays for {payment_hash}: {exc}"
            )

        label = _generate_label()

        # Prefer pay. Keep renepay for installations that only configured
        # a renepay rune.
        if self.pay_headers:
            method = "pay"
            headers = self.pay_headers

            data: dict[str, Any] = {
                "bolt11": bolt11,
                "label": label,
                "maxfee": int(fee_limit_msat),
            }

            if invoice.description:
                data["description"] = invoice.description

        else:
            method = "renepay"
            headers = self.renepay_headers

            data = {
                "invstring": bolt11,
                "label": label,
                "maxfee": int(fee_limit_msat),
            }

            if invoice.description:
                data["description"] = invoice.description

        try:
            response_data = await self._rpc(
                method,
                payload=data,
                headers=headers,
                timeout=None,
            )

            response_hash = (
                response_data.get("payment_hash") or payment_hash
            )
            status = response_data.get("status")
            preimage = (
                response_data.get("payment_preimage")
                or response_data.get("preimage")
            )

            fee_msat = _payment_fee_msat(response_data)

            if status == "complete":
                if not preimage:
                    logger.warning(
                        f"{method} returned complete without a preimage; "
                        "reconciling with listpays"
                    )

                    return await self._reconcile_payment_response(
                        response_hash,
                        fallback_error=(
                            f"{method} returned complete without a preimage"
                        ),
                    )

                if not _preimage_matches(preimage, response_hash):
                    logger.error(
                        f"{method} returned an invalid preimage/payment_hash pair"
                    )

                    return PaymentResponse(
                        ok=None,
                        checking_id=response_hash,
                        error_message=(
                            "Core Lightning returned an invalid payment preimage"
                        ),
                    )

                return PaymentResponse(
                    ok=True,
                    checking_id=response_hash,
                    fee_msat=fee_msat,
                    preimage=preimage,
                )

            if status == "pending":
                return PaymentResponse(
                    ok=None,
                    checking_id=response_hash,
                    fee_msat=fee_msat,
                )

            if status == "failed":
                reconciled = await self._reconcile_payment_response(
                    response_hash,
                    fallback_error=(
                        self._extract_error_message(response_data)
                        or "Payment failed"
                    ),
                )

                if reconciled.success or reconciled.pending:
                    return reconciled

                return PaymentResponse(
                    ok=False,
                    checking_id=response_hash,
                    error_message=(
                        self._extract_error_message(response_data)
                        or "Payment failed"
                    ),
                )

            return await self._reconcile_payment_response(
                response_hash,
                fallback_error=(
                    f"Unexpected Core Lightning payment status: {status!r}"
                ),
            )

        except httpx.HTTPStatusError as exc:
            parsed_error = self._parse_rpc_http_error(exc)

            reconciled = await self._reconcile_payment_response(
                payment_hash,
                fallback_error=parsed_error["message"],
            )

            if reconciled.success or reconciled.pending:
                return reconciled

            if parsed_error["terminal"]:
                return PaymentResponse(
                    ok=False,
                    checking_id=payment_hash,
                    error_message=parsed_error["message"],
                )

            return PaymentResponse(
                ok=None,
                checking_id=payment_hash,
                error_message=parsed_error["message"],
            )

        except Exception as exc:
            logger.warning(
                f"Failed to pay invoice {payment_hash} using {method}: {exc}"
            )

            # A transport failure is ambiguous because lightningd may have
            # accepted the payment before LNbits lost the response.
            return await self._reconcile_payment_response(
                payment_hash,
                fallback_error=str(exc),
            )

    async def get_invoice_status(self, checking_id: str) -> PaymentStatus:
        try:
            data = await self._rpc(
                "listinvoices",
                payload={"payment_hash": checking_id},
                headers=self.readonly_headers,
            )

            invoices = data.get("invoices") or []

            if not invoices:
                logger.debug(
                    f"No CLN invoice found for payment hash {checking_id}"
                )
                return PaymentPendingStatus()

            invoice = invoices[0]
            status = invoice.get("status")

            if status == "paid":
                preimage = (
                    invoice.get("payment_preimage")
                    or invoice.get("preimage")
                )

                if not preimage:
                    logger.error(
                        f"Paid CLN invoice {checking_id} has no preimage"
                    )
                    return PaymentPendingStatus()

                if not _preimage_matches(preimage, checking_id):
                    logger.error(
                        f"Paid CLN invoice {checking_id} returned "
                        "an invalid preimage"
                    )
                    return PaymentPendingStatus()

                fee_msat = (
                    _msat_to_int(invoice.get("amount_received_msat"))
                    - _msat_to_int(invoice.get("amount_msat"))
                )

                return PaymentSuccessStatus(
                    fee_msat=fee_msat,
                    preimage=preimage,
                )

            if status in {"expired", "failed"}:
                return PaymentFailedStatus()

            return PaymentPendingStatus()

        except Exception as exc:
            logger.warning(
                f"Error getting invoice status for {checking_id}: {exc}"
            )
            return PaymentPendingStatus()

    async def get_payment_status(self, checking_id: str) -> PaymentStatus:
        try:
            found, status = await self._get_listpays_status(checking_id)

            if not found:
                return PaymentPendingStatus()

            return status

        except Exception as exc:
            logger.warning(
                f"Error getting payment status for {checking_id}: {exc}"
            )
            return PaymentPendingStatus()

    async def paid_invoices_stream(self) -> AsyncGenerator[str, None]:
        """
        Listen for newly paid invoices without replaying CLN's historical
        invoice database when LNbits starts.

        Startup behavior:
          1. If CLNREST_LAST_PAY_INDEX is explicitly non-zero, use it.
          2. Otherwise find the highest currently paid pay_index.
          3. Start waitanyinvoice from that cursor.
          4. Emit only newer paid invoices.

        LNbits separately reconciles its pending database entries at startup,
        so the event listener does not need to replay CLN's entire history.
        """

        while settings.lnbits_running:
            try:
                if not self._listener_bootstrapped:
                    await self._bootstrap_listener_index()

                invoice = await self._rpc(
                    "waitanyinvoice",
                    payload={
                        "lastpay_index": self.last_pay_index,
                    },
                    headers=self.readonly_headers,
                    timeout=None,
                )

                status = invoice.get("status")

                if status != "paid":
                    continue

                payment_hash = invoice.get("payment_hash")
                pay_index = invoice.get("pay_index")

                if pay_index is None:
                    logger.warning(
                        "waitanyinvoice returned a paid invoice "
                        "without pay_index"
                    )
                    continue

                try:
                    pay_index = int(pay_index)
                except (TypeError, ValueError):
                    logger.warning(
                        "waitanyinvoice returned invalid pay_index: "
                        f"{pay_index!r}"
                    )
                    continue

                # Defensive replay protection.
                if pay_index <= self.last_pay_index:
                    logger.warning(
                        "Ignoring stale CLN invoice event "
                        f"pay_index={pay_index}, "
                        f"last_pay_index={self.last_pay_index}"
                    )
                    continue

                # Advance before yielding so downstream cancellation/error
                # cannot immediately replay this event in the same process.
                self.last_pay_index = pay_index

                if not payment_hash:
                    logger.warning(
                        "waitanyinvoice returned a paid invoice "
                        "without payment_hash"
                    )
                    continue

                preimage = (
                    invoice.get("payment_preimage")
                    or invoice.get("preimage")
                )

                if preimage and not _preimage_matches(
                    preimage,
                    payment_hash,
                ):
                    logger.error(
                        "waitanyinvoice returned invalid preimage "
                        f"for payment_hash={payment_hash}"
                    )
                    continue

                logger.debug(
                    "new paid CLN invoice: "
                    f"payment_hash={payment_hash}, "
                    f"pay_index={self.last_pay_index}"
                )

                yield payment_hash

            except asyncio.CancelledError:
                raise

            except Exception as exc:
                logger.debug(
                    "lost connection to corelightning-rest invoice listener: "
                    f"'{exc}', reconnecting..."
                )

                await asyncio.sleep(1.0)

    async def _bootstrap_listener_index(self) -> None:
        """
        Initialize waitanyinvoice at the current end of CLN's paid-invoice
        history so restarting LNbits does not replay historical payments.

        If CLNREST_LAST_PAY_INDEX is explicitly configured to a non-zero
        value, preserve it and treat it as an operator-specified resume cursor.

        If bootstrap fails, do not silently fall back to zero: doing so would
        replay historical invoices. The listener retries bootstrap instead.
        """

        if self._listener_bootstrapped:
            return

        if self.last_pay_index > 0:
            logger.info(
                "Using configured CLN waitanyinvoice cursor "
                f"pay_index={self.last_pay_index}"
            )
            self._listener_bootstrapped = True
            return

        logger.info(
            "Bootstrapping CLN invoice listener to current pay_index"
        )

        try:
            data = await self._rpc(
                "listinvoices",
                headers=self.readonly_headers,
                timeout=30.0,
            )

            invoices = data.get("invoices") or []
            highest_pay_index = 0

            for invoice in invoices:
                if invoice.get("status") != "paid":
                    continue

                pay_index = invoice.get("pay_index")

                if pay_index is None:
                    continue

                try:
                    normalized_pay_index = int(pay_index)
                except (TypeError, ValueError):
                    logger.warning(
                        "Ignoring invalid CLN invoice pay_index: "
                        f"{pay_index!r}"
                    )
                    continue

                if normalized_pay_index > highest_pay_index:
                    highest_pay_index = normalized_pay_index

            self.last_pay_index = highest_pay_index
            self._listener_bootstrapped = True

            if highest_pay_index > 0:
                logger.info(
                    "CLN invoice listener bootstrapped at "
                    f"pay_index={highest_pay_index}; "
                    "historical paid invoices will not be replayed"
                )
            else:
                logger.info(
                    "No historical paid CLN invoices found; "
                    "starting waitanyinvoice from pay_index=0"
                )

        except asyncio.CancelledError:
            raise

        except Exception as exc:
            # Never mark bootstrap complete here. The calling listener will
            # sleep and retry instead of accidentally starting from zero.
            logger.warning(
                "Unable to bootstrap CLN invoice listener safely: "
                f"{exc}"
            )
            raise

    async def _get_listpays_status(
        self,
        checking_id: str,
    ) -> tuple[bool, PaymentStatus]:
        """
        Return (found, status) for a CLN payment.

        `found` is important: "no payment exists" and "payment exists and is
        pending" must not be treated as the same thing. A missing payment must
        still be dispatched by pay_invoice().
        """

        data = await self._rpc(
            "listpays",
            payload={"payment_hash": checking_id},
            headers=self.readonly_headers,
        )

        pays = data.get("pays") or []

        if not pays:
            return False, PaymentPendingStatus()

        pay = _select_best_pay(pays)
        status = pay.get("status")

        if status == "complete":
            preimage = (
                pay.get("preimage")
                or pay.get("payment_preimage")
            )

            if not preimage:
                logger.error(
                    f"Completed payment {checking_id} has no preimage"
                )
                return True, PaymentPendingStatus()

            if not _preimage_matches(preimage, checking_id):
                logger.error(
                    f"Completed payment {checking_id} has an invalid preimage"
                )
                return True, PaymentPendingStatus()

            return True, PaymentSuccessStatus(
                fee_msat=_payment_fee_msat(pay),
                preimage=preimage,
            )

        if status == "failed":
            return True, PaymentFailedStatus()

        return True, PaymentPendingStatus(
            fee_msat=_payment_fee_msat(pay),
        )

    async def _reconcile_payment_response(
        self,
        payment_hash: str,
        fallback_error: str,
    ) -> PaymentResponse:
        """
        Reconcile an ambiguous payment result through listpays.

        Used after timeouts, HTTP errors, duplicate/already-paid responses,
        and unusual pay responses.

        Only a confirmed complete payment is reported as success.
        """

        try:
            found, status = await self._get_listpays_status(payment_hash)

            if found and status.success:
                return PaymentResponse(
                    ok=True,
                    checking_id=payment_hash,
                    fee_msat=status.fee_msat,
                    preimage=status.preimage,
                )

            if found and status.paid is None:
                return PaymentResponse(
                    ok=None,
                    checking_id=payment_hash,
                    fee_msat=status.fee_msat,
                    preimage=status.preimage,
                    error_message=fallback_error,
                )

            if found and status.failed:
                return PaymentResponse(
                    ok=False,
                    checking_id=payment_hash,
                    error_message=fallback_error,
                )

        except Exception as exc:
            logger.warning(
                f"Could not reconcile payment {payment_hash}: {exc}"
            )

        # If success or terminal failure cannot be proven, preserve pending
        # status so LNbits does not accidentally retry and double-pay.
        return PaymentResponse(
            ok=None,
            checking_id=payment_hash,
            error_message=fallback_error,
        )

    async def _rpc(
        self,
        method: str,
        payload: dict[str, Any] | None = None,
        headers: dict[str, str] | None = None,
        timeout: float | None = 30.0,
    ) -> dict[str, Any]:
        response = await self.client.post(
            f"/v1/{method}",
            json=payload or {},
            headers=headers,
            timeout=timeout,
        )

        parsed_body: Any = None

        try:
            parsed_body = response.json()
        except json.JSONDecodeError:
            pass

        if response.is_error:
            # Preserve the actual CLN response object so callers can inspect
            # the RPC error body instead of seeing only a generic HTTP 500.
            message = (
                self._extract_error_message(parsed_body)
                if isinstance(parsed_body, dict)
                else None
            )

            raise httpx.HTTPStatusError(
                message
                or f"CLN REST returned HTTP {response.status_code}",
                request=response.request,
                response=response,
            )

        if parsed_body is None:
            raise json.JSONDecodeError(
                f"Invalid JSON response from CLN REST {method}",
                response.text,
                0,
            )

        if not isinstance(parsed_body, dict):
            raise ValueError(
                f"Unexpected CLN response type for {method}: "
                f"{type(parsed_body)!r}"
            )

        # Be defensive in case a CLN REST version returns an RPC error body
        # with a successful HTTP status.
        if "error" in parsed_body:
            error_message = (
                self._extract_error_message(parsed_body)
                or f"Core Lightning RPC '{method}' returned an error"
            )
            raise ValueError(error_message)

        if (
            parsed_body.get("code") is not None
            and parsed_body.get("message")
        ):
            raise ValueError(str(parsed_body["message"]))

        return parsed_body

    def _format_http_error(
        self,
        exc: httpx.HTTPStatusError,
    ) -> str:
        message = f"CLN REST HTTP {exc.response.status_code}"

        try:
            data = exc.response.json()

            extracted = self._extract_error_message(data)

            if extracted:
                return f"{message}: {extracted}"

        except Exception:
            pass

        body = exc.response.text.strip()

        if body:
            return f"{message}: {body}"

        return message

    def _parse_rpc_http_error(
        self,
        exc: httpx.HTTPStatusError,
    ) -> dict[str, Any]:
        message = self._format_http_error(exc)
        code: int | None = None

        try:
            data = exc.response.json()

            error = data.get("error")

            if isinstance(error, dict):
                raw_code = error.get("code")
            else:
                raw_code = data.get("code")

            if raw_code is not None:
                code = int(raw_code)

        except Exception:
            pass

        return {
            "message": message,
            "code": code,
            "terminal": code in self.pay_failure_error_codes,
        }

    @staticmethod
    def _extract_error_message(
        data: dict[str, Any] | None,
    ) -> str | None:
        if not data:
            return None

        error = data.get("error")

        if isinstance(error, dict):
            message = error.get("message")

            if message:
                return str(message)

            return str(error)

        if isinstance(error, str):
            return error

        message = data.get("message")

        if message:
            return str(message)

        detail = data.get("detail")

        if detail:
            return str(detail)

        return None

    def _create_client(self) -> httpx.AsyncClient:
        """
        Create the HTTP client and TLS configuration.

        HTTP is permitted only for loopback connections.
        HTTPS verifies against CLNREST_CA. Hostname verification remains
        disabled for compatibility with CLN's locally generated certificates
        and IP/localhost deployments, while certificate-chain verification
        remains enabled.
        """

        parsed_url = urlparse(self.url)

        if parsed_url.scheme == "http":
            if parsed_url.hostname not in (
                "localhost",
                "127.0.0.1",
                "::1",
            ):
                raise ValueError(
                    "Insecure HTTP connections are only allowed for localhost "
                    "or equivalent loopback IP addresses. Set CLNREST_URL to "
                    "https:// for external connections."
                )

            logger.warning(
                "Not using TLS for local CLNRestWallet connection"
            )

            return httpx.AsyncClient(
                base_url=self.url,
            )

        if parsed_url.scheme != "https":
            raise ValueError(
                "CLNREST_URL must start with http:// or https://"
            )

        logger.info(f"Using TLS to connect to {self.url}")

        if not settings.clnrest_ca:
            raise ValueError(
                "CLNREST_CA is required for an HTTPS CLN REST connection"
            )

        ssl_context = ssl.create_default_context(
            ssl.Purpose.SERVER_AUTH
        )

        if os.path.isfile(settings.clnrest_ca):
            logger.info(
                f"Using CLN REST CA file: {settings.clnrest_ca}"
            )

            ssl_context.load_verify_locations(
                cafile=settings.clnrest_ca,
            )

        else:
            logger.info(
                "Using CLN REST CA certificate from configured PEM content"
            )

            ca_content = settings.clnrest_ca.replace("\\n", "\n")

            ssl_context.load_verify_locations(
                cadata=ca_content,
            )

        # Disable hostname matching only. Certificate validation against the
        # configured CA remains active.
        ssl_context.check_hostname = False

        return httpx.AsyncClient(
            base_url=self.url,
            verify=ssl_context,
        )


def _preimage_matches(
    preimage: str,
    payment_hash: str,
) -> bool:
    """
    Verify a preimage using LNbits' shared crypto helper.

    Invalid/non-hex backend values are treated as verification failures rather
    than being allowed to escape as ValueError.
    """

    try:
        return verify_preimage(preimage, payment_hash)
    except (TypeError, ValueError):
        return False


def _msat_to_int(value: Any) -> int:
    """
    Normalize Core Lightning millisatoshi values.

    Depending on CLN/REST/plugin versions, msat values can appear as native
    integers, strings such as "1000msat", or amount-shaped objects.
    """

    if value is None:
        return 0

    if isinstance(value, bool):
        return int(value)

    if isinstance(value, int):
        return value

    if isinstance(value, float):
        return int(value)

    if isinstance(value, str):
        amount = value.strip()

        if amount.endswith("msat"):
            amount = amount[:-4]

        return int(amount)

    if isinstance(value, dict):
        if "msat" in value:
            return _msat_to_int(value["msat"])

        if "amount_msat" in value:
            return _msat_to_int(value["amount_msat"])

    raise TypeError(
        f"Unsupported Core Lightning msat value: {value!r}"
    )


def _payment_fee_msat(
    payment: dict[str, Any],
) -> int | None:
    amount_sent = payment.get("amount_sent_msat")
    amount = payment.get("amount_msat")

    if amount_sent is None or amount is None:
        return None

    return (
        _msat_to_int(amount_sent)
        - _msat_to_int(amount)
    )


def _select_best_pay(
    pays: list[dict[str, Any]],
) -> dict[str, Any]:
    """
    Select the most useful logical payment status.

    Handling multiple entries defensively avoids converting an existing
    successful payment into pending merely because more than one result
    was returned.
    """

    complete = [
        payment
        for payment in pays
        if payment.get("status") == "complete"
    ]

    if complete:
        return complete[-1]

    pending = [
        payment
        for payment in pays
        if payment.get("status") == "pending"
    ]

    if pending:
        return pending[-1]

    failed = [
        payment
        for payment in pays
        if payment.get("status") == "failed"
    ]

    if failed:
        return failed[-1]

    return pays[-1]


def _generate_label() -> str:
    """Generate a unique Core Lightning invoice/payment label."""

    random_uuid = (
        base64.urlsafe_b64encode(uuid.uuid4().bytes)
        .rstrip(b"=")
        .decode()
    )

    return f"LNbits_{random_uuid}"
