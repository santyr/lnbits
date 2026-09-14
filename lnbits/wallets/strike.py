from __future__ import annotations

import asyncio
import hashlib
import json
import math
import os
import secrets
import time
from collections.abc import AsyncGenerator
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation, localcontext
from email.utils import parsedate_to_datetime
from enum import Enum
from pathlib import Path
from typing import Any
from urllib.parse import urlsplit, urlunsplit
from uuid import UUID, uuid4
from weakref import WeakValueDictionary

import httpx
from bolt11 import decode as bolt11_decode
from loguru import logger
from pydantic import BaseModel, Field, validator

from lnbits.db import Connection, Database, compat_timestamp_placeholder
from lnbits.helpers import normalize_endpoint
from lnbits.settings import settings

from .base import (
    Feature,
    InvoiceResponse,
    PaymentFailedStatus,
    PaymentPendingStatus,
    PaymentResponse,
    PaymentStatus,
    PaymentSuccessStatus,
    StatusResponse,
    Wallet,
)

# Fixed adapter policy: these do not require additions to LNbits Settings.
MAX_EXECUTE_ATTEMPTS = 3
STRIKE_SCHEMA_VERSION = "1"
STRIKE_SCHEMA_KEY = "single_file_schema_version"


class StrikePaymentResponse(PaymentResponse):
    """Keep the core's existing response logging from disclosing a preimage.

    All NamedTuple fields/properties and isinstance(PaymentResponse) remain
    compatible. The preimage is still available to LNbits for persistence.
    """

    __slots__ = ()

    def __repr__(self) -> str:
        return (
            f"PaymentResponse(ok={self.ok!r}, checking_id={self.checking_id!r}, "
            f"fee_msat={self.fee_msat!r}, preimage=<redacted>, "
            f"error_message={self.error_message!r})"
        )

    __str__ = __repr__


# Provider validation and typed journal records.
MSATS_PER_BTC = Decimal("100000000000")
SATS_PER_BTC = Decimal("100000000")
MAX_ERROR_TEXT_LENGTH = 512
MAX_ERROR_VALUES = 16
MAX_BTC = Decimal("21000000")


def _utc_datetime(value: Any, field_name: str) -> datetime:
    if isinstance(value, datetime):
        parsed = value
    elif isinstance(value, (int, float)):
        try:
            parsed = datetime.fromtimestamp(value, timezone.utc)
        except (OverflowError, OSError, ValueError) as exc:
            raise ValueError(f"invalid {field_name}") from exc
    elif isinstance(value, str):
        try:
            parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        except ValueError as exc:
            raise ValueError(f"invalid {field_name}") from exc
    else:
        raise ValueError(f"invalid {field_name}")

    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def _bounded_text(value: Any) -> str | None:
    if not isinstance(value, str):
        return None
    return "".join(c for c in value[:MAX_ERROR_TEXT_LENGTH] if c.isprintable())


def _safe_error_values(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        return {}
    safe: dict[str, Any] = {}
    for key, item in value.items():
        if len(safe) >= MAX_ERROR_VALUES:
            break
        if not isinstance(key, str):
            continue
        if isinstance(item, str):
            safe[key[:128]] = item[:MAX_ERROR_TEXT_LENGTH]
        elif isinstance(item, (bool, int, float)) or item is None:
            safe[key[:128]] = item
    return safe


class StrikeContractError(ValueError):
    """Raised when Strike returns data that is unsafe to use for accounting."""


class StrikeEnvironment(str, Enum):
    PRODUCTION = "production"
    SANDBOX = "sandbox"


class StrikePaymentPhase(str, Enum):
    QUOTE_INTENT_PERSISTED = "QUOTE_INTENT_PERSISTED"
    QUOTE_CREATED = "QUOTE_CREATED"
    FEE_APPROVED = "FEE_APPROVED"
    EXECUTE_DISPATCHED = "EXECUTE_DISPATCHED"
    PAYMENT_IDENTIFIED = "PAYMENT_IDENTIFIED"
    AMBIGUOUS = "AMBIGUOUS"
    COMPLETED = "COMPLETED"
    FAILED = "FAILED"
    QUOTE_ABANDONED = "QUOTE_ABANDONED"


class StrikeReceiveState(str, Enum):
    PENDING = "PENDING"
    COMPLETED = "COMPLETED"
    EXPIRED = "EXPIRED"


class StrikePaymentAttempt(BaseModel):
    payment_hash: str
    bolt11: str
    idempotency_key: str
    phase: StrikePaymentPhase
    invoice_amount_msat: int
    fee_limit_msat: int
    payment_quote_id: str | None = None
    payment_id: str | None = None
    quoted_fee_msat: int | None = None
    quoted_total_msat: int | None = None
    quote_valid_until: datetime | None = None
    execute_attempts: int = 0
    last_http_status: int | None = None
    last_error_code: str | None = None
    last_trace_id: str | None = None
    provider_state: str | None = None
    actual_fee_msat: int | None = None
    preimage: str | None = None
    created_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    updated_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    terminal_at: datetime | None = None

    @validator("payment_hash")
    def validate_payment_hash(cls, value: str) -> str:
        return normalize_payment_hash(value)

    @validator("idempotency_key")
    def validate_idempotency_key(cls, value: str) -> str:
        try:
            parsed = UUID(value)
        except (ValueError, AttributeError) as exc:
            raise ValueError("invalid Strike idempotency key") from exc
        if parsed.version != 4:
            raise ValueError("Strike idempotency key must be UUIDv4")
        return str(parsed)

    @validator("payment_quote_id", "payment_id")
    def validate_provider_id(cls, value: str | None, field) -> str | None:
        return validate_uuid(value, field.name) if value is not None else None

    @validator("invoice_amount_msat")
    def validate_invoice_amount(cls, value: int) -> int:
        if value <= 0:
            raise ValueError("Strike invoice amount must be positive")
        return value

    @validator(
        "fee_limit_msat",
        "quoted_fee_msat",
        "quoted_total_msat",
        "actual_fee_msat",
    )
    def validate_nonnegative_amount(
        cls, value: int | None, field
    ) -> int | None:
        if value is not None and value < 0:
            raise ValueError(f"{field.name} must not be negative")
        return value

    @validator("execute_attempts")
    def validate_execute_attempts(cls, value: int) -> int:
        if value < 0:
            raise ValueError("execute_attempts must not be negative")
        return value

    @validator("preimage")
    def validate_preimage(cls, value: str | None) -> str | None:
        if value is None:
            return None
        if len(value) != 64:
            raise ValueError("invalid Strike payment preimage")
        try:
            bytes.fromhex(value)
        except ValueError as exc:
            raise ValueError("invalid Strike payment preimage") from exc
        return value.lower()

    @validator(
        "quote_valid_until",
        "created_at",
        "updated_at",
        "terminal_at",
        pre=True,
    )
    def validate_datetime(cls, value: Any, field) -> datetime | None:
        if value is None:
            return None
        return _utc_datetime(value, field.name)

    class Config:
        use_enum_values = True
        validate_assignment = True
        validate_all = True

    @property
    def terminal(self) -> bool:
        return self.phase in {
            StrikePaymentPhase.COMPLETED.value,
            StrikePaymentPhase.FAILED.value,
            StrikePaymentPhase.QUOTE_ABANDONED.value,
        }


class StrikeReceiveRequest(BaseModel):
    receive_request_id: str
    payment_hash: str | None = None
    amount_msat: int | None = None
    expires_at: datetime | None = None
    state: StrikeReceiveState = StrikeReceiveState.PENDING
    last_checked_at: datetime | None = None
    created_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    updated_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))
    completed_at: datetime | None = None

    @validator("receive_request_id")
    def validate_receive_request_id(cls, value: str) -> str:
        return validate_uuid(value, "receiveRequestId")

    @validator("payment_hash")
    def validate_receive_payment_hash(cls, value: str | None) -> str | None:
        return normalize_payment_hash(value) if value is not None else None

    @validator("amount_msat")
    def validate_receive_amount(cls, value: int | None) -> int | None:
        if value is not None and value <= 0:
            raise ValueError("Strike receive amount must be positive")
        return value

    @validator(
        "expires_at",
        "last_checked_at",
        "created_at",
        "updated_at",
        "completed_at",
        pre=True,
    )
    def validate_datetime(cls, value: Any, field) -> datetime | None:
        if value is None:
            return None
        return _utc_datetime(value, field.name)

    class Config:
        use_enum_values = True
        validate_assignment = True
        validate_all = True


@dataclass(frozen=True)
class StrikeApiError:
    status_code: int
    code: str | None = None
    message: str | None = None
    values: dict[str, Any] | None = None
    validation_errors: dict[str, list[str]] | None = None
    trace_id: str | None = None

    @classmethod
    def from_response(  # noqa: C901
        cls, response: httpx.Response
    ) -> StrikeApiError:
        try:
            if len(response.content) > 1024 * 1024:
                raise ValueError("oversized Strike error")
            body: Any = response.json()
        except ValueError:
            body = None

        root = body if isinstance(body, dict) else {}
        data = root.get("data") if isinstance(root.get("data"), dict) else {}
        values = _safe_error_values(data.get("values"))
        validation_errors: dict[str, list[str]] = {}
        raw_validation = data.get("validationErrors")
        if isinstance(raw_validation, dict):
            for field, entries in raw_validation.items():
                if not isinstance(field, str) or not isinstance(entries, list):
                    continue
                codes = [
                    _bounded_text(entry.get("code")) or "UNKNOWN"
                    for entry in entries
                    if isinstance(entry, dict) and isinstance(entry.get("code"), str)
                ]
                if codes and len(validation_errors) < MAX_ERROR_VALUES:
                    validation_errors[field[:128]] = codes[:MAX_ERROR_VALUES]

        return cls(
            status_code=response.status_code,
            code=_bounded_text(data.get("code")),
            message=_bounded_text(data.get("message")),
            values=values,
            validation_errors=validation_errors,
            trace_id=_bounded_text(root.get("traceId")),
        )

    def value(self, key: str) -> Any:
        return (self.values or {}).get(key)

    def public_message(self, operation: str) -> str:
        messages = {
            "BALANCE_TOO_LOW": "Strike balance is too low.",
            "INVALID_STATE_FOR_INVOICE_EXPIRED": "Lightning invoice has expired.",
            "INVALID_LN_INVOICE": "Strike rejected the Lightning invoice.",
            "LN_ROUTE_NOT_FOUND": "Strike could not find a Lightning route.",
            "SELF_PAYMENT_NOT_ALLOWED": "Strike does not allow this self-payment.",
            "PAYMENT_QUOTE_EXPIRED": "Strike payment quote expired.",
            "USER_CURRENCY_UNAVAILABLE": "Strike BTC balance is unavailable.",
            "RECIPIENT_DATA_REQUIRED": "Strike requires beneficiary information.",
            "RECIPIENT_DATA_INVALID": "Strike rejected the beneficiary information.",
            "INVALID_RECIPIENT": "Strike reports that the recipient is unavailable.",
            "TOO_MANY_TRANSACTIONS": "Strike transaction limit was exceeded.",
        }
        if self.code in messages:
            return messages[self.code]
        if self.status_code == 401:
            return "Strike API authentication failed."
        if self.status_code == 403:
            return "Strike API key does not have the required scope."
        if self.status_code == 404:
            return f"Strike could not find the resource required to {operation}."
        if self.status_code == 429:
            return "Strike API rate limit exceeded."
        return f"Strike could not {operation}."


@dataclass(frozen=True)
class StrikeQuote:
    payment_quote_id: str
    amount_msat: int
    fee_msat: int
    total_msat: int
    valid_until: datetime | None


@dataclass(frozen=True)
class StrikePaymentData:
    payment_id: str | None
    state: str
    fee_msat: int
    preimage: str | None
    preimage_error: str | None = None


@dataclass(frozen=True)
class StrikeReceiveData:
    receive_request_id: str
    receive_type: str
    state: str
    payment_hash: str | None
    amount_msat: int | None
    preimage: str | None
    preimage_error: str | None = None


def normalize_payment_hash(value: Any) -> str:
    if not isinstance(value, str) or len(value) != 64:
        raise StrikeContractError("invalid Lightning payment hash")
    try:
        if len(bytes.fromhex(value)) != 32:
            raise ValueError("invalid hash length")
    except ValueError as exc:
        raise StrikeContractError("invalid Lightning payment hash") from exc
    return value.lower()


def validate_uuid(value: Any, field_name: str) -> str:
    if not isinstance(value, str):
        raise StrikeContractError(f"missing {field_name}")
    try:
        parsed = UUID(value)
    except (ValueError, AttributeError) as exc:
        raise StrikeContractError(f"invalid {field_name}") from exc
    return str(parsed)


def is_uuid(value: str) -> bool:
    try:
        validate_uuid(value, "identifier")
        return True
    except StrikeContractError:
        return False


def parse_datetime(value: Any, field_name: str) -> datetime:
    try:
        return _utc_datetime(value, field_name)
    except ValueError as exc:
        raise StrikeContractError(str(exc)) from exc


def btc_to_msat(value: Any, field_name: str, *, allow_zero: bool = True) -> int:
    # Strike documents decimal STRINGS. Do not accept rounded JSON floats,
    # enormous exponents, context-rounded values, NaN, or database overflows.
    if not isinstance(value, str) or not value or len(value) > 64:
        raise StrikeContractError(f"invalid {field_name} amount")
    try:
        amount = Decimal(value)
    except InvalidOperation as exc:
        raise StrikeContractError(f"invalid {field_name} amount") from exc
    if not amount.is_finite() or amount < 0 or amount > MAX_BTC:
        raise StrikeContractError(f"invalid {field_name} amount")
    if not allow_zero and amount == 0:
        raise StrikeContractError(f"invalid {field_name} amount")
    exponent = amount.as_tuple().exponent
    if not isinstance(exponent, int) or abs(exponent) > 64:
        raise StrikeContractError(f"invalid {field_name} precision")
    with localcontext() as context:
        context.prec = 80
        scaled = amount * MSATS_PER_BTC
        integral = scaled.to_integral_value()
    if scaled != integral:
        raise StrikeContractError(f"{field_name} has sub-millisatoshi precision")
    return int(integral)


def btc_money_to_msat(
    value: Any, field_name: str, *, allow_zero: bool = True
) -> int:
    if not isinstance(value, dict):
        raise StrikeContractError(f"missing {field_name}")
    currency = value.get("currency")
    if not isinstance(currency, str) or currency != "BTC":
        raise StrikeContractError(f"{field_name} is not denominated in BTC")
    return btc_to_msat(value.get("amount"), field_name, allow_zero=allow_zero)


def sats_to_btc_string(amount_sat: int) -> str:
    if type(amount_sat) is not int or not 0 < amount_sat <= 2100000000000000:
        raise StrikeContractError("invoice amount must be positive")
    amount = Decimal(amount_sat) / SATS_PER_BTC
    return f"{amount:.8f}"


def _validate_conversion_rate(  # noqa: C901
    data: dict[str, Any], field_name: str
) -> None:
    direct_source = data.get("sourceCurrency")
    direct_target = data.get("targetCurrency")
    if direct_source is not None and str(direct_source).upper() != "BTC":
        raise StrikeContractError(f"{field_name} source currency is not BTC")
    if direct_target is not None and str(direct_target).upper() != "BTC":
        raise StrikeContractError(f"{field_name} target currency is not BTC")

    conversion_rate = data.get("conversionRate")
    if conversion_rate is None:
        return
    if not isinstance(conversion_rate, dict):
        raise StrikeContractError(f"invalid {field_name} conversionRate")
    source = conversion_rate.get("sourceCurrency")
    target = conversion_rate.get("targetCurrency")
    if source is None or str(source).upper() != "BTC":
        raise StrikeContractError(f"{field_name} source currency is not BTC")
    if target is None or str(target).upper() != "BTC":
        raise StrikeContractError(f"{field_name} target currency is not BTC")
    try:
        value = conversion_rate.get("amount")
        if not isinstance(value, str) or len(value) > 64:
            raise ValueError("invalid conversion amount")
        amount = Decimal(value)
    except (InvalidOperation, ValueError, TypeError) as exc:
        raise StrikeContractError(
            f"invalid {field_name} conversionRate amount"
        ) from exc
    if not amount.is_finite() or amount != Decimal("1"):
        raise StrikeContractError(
            f"{field_name} contains a contradictory BTC conversion rate"
        )


def _fee_fields(
    data: dict[str, Any], *, prefix: str
) -> tuple[int | None, list[int]]:
    total_fee_msat: int | None = None
    if data.get("totalFee") is not None:
        total_fee_msat = btc_money_to_msat(data["totalFee"], f"{prefix}.totalFee")

    network_fees: list[int] = []
    if data.get("lightningNetworkFee") is not None:
        network_fees.append(
            btc_money_to_msat(
                data["lightningNetworkFee"],
                f"{prefix}.lightningNetworkFee",
            )
        )
    lightning = data.get("lightning")
    if lightning is not None:
        if not isinstance(lightning, dict):
            raise StrikeContractError(f"invalid {prefix}.lightning")
        if lightning.get("networkFee") is not None:
            network_fees.append(
                btc_money_to_msat(
                    lightning["networkFee"],
                    f"{prefix}.lightning.networkFee",
                )
            )
    return total_fee_msat, network_fees


def parse_quote(  # noqa: C901
    data: Any,
    *,
    expected_amount_msat: int,
    fee_limit_msat: int,
    now: datetime | None = None,
    minimum_validity_seconds: int = 1,
) -> StrikeQuote:
    if not isinstance(data, dict):
        raise StrikeContractError("invalid payment quote response")
    if fee_limit_msat < 0:
        raise StrikeContractError("invalid fee limit")
    if minimum_validity_seconds < 1:
        raise StrikeContractError("invalid quote validity margin")

    quote_id = validate_uuid(data.get("paymentQuoteId"), "paymentQuoteId")
    amount_msat = btc_money_to_msat(
        data.get("amount"), "quote.amount", allow_zero=False
    )
    total_msat = btc_money_to_msat(
        data.get("totalAmount"), "quote.totalAmount", allow_zero=False
    )
    if amount_msat != expected_amount_msat:
        raise StrikeContractError("payment quote amount does not match the invoice")
    if total_msat < amount_msat:
        raise StrikeContractError("payment quote total is below its amount")

    fee_msat = total_msat - amount_msat
    total_fee_msat, network_fees = _fee_fields(data, prefix="quote")
    if total_fee_msat is not None and total_fee_msat != fee_msat:
        raise StrikeContractError("payment quote fee fields disagree")
    if len(set(network_fees)) > 1:
        raise StrikeContractError("payment quote network fee fields disagree")
    if any(network_fee > fee_msat for network_fee in network_fees):
        raise StrikeContractError("payment quote network fee exceeds total fee")
    if fee_msat > fee_limit_msat:
        raise StrikeContractError("payment quote fee exceeds the authorized limit")

    raw_valid_until = data.get("validUntil")
    valid_until = (
        parse_datetime(raw_valid_until, "validUntil")
        if raw_valid_until is not None
        else None
    )
    if valid_until is not None:
        current_time = now or datetime.now(timezone.utc)
        minimum_valid_until = current_time + timedelta(
            seconds=minimum_validity_seconds
        )
        if valid_until <= minimum_valid_until:
            raise StrikeContractError("payment quote expires too soon")

    _validate_conversion_rate(data, "payment quote")
    return StrikeQuote(
        payment_quote_id=quote_id,
        amount_msat=amount_msat,
        fee_msat=fee_msat,
        total_msat=total_msat,
        valid_until=valid_until,
    )


def _verified_preimage(
    value: Any, payment_hash: str
) -> tuple[str | None, str | None]:
    if value is None:
        return None, None
    if not isinstance(value, str) or len(value) != 64:
        return None, "invalid payment preimage"
    try:
        raw = bytes.fromhex(value)
    except ValueError:
        return None, "invalid payment preimage"
    if len(raw) != 32:
        return None, "invalid payment preimage length"
    if hashlib.sha256(raw).hexdigest() != payment_hash:
        return None, "payment preimage does not match the invoice"
    return value.lower(), None


def extract_verified_preimage(
    data: dict[str, Any], payment_hash: str
) -> tuple[str | None, str | None]:
    lightning = data.get("lightning")
    lightning_data = lightning if isinstance(lightning, dict) else {}
    value = (
        lightning_data.get("preImage")
        or lightning_data.get("preimage")
        or data.get("preImage")
        or data.get("preimage")
    )
    return _verified_preimage(value, payment_hash)


def parse_payment_data(  # noqa: C901
    data: Any,
    *,
    payment_hash: str,
    expected_amount_msat: int,
    quoted_fee_msat: int | None,
) -> StrikePaymentData:
    if not isinstance(data, dict):
        raise StrikeContractError("invalid payment response")

    raw_payment_id = data.get("paymentId")
    payment_id = (
        validate_uuid(raw_payment_id, "paymentId")
        if raw_payment_id is not None
        else None
    )
    raw_state = data.get("state")
    if not isinstance(raw_state, str) or not raw_state:
        raise StrikeContractError("missing payment state")
    state = raw_state
    if state == "FAILED":
        if payment_id is None:
            raise StrikeContractError("failed payment response lacks paymentId")
        return StrikePaymentData(
            payment_id=payment_id,
            state=state,
            fee_msat=0,
            preimage=None,
        )

    raw_amount = data.get("amount")
    raw_total = data.get("totalAmount")
    if (raw_amount is None) != (raw_total is None):
        raise StrikeContractError("payment amount fields are incomplete")

    total_fee_msat, network_fees = _fee_fields(data, prefix="payment")
    if raw_amount is not None and raw_total is not None:
        amount_msat = btc_money_to_msat(
            raw_amount, "payment.amount", allow_zero=False
        )
        total_msat = btc_money_to_msat(
            raw_total, "payment.totalAmount", allow_zero=False
        )
        if amount_msat != expected_amount_msat:
            raise StrikeContractError("payment amount does not match the invoice")
        if total_msat < amount_msat:
            raise StrikeContractError("payment total is below its amount")
        fee_msat = total_msat - amount_msat
    elif quoted_fee_msat is not None:
        fee_msat = quoted_fee_msat
    else:
        raise StrikeContractError("payment response is missing accounting fields")

    if total_fee_msat is not None and total_fee_msat != fee_msat:
        raise StrikeContractError("payment fee fields disagree")
    if len(set(network_fees)) > 1:
        raise StrikeContractError("payment network fee fields disagree")
    if any(network_fee > fee_msat for network_fee in network_fees):
        raise StrikeContractError("payment network fee exceeds total fee")

    _validate_conversion_rate(data, "payment")
    preimage, preimage_error = (None, None)
    if state == "COMPLETED":
        preimage, preimage_error = extract_verified_preimage(data, payment_hash)
        if payment_id is None and preimage is None:
            raise StrikeContractError(
                "completed payment has neither paymentId nor valid preimage"
            )
    elif state != "FAILED" and payment_id is None:
        raise StrikeContractError("non-terminal payment is missing paymentId")
    return StrikePaymentData(
        payment_id=payment_id,
        state=state,
        fee_msat=fee_msat,
        preimage=preimage,
        preimage_error=preimage_error,
    )


def parse_receive_data(  # noqa: C901
    data: Any, receive_request_id: str
) -> StrikeReceiveData:
    if not isinstance(data, dict):
        raise StrikeContractError("invalid receive response")
    response_request_id = validate_uuid(
        data.get("receiveRequestId"), "receiveRequestId"
    )
    if response_request_id != receive_request_id:
        raise StrikeContractError("receive response belongs to another request")

    raw_state = data.get("state")
    if not isinstance(raw_state, str) or not raw_state:
        raise StrikeContractError("missing receive state")
    state = raw_state
    raw_type = data.get("type")
    receive_type = raw_type if isinstance(raw_type, str) else "UNKNOWN"

    if state != StrikeReceiveState.COMPLETED.value:
        return StrikeReceiveData(
            receive_request_id=receive_request_id,
            receive_type=receive_type,
            state=state,
            payment_hash=None,
            amount_msat=None,
            preimage=None,
        )

    credited = data.get("amountCredited")
    if receive_type == "LIGHTNING":
        lightning = data.get("lightning")
        if not isinstance(lightning, dict):
            raise StrikeContractError(
                "completed Lightning receive is missing Lightning data"
            )
        payment_hash = normalize_payment_hash(lightning.get("paymentHash"))
        amount_msat = btc_money_to_msat(
            data.get("amountReceived"),
            "receive.amountReceived",
            allow_zero=False,
        )
        if credited is not None:
            credited_msat = btc_money_to_msat(
                credited, "receive.amountCredited", allow_zero=False
            )
            if credited_msat != amount_msat:
                raise StrikeContractError(
                    "receive credited amount differs from received amount"
                )
        preimage, preimage_error = _verified_preimage(
            lightning.get("preimage") or lightning.get("preImage"),
            payment_hash,
        )
    elif receive_type == "P2P":
        if not isinstance(data.get("p2p"), dict):
            raise StrikeContractError("completed P2P receive is missing P2P data")
        if credited is None:
            raise StrikeContractError(
                "completed P2P receive is missing its credited BTC amount"
            )
        payment_hash = None
        amount_msat = btc_money_to_msat(
            credited,
            "receive.amountCredited",
            allow_zero=False,
        )
        preimage, preimage_error = None, None
    else:
        raise StrikeContractError(
            "completed receive used an unsupported settlement rail"
        )

    return StrikeReceiveData(
        receive_request_id=receive_request_id,
        receive_type=receive_type,
        state=state,
        payment_hash=payment_hash,
        amount_msat=amount_msat,
        preimage=preimage,
        preimage_error=preimage_error,
    )


# Database bootstrap and compare-and-swap state transitions.

async def _create_strike_tables(db: Connection) -> None:
    """Adds durable state for the Strike funding source."""
    await db.execute(f"""
        CREATE TABLE IF NOT EXISTS strike_payment_attempts (
            payment_hash TEXT PRIMARY KEY,
            bolt11 TEXT NOT NULL,
            idempotency_key TEXT NOT NULL UNIQUE,
            phase TEXT NOT NULL,
            invoice_amount_msat {db.big_int} NOT NULL,
            fee_limit_msat {db.big_int} NOT NULL,
            payment_quote_id TEXT UNIQUE,
            payment_id TEXT UNIQUE,
            quoted_fee_msat {db.big_int},
            quoted_total_msat {db.big_int},
            quote_valid_until TIMESTAMP,
            execute_attempts INT NOT NULL DEFAULT 0,
            last_http_status INT,
            last_error_code TEXT,
            last_trace_id TEXT,
            provider_state TEXT,
            actual_fee_msat {db.big_int},
            preimage TEXT,
            created_at TIMESTAMP NOT NULL DEFAULT {db.timestamp_now},
            updated_at TIMESTAMP NOT NULL DEFAULT {db.timestamp_now},
            terminal_at TIMESTAMP
        );
    """)
    await db.execute("""
        CREATE INDEX IF NOT EXISTS idx_strike_payment_attempts_phase
        ON strike_payment_attempts (phase);
    """)
    await db.execute("""
        CREATE INDEX IF NOT EXISTS idx_strike_payment_attempts_updated_at
        ON strike_payment_attempts (updated_at);
    """)

    await db.execute(f"""
        CREATE TABLE IF NOT EXISTS strike_receive_requests (
            receive_request_id TEXT PRIMARY KEY,
            payment_hash TEXT,
            amount_msat {db.big_int},
            expires_at TIMESTAMP,
            state TEXT NOT NULL DEFAULT 'PENDING',
            last_checked_at TIMESTAMP,
            created_at TIMESTAMP NOT NULL DEFAULT {db.timestamp_now},
            updated_at TIMESTAMP NOT NULL DEFAULT {db.timestamp_now},
            completed_at TIMESTAMP
        );
    """)
    await db.execute("""
        CREATE INDEX IF NOT EXISTS idx_strike_receive_requests_state_checked
        ON strike_receive_requests (state, last_checked_at);
    """)
    await db.execute("""
        CREATE INDEX IF NOT EXISTS idx_strike_receive_requests_payment_hash
        ON strike_receive_requests (payment_hash);
    """)

    await db.execute(f"""
        CREATE TABLE IF NOT EXISTS strike_wallet_metadata (
            metadata_key TEXT PRIMARY KEY,
            value TEXT NOT NULL,
            updated_at TIMESTAMP NOT NULL DEFAULT {db.timestamp_now}
        );
    """)


def utcnow() -> datetime:
    return datetime.now(timezone.utc)


def _timestamp_placeholder(name: str) -> str:
    return compat_timestamp_placeholder(name)


def _payment_attempt(row: Any) -> StrikePaymentAttempt | None:
    return StrikePaymentAttempt.parse_obj(row) if row else None


def _receive_request(row: Any) -> StrikeReceiveRequest | None:
    return StrikeReceiveRequest.parse_obj(row) if row else None


class StrikeStore:
    """Durable state used to make Strike payments and receives restart-safe."""

    def __init__(self, database: Database | None = None) -> None:
        # The caller can already hold core_db.lock while invoking the wallet.
        # Use a separate connection pool/lock to the SAME database, not core_db.
        # This keeps the journal in normal LNbits backups without lock reentry.
        self._owns_database = database is None
        self.db = database if database is not None else Database("database")
        self._schema_lock = asyncio.Lock()
        self._schema_ready = False

    async def initialize(self) -> None:
        """Bootstrap additive state without registering a core migration.

        The version marker is written last. Interrupted creation is safe to retry.
        Existing tables from the multi-file candidate use the same schema.
        Never upgrade/drop a schema that this file does not understand.
        """
        if self._schema_ready:
            return
        async with self._schema_lock:
            if self._schema_ready:
                return
            async with self.db.connect() as conn:
                await conn.execute(f"""
                    CREATE TABLE IF NOT EXISTS strike_wallet_metadata (
                        metadata_key TEXT PRIMARY KEY,
                        value TEXT NOT NULL,
                        updated_at TIMESTAMP NOT NULL DEFAULT {conn.timestamp_now}
                    );
                """)
                row = await conn.fetchone(
                    "SELECT value FROM strike_wallet_metadata "
                    "WHERE metadata_key = :key",
                    {"key": STRIKE_SCHEMA_KEY},
                )
                if row and row["value"] != STRIKE_SCHEMA_VERSION:
                    raise RuntimeError("Unsupported Strike journal schema version.")
                await _create_strike_tables(conn)
                # Validate the full set of columns before authorizing any API work.
                # A pre-existing incompatible table must fail closed, not appear
                # initialized merely because CREATE TABLE IF NOT EXISTS succeeded.
                await conn.fetchone("""
                    SELECT payment_hash, bolt11, idempotency_key, phase,
                           invoice_amount_msat, fee_limit_msat, payment_quote_id,
                           payment_id, quoted_fee_msat, quoted_total_msat,
                           quote_valid_until, execute_attempts, last_http_status,
                           last_error_code, last_trace_id, provider_state,
                           actual_fee_msat, preimage, created_at, updated_at,
                           terminal_at
                    FROM strike_payment_attempts WHERE 1 = 0
                """)
                await conn.fetchone("""
                    SELECT receive_request_id, payment_hash, amount_msat,
                           expires_at, state, last_checked_at, created_at,
                           updated_at, completed_at
                    FROM strike_receive_requests WHERE 1 = 0
                """)
                stamp = conn.timestamp_placeholder("updated_at")
                await conn.execute(
                    "INSERT INTO strike_wallet_metadata "
                    "(metadata_key, value, updated_at) "
                    f"VALUES (:key, :value, {stamp}) "
                    "ON CONFLICT (metadata_key) DO NOTHING",
                    {
                        "key": STRIKE_SCHEMA_KEY,
                        "value": STRIKE_SCHEMA_VERSION,
                        "updated_at": utcnow(),
                    },
                )
                row = await conn.fetchone(
                    "SELECT value FROM strike_wallet_metadata "
                    "WHERE metadata_key = :key",
                    {"key": STRIKE_SCHEMA_KEY},
                )
                if not row or row["value"] != STRIKE_SCHEMA_VERSION:
                    raise RuntimeError("Strike journal schema changed during startup.")
            self._schema_ready = True

    async def cleanup(self) -> None:
        if self._owns_database:
            await self.db.engine.dispose()

    async def create_payment_attempt(
        self,
        *,
        payment_hash: str,
        bolt11: str,
        invoice_amount_msat: int,
        fee_limit_msat: int,
    ) -> StrikePaymentAttempt:
        now = utcnow()
        values: dict[str, Any] = {
            "payment_hash": payment_hash,
            "bolt11": bolt11,
            "idempotency_key": str(uuid4()),
            "phase": StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value,
            "invoice_amount_msat": invoice_amount_msat,
            "fee_limit_msat": fee_limit_msat,
            "created_at": now,
            "updated_at": now,
        }
        created_at = _timestamp_placeholder("created_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            INSERT INTO strike_payment_attempts (
                payment_hash,
                bolt11,
                idempotency_key,
                phase,
                invoice_amount_msat,
                fee_limit_msat,
                created_at,
                updated_at
            ) VALUES (
                :payment_hash,
                :bolt11,
                :idempotency_key,
                :phase,
                :invoice_amount_msat,
                :fee_limit_msat,
                {created_at},
                {updated_at}
            )
            ON CONFLICT (payment_hash) DO NOTHING
        """  # noqa: S608
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": payment_hash},
            )

        attempt = _payment_attempt(row)
        if not attempt:
            raise RuntimeError("Could not persist Strike payment attempt.")
        if attempt.bolt11.lower() != bolt11.lower():
            raise ValueError("Strike payment hash is already bound to another invoice.")
        if attempt.invoice_amount_msat != invoice_amount_msat:
            raise ValueError("Strike payment amount changed for an existing invoice.")
        return attempt

    async def tighten_payment_fee_limit(
        self, payment_hash: str, fee_limit_msat: int
    ) -> StrikePaymentAttempt:
        """Atomically reduce a payment's authorization before dispatch."""
        if fee_limit_msat < 0:
            raise ValueError("Strike fee limit must not be negative.")
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                fee_limit_msat = :fee_limit_msat,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase IN (
                  :intent_phase,
                  :quote_phase,
                  :approved_phase
              )
              AND execute_attempts = 0
              AND fee_limit_msat > :fee_limit_msat
        """  # noqa: S608
        async with self.db.connect() as conn:
            await conn.execute(
                query,
                {
                    "payment_hash": payment_hash,
                    "fee_limit_msat": fee_limit_msat,
                    "intent_phase": (
                        StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value
                    ),
                    "quote_phase": StrikePaymentPhase.QUOTE_CREATED.value,
                    "approved_phase": StrikePaymentPhase.FEE_APPROVED.value,
                    "updated_at": now,
                },
            )
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": payment_hash},
            )
        attempt = _payment_attempt(row)
        if not attempt:
            raise RuntimeError("Strike payment attempt disappeared.")
        return attempt

    async def get_payment_attempt(
        self, payment_hash: str
    ) -> StrikePaymentAttempt | None:
        row = await self.db.fetchone(
            """
            SELECT * FROM strike_payment_attempts
            WHERE payment_hash = :payment_hash
            """,
            {"payment_hash": payment_hash},
        )
        return _payment_attempt(row)

    async def get_payment_attempt_by_payment_id(
        self, payment_id: str
    ) -> StrikePaymentAttempt | None:
        row = await self.db.fetchone(
            """
            SELECT * FROM strike_payment_attempts
            WHERE payment_id = :payment_id
            """,
            {"payment_id": payment_id},
        )
        return _payment_attempt(row)

    async def persist_validated_quote(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Persist a quote only for the worker that owns its request lease."""
        if not attempt.payment_quote_id:
            raise ValueError("Strike quote ID is required.")
        if attempt.quoted_fee_msat is None or attempt.quoted_total_msat is None:
            raise ValueError("Strike quote accounting is required.")
        now = utcnow()
        quote_valid_until = _timestamp_placeholder("quote_valid_until")
        terminal_at = _timestamp_placeholder("terminal_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = CASE
                    WHEN :quoted_fee_msat <= fee_limit_msat
                    THEN :approved_phase
                    ELSE :abandoned_phase
                END,
                payment_quote_id = :payment_quote_id,
                quoted_fee_msat = :quoted_fee_msat,
                quoted_total_msat = :quoted_total_msat,
                quote_valid_until = {quote_valid_until},
                last_http_status = :last_http_status,
                last_error_code = NULL,
                last_trace_id = NULL,
                terminal_at = CASE
                    WHEN :quoted_fee_msat <= fee_limit_msat
                    THEN NULL
                    ELSE {terminal_at}
                END,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :claimed_phase
              AND idempotency_key = :idempotency_key
              AND payment_quote_id IS NULL
              AND payment_id IS NULL
              AND execute_attempts = 0
        """  # noqa: S608
        values = {
            "payment_hash": attempt.payment_hash,
            "idempotency_key": attempt.idempotency_key,
            "claimed_phase": StrikePaymentPhase.QUOTE_CREATED.value,
            "approved_phase": StrikePaymentPhase.FEE_APPROVED.value,
            "abandoned_phase": StrikePaymentPhase.QUOTE_ABANDONED.value,
            "payment_quote_id": attempt.payment_quote_id,
            "quoted_fee_msat": attempt.quoted_fee_msat,
            "quoted_total_msat": attempt.quoted_total_msat,
            "quote_valid_until": attempt.quote_valid_until,
            "last_http_status": attempt.last_http_status,
            "terminal_at": now,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def abandon_payment_before_execution(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Fail an attempt only while the same quote remains undispatched."""
        if attempt.phase not in {
            StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value,
            StrikePaymentPhase.QUOTE_CREATED.value,
            StrikePaymentPhase.FEE_APPROVED.value,
        }:
            raise ValueError("Invalid Strike pre-dispatch phase.")
        now = utcnow()
        terminal_at = _timestamp_placeholder("terminal_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :abandoned_phase,
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                terminal_at = {terminal_at},
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND idempotency_key = :idempotency_key
              AND execute_attempts = 0
              AND (
                  payment_quote_id = :payment_quote_id
                  OR (
                      payment_quote_id IS NULL
                      AND :payment_quote_id IS NULL
                  )
              )
        """  # noqa: S608
        values = {
            "payment_hash": attempt.payment_hash,
            "idempotency_key": attempt.idempotency_key,
            "payment_quote_id": attempt.payment_quote_id,
            "expected_phase": attempt.phase,
            "abandoned_phase": StrikePaymentPhase.QUOTE_ABANDONED.value,
            "last_http_status": attempt.last_http_status,
            "last_error_code": attempt.last_error_code,
            "last_trace_id": attempt.last_trace_id,
            "terminal_at": now,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def identify_payment(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Persist a payment ID learned from a valid execute response."""
        if not attempt.payment_quote_id or not attempt.payment_id:
            raise ValueError("Strike quote and payment IDs are required.")
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :identified_phase,
                payment_id = :payment_id,
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND payment_quote_id = :payment_quote_id
              AND phase IN (
                  :dispatched_phase,
                  :ambiguous_phase,
                  :identified_phase
              )
              AND (payment_id IS NULL OR payment_id = :payment_id)
        """  # noqa: S608
        values = {
            "payment_hash": attempt.payment_hash,
            "payment_quote_id": attempt.payment_quote_id,
            "payment_id": attempt.payment_id,
            "dispatched_phase": StrikePaymentPhase.EXECUTE_DISPATCHED.value,
            "ambiguous_phase": StrikePaymentPhase.AMBIGUOUS.value,
            "identified_phase": StrikePaymentPhase.PAYMENT_IDENTIFIED.value,
            "last_http_status": attempt.last_http_status,
            "last_error_code": attempt.last_error_code,
            "last_trace_id": attempt.last_trace_id,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def record_payment_diagnostics(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Record bounded API diagnostics without changing payment state."""
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND (
                  :payment_id IS NULL
                  OR payment_id IS NULL
                  OR payment_id = :payment_id
              )
        """  # noqa: S608
        values = {
            "payment_hash": attempt.payment_hash,
            "payment_id": attempt.payment_id,
            "last_http_status": attempt.last_http_status,
            "last_error_code": attempt.last_error_code,
            "last_trace_id": attempt.last_trace_id,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def persist_payment_result(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Persist a provider observation without regressing terminal state."""
        if not attempt.payment_quote_id:
            raise ValueError("Strike quote ID is required.")
        if attempt.phase not in {
            StrikePaymentPhase.PAYMENT_IDENTIFIED.value,
            StrikePaymentPhase.COMPLETED.value,
            StrikePaymentPhase.FAILED.value,
        }:
            raise ValueError("Invalid Strike payment result phase.")
        now = utcnow()
        if attempt.phase in {
            StrikePaymentPhase.COMPLETED.value,
            StrikePaymentPhase.FAILED.value,
        } and attempt.terminal_at is None:
            attempt.terminal_at = now
        terminal_at = _timestamp_placeholder("terminal_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :phase,
                payment_id = COALESCE(payment_id, :payment_id),
                provider_state = :provider_state,
                actual_fee_msat = :actual_fee_msat,
                preimage = COALESCE(:preimage, preimage),
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                terminal_at = {terminal_at},
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND payment_quote_id = :payment_quote_id
              AND phase IN (
                  :dispatched_phase,
                  :ambiguous_phase,
                  :identified_phase
              )
              AND (
                  :payment_id IS NULL
                  OR payment_id IS NULL
                  OR payment_id = :payment_id
              )
        """  # noqa: S608
        values = {
            **attempt.dict(),
            "dispatched_phase": StrikePaymentPhase.EXECUTE_DISPATCHED.value,
            "ambiguous_phase": StrikePaymentPhase.AMBIGUOUS.value,
            "identified_phase": StrikePaymentPhase.PAYMENT_IDENTIFIED.value,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def fail_execution_if_current(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Record terminal rejection only for the exact execute attempt."""
        if not attempt.payment_quote_id:
            raise ValueError("Strike quote ID is required.")
        now = utcnow()
        terminal_at = _timestamp_placeholder("terminal_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :failed_phase,
                provider_state = :provider_state,
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                terminal_at = {terminal_at},
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND payment_quote_id = :payment_quote_id
              AND phase = :dispatched_phase
              AND execute_attempts = :execute_attempts
              AND payment_id IS NULL
        """  # noqa: S608
        values = {
            "payment_hash": attempt.payment_hash,
            "payment_quote_id": attempt.payment_quote_id,
            "execute_attempts": attempt.execute_attempts,
            "dispatched_phase": StrikePaymentPhase.EXECUTE_DISPATCHED.value,
            "failed_phase": StrikePaymentPhase.FAILED.value,
            "provider_state": attempt.provider_state,
            "last_http_status": attempt.last_http_status,
            "last_error_code": attempt.last_error_code,
            "last_trace_id": attempt.last_trace_id,
            "terminal_at": now,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def mark_execution_ambiguous(
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt:
        """Mark only the matching dispatched execution attempt ambiguous."""
        if not attempt.payment_quote_id:
            raise ValueError("Strike quote ID is required.")
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :ambiguous_phase,
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND payment_quote_id = :payment_quote_id
              AND phase = :dispatched_phase
              AND execute_attempts = :execute_attempts
              AND payment_id IS NULL
        """  # noqa: S608
        values = {
            "payment_hash": attempt.payment_hash,
            "payment_quote_id": attempt.payment_quote_id,
            "execute_attempts": attempt.execute_attempts,
            "dispatched_phase": StrikePaymentPhase.EXECUTE_DISPATCHED.value,
            "ambiguous_phase": StrikePaymentPhase.AMBIGUOUS.value,
            "last_http_status": attempt.last_http_status,
            "last_error_code": attempt.last_error_code,
            "last_trace_id": attempt.last_trace_id,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        saved = _payment_attempt(row)
        if not saved:
            raise RuntimeError("Strike payment attempt disappeared.")
        return saved

    async def claim_quote_creation(
        self, payment_hash: str
    ) -> StrikePaymentAttempt | None:
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :claimed_phase,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND payment_quote_id IS NULL
              AND payment_id IS NULL
              AND execute_attempts = 0
        """  # noqa: S608
        async with self.db.connect() as conn:
            result = await conn.execute(
                query,
                {
                    "payment_hash": payment_hash,
                    "claimed_phase": StrikePaymentPhase.QUOTE_CREATED.value,
                    "expected_phase": (
                        StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value
                    ),
                    "updated_at": now,
                },
            )
            if result.rowcount != 1:
                return None
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": payment_hash},
            )
        return _payment_attempt(row)

    async def release_quote_creation_claim(
        self,
        attempt: StrikePaymentAttempt,
        *,
        stale_before: datetime | None = None,
    ) -> StrikePaymentAttempt | None:
        """Release a quote request lease and preserve its idempotency key."""
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        stale_at = _timestamp_placeholder("stale_before")
        stale_clause = f"AND updated_at <= {stale_at}" if stale_before else ""
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :intent_phase,
                last_http_status = :last_http_status,
                last_error_code = :last_error_code,
                last_trace_id = :last_trace_id,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND idempotency_key = :idempotency_key
              AND payment_quote_id IS NULL
              AND payment_id IS NULL
              AND execute_attempts = 0
              {stale_clause}
        """  # noqa: S608
        values: dict[str, Any] = {
            "payment_hash": attempt.payment_hash,
            "idempotency_key": attempt.idempotency_key,
            "intent_phase": StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value,
            "expected_phase": StrikePaymentPhase.QUOTE_CREATED.value,
            "last_http_status": attempt.last_http_status,
            "last_error_code": attempt.last_error_code,
            "last_trace_id": attempt.last_trace_id,
            "updated_at": now,
            "stale_before": stale_before,
        }
        async with self.db.connect() as conn:
            result = await conn.execute(query, values)
            if result.rowcount != 1:
                return None
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        return _payment_attempt(row)

    async def claim_execution(
        self,
        payment_hash: str,
        expected_phase: StrikePaymentPhase | str,
        *,
        max_attempts: int,
        minimum_valid_until: datetime,
        allow_missing_valid_until: bool = False,
    ) -> StrikePaymentAttempt | None:
        phase = (
            expected_phase.value
            if isinstance(expected_phase, StrikePaymentPhase)
            else expected_phase
        )
        if phase not in {
            StrikePaymentPhase.FEE_APPROVED.value,
            StrikePaymentPhase.AMBIGUOUS.value,
        }:
            raise ValueError("Invalid Strike execution claim phase.")
        now = utcnow()
        minimum_validity = _timestamp_placeholder("minimum_valid_until")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :claimed_phase,
                execute_attempts = execute_attempts + 1,
                last_error_code = NULL,
                last_trace_id = NULL,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND execute_attempts < :max_attempts
              AND payment_quote_id IS NOT NULL
              AND payment_id IS NULL
              AND quoted_fee_msat IS NOT NULL
              AND quoted_fee_msat <= fee_limit_msat
              AND (
                  quote_valid_until > {minimum_validity}
                  OR (
                      :allow_missing_valid_until = 1
                      AND quote_valid_until IS NULL
                      AND execute_attempts = 0
                  )
              )
        """  # noqa: S608
        async with self.db.connect() as conn:
            result = await conn.execute(
                query,
                {
                    "payment_hash": payment_hash,
                    "claimed_phase": (
                        StrikePaymentPhase.EXECUTE_DISPATCHED.value
                    ),
                    "expected_phase": phase,
                    "max_attempts": max_attempts,
                    "minimum_valid_until": minimum_valid_until,
                    "allow_missing_valid_until": int(
                        allow_missing_valid_until
                    ),
                    "updated_at": now,
                },
            )
            if result.rowcount != 1:
                return None
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": payment_hash},
            )
        return _payment_attempt(row)

    async def abandon_predispatch_if_stale(
        self,
        payment_hash: str,
        expected_phase: StrikePaymentPhase | str,
        *,
        stale_before: datetime,
    ) -> StrikePaymentAttempt | None:
        phase = (
            expected_phase.value
            if isinstance(expected_phase, StrikePaymentPhase)
            else expected_phase
        )
        if phase not in {
            StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value,
            StrikePaymentPhase.QUOTE_CREATED.value,
            StrikePaymentPhase.FEE_APPROVED.value,
        }:
            raise ValueError("Invalid Strike pre-dispatch phase.")
        now = utcnow()
        terminal_at = _timestamp_placeholder("terminal_at")
        updated_at = _timestamp_placeholder("updated_at")
        stale_at = _timestamp_placeholder("stale_before")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :abandoned_phase,
                terminal_at = {terminal_at},
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND execute_attempts = 0
              AND updated_at <= {stale_at}
        """  # noqa: S608
        async with self.db.connect() as conn:
            result = await conn.execute(
                query,
                {
                    "payment_hash": payment_hash,
                    "abandoned_phase": (
                        StrikePaymentPhase.QUOTE_ABANDONED.value
                    ),
                    "expected_phase": phase,
                    "stale_before": stale_before,
                    "terminal_at": now,
                    "updated_at": now,
                },
            )
            if result.rowcount != 1:
                return None
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": payment_hash},
            )
        return _payment_attempt(row)

    async def mark_execution_ambiguous_if_stale(
        self, payment_hash: str, *, stale_before: datetime
    ) -> StrikePaymentAttempt | None:
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        stale_at = _timestamp_placeholder("stale_before")
        query = f"""
            UPDATE strike_payment_attempts SET
                phase = :ambiguous_phase,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND payment_quote_id IS NOT NULL
              AND payment_id IS NULL
              AND updated_at <= {stale_at}
        """  # noqa: S608
        async with self.db.connect() as conn:
            result = await conn.execute(
                query,
                {
                    "payment_hash": payment_hash,
                    "ambiguous_phase": StrikePaymentPhase.AMBIGUOUS.value,
                    "expected_phase": (
                        StrikePaymentPhase.EXECUTE_DISPATCHED.value
                    ),
                    "stale_before": stale_before,
                    "updated_at": now,
                },
            )
            if result.rowcount != 1:
                return None
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": payment_hash},
            )
        return _payment_attempt(row)

    async def reset_quote_intent(
        self,
        attempt: StrikePaymentAttempt,
        *,
        stale_before: datetime | None = None,
    ) -> StrikePaymentAttempt | None:
        """Abandon an unexecuted quote and use a fresh idempotency key."""
        expected_phase = attempt.phase
        if expected_phase not in {
            StrikePaymentPhase.QUOTE_CREATED.value,
            StrikePaymentPhase.FEE_APPROVED.value,
        }:
            raise ValueError("Invalid Strike quote reset phase.")
        now = utcnow()
        updated_at = _timestamp_placeholder("updated_at")
        stale_at = _timestamp_placeholder("stale_before")
        stale_clause = f"AND updated_at <= {stale_at}" if stale_before else ""
        query = f"""
            UPDATE strike_payment_attempts SET
                idempotency_key = :idempotency_key,
                phase = :intent_phase,
                payment_quote_id = NULL,
                payment_id = NULL,
                quoted_fee_msat = NULL,
                quoted_total_msat = NULL,
                quote_valid_until = NULL,
                execute_attempts = 0,
                last_http_status = NULL,
                last_error_code = NULL,
                last_trace_id = NULL,
                provider_state = NULL,
                actual_fee_msat = NULL,
                preimage = NULL,
                terminal_at = NULL,
                updated_at = {updated_at}
            WHERE payment_hash = :payment_hash
              AND phase = :expected_phase
              AND idempotency_key = :current_idempotency_key
              AND payment_id IS NULL
              AND execute_attempts = 0
              AND (
                  payment_quote_id = :current_payment_quote_id
                  OR (
                      payment_quote_id IS NULL
                      AND :current_payment_quote_id IS NULL
                  )
              )
              {stale_clause}
        """  # noqa: S608
        values: dict[str, Any] = {
            "payment_hash": attempt.payment_hash,
            "expected_phase": expected_phase,
            "idempotency_key": str(uuid4()),
            "current_idempotency_key": attempt.idempotency_key,
            "current_payment_quote_id": attempt.payment_quote_id,
            "intent_phase": StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value,
            "updated_at": now,
            "stale_before": stale_before,
        }
        async with self.db.connect() as conn:
            result = await conn.execute(query, values)
            if result.rowcount != 1:
                return None
            row = await conn.fetchone(
                """
                SELECT * FROM strike_payment_attempts
                WHERE payment_hash = :payment_hash
                """,
                {"payment_hash": attempt.payment_hash},
            )
        return _payment_attempt(row)

    async def upsert_receive_request(
        self,
        *,
        receive_request_id: str,
        payment_hash: str | None = None,
        amount_msat: int | None = None,
        expires_at: datetime | None = None,
    ) -> StrikeReceiveRequest:
        now = utcnow()
        expires_at_placeholder = _timestamp_placeholder("expires_at")
        created_at = _timestamp_placeholder("created_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            INSERT INTO strike_receive_requests (
                receive_request_id,
                payment_hash,
                amount_msat,
                expires_at,
                state,
                created_at,
                updated_at
            ) VALUES (
                :receive_request_id,
                :payment_hash,
                :amount_msat,
                {expires_at_placeholder},
                :state,
                {created_at},
                {updated_at}
            )
            ON CONFLICT (receive_request_id) DO UPDATE SET
                payment_hash = COALESCE(
                    strike_receive_requests.payment_hash,
                    excluded.payment_hash
                ),
                amount_msat = COALESCE(
                    strike_receive_requests.amount_msat,
                    excluded.amount_msat
                ),
                expires_at = COALESCE(
                    strike_receive_requests.expires_at,
                    excluded.expires_at
                ),
                updated_at = excluded.updated_at
        """  # noqa: S608
        values = {
            "receive_request_id": receive_request_id,
            "payment_hash": payment_hash,
            "amount_msat": amount_msat,
            "expires_at": expires_at,
            "state": StrikeReceiveState.PENDING.value,
            "created_at": now,
            "updated_at": now,
        }
        async with self.db.connect() as conn:
            await conn.execute(query, values)
            row = await conn.fetchone(
                """
                SELECT * FROM strike_receive_requests
                WHERE receive_request_id = :receive_request_id
                """,
                {"receive_request_id": receive_request_id},
            )

        receive = _receive_request(row)
        if not receive:
            raise RuntimeError("Could not persist Strike receive request.")
        if payment_hash and receive.payment_hash != payment_hash:
            raise ValueError("Strike receive request payment hash changed.")
        if amount_msat is not None and receive.amount_msat != amount_msat:
            raise ValueError("Strike receive request amount changed.")
        return receive

    async def get_receive_request(
        self, receive_request_id: str
    ) -> StrikeReceiveRequest | None:
        row = await self.db.fetchone(
            """
            SELECT * FROM strike_receive_requests
            WHERE receive_request_id = :receive_request_id
            """,
            {"receive_request_id": receive_request_id},
        )
        return _receive_request(row)

    async def restore_receive_request_from_lnbits(
        self, receive_request_id: str
    ) -> StrikeReceiveRequest | None:
        from lnbits.core.models.payments import Payment

        payment = await self.db.fetchone(
            """
            SELECT * FROM apipayments
            WHERE checking_id = :checking_id
              AND amount > 0
            LIMIT 1
            """,
            {"checking_id": receive_request_id},
            model=Payment,
        )
        if not payment:
            return None
        return await self.upsert_receive_request(
            receive_request_id=receive_request_id,
            payment_hash=payment.payment_hash,
            amount_msat=payment.amount,
            expires_at=payment.expiry,
        )

    async def list_pending_receive_requests(self) -> list[StrikeReceiveRequest]:
        # LNbits may mark an invoice failed simply because it expired locally,
        # before asking Strike. That does not prove it was never paid. Keep such
        # requests recoverable, but check old expired requests at most hourly.
        now = utcnow()
        current = _timestamp_placeholder("now")
        due = _timestamp_placeholder("expired_due")
        query = f"""
            SELECT * FROM strike_receive_requests
            WHERE state = :state
              AND (
                  expires_at IS NULL OR expires_at > {current}
                  OR last_checked_at IS NULL OR last_checked_at <= {due}
              )
            ORDER BY
                CASE WHEN last_checked_at IS NULL THEN 0 ELSE 1 END,
                last_checked_at,
                created_at,
                receive_request_id
            LIMIT 100
        """  # noqa: S608
        rows = await self.db.fetchall(
            query,
            {
                "state": StrikeReceiveState.PENDING.value,
                "now": now,
                "expired_due": now - timedelta(hours=1),
            },
        )
        return [StrikeReceiveRequest.parse_obj(row) for row in rows]

    async def touch_receive_request(self, receive_request_id: str) -> None:
        now = utcnow()
        last_checked_at = _timestamp_placeholder("last_checked_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_receive_requests SET
                last_checked_at = {last_checked_at},
                updated_at = {updated_at}
            WHERE receive_request_id = :receive_request_id
        """  # noqa: S608
        await self.db.execute(
            query,
            {
                "receive_request_id": receive_request_id,
                "last_checked_at": now,
                "updated_at": now,
            },
        )

    async def mark_receive_completed(self, receive_request_id: str) -> None:
        now = utcnow()
        completed_at = _timestamp_placeholder("completed_at")
        last_checked_at = _timestamp_placeholder("last_checked_at")
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            UPDATE strike_receive_requests SET
                state = :state,
                completed_at = {completed_at},
                last_checked_at = {last_checked_at},
                updated_at = {updated_at}
            WHERE receive_request_id = :receive_request_id
              AND state = :pending_state
        """  # noqa: S608
        await self.db.execute(
            query,
            {
                "receive_request_id": receive_request_id,
                "state": StrikeReceiveState.COMPLETED.value,
                "pending_state": StrikeReceiveState.PENDING.value,
                "completed_at": now,
                "last_checked_at": now,
                "updated_at": now,
            },
        )


    async def is_lnbits_invoice_settled(self, receive_request_id: str) -> bool:
        row = await self.db.fetchone(
            """
            SELECT checking_id FROM apipayments
            WHERE checking_id = :checking_id
              AND amount > 0
              AND status = 'success'
            LIMIT 1
            """,
            {"checking_id": receive_request_id},
        )
        return bool(row)

    async def get_metadata(self, key: str) -> str | None:
        row = await self.db.fetchone(
            "SELECT value FROM strike_wallet_metadata WHERE metadata_key = :key",
            {"key": key},
        )
        return str(row["value"]) if row and row.get("value") is not None else None

    async def set_metadata(self, key: str, value: str) -> None:
        updated_at = _timestamp_placeholder("updated_at")
        query = f"""
            INSERT INTO strike_wallet_metadata (metadata_key, value, updated_at)
            VALUES (:key, :value, {updated_at})
            ON CONFLICT (metadata_key) DO UPDATE SET
                value = excluded.value,
                updated_at = excluded.updated_at
        """  # noqa: S608
        await self.db.execute(
            query,
            {"key": key, "value": value, "updated_at": utcnow()},
        )


# LNbits adapter and HTTP transport.

PRODUCTION_HOST = "api.strike.me"
SANDBOX_HOST = "api.dev.strike.me"
MAX_RESPONSE_BYTES = 1024 * 1024
MAX_INLINE_RETRY_SECONDS = 5.0
MIN_QUOTE_VALIDITY_SECONDS = 5
QUOTE_EXECUTION_MARGIN_SECONDS = 2
QUOTE_CREATION_LEASE_SECONDS = 300
EXECUTION_LEASE_SECONDS = 120
PREDISPATCH_GRACE_SECONDS = 60
LEGACY_IMPORT_KEY = "legacy_pending_invoices_imported_v1"
MAX_LEGACY_STATE_BYTES = 8 * 1024 * 1024

TERMINAL_EXECUTE_ERROR_CODES = {
    "AMOUNT_TOO_HIGH",
    "AMOUNT_TOO_LOW",
    "BALANCE_TOO_LOW",
    "INVALID_AMOUNT",
    "INVALID_LN_INVOICE",
    "INVALID_RECIPIENT",
    "INVALID_STATE_FOR_INVOICE_EXPIRED",
    "LN_ROUTE_NOT_FOUND",
    "RECIPIENT_DATA_INVALID",
    "RECIPIENT_DATA_REQUIRED",
    "RECIPIENT_INVALID_NAME",
    "RECIPIENT_INVALID_VASP",
    "SELF_PAYMENT_NOT_ALLOWED",
    "TOO_MANY_TRANSACTIONS",
    "USER_CURRENCY_UNAVAILABLE",
}
PROCESSED_EXECUTE_ERROR_CODES = {
    "LN_INVOICE_PROCESSED",
    "PAYMENT_PROCESSED",
    "PROCESSING_PAYMENT",
}


@dataclass(frozen=True)
class StrikeEndpoint:
    url: str
    environment: StrikeEnvironment
    bolt11_currency: str


class TokenBucket:
    """Concurrency-safe token bucket with fractional refill accounting."""

    def __init__(self, rate: int, period_seconds: int) -> None:
        if rate <= 0 or period_seconds <= 0:
            raise ValueError("Strike rate limit values must be positive.")
        self.rate = float(rate)
        self.period = float(period_seconds)
        self.tokens = 1.0
        self.capacity = 1.0
        self.last_refill = time.monotonic()
        self.lock = asyncio.Lock()

    async def consume(self) -> None:
        while True:
            async with self.lock:
                now = time.monotonic()
                elapsed = now - self.last_refill
                self.last_refill = now
                self.tokens = min(
                    self.capacity,
                    self.tokens + elapsed * self.rate / self.period,
                )
                if self.tokens >= 1:
                    self.tokens -= 1
                    return
                wait_seconds = (1 - self.tokens) * self.period / self.rate
            await asyncio.sleep(wait_seconds)


class StrikeWallet(Wallet):
    """LNbits funding source backed by the Strike v1 API."""

    features = [Feature.descriptionhash]

    def __init__(
        self,
        *,
        client: httpx.AsyncClient | None = None,
        store: StrikeStore | None = None,
    ) -> None:
        if not settings.strike_api_endpoint:
            raise ValueError("Missing strike_api_endpoint")
        api_key = settings.strike_api_key
        if not isinstance(api_key, str) or not api_key:
            raise ValueError("Missing strike_api_key")
        if not all(33 <= ord(char) <= 126 for char in api_key):
            raise ValueError("Invalid strike_api_key")

        super().__init__()
        self.endpoint = self._validate_endpoint(settings.strike_api_endpoint)
        self.store = store or StrikeStore()
        self._sem = asyncio.Semaphore(value=20)
        self._initialization_lock = asyncio.Lock()
        self._balance_lock = asyncio.Lock()
        self._payment_locks_guard = asyncio.Lock()
        self._payment_locks: WeakValueDictionary[str, asyncio.Lock] = (
            WeakValueDictionary()
        )
        self._execution_tasks: dict[str, asyncio.Task[PaymentResponse]] = {}
        self._initialized = False
        self._closed = False
        self._retry_not_before = 0.0
        self._running = False

        if self.endpoint.environment == StrikeEnvironment.SANDBOX:
            payment_rate, general_rate = 90, 350
        else:
            payment_rate, general_rate = 250, 1000
        self._payment_limiter = TokenBucket(payment_rate, 60)
        self._general_limiter = TokenBucket(general_rate, 600)
        self._minimum_poll_seconds = max(1.0, 600 / general_rate)

        self.client = client or httpx.AsyncClient(
            base_url=self.endpoint.url,
            headers={
                "Authorization": f"Bearer {api_key}",
                "Content-Type": "application/json",
                "Accept": "application/json",
                "User-Agent": settings.user_agent,
            },
            timeout=httpx.Timeout(connect=5.0, read=40.0, write=10.0, pool=5.0),
            transport=httpx.AsyncHTTPTransport(
                limits=httpx.Limits(
                    max_connections=20,
                    max_keepalive_connections=10,
                ),
                retries=0,
            ),
            follow_redirects=False,
        )

        self._cached_balance: int | None = None
        self._cached_balance_ts = 0.0
        self._cache_ttl = 30.0

    @staticmethod
    def _validate_endpoint(  # noqa: C901
        raw_endpoint: str,
    ) -> StrikeEndpoint:
        endpoint = normalize_endpoint(raw_endpoint).rstrip("/")
        parsed = urlsplit(endpoint)
        if parsed.scheme.lower() != "https":
            raise ValueError("Strike API endpoint must use HTTPS.")
        if parsed.username or parsed.password:
            raise ValueError("Strike API endpoint must not contain user information.")
        if parsed.query or parsed.fragment:
            raise ValueError(
                "Strike API endpoint must not contain a query or fragment."
            )
        if not parsed.hostname:
            raise ValueError("Invalid Strike API endpoint.")

        hostname = parsed.hostname.lower()
        path = parsed.path.rstrip("/")
        if path != "/v1":
            raise ValueError("Strike API endpoint path must be exactly '/v1'.")
        if hostname in {PRODUCTION_HOST, SANDBOX_HOST} and parsed.port not in {
            None,
            443,
        }:
            raise ValueError("Official Strike API endpoints must use port 443.")

        if hostname == PRODUCTION_HOST:
            environment = StrikeEnvironment.PRODUCTION
            bolt11_currency = "bc"
        elif hostname == SANDBOX_HOST:
            environment = StrikeEnvironment.SANDBOX
            bolt11_currency = "tb"
        else:
            raise ValueError(
                "Custom Strike API endpoints are not supported by this adapter; "
                "use the official production or sandbox endpoint."
            )

        clean_url = urlunsplit(
            (parsed.scheme.lower(), parsed.netloc, "/v1", "", "")
        )
        return StrikeEndpoint(clean_url, environment, bolt11_currency)

    async def cleanup(self) -> None:
        self._running = False
        self._closed = True
        tasks = [task for task in self._execution_tasks.values() if not task.done()]
        if tasks:
            done, pending = await asyncio.wait(tasks, timeout=45)
            for task in done:
                try:
                    task.result()
                except asyncio.CancelledError:
                    pass
                except Exception as exc:
                    logger.warning(
                        "Strike execution task failed during shutdown: "
                        f"{exc.__class__.__name__}"
                    )
            if pending:
                logger.warning(
                    f"Strike has {len(pending)} execution task(s) journaled "
                    "for startup reconciliation."
                )
                for task in pending:
                    task.cancel()
                await asyncio.gather(*pending, return_exceptions=True)
        try:
            await self.client.aclose()
        except Exception as exc:
            logger.warning(f"Error closing Strike client: {exc.__class__.__name__}")

        if isinstance(self.store, StrikeStore):
            await self.store.cleanup()

    async def status(self) -> StatusResponse:  # noqa: C901
        try:
            await self._ensure_initialized()
        except Exception as exc:
            logger.warning("Strike journal unavailable: {}", type(exc).__name__)
            return StatusResponse("Strike payment journal is unavailable.", 0)
        now = time.monotonic()
        if (
            self._cached_balance is not None
            and now - self._cached_balance_ts < self._cache_ttl
        ):
            return StatusResponse(None, self._cached_balance)

        async with self._balance_lock:
            now = time.monotonic()
            if (
                self._cached_balance is not None
                and now - self._cached_balance_ts < self._cache_ttl
            ):
                return StatusResponse(None, self._cached_balance)
            try:
                response = await self._request("GET", "/balances", retry_safe=True)
                if response.is_error:
                    error = StrikeApiError.from_response(response)
                    self._log_api_error("fetch balance", error)
                    return StatusResponse(error.public_message("fetch the balance"), 0)
                data = self._response_json(response)
                balances = data.get("data") if isinstance(data, dict) else data
                if not isinstance(balances, list):
                    raise StrikeContractError("invalid balances response")
                btc_balances = [
                    item
                    for item in balances
                    if isinstance(item, dict)
                    and str(item.get("currency", "")).upper() == "BTC"
                ]
                if len(btc_balances) != 1:
                    raise StrikeContractError("expected exactly one BTC balance")
                balance_msat = btc_to_msat(
                    btc_balances[0].get("available"),
                    "available BTC balance",
                )
                self._cached_balance = balance_msat
                self._cached_balance_ts = now
                return StatusResponse(None, balance_msat)
            except (httpx.HTTPError, StrikeContractError, ValueError) as exc:
                logger.warning(f"Strike balance check failed: {exc.__class__.__name__}")
                return StatusResponse("Unable to read a valid Strike BTC balance.", 0)

    async def create_invoice(
        self,
        amount: int,
        memo: str | None = None,
        description_hash: bytes | None = None,
        unhashed_description: bytes | None = None,
        **kwargs,
    ) -> InvoiceResponse:
        try:
            await self._ensure_initialized()
            payload, expected_description_hash, expiry = self._invoice_payload(
                amount=amount,
                memo=memo,
                description_hash=description_hash,
                unhashed_description=unhashed_description,
                expiry=kwargs.get("expiry"),
            )
            response = await self._request(
                "POST",
                "/receive-requests",
                retry_safe=False,
                json=payload,
            )
            if response.is_error:
                error = StrikeApiError.from_response(response)
                self._log_api_error("create receive request", error)
                return InvoiceResponse(
                    ok=False,
                    error_message=error.public_message("create the invoice"),
                )

            data = self._response_json(response)
            receive_request_id, bolt11, payment_hash, expires_at = (
                self._validate_invoice_response(
                    data,
                    amount=amount,
                    memo=memo,
                    description_hash=expected_description_hash,
                    expiry=expiry,
                )
            )
            await self.store.upsert_receive_request(
                receive_request_id=receive_request_id,
                payment_hash=payment_hash,
                amount_msat=amount * 1000,
                expires_at=expires_at,
            )
            return InvoiceResponse(
                ok=True,
                checking_id=receive_request_id,
                payment_request=bolt11,
            )
        except httpx.HTTPError as exc:
            logger.warning(
                "Strike receive-request result is unknown after a transport error: "
                f"{exc.__class__.__name__}"
            )
            return InvoiceResponse(
                ok=False,
                error_message="Strike invoice creation outcome is unknown.",
            )
        except Exception as exc:
            logger.warning("Strike invoice creation failed: {}", type(exc).__name__)
            return InvoiceResponse(
                ok=False, error_message="Invalid Strike invoice request or response."
            )

    async def pay_invoice(self, bolt11: str, fee_limit_msat: int) -> PaymentResponse:
        try:
            invoice = bolt11_decode(bolt11)
            payment_hash = normalize_payment_hash(invoice.payment_hash)
        except Exception:
            return StrikePaymentResponse(
                ok=False, error_message="Invalid Lightning invoice."
            )

        try:
            await self._ensure_initialized()
            lock = await self._get_payment_lock(payment_hash)
            async with lock:
                existing = await self.store.get_payment_attempt(payment_hash)
                # Expiry, a changed BOLT11, or a new fee limit is NOT evidence
                # that a previously dispatched payment failed.
                if existing and (existing.execute_attempts or existing.terminal):
                    return await self._status_for_attempt(existing)
                error = self._validate_outgoing_invoice(invoice, fee_limit_msat)
                if error:
                    if existing:
                        return await self._fail_before_execution(existing, error)
                    return StrikePaymentResponse(
                        ok=False, checking_id=payment_hash, error_message=error
                    )
                attempt = await self.store.create_payment_attempt(
                    payment_hash=payment_hash,
                    bolt11=bolt11.lower(),
                    invoice_amount_msat=int(invoice.amount_msat),
                    fee_limit_msat=fee_limit_msat,
                )
                attempt = await self.store.tighten_payment_fee_limit(
                    payment_hash, fee_limit_msat
                )
                return await self._continue_payment(attempt)
        except Exception as exc:
            # This includes storage errors and post-dispatch parsing errors.
            # Without durable evidence of rejection, funds must stay reserved.
            logger.warning("Strike payment remains unknown: {}", type(exc).__name__)
            return StrikePaymentResponse(
                ok=None,
                checking_id=payment_hash,
                error_message="Strike payment outcome requires reconciliation.",
            )

    def _validate_outgoing_invoice(
        self, invoice: Any, fee_limit_msat: int
    ) -> str | None:
        if invoice.currency != self.endpoint.bolt11_currency:
            return "Lightning invoice is for the wrong network."
        if (
            not invoice.amount_msat
            or not 0 < int(invoice.amount_msat) <= 2100000000000000000
        ):
            return "Unsupported Lightning invoice amount."
        if invoice.expiry_time <= int(time.time()):
            return "Lightning invoice has expired."
        if type(fee_limit_msat) is not int or not 0 <= fee_limit_msat < 2**63:
            return "Invalid fee limit."
        return None

    async def get_invoice_status(self, checking_id: str) -> PaymentStatus:
        try:
            await self._ensure_initialized()
            if not is_uuid(checking_id):
                return PaymentPendingStatus()
            checking_id = validate_uuid(checking_id, "receiveRequestId")
            tracked = await self._bound_receive_request(checking_id)
            if tracked is None:
                return PaymentPendingStatus()
            async for page in self._receive_pages(
                f"/receive-requests/{checking_id}/receives", []
            ):
                status = self._invoice_status_from_page(
                    page, checking_id, tracked.payment_hash, tracked.amount_msat
                )
                if status.success:
                    self._invalidate_balance_cache()
                    return status
            await self.store.touch_receive_request(checking_id)
        except Exception as exc:
            logger.warning("Strike receive remains pending: {}", type(exc).__name__)
        # Missing records, expiry and HTTP errors do not prove non-settlement.
        return PaymentPendingStatus()

    async def _bound_receive_request(
        self, checking_id: str
    ) -> StrikeReceiveRequest | None:
        tracked = await self.store.get_receive_request(checking_id)
        if not tracked or tracked.payment_hash is None or tracked.amount_msat is None:
            tracked = await self.store.restore_receive_request_from_lnbits(checking_id)
        if not tracked or tracked.payment_hash is None or tracked.amount_msat is None:
            return None
        return tracked

    async def get_payment_status(self, checking_id: str) -> PaymentStatus:
        try:
            await self._ensure_initialized()
            attempt: StrikePaymentAttempt | None
            if is_uuid(checking_id):
                checking_id = validate_uuid(checking_id, "paymentId")
                attempt = await self.store.get_payment_attempt_by_payment_id(
                    checking_id
                )
            else:
                try:
                    payment_hash = normalize_payment_hash(checking_id)
                except StrikeContractError:
                    return PaymentPendingStatus()
                attempt = await self.store.get_payment_attempt(payment_hash)

            if not attempt:
                if is_uuid(checking_id):
                    return await self._get_legacy_payment_status(checking_id)
                logger.warning(
                    "Strike has no durable payment attempt for the requested "
                    "checking ID."
                )
                return PaymentPendingStatus()

            lock = await self._get_payment_lock(attempt.payment_hash)
            async with lock:
                response = await self._status_for_attempt(attempt)
                return self._payment_status_from_response(response)
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            logger.warning("Strike payment remains pending: {}", type(exc).__name__)
            return PaymentPendingStatus()

    async def paid_invoices_stream(self) -> AsyncGenerator[str, None]:
        self._running = True
        sleep_seconds = self._minimum_poll_seconds
        max_poll_seconds = max(5.0, self._minimum_poll_seconds * 4)

        while self._running and not self._closed and settings.lnbits_running:
            had_activity = False
            try:
                await self._ensure_initialized()
                pending = await self.store.list_pending_receive_requests()
                for start in range(0, len(pending), 100):
                    batch = pending[start : start + 100]
                    try:
                        completed = await self._get_completed_receives(batch)
                    finally:
                        # Rotate even a problematic batch instead of starving
                        # all later requests behind it.
                        for item in batch:
                            await self.store.touch_receive_request(
                                item.receive_request_id
                            )
                    for receive_request_id in completed:
                        if await self.store.is_lnbits_invoice_settled(
                            receive_request_id
                        ):
                            await self.store.mark_receive_completed(
                                receive_request_id
                            )
                            continue
                        had_activity = True
                        yield receive_request_id
                        if await self.store.is_lnbits_invoice_settled(
                            receive_request_id
                        ):
                            await self.store.mark_receive_completed(
                                receive_request_id
                            )
                            self._invalidate_balance_cache()
            except asyncio.CancelledError:
                raise
            except Exception as exc:
                logger.warning(f"Strike invoice poll failed: {exc.__class__.__name__}")

            if had_activity:
                sleep_seconds = self._minimum_poll_seconds
            else:
                sleep_seconds = min(max_poll_seconds, sleep_seconds * 1.5)
            await asyncio.sleep(sleep_seconds)

    async def _ensure_initialized(self) -> None:
        if self._closed:
            raise RuntimeError("Strike wallet is closed.")
        if self._initialized:
            return
        async with self._initialization_lock:
            if self._initialized:
                return
            await self.store.initialize()
            await self._import_legacy_pending_invoices()
            self._initialized = True

    async def _import_legacy_pending_invoices(self) -> None:
        if await self.store.get_metadata(LEGACY_IMPORT_KEY):
            return
        state_path = Path(
            settings.lnbits_data_folder,
            "strike_pending_invoices.json",
        )
        if state_path.exists():
            try:
                with state_path.open("rb") as state_file:
                    raw = state_file.read(MAX_LEGACY_STATE_BYTES + 1)
                if len(raw) > MAX_LEGACY_STATE_BYTES:
                    raise ValueError("legacy Strike state exceeds the size limit")
                raw_ids = json.loads(raw)
                if not isinstance(raw_ids, list):
                    raise ValueError("legacy Strike state is not a list")
                receive_request_ids = {
                    validate_uuid(value, "legacy receiveRequestId")
                    for value in raw_ids
                }
                for receive_request_id in receive_request_ids:
                    restored = await self.store.restore_receive_request_from_lnbits(
                        receive_request_id
                    )
                    if not restored:
                        await self.store.upsert_receive_request(
                            receive_request_id=receive_request_id
                        )
                backup_path = state_path.with_suffix(state_path.suffix + ".migrated")
                if backup_path.exists():
                    backup_path = state_path.with_suffix(
                        state_path.suffix + f".migrated.{int(time.time())}"
                    )
                os.replace(state_path, backup_path)
                logger.info(
                    "Imported "
                    f"{len(receive_request_ids)} legacy Strike receive requests."
                )
            except Exception as exc:
                logger.warning(
                    "Could not safely import strike_pending_invoices.json; "
                    f"leaving it untouched: {exc.__class__.__name__}"
                )
                raise RuntimeError(
                    "Legacy Strike invoice state needs repair."
                ) from exc
        await self.store.set_metadata(LEGACY_IMPORT_KEY, utcnow().isoformat())

    def _invoice_payload(  # noqa: C901
        self,
        *,
        amount: int,
        memo: str | None,
        description_hash: bytes | None,
        unhashed_description: bytes | None,
        expiry: Any,
    ) -> tuple[dict[str, Any], bytes | None, int]:
        if type(amount) is not int or amount <= 0:
            raise ValueError("Strike invoice amount must be a positive integer.")
        if description_hash is not None and unhashed_description is not None:
            raise ValueError("Only one invoice description hash source may be used.")

        expected_hash = description_hash
        if unhashed_description is not None:
            expected_hash = hashlib.sha256(unhashed_description).digest()
        if expected_hash is not None and len(expected_hash) != 32:
            raise ValueError("Invoice description hash must be 32 bytes.")

        expiry_seconds = (
            settings.lightning_invoice_expiry if expiry is None else expiry
        )
        if type(expiry_seconds) is not int or not 0 < expiry_seconds < 2**63:
            raise ValueError("Strike invoice expiry must be a positive integer.")

        bolt11: dict[str, Any] = {
            "amount": {
                "currency": "BTC",
                "amount": sats_to_btc_string(amount),
            },
            "expiryInSeconds": expiry_seconds,
        }
        if expected_hash is not None:
            bolt11["descriptionHash"] = expected_hash.hex()
        else:
            description = (memo or "")[:250]
            if description:
                bolt11["description"] = description

        return (
            {"bolt11": bolt11, "targetCurrency": "BTC"},
            expected_hash,
            expiry_seconds,
        )

    def _validate_invoice_response(  # noqa: C901
        self,
        data: Any,
        *,
        amount: int,
        memo: str | None,
        description_hash: bytes | None,
        expiry: int,
    ) -> tuple[str, str, str, datetime]:
        if not isinstance(data, dict):
            raise StrikeContractError("invalid receive-request response")
        receive_request_id = validate_uuid(
            data.get("receiveRequestId"), "receiveRequestId"
        )
        target_currency = data.get("targetCurrency")
        if target_currency is not None and str(target_currency).upper() != "BTC":
            raise StrikeContractError("receive request target currency is not BTC")

        bolt11_data = data.get("bolt11")
        if not isinstance(bolt11_data, dict):
            raise StrikeContractError("receive request is missing its Bolt11 data")
        payment_request = bolt11_data.get("invoice")
        if not isinstance(payment_request, str) or not payment_request:
            raise StrikeContractError("receive request is missing its Bolt11 invoice")
        payment_hash = normalize_payment_hash(bolt11_data.get("paymentHash"))
        expires_at = parse_datetime(bolt11_data.get("expires"), "expires")
        if expires_at <= utcnow():
            raise StrikeContractError("Strike returned an expired invoice")

        requested_amount = bolt11_data.get("requestedAmount")
        if requested_amount is not None:
            expected_msat = amount * 1000
            actual_msat = btc_money_to_msat(
                requested_amount,
                "receive-request requestedAmount",
                allow_zero=False,
            )
            if actual_msat != expected_msat:
                raise StrikeContractError("receive-request amount changed")

        decoded = bolt11_decode(payment_request)
        if decoded.currency != self.endpoint.bolt11_currency:
            raise StrikeContractError(
                "Strike returned an invoice for the wrong network"
            )
        if not decoded.amount_msat or int(decoded.amount_msat) != amount * 1000:
            raise StrikeContractError(
                "Strike returned an invoice with the wrong amount"
            )
        if normalize_payment_hash(decoded.payment_hash) != payment_hash:
            raise StrikeContractError("Strike invoice payment hash changed")
        if description_hash is not None:
            if decoded.description_hash != description_hash.hex():
                raise StrikeContractError("Strike invoice description hash changed")
        elif memo:
            if decoded.description != memo[:250]:
                raise StrikeContractError("Strike invoice description changed")
        elif decoded.description not in {None, ""}:
            raise StrikeContractError("Strike added an unexpected invoice description")
        if decoded.expiry <= 0 or abs(decoded.expiry - expiry) > 5:
            raise StrikeContractError("Strike invoice expiry changed unexpectedly")
        if decoded.expiry_time <= int(time.time()):
            raise StrikeContractError("Strike returned an expired Bolt11 invoice")
        decoded_expires_at = datetime.fromtimestamp(
            decoded.expiry_time, timezone.utc
        )
        if abs((decoded_expires_at - expires_at).total_seconds()) > 5:
            raise StrikeContractError("Strike invoice expiry fields disagree")
        return receive_request_id, payment_request, payment_hash, expires_at

    @staticmethod
    def _terminal_payment_response(
        attempt: StrikePaymentAttempt,
    ) -> PaymentResponse | None:
        if attempt.phase == StrikePaymentPhase.COMPLETED.value:
            return StrikePaymentResponse(
                ok=True,
                checking_id=attempt.payment_id or attempt.payment_hash,
                fee_msat=(
                    attempt.actual_fee_msat
                    if attempt.actual_fee_msat is not None
                    else attempt.quoted_fee_msat
                ),
                preimage=attempt.preimage,
            )
        if attempt.phase == StrikePaymentPhase.FAILED.value:
            return StrikePaymentResponse(
                ok=False,
                checking_id=attempt.payment_id or attempt.payment_hash,
                error_message="Strike payment failed.",
            )
        if attempt.phase == StrikePaymentPhase.QUOTE_ABANDONED.value:
            return StrikePaymentResponse(
                ok=False,
                checking_id=attempt.payment_hash,
                error_message="Strike payment stopped before quote execution.",
            )
        return None

    async def _continue_payment(  # noqa: C901
        self, attempt: StrikePaymentAttempt
    ) -> PaymentResponse:
        """Continue an explicitly authorized payment without changing its identity."""
        terminal_response = self._terminal_payment_response(attempt)
        if terminal_response:
            return terminal_response
        if attempt.payment_id:
            return await self._reconcile_payment(attempt)

        if attempt.payment_quote_id:
            if (
                attempt.quoted_fee_msat is None
                or attempt.quoted_fee_msat > attempt.fee_limit_msat
            ):
                if attempt.phase == StrikePaymentPhase.FEE_APPROVED.value:
                    return await self._fail_before_execution(
                        attempt,
                        "Strike payment quote fee exceeds the authorized limit.",
                    )
                return await self._mark_ambiguous(
                    attempt,
                    "Strike payment quote accounting requires manual review.",
                )

            if attempt.phase == StrikePaymentPhase.FEE_APPROVED.value:
                if (
                    attempt.quote_valid_until
                    and attempt.quote_valid_until
                    <= utcnow() + timedelta(seconds=QUOTE_EXECUTION_MARGIN_SECONDS)
                ):
                    reset_attempt = await self.store.reset_quote_intent(attempt)
                    if not reset_attempt:
                        return StrikePaymentResponse(
                            ok=None,
                            checking_id=attempt.payment_hash,
                        )
                    return await self._continue_payment(reset_attempt)
                return await self._execute_with_tracking(attempt)

            if attempt.phase == StrikePaymentPhase.EXECUTE_DISPATCHED.value:
                existing = self._execution_tasks.get(attempt.payment_hash)
                if existing and not existing.done():
                    return await asyncio.shield(existing)
                stale_before = utcnow() - timedelta(
                    seconds=EXECUTION_LEASE_SECONDS
                )
                stale_attempt = (
                    await self.store.mark_execution_ambiguous_if_stale(
                        attempt.payment_hash,
                        stale_before=stale_before,
                    )
                )
                if not stale_attempt:
                    return StrikePaymentResponse(
                        ok=None,
                        checking_id=attempt.payment_hash,
                    )
                attempt = stale_attempt

            if attempt.phase == StrikePaymentPhase.AMBIGUOUS.value:
                if (
                    not attempt.quote_valid_until
                    or attempt.quote_valid_until
                    <= utcnow() + timedelta(seconds=QUOTE_EXECUTION_MARGIN_SECONDS)
                    or attempt.execute_attempts
                    >= MAX_EXECUTE_ATTEMPTS
                ):
                    return StrikePaymentResponse(
                        ok=None,
                        checking_id=attempt.payment_hash,
                        error_message=(
                            "Strike payment requires manual reconciliation."
                        ),
                    )
                return await self._execute_with_tracking(attempt)

            logger.error(
                "Strike payment journal has a quote in a non-executable phase: "
                f"payment={attempt.payment_hash[:12]} phase={attempt.phase}"
            )
            return StrikePaymentResponse(
                ok=None,
                checking_id=attempt.payment_hash,
                error_message="Strike payment requires manual reconciliation.",
            )

        if attempt.phase == StrikePaymentPhase.QUOTE_CREATED.value:
            stale_before = utcnow() - timedelta(
                seconds=QUOTE_CREATION_LEASE_SECONDS
            )
            if attempt.updated_at > stale_before:
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_hash,
                )
            released_attempt = await self.store.release_quote_creation_claim(
                attempt,
                stale_before=stale_before,
            )
            if not released_attempt:
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_hash,
                )
            attempt = released_attempt

        if attempt.phase != StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value:
            logger.error(
                "Strike payment journal is missing its quote identifier: "
                f"payment={attempt.payment_hash[:12]} phase={attempt.phase}"
            )
            return StrikePaymentResponse(
                ok=None,
                checking_id=attempt.payment_hash,
                error_message="Strike payment requires manual reconciliation.",
            )

        claimed = await self.store.claim_quote_creation(attempt.payment_hash)
        if not claimed:
            return StrikePaymentResponse(ok=None, checking_id=attempt.payment_hash)
        quote_response = await self._create_quote(claimed)
        if isinstance(quote_response, PaymentResponse):
            return quote_response
        return await self._execute_with_tracking(quote_response)

    async def _create_quote(  # noqa: C901
        self, attempt: StrikePaymentAttempt
    ) -> StrikePaymentAttempt | PaymentResponse:
        for duplicate_recovery in range(2):
            try:
                response = await self._request(
                    "POST",
                    "/payment-quotes/lightning",
                    retry_safe=True,
                    headers={"idempotency-key": attempt.idempotency_key},
                    json={
                        "lnInvoice": attempt.bolt11,
                        "sourceCurrency": "BTC",
                    },
                )
            except asyncio.CancelledError:
                await self.store.release_quote_creation_claim(attempt)
                raise
            except httpx.HTTPError as exc:
                released = await self.store.release_quote_creation_claim(attempt)
                current = released or await self.store.get_payment_attempt(
                    attempt.payment_hash
                )
                terminal_response = (
                    self._terminal_payment_response(current) if current else None
                )
                if terminal_response:
                    return terminal_response
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_hash,
                    error_message=(
                        "Strike quote creation will be retried with the same "
                        f"idempotency key after {exc.__class__.__name__}."
                    ),
                )

            if response.is_success:
                try:
                    quote = parse_quote(
                        self._response_json(response),
                        expected_amount_msat=attempt.invoice_amount_msat,
                        fee_limit_msat=attempt.fee_limit_msat,
                        minimum_validity_seconds=MIN_QUOTE_VALIDITY_SECONDS,
                    )
                except StrikeContractError as exc:
                    return await self._fail_before_execution(attempt, str(exc))
                attempt.payment_quote_id = quote.payment_quote_id
                attempt.quoted_fee_msat = quote.fee_msat
                attempt.quoted_total_msat = quote.total_msat
                attempt.quote_valid_until = quote.valid_until
                attempt.phase = StrikePaymentPhase.FEE_APPROVED
                attempt.last_http_status = response.status_code
                attempt = await self.store.persist_validated_quote(attempt)
                terminal_response = self._terminal_payment_response(attempt)
                if terminal_response:
                    return terminal_response
                if attempt.phase != StrikePaymentPhase.FEE_APPROVED.value:
                    return StrikePaymentResponse(
                        ok=None,
                        checking_id=attempt.payment_id or attempt.payment_hash,
                    )
                return attempt

            error = StrikeApiError.from_response(response)
            self._log_api_error("create payment quote", error)
            if error.code == "DUPLICATE_PAYMENT_QUOTE" and duplicate_recovery == 0:
                try:
                    duplicate_quote_id = validate_uuid(
                        error.value("paymentQuoteId"),
                        "paymentQuoteId",
                    )
                except StrikeContractError as exc:
                    return await self._fail_before_execution(attempt, str(exc))
                logger.info(
                    "Strike quote response was lost; abandoning the unexecuted "
                    f"quote={duplicate_quote_id} and creating a fresh quote."
                )
                reset_attempt = await self.store.reset_quote_intent(attempt)
                if not reset_attempt:
                    return StrikePaymentResponse(
                        ok=None,
                        checking_id=attempt.payment_hash,
                    )
                attempt = reset_attempt
                claimed = await self.store.claim_quote_creation(
                    attempt.payment_hash
                )
                if not claimed:
                    return StrikePaymentResponse(
                        ok=None,
                        checking_id=attempt.payment_hash,
                    )
                attempt = claimed
                continue
            if self._retryable_response(response):
                self._record_error(attempt, error)
                released = await self.store.release_quote_creation_claim(attempt)
                current = released or await self.store.get_payment_attempt(
                    attempt.payment_hash
                )
                terminal_response = (
                    self._terminal_payment_response(current) if current else None
                )
                if terminal_response:
                    return terminal_response
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_hash,
                    error_message=error.public_message("create the payment quote"),
                )
            return await self._fail_before_execution(
                attempt,
                error.public_message("create the payment quote"),
                error=error,
            )

        return await self._fail_before_execution(
            attempt, "Strike could not create a unique payment quote."
        )

    async def _fail_before_execution(
        self,
        attempt: StrikePaymentAttempt,
        message: str,
        *,
        error: StrikeApiError | None = None,
    ) -> PaymentResponse:
        if error:
            self._record_error(attempt, error)
        attempt = await self.store.abandon_payment_before_execution(attempt)
        terminal_response = self._terminal_payment_response(attempt)
        if terminal_response:
            return terminal_response
        return StrikePaymentResponse(
            ok=None,
            checking_id=attempt.payment_id or attempt.payment_hash,
            error_message="Strike payment changed during quote validation.",
        )

    async def _execute_with_tracking(
        self, attempt: StrikePaymentAttempt
    ) -> PaymentResponse:
        existing = self._execution_tasks.get(attempt.payment_hash)
        if existing and not existing.done():
            return await asyncio.shield(existing)

        claimed = await self.store.claim_execution(
            attempt.payment_hash,
            attempt.phase,
            max_attempts=MAX_EXECUTE_ATTEMPTS,
            minimum_valid_until=(
                utcnow() + timedelta(seconds=QUOTE_EXECUTION_MARGIN_SECONDS)
            ),
            allow_missing_valid_until=(
                attempt.phase == StrikePaymentPhase.FEE_APPROVED.value
                and attempt.quote_valid_until is None
            ),
        )
        if not claimed:
            current = await self.store.get_payment_attempt(attempt.payment_hash)
            if current:
                terminal = self._terminal_payment_response(current)
                if terminal:
                    return terminal
                return StrikePaymentResponse(
                    ok=None, checking_id=current.payment_id or current.payment_hash
                )
            return StrikePaymentResponse(ok=None, checking_id=attempt.payment_hash)

        task = asyncio.create_task(
            self._execute_payment(claimed.payment_hash),
            name=f"strike_execute_{claimed.payment_hash}",
        )
        self._execution_tasks[claimed.payment_hash] = task

        def remove_task(completed: asyncio.Task[PaymentResponse]) -> None:
            current = self._execution_tasks.get(claimed.payment_hash)
            if current is completed:
                self._execution_tasks.pop(claimed.payment_hash, None)
            if completed.cancelled():
                return
            exception = completed.exception()
            if exception:
                logger.warning(
                    "Strike execution task failed: "
                    f"payment={claimed.payment_hash[:12]} "
                    f"error={exception.__class__.__name__}"
                )

        task.add_done_callback(remove_task)
        return await asyncio.shield(task)

    async def _execute_payment(  # noqa: C901
        self, payment_hash: str
    ) -> PaymentResponse:
        attempt = await self.store.get_payment_attempt(payment_hash)
        if (
            not attempt
            or not attempt.payment_quote_id
            or attempt.phase != StrikePaymentPhase.EXECUTE_DISPATCHED.value
        ):
            return StrikePaymentResponse(ok=None, checking_id=payment_hash)

        try:
            response = await self._request(
                "PATCH",
                f"/payment-quotes/{attempt.payment_quote_id}/execute",
                retry_safe=False,
            )
        except httpx.HTTPError as exc:
            return await self._mark_ambiguous(
                attempt,
                f"Strike execute transport error: {exc.__class__.__name__}",
            )

        if response.is_success:
            try:
                response_data = self._response_json(response)
                if not isinstance(response_data, dict):
                    raise StrikeContractError("invalid payment execution response")
                attempt.last_http_status = response.status_code
                raw_payment_id = response_data.get("paymentId")
                if raw_payment_id is not None:
                    attempt.payment_id = validate_uuid(
                        raw_payment_id, "paymentId"
                    )
                    attempt.phase = StrikePaymentPhase.PAYMENT_IDENTIFIED
                    attempt = await self.store.identify_payment(attempt)
                    terminal_response = self._terminal_payment_response(attempt)
                    if terminal_response:
                        return terminal_response
                payment_data = parse_payment_data(
                    response_data,
                    payment_hash=attempt.payment_hash,
                    expected_amount_msat=attempt.invoice_amount_msat,
                    quoted_fee_msat=attempt.quoted_fee_msat,
                )
            except StrikeContractError as exc:
                return await self._mark_ambiguous(attempt, str(exc))
            return await self._apply_payment_data(attempt, payment_data)

        error = StrikeApiError.from_response(response)
        self._record_error(attempt, error)
        self._log_api_error("execute payment quote", error)
        payment_id = error.value("paymentId")
        if error.code in PROCESSED_EXECUTE_ERROR_CODES and payment_id:
            try:
                attempt.payment_id = validate_uuid(payment_id, "paymentId")
            except StrikeContractError:
                return await self._mark_ambiguous(
                    attempt, "Strike returned an invalid processed payment ID."
                )
            attempt.phase = StrikePaymentPhase.PAYMENT_IDENTIFIED
            attempt = await self.store.identify_payment(attempt)
            terminal_response = self._terminal_payment_response(attempt)
            if terminal_response:
                return terminal_response
            return await self._reconcile_payment(attempt)

        if (
            response.status_code == 422
            and error.code == "PAYMENT_QUOTE_EXPIRED"
            and attempt.execute_attempts == 1
        ):
            attempt.phase = StrikePaymentPhase.FAILED
            attempt.terminal_at = utcnow()
            attempt = await self.store.fail_execution_if_current(attempt)
            terminal_response = self._terminal_payment_response(attempt)
            if not terminal_response:
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_id or attempt.payment_hash,
                    error_message=(
                        "Strike payment outcome changed during reconciliation."
                    ),
                )
            return terminal_response or StrikePaymentResponse(
                ok=False,
                checking_id=attempt.payment_hash,
                error_message=error.public_message("execute the payment quote"),
            )
        if attempt.execute_attempts == 1 and (
            (
                response.status_code == 422
                and error.code in TERMINAL_EXECUTE_ERROR_CODES
            )
            or response.status_code in {401, 403, 404, 405}
        ):
            attempt.phase = StrikePaymentPhase.FAILED
            attempt.terminal_at = utcnow()
            attempt = await self.store.fail_execution_if_current(attempt)
            terminal_response = self._terminal_payment_response(attempt)
            if not terminal_response:
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_id or attempt.payment_hash,
                    error_message=(
                        "Strike payment outcome changed during reconciliation."
                    ),
                )
            return terminal_response or StrikePaymentResponse(
                ok=False,
                checking_id=attempt.payment_hash,
                error_message=error.public_message("execute the payment quote"),
            )
        return await self._mark_ambiguous(
            attempt,
            error.public_message("confirm the payment outcome"),
        )

    async def _mark_ambiguous(
        self, attempt: StrikePaymentAttempt, message: str
    ) -> PaymentResponse:
        if attempt.payment_id:
            attempt.phase = StrikePaymentPhase.PAYMENT_IDENTIFIED
            attempt = await self.store.identify_payment(attempt)
        elif attempt.phase == StrikePaymentPhase.EXECUTE_DISPATCHED.value:
            attempt = await self.store.mark_execution_ambiguous(attempt)
        elif attempt.phase != StrikePaymentPhase.AMBIGUOUS.value:
            logger.error(
                "Strike could not safely move a non-dispatched payment to the "
                f"ambiguous phase: payment={attempt.payment_hash[:12]} "
                f"phase={attempt.phase}"
            )
        terminal_response = self._terminal_payment_response(attempt)
        if terminal_response:
            return terminal_response
        return StrikePaymentResponse(
            ok=None,
            checking_id=attempt.payment_id or attempt.payment_hash,
            error_message=message,
        )

    async def _reconcile_payment(
        self, attempt: StrikePaymentAttempt
    ) -> PaymentResponse:
        if not attempt.payment_id:
            return StrikePaymentResponse(ok=None, checking_id=attempt.payment_hash)
        try:
            response = await self._request(
                "GET",
                f"/payments/{attempt.payment_id}",
                retry_safe=True,
            )
        except httpx.HTTPError as exc:
            return await self._mark_ambiguous(
                attempt,
                f"Strike payment lookup failed: {exc.__class__.__name__}",
            )
        if response.is_error:
            error = StrikeApiError.from_response(response)
            self._record_error(attempt, error)
            attempt = await self.store.record_payment_diagnostics(attempt)
            self._log_api_error("lookup payment", error)
            terminal_response = self._terminal_payment_response(attempt)
            if terminal_response:
                return terminal_response
            return StrikePaymentResponse(
                ok=None,
                checking_id=attempt.payment_id,
                error_message=error.public_message("lookup the payment"),
            )
        try:
            attempt.last_http_status = response.status_code
            payment_data = parse_payment_data(
                self._response_json(response),
                payment_hash=attempt.payment_hash,
                expected_amount_msat=attempt.invoice_amount_msat,
                quoted_fee_msat=attempt.quoted_fee_msat,
            )
        except StrikeContractError as exc:
            return await self._mark_ambiguous(attempt, str(exc))
        return await self._apply_payment_data(attempt, payment_data)

    async def _apply_payment_data(  # noqa: C901
        self,
        attempt: StrikePaymentAttempt,
        payment_data: StrikePaymentData,
    ) -> PaymentResponse:
        if (
            attempt.payment_id
            and payment_data.payment_id
            and attempt.payment_id != payment_data.payment_id
        ):
            return await self._mark_ambiguous(
                attempt, "Strike payment ID changed during reconciliation."
            )
        if payment_data.payment_id:
            attempt.payment_id = payment_data.payment_id
        attempt.provider_state = payment_data.state
        attempt.actual_fee_msat = payment_data.fee_msat
        if payment_data.preimage_error:
            logger.error(
                "Strike completed payment returned an unusable preimage: "
                f"{payment_data.preimage_error}"
            )
        attempt.preimage = payment_data.preimage

        if payment_data.state == "COMPLETED":
            if (
                attempt.quoted_fee_msat is not None
                and payment_data.fee_msat != attempt.quoted_fee_msat
            ):
                logger.critical(
                    "Strike completed payment fee differs from its approved quote: "
                    f"payment={attempt.payment_hash[:12]} "
                    f"quoted_fee_msat={attempt.quoted_fee_msat} "
                    f"actual_fee_msat={payment_data.fee_msat}"
                )
            if payment_data.fee_msat > attempt.fee_limit_msat:
                logger.critical(
                    "Strike completed payment fee exceeded the authorized limit: "
                    f"payment={attempt.payment_hash[:12]} "
                    f"fee_msat={payment_data.fee_msat} "
                    f"limit_msat={attempt.fee_limit_msat}"
                )
            attempt.phase = StrikePaymentPhase.COMPLETED
            attempt.terminal_at = utcnow()
            attempt = await self.store.persist_payment_result(attempt)
            terminal_response = self._terminal_payment_response(attempt)
            if terminal_response and terminal_response.success:
                self._invalidate_balance_cache()
                return terminal_response
            return StrikePaymentResponse(
                ok=None,
                checking_id=attempt.payment_id or attempt.payment_hash,
                error_message=(
                    "Strike completion conflicted with durable payment state."
                ),
            )

        if payment_data.state == "FAILED":
            attempt.phase = StrikePaymentPhase.FAILED
            attempt.terminal_at = utcnow()
            attempt = await self.store.persist_payment_result(attempt)
            terminal_response = self._terminal_payment_response(attempt)
            if terminal_response:
                return terminal_response
            return StrikePaymentResponse(
                ok=None,
                checking_id=attempt.payment_id or attempt.payment_hash,
                error_message=(
                    "Strike failure conflicted with durable payment state."
                ),
            )

        if not attempt.payment_id:
            return await self._mark_ambiguous(
                attempt, "Strike returned a non-terminal payment without paymentId."
            )
        attempt.phase = StrikePaymentPhase.PAYMENT_IDENTIFIED
        attempt = await self.store.persist_payment_result(attempt)
        terminal_response = self._terminal_payment_response(attempt)
        return terminal_response or StrikePaymentResponse(
            ok=None,
            checking_id=attempt.payment_id or attempt.payment_hash,
        )

    async def _get_legacy_payment_status(self, payment_id: str) -> PaymentStatus:
        """Reconcile provider IDs created before the durable Strike journal existed."""
        try:
            response = await self._request(
                "GET",
                f"/payments/{validate_uuid(payment_id, 'paymentId')}",
                retry_safe=True,
            )
            if response.is_error:
                return PaymentPendingStatus()
            data = self._response_json(response)
            if not isinstance(data, dict):
                raise StrikeContractError("invalid legacy payment response")
            response_payment_id = validate_uuid(data.get("paymentId"), "paymentId")
            if response_payment_id != payment_id:
                raise StrikeContractError("legacy payment ID changed")
            state = str(data.get("state") or "")
            if state == "FAILED":
                return PaymentFailedStatus()
            if state != "COMPLETED":
                return PaymentPendingStatus()
            fee_msat = self._legacy_payment_fee_msat(data)
            return PaymentSuccessStatus(fee_msat=fee_msat)
        except (httpx.HTTPError, StrikeContractError, ValueError) as exc:
            logger.warning("Strike legacy payment pending: {}", type(exc).__name__)
            return PaymentPendingStatus()

    @staticmethod
    def _legacy_payment_fee_msat(data: dict[str, Any]) -> int:
        amount_msat = btc_money_to_msat(
            data.get("amount"), "legacy payment amount", allow_zero=False
        )
        total_msat = btc_money_to_msat(
            data.get("totalAmount"),
            "legacy payment totalAmount",
            allow_zero=False,
        )
        if total_msat < amount_msat:
            raise StrikeContractError("legacy payment total is below its amount")
        fee_msat = total_msat - amount_msat
        if data.get("totalFee") is not None:
            total_fee_msat = btc_money_to_msat(
                data.get("totalFee"), "legacy payment totalFee"
            )
            if total_fee_msat != fee_msat:
                raise StrikeContractError("legacy payment fee fields disagree")
        return fee_msat

    async def _status_for_attempt(  # noqa: C901
        self, attempt: StrikePaymentAttempt
    ) -> PaymentResponse:
        """Reconcile status without creating or dispatching a new payment intent."""
        if attempt.phase in {
            StrikePaymentPhase.COMPLETED.value,
            StrikePaymentPhase.FAILED.value,
            StrikePaymentPhase.QUOTE_ABANDONED.value,
        }:
            return await self._continue_payment(attempt)
        if attempt.payment_id:
            return await self._reconcile_payment(attempt)

        if attempt.phase == StrikePaymentPhase.EXECUTE_DISPATCHED.value:
            payment_hash = attempt.payment_hash
            existing = self._execution_tasks.get(payment_hash)
            if existing and not existing.done():
                return await asyncio.shield(existing)
            stale_before = utcnow() - timedelta(
                seconds=EXECUTION_LEASE_SECONDS
            )
            stale_attempt = (
                await self.store.mark_execution_ambiguous_if_stale(
                    payment_hash,
                    stale_before=stale_before,
                )
            )
            if not stale_attempt:
                current = await self.store.get_payment_attempt(payment_hash)
                if current and current.payment_id:
                    return await self._reconcile_payment(current)
                if current and current.phase in {
                    StrikePaymentPhase.COMPLETED.value,
                    StrikePaymentPhase.FAILED.value,
                }:
                    return await self._continue_payment(current)
                return StrikePaymentResponse(ok=None, checking_id=payment_hash)
            attempt = stale_attempt

        if attempt.phase == StrikePaymentPhase.AMBIGUOUS.value:
            if (
                not attempt.quote_valid_until
                or attempt.quote_valid_until
                <= utcnow() + timedelta(seconds=QUOTE_EXECUTION_MARGIN_SECONDS)
                or attempt.execute_attempts >= MAX_EXECUTE_ATTEMPTS
            ):
                return StrikePaymentResponse(
                    ok=None,
                    checking_id=attempt.payment_hash,
                    error_message="Strike payment requires manual reconciliation.",
                )
            return await self._execute_with_tracking(attempt)

        if attempt.phase == StrikePaymentPhase.QUOTE_CREATED.value:
            stale_before = utcnow() - timedelta(
                seconds=QUOTE_CREATION_LEASE_SECONDS
            )
            released = await self.store.release_quote_creation_claim(
                attempt,
                stale_before=stale_before,
            )
            return StrikePaymentResponse(
                ok=None,
                checking_id=(released or attempt).payment_hash,
            )

        if attempt.phase in {
            StrikePaymentPhase.QUOTE_INTENT_PERSISTED.value,
            StrikePaymentPhase.FEE_APPROVED.value,
        }:
            stale_before = utcnow() - timedelta(
                seconds=PREDISPATCH_GRACE_SECONDS
            )
            abandoned = await self.store.abandon_predispatch_if_stale(
                attempt.payment_hash,
                attempt.phase,
                stale_before=stale_before,
            )
            if abandoned:
                return StrikePaymentResponse(
                    ok=False,
                    checking_id=abandoned.payment_hash,
                    error_message="Strike payment stopped before quote execution.",
                )
            return StrikePaymentResponse(ok=None, checking_id=attempt.payment_hash)

        return StrikePaymentResponse(
            ok=None,
            checking_id=attempt.payment_hash,
            error_message="Strike payment requires manual reconciliation.",
        )

    @staticmethod
    def _payment_status_from_response(response: PaymentResponse) -> PaymentStatus:
        if response.success:
            return PaymentSuccessStatus(
                fee_msat=response.fee_msat,
                preimage=response.preimage,
            )
        if response.failed:
            return PaymentFailedStatus()
        return PaymentPendingStatus()

    def _invoice_status_from_page(  # noqa: C901
        self,
        data: Any,
        receive_request_id: str,
        expected_payment_hash: str | None,
        expected_amount_msat: int | None,
    ) -> PaymentStatus:
        if not isinstance(data, dict) or not isinstance(data.get("items"), list):
            raise StrikeContractError("invalid receives response")
        if expected_payment_hash is None or expected_amount_msat is None:
            return PaymentPendingStatus()
        for item in data["items"]:
            if not isinstance(item, dict):
                continue
            item_request_id = item.get("receiveRequestId")
            if item_request_id != receive_request_id:
                continue
            try:
                receive = parse_receive_data(item, receive_request_id)
            except StrikeContractError:
                continue
            if receive.state != StrikeReceiveState.COMPLETED.value:
                continue
            if (
                expected_payment_hash
                and receive.payment_hash
                and receive.payment_hash != expected_payment_hash
            ):
                logger.critical(
                    "Strike completed receive payment hash does not match its request."
                )
                continue
            if (
                expected_amount_msat is not None
                and receive.amount_msat != expected_amount_msat
            ):
                logger.critical(
                    "Strike completed receive amount does not match its request."
                )
                continue
            if receive.preimage_error:
                logger.error(
                    "Strike completed receive returned an unusable preimage: "
                    f"{receive.preimage_error}"
                )
            return PaymentSuccessStatus(fee_msat=0, preimage=receive.preimage)
        return PaymentPendingStatus()

    async def _get_completed_receives(
        self, receive_requests: list[StrikeReceiveRequest]
    ) -> set[str]:
        if len(receive_requests) > 100:
            raise ValueError("Strike receive status batch exceeds 100 items.")
        by_id: dict[str, StrikeReceiveRequest] = {}
        for candidate in receive_requests:
            tracked = candidate
            if candidate.payment_hash is None or candidate.amount_msat is None:
                tracked = await self._bound_receive_request(
                    candidate.receive_request_id
                )
            if tracked:
                by_id[tracked.receive_request_id] = tracked
        if not by_id:
            return set()
        params = [("$receiveRequestId", request_id) for request_id in by_id]
        completed: set[str] = set()
        async for page in self._receive_pages("/receive-requests/receives", params):
            for request_id, expected in by_id.items():
                status = self._invoice_status_from_page(
                    page, request_id, expected.payment_hash, expected.amount_msat
                )
                if status.success:
                    completed.add(request_id)
            if completed == set(by_id):
                break
        if completed:
            self._invalidate_balance_cache()
        return completed

    async def _receive_pages(
        self, path: str, filters: list[tuple[str, str]]
    ) -> AsyncGenerator[dict[str, Any], None]:
        # A batch can contain more receives than receive requests. Do not infer
        # completeness from the number of requested IDs or assume one page.
        seen: set[str] = set()
        for skip in range(0, 10000, 100):
            params = [*filters, ("$top", "100"), ("$skip", str(skip))]
            response = await self._request(
                "GET", path, retry_safe=True, params=params
            )
            if not response.is_success:
                self._log_api_error(
                    "read receives", StrikeApiError.from_response(response)
                )
                raise StrikeContractError("Strike receive query failed")
            data = self._response_json(response)
            if not isinstance(data, dict) or not isinstance(data.get("items"), list):
                raise StrikeContractError("invalid receives response")
            items = data["items"]
            if len(items) > 100:
                raise StrikeContractError("Strike receive page exceeds requested size")
            encoded = json.dumps(items, sort_keys=True).encode()
            digest = hashlib.sha256(encoded).hexdigest()
            if digest in seen:
                raise StrikeContractError("Strike receive pagination made no progress")
            seen.add(digest)
            yield data
            if len(items) < 100:
                return
        raise StrikeContractError("Strike receive pagination requires operator review")

    async def _get_payment_lock(self, payment_hash: str) -> asyncio.Lock:
        async with self._payment_locks_guard:
            lock = self._payment_locks.get(payment_hash)
            if lock is None:
                lock = asyncio.Lock()
                self._payment_locks[payment_hash] = lock
            return lock

    async def _request(
        self,
        method: str,
        path: str,
        *,
        retry_safe: bool,
        **kwargs: Any,
    ) -> httpx.Response:
        method = method.upper()
        self._validate_retry_policy(method, path, retry_safe, kwargs)
        kwargs.setdefault("timeout", self._timeout_for_request(method, path))
        attempts = (
            min(4, max(1, settings.funding_source_max_retries + 1))
            if retry_safe else 1
        )
        for attempt_number in range(attempts):
            self._check_request_available()
            await self._limiter_for_path(path).consume()
            self._check_request_available()
            try:
                async with self._sem:
                    response = await self._bounded_request(method, path, **kwargs)
            except httpx.TransportError:
                if attempt_number + 1 == attempts:
                    raise
                await asyncio.sleep(self._backoff_seconds(attempt_number))
                continue
            delay = self._retry_delay(response, attempt_number)
            self._remember_retry_after(response, delay)
            if not retry_safe or not self._retryable_response(response):
                return response
            if attempt_number + 1 == attempts or delay > MAX_INLINE_RETRY_SECONDS:
                return response
            await asyncio.sleep(delay)
        raise RuntimeError("Strike request retry budget exhausted.")

    def _check_request_available(self) -> None:
        if self._closed:
            raise httpx.RequestError("Strike wallet is closed")
        if time.monotonic() < self._retry_not_before:
            raise httpx.RequestError("Strike API cooldown is in effect")

    def _remember_retry_after(self, response: httpx.Response, delay: float) -> None:
        if response.status_code not in {429, 503}:
            return
        retry_after = response.headers.get("retry-after")
        if response.status_code == 429 and (
            not retry_after or self._parse_retry_after(retry_after) is None
        ):
            delay = (
                3600 if self.endpoint.environment == StrikeEnvironment.SANDBOX
                else 900
            )
        self._retry_not_before = max(self._retry_not_before, time.monotonic() + delay)

    async def _bounded_request(
        self, method: str, path: str, **kwargs: Any
    ) -> httpx.Response:
        async def read_response() -> httpx.Response:
            kwargs["follow_redirects"] = False
            async with self.client.stream(method, path, **kwargs) as response:
                if response.is_redirect:
                    response.raise_for_status()
                content = bytearray()
                async for chunk in response.aiter_bytes(chunk_size=16384):
                    if len(content) + len(chunk) > MAX_RESPONSE_BYTES:
                        raise StrikeContractError("Strike response exceeds size limit")
                    content.extend(chunk)
                headers = dict(response.headers)
                headers.pop("content-encoding", None)
                headers["content-length"] = str(len(content))
                return httpx.Response(
                    response.status_code, headers=headers, content=bytes(content),
                    request=response.request,
                )
        try:
            return await asyncio.wait_for(read_response(), timeout=60)
        except asyncio.TimeoutError as exc:
            raise httpx.ReadTimeout("Strike request exceeded its time limit") from exc

    @staticmethod
    def _validate_retry_policy(
        method: str,
        path: str,
        retry_safe: bool,
        kwargs: dict[str, Any],
    ) -> None:
        if not retry_safe or method == "GET":
            return
        if method == "POST" and path == "/payment-quotes/lightning":
            headers = kwargs.get("headers")
            if isinstance(headers, dict) and headers.get("idempotency-key"):
                return
        raise ValueError("Unsafe Strike request cannot use automatic retries.")

    @staticmethod
    def _timeout_for_request(method: str, path: str) -> httpx.Timeout:
        if method == "PATCH" and path.endswith("/execute"):
            return httpx.Timeout(connect=5.0, read=40.0, write=10.0, pool=5.0)
        if method == "POST":
            return httpx.Timeout(connect=5.0, read=30.0, write=10.0, pool=5.0)
        return httpx.Timeout(connect=5.0, read=20.0, write=10.0, pool=5.0)

    def _limiter_for_path(self, path: str) -> TokenBucket:
        if path == "/payment-quotes/lightning" or path.endswith("/execute"):
            return self._payment_limiter
        return self._general_limiter

    @staticmethod
    def _retryable_response(response: httpx.Response) -> bool:
        return response.status_code in {
            408,
            409,
            425,
            429,
            500,
            502,
            503,
            504,
        }

    def _retry_delay(self, response: httpx.Response, attempt_number: int) -> float:
        retry_after = response.headers.get("retry-after")
        if retry_after:
            parsed = self._parse_retry_after(retry_after)
            if parsed is not None:
                return parsed
        return self._backoff_seconds(attempt_number)

    @staticmethod
    def _parse_retry_after(value: str) -> float | None:
        try:
            seconds = float(value)
            return max(0.0, seconds) if math.isfinite(seconds) else None
        except ValueError:
            try:
                retry_time = parsedate_to_datetime(value)
                if retry_time.tzinfo is None:
                    retry_time = retry_time.replace(tzinfo=timezone.utc)
                seconds = (retry_time - datetime.now(timezone.utc)).total_seconds()
                return max(0.0, seconds)
            except (TypeError, ValueError, OverflowError):
                return None

    @staticmethod
    def _backoff_seconds(attempt_number: int) -> float:
        jitter = secrets.randbelow(250) / 1000
        return min(2.0, 0.25 * (2**attempt_number) + jitter)

    @staticmethod
    def _response_json(response: httpx.Response) -> Any:
        if len(response.content) > MAX_RESPONSE_BYTES:
            raise StrikeContractError("Strike response is too large")
        try:
            return response.json()
        except ValueError as exc:
            raise StrikeContractError("Strike returned invalid JSON") from exc

    @staticmethod
    def _record_error(
        attempt: StrikePaymentAttempt, error: StrikeApiError
    ) -> None:
        attempt.last_http_status = error.status_code
        attempt.last_error_code = error.code
        attempt.last_trace_id = error.trace_id

    @staticmethod
    def _log_api_error(operation: str, error: StrikeApiError) -> None:
        logger.warning(
            "Strike API error "
            f"operation={operation} status={error.status_code} "
            f"code={error.code or 'unknown'} trace_id={error.trace_id or 'unknown'}"
        )

    def _invalidate_balance_cache(self) -> None:
        self._cached_balance = None
        self._cached_balance_ts = 0.0
