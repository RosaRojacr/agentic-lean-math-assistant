"""Exact decimal and rational enclosure helpers."""

from __future__ import annotations

from decimal import Decimal, InvalidOperation
from fractions import Fraction


def decimal_fraction(value: str | Decimal) -> Fraction:
    """Convert a finite decimal to its exact reduced rational value."""

    try:
        decimal = value if isinstance(value, Decimal) else Decimal(value)
    except InvalidOperation as exc:
        raise ValueError(f"invalid decimal: {value!r}") from exc
    if not decimal.is_finite():
        raise ValueError("decimal must be finite")
    sign, digits, exponent = decimal.as_tuple()
    if not isinstance(exponent, int):
        raise TypeError("decimal exponent must be finite")
    numerator = 0
    for digit in digits:
        numerator = numerator * 10 + digit
    if sign:
        numerator = -numerator
    if exponent >= 0:
        return Fraction(numerator * 10**exponent, 1)
    return Fraction(numerator, 10 ** (-exponent))


def outward_decimal_interval(
    value: Fraction, decimal_places: int
) -> tuple[Fraction, Fraction]:
    """Return the tight decimal-grid enclosure of an exact rational."""

    if decimal_places < 0:
        raise ValueError("decimal_places must be nonnegative")
    scale = 10**decimal_places
    scaled_numerator = value.numerator * scale
    denominator = value.denominator
    lower_integer = scaled_numerator // denominator
    upper_integer = -(-scaled_numerator // denominator)
    return Fraction(lower_integer, scale), Fraction(upper_integer, scale)


def interval_horner(
    coefficients: tuple[Fraction, ...], lower: Fraction, upper: Fraction
) -> tuple[Fraction, Fraction]:
    """Enclose a polynomial on an interval using rational interval Horner evaluation."""

    if lower > upper:
        raise ValueError("interval lower bound exceeds upper bound")
    if not coefficients:
        return Fraction(0), Fraction(0)
    result_lower = coefficients[0]
    result_upper = coefficients[0]
    for coefficient in coefficients[1:]:
        products = (
            result_lower * lower,
            result_lower * upper,
            result_upper * lower,
            result_upper * upper,
        )
        result_lower = min(products) + coefficient
        result_upper = max(products) + coefficient
    return result_lower, result_upper
