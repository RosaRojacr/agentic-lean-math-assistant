from __future__ import annotations

from email.message import Message
from fractions import Fraction
from pathlib import Path
from urllib.request import Request

import pytest
import sympy as sp

from agentic_lean_math_assistant.math_tools import (
    RootBracket,
    bisect_root,
    bracket_sign_changes,
    check_identity,
    decimal_fraction,
    interval_horner,
    outward_decimal_interval,
)
from agentic_lean_math_assistant.math_tools.references import (
    _HttpsRedirectHandler,
    download_reference,
)


def test_decimal_conversion_and_outward_enclosure_are_exact() -> None:
    value = decimal_fraction("-12.3400")
    lower, upper = outward_decimal_interval(Fraction(1, 3), 4)

    assert value == Fraction(-617, 50)
    assert lower == Fraction(3333, 10_000)
    assert upper == Fraction(1667, 5000)
    assert lower <= Fraction(1, 3) <= upper


def test_interval_horner_contains_every_endpoint_value() -> None:
    lower, upper = interval_horner(
        [Fraction(1), Fraction(-3), Fraction(2)],
        Fraction(0),
        Fraction(2),
    )

    values = [x * x - 3 * x + 2 for x in (Fraction(0), Fraction(1), Fraction(2))]
    assert all(lower <= value <= upper for value in values)


def test_sign_scan_and_bisection_retain_a_certified_bracket() -> None:
    function = lambda x: x * x - 2
    brackets = bracket_sign_changes(function, [0, 1, 2, 3])
    narrowed = bisect_root(function, brackets[0], absolute_tolerance=1e-10)

    assert len(brackets) == 1
    assert narrowed.right - narrowed.left <= 1e-10
    assert (
        narrowed.f_left == 0
        or narrowed.f_right == 0
        or narrowed.f_left * narrowed.f_right < 0
    )


def test_symbolic_identity_returns_a_visible_residual() -> None:
    x = sp.symbols("x")

    proved = check_identity((x + 1) ** 2, x**2 + 2 * x + 1)
    disproved = check_identity((x + 1) ** 2, x**2 + 1)

    assert proved.proved
    assert proved.residual == 0
    assert not disproved.proved
    assert sp.expand(disproved.residual) == 2 * x


def test_root_bracket_rejects_same_sign_endpoints() -> None:
    try:
        RootBracket(0.0, 1.0, 1.0, 2.0)
    except ValueError as exc:
        assert "opposite signs" in str(exc)
    else:
        raise AssertionError("same-sign endpoints were accepted")


def test_reference_download_rejects_non_https_before_creating_output(
    tmp_path: Path,
) -> None:
    destination = tmp_path / "reference.pdf"

    with pytest.raises(ValueError, match="reference URL must be absolute HTTPS"):
        download_reference("file:///etc/passwd", destination)

    assert not destination.exists()


def test_reference_redirect_cannot_downgrade_to_cleartext_http() -> None:
    handler = _HttpsRedirectHandler()

    with pytest.raises(
        ValueError, match="reference redirect URL must be absolute HTTPS"
    ):
        handler.redirect_request(
            Request("https://example.test/source.pdf"),
            None,
            302,
            "Found",
            Message(),
            "http://example.test/source.pdf",
        )
