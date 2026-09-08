#!/usr/bin/env python3
"""Verify the canonical CMV full-domain scalar certificates exactly.

The two JSON files contain retained directed-MPFR interval ledgers. This
verifier checks their exact dyadic endpoints, complete adjacency ledgers, sign
fields, artifact hashes, source identity, and the rational inequalities used
by the analytic large-density tail. Decimal display fields are never trusted.
It does not independently recompute the transcendental enclosures, so the
claimed full-domain sign remains conditional on the retained generators and
equal-area reduction.
"""

from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
LOW = HERE / "full_domain_low_certificate.json"
COMPACT = HERE / "full_domain_compact_certificate.json"
SOURCE = HERE.parent / "references" / "Canete2010.pdf"
EXPECTED_LOW_SHA256 = "7da2f8504583bafb4dbba8a150c3d12f1fb5014d25c9aef3d22c5bc8a0447f60"
EXPECTED_COMPACT_SHA256 = (
    "f35daee5bee3b7d51a49d77860e7fbf0ce749f8d2ad8f4a4b91ed6f3824664c7"
)
EXPECTED_SOURCE_SHA256 = (
    "0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def endpoint(value: dict[str, Any]) -> Fraction:
    return Fraction(int(value["numerator"]), 1 << int(value["denominator_power"]))


def interval(value: dict[str, Any]) -> tuple[Fraction, Fraction]:
    return endpoint(value["lower"]), endpoint(value["upper"])


def negative_upper(entry: dict[str, Any], key: str) -> bool:
    return endpoint(entry[key]["upper"]) < 0


def check_low_density(data: dict[str, Any]) -> None:
    assert data["schema"] == "cmv-scaled-interval-certificate-v2"
    assert data["precision_bits"] == 224
    conclusion = data["unconditional_conclusion"]
    assert conclusion["all_checked_interval_dependencies_passed"] is True
    assert all(conclusion["checked_interval_dependencies"].values())

    tail = data["tail"]
    compact = data["compact_coverage"]
    boxes = compact["boxes"]
    all_boxes = [tail, *boxes]
    assert interval(tail["t"]) == (Fraction(0), Fraction(1, 256))
    assert interval(compact["range"]) == (Fraction(1, 256), Fraction(13, 32))
    assert len(boxes) == compact["terminal_box_count"] == 107
    assert compact["certified_negative_count"] == 107
    assert compact["K3_transition_certified_negative_count"] == 107
    assert compact["coverage_complete"] is True
    assert compact["unresolved_count"] == 0
    assert compact["all_adjacencies_exact"] is True
    assert compact["adjacency_count"] == compact["expected_adjacency_count"] == 106

    t_boxes = [interval(item["t"]) for item in all_boxes]
    assert t_boxes[0][0] == 0 and t_boxes[-1][1] == Fraction(13, 32)
    assert all(lo < hi for lo, hi in t_boxes)
    assert all(
        t_boxes[index][1] == t_boxes[index + 1][0] for index in range(len(t_boxes) - 1)
    )
    assert all(negative_upper(item, "Gamma_over_t4") for item in all_boxes)
    assert all(item["K3_at_h3_1_minus_t2_over_2_sign"] == -1 for item in all_boxes)
    assert all(
        item["fold_root_receipt"]["endpoint_signs"] == [1, -1] for item in all_boxes
    )
    assert all(
        item["equal_area_root_receipt"]["endpoint_signs"] == [-1, 1]
        for item in all_boxes
    )
    assert Fraction(1) + Fraction(13, 32) ** 3 > Fraction(17, 16)
    assert endpoint(data["global_Gamma_over_t4_upper_bound"]) < 0

    print(
        "EXACT low_t=[0,13/32] entries=108 adjacencies=107/107 "
        "K3_negative=108/108 Gamma_scaled_upper_negative=108/108"
    )


def check_compact_density(data: dict[str, Any]) -> None:
    coverage = data["adaptive_compact_coverage"]
    boxes = coverage["certified_boxes"]
    lambda_boxes = [interval(item["lambda"]) for item in boxes]
    assert data["precision_bits"] == 224
    assert data["self_tests"]["all_passed"] is True
    assert coverage["coverage_complete"] is True
    assert coverage["unresolved_count"] == 0
    assert len(boxes) == coverage["certified_count"] == 127
    assert lambda_boxes[0][0] == Fraction(17, 16)
    assert lambda_boxes[-1][1] == Fraction(3, 2)
    assert all(lo < hi for lo, hi in lambda_boxes)
    assert all(
        lambda_boxes[index][1] == lambda_boxes[index + 1][0]
        for index in range(len(lambda_boxes) - 1)
    )
    assert all(negative_upper(item, "Gamma_gap") for item in boxes)
    assert all(item["gap_sign"] == -1 for item in boxes)
    assert all(item["descending_branch_K3_sign"] == -1 for item in boxes)
    print(
        "EXACT compact_lambda=[17/16,3/2] boxes=127 "
        "adjacencies=126/126 Gamma_upper_negative=127/127"
    )


def check_large_density_analytic_margins() -> None:
    # A3(3/5)-A4(1) > 205*pi/288-2 and 3 < pi.
    area_margin = Fraction(205 * 3, 288) - 2
    assert area_margin == Fraction(13, 96) > 0

    # asin(2/15) < 2/sqrt(221) < 3/16 < pi/16.
    assert 4 * 16 * 16 < 9 * 221

    # cos(5/6) exceeds this alternating-Taylor lower bound, itself > 2/3.
    x = Fraction(5, 6)
    cosine_lower = 1 - x**2 / 2 + x**4 / 24 - x**6 / 720
    assert cosine_lower - Fraction(2, 3) == Fraction(38563, 6718464) > 0

    # sqrt(5)>11/5 and 3<pi<22/7 imply
    # j(2/3)>5/6+22/45=119/90>55/42>5*pi/12.
    assert Fraction(121, 25) < 5
    j_margin = Fraction(119, 90) - Fraction(55, 42)
    assert j_margin == Fraction(4, 315) > 0

    # K3(3/5)<72/(25*sqrt(24))-2*pi <18/25-6<0.
    lower_square, radicand = 16, 24
    assert lower_square < radicand
    k3_upper = Fraction(18, 25) - 6
    assert k3_upper < 0
    print(
        "EXACT large_lambda_tail=analytic Gamma_strictly_decreasing_on_[3/2,infinity) "
        f"area_margin>{area_margin} j_margin>{j_margin} K3_upper<{k3_upper}"
    )


def check_hashes() -> None:
    low_digest = sha256(LOW)
    compact_digest = sha256(COMPACT)
    source_digest = sha256(SOURCE)
    assert low_digest == EXPECTED_LOW_SHA256
    assert compact_digest == EXPECTED_COMPACT_SHA256
    assert source_digest == EXPECTED_SOURCE_SHA256
    print(f"HASH low={low_digest}")
    print(f"HASH compact={compact_digest}")
    print(f"HASH source={source_digest}")


def main() -> int:
    low = json.loads(LOW.read_text(encoding="utf-8"))
    compact = json.loads(COMPACT.read_text(encoding="utf-8"))
    check_low_density(low)
    check_compact_density(compact)
    check_large_density_analytic_margins()
    check_hashes()
    print("FULL_DOMAIN_LEDGER_RESULT=PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
