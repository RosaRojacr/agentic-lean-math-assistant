#!/usr/bin/env python3
"""Independent exact checker for the compact CMV fold-gap certificate.

Only Python integers and fractions are used for proof decisions.  The checker
imports no producer code and rejects every unrecognised certificate field.
Square roots are enclosed by integer square-root inequalities.  Pi and atan
are enclosed by alternating series with the first omitted term.  The
principal asin/acos branches are reconstructed from sqrt and atan.  The
sin/cos routines use exact quadrant reduction followed by Taylor polynomials
with Lagrange remainders; their recomputation is part of every check even
though the CMV formulas below need only sqrt, asin, and acos.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
from typing import Any

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

SCHEMA = "cmv-compact-rational-certificate-v1"
TARGET_LO = Q(33, 32)
TARGET_HI = Q(9, 7)
NEAR_ONE_HI = Q(17, 16)
SQRT_BITS = 80
ATAN_TERMS = 36
TRIG_TERMS = 14

DIVISION_CHECKS = 0


def fail(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def parse_q(value: Any, label: str) -> Q:
    fail(isinstance(value, str), f"{label}: rational must be a string")
    parts = value.split("/")
    fail(len(parts) in (1, 2), f"{label}: malformed rational")
    try:
        numerator = int(parts[0])
        denominator = 1 if len(parts) == 1 else int(parts[1])
    except ValueError as exc:
        raise ValueError(f"{label}: malformed integer") from exc
    fail(denominator > 0, f"{label}: denominator is not positive")
    result = Q(numerator, denominator)
    fail(str(result) == value, f"{label}: rational is not canonical")
    return result


def qstr(value: Q) -> str:
    return str(value)

def coarse_down(value: Q, scale: int = 10**18) -> Q:
    scaled = value * scale
    return Q(scaled.numerator // scaled.denominator, scale)


def coarse_up(value: Q, scale: int = 10**18) -> Q:
    return -coarse_down(-value, scale)


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        fail(self.lo <= self.hi, "reversed interval")

    @staticmethod
    def point(value: Q | int) -> "I":
        q = Q(value)
        return I(q, q)

    def __add__(self, other: "I | Q | int") -> "I":
        o = as_i(other)
        return I(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self) -> "I":
        return I(-self.hi, -self.lo)

    def __sub__(self, other: "I | Q | int") -> "I":
        return self + (-as_i(other))

    def __rsub__(self, other: "I | Q | int") -> "I":
        return as_i(other) - self

    def __mul__(self, other: "I | Q | int") -> "I":
        o = as_i(other)
        values = (
            self.lo * o.lo,
            self.lo * o.hi,
            self.hi * o.lo,
            self.hi * o.hi,
        )
        return I(min(values), max(values))

    __rmul__ = __mul__

    def reciprocal(self) -> "I":
        global DIVISION_CHECKS
        DIVISION_CHECKS += 1
        fail(self.hi < 0 or self.lo > 0, "division denominator contains zero")
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other: "I | Q | int") -> "I":
        return self * as_i(other).reciprocal()

    def __rtruediv__(self, other: "I | Q | int") -> "I":
        return as_i(other) / self

    def square(self) -> "I":
        if self.lo >= 0:
            return I(self.lo * self.lo, self.hi * self.hi)
        if self.hi <= 0:
            return I(self.hi * self.hi, self.lo * self.lo)
        return I(Q(0), max(self.lo * self.lo, self.hi * self.hi))


def as_i(value: I | Q | int) -> I:
    return value if isinstance(value, I) else I.point(Q(value))


def sqrt_q(value: Q) -> I:
    """Binary enclosure proved by the two exact square comparisons below."""
    fail(value >= 0, "sqrt domain")
    if value == 0:
        return I.point(0)
    scale = 1 << SQRT_BITS
    k = math.isqrt((value.numerator * scale * scale) // value.denominator)
    while Q((k + 1) * (k + 1), scale * scale) <= value:
        k += 1
    while Q(k * k, scale * scale) > value:
        k -= 1
    lo, hi = Q(k, scale), Q(k + 1, scale)
    fail(lo * lo <= value < hi * hi, "sqrt enclosure proof failed")
    return I(lo, hi)


def sqrt_i(value: I) -> I:
    fail(value.lo >= 0, "sqrt interval domain")
    return I(sqrt_q(value.lo).lo, sqrt_q(value.hi).hi)


def atan_small_nonnegative(value: Q) -> I:
    """Alternating atan series; the remainder lies toward its next term."""
    fail(0 <= value <= Q(1, 2), "atan small range")
    total = Q(0)
    power = value
    square = value * value
    for k in range(ATAN_TERMS):
        term = power / (2 * k + 1)
        total = total + term if k % 2 == 0 else total - term
        power *= square
    omitted = power / (2 * ATAN_TERMS + 1)
    alternate = total + (omitted if ATAN_TERMS % 2 == 0 else -omitted)
    return I(min(total, alternate), max(total, alternate))


def atan_small(value: Q) -> I:
    if value >= 0:
        return atan_small_nonnegative(value)
    positive = atan_small_nonnegative(-value)
    return -positive


def pi_interval() -> I:
    """Machin identity pi = 16 atan(1/5) - 4 atan(1/239)."""
    return 16 * atan_small(Q(1, 5)) - 4 * atan_small(Q(1, 239))


PI = pi_interval()


def atan_q(value: Q) -> I:
    """Exact range reductions leave an alternating-series argument <= 1/2."""
    if value < 0:
        return -atan_q(-value)
    if value <= Q(1, 2):
        return atan_small(value)
    if value <= 2:
        reduced = (value - 1) / (value + 1)
        fail(abs(reduced) <= Q(1, 3), "atan pi/4 reduction")
        return PI / 4 + atan_small(reduced)
    return PI / 2 - atan_small(1 / value)


def atan_i(value: I) -> I:
    lower = atan_q(value.lo)
    upper = atan_q(value.hi)
    return I(lower.lo, upper.hi)


def asin_q(value: Q) -> I:
    """Principal asin reconstructed as atan(x/sqrt(1-x^2))."""
    fail(-1 <= value <= 1, "asin domain")
    if value < 0:
        return -asin_q(-value)
    if value == 0:
        return I.point(0)
    if value == 1:
        return PI / 2
    root = sqrt_q(1 - value * value)
    ratio = I.point(value) / root
    return atan_i(ratio)


def asin_i(value: I) -> I:
    fail(-1 <= value.lo <= value.hi <= 1, "asin interval domain")
    lower, upper = asin_q(value.lo), asin_q(value.hi)
    return I(lower.lo, upper.hi)


def acos_q(value: Q) -> I:
    """Principal acos, with branch fixed by acos(x)=pi/2-asin(x)."""
    fail(-1 <= value <= 1, "acos domain")
    return PI / 2 - asin_q(value)


def acos_i(value: I) -> I:
    fail(-1 <= value.lo <= value.hi <= 1, "acos interval domain")
    lower, upper = acos_q(value.hi), acos_q(value.lo)
    return I(lower.lo, upper.hi)


def sin_taylor_q(value: Q) -> I:
    fail(abs(value) <= PI.lo / 4, "sin reduced range")
    total = Q(0)
    factorial = 1
    power = value
    for k in range(TRIG_TERMS):
        if k:
            factorial *= (2 * k) * (2 * k + 1)
            power *= value * value
        term = power / factorial
        total = total + term if k % 2 == 0 else total - term
    degree = 2 * TRIG_TERMS - 1
    remainder = abs(value) ** (degree + 1) / math.factorial(degree + 1)
    return I(total - remainder, total + remainder)


def cos_taylor_q(value: Q) -> I:
    fail(abs(value) <= PI.lo / 4, "cos reduced range")
    total = Q(0)
    factorial = 1
    power = Q(1)
    for k in range(TRIG_TERMS):
        if k:
            factorial *= (2 * k - 1) * (2 * k)
            power *= value * value
        term = power / factorial
        total = total + term if k % 2 == 0 else total - term
    degree = 2 * TRIG_TERMS - 2
    remainder = abs(value) ** (degree + 1) / math.factorial(degree + 1)
    return I(total - remainder, total + remainder)


def sin_cos_q(value: Q) -> tuple[I, I]:
    """Reduce by an exact multiple of pi/2, then apply Taylor bounds."""
    choices: list[tuple[int, I]] = []
    for quadrant in range(-16, 17):
        reduced = I.point(value) - quadrant * PI / 2
        if -PI.lo / 4 <= reduced.lo and reduced.hi <= PI.lo / 4:
            choices.append((quadrant, reduced))
    fail(len(choices) == 1, "trig range reduction is not unique")
    quadrant, reduced = choices[0]

    # On [-pi/4,pi/4], sin is increasing.  Cos is even and decreases in |x|.
    sin_reduced = I(sin_taylor_q(reduced.lo).lo, sin_taylor_q(reduced.hi).hi)
    cos_lows = [cos_taylor_q(reduced.lo).lo, cos_taylor_q(reduced.hi).lo]
    if reduced.lo <= 0 <= reduced.hi:
        cos_reduced = I(min(cos_lows), Q(1))
    else:
        cos_highs = [cos_taylor_q(reduced.lo).hi, cos_taylor_q(reduced.hi).hi]
        cos_reduced = I(min(cos_lows), max(cos_highs))

    q = quadrant % 4
    if q == 0:
        return sin_reduced, cos_reduced
    if q == 1:
        return cos_reduced, -sin_reduced
    if q == 2:
        return -sin_reduced, -cos_reduced
    return -cos_reduced, sin_reduced


def type3(lam: I, h: I) -> tuple[I, I, I]:
    q = 2 * h - 1
    u = sqrt_i(1 - q.square())
    droot = sqrt_i(lam.square() - q.square())
    ratio = q / lam
    fail(-1 < ratio.lo and ratio.hi < 1, "type3 acos branch")
    alpha = acos_i(ratio)
    angle = lam * alpha + asin_i(q)
    delta = droot / lam - u
    area = (angle + PI / 2 + (q + 2) * delta) / h.square()
    perimeter = 2 * (angle + PI / 2 + delta) / h
    fold = 4 * h * ((1 + q) / u - (lam.square() + q) / (lam * droot))
    fold = fold - 2 * (angle + PI / 2 + delta)
    return area, perimeter, fold


def type4(lam: I, h: I) -> tuple[I, I, I]:
    u = sqrt_i(1 - h.square())
    droot = sqrt_i(lam.square() - h.square())
    ratio = h / lam
    fail(0 < ratio.lo and ratio.hi < 1, "type4 acos branch")
    alpha = acos_i(ratio)
    angle = lam * alpha + asin_i(h)
    delta = droot / lam - u
    area = 2 * (angle + h * delta) / h.square()
    perimeter = 4 * angle / h
    fold = 4 * (h * (1 / u - lam / droot) - angle)
    return area, perimeter, fold

def centered_type3(lam: I, h: I) -> tuple[I, I, I]:
    """Mean-value enclosure in h using A'=K/h^3 and P'=K/h^2."""
    center = (h.lo + h.hi) / 2
    area0, perimeter0, _ = type3(lam, I.point(center))
    _, _, fold = type3(lam, h)
    displacement = h - center
    area = area0 + fold / (h.square() * h) * displacement
    perimeter = perimeter0 + fold / h.square() * displacement
    return area, perimeter, fold


def centered_type4(lam: I, h: I) -> tuple[I, I, I]:
    """Mean-value enclosure in h using A'=K/h^3 and P'=K/h^2."""
    center = (h.lo + h.hi) / 2
    area0, perimeter0, _ = type4(lam, I.point(center))
    _, _, fold = type4(lam, h)
    displacement = h - center
    area = area0 + fold / (h.square() * h) * displacement
    perimeter = perimeter0 + fold / h.square() * displacement
    return area, perimeter, fold


def strict_increasing_proofs(lam: I, h3: I, h4: I) -> None:
    """Exact algebraic witnesses for K3'>0 and K4'>0 on each box.

    D4^2-(lambda*u4)^2 = h4^2(lambda^2-1)>0 and
    D3^2-(lambda*u3)^2 = q^2(lambda^2-1)>0.  Since all factors are
    positive, these imply 1/u^3-lambda/D^3>0.  The retained derivative
    identities then give K4'>0 and K3'>0.
    """
    fail(lam.lo > 1, "lambda derivative domain")
    q = 2 * h3 - 1
    fail(q.lo > 0, "K3 derivative q domain")
    witness4 = h4.square() * (lam.square() - 1)
    witness3 = q.square() * (lam.square() - 1)
    fail(witness4.lo > 0, "K4 derivative witness")
    fail(witness3.lo > 0, "K3 derivative witness")


def exact_elementary_self_check() -> None:
    """Exercise every elementary enclosure and its exact defining relation."""
    fail(PI.lo < PI.hi, "pi interval is not strict")
    fail(Q(333, 106) < PI.lo and PI.hi < Q(355, 113), "pi rational bounds")

    root = sqrt_q(Q(2))
    fail(root.lo * root.lo <= 2 < root.hi * root.hi, "sqrt(2)")

    x = Q(1, 3)
    sine, cosine = sin_cos_q(x)
    fail(-1 < sine.lo < sine.hi < 1, "sin enclosure")
    fail(0 < cosine.lo < cosine.hi <= 1, "cos enclosure")

    arcsine = asin_q(x)
    arccosine = acos_q(x)
    fail(arcsine.lo > 0 and arccosine.lo > 0, "inverse trig branches")
    sum_angles = arcsine + arccosine
    fail(sum_angles.lo <= PI.hi / 2 and PI.lo / 2 <= sum_angles.hi,
         "asin/acos complement")


def canonical_payload(boxes: list[dict[str, Any]]) -> bytes:
    return json.dumps(boxes, sort_keys=True, separators=(",", ":")).encode()


def check_keys(value: dict[str, Any], expected: set[str], label: str) -> None:
    fail(set(value) == expected, f"{label}: fields {sorted(set(value))} != {sorted(expected)}")


def read_interval(value: Any, label: str) -> I:
    fail(isinstance(value, list) and len(value) == 2, f"{label}: expected pair")
    return I(parse_q(value[0], label + ".lo"), parse_q(value[1], label + ".hi"))


def check_certificate(data: Any) -> dict[str, Any]:
    global DIVISION_CHECKS
    DIVISION_CHECKS = 0
    exact_elementary_self_check()

    fail(isinstance(data, dict), "certificate root must be an object")
    check_keys(data, {"schema", "target", "precision", "boxes", "payload_sha256"}, "root")
    fail(data["schema"] == SCHEMA, "schema mismatch")

    target = data["target"]
    fail(isinstance(target, dict), "target object")
    check_keys(target, {"lambda_lower", "lambda_upper"}, "target")
    fail(parse_q(target["lambda_lower"], "target.lambda_lower") == TARGET_LO,
         "target lower mismatch")
    fail(parse_q(target["lambda_upper"], "target.lambda_upper") == TARGET_HI,
         "target upper mismatch")

    precision = data["precision"]
    fail(isinstance(precision, dict), "precision object")
    check_keys(precision, {"sqrt_bits", "atan_terms", "trig_terms"}, "precision")
    fail(precision == {
        "sqrt_bits": SQRT_BITS,
        "atan_terms": ATAN_TERMS,
        "trig_terms": TRIG_TERMS,
    }, "precision mismatch")

    boxes = data["boxes"]
    fail(isinstance(boxes, list) and boxes, "empty boxes")
    digest = hashlib.sha256(canonical_payload(boxes)).hexdigest()
    fail(data["payload_sha256"] == digest, "payload hash mismatch")

    previous = TARGET_LO
    global_gap_upper: Q | None = None
    global_gap_lower: Q | None = None
    minimum_fold_margin: Q | None = None
    minimum_area_margin: Q | None = None
    for index, row in enumerate(boxes):
        label = f"box[{index}]"
        fail(isinstance(row, dict), f"{label}: object required")
        # No serialized signs or elementary enclosures are accepted.
        check_keys(row, {"lambda", "h4_root", "h3_root"}, label)
        lam = read_interval(row["lambda"], label + ".lambda")
        h4 = read_interval(row["h4_root"], label + ".h4_root")
        h3 = read_interval(row["h3_root"], label + ".h3_root")

        fail(lam.lo == previous, f"{label}: coverage gap or overlap")
        fail(lam.lo < lam.hi, f"{label}: empty lambda box")
        previous = lam.hi
        fail(TARGET_LO <= lam.lo and lam.hi <= TARGET_HI, f"{label}: target escape")
        fail(0 < h4.lo < h4.hi < 1, f"{label}: h4 domain")
        fail(Q(1, 2) < h3.lo < h3.hi < 1, f"{label}: descending h3 domain")
        strict_increasing_proofs(lam, h3, h4)

        # K4 is strictly increasing.  Opposite endpoint signs prove one and
        # only one fold root for every lambda in this lambda box.
        _, _, k4_low = type4(lam, I.point(h4.lo))
        _, _, k4_high = type4(lam, I.point(h4.hi))
        fail(k4_low.hi < 0, f"{label}: fold lower sign unresolved ({float(k4_low.hi):.6g})")
        fail(k4_high.lo > 0, f"{label}: fold upper sign unresolved ({float(k4_high.lo):.6g})")
        fold_margin = min(-k4_low.hi, k4_high.lo)
        minimum_fold_margin = fold_margin if minimum_fold_margin is None else min(
            minimum_fold_margin, fold_margin)

        # The h4 interval contains that fold root.  On the h3 descending
        # branch A3 is strictly decreasing because K3<0.  The endpoint area
        # signs therefore isolate exactly one designated equal-area root.
        area4, perimeter4, _ = centered_type4(lam, h4)
        area3_low, _, _ = type3(lam, I.point(h3.lo))
        area3_high, _, k3_high = type3(lam, I.point(h3.hi))
        equal_low = area3_low - area4
        equal_high = area3_high - area4
        fail(equal_low.lo > 0,
             f"{label}: equal-area lower sign unresolved ({float(equal_low.lo):.6g})")
        fail(equal_high.hi < 0,
             f"{label}: equal-area upper sign unresolved ({float(equal_high.hi):.6g})")
        fail(k3_high.hi < 0,
             f"{label}: descending K3 sign unresolved ({float(k3_high.hi):.6g})")
        area_margin = min(equal_low.lo, -equal_high.hi, -k3_high.hi)
        minimum_area_margin = area_margin if minimum_area_margin is None else min(
            minimum_area_margin, area_margin)

        _, perimeter3, _ = centered_type3(lam, h3)
        gap = perimeter3 - perimeter4
        fail(gap.hi < 0, f"{label}: gap upper bound is not strict ({float(gap.hi):.6g})")
        global_gap_upper = gap.hi if global_gap_upper is None else max(global_gap_upper, gap.hi)
        global_gap_lower = gap.lo if global_gap_lower is None else min(global_gap_lower, gap.lo)

    fail(previous == TARGET_HI, "coverage does not reach target upper endpoint")

    # Exact overlap with the accepted near-one target and exact containment
    # of 4/pi in the compact interval.  The endpoint inequalities are
    # 33*pi < 128 and 28 < 9*pi.
    fail(TARGET_LO < NEAR_ONE_HI, "near-one overlap is empty")
    lower_pi_margin = 128 - 33 * PI.hi
    upper_pi_margin = 9 * PI.lo - 28
    fail(lower_pi_margin > 0, "failed to prove 33/32 < 4/pi")
    fail(upper_pi_margin > 0, "failed to prove 4/pi < 9/7")

    assert global_gap_upper is not None and global_gap_lower is not None
    assert minimum_fold_margin is not None and minimum_area_margin is not None
    receipt_gap_lower = coarse_down(global_gap_lower)
    receipt_gap_upper = coarse_up(global_gap_upper)
    receipt_fold_margin = coarse_down(minimum_fold_margin)
    receipt_area_margin = coarse_down(minimum_area_margin)
    fail(receipt_gap_upper < 0, "coarse gap receipt lost strictness")
    fail(receipt_fold_margin > 0, "coarse fold receipt lost strictness")
    fail(receipt_area_margin > 0, "coarse equal-area receipt lost strictness")
    rational_upper_pi_margin = 9 * Q(333, 106) - 28
    rational_lower_pi_margin = 128 - 33 * Q(355, 113)
    fail(rational_upper_pi_margin > 0, "rational upper pi receipt margin")
    fail(rational_lower_pi_margin > 0, "rational lower pi receipt margin")
    return {
        "status": "PASS",
        "schema": SCHEMA,
        "python": platform.python_version(),
        "boxes": len(boxes),
        "coverage": [qstr(TARGET_LO), qstr(TARGET_HI)],
        "adjacencies": len(boxes) - 1,
        "unresolved_boxes": 0,
        "roots": {
            "fold_existence_unique": len(boxes),
            "equal_area_existence_unique": len(boxes),
        },
        "global_gap": [qstr(receipt_gap_lower), qstr(receipt_gap_upper)],
        "minimum_fold_sign_margin": qstr(receipt_fold_margin),
        "minimum_equal_area_sign_margin": qstr(receipt_area_margin),
        "pi_proof_bounds": ["333/106", "355/113"],
        "four_over_pi_interior_margins": {
            "128_minus_33_pi_upper": qstr(rational_lower_pi_margin),
            "nine_pi_lower_minus_28": qstr(rational_upper_pi_margin),
        },
        "near_one_overlap": [qstr(TARGET_LO), qstr(NEAR_ONE_HI)],
        "division_denominator_checks": DIVISION_CHECKS,
        "payload_sha256": digest,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    try:
        with args.certificate.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
        receipt = check_certificate(data)
    except (OSError, json.JSONDecodeError, ValueError, ZeroDivisionError) as exc:
        print(f"FAIL {exc}", file=sys.stderr)
        return 1

    output = json.dumps(receipt, sort_keys=True, separators=(",", ":"))
    print(output)
    if args.receipt is not None:
        args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
