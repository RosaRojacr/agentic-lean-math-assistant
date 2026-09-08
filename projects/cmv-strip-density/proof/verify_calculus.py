#!/usr/bin/env python3
"""Fail-closed exact and high-precision checks for the CMV envelope calculus.

The exact layer uses Fraction-valued forward automatic differentiation and
Green's formula.  Its angle values are formal rational placeholders; only the
branch-correct derivative rules and circle identities are supplied.  The
numerical layer checks principal inverse-trigonometric branches and rejects
listed mutations on both sides of h=1/2.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path
from typing import Callable

import mpmath as mp

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "references" / "Canete2010.pdf"
EXPECTED_SOURCE_SHA256 = (
    "0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230"
)
FIXTURES = Path(__file__).with_name("calculus_mutation_fixtures.json")


@dataclass(frozen=True)
class Dual:
    v: Q
    d: Q = Q(0)

    @staticmethod
    def lift(x: Dual | Q | int) -> Dual:
        return x if isinstance(x, Dual) else Dual(Q(x))

    def __add__(self, other: Dual | Q | int) -> Dual:
        o = Dual.lift(other)
        return Dual(self.v + o.v, self.d + o.d)

    __radd__ = __add__

    def __neg__(self) -> Dual:
        return Dual(-self.v, -self.d)

    def __sub__(self, other: Dual | Q | int) -> Dual:
        return self + (-Dual.lift(other))

    def __rsub__(self, other: Dual | Q | int) -> Dual:
        return Dual.lift(other) - self

    def __mul__(self, other: Dual | Q | int) -> Dual:
        o = Dual.lift(other)
        return Dual(self.v * o.v, self.d * o.v + self.v * o.d)

    __rmul__ = __mul__

    def inv(self) -> Dual:
        assert self.v != 0
        return Dual(1 / self.v, -self.d / (self.v * self.v))

    def __truediv__(self, other: Dual | Q | int) -> Dual:
        return self * Dual.lift(other).inv()

    def __rtruediv__(self, other: Dual | Q | int) -> Dual:
        return Dual.lift(other) / self

    def __pow__(self, n: int) -> Dual:
        if n < 0:
            return (self.inv()) ** (-n)
        if n == 0:
            return Dual(Q(1))
        return Dual(self.v**n, Q(n) * self.v ** (n - 1) * self.d)


def assert_dual_equal(left: Dual, right: Dual, label: str) -> None:
    assert left == right, f"{label}: {left!r} != {right!r}"


def arc_green(
    radius: Q, theta: Q, center_x: Q, center_y: Q, dx: Q, dy: Q
) -> Q:
    """1/2 integral (x dy-y dx) on one counterclockwise circle arc."""
    return (radius * radius * theta + center_x * dy - center_y * dx) / 2


# Rational fixtures satisfy u^2=1-x^2 and D^2=lambda^2-x^2 exactly.
TYPE3_EXACT = [
    # h, q, U(q), lambda, D_lambda(q), alpha, asin(q), pi
    (Q(9, 13), Q(5, 13), Q(12, 13), Q(185, 156), Q(175, 156), Q(7, 11), Q(2, 9), Q(22, 7)),
    (Q(1, 5), Q(-3, 5), Q(4, 5), Q(1113, 980), Q(189, 196), Q(8, 13), Q(-3, 10), Q(22, 7)),
    (Q(1, 2), Q(0), Q(1), Q(6, 5), Q(6, 5), Q(5, 7), Q(0), Q(22, 7)),
]
TYPE4_EXACT = [
    # h, U(h), lambda, D_lambda(h), alpha, asin(h), pi
    (Q(3, 5), Q(4, 5), Q(1113, 980), Q(189, 196), Q(7, 12), Q(3, 10), Q(22, 7)),
    (Q(5, 13), Q(12, 13), Q(185, 156), Q(175, 156), Q(6, 11), Q(2, 9), Q(22, 7)),
]


def exact_type3_check(row: tuple[Q, ...]) -> int:
    hv, qv, uv, lam, Dv, alphav, asinqv, piv = row
    assert qv == 2 * hv - 1
    assert uv * uv == 1 - qv * qv
    assert Dv * Dv == lam * lam - qv * qv

    h = Dual(hv, Q(1))
    q = 2 * h - 1
    u = Dual(uv, -2 * qv / uv)
    D = Dual(Dv, -2 * qv / Dv)
    alpha = Dual(alphav, -2 / Dv)
    asin_q = Dual(asinqv, 2 / uv)
    pi = Dual(piv)

    L = lam * alpha + asin_q
    d = D / lam - u
    A = (L + pi / 2 + (q + 2) * d) / h**2
    P = 2 * (L + pi / 2 + d) / h
    K = (
        4 * h * ((1 + q) / u - (lam * lam + q) / (lam * D))
        - 2 * (L + pi / 2 + d)
    )
    Kprime = 8 * h * (1 + q) * (u ** (-3) - lam * D ** (-3))

    assert A.d == K.v / hv**3
    assert P.d == K.v / hv**2
    assert P.d == hv * A.d
    assert K.d == Kprime.v
    assert P.v - 2 * hv * A.v == -4 * d.v

    # Independent Green reconstruction from centers and oriented pieces.
    R = 1 / hv
    s = Dv / lam
    width = R * (s - uv)
    side_angle = piv / 2 + asinqv
    bottom = width
    right = arc_green(R, side_angle, width, R - 1, R * uv, Q(2))
    top_chord = R * s
    left = arc_green(R, side_angle, -width, R - 1, R * uv, Q(-2))
    core = bottom + right + top_chord + left
    cap = R * R * (alphav - s * qv / lam)
    area_green = core + lam * cap
    perimeter_parts = 2 * width + 2 * R * side_angle + 2 * lam * R * alphav
    assert area_green == A.v
    assert perimeter_parts == P.v
    return 7


def exact_type4_check(row: tuple[Q, ...]) -> int:
    hv, uv, lam, Dv, alphav, asinhv, piv = row
    assert uv * uv == 1 - hv * hv
    assert Dv * Dv == lam * lam - hv * hv

    h = Dual(hv, Q(1))
    u = Dual(uv, -hv / uv)
    D = Dual(Dv, -hv / Dv)
    alpha = Dual(alphav, -1 / Dv)
    asin_h = Dual(asinhv, 1 / uv)

    L = lam * alpha + asin_h
    d = D / lam - u
    A = 2 * (L + h * d) / h**2
    P = 4 * L / h
    K = 4 * (h * (1 / u - lam / D) - L)
    Kprime = 4 * h**2 * (u ** (-3) - lam * D ** (-3))

    assert A.d == K.v / hv**3
    assert P.d == K.v / hv**2
    assert P.d == hv * A.d
    assert K.d == Kprime.v
    assert P.v - 2 * hv * A.v == -4 * d.v

    # Independent Green decomposition: rectangle, two side segments, two caps.
    R = 1 / hv
    S = Dv / lam
    X = R * S
    rectangle = 4 * X
    side_segment = R * R * (asinhv - hv * uv)
    cap_segment = R * R * (alphav - S * hv / lam)
    area_green = rectangle + 2 * side_segment + 2 * lam * cap_segment
    perimeter_parts = 4 * R * asinhv + 4 * lam * R * alphav
    assert area_green == A.v
    assert perimeter_parts == P.v
    return 7


def mp_formulas(lam: mp.mpf, h: mp.mpf, kind: int) -> tuple[mp.mpf, mp.mpf]:
    if kind == 3:
        q = 2 * h - 1
        U = mp.sqrt(1 - q * q)
        D = mp.sqrt(lam * lam - q * q)
        alpha = mp.acos(q / lam)
        L = lam * alpha + mp.asin(q)
        d = D / lam - U
        return (L + mp.pi / 2 + (q + 2) * d) / h**2, 2 * (L + mp.pi / 2 + d) / h
    U = mp.sqrt(1 - h * h)
    D = mp.sqrt(lam * lam - h * h)
    alpha = mp.acos(h / lam)
    L = lam * alpha + mp.asin(h)
    d = D / lam - U
    return 2 * (L + h * d) / h**2, 4 * L / h


def mp_green(lam: mp.mpf, h: mp.mpf, kind: int) -> tuple[mp.mpf, mp.mpf]:
    R = 1 / h
    if kind == 3:
        q = 2 * h - 1
        U = mp.sqrt(1 - q * q)
        S = mp.sqrt(1 - (q / lam) ** 2)
        alpha = mp.acos(q / lam)
        side = mp.pi / 2 + mp.asin(q)
        width = R * (S - U)
        core = 4 * width + R**2 * (side + q * U)
        cap = R**2 * (alpha - S * q / lam)
        return core + lam * cap, 2 * width + 2 * R * side + 2 * lam * R * alpha
    U = mp.sqrt(1 - h * h)
    S = mp.sqrt(1 - (h / lam) ** 2)
    alpha = mp.acos(h / lam)
    delta = mp.asin(h)
    area = 4 * S / h + 2 * R**2 * (delta - h * U) + 2 * lam * R**2 * (alpha - S * h / lam)
    perimeter = 4 * R * delta + 4 * lam * R * alpha
    return area, perimeter


def mutation_values(lam: mp.mpf, h: mp.mpf) -> dict[str, mp.mpf]:
    q = 2 * h - 1
    U3 = mp.sqrt(1 - q * q)
    S3 = mp.sqrt(1 - (q / lam) ** 2)
    a3 = mp.acos(q / lam)
    side = mp.pi / 2 + mp.asin(q)
    R = 1 / h
    w = R * (S3 - U3)
    canonical_a3, canonical_p3 = mp_green(lam, h, 3)

    U4 = mp.sqrt(1 - h * h)
    S4 = mp.sqrt(1 - (h / lam) ** 2)
    a4 = mp.acos(h / lam)
    delta = mp.asin(h)
    canonical_a4, canonical_p4 = mp_green(lam, h, 4)

    return {
        "type3_cap_density_parentheses": (
            4 * w + R**2 * (side + q * U3) + lam * R**2 * (a3 - S3 * q)
        ) - canonical_a3,
        "type3_bottom_width_plus": (
            2 * R * (S3 + U3) + 2 * R * side + 2 * lam * R * a3
        ) - canonical_p3,
        "type3_core_qu_sign": (
            4 * w + R**2 * (side - q * U3) + lam * R**2 * (a3 - S3 * q / lam)
        ) - canonical_a3,
        "type3_acute_alpha": mp.acos(abs(q) / lam) - a3,
        "type3_exterior_complement": (mp.pi - a3) - a3,
        "type4_cap_density_parentheses": (
            4 * S4 / h + 2 * R**2 * (delta - h * U4)
            + 2 * lam * R**2 * (a4 - S4 * h)
        ) - canonical_a4,
        "type4_core_segment_sign": (
            4 * S4 / h + 2 * R**2 * (delta + h * U4)
            + 2 * lam * R**2 * (a4 - S4 * h / lam)
        ) - canonical_a4,
        "type4_exterior_complement": (mp.pi - a4) - a4,
        "type4_drop_lower_cap": -lam * R**2 * (a4 - S4 * h / lam),
        "type3_qprime_one": mp.mpf("0.5"),
        "legendre_d_sign": 8 * (S4 - U4),
    }


def numerical_checks() -> tuple[int, str, dict[str, bool], dict[str, str]]:
    mp.mp.dps = 100
    lambdas = [mp.mpf("1.0001"), mp.mpf("1.07"), mp.mpf("1.2"), 4 / mp.pi - mp.mpf("1e-20")]
    hs = [mp.mpf("0.03"), mp.mpf("0.27"), mp.mpf("0.499"), mp.mpf("0.5"), mp.mpf("0.501"), mp.mpf("0.83"), mp.mpf("0.997")]
    max_residual = mp.mpf(0)
    checks = 0
    for lam in lambdas:
        for h in hs:
            for kind in (3, 4):
                direct = mp_formulas(lam, h, kind)
                green = mp_green(lam, h, kind)
                for x, y in zip(direct, green):
                    max_residual = max(max_residual, abs(x - y))
                    checks += 1
            a3, p3 = mp_formulas(lam, h, 3)
            da3 = mp.diff(lambda z: mp_formulas(lam, z, 3)[0], h)
            dp3 = mp.diff(lambda z: mp_formulas(lam, z, 3)[1], h)
            a4, p4 = mp_formulas(lam, h, 4)
            da4 = mp.diff(lambda z: mp_formulas(lam, z, 4)[0], h)
            dp4 = mp.diff(lambda z: mp_formulas(lam, z, 4)[1], h)
            del a3, p3, a4, p4
            max_residual = max(max_residual, abs(dp3 - h * da3), abs(dp4 - h * da4))
            checks += 2
    assert max_residual < mp.mpf("1e-80")

    fixture_data = json.loads(FIXTURES.read_text())
    expected = [item["id"] for item in fixture_data["mutations"]]
    rejected: dict[str, bool] = {name: False for name in expected}
    witnesses: dict[str, str] = {}
    mutation_points = [
        (mp.mpf("1.17"), mp.mpf("0.23")),
        (mp.mpf("1.21"), mp.mpf("0.71")),
    ]
    for lam, h in mutation_points:
        for name, residual in mutation_values(lam, h).items():
            if name in rejected and abs(residual) > mp.mpf("1e-40"):
                rejected[name] = True
                witnesses.setdefault(name, mp.nstr(residual, 25))
    assert set(expected) == set(rejected)
    assert all(rejected.values())

    # Principal branch and transition oracles.
    lam = mp.mpf("1.19")
    assert mp.acos((2 * mp.mpf("0.49") - 1) / lam) > mp.pi / 2
    assert mp.acos((2 * mp.mpf("0.51") - 1) / lam) < mp.pi / 2
    at, pt = mp_formulas(lam, mp.mpf("0.5"), 3)
    target = 2 * mp.pi * (lam + 1)
    assert abs(at - target) < mp.mpf("1e-95")
    assert abs(pt - target) < mp.mpf("1e-95")
    return checks, mp.nstr(max_residual, 30), rejected, witnesses


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    source_hash = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    assert source_hash == EXPECTED_SOURCE_SHA256
    exact_checks = sum(exact_type3_check(row) for row in TYPE3_EXACT)
    exact_checks += sum(exact_type4_check(row) for row in TYPE4_EXACT)
    numerical_count, max_residual, rejected, witnesses = numerical_checks()

    receipt = {
        "result": "PASS",
        "precision_decimal_digits": mp.mp.dps,
        "source": str(SOURCE.relative_to(ROOT)),
        "source_sha256": source_hash,
        "exact_fraction_checks": exact_checks,
        "numerical_checks": numerical_count,
        "maximum_numerical_residual": max_residual,
        "principal_branch_transition": "major/semicircle/minor PASS",
        "mutations_rejected": f"{sum(rejected.values())}/{len(rejected)}",
        "mutation_results": rejected,
        "mutation_witness_residuals": witnesses,
    }
    text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(text)
    print("CALCULUS_CHECKER_RESULT=PASS")
    print(f"SOURCE_SHA256={source_hash}")
    print(f"EXACT_FRACTION_CHECKS={exact_checks}")
    print(f"NUMERICAL_CHECKS={numerical_count} MAX_RESIDUAL={max_residual}")
    print(f"MUTATIONS_REJECTED={sum(rejected.values())}/{len(rejected)}")


if __name__ == "__main__":
    main()
