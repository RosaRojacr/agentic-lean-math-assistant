#!/usr/bin/env python3
"""Exact formal-series checker for the CMV near-one height germ.

Proof decisions use only Python integers and fractions.  The symbol `pi` is
an indeterminate, represented by a Laurent polynomial over Q.  Consequently
all reported cancellations are identities in Q[pi, pi^-1], not numerical
comparisons.  The sole sign decision uses pi > 0.
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
from typing import Iterable

SCHEMA = "cmv-exact-height-germ-pilot-v1"
JET_ORDER = 5
SERIES_ORDER = 14
EXPECTED_SOURCE_SHA256 = (
    "0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230"
)
ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "references" / "Canete2010.pdf"
FIXTURES = Path(__file__).with_name("mutation_fixtures.json")


def fail(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def file_hash(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


@dataclass(frozen=True)
class LP:
    """Laurent polynomial in the formal positive symbol pi."""

    terms: tuple[tuple[int, Q], ...]

    @staticmethod
    def make(values: dict[int, Q]) -> "LP":
        return LP(tuple(sorted((k, Q(v)) for k, v in values.items() if v)))

    @staticmethod
    def constant(value: int | Q) -> "LP":
        value = Q(value)
        return LP(()) if value == 0 else LP(((0, value),))

    def as_dict(self) -> dict[int, Q]:
        return dict(self.terms)

    def __add__(self, other: "LP | int | Q") -> "LP":
        other = as_lp(other)
        out = self.as_dict()
        for exponent, coefficient in other.terms:
            out[exponent] = out.get(exponent, Q(0)) + coefficient
        return LP.make(out)

    __radd__ = __add__

    def __neg__(self) -> "LP":
        return LP(tuple((k, -v) for k, v in self.terms))

    def __sub__(self, other: "LP | int | Q") -> "LP":
        return self + (-as_lp(other))

    def __rsub__(self, other: "LP | int | Q") -> "LP":
        return as_lp(other) - self

    def __mul__(self, other: "LP | int | Q") -> "LP":
        other = as_lp(other)
        out: dict[int, Q] = {}
        for left_power, left_coefficient in self.terms:
            for right_power, right_coefficient in other.terms:
                power = left_power + right_power
                out[power] = out.get(power, Q(0)) + left_coefficient * right_coefficient
        return LP.make(out)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "LP":
        fail(exponent >= 0, "negative Laurent-polynomial power")
        result = ONE
        base = self
        n = exponent
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n //= 2
        return result

    def divide_monomial(self, denominator: "LP") -> "LP":
        fail(len(denominator.terms) == 1, f"non-monomial exact divisor: {denominator}")
        power, coefficient = denominator.terms[0]
        fail(coefficient != 0, "zero exact divisor")
        return LP.make({k - power: v / coefficient for k, v in self.terms})

    def __truediv__(self, other: "LP | int | Q") -> "LP":
        return self.divide_monomial(as_lp(other))

    def is_zero(self) -> bool:
        return not self.terms

    def text(self) -> str:
        if not self.terms:
            return "0"
        pieces: list[str] = []
        for power, coefficient in self.terms:
            coeff = str(coefficient)
            if power == 0:
                term = coeff
            elif power == 1:
                term = f"{coeff}*pi"
            else:
                term = f"{coeff}*pi^{power}"
            pieces.append(term)
        return " + ".join(pieces).replace("+ -", "- ")


def as_lp(value: LP | int | Q) -> LP:
    return value if isinstance(value, LP) else LP.constant(value)


ZERO = LP.constant(0)
ONE = LP.constant(1)
PI = LP.make({1: Q(1)})


@dataclass(frozen=True)
class Series:
    coefficients: tuple[LP, ...]

    @staticmethod
    def make(values: Iterable[LP | int | Q]) -> "Series":
        data = [as_lp(v) for v in values]
        data.extend([ZERO] * (SERIES_ORDER + 1 - len(data)))
        return Series(tuple(data[: SERIES_ORDER + 1]))

    @staticmethod
    def constant(value: LP | int | Q) -> "Series":
        return Series.make([value])

    def coefficient(self, degree: int) -> LP:
        return self.coefficients[degree]

    def __add__(self, other: "Series | LP | int | Q") -> "Series":
        other = as_series(other)
        return Series.make(a + b for a, b in zip(self.coefficients, other.coefficients))

    __radd__ = __add__

    def __neg__(self) -> "Series":
        return Series.make(-v for v in self.coefficients)

    def __sub__(self, other: "Series | LP | int | Q") -> "Series":
        return self + (-as_series(other))

    def __rsub__(self, other: "Series | LP | int | Q") -> "Series":
        return as_series(other) - self

    def __mul__(self, other: "Series | LP | int | Q") -> "Series":
        other = as_series(other)
        out = [ZERO] * (SERIES_ORDER + 1)
        for i, left in enumerate(self.coefficients):
            if left.is_zero():
                continue
            for j, right in enumerate(other.coefficients[: SERIES_ORDER + 1 - i]):
                if not right.is_zero():
                    out[i + j] = out[i + j] + left * right
        return Series.make(out)

    __rmul__ = __mul__

    def __pow__(self, exponent: int) -> "Series":
        fail(exponent >= 0, "negative series power")
        result = Series.constant(1)
        base = self
        n = exponent
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n //= 2
        return result

    def reciprocal(self) -> "Series":
        a0 = self.coefficient(0)
        fail(len(a0.terms) == 1, f"series constant is not an exact monomial: {a0.text()}")
        out = [ONE / a0]
        for degree in range(1, SERIES_ORDER + 1):
            total = ZERO
            for k in range(1, degree + 1):
                total = total + self.coefficient(k) * out[degree - k]
            out.append(-(total / a0))
        return Series.make(out)

    def __truediv__(self, other: "Series | LP | int | Q") -> "Series":
        return self * as_series(other).reciprocal()

    def shift_down(self, places: int, label: str) -> "Series":
        fail(all(self.coefficient(k).is_zero() for k in range(places)), f"{label}: nonzero removed coefficient")
        return Series.make(self.coefficients[places:])


def as_series(value: Series | LP | int | Q) -> Series:
    return value if isinstance(value, Series) else Series.constant(value)


X = Series.make([0, 1])


def sin_series(value: Series) -> Series:
    result = Series.constant(0)
    for k in range((SERIES_ORDER + 1) // 2 + 1):
        degree = 2 * k + 1
        result = result + ((-1) ** k * Q(1, math.factorial(degree))) * value**degree
    return result


def cos_series(value: Series) -> Series:
    result = Series.constant(0)
    for k in range(SERIES_ORDER // 2 + 1):
        degree = 2 * k
        result = result + ((-1) ** k * Q(1, math.factorial(degree))) * value**degree
    return result


def from_jet(values: list[LP]) -> Series:
    return Series.make(values)


def equations(z_values: list[LP], r_values: list[LP], e_values: list[LP]) -> tuple[Series, Series, Series, Series, Series]:
    z = from_jet(z_values)
    r = from_jet(r_values)
    e = from_jet(e_values)
    x2 = X * X

    y = X + x2 * z
    w = X * r
    v = w + x2 * e

    sin_x = sin_series(X)
    sin_y = sin_series(y)
    sin_w = sin_series(w)
    sin_v = sin_series(v)
    cos_x = cos_series(X)
    cos_y = cos_series(y)
    cos_w = cos_series(w)
    cos_v = cos_series(v)

    lam = cos_x / cos_y

    sin_diff_4 = (sin_y - sin_x).shift_down(2, "fold numerator")
    sin_x_over_x = sin_x.shift_down(1, "sin(x)/x")
    sin_y_over_x = sin_y.shift_down(1, "sin(y)/x")
    fold = cos_x * sin_diff_4 / (sin_x_over_x * sin_y_over_x) - (lam * y + PI / 2 - X)

    cosine_constraint = (cos_v * cos_x - cos_w * cos_y).shift_down(3, "cosine constraint")

    h4 = cos_x
    l4 = lam * y + PI / 2 - X
    d4 = sin_y - sin_x
    a4 = 2 * (l4 + h4 * d4) / (h4 * h4)
    p4 = 4 * l4 / h4

    q3 = cos_w
    h3 = (1 + q3) / 2
    l3_plus_half_pi = lam * v + PI - w
    d3 = sin_v - sin_w
    a3 = (l3_plus_half_pi + (q3 + 2) * d3) / (h3 * h3)
    p3 = 2 * (l3_plus_half_pi + d3) / h3

    area = (a3 - a4).shift_down(2, "equal-area equation")
    gap = p3 - p4
    return fold, cosine_constraint, area, gap, lam


def response(base: LP, changed: LP) -> LP:
    return changed - base


def solve_jet() -> dict[str, object]:
    z = [ZERO] * (JET_ORDER + 1)
    r = [ZERO] * (JET_ORDER + 1)
    e = [ZERO] * (JET_ORDER + 1)

    # Fold base coefficient: F(0,z0) = z0 - pi/2.
    f0 = equations(z, r, e)[0].coefficient(0)
    z_trial = z.copy()
    z_trial[0] = ONE
    f1 = equations(z_trial, r, e)[0].coefficient(0)
    fold_jacobian = response(f0, f1)
    fail(fold_jacobian == ONE, f"fold Jacobian mismatch: {fold_jacobian.text()}")
    z[0] = -(f0 / fold_jacobian)
    fail(z[0] == PI / 2, f"fold base mismatch: {z[0].text()}")

    # At x=0, C=z-re and H=pi*r^2/2+4e-(pi+4z).
    # The descending branch is the exact root r0=2, e0=pi/4.
    r[0] = LP.constant(2)
    e[0] = PI / 4
    fold, cosine, area, gap, lam = equations(z, r, e)
    fail(fold.coefficient(0).is_zero(), "fold base equation failed")
    fail(cosine.coefficient(0).is_zero(), "cosine base equation failed")
    fail(area.coefficient(0).is_zero(), "equal-area base equation failed")
    branch_k3_limit = 8 * e[0] / (r[0] ** 2) - 2 * PI
    fail(branch_k3_limit == -(3 * PI / 2), f"descending K3 limit mismatch: {branch_k3_limit.text()}")

    base_cosine = equations(z, r, e)[1].coefficient(1)
    base_area = equations(z, r, e)[2].coefficient(1)
    r_trial = r.copy()
    r_trial[1] = ONE
    r_eqs = equations(z, r_trial, e)
    e_trial = e.copy()
    e_trial[1] = ONE
    e_eqs = equations(z, r, e_trial)
    c_r = response(base_cosine, r_eqs[1].coefficient(1))
    c_e = response(base_cosine, e_eqs[1].coefficient(1))
    h_r = response(base_area, r_eqs[2].coefficient(1))
    h_e = response(base_area, e_eqs[2].coefficient(1))
    equal_area_determinant = c_r * h_e - c_e * h_r
    fail(c_r == -(PI / 4), f"C_r mismatch: {c_r.text()}")
    fail(c_e == LP.constant(-2), f"C_e mismatch: {c_e.text()}")
    fail(h_r == 2 * PI, f"H_r mismatch: {h_r.text()}")
    fail(h_e == LP.constant(4), f"H_e mismatch: {h_e.text()}")
    fail(equal_area_determinant == 3 * PI, f"equal-area determinant mismatch: {equal_area_determinant.text()}")

    for degree in range(1, JET_ORDER + 1):
        # The degree-n fold coefficient is affine in z_n with derivative one.
        f_base = equations(z, r, e)[0].coefficient(degree)
        z_trial = z.copy()
        z_trial[degree] = ONE
        f_changed = equations(z_trial, r, e)[0].coefficient(degree)
        f_jac = response(f_base, f_changed)
        fail(f_jac == ONE, f"fold degree {degree}: Jacobian {f_jac.text()}")
        z[degree] = -(f_base / f_jac)
        fail(equations(z, r, e)[0].coefficient(degree).is_zero(), f"fold degree {degree} unsolved")

        # Solve the two regular equations C_n=H_n=0 for (r_n,e_n).
        current = equations(z, r, e)
        c0 = current[1].coefficient(degree)
        h0 = current[2].coefficient(degree)
        r_trial = r.copy()
        r_trial[degree] = ONE
        changed_r = equations(z, r_trial, e)
        e_trial = e.copy()
        e_trial[degree] = ONE
        changed_e = equations(z, r, e_trial)
        ar = response(c0, changed_r[1].coefficient(degree))
        ae = response(c0, changed_e[1].coefficient(degree))
        br = response(h0, changed_r[2].coefficient(degree))
        be = response(h0, changed_e[2].coefficient(degree))
        determinant = ar * be - ae * br
        fail(determinant == 3 * PI, f"degree {degree}: determinant {determinant.text()}")
        r[degree] = (ae * h0 - be * c0) / determinant
        e[degree] = (br * c0 - ar * h0) / determinant
        solved = equations(z, r, e)
        fail(solved[1].coefficient(degree).is_zero(), f"cosine degree {degree} unsolved")
        fail(solved[2].coefficient(degree).is_zero(), f"area degree {degree} unsolved")

    fold, cosine, area, gap, lam = equations(z, r, e)
    fail(all(fold.coefficient(k).is_zero() for k in range(JET_ORDER + 1)), "fold residual jet")
    fail(all(cosine.coefficient(k).is_zero() for k in range(JET_ORDER + 1)), "cosine residual jet")
    fail(all(area.coefficient(k).is_zero() for k in range(JET_ORDER + 1)), "area residual jet")
    fail(lam.coefficient(0) == ONE, "lambda constant mismatch")
    fail(lam.coefficient(1).is_zero() and lam.coefficient(2).is_zero(), "lambda lower jet mismatch")
    fail(lam.coefficient(3) == PI / 2, f"lambda x^3 mismatch: {lam.coefficient(3).text()}")

    cancellation = {str(k): gap.coefficient(k).text() for k in range(6)}
    fail(all(gap.coefficient(k).is_zero() for k in range(4)), f"gap lower cancellation failed: {cancellation}")
    fail(gap.coefficient(4) == -(3 * PI / 4), f"gap x^4 mismatch: {gap.coefficient(4).text()}")

    # Branch polynomial after eliminating e0=z0/r0.
    # 2*r*(H0/pi) = r^3-6r+4 = (r-2)(r^2+2r-2).
    branch_polynomial = [Q(4), Q(-6), Q(0), Q(1)]
    branch_factor_product = [Q(0)] * 4
    for i, left in enumerate([Q(-2), Q(1)]):
        for j, right in enumerate([Q(-2), Q(2), Q(1)]):
            branch_factor_product[i + j] += left * right
    fail(branch_polynomial == branch_factor_product, "branch factor identity failed")

    return {
        "schema": SCHEMA,
        "parameterization": {
            "u": "1-cos(x)",
            "h4": "cos(x)",
            "y": "x+x^2*z(x)",
            "lambda": "cos(x)/cos(y)",
            "q3": "cos(w)",
            "h3": "(1+cos(w))/2",
            "w": "x*r(x)",
            "v": "w+x^2*e(x)",
        },
        "base": {
            "z0": z[0].text(),
            "r0": r[0].text(),
            "e0": e[0].text(),
            "lambda_minus_one_leading": "1/2*pi*x^3",
        },
        "jacobians": {
            "fold_dF_dz": fold_jacobian.text(),
            "equal_area_matrix_order": ["r", "e"],
            "equal_area_matrix": [[c_r.text(), c_e.text()], [h_r.text(), h_e.text()]],
            "equal_area_determinant": equal_area_determinant.text(),
        },
        "branch_polynomial": "r^3-6*r+4=(r-2)*(r^2+2*r-2)",
        "selected_branch": "r=2 (descending type-(iii) height branch)",
        "descending_branch_guard": "K3 tends to -3/2*pi < 0",
        "jets": {
            "z": [value.text() for value in z],
            "r": [value.text() for value in r],
            "e": [value.text() for value in e],
        },
        "gap_coefficients_x0_through_x5": cancellation,
        "first_nonzero_gap_term": "-3/4*pi*x^4",
        "strict_sign_basis": "pi>0 and x>0",
    }


def mutation_checks(baseline: dict[str, object], fixture_path: Path) -> dict[str, bool]:
    raw = json.loads(fixture_path.read_text())
    fail(isinstance(raw, dict) and set(raw) == {"schema", "mutations"}, "fixture schema fields")
    fail(raw["schema"] == "cmv-exact-height-germ-mutations-v1", "fixture schema")
    fail(isinstance(raw["mutations"], list), "fixture mutations")
    rejected: dict[str, bool] = {}
    for row in raw["mutations"]:
        fail(isinstance(row, dict) and set(row) == {"id", "field", "replacement"}, "mutation row fields")
        identifier = row["id"]
        field = row["field"]
        replacement = row["replacement"]
        fail(isinstance(identifier, str) and identifier not in rejected, "mutation id")
        if field == "fold_jacobian":
            rejected[identifier] = replacement != baseline["jacobians"]["fold_dF_dz"]
        elif field == "equal_area_determinant":
            rejected[identifier] = replacement != baseline["jacobians"]["equal_area_determinant"]
        elif field == "first_gap_term":
            rejected[identifier] = replacement != baseline["first_nonzero_gap_term"]
        elif field == "descending_branch_guard":
            rejected[identifier] = replacement != baseline["descending_branch_guard"]
        elif field == "branch_polynomial":
            rejected[identifier] = replacement != baseline["branch_polynomial"]
        else:
            fail(False, f"unknown mutation field {field}")
        fail(rejected[identifier], f"mutation not rejected: {identifier}")
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--fixtures", type=Path, default=FIXTURES)
    args = parser.parse_args()

    fail(file_hash(SOURCE) == EXPECTED_SOURCE_SHA256, "primary-source hash mismatch")
    result = solve_jet()
    mutations = mutation_checks(result, args.fixtures)
    result["checks"] = {
        "source_sha256": EXPECTED_SOURCE_SHA256,
        "checker_sha256": file_hash(Path(__file__)),
        "fixtures_sha256": file_hash(args.fixtures),
        "python": platform.python_version(),
        "exact_decision_type": "fractions.Fraction Laurent polynomials",
        "mutations_rejected": f"{sum(mutations.values())}/{len(mutations)}",
        "mutation_results": mutations,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")

    print(f"SCHEMA={SCHEMA}")
    print(f"SOURCE_SHA256={EXPECTED_SOURCE_SHA256}")
    print(f"FOLD_JACOBIAN={result['jacobians']['fold_dF_dz']}")
    print(f"EQUAL_AREA_DETERMINANT={result['jacobians']['equal_area_determinant']}")
    print(f"BRANCH={result['selected_branch']}")
    print(f"GAP_COEFFICIENTS={result['gap_coefficients_x0_through_x5']}")
    print(f"FIRST_NONZERO={result['first_nonzero_gap_term']}")
    print(f"MUTATIONS_REJECTED={sum(mutations.values())}/{len(mutations)}")
    print("RESULT=PASS")


if __name__ == "__main__":
    main()
