#!/usr/bin/env python3
"""Exact outward-rounded source-native scalar preflight; not a Lean proof."""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

BITS = 160
SCALE = 1 << BITS
NVAR = 3
TERMS = 6


def floor_dyadic(x: Q) -> int:
    scaled = Q(x) * SCALE
    return scaled.numerator // scaled.denominator


def ceil_dyadic(x: Q) -> int:
    return -floor_dyadic(-Q(x))


@dataclass(frozen=True, slots=True)
class I:
    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("reversed interval")

    @staticmethod
    def bounds(lo, hi):
        return I(floor_dyadic(lo), ceil_dyadic(hi))

    @staticmethod
    def point(x):
        return I.bounds(x, x)

    def __add__(self, other):
        if isinstance(other, D):
            return NotImplemented
        other = as_i(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        if isinstance(other, D):
            return NotImplemented
        return self + -as_i(other)

    def __rsub__(self, other):
        return as_i(other) + -self

    def __mul__(self, other):
        if isinstance(other, D):
            return NotImplemented
        other = as_i(other)
        products = (self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi)
        return I(min(products) // SCALE, -((-max(products)) // SCALE))

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0 <= self.hi:
            raise ValueError("denominator contains zero")
        return I.bounds(Q(SCALE, self.hi), Q(SCALE, self.lo))

    def __truediv__(self, other):
        if isinstance(other, D):
            return NotImplemented
        return self * as_i(other).reciprocal()

    def __rtruediv__(self, other):
        return as_i(other) * self.reciprocal()

    def __pow__(self, exponent):
        if type(exponent) is not int:
            raise ValueError("only integer powers are supported")
        if exponent < 0:
            return self.reciprocal() ** -exponent
        if exponent == 0:
            return I.point(1)
        if exponent % 2 == 0:
            endpoints = (Q(self.lo, SCALE) ** exponent,
                         Q(self.hi, SCALE) ** exponent)
            lower = 0 if self.lo <= 0 <= self.hi else min(endpoints)
            return I.bounds(lower, max(endpoints))
        return I.bounds(Q(self.lo, SCALE) ** exponent,
                        Q(self.hi, SCALE) ** exponent)

    def exact(self):
        return [str(Q(self.lo, SCALE)), str(Q(self.hi, SCALE))]


def as_i(x):
    return x if isinstance(x, I) else I.point(x)


ZERO = I.point(0)
ONE = I.point(1)


@dataclass(frozen=True, slots=True)
class D:
    v: I
    d: tuple[I, ...]

    @staticmethod
    def constant(x):
        return D(as_i(x), (ZERO,) * NVAR)

    def __add__(self, other):
        other = as_d(other)
        return D(self.v + other.v,
                 tuple(a + b for a, b in zip(self.d, other.d)))

    __radd__ = __add__

    def __neg__(self):
        return D(-self.v, tuple(-entry for entry in self.d))

    def __sub__(self, other):
        return self + -as_d(other)

    def __rsub__(self, other):
        return as_d(other) + -self

    def __mul__(self, other):
        other = as_d(other)
        return D(self.v * other.v,
                 tuple(a * other.v + self.v * b
                       for a, b in zip(self.d, other.d)))

    __rmul__ = __mul__

    def reciprocal(self):
        inverse = self.v.reciprocal()
        factor = -(inverse ** 2)
        return D(inverse, tuple(factor * entry for entry in self.d))

    def __truediv__(self, other):
        return self * as_d(other).reciprocal()

    def __rtruediv__(self, other):
        return as_d(other) * self.reciprocal()

    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError("dual powers require nonnegative integer exponents")
        if exponent == 0:
            return D.constant(1)
        factor = exponent * self.v ** (exponent - 1)
        return D(self.v ** exponent,
                 tuple(factor * entry for entry in self.d))


def as_d(x):
    return x if isinstance(x, D) else D.constant(x)


def remainder_interval(x: I, index: int) -> tuple[I, I]:
    if type(index) is not int or index < 0:
        raise ValueError("remainder index must be nonnegative")
    bound = max(abs(Q(x.lo, SCALE)), abs(Q(x.hi, SCALE)))
    if bound > Q(1, 2):
        raise ValueError("atan quotient argument exceeds one half")
    square = x ** 2
    value = ZERO
    derivative = ZERO
    for j in reversed(range(TERMS)):
        coefficient = Q((-1) ** (index + j), 2 * (index + j) + 1)
        value = value * square + coefficient
        if j:
            derivative = derivative * square + 2 * j * coefficient
    derivative = x * derivative
    tail_index = index + TERMS
    value_error = bound ** (2 * TERMS) / (2 * tail_index + 1)
    derivative_error = (
        2 * TERMS * bound ** (2 * TERMS - 1) / (2 * tail_index + 1)
        + 2 * bound ** (2 * TERMS + 1) / (2 * tail_index + 3))
    return (value + I.bounds(-value_error, value_error),
            derivative + I.bounds(-derivative_error, derivative_error))


def remainder(x: D, index: int) -> D:
    value, derivative = remainder_interval(x.v, index)
    return D(value, tuple(derivative * entry for entry in x.d))


def alternating_atan_bounds(inverse: int, terms: int = 36) -> tuple[Q, Q]:
    x = Q(1, inverse)
    partial = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
                   for k in range(terms)), Q(0))
    tail = x ** (2 * terms + 1) / (2 * terms + 1)
    return partial, partial + tail


atan5 = alternating_atan_bounds(5)
atan239 = alternating_atan_bounds(239)
PI = I.bounds(16 * atan5[0] - 4 * atan239[1],
              16 * atan5[1] - 4 * atan239[0])

SCHEMA = "cmv-source-native-scalar-preflight-v1"
EXPECTED_CONTRACT = {
    "density_parameter": "lambda=1+t^3",
    "target_bands": 13,
    "cells_per_band": 64,
    "target_cells": 832,
    "remote_cells": 1,
    "retained_predictor_degree": 1,
    "maximum_predictor_degree": 12,
    "maximum_transient_polynomial_degree": 24,
    "arithmetic_bits": 160,
    "maximum_arithmetic_bits": 512,
    "atan_quotient_polynomial_terms": 7,
    "additional_subdivision": 0,
}
N = Q(126334)
HALF = Q(1, 2)


def qtext(x: Q) -> str:
    return str(Q(x))


def parse_q(x, where: str) -> Q:
    if type(x) is not str:
        raise ValueError(f"rational must be a canonical string at {where}")
    try:
        value = Q(x)
    except Exception as exc:
        raise ValueError(f"invalid rational at {where}") from exc
    if str(value) != x:
        raise ValueError(f"noncanonical rational at {where}")
    return value


def interval_fraction(x: I) -> tuple[Q, Q]:
    return Q(x.lo, SCALE), Q(x.hi, SCALE)


def max_abs(x: I) -> Q:
    lo, hi = interval_fraction(x)
    return max(abs(lo), abs(hi))


def scaled_sqrt_floor(x: Q) -> int:
    if x < 0:
        raise ValueError("sqrt of negative endpoint")
    numerator = x.numerator * SCALE * SCALE
    return math.isqrt(numerator // x.denominator)


def scaled_sqrt_ceil(x: Q) -> int:
    k = scaled_sqrt_floor(x)
    if k * k * x.denominator < x.numerator * SCALE * SCALE:
        k += 1
    return k


def sqrt_i(x: I) -> I:
    lo, hi = interval_fraction(x)
    if lo < 0:
        raise ValueError("sqrt interval crosses the negative axis")
    return I(scaled_sqrt_floor(lo), scaled_sqrt_ceil(hi))


def sqrt_d(x: D) -> D:
    root = sqrt_i(x.v)
    if root.lo <= 0:
        raise ValueError("sqrt derivative denominator is not positive")
    derivative = Q(1, 2) / root
    return D(root, tuple(derivative * entry for entry in x.d))


def aq(x: D) -> D:
    """Exact seven-polynomial-term atan quotient with the analytic tail retained."""
    return 1 + x * x * remainder(x, 1)


def unit(index: int) -> tuple[I, ...]:
    return tuple(ONE if i == index else ZERO for i in range(NVAR))


def variable(lo: Q, hi: Q, index: int) -> D:
    return D(I.bounds(lo, hi), unit(index))


def constant(x) -> D:
    return D.constant(x)


def intersect(a: I, b: I) -> I:
    lo, hi = max(a.lo, b.lo), min(a.hi, b.hi)
    if lo > hi:
        raise ValueError("independent sound enclosures are disjoint")
    return I(lo, hi)


def centered_enclosure(whole: D, center: D, bounds: tuple[I, ...]) -> I:
    enclosure = center.v
    for derivative, bound in zip(whole.d, bounds):
        enclosure = enclosure + derivative * bound
    return intersect(enclosure, whole.v)


def atom(t: D, c: D) -> dict[str, D]:
    lam = 1 + t ** 3
    x = 1 - t ** 2 * c
    ui = 2 * c - t ** 2 * c ** 2
    vi = 2 * c + 2 * t - t ** 2 * c ** 2 + t ** 4
    u = sqrt_d(ui)
    v = sqrt_d(vi)
    radical_sum = v + lam * u
    k_den = u * v * radical_sum
    d_den = lam * radical_sum
    rho_den = (u + v) * (x ** 2 + t ** 2 * u * v)
    inv_k_den = k_den.reciprocal()
    inv_d_den = d_den.reciprocal()
    inv_rho_den = rho_den.reciprocal()
    inv_x = x.reciprocal()
    k = x ** 2 * (2 + t ** 3) * inv_k_den
    d = x ** 2 * (2 + t ** 3) * inv_d_den
    rho = x * (2 + t ** 3) * inv_rho_den
    arg_linear = t * v * inv_x
    arg_quadratic = t ** 2 * rho
    h = t ** 2 * v * inv_x * aq(arg_linear) + rho * aq(arg_quadratic)
    return {
        "lam": lam,
        "x": x,
        "ui": ui,
        "vi": vi,
        "u": u,
        "v": v,
        "radical_sum": radical_sum,
        "k_den": k_den,
        "d_den": d_den,
        "rho_den": rho_den,
        "inv_k_den": inv_k_den,
        "inv_d_den": inv_d_den,
        "inv_rho_den": inv_rho_den,
        "inv_x": inv_x,
        "k": k,
        "d": d,
        "rho": rho,
        "arg_linear": arg_linear,
        "arg_quadratic": arg_quadratic,
        "h": h,
    }


def source_model(t: D, a: D, b: D):
    four = atom(t, a)
    three = atom(t, 2 * b)
    h4 = four["x"]
    h3 = 1 - t ** 2 * b
    pi = constant(PI)
    fold = h4 * four["k"] - pi / 2 - t ** 2 * four["h"]
    area = (pi * (b - a) * (h4 + h3)
            + h4 ** 2 * (three["h"] + (2 * h3 + 1) * three["d"])
            - 2 * h3 ** 2 * (four["h"] + h4 * four["d"]))
    gap = (a - b) * four["k"] + h3 * four["d"] - h4 * three["d"]
    guards = {
        "t_pos": t,
        "t_lt_half": HALF - t,
        "lambda_sub_one": t ** 3,
        "lambda_pos": four["lam"],
        "t_sq": t ** 2,
        "a_pos": a,
        "b_pos": b,
        "height_order_b_sub_a": b - a,
        "height_order_hFour_sub_hThree": h4 - h3,
        "hFour_pos": h4,
        "hFour_gt_half": h4 - HALF,
        "hFour_lt_one": 1 - h4,
        "hThree_pos": h3,
        "hThree_gt_half": h3 - HALF,
        "hThree_lt_one": 1 - h3,
        "typeThreeShape_pos": three["x"],
        "typeThreeShape_lt_one": 1 - three["x"],
        "positive_area_factor": h3 ** 2 * h4 ** 2,
        "uInner_four": four["ui"],
        "vInner_four": four["vi"],
        "uInner_three": three["ui"],
        "vInner_three": three["vi"],
        "U_four": four["u"],
        "V_four": four["v"],
        "U_three": three["u"],
        "V_three": three["v"],
        "radical_sum_four": four["radical_sum"],
        "radical_sum_three": three["radical_sum"],
        "K_den_four": four["k_den"],
        "K_den_three": three["k_den"],
        "D_den_four": four["d_den"],
        "D_den_three": three["d_den"],
        "rho_den_four": four["rho_den"],
        "rho_den_three": three["rho_den"],
        "rho_four": four["rho"],
        "rho_three": three["rho"],
        "atan_linear_four_pos": four["arg_linear"],
        "atan_quadratic_four_pos": four["arg_quadratic"],
        "atan_linear_three_pos": three["arg_linear"],
        "atan_quadratic_three_pos": three["arg_quadratic"],
        "atan_linear_four_lt_half": HALF - four["arg_linear"],
        "atan_quadratic_four_lt_half": HALF - four["arg_quadratic"],
        "atan_linear_three_lt_half": HALF - three["arg_linear"],
        "atan_quadratic_three_lt_half": HALF - three["arg_quadratic"],
    }
    arguments = {
        "linear_four": four["arg_linear"],
        "quadratic_four": four["arg_quadratic"],
        "linear_three": three["arg_linear"],
        "quadratic_three": three["arg_quadratic"],
    }
    radicals = {
        "U_four": (four["ui"], four["u"]),
        "V_four": (four["vi"], four["v"]),
        "U_three": (three["ui"], three["u"]),
        "V_three": (three["vi"], three["v"]),
    }
    reciprocals = {
        "K_den_four": (four["k_den"], four["inv_k_den"]),
        "D_den_four": (four["d_den"], four["inv_d_den"]),
        "rho_den_four": (four["rho_den"], four["inv_rho_den"]),
        "x_four": (four["x"], four["inv_x"]),
        "K_den_three": (three["k_den"], three["inv_k_den"]),
        "D_den_three": (three["d_den"], three["inv_d_den"]),
        "rho_den_three": (three["rho_den"], three["inv_rho_den"]),
        "x_three": (three["x"], three["inv_x"]),
    }
    return fold, area, gap, guards, arguments, radicals, reciprocals


def predictor(coefficients: tuple[Q, Q], t: D) -> D:
    return coefficients[0] + coefficients[1] * t


def epsilon_center_radius(bounds: tuple[Q, Q]) -> tuple[Q, Q]:
    center = (bounds[0] + bounds[1]) / 2
    radius = (bounds[1] - bounds[0]) / 2
    return center, radius


def evaluate(cell: dict, theta: tuple[Q, Q] | None,
             eps4: tuple[Q, Q] | Q, eps3: tuple[Q, Q] | Q):
    t_center = (cell["t"][0] + cell["t"][1]) / 2
    if theta is None:
        theta_d = constant(0)
    else:
        theta_d = variable(theta[0], theta[1], 0)
    t = t_center + theta_d
    if isinstance(eps4, tuple):
        e4 = variable(eps4[0], eps4[1], 1)
    else:
        e4 = constant(eps4)
    if isinstance(eps3, tuple):
        e3 = variable(eps3[0], eps3[1], 2)
    else:
        e3 = constant(eps3)
    a = predictor(cell["p4"], t) + t ** 2 * e4
    b = predictor(cell["p3"], t) + t ** 2 * e3
    return source_model(t, a, b)


def face_enclosure(cell: dict, which: str, endpoint: Q) -> I:
    t_center = sum(cell["t"]) / 2
    theta_radius = (cell["t"][1] - cell["t"][0]) / 2
    theta = (-theta_radius, theta_radius)
    e4_center, e4_radius = epsilon_center_radius(cell["eps4"])
    e3_center, _ = epsilon_center_radius(cell["eps3"])
    if which == "fold":
        whole = evaluate(cell, theta, endpoint, e3_center)[0]
        center = evaluate(cell, None, endpoint, e3_center)[0]
        bounds = (I.bounds(*theta), ZERO, ZERO)
    elif which == "area":
        whole = evaluate(cell, theta, cell["eps4"], endpoint)[1]
        center = evaluate(cell, None, e4_center, endpoint)[1]
        bounds = (I.bounds(*theta), I.bounds(-e4_radius, e4_radius), ZERO)
    else:
        raise ValueError("unknown face")
    return centered_enclosure(whole, center, bounds)


def whole_enclosures(cell: dict):
    theta_radius = (cell["t"][1] - cell["t"][0]) / 2
    theta = (-theta_radius, theta_radius)
    e4_center, e4_radius = epsilon_center_radius(cell["eps4"])
    e3_center, e3_radius = epsilon_center_radius(cell["eps3"])
    whole = evaluate(cell, theta, cell["eps4"], cell["eps3"])
    center = evaluate(cell, None, e4_center, e3_center)
    bounds = (I.bounds(*theta), I.bounds(-e4_radius, e4_radius),
              I.bounds(-e3_radius, e3_radius))
    gap = centered_enclosure(whole[2], center[2], bounds)
    guards = {name: centered_enclosure(value, center[3][name], bounds)
              for name, value in whole[3].items()}
    return gap, guards, whole[4], whole[5], whole[6]


def atan_error_budget(arguments: dict[str, D]) -> dict:
    rows = {}
    for name, argument in arguments.items():
        bound = max_abs(argument.v)
        if bound > HALF:
            raise ValueError("atan quotient argument exceeds one half")
        value_error = bound ** 14 / 15
        derivative_error = 14 * bound ** 13 / 15 + 2 * bound ** 15 / 17
        rows[name] = {
            "argument_bound": qtext(bound),
            "value_tail_error": qtext(value_error),
            "derivative_tail_error": qtext(derivative_error),
        }
    return rows


def parse_cell(raw: dict, expected_t: tuple[Q, Q], where: str) -> dict:
    if set(raw) != {"t", "p4", "p3", "eps4", "eps3"}:
        raise ValueError(f"unexpected cell keys at {where}")
    cell = {}
    for key in ["t", "p4", "p3", "eps4", "eps3"]:
        if not isinstance(raw[key], list) or len(raw[key]) != 2:
            raise ValueError(f"wrong pair at {where}.{key}")
        cell[key] = tuple(parse_q(x, f"{where}.{key}") for x in raw[key])
    if cell["t"] != expected_t or not cell["t"][0] < cell["t"][1]:
        raise ValueError(f"wrong frozen t interval at {where}")
    if not cell["eps4"][0] < cell["eps4"][1]:
        raise ValueError(f"empty eps4 bracket at {where}")
    if not cell["eps3"][0] < cell["eps3"][1]:
        raise ValueError(f"empty eps3 bracket at {where}")
    return cell


def expected_band(j: int) -> tuple[Q, Q]:
    return Q(2 ** (j + 1), N), min(Q(2 ** (j + 2), N), Q(1, 10))


def expected_cell(j: int, k: int) -> tuple[Q, Q]:
    lo, hi = expected_band(j)
    return lo + Q(k, 64) * (hi - lo), lo + Q(k + 1, 64) * (hi - lo)


def check_cell(cell: dict) -> dict:
    fold_lower = face_enclosure(cell, "fold", cell["eps4"][0])
    fold_upper = face_enclosure(cell, "fold", cell["eps4"][1])
    area_lower = face_enclosure(cell, "area", cell["eps3"][0])
    area_upper = face_enclosure(cell, "area", cell["eps3"][1])
    gap, guards, arguments, radicals, reciprocals = whole_enclosures(cell)
    accepted = (fold_lower.lo > 0 and fold_upper.hi < 0
                and area_lower.hi < 0 and area_upper.lo > 0
                and gap.hi < 0 and all(value.lo > 0 for value in guards.values()))
    radicand_enclosures = {
        name: radicand.v.exact() for name, (radicand, _) in radicals.items()}
    sqrt_enclosures = {
        name: root.v.exact() for name, (_, root) in radicals.items()}
    reciprocal_witnesses = {
        name: {
            "denominator": denominator.v.exact(),
            "reciprocal": inverse.v.exact(),
        }
        for name, (denominator, inverse) in reciprocals.items()
    }
    return {
        "status": "SCALAR_CELL_PASS" if accepted else "SCALAR_CELL_FAIL",
        "fold_faces": {"eps_lower": fold_lower.exact(), "eps_upper": fold_upper.exact()},
        "area_faces": {"eps_lower": area_lower.exact(), "eps_upper": area_upper.exact()},
        "gap": gap.exact(),
        "guards": {name: value.exact() for name, value in guards.items()},
        "atan_error_budgets": atan_error_budget(arguments),
        "sqrt_enclosures": sqrt_enclosures,
        "radicand_enclosures": radicand_enclosures,
        "reciprocal_witnesses": reciprocal_witnesses,
        "sqrt_rounding_endpoint_error_bound": qtext(Q(1, SCALE)),
        "dyadic_operation_rounding_ulp": qtext(Q(1, SCALE)),
        "discarded_predictor_terms": "none",
    }


def load_manifest(path: Path) -> dict:
    raw = json.loads(path.read_text())
    if set(raw) != {"schema", "contract", "bands", "remote"} or raw["schema"] != SCHEMA:
        raise ValueError("invalid scalar preflight schema")
    if raw["contract"] != EXPECTED_CONTRACT:
        raise ValueError("scalar preflight contract mismatch")
    if len(raw["bands"]) != 13:
        raise ValueError("target band inventory changed")
    return raw


def check(path: Path) -> dict:
    raw = load_manifest(path)
    output_bands = []
    accepted_count = 0
    for j, band in enumerate(raw["bands"]):
        if set(band) != {"t", "cells"} or len(band["cells"]) != 64:
            raise ValueError(f"band {j} does not contain exactly 64 cells")
        expected = expected_band(j)
        if tuple(parse_q(x, f"band {j}") for x in band["t"]) != expected:
            raise ValueError(f"band {j} endpoint mismatch")
        rows = []
        for k, raw_cell in enumerate(band["cells"]):
            cell = parse_cell(raw_cell, expected_cell(j, k), f"band {j} cell {k}")
            try:
                result = check_cell(cell)
            except ValueError as exc:
                result = {"status": "SCALAR_CELL_FAIL", "error": str(exc)}
            rows.append(result)
            accepted_count += result["status"] == "SCALAR_CELL_PASS"
        output_bands.append({"index": j, "t": [qtext(x) for x in expected],
                             "accepted": sum(x["status"] == "SCALAR_CELL_PASS" for x in rows),
                             "cells": rows})
    remote_expected = (Q(1, 10), Q(101, 1000))
    remote = parse_cell(raw["remote"], remote_expected, "remote")
    remote_result = check_cell(remote)
    passed = accepted_count == 832 and remote_result["status"] == "SCALAR_CELL_PASS"
    return {
        "status": "SCALAR_PREFLIGHT_PASS" if passed else "SCALAR_PREFLIGHT_FAIL",
        "proof_status": "NOT_KERNEL_REPLAYED",
        "schema": SCHEMA,
        "dependency_enclosure": "centered first-order Taylor interval",
        "retained_predictor_degree": 1,
        "outward_bits": BITS,
        "atan_quotient_polynomial_terms": 7,
        "pi_interval": PI.exact(),
        "target_cells": 832,
        "accepted_target_cells": accepted_count,
        "remote": remote_result,
        "bands": output_bands,
        "manifest_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.manifest)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "bands"}))
    for band in result["bands"]:
        print(f"band {band['index']}: {band['accepted']}/64")
    return 0 if result["status"] == "SCALAR_PREFLIGHT_PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
