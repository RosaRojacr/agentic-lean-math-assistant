#!/usr/bin/env python3
"""Emit the frozen source-native scalar program and one data-only integer trace.

The producer is untrusted.  Lean checks every dyadic witness with signed integer
inequalities; this script performs no proof step.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

import check_scalar_preflight as reference

S = reference.SCALE
TERMS = reference.TERMS
GUARD_NAMES = tuple(reference.source_model(
    reference.D.constant(Q(1, 100)),
    reference.D.constant(Q(1, 3)),
    reference.D.constant(Q(3, 4)))[3].keys())

SLOTS = {
    name: index for index, name in enumerate((
        "whole_t_center", "whole_theta", "whole_e4", "whole_e3",
        "whole_p4_0", "whole_p4_1", "whole_p3_0", "whole_p3_1",
        "center_t_center", "center_theta", "center_e4", "center_e3",
        "center_p4_0", "center_p4_1", "center_p3_0", "center_p3_1",
        "t_displacement", "e4_displacement", "e3_displacement"))
}
KINDS = ("foldLower", "foldUpper", "areaLower", "areaUpper", "whole")


def floor_dyadic(x: Q) -> int:
    y = Q(x) * S
    return y.numerator // y.denominator


def ceil_dyadic(x: Q) -> int:
    return -floor_dyadic(-Q(x))


@dataclass(frozen=True, slots=True)
class TI:
    builder: "Builder"
    lo: int
    hi: int
    ref: int

    def __add__(self, other):
        other = self.builder.as_interval(other)
        return self.builder.emit(("add", self.ref, other.ref),
                                 self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return self.builder.emit(("neg", self.ref), -self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.builder.as_interval(other)

    def __rsub__(self, other):
        return self.builder.as_interval(other) + -self

    def __mul__(self, other):
        other = self.builder.as_interval(other)
        products = (self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi)
        lo = min(products) // S
        hi = -((-max(products)) // S)
        return self.builder.emit(("mul", self.ref, other.ref), lo, hi)

    __rmul__ = __mul__

    def reciprocal(self):
        if self.lo <= 0:
            raise ValueError("integer trace supports only positive reciprocals")
        lo = floor_dyadic(Q(S, self.hi))
        hi = ceil_dyadic(Q(S, self.lo))
        return self.builder.emit(("recip", self.ref), lo, hi)

    def __truediv__(self, other):
        return self * self.builder.as_interval(other).reciprocal()

    def __rtruediv__(self, other):
        return self.builder.as_interval(other) * self.reciprocal()

    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError("only nonnegative integer powers are supported")
        if exponent == 0:
            out = (S, S)
        elif exponent % 2 == 0:
            endpoints = (Q(self.lo, S) ** exponent, Q(self.hi, S) ** exponent)
            lower = Q(0) if self.lo <= 0 <= self.hi else min(endpoints)
            out = (floor_dyadic(lower), ceil_dyadic(max(endpoints)))
        else:
            out = (floor_dyadic(Q(self.lo, S) ** exponent),
                   ceil_dyadic(Q(self.hi, S) ** exponent))
        return self.builder.emit(("pow", self.ref, exponent), *out)


@dataclass(frozen=True, slots=True)
class TD:
    v: TI
    d: tuple[TI, TI, TI]

    @property
    def builder(self):
        return self.v.builder

    def __add__(self, other):
        other = self.builder.as_dual(other)
        return TD(self.v + other.v, tuple(a + b for a, b in zip(self.d, other.d)))

    __radd__ = __add__

    def __neg__(self):
        return TD(-self.v, tuple(-x for x in self.d))

    def __sub__(self, other):
        return self + -self.builder.as_dual(other)

    def __rsub__(self, other):
        return self.builder.as_dual(other) + -self

    def __mul__(self, other):
        other = self.builder.as_dual(other)
        return TD(self.v * other.v,
                  tuple(a * other.v + self.v * b
                        for a, b in zip(self.d, other.d)))

    __rmul__ = __mul__

    def reciprocal(self):
        inverse = self.v.reciprocal()
        factor = -(inverse ** 2)
        return TD(inverse, tuple(factor * x for x in self.d))

    def __truediv__(self, other):
        return self * self.builder.as_dual(other).reciprocal()

    def __rtruediv__(self, other):
        return self.builder.as_dual(other) * self.reciprocal()

    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError("dual powers require nonnegative integer exponents")
        if exponent == 0:
            return self.builder.constant(1)
        factor = exponent * self.v ** (exponent - 1)
        return TD(self.v ** exponent, tuple(factor * x for x in self.d))


class Builder:
    def __init__(self):
        self.steps: list[dict] = []
        self.zero = self.rat(Q(0))
        self.one = self.rat(Q(1))

    def emit(self, op: tuple, lo: int, hi: int) -> TI:
        if lo > hi:
            raise ValueError("reversed emitted interval")
        ref = len(self.steps)
        self.steps.append({"op": op, "lo": lo, "hi": hi})
        return TI(self, lo, hi, ref)

    def rat(self, x: Q) -> TI:
        x = Q(x)
        return self.emit(("rat", x.numerator, x.denominator),
                         floor_dyadic(x), ceil_dyadic(x))

    def input(self, slot: str, lo: Q, hi: Q, mode: str) -> TI:
        lo, hi = Q(lo), Q(hi)
        if lo > hi or mode not in ("point", "range"):
            raise ValueError("invalid input")
        if mode == "point" and lo != hi:
            raise ValueError("point input is not a point")
        return self.emit(("input", SLOTS[slot], mode,
                          lo.numerator, lo.denominator, hi.numerator, hi.denominator),
                         floor_dyadic(lo), ceil_dyadic(hi))

    def pi(self) -> TI:
        return self.emit(("pi",), reference.PI.lo, reference.PI.hi)

    def sqrt(self, x: TI) -> TI:
        if x.lo < 0:
            raise ValueError("negative square-root radicand")
        lo_q, hi_q = Q(x.lo, S), Q(x.hi, S)
        lo = reference.scaled_sqrt_floor(lo_q)
        hi = reference.scaled_sqrt_ceil(hi_q)
        return self.emit(("sqrt", x.ref), lo, hi)

    def intersect(self, a: TI, b: TI) -> TI:
        lo, hi = max(a.lo, b.lo), min(a.hi, b.hi)
        if lo > hi:
            raise ValueError("disjoint enclosures")
        return self.emit(("intersect", a.ref, b.ref), lo, hi)

    def tail(self, x: TI, index: int, derivative: bool) -> TI:
        bound = max(abs(Q(x.lo, S)), abs(Q(x.hi, S)))
        if bound > Q(1, 2):
            raise ValueError("atan quotient argument exceeds one half")
        tail_index = index + TERMS
        if derivative:
            error = (2 * TERMS * bound ** (2 * TERMS - 1) /
                     (2 * tail_index + 1) +
                     2 * bound ** (2 * TERMS + 1) /
                     (2 * tail_index + 3))
            tag = "tailDerivative"
        else:
            error = bound ** (2 * TERMS) / (2 * tail_index + 1)
            tag = "tailValue"
        return self.emit((tag, x.ref, index, TERMS),
                         floor_dyadic(-error), ceil_dyadic(error))

    def as_interval(self, x) -> TI:
        if isinstance(x, TI):
            if x.builder is not self:
                raise ValueError("cross-builder interval")
            return x
        return self.rat(Q(x))

    def constant(self, x) -> TD:
        return TD(self.as_interval(x), (self.zero, self.zero, self.zero))

    def as_dual(self, x) -> TD:
        return x if isinstance(x, TD) else self.constant(x)

    def variable(self, interval: TI, index: int) -> TD:
        derivatives = [self.zero, self.zero, self.zero]
        derivatives[index] = self.one
        return TD(interval, tuple(derivatives))


def remainder_interval(x: TI, index: int) -> tuple[TI, TI]:
    b = x.builder
    square = x ** 2
    value = b.zero
    derivative = b.zero
    for j in reversed(range(TERMS)):
        coefficient = Q((-1) ** (index + j), 2 * (index + j) + 1)
        value = value * square + coefficient
        if j:
            derivative = derivative * square + 2 * j * coefficient
    derivative = x * derivative
    return value + b.tail(x, index, False), derivative + b.tail(x, index, True)


def remainder(x: TD, index: int) -> TD:
    value, derivative = remainder_interval(x.v, index)
    return TD(value, tuple(derivative * entry for entry in x.d))


def sqrt_d(x: TD) -> TD:
    b = x.builder
    root = b.sqrt(x.v)
    if root.lo <= 0:
        raise ValueError("nonpositive square-root witness")
    derivative = Q(1, 2) / root
    return TD(root, tuple(derivative * entry for entry in x.d))


def aq(x: TD) -> TD:
    return 1 + x * x * remainder(x, 1)


def atom(t: TD, c: TD) -> dict[str, TD]:
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
    return {"lam": lam, "x": x, "ui": ui, "vi": vi, "u": u, "v": v,
            "radical_sum": radical_sum, "k_den": k_den, "d_den": d_den,
            "rho_den": rho_den, "inv_k_den": inv_k_den,
            "inv_d_den": inv_d_den, "inv_rho_den": inv_rho_den,
            "inv_x": inv_x, "k": k, "d": d, "rho": rho,
            "arg_linear": arg_linear, "arg_quadratic": arg_quadratic, "h": h}


def source_model(t: TD, a: TD, b: TD, pi: TD):
    four = atom(t, a)
    three = atom(t, 2 * b)
    h4 = four["x"]
    h3 = 1 - t ** 2 * b
    fold = h4 * four["k"] - pi / 2 - t ** 2 * four["h"]
    area = (pi * (b - a) * (h4 + h3)
            + h4 ** 2 * (three["h"] + (2 * h3 + 1) * three["d"])
            - 2 * h3 ** 2 * (four["h"] + h4 * four["d"]))
    gap = (a - b) * four["k"] + h3 * four["d"] - h4 * three["d"]
    guards = {
        "t_pos": t, "t_lt_half": Q(1, 2) - t,
        "lambda_sub_one": t ** 3, "lambda_pos": four["lam"], "t_sq": t ** 2,
        "a_pos": a, "b_pos": b, "height_order_b_sub_a": b - a,
        "height_order_hFour_sub_hThree": h4 - h3,
        "hFour_pos": h4, "hFour_gt_half": h4 - Q(1, 2),
        "hFour_lt_one": 1 - h4, "hThree_pos": h3,
        "hThree_gt_half": h3 - Q(1, 2), "hThree_lt_one": 1 - h3,
        "typeThreeShape_pos": three["x"], "typeThreeShape_lt_one": 1 - three["x"],
        "positive_area_factor": h3 ** 2 * h4 ** 2,
        "uInner_four": four["ui"], "vInner_four": four["vi"],
        "uInner_three": three["ui"], "vInner_three": three["vi"],
        "U_four": four["u"], "V_four": four["v"],
        "U_three": three["u"], "V_three": three["v"],
        "radical_sum_four": four["radical_sum"],
        "radical_sum_three": three["radical_sum"],
        "K_den_four": four["k_den"], "K_den_three": three["k_den"],
        "D_den_four": four["d_den"], "D_den_three": three["d_den"],
        "rho_den_four": four["rho_den"], "rho_den_three": three["rho_den"],
        "rho_four": four["rho"], "rho_three": three["rho"],
        "atan_linear_four_pos": four["arg_linear"],
        "atan_quadratic_four_pos": four["arg_quadratic"],
        "atan_linear_three_pos": three["arg_linear"],
        "atan_quadratic_three_pos": three["arg_quadratic"],
        "atan_linear_four_lt_half": Q(1, 2) - four["arg_linear"],
        "atan_quadratic_four_lt_half": Q(1, 2) - four["arg_quadratic"],
        "atan_linear_three_lt_half": Q(1, 2) - three["arg_linear"],
        "atan_quadratic_three_lt_half": Q(1, 2) - three["arg_quadratic"],
    }
    if tuple(guards) != GUARD_NAMES:
        raise AssertionError("guard schedule drift")
    return fold, area, gap, guards


def input_dual(b: Builder, prefix: str, slot: str, lo: Q, hi: Q,
               mode: str, derivative: int | None) -> TD:
    value = b.input(f"{prefix}_{slot}", lo, hi, mode)
    return b.variable(value, derivative) if derivative is not None else b.constant(value)


def evaluate(b: Builder, cell: dict, prefix: str,
             theta: tuple[Q, Q] | None,
             eps4: tuple[Q, Q] | Q, eps3: tuple[Q, Q] | Q):
    t_center = sum(cell["t"]) / 2
    tc = input_dual(b, prefix, "t_center", t_center, t_center, "point", None)
    if theta is None:
        th = input_dual(b, prefix, "theta", Q(0), Q(0), "point", None)
    else:
        th = input_dual(b, prefix, "theta", theta[0], theta[1], "range", 0)
    t = tc + th
    if isinstance(eps4, tuple):
        e4 = input_dual(b, prefix, "e4", eps4[0], eps4[1], "range", 1)
    else:
        e4 = input_dual(b, prefix, "e4", eps4, eps4, "point", None)
    if isinstance(eps3, tuple):
        e3 = input_dual(b, prefix, "e3", eps3[0], eps3[1], "range", 2)
    else:
        e3 = input_dual(b, prefix, "e3", eps3, eps3, "point", None)
    p40 = input_dual(b, prefix, "p4_0", cell["p4"][0], cell["p4"][0], "point", None)
    p41 = input_dual(b, prefix, "p4_1", cell["p4"][1], cell["p4"][1], "point", None)
    p30 = input_dual(b, prefix, "p3_0", cell["p3"][0], cell["p3"][0], "point", None)
    p31 = input_dual(b, prefix, "p3_1", cell["p3"][1], cell["p3"][1], "point", None)
    a = p40 + p41 * t + t ** 2 * e4
    bb = p30 + p31 * t + t ** 2 * e3
    pi = TD(b.pi(), (b.zero, b.zero, b.zero))
    return source_model(t, a, bb, pi)


def displacement(b: Builder, slot: str, lo: Q, hi: Q) -> TI:
    mode = "point" if lo == hi else "range"
    return b.input(slot, lo, hi, mode)


def centered(b: Builder, whole: TD, center: TD,
             bounds: tuple[TI, TI, TI]) -> TI:
    out = center.v
    for deriv, bound in zip(whole.d, bounds):
        out = out + deriv * bound
    return b.intersect(out, whole.v)


def trace_package(cell: dict, kind: str) -> tuple[Builder, list[tuple[str, int, str]]]:
    b = Builder()
    t_radius = (cell["t"][1] - cell["t"][0]) / 2
    theta = (-t_radius, t_radius)
    e4_center = sum(cell["eps4"]) / 2
    e4_radius = (cell["eps4"][1] - cell["eps4"][0]) / 2
    e3_center = sum(cell["eps3"]) / 2
    e3_radius = (cell["eps3"][1] - cell["eps3"][0]) / 2
    if kind in ("foldLower", "foldUpper"):
        endpoint = cell["eps4"][0 if kind == "foldLower" else 1]
        whole = evaluate(b, cell, "whole", theta, endpoint, e3_center)[0]
        center = evaluate(b, cell, "center", None, endpoint, e3_center)[0]
        bounds = (displacement(b, "t_displacement", *theta),
                  displacement(b, "e4_displacement", Q(0), Q(0)),
                  displacement(b, "e3_displacement", Q(0), Q(0)))
        out = centered(b, whole, center, bounds)
        sign = "positive" if kind == "foldLower" else "negative"
        outputs = [("fold", out.ref, sign)]
    elif kind in ("areaLower", "areaUpper"):
        endpoint = cell["eps3"][0 if kind == "areaLower" else 1]
        whole_all = evaluate(b, cell, "whole", theta, cell["eps4"], endpoint)
        center_all = evaluate(b, cell, "center", None, e4_center, endpoint)
        bounds = (displacement(b, "t_displacement", *theta),
                  displacement(b, "e4_displacement", -e4_radius, e4_radius),
                  displacement(b, "e3_displacement", Q(0), Q(0)))
        out = centered(b, whole_all[1], center_all[1], bounds)
        sign = "negative" if kind == "areaLower" else "positive"
        outputs = [("area", out.ref, sign)]
    elif kind == "whole":
        whole_all = evaluate(b, cell, "whole", theta, cell["eps4"], cell["eps3"])
        center_all = evaluate(b, cell, "center", None, e4_center, e3_center)
        bounds = (displacement(b, "t_displacement", *theta),
                  displacement(b, "e4_displacement", -e4_radius, e4_radius),
                  displacement(b, "e3_displacement", -e3_radius, e3_radius))
        gap = centered(b, whole_all[2], center_all[2], bounds)
        outputs = [("gap", gap.ref, "negative")]
        for name in GUARD_NAMES:
            out = centered(b, whole_all[3][name], center_all[3][name], bounds)
            outputs.append((name, out.ref, "positive"))
    else:
        raise ValueError(f"unknown package {kind}")
    return b, outputs


def parse_cell(raw: dict) -> dict:
    return {key: tuple(Q(x) for x in raw[key])
            for key in ("t", "p4", "p3", "eps4", "eps3")}


def shape(step: dict) -> tuple:
    op = step["op"]
    if op[0] == "input":
        return op[:3]
    return op


def lean_int(x: int) -> str:
    return f"({x} : Int)" if x < 0 else str(x)


def lean_shape(op: tuple) -> str:
    tag = op[0]
    if tag == "input":
        return f".input {op[1]} .{op[2]}"
    if tag == "rat":
        return f".rat {lean_int(op[1])} {op[2]}"
    if tag == "pi":
        return ".pi"
    if tag in ("add", "mul", "intersect"):
        return f".{tag} {op[1]} {op[2]}"
    if tag in ("neg", "recip", "sqrt"):
        return f".{tag} {op[1]}"
    if tag == "pow":
        return f".pow {op[1]} {op[2]}"
    if tag in ("tailValue", "tailDerivative"):
        return f".{tag} {op[1]} {op[2]} {op[3]}"
    raise ValueError(op)


def lean_op(op: tuple) -> str:
    if op[0] != "input":
        return lean_shape(op)
    return (f".input {op[1]} .{op[2]} {lean_int(op[3])} {op[4]} "
            f"{lean_int(op[5])} {op[6]}")


def emit_array(items: list[str], indent: str = "  ") -> str:
    return "#[\n" + "\n".join(f"{indent}{x}," for x in items) + "\n]"


def emit_program(path: Path, packages: dict) -> None:
    representatives = {
        "foldLower": packages["foldLower"],
        "foldUpper": packages["foldUpper"],
        "areaLower": packages["areaLower"],
        "areaUpper": packages["areaUpper"],
        "whole": packages["whole"],
    }
    chunks = ["import NearOneScalarInteger\n",
              "set_option maxRecDepth 100000\n",
              "namespace NearOneScalarIntegerProgram\n",
              "open NearOneScalarInteger\n\n"]
    for kind in KINDS:
        builder, outputs = representatives[kind]
        shapes = emit_array([lean_shape(shape(step)) for step in builder.steps])
        bindings = emit_array([
            f"{{ ref := {ref}, sign := .{sign} }}" for _, ref, sign in outputs])
        chunks.append(f"def {kind}Shapes : Array OpShape := {shapes}\n\n")
        chunks.append(f"def {kind}Outputs : Array OutputBinding := {bindings}\n\n")
    chunks.append("def program (kind : DomainKind) : Program :=\n  match kind with\n")
    for kind in KINDS:
        chunks.append(f"  | .{kind} => ⟨{kind}Shapes, {kind}Outputs⟩\n")
    chunks.append("\nend NearOneScalarIntegerProgram\n")
    path.write_text("".join(chunks))


def emit_trace(path: Path, packages: dict) -> None:
    chunks = ["import NearOneScalarIntegerProgram\n",
              "set_option maxRecDepth 100000\n",
              "namespace NearOneScalarIntegerCell10\n",
              "open NearOneScalarInteger\n",
              "open NearOneScalarIntegerProgram\n\n"]
    names = []
    for kind in KINDS:
        builder, _ = packages[kind]
        steps = emit_array([
            f"{{ op := {lean_op(step['op'])}, out := ⟨{lean_int(step['lo'])}, {lean_int(step['hi'])}⟩ }}"
            for step in builder.steps])
        name = f"{kind}Trace"
        names.append(name)
        chunks.append(f"def {name} : Trace := ⟨.{kind}, {steps}⟩\n\n")
    traces = emit_array(names)
    chunks.append(f"def traces : Array Trace := {traces}\n\n")
    chunks.append("/-- Diagnostic Boolean only: strategy-00041 exceeded its acceptance cap before kernel proof. -/\n")
    chunks.append("def acceptanceAttempt : Bool := acceptCell program traces\n\n")
    chunks.append("end NearOneScalarIntegerCell10\n")
    path.write_text("".join(chunks))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--program-output", type=Path, required=True)
    parser.add_argument("--trace-output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    raw = reference.load_manifest(args.manifest)
    cell = parse_cell(raw["bands"][0]["cells"][10])
    if cell["t"] != reference.expected_cell(0, 10):
        raise ValueError("band-0 cell-10 locator changed")
    packages = {kind: trace_package(cell, kind) for kind in KINDS}

    observed = {}
    for kind, (builder, outputs) in packages.items():
        observed[kind] = {name: [builder.steps[ref]["lo"], builder.steps[ref]["hi"]]
                          for name, ref, _ in outputs}
    expected = reference.check_cell(cell)
    comparisons = {
        "foldLower": expected["fold_faces"]["eps_lower"],
        "foldUpper": expected["fold_faces"]["eps_upper"],
        "areaLower": expected["area_faces"]["eps_lower"],
        "areaUpper": expected["area_faces"]["eps_upper"],
        "whole_gap": expected["gap"],
    }
    def exact_to_ints(pair):
        return [int(Q(x) * S) for x in pair]
    if observed["foldLower"]["fold"] != exact_to_ints(comparisons["foldLower"]):
        raise AssertionError("fold-lower replay differs from retained preflight")
    if observed["foldUpper"]["fold"] != exact_to_ints(comparisons["foldUpper"]):
        raise AssertionError("fold-upper replay differs from retained preflight")
    if observed["areaLower"]["area"] != exact_to_ints(comparisons["areaLower"]):
        raise AssertionError("area-lower replay differs from retained preflight")
    if observed["areaUpper"]["area"] != exact_to_ints(comparisons["areaUpper"]):
        raise AssertionError("area-upper replay differs from retained preflight")
    if observed["whole"]["gap"] != exact_to_ints(comparisons["whole_gap"]):
        raise AssertionError("whole-gap replay differs from retained preflight")
    for name in GUARD_NAMES:
        if observed["whole"][name] != exact_to_ints(expected["guards"][name]):
            raise AssertionError(f"guard replay differs: {name}")

    emit_program(args.program_output, packages)
    emit_trace(args.trace_output, packages)
    all_steps = [step for b, _ in packages.values() for step in b.steps]
    widths = [abs(x).bit_length() for step in all_steps
              for x in (step["lo"], step["hi"])]
    op_counts = {}
    for step in all_steps:
        tag = step["op"][0]
        op_counts[tag] = op_counts.get(tag, 0) + 1
    receipt = {
        "schema": "cmv-source-native-integer-trace-v1",
        "proof_status": "UNTRUSTED_TRACE_INPUT",
        "cell": {"band": 0, "index": 10},
        "arithmetic_bits": 160,
        "atan_remainder_terms": TERMS,
        "domain_packages": list(KINDS),
        "input_slots": SLOTS,
        "guard_names": list(GUARD_NAMES),
        "step_counts": {kind: len(builder.steps)
                        for kind, (builder, _) in packages.items()},
        "total_steps": len(all_steps),
        "operation_counts": op_counts,
        "maximum_saved_endpoint_bits": max(widths),
        "outputs": observed,
        "reference_match": "exact integer endpoint equality for all four faces, gap, and 44 guards",
        "manifest_sha256": hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
        "program_sha256": hashlib.sha256(args.program_output.read_bytes()).hexdigest(),
        "trace_sha256": hashlib.sha256(args.trace_output.read_bytes()).hexdigest(),
    }
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "outputs"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
