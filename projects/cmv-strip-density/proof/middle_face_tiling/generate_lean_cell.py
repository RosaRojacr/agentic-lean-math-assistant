#!/usr/bin/env python3
"""Generate one kernel-replayed middle-face cell from an exact brick shard.

The JSON shard supplies only rational affine data.  This script recomputes the
coarse affine boxes and degree-27/26 Taylor enclosures used by the Lean proof.
The generated theorem does not trust this script: Lean replays every enclosure
with ``sinTaylor27Interval_sound``, ``cosTaylor26Interval_sound``, and exact
rational normalization.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from math import factorial
import hashlib
import json
from pathlib import Path
import re
from typing import Any

Q = Fraction
Interval = tuple[Q, Q]
SCHEMA = "cmv-middle-face-brick-v1"
MODEL = "cmv-angle-fold-equal-area-v1"
ROOT_KEYS = {"schema", "model", "brick_id", "brick", "payload_sha256"}
BRICK_KEYS = {
    "lambda", "centers", "slopes", "y_xi_slope", "v_rho_slope", "radii"
}
ANGLE_SCALE = 100_000
TRIG_SCALE = 1_000_000
FINE_SCALE = 100_000_000
EXPECTED_RADII = (Q(1, 100_000), Q(1, 1_000_000),
                  Q(1, 100_000), Q(1, 1_000_000))
FULL_T_RADIUS = Q(1, 20_000)
PI_LO = Q(3_141_592, 1_000_000)
PI_HI = Q(3_141_593, 1_000_000)
GAP_MARGIN = Q(437, 1_000_000)
K3_W_SLAB_HI = Q(12, 25)
K3_V_SLAB_HI = Q(8, 15)


def fail(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def qstr(value: Q) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def lean_q(value: Q) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator} / {value.denominator}"


def parse_q(value: Any, label: str) -> Q:
    fail(isinstance(value, str), f"{label} must be a rational string")
    fail(re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", value) is not None,
         f"{label} must be a canonical rational string")
    result = Q(value)
    fail(qstr(result) == value, f"{label} must be reduced")
    return result


def semantic_hash(raw: dict[str, Any]) -> str:
    payload = {key: value for key, value in raw.items() if key != "payload_sha256"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"),
                         ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


@dataclass(frozen=True)
class Brick:
    brick_id: str
    lam: tuple[Q, Q]
    centers: tuple[Q, Q, Q, Q]
    slopes: tuple[Q, Q, Q, Q]
    y_xi_slope: Q
    v_rho_slope: Q
    radii: tuple[Q, Q, Q, Q]

    @property
    def cell_number(self) -> int:
        return int(self.brick_id[1:])


def qtuple(raw: Any, length: int, label: str) -> tuple[Q, ...]:
    fail(isinstance(raw, list) and len(raw) == length,
         f"{label} must contain {length} rationals")
    return tuple(parse_q(value, f"{label}[{index}]")
                 for index, value in enumerate(raw))


def read_brick(path: Path) -> Brick:
    raw = json.loads(path.read_text(encoding="utf-8"))
    fail(isinstance(raw, dict) and set(raw) == ROOT_KEYS,
         "brick shard root keys mismatch")
    fail(raw["schema"] == SCHEMA, "brick schema mismatch")
    fail(raw["model"] == MODEL, "brick model mismatch")
    fail(isinstance(raw["brick_id"], str) and
         re.fullmatch(r"B[0-9]{4}", raw["brick_id"]) is not None,
         "brick_id must have the form Bdddd")
    fail(path.stem == raw["brick_id"], "brick_id does not match the input filename")
    fail(isinstance(raw["payload_sha256"], str) and
         re.fullmatch(r"[0-9a-f]{64}", raw["payload_sha256"]) is not None,
         "payload_sha256 must be lowercase hexadecimal")
    fail(semantic_hash(raw) == raw["payload_sha256"], "brick payload hash mismatch")

    body = raw["brick"]
    fail(isinstance(body, dict) and set(body) == BRICK_KEYS,
         "brick data keys mismatch")
    lam_raw = qtuple(body["lambda"], 2, "brick.lambda")
    centers_raw = qtuple(body["centers"], 4, "brick.centers")
    slopes_raw = qtuple(body["slopes"], 4, "brick.slopes")
    radii_raw = qtuple(body["radii"], 4, "brick.radii")
    lam = (lam_raw[0], lam_raw[1])
    centers = (centers_raw[0], centers_raw[1], centers_raw[2], centers_raw[3])
    slopes = (slopes_raw[0], slopes_raw[1], slopes_raw[2], slopes_raw[3])
    radii = (radii_raw[0], radii_raw[1], radii_raw[2], radii_raw[3])
    y_xi_slope = parse_q(body["y_xi_slope"], "brick.y_xi_slope")
    v_rho_slope = parse_q(body["v_rho_slope"], "brick.v_rho_slope")

    width = lam[1] - lam[0]
    fail(Q(0) < width <= Q(1, 10_000),
         "lambda width must satisfy 0 < width <= 1/10000")
    fail(radii == EXPECTED_RADII,
         "the current Lean template requires the recorded face radii")
    fail(all(value > 0 for value in slopes), "all affine slopes must be positive")
    fail(y_xi_slope > 0 and v_rho_slope > 0,
         "correlation slopes must be positive")
    return Brick(raw["brick_id"], lam, centers, slopes,
                 y_xi_slope, v_rho_slope, radii)


def add(left: Interval, right: Interval) -> Interval:
    return left[0] + right[0], left[1] + right[1]


def mul(left: Interval, right: Interval) -> Interval:
    corners = (left[0] * right[0], left[0] * right[1],
               left[1] * right[0], left[1] * right[1])
    return min(corners), max(corners)


def symmetric(radius: Q) -> Interval:
    return -radius, radius


def affine(center: Q, *terms: tuple[Q, Interval]) -> Interval:
    result = (center, center)
    for coefficient, value in terms:
        result = add(result, mul((coefficient, coefficient), value))
    return result


def floor_scaled(value: Q, scale: int) -> int:
    return value.numerator * scale // value.denominator


def ceil_scaled(value: Q, scale: int) -> int:
    return -((-value.numerator * scale) // value.denominator)


def strict_floor_scaled(value: Q, scale: int) -> int:
    """Largest integer n with n/scale strictly below value."""
    return ceil_scaled(value, scale) - 1


def sin_taylor_27(value: Q) -> Q:
    return sum((Q((-1) ** k) * value ** (2 * k + 1) /
                factorial(2 * k + 1) for k in range(14)), Q())


def cos_taylor_26(value: Q) -> Q:
    return sum((Q((-1) ** k) * value ** (2 * k) /
                factorial(2 * k) for k in range(14)), Q())


def sin_interval(value: Q) -> Interval:
    polynomial = sin_taylor_27(value)
    radius = abs(value) ** 28 / factorial(28)
    return polynomial - radius, polynomial + radius


def cos_interval(value: Q) -> Interval:
    polynomial = cos_taylor_26(value)
    radius = abs(value) ** 27 / factorial(27)
    return polynomial - radius, polynomial + radius


@dataclass(frozen=True)
class Bounds:
    brick: Brick
    # Integer numerators at denominators ANGLE_SCALE and TRIG_SCALE.
    angles: tuple[tuple[int, int], tuple[int, int], tuple[int, int], tuple[int, int]]
    trig: tuple[tuple[int, int, int, int], tuple[int, int, int, int],
                tuple[int, int, int, int], tuple[int, int, int, int]]
    k3_w_hi: int
    k3_v_hi: int
    gap_a_hi: int
    gap_b_lo: int
    gap_factor_lo: int


def derive_bounds(brick: Brick) -> Bounds:
    t = symmetric((brick.lam[1] - brick.lam[0]) / 2)
    radius = tuple(symmetric(value) for value in brick.radii)
    exact = (
        affine(brick.centers[0], (brick.slopes[0], t), (Q(1), radius[0])),
        affine(brick.centers[1], (brick.slopes[1], t),
               (brick.y_xi_slope, radius[0]), (Q(1), radius[1])),
        affine(brick.centers[2], (brick.slopes[2], t), (Q(1), radius[2])),
        affine(brick.centers[3], (brick.slopes[3], t),
               (brick.v_rho_slope, radius[2]), (Q(1), radius[3])),
    )
    angles_raw = tuple((floor_scaled(value[0], ANGLE_SCALE),
                        ceil_scaled(value[1], ANGLE_SCALE)) for value in exact)
    angles = (angles_raw[0], angles_raw[1], angles_raw[2], angles_raw[3])
    fail(all(0 < lo < hi < 78_539 for lo, hi in angles),
         "an affine angle box is outside (0, pi/4)")
    fail(angles[0][1] < angles[1][0] and angles[2][1] < angles[3][0],
         "coarse affine boxes do not prove the required angle ordering")

    trig_raw: list[tuple[int, int, int, int]] = []
    for lo_num, hi_num in angles:
        lo, hi = Q(lo_num, ANGLE_SCALE), Q(hi_num, ANGLE_SCALE)
        trig_raw.append((
            floor_scaled(sin_interval(lo)[0], TRIG_SCALE),
            ceil_scaled(sin_interval(hi)[1], TRIG_SCALE),
            floor_scaled(cos_interval(hi)[0], TRIG_SCALE),
            ceil_scaled(cos_interval(lo)[1], TRIG_SCALE),
        ))
    trig = (trig_raw[0], trig_raw[1], trig_raw[2], trig_raw[3])

    x, y, w, v = angles
    tx, _ty, tw, tv = trig
    k3_w_hi = ceil_scaled(Q(w[1], ANGLE_SCALE), 500)
    k3_v_hi = max(470, ceil_scaled(exact[3][1], 1_000))
    fail(Q(k3_v_hi, 1_000) <= K3_V_SLAB_HI,
         "the generated K3 v slab exceeds the template's trigonometric bounds")
    fail(Q(k3_w_hi, 500) <= K3_W_SLAB_HI,
         "the generated K3 w slab exceeds the template's trigonometric bounds")
    a_exact = (brick.lam[1] * Q(v[1], ANGLE_SCALE) + PI_HI -
               Q(w[0], ANGLE_SCALE) + Q(tv[1], TRIG_SCALE) -
               Q(tw[0], TRIG_SCALE))
    b_exact = (brick.lam[0] * Q(y[0], ANGLE_SCALE) + PI_LO / 2 -
               Q(x[1], ANGLE_SCALE))
    gap_a_hi = ceil_scaled(a_exact, 5_000)
    gap_b_lo = floor_scaled(b_exact, 10_000)
    gap_factor_lo = strict_floor_scaled(Q(1) + Q(tw[2], TRIG_SCALE), 100_000)
    first_hi = Q(tx[3], TRIG_SCALE) * Q(gap_a_hi, 5_000)
    second_lo = Q(gap_factor_lo, 100_000) * Q(gap_b_lo, 10_000)
    fail(gap_b_lo > 0 and gap_factor_lo > 0,
         "gap decomposition lost positivity")
    fail(first_hi - second_lo < -GAP_MARGIN,
         "the template's uniform gap margin is not certified")
    return Bounds(brick, angles, trig, k3_w_hi, k3_v_hi,
                  gap_a_hi, gap_b_lo, gap_factor_lo)


def fixed_q(numerator: int, denominator: int) -> str:
    return f"{numerator} / {denominator}"

def k3_v_tokens(bounds: Bounds) -> tuple[str, str, str]:
    upper = lean_q(Q(bounds.k3_v_hi, 1_000))
    return (
        f"have hvHi : v p ≤ ({upper} : ℝ)",
        f"(⟨9 / 20, {upper}, by norm_num⟩ : QInterval).RealContains (v p)",
        f"(sinTaylor27Interval_sound ({upper})).2",
    )


def replacement_tokens(bounds: Bounds) -> dict[str, str]:
    result = {
        "lam_lo": lean_q(bounds.brick.lam[0]),
        "lam_hi": lean_q(bounds.brick.lam[1]),
        "k3_w_hi": lean_q(Q(bounds.k3_w_hi, 500)),
        "gap_a_hi": fixed_q(bounds.gap_a_hi, 5_000),
        "gap_b_lo": fixed_q(bounds.gap_b_lo, 10_000),
        "gap_factor_lo": fixed_q(bounds.gap_factor_lo, 100_000),
        "t_radius": lean_q((bounds.brick.lam[1] - bounds.brick.lam[0]) / 2),
    }
    names = ("x", "y", "w", "v")
    for name, (lo, hi), (sin_lo, sin_hi, cos_lo, cos_hi) in zip(
            names, bounds.angles, bounds.trig):
        result[f"{name}_lo"] = fixed_q(lo, ANGLE_SCALE)
        result[f"{name}_hi"] = fixed_q(hi, ANGLE_SCALE)
        result[f"{name}_lo_fine"] = fixed_q(lo * 1_000, FINE_SCALE)
        result[f"{name}_hi_fine"] = fixed_q(hi * 1_000, FINE_SCALE)
        for function, lower, upper in (("sin", sin_lo, sin_hi),
                                       ("cos", cos_lo, cos_hi)):
            result[f"{function}_{name}_lo"] = fixed_q(lower, TRIG_SCALE)
            result[f"{function}_{name}_hi"] = fixed_q(upper, TRIG_SCALE)
            result[f"{function}_{name}_lo_fine"] = fixed_q(lower * 100, FINE_SCALE)
            result[f"{function}_{name}_hi_fine"] = fixed_q(upper * 100, FINE_SCALE)
    return result


def brick_documentation(brick: Brick) -> str:
    return (
        f"/-- Exact inventory brick `{brick.brick_id}`, spanning "
        f"`[{qstr(brick.lam[0])}, {qstr(brick.lam[1])}]`. -/"
    )


def brick_definition(brick: Brick) -> str:
    centers = [lean_q(value) for value in brick.centers]
    slopes = [lean_q(value) for value in brick.slopes]
    radii = [lean_q(value) for value in brick.radii]
    return "\n".join([
        "def brick : Brick where",
        f"  lamLo := {lean_q(brick.lam[0])}",
        f"  lamHi := {lean_q(brick.lam[1])}",
        f"  centers := ![{centers[0]},",
        f"    {centers[1]},",
        f"    {centers[2]},",
        f"    {centers[3]}]",
        f"  slopes := ![{slopes[0]},",
        f"    {slopes[1]},",
        f"    {slopes[2]},",
        f"    {slopes[3]}]",
        f"  yXiSlope := {lean_q(brick.y_xi_slope)}",
        f"  vRhoSlope := {lean_q(brick.v_rho_slope)}",
        f"  radii := ![{', '.join(radii)}]",
        "  lamOrdered := by norm_num",
        "  radiiPos := by intro j; fin_cases j <;> norm_num",
    ]) + "\n"


def replace_brick_definition(source: str, replacement: str) -> str:
    start_marker = "def brick : Brick where\n"
    end_marker = "  radiiPos := by intro j; fin_cases j <;> norm_num\n"
    fail(source.count(start_marker) == 1 and source.count(end_marker) == 1,
         "template brick-definition markers changed")
    start = source.index(start_marker)
    end = source.index(end_marker, start) + len(end_marker)
    return source[:start] + replacement + source[end:]


def substitute_simultaneously(source: str, substitutions: dict[str, str]) -> str:
    changed = {
        old: new for old, new in substitutions.items()
        if old != new and old in source
    }
    if not changed:
        return source
    pattern = re.compile("|".join(re.escape(old)
                                  for old in sorted(changed, key=len, reverse=True)))
    return pattern.sub(lambda match: changed[match.group(0)], source)


def validate_template(source: str, bounds: Bounds) -> None:
    tokens = replacement_tokens(bounds)
    for key, value in tokens.items():
        if key != "cos_w_hi":
            fail(value in source, f"template is missing derived token {key}: {value}")
    for token in k3_v_tokens(bounds):
        fail(source.count(token) == 1,
             f"template is missing unique K3 v token: {token}")
    fail(source.count(bounds.brick.brick_id) > 0,
         "template does not name its brick")
    fail(source.count(f"namespace MiddleFaceCell{bounds.brick.cell_number}") == 1,
         "template namespace does not match its brick")


def render_core(template: str, template_bounds: Bounds, target_bounds: Bounds) -> str:
    old = replacement_tokens(template_bounds)
    new = replacement_tokens(target_bounds)
    fail(old.keys() == new.keys(), "internal replacement schema mismatch")
    source = template
    for old_token, new_token in zip(k3_v_tokens(template_bounds),
                                    k3_v_tokens(target_bounds)):
        fail(source.count(old_token) == 1,
             f"template K3 v token is not unique: {old_token}")
        source = source.replace(old_token, new_token)
    substitutions: dict[str, str] = {}
    for key in old:
        prior = substitutions.get(old[key])
        fail(prior is None or prior == new[key],
             f"ambiguous template token generated by {key}: {old[key]}")
        substitutions[old[key]] = new[key]
    source = substitute_simultaneously(source, substitutions)
    old_documentation = brick_documentation(template_bounds.brick)
    fail(source.count(old_documentation) == 1,
         "template inventory-brick documentation changed")
    source = source.replace(
        old_documentation, brick_documentation(target_bounds.brick))
    source = replace_brick_definition(source, brick_definition(target_bounds.brick))
    source = source.replace(template_bounds.brick.brick_id,
                            target_bounds.brick.brick_id)
    source = source.replace(
        f"MiddleFaceCell{template_bounds.brick.cell_number}",
        f"MiddleFaceCell{target_bounds.brick.cell_number}")
    return source

def render_radius_contracts(source: str, radius: Q) -> str:
    """Select the radius-aware residual API for a generated narrow cell."""
    if radius == FULL_T_RADIUS:
        return source

    lean_radius = f"({lean_q(radius)} : ℝ)"
    derivative_contracts = (
        "MiddleFaceAssembly.C4Residual.DerivativeBounds",
        "MiddleFaceAssembly.FResidual.DerivativeBounds",
        "MiddleFaceAssembly.C3Residual.DerivativeBounds",
    )
    for contract in derivative_contracts:
        old = f"{contract} brick"
        new = f"{contract}On brick {lean_radius}"
        fail(source.count(old) == 1,
             f"generated source is missing unique residual contract: {old}")
        source = source.replace(old, new)
    for theorem in ("low_face_margin", "high_face_margin"):
        old = f"{theorem} brick"
        new = (f"{theorem}_on (R := {lean_radius}) brick\n"
               "    (by norm_num) (by norm_num)")
        fail(source.count(old) == 4,
             f"generated source must contain four residual calls: {theorem}")
        source = source.replace(old, new)
    return source



def render(input_path: Path, template_path: Path, template_input_path: Path) -> str:
    target_bounds = derive_bounds(read_brick(input_path))
    template_bounds = derive_bounds(read_brick(template_input_path))
    template_radius = ((template_bounds.brick.lam[1] -
                        template_bounds.brick.lam[0]) / 2)
    fail(template_radius == FULL_T_RADIUS,
         "Lean generation requires an existing full-width template")
    template = template_path.read_text(encoding="utf-8")
    validate_template(template, template_bounds)
    fail(render_core(template, template_bounds, template_bounds) == template,
         "template does not exactly match its brick shard and derived bounds")
    output = render_core(template, template_bounds, target_bounds)
    target_radius = ((target_bounds.brick.lam[1] -
                      target_bounds.brick.lam[0]) / 2)
    output = render_radius_contracts(output, target_radius)
    for forbidden in ("sorry", "admit", "axiom", "native_decide"):
        fail(re.search(rf"\b{forbidden}\b", output) is None,
             f"generated output contains forbidden token {forbidden}")
    return output


def main() -> int:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=here / "bricks" / "B0005.json")
    parser.add_argument("--template", type=Path, default=here.parent / "MiddleFaceCell4.lean")
    parser.add_argument("--template-input", type=Path,
                        default=here / "bricks" / "B0004.json")
    parser.add_argument("--output", type=Path, default=here.parent / "MiddleFaceCell5.lean")
    args = parser.parse_args()
    output = render(args.input.resolve(), args.template.resolve(),
                    args.template_input.resolve())
    args.output.resolve().write_text(output, encoding="utf-8")
    print(f"wrote {args.output} ({len(output.encode())} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
