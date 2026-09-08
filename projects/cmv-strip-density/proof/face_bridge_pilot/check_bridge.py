#!/usr/bin/env python3
"""Fail-closed exact-rational checker for slanted CMV opposite-face bricks."""
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
from typing import Any, Callable

SCHEMA = "cmv-opposite-face-bridge-pilot-v1"
MODEL = "cmv-angle-fold-equal-area-v1"
ATAN_TERMS = 36
TRIG_TERMS = 14
NVAR = 5  # centered lambda t, xi, eta, rho, sigma
PI_FORMULA = "16*atan(1/5)-4*atan(1/239)"


class CheckFailure(Exception):
    def __init__(self, code: str, phase: str, brick: int | None, detail: str, value: "I | None" = None):
        super().__init__(detail)
        self.code, self.phase, self.brick, self.detail, self.value = code, phase, brick, detail, value


def require(ok: bool, code: str, phase: str, brick: int | None, detail: str, value: "I | None" = None) -> None:
    if not ok:
        raise CheckFailure(code, phase, brick, detail, value)


def strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise CheckFailure("DUPLICATE_JSON_KEY", "parse", None, key)
        out[key] = value
    return out


def load_json(path: Path) -> dict[str, Any]:
    def bad_constant(value: str) -> None:
        raise CheckFailure("NONFINITE_JSON", "parse", None, value)
    try:
        raw = json.loads(path.read_text(), object_pairs_hook=strict_object, parse_constant=bad_constant)
    except CheckFailure:
        raise
    except Exception as exc:
        raise CheckFailure("INVALID_JSON", "parse", None, str(exc)) from exc
    require(isinstance(raw, dict), "TOP_LEVEL_NOT_OBJECT", "schema", None, "top level")
    return raw


def exact_keys(value: dict[str, Any], keys: set[str], code: str, phase: str, brick: int | None = None) -> None:
    require(set(value) == keys, code, phase, brick, f"expected {sorted(keys)}, got {sorted(value)}")


def parse_q(value: Any, label: str, brick: int | None = None) -> Q:
    require(isinstance(value, str), "RATIONAL_NOT_STRING", "schema", brick, label)
    parts = value.split("/")
    require(len(parts) in (1, 2), "MALFORMED_RATIONAL", "schema", brick, label)
    try:
        numerator = int(parts[0])
        denominator = 1 if len(parts) == 1 else int(parts[1])
    except ValueError as exc:
        raise CheckFailure("MALFORMED_RATIONAL", "schema", brick, label) from exc
    require(denominator > 0, "NONPOSITIVE_DENOMINATOR", "schema", brick, label)
    answer = Q(numerator, denominator)
    require(str(answer) == value, "NONCANONICAL_RATIONAL", "schema", brick, label)
    return answer


def qstr(q: Q) -> str:
    return str(q)


@dataclass(frozen=True)
class I:
    lo: Q
    hi: Q

    def __post_init__(self) -> None:
        if self.lo > self.hi:
            raise CheckFailure("REVERSED_INTERVAL", "arithmetic", None, f"{self.lo}>{self.hi}")

    @staticmethod
    def point(value: Q | int) -> "I":
        return I(Q(value), Q(value))

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
        values = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return I(min(values), max(values))

    __rmul__ = __mul__

    def reciprocal(self) -> "I":
        if not (self.hi < 0 or self.lo > 0):
            raise CheckFailure("DENOMINATOR_CONTAINS_ZERO", "denominators", None, "reciprocal", self)
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, other: "I | Q | int") -> "I":
        return self * as_i(other).reciprocal()

    def __rtruediv__(self, other: "I | Q | int") -> "I":
        return as_i(other) / self


def as_i(value: I | Q | int) -> I:
    return value if isinstance(value, I) else I.point(Q(value))


def atan_small(value: Q) -> I:
    require(0 <= value <= Q(1, 2), "ATAN_RANGE", "arithmetic", None, str(value))
    total, power, square = Q(0), value, value * value
    for k in range(ATAN_TERMS):
        term = power / (2 * k + 1)
        total = total + term if k % 2 == 0 else total - term
        power *= square
    omitted = power / (2 * ATAN_TERMS + 1)
    alternate = total + (omitted if ATAN_TERMS % 2 == 0 else -omitted)
    return I(min(total, alternate), max(total, alternate))


PI = 16 * atan_small(Q(1, 5)) - 4 * atan_small(Q(1, 239))


def sin_q(value: Q) -> I:
    require(0 <= value <= PI.lo / 4, "TRIG_RANGE", "arithmetic", None, str(value))
    total, power, factorial = Q(0), value, 1
    for k in range(TRIG_TERMS):
        if k:
            power *= value * value
            factorial *= (2 * k) * (2 * k + 1)
        term = power / factorial
        total = total + term if k % 2 == 0 else total - term
    degree = 2 * TRIG_TERMS - 1
    error = value ** (degree + 1) / math.factorial(degree + 1)
    return I(total - error, total + error)


def cos_q(value: Q) -> I:
    require(0 <= value <= PI.lo / 4, "TRIG_RANGE", "arithmetic", None, str(value))
    total, power, factorial = Q(0), Q(1), 1
    for k in range(TRIG_TERMS):
        if k:
            power *= value * value
            factorial *= (2 * k - 1) * (2 * k)
        term = power / factorial
        total = total + term if k % 2 == 0 else total - term
    degree = 2 * TRIG_TERMS - 2
    error = value ** (degree + 1) / math.factorial(degree + 1)
    return I(total - error, total + error)


def sin_i(value: I) -> I:
    require(0 <= value.lo <= value.hi <= PI.lo / 4, "ANGLE_OUT_OF_RANGE", "branches", None, str(value))
    return I(sin_q(value.lo).lo, sin_q(value.hi).hi)


def cos_i(value: I) -> I:
    require(0 <= value.lo <= value.hi <= PI.lo / 4, "ANGLE_OUT_OF_RANGE", "branches", None, str(value))
    return I(cos_q(value.hi).lo, cos_q(value.lo).hi)


@dataclass(frozen=True)
class D:
    v: I
    d: tuple[I, ...]

    @staticmethod
    def constant(value: I | Q | int) -> "D":
        return D(as_i(value), (I.point(0),) * NVAR)

    def __add__(self, other: "D | I | Q | int") -> "D":
        o = as_d(other)
        return D(self.v + o.v, tuple(a + b for a, b in zip(self.d, o.d)))

    __radd__ = __add__

    def __neg__(self) -> "D":
        return D(-self.v, tuple(-a for a in self.d))

    def __sub__(self, other: "D | I | Q | int") -> "D":
        return self + (-as_d(other))

    def __rsub__(self, other: "D | I | Q | int") -> "D":
        return as_d(other) - self

    def __mul__(self, other: "D | I | Q | int") -> "D":
        o = as_d(other)
        return D(self.v * o.v, tuple(a * o.v + self.v * b for a, b in zip(self.d, o.d)))

    __rmul__ = __mul__

    def reciprocal(self) -> "D":
        inv = self.v.reciprocal()
        return D(inv, tuple(-a * inv * inv for a in self.d))

    def __truediv__(self, other: "D | I | Q | int") -> "D":
        return self * as_d(other).reciprocal()

    def __rtruediv__(self, other: "D | I | Q | int") -> "D":
        return as_d(other) / self


def as_d(value: D | I | Q | int) -> D:
    return value if isinstance(value, D) else D.constant(value)


def sin_d(value: D) -> D:
    return D(sin_i(value.v), tuple(cos_i(value.v) * a for a in value.d))


def cos_d(value: D) -> D:
    return D(cos_i(value.v), tuple(-sin_i(value.v) * a for a in value.d))


@dataclass(frozen=True)
class Brick:
    lam_lo: Q
    lam_hi: Q
    centers: tuple[Q, Q, Q, Q]
    slopes: tuple[Q, Q, Q, Q]
    y_xi_slope: Q
    v_rho_slope: Q
    radii: tuple[Q, Q, Q, Q]

    @property
    def lam_mid(self) -> Q:
        return (self.lam_lo + self.lam_hi) / 2

    @property
    def t_radius(self) -> Q:
        return (self.lam_hi - self.lam_lo) / 2


def parse_pair(value: Any, label: str, brick: int) -> tuple[Q, Q]:
    require(isinstance(value, list) and len(value) == 2, "BAD_PAIR", "schema", brick, label)
    lo, hi = parse_q(value[0], label + ".lo", brick), parse_q(value[1], label + ".hi", brick)
    require(lo < hi, "NONPOSITIVE_INTERVAL_WIDTH", "schema", brick, label)
    return lo, hi


def parse_vector(value: Any, label: str, brick: int, length: int) -> tuple[Q, ...]:
    require(isinstance(value, list) and len(value) == length, "BAD_VECTOR", "schema", brick, label)
    return tuple(parse_q(item, f"{label}[{j}]", brick) for j, item in enumerate(value))


def parse_brick(raw: Any, index: int) -> Brick:
    require(isinstance(raw, dict), "BRICK_NOT_OBJECT", "schema", index, "brick")
    exact_keys(raw, {"lambda", "centers", "slopes", "y_xi_slope", "v_rho_slope", "radii"}, "BRICK_FIELDS", "schema", index)
    lo, hi = parse_pair(raw["lambda"], "lambda", index)
    centers = parse_vector(raw["centers"], "centers", index, 4)
    slopes = parse_vector(raw["slopes"], "slopes", index, 4)
    radii = parse_vector(raw["radii"], "radii", index, 4)
    require(all(r > 0 for r in radii), "NONPOSITIVE_RADIUS", "schema", index, "radii")
    return Brick(lo, hi, centers, slopes, parse_q(raw["y_xi_slope"], "y_xi_slope", index), parse_q(raw["v_rho_slope"], "v_rho_slope", index), radii)  # type: ignore[arg-type]


def semantic_hash(raw: dict[str, Any]) -> str:
    payload = {key: value for key, value in raw.items() if key != "payload_sha256"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def independent(bounds: tuple[I, ...]) -> tuple[D, ...]:
    result = []
    for j, bound in enumerate(bounds):
        gradient = [I.point(0)] * NVAR
        gradient[j] = I.point(1)
        result.append(D(bound, tuple(gradient)))
    return tuple(result)


def model(brick: Brick, bounds: tuple[I, ...]) -> dict[str, D]:
    t, xi, eta, rho, sigma = independent(bounds)
    lam = brick.lam_mid + t
    x = brick.centers[0] + brick.slopes[0] * t + xi
    y = brick.centers[1] + brick.slopes[1] * t + brick.y_xi_slope * xi + eta
    w = brick.centers[2] + brick.slopes[2] * t + rho
    v = brick.centers[3] + brick.slopes[3] * t + brick.v_rho_slope * rho + sigma
    sx, cx, sy, cy = sin_d(x), cos_d(x), sin_d(y), cos_d(y)
    sw, cw, sv, cv = sin_d(w), cos_d(w), sin_d(v), cos_d(v)
    b4 = lam * y + PI / 2 - x
    d4 = sy - sx
    n4 = b4 + cx * d4
    b3 = lam * v + PI - w
    d3 = sv - sw
    n3 = b3 + (cw + 2) * d3
    c4 = cx - lam * cy
    fold = cx * d4 - sx * sy * b4
    c3 = cw - lam * cv
    area = 2 * cx * cx * n3 - (1 + cw) * (1 + cw) * n4
    gap = cx * (b3 + d3) - (1 + cw) * b4
    h3 = (1 + cw) / 2
    droot3 = lam * sv
    k3 = 4 * h3 * ((1 + cw) / sw - (lam * lam + cw) / (lam * droot3)) - 2 * (b3 + d3)
    return {"lambda": lam, "x": x, "y": y, "w": w, "v": v, "sin_x": sx, "cos_x": cx, "sin_w": sw, "cos_w": cw, "C4": c4, "F": fold, "C3": c3, "E": area, "G": gap, "K3": k3}


def base_bounds(brick: Brick, fixed: int | None = None, side: int = 0) -> tuple[tuple[I, ...], tuple[I, ...]]:
    radii = (brick.t_radius,) + brick.radii
    full = tuple(I(-r, r) for r in radii)
    if fixed is not None:
        endpoint = Q(side) * radii[fixed]
        full = tuple(I.point(endpoint) if j == fixed else value for j, value in enumerate(full))
    base = tuple(I.point((value.lo + value.hi) / 2) for value in full)
    return full, base


def mean_enclosure(brick: Brick, name: str, fixed: int | None = None, side: int = 0) -> I:
    full, base = base_bounds(brick, fixed, side)
    whole = model(brick, full)[name]
    center = model(brick, base)[name].v
    answer = center
    for derivative, domain, point in zip(whole.d, full, base):
        answer = answer + derivative * (domain - point)
    return answer


def signed_check(value: I, orientation: str, code: str, phase: str, brick: int) -> Q:
    if orientation == "positive":
        require(value.lo > 0, code, phase, brick, "required lo > 0", value)
        return value.lo
    require(value.hi < 0, code, phase, brick, "required hi < 0", value)
    return -value.hi


def check_brick(brick: Brick, index: int) -> dict[str, str]:
    full, _ = base_bounds(brick)
    values = model(brick, full)
    require(brick.lam_lo > 1, "LAMBDA_NOT_ABOVE_ONE", "branches", index, str(brick.lam_lo))
    for angle in ("x", "y", "w", "v"):
        value = values[angle].v
        require(value.lo > 0 and value.hi < PI.lo / 4, "ANGLE_BRANCH_GUARD", "branches", index, angle, value)
    require(values["y"].v.lo > values["x"].v.hi, "TYPE4_ANGLE_ORDER", "branches", index, "x<y")
    require(values["v"].v.lo > values["w"].v.hi, "TYPE3_ANGLE_ORDER", "branches", index, "w<v")
    require(values["sin_x"].v.lo > 0 and values["cos_x"].v.lo > 0 and values["sin_w"].v.lo > 0 and values["cos_w"].v.lo > 0, "POSITIVE_FACTOR_GUARD", "denominators", index, "trig factors")

    # Scalar uniqueness, not interval-Jacobian inversion: on C4=0 the exact
    # K4 derivative is 4 h^2(U^-3-lambda*D^-3)>0 because lambda>1 and y>x.
    # Since h=cos(x) decreases, the reduced fold has strictly negative x derivative.
    fold_unique_margin = min(brick.lam_lo - 1, values["y"].v.lo - values["x"].v.hi)
    require(fold_unique_margin > 0, "FOLD_DERIVATIVE_NOT_STRICT", "uniqueness", index, "lambda>1 and y>x")

    k3 = values["K3"].v
    k3_margin = signed_check(k3, "negative", "DESCENDING_K3_NOT_NEGATIVE", "uniqueness", index)

    obligations = [
        ("C4", 2, -1, "negative", "C4_ETA_LO_NOT_NEGATIVE", "type4_faces"),
        ("C4", 2, +1, "positive", "C4_ETA_HI_NOT_POSITIVE", "type4_faces"),
        ("F", 1, -1, "positive", "F_XI_LO_NOT_POSITIVE", "fold_faces"),
        ("F", 1, +1, "negative", "F_XI_HI_NOT_NEGATIVE", "fold_faces"),
        ("C3", 4, -1, "negative", "C3_SIGMA_LO_NOT_NEGATIVE", "type3_faces"),
        ("C3", 4, +1, "positive", "C3_SIGMA_HI_NOT_POSITIVE", "type3_faces"),
        ("E", 3, -1, "negative", "E_RHO_LO_NOT_NEGATIVE", "area_faces"),
        ("E", 3, +1, "positive", "E_RHO_HI_NOT_POSITIVE", "area_faces"),
    ]
    margins: dict[str, Q] = {"fold_uniqueness": fold_unique_margin, "descending_k3": k3_margin}
    for name, fixed, side, orientation, code, phase in obligations:
        enclosure = mean_enclosure(brick, name, fixed, side)
        margins[code] = signed_check(enclosure, orientation, code, phase, index)
    gap = mean_enclosure(brick, "G")
    margins["gap"] = signed_check(gap, "negative", "GAP_NOT_NEGATIVE", "gap", index)
    return {key: qstr(value) for key, value in margins.items()}


def check(path: Path) -> dict[str, Any]:
    raw = load_json(path)
    exact_keys(raw, {"schema", "model", "arithmetic", "prototype_scope", "bricks", "payload_sha256"}, "TOP_LEVEL_FIELDS", "schema")
    require(raw["schema"] == SCHEMA, "SCHEMA_MISMATCH", "schema", None, str(raw["schema"]))
    require(raw["model"] == MODEL, "MODEL_MISMATCH", "schema", None, str(raw["model"]))
    exact_keys(raw["arithmetic"], {"atan_terms", "trig_terms", "pi_formula", "decision_type"}, "ARITHMETIC_FIELDS", "schema")
    require(raw["arithmetic"] == {"atan_terms": ATAN_TERMS, "trig_terms": TRIG_TERMS, "pi_formula": PI_FORMULA, "decision_type": "fractions.Fraction mean-value intervals"}, "ARITHMETIC_MISMATCH", "schema", None, "pinned arithmetic")
    exact_keys(raw["prototype_scope"], {"near_one_proposed_overlap", "compact_overlap", "uncovered_lambda_intervals", "claim"}, "SCOPE_FIELDS", "schema")
    require(raw["prototype_scope"]["near_one_proposed_overlap"] == "51/50", "NEAR_ONE_ENDPOINT_MISMATCH", "coverage", None, "51/50")
    require(raw["prototype_scope"]["compact_overlap"] == "33/32", "COMPACT_ENDPOINT_MISMATCH", "coverage", None, "33/32")
    require(raw["prototype_scope"]["claim"] == "prototype bricks only; not contiguous bridge coverage", "SCOPE_OVERCLAIM", "coverage", None, "prototype claim")
    require(raw["prototype_scope"]["uncovered_lambda_intervals"] == [["102001/100000", "25781/25000"]], "UNCOVERED_SCOPE_MISMATCH", "coverage", None, "exact uncovered interval")
    require(isinstance(raw["bricks"], list) and len(raw["bricks"]) == 2, "BRICK_COUNT", "coverage", None, "two pilot bricks")
    require(isinstance(raw["payload_sha256"], str) and raw["payload_sha256"] == semantic_hash(raw), "PAYLOAD_HASH_MISMATCH", "integrity", None, "semantic hash")
    bricks = [parse_brick(item, j) for j, item in enumerate(raw["bricks"])]
    require((bricks[0].lam_lo, bricks[0].lam_hi) == (Q(51, 50), Q(102001, 100000)), "FIRST_BRICK_DOMAIN", "coverage", 0, "fixed pilot interval")
    require((bricks[1].lam_lo, bricks[1].lam_hi) == (Q(25781, 25000), Q(33, 32)), "SECOND_BRICK_DOMAIN", "coverage", 1, "fixed pilot interval")
    results = [check_brick(brick, j) for j, brick in enumerate(bricks)]
    return {
        "status": "PASS",
        "schema": SCHEMA,
        "prototype_lambda_intervals": [[qstr(b.lam_lo), qstr(b.lam_hi)] for b in bricks],
        "proposed_near_one_overlap": "51/50",
        "compact_overlap": "33/32",
        "uncovered_lambda_intervals": [["102001/100000", "25781/25000"]],
        "pi_interval": [qstr(PI.lo), qstr(PI.hi)],
        "strict_margins": results,
        "proof_method": "opposite faces plus scalar derivative signs; no interval Jacobian",
        "python": platform.python_version(),
        "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def failure_json(exc: CheckFailure) -> dict[str, Any]:
    result: dict[str, Any] = {"status": "FAIL", "failure": {"code": exc.code, "phase": exc.phase, "brick_index": exc.brick, "detail": exc.detail}}
    if exc.value is not None:
        result["failure"]["interval"] = [qstr(exc.value.lo), qstr(exc.value.hi)]
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", nargs="?", default=str(Path(__file__).with_name("bridge_certificate.json")))
    parser.add_argument("--output")
    args = parser.parse_args()
    try:
        result = check(Path(args.certificate))
        status = 0
    except CheckFailure as exc:
        result, status = failure_json(exc), 1
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text)
    print(text, end="")
    raise SystemExit(status)


if __name__ == "__main__":
    main()
