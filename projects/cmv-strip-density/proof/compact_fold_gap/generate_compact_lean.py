#!/usr/bin/env python3
"""Deterministically emit bounded shards of kernel-checkable compact boxes.

Only the lambda and root slabs are read from the JSON certificate.  Every
auxiliary enclosure is recomputed here with deterministic Decimal arithmetic;
the generated Lean proves all resulting rational inequalities with the sound
interval layer and ``norm_num``.  Box indices are zero-based and inclusive.
"""

from __future__ import annotations

import argparse
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
from typing import Any

SCHEMA = "cmv-compact-rational-certificate-v1"
DEFAULT_FIRST_BOX = 2
DEFAULT_LAST_BOX = 10
SCALE = 1_000_000
ROOT_KEYS = {"schema", "target", "precision", "boxes", "payload_sha256"}
BOX_KEYS = {"lambda", "h3_root", "h4_root"}

Q = Fraction
Interval = tuple[Q, Q]


def fail(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def parse_q(value: Any, label: str) -> Q:
    fail(isinstance(value, str), f"{label} must be a rational string")
    fail(re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", value) is not None,
         f"{label} is not a canonical rational string")
    result = Q(value)
    fail(qstr(result) == value, f"{label} is not reduced")
    return result


def qstr(value: Q) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def lean_q(value: Q) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator} / {value.denominator}"


def read_slabs(path: Path, last_box: int) -> list[dict[str, Interval]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    fail(isinstance(data, dict), "certificate root must be an object")
    fail(set(data) == ROOT_KEYS, "certificate root keys mismatch")
    fail(data["schema"] == SCHEMA, "certificate schema mismatch")

    target = data["target"]
    fail(isinstance(target, dict) and set(target) == {"lambda_lower", "lambda_upper"},
         "target schema mismatch")
    target_lo = parse_q(target["lambda_lower"], "target.lambda_lower")
    target_hi = parse_q(target["lambda_upper"], "target.lambda_upper")
    fail(target_lo < target_hi, "target interval is not ordered")

    precision = data["precision"]
    fail(isinstance(precision, dict) and set(precision) ==
         {"sqrt_bits", "atan_terms", "trig_terms"}, "precision schema mismatch")
    for key, value in precision.items():
        fail(type(value) is int and value > 0, f"precision.{key} must be a positive integer")

    boxes = data["boxes"]
    fail(isinstance(boxes, list), "boxes must be an array")
    fail(len(boxes) > last_box, f"certificate must contain box {last_box}")
    encoded = json.dumps(boxes, sort_keys=True, separators=(",", ":")).encode()
    fail(isinstance(data["payload_sha256"], str) and
         re.fullmatch(r"[0-9a-f]{64}", data["payload_sha256"]) is not None,
         "payload_sha256 schema mismatch")
    fail(hashlib.sha256(encoded).hexdigest() == data["payload_sha256"],
         "payload hash mismatch")

    result: list[dict[str, Interval]] = []
    previous = target_lo
    for index, raw in enumerate(boxes):
        fail(isinstance(raw, dict) and set(raw) == BOX_KEYS,
             f"boxes[{index}] schema mismatch")
        parsed: dict[str, Interval] = {}
        for key in ("lambda", "h3_root", "h4_root"):
            pair = raw[key]
            fail(isinstance(pair, list) and len(pair) == 2,
                 f"boxes[{index}].{key} must be a pair")
            lo = parse_q(pair[0], f"boxes[{index}].{key}[0]")
            hi = parse_q(pair[1], f"boxes[{index}].{key}[1]")
            fail(lo <= hi, f"boxes[{index}].{key} is not ordered")
            parsed[key] = (lo, hi)
        lam, h3, h4 = parsed["lambda"], parsed["h3_root"], parsed["h4_root"]
        fail(lam[0] == previous, f"boxes[{index}] does not meet the preceding lambda seam")
        fail(1 < lam[0] < lam[1], f"boxes[{index}].lambda is outside the regular range")
        fail(0 < h3[0] <= h3[1] < 1, f"boxes[{index}].h3_root is outside (0,1)")
        fail(0 < h4[0] <= h4[1] < 1, f"boxes[{index}].h4_root is outside (0,1)")
        previous = lam[1]
        result.append(parsed)
    fail(previous == target_hi, "boxes do not end at target.lambda_upper")
    return result


def decimal_q(value: Q) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def atan_small(x: Decimal) -> Decimal:
    fail(abs(x) < 1, "atan_small argument must have absolute value below one")
    x2 = x * x
    term = x
    total = term
    n = 1
    threshold = Decimal(1).scaleb(-90)
    while True:
        term *= -x2
        addend = term / Decimal(2 * n + 1)
        total += addend
        if abs(addend) < threshold:
            return total
        n += 1


def decimal_pi() -> Decimal:
    return Decimal(16) * atan_small(Decimal(1) / Decimal(5)) - \
        Decimal(4) * atan_small(Decimal(1) / Decimal(239))


def decimal_atan(x: Decimal, pi: Decimal) -> Decimal:
    if x < 0:
        return -decimal_atan(-x, pi)
    if x > 1:
        return pi / 2 - atan_small(1 / x)
    return atan_small(x)


def decimal_asin(x: Q, pi: Decimal) -> Decimal:
    xd = decimal_q(x)
    fail(0 <= x < 1, "asin enclosure input must lie in [0,1)")
    return decimal_atan(xd / (Decimal(1) - xd * xd).sqrt(), pi)


def outward_decimal(lo: Decimal, hi: Decimal) -> Interval:
    fail(lo <= hi, "decimal enclosure is not ordered")
    # One extra unit on each side makes the approximation independent of the
    # final discarded Decimal digits; Lean still verifies the exact bounds.
    a = int((lo * SCALE).to_integral_value(rounding=ROUND_FLOOR)) - 1
    b = int((hi * SCALE).to_integral_value(rounding=ROUND_CEILING)) + 1
    return Q(a, SCALE), Q(b, SCALE)


def atom_interval(lam: Interval, h: Interval, kind: int, pi: Decimal) -> dict[str, Interval]:
    qlo = 2 * h[0] - 1 if kind == 3 else h[0]
    qhi = 2 * h[1] - 1 if kind == 3 else h[1]
    fail(0 <= qlo <= qhi < 1, "shape interval is outside [0,1)")
    ulo = (Decimal(1) - decimal_q(qhi) ** 2).sqrt()
    uhi = (Decimal(1) - decimal_q(qlo) ** 2).sqrt()
    dlo = (decimal_q(lam[0]) ** 2 - decimal_q(qhi) ** 2).sqrt()
    dhi = (decimal_q(lam[1]) ** 2 - decimal_q(qlo) ** 2).sqrt()
    alo = decimal_asin(qlo, pi)
    ahi = decimal_asin(qhi, pi)
    rlo = decimal_asin(qlo / lam[1], pi)
    rhi = decimal_asin(qhi / lam[0], pi)
    return {
        "u": outward_decimal(ulo, uhi),
        "d": outward_decimal(dlo, dhi),
        "asin": outward_decimal(alo, ahi),
        "ratio": outward_decimal(rlo, rhi),
    }


def add(i: Interval, j: Interval) -> Interval:
    return i[0] + j[0], i[1] + j[1]


def neg(i: Interval) -> Interval:
    return -i[1], -i[0]


def sub(i: Interval, j: Interval) -> Interval:
    return add(i, neg(j))


def mul(i: Interval, j: Interval) -> Interval:
    corners = [i[0] * j[0], i[0] * j[1], i[1] * j[0], i[1] * j[1]]
    return min(corners), max(corners)


def scale(q: Q, i: Interval) -> Interval:
    fail(q >= 0, "interval scale must be nonnegative")
    return q * i[0], q * i[1]


def div_pos(i: Interval, j: Interval) -> Interval:
    fail(j[0] > 0, "positive interval division has a nonpositive denominator")
    return mul(i, (1 / j[1], 1 / j[0]))


PI_INTERVAL: Interval = (Q(3141592, 1000000), Q(3141593, 1000000))
HALF_PI = scale(Q(1, 2), PI_INTERVAL)
ONE: Interval = (Q(1), Q(1))
TWO: Interval = (Q(2), Q(2))


def type3_formula(lam: Interval, h: Interval, atoms: dict[str, Interval]) -> dict[str, Interval]:
    q = sub(scale(Q(2), h), ONE)
    angle = add(mul(lam, sub(HALF_PI, atoms["ratio"])), atoms["asin"])
    delta = sub(div_pos(atoms["d"], lam), atoms["u"])
    area = div_pos(add(add(angle, HALF_PI), mul(add(q, TWO), delta)), mul(h, h))
    perimeter = scale(Q(2), div_pos(add(add(angle, HALF_PI), delta), h))
    first = div_pos(add(ONE, q), atoms["u"])
    second = div_pos(add(mul(lam, lam), q), mul(lam, atoms["d"]))
    fold = sub(scale(Q(4), mul(h, sub(first, second))),
               scale(Q(2), add(add(angle, HALF_PI), delta)))
    return {"area": area, "perimeter": perimeter, "fold": fold}


def type4_formula(lam: Interval, h: Interval, atoms: dict[str, Interval]) -> dict[str, Interval]:
    angle = add(mul(lam, sub(HALF_PI, atoms["ratio"])), atoms["asin"])
    delta = sub(div_pos(atoms["d"], lam), atoms["u"])
    area = div_pos(scale(Q(2), add(angle, mul(h, delta))), mul(h, h))
    perimeter = div_pos(scale(Q(4), angle), h)
    fold = scale(Q(4), sub(mul(h, sub(div_pos(ONE, atoms["u"]),
                                      div_pos(lam, atoms["d"]))), angle))
    return {"area": area, "perimeter": perimeter, "fold": fold}


def enclosing_micro(i: Interval) -> Interval:
    with localcontext() as ctx:
        ctx.prec = 100
        return outward_decimal(decimal_q(i[0]), decimal_q(i[1]))


def interval_def(name: str, value: Interval, private: bool = True) -> str:
    prefix = "private " if private else ""
    head = f"{prefix}def {name} : QInterval := "
    body = f"⟨{lean_q(value[0])}, {lean_q(value[1])}, by norm_num⟩"
    if len(head + body) <= 100:
        return head + body
    return (head.rstrip() + "\n  " +
            f"⟨{lean_q(value[0])},\n    {lean_q(value[1])}, by norm_num⟩")


def rational_def(name: str, value: Q) -> str:
    return f"def {name} : ℚ := {lean_q(value)}"


def replace_definition(source: str, name: str, replacement: str) -> str:
    lines = source.splitlines()
    starts = [i for i, line in enumerate(lines)
              if re.match(rf"^(?:private )?def {re.escape(name)}\b", line)]
    fail(len(starts) == 1, f"template definition {name} occurs {len(starts)} times")
    start = starts[0]
    end = start + 1
    while (end < len(lines) and lines[end].strip() != "" and
           re.match(r"^(?:private )?def [A-Za-z0-9_]+\b", lines[end]) is None):
        end += 1
    lines[start:end] = replacement.splitlines()
    return "\n".join(lines)


def box_values(slab: dict[str, Interval], pi: Decimal) -> dict[str, Interval | Q]:
    lam, h3, h4 = slab["lambda"], slab["h3_root"], slab["h4_root"]
    c3, c4 = (h3[0] + h3[1]) / 2, (h4[0] + h4[1]) / 2
    result: dict[str, Interval | Q] = {
        "lambdaInterval": lam, "h3Interval": h3, "h4Interval": h4,
        "h3Center": c3, "h4Center": c4,
    }
    cases: dict[str, tuple[int, Interval]] = {
        "3Lower": (3, (h3[0], h3[0])),
        "3Upper": (3, (h3[1], h3[1])),
        "3Cell": (3, h3),
        "3Center": (3, (c3, c3)),
        "4Lower": (4, (h4[0], h4[0])),
        "4Upper": (4, (h4[1], h4[1])),
        "4Cell": (4, h4),
        "4Center": (4, (c4, c4)),
    }
    atoms_by_case: dict[str, dict[str, Interval]] = {}
    for suffix, (kind, hs) in cases.items():
        atoms = atom_interval(lam, hs, kind, pi)
        atoms_by_case[suffix] = atoms
        result[f"u{suffix}"] = atoms["u"]
        result[f"d{suffix}"] = atoms["d"]
        result[("asinQ" if kind == 3 else "asinH") + suffix] = atoms["asin"]
        result[f"asinR{suffix}"] = atoms["ratio"]

    f3lo = type3_formula(lam, (h3[0], h3[0]), atoms_by_case["3Lower"])
    f3hi = type3_formula(lam, (h3[1], h3[1]), atoms_by_case["3Upper"])
    f3cell = type3_formula(lam, h3, atoms_by_case["3Cell"])
    f4lo = type4_formula(lam, (h4[0], h4[0]), atoms_by_case["4Lower"])
    f4hi = type4_formula(lam, (h4[1], h4[1]), atoms_by_case["4Upper"])
    result["typeThreeLowerArea"] = enclosing_micro(f3lo["area"])
    result["typeThreeUpperArea"] = enclosing_micro(f3hi["area"])
    result["typeThreeFoldCell"] = enclosing_micro(f3cell["fold"])
    result["typeFourLowerFold"] = enclosing_micro(f4lo["fold"])
    result["typeFourUpperFold"] = enclosing_micro(f4hi["fold"])
    result["typeFourCenteredArea"] = enclosing_micro(
        type4_formula(lam, (c4, c4), atoms_by_case["4Center"])["area"])

    # Fail early on the three direct sign certificates.  The centered gap
    # inequalities are intentionally left to generated Lean's exact replay.
    fail(f4lo["fold"][1] < 0, "type-(iv) lower-face fold enclosure is not negative")
    fail(0 < f4hi["fold"][0], "type-(iv) upper-face fold enclosure is not positive")
    fail(f3cell["fold"][1] < 0, "type-(iii) slab fold enclosure is not negative")
    return result


def render_box(template: str, index: int, values: dict[str, Interval | Q]) -> str:
    source = template.replace("box 1", f"box {index}")
    interval_names = [
        "lambdaInterval", "h4Interval", "h3Interval",
        "u3Lower", "d3Lower", "asinQ3Lower", "asinR3Lower",
        "u3Upper", "d3Upper", "asinQ3Upper", "asinR3Upper",
        "u3Cell", "d3Cell", "asinQ3Cell", "asinR3Cell",
        "u3Center", "d3Center", "asinQ3Center", "asinR3Center",
        "u4Lower", "d4Lower", "asinH4Lower", "asinR4Lower",
        "u4Upper", "d4Upper", "asinH4Upper", "asinR4Upper",
        "u4Cell", "d4Cell", "asinH4Cell", "asinR4Cell",
        "u4Center", "d4Center", "asinH4Center", "asinR4Center",
        "typeFourLowerFold", "typeFourUpperFold", "typeThreeFoldCell",
        "typeThreeLowerArea", "typeThreeUpperArea", "typeFourCenteredArea",
    ]
    for name in interval_names:
        value = values[name]
        assert isinstance(value, tuple)
        source = replace_definition(source, name, interval_def(
            name, value, private=name not in {"lambdaInterval", "h3Interval", "h4Interval"}))
    for name in ("h4Center", "h3Center"):
        value = values[name]
        assert isinstance(value, Q)
        source = replace_definition(source, name, rational_def(name, value))
    source = source.replace("namespace CompactSecondCell", f"namespace Box{index}")
    fail("end CompactSecondCell" not in source, "template unexpectedly closes its namespace")
    return source.strip() + f"\n\nend Box{index}\n"


def dispatch_theorem(boxes: list[dict[str, Interval]],
                     first_box: int, last_box: int) -> str:
    lower = boxes[first_box]["lambda"][0]
    upper = boxes[last_box]["lambda"][1]
    lines = [
        "/-- Candidate-facing exclusion on the closed union of zero-based boxes",
        f"{first_box} through {last_box} across every exact seam. -/",
        f"theorem boxes{first_box}To{last_box}_candidate_not_isWeightedPerimeterMinimizer",
        "    {lam : ℝ}",
        f"    (hlower : ({lean_q(lower)} : ℝ) ≤ lam)",
        f"    (hupper : lam ≤ ({lean_q(upper)} : ℝ))",
        "    (candidate : _root_.FourArcCandidate lam)",
        "    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :",
        "    ¬ candidate.IsWeightedPerimeterMinimizer := by",
    ]
    previous_hyp = "hlower"
    for index in range(first_box, last_box + 1):
        box_upper = boxes[index]["lambda"][1]
        if index < last_box:
            current_hyp = f"h{index}"
            lines.append(
                f"  by_cases {current_hyp} : "
                f"lam ≤ ({lean_q(box_upper)} : ℝ)")
            upper_hyp = current_hyp
            statement_indent = "  · "
            proof_indent = "      "
            result_indent = "    "
        else:
            upper_hyp = "hupper"
            statement_indent = "  "
            proof_indent = "    "
            result_indent = "  "
        lower_proof = previous_hyp if index == first_box else f"{previous_hyp}.le"
        lines += [
            f"{statement_indent}have hbox : "
            f"Box{index}.lambdaInterval.RealContains lam := by",
            f"{proof_indent}norm_num [Box{index}.lambdaInterval,",
            f"{proof_indent}  LeanSuffixReflective.QInterval.RealContains] "
            f"at {previous_hyp} {upper_hyp} ⊢",
            f"{proof_indent}exact ⟨{lower_proof}, {upper_hyp}⟩",
            f"{result_indent}exact "
            f"Box{index}.compactCandidate_not_isWeightedPerimeterMinimizer",
            f"{result_indent}  hbox candidate hcandidate",
        ]
        previous_hyp = f"h{index}"
    return "\n".join(lines) + "\n"


def base_union_theorem(boxes: list[dict[str, Interval]],
                       first_box: int, last_box: int) -> str:
    fail(first_box == 2, "the specialized base union must start at box 2")
    upper = boxes[last_box]["lambda"][1]
    lines = [
        "/-- Candidate-facing exclusion on the closed union of zero-based boxes",
        f"0 through {last_box} across every exact seam. -/",
        f"theorem boxes0To{last_box}_candidate_not_isWeightedPerimeterMinimizer",
        "    {lam : ℝ}",
        f"    (hlower : (33 / 32 : ℝ) ≤ lam) (hupper : lam ≤ ({lean_q(upper)} : ℝ))",
        "    (candidate : _root_.FourArcCandidate lam)",
        "    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :",
        "    ¬ candidate.IsWeightedPerimeterMinimizer := by",
    ]
    first_upper = boxes[1]["lambda"][1]
    lines += [
        f"  by_cases h1 : lam ≤ ({lean_q(first_upper)} : ℝ)",
        "  · exact CompactSecondCell.firstTwoBoxes_candidate_not_isWeightedPerimeterMinimizer",
        "      hlower h1 candidate hcandidate",
    ]
    previous_hyp = "h1"
    for index in range(first_box, last_box + 1):
        box_upper = boxes[index]["lambda"][1]
        branch_indent = "  " * (index - 1)
        if index < last_box:
            current_hyp = f"h{index}"
            lines.append(
                f"{branch_indent}· by_cases {current_hyp} : "
                f"lam ≤ ({lean_q(box_upper)} : ℝ)")
            proof_indent = "  " * index
            upper_hyp = current_hyp
        else:
            proof_indent = branch_indent
            upper_hyp = "hupper"
        lines += [
            f"{proof_indent}· have hbox : Box{index}.lambdaInterval.RealContains lam := by",
            f"{proof_indent}    norm_num [Box{index}.lambdaInterval,",
            f"{proof_indent}      LeanSuffixReflective.QInterval.RealContains] "
            f"at {previous_hyp} {upper_hyp} ⊢",
            f"{proof_indent}    exact ⟨{previous_hyp}.le, {upper_hyp}⟩",
            f"{proof_indent}  exact "
            f"Box{index}.compactCandidate_not_isWeightedPerimeterMinimizer",
            f"{proof_indent}    hbox candidate hcandidate",
        ]
        previous_hyp = f"h{index}"
    return "\n".join(lines) + "\n"


def shard_union_theorems(boxes: list[dict[str, Interval]],
                         first_box: int, last_box: int,
                         prefix_module: str) -> str:
    prefix_last = first_box - 1
    lower = boxes[first_box]["lambda"][0]
    upper = boxes[last_box]["lambda"][1]
    local = dispatch_theorem(boxes, first_box, last_box)
    aggregate = f"""
/-- Composition of the preceding aggregate with this bounded shard. -/
theorem boxes0To{last_box}_candidate_not_isWeightedPerimeterMinimizer
    {{lam : ℝ}}
    (hlower : (33 / 32 : ℝ) ≤ lam)
    (hupper : lam ≤ ({lean_q(upper)} : ℝ))
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  by_cases hprefix : lam ≤ ({lean_q(lower)} : ℝ)
  · exact {prefix_module}.boxes0To{prefix_last}_candidate_not_isWeightedPerimeterMinimizer
      hlower hprefix candidate hcandidate
  · exact boxes{first_box}To{last_box}_candidate_not_isWeightedPerimeterMinimizer
      (not_le.mp hprefix).le hupper candidate hcandidate
"""
    return local + aggregate.lstrip()


def load_template(path: Path) -> str:
    source = path.read_text(encoding="utf-8")
    start_marker = "namespace CompactSecondCell\n"
    end_marker = "/-- Candidate-facing exclusion on the closed union of zero-based boxes 0 and 1"
    fail(source.count(start_marker) == 1 and source.count(end_marker) == 1,
         "CompactSecondCell template markers changed")
    start = source.index(start_marker)
    end = source.index(end_marker)
    fragment = source[start:end].rstrip()
    fail("theorem checkedConditions" in fragment and
         "theorem compactCandidate_not_isWeightedPerimeterMinimizer" in fragment,
         "CompactSecondCell template is missing public conclusions")
    return fragment


def render(input_path: Path, template_path: Path,
           first_box: int, last_box: int,
           prefix_module: str | None) -> str:
    fail(2 <= first_box <= last_box,
         "generated range must satisfy 2 <= first <= last")
    if first_box == 2:
        fail(prefix_module is None,
             "the base shard must not name a predecessor module")
    else:
        fail(prefix_module is not None,
             "a shard after box 2 requires --prefix-module")
    boxes = read_slabs(input_path, last_box)
    template = load_template(template_path)
    with localcontext() as ctx:
        ctx.prec = 110
        pi = decimal_pi()
        rendered = [render_box(template, index, box_values(boxes[index], pi))
                    for index in range(first_box, last_box + 1)]
    namespace = f"CompactCells{first_box}To{last_box}"
    dependency = "CompactSecondCell" if prefix_module is None else prefix_module
    header = f"""/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import {dependency}

/-!
# Generated compact fold-gap cells {first_box} through {last_box}

This file is generated by `compact_fold_gap/generate_compact_lean.py`.
Its numerical leaves are exact rationals replayed by the kernel.
-/

open Real Set
noncomputable section

namespace {namespace}

"""
    if prefix_module is None:
        unions = base_union_theorem(boxes, first_box, last_box)
    else:
        unions = shard_union_theorems(
            boxes, first_box, last_box, prefix_module)
    output = header + "\n".join(rendered) + "\n" + unions + \
        f"\nend {namespace}\n"
    for forbidden in ("sorry", "admit", "axiom", "native_decide"):
        fail(re.search(rf"\b{forbidden}\b", output) is None,
             f"generated output contains forbidden token {forbidden}")
    return output


def main() -> int:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=here / "compact_certificate.json")
    parser.add_argument("--template", type=Path, default=here.parent / "CompactSecondCell.lean")
    parser.add_argument("--first", type=int, default=DEFAULT_FIRST_BOX)
    parser.add_argument("--last", type=int, default=DEFAULT_LAST_BOX)
    parser.add_argument("--prefix-module")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    fail(args.prefix_module is None or
         re.fullmatch(r"[A-Z][A-Za-z0-9_.]*", args.prefix_module) is not None,
         "--prefix-module must be a Lean module/namespace name")
    output_path = args.output
    if output_path is None:
        output_path = here.parent / f"CompactCells{args.first}To{args.last}.lean"
    output = render(args.input.resolve(), args.template.resolve(),
                    args.first, args.last, args.prefix_module)
    output_path.resolve().write_text(output, encoding="utf-8")
    print(f"wrote {output_path} ({len(output.encode())} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
