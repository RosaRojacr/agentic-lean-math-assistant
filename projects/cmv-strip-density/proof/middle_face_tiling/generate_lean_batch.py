#!/usr/bin/env python3
"""Generate a checked batch of middle-face Lean cells and a balanced aggregate.

The manifest and every selected shard are untrusted inputs.  This driver verifies
the manifest's semantic hash, the byte hash and semantic hash of every listed
shard, exact brick ordering and adjacency, and the selected closed range before
calling ``generate_lean_cell.render``.  Lean still replays every emitted numeric
certificate; this script only removes repetitive emission and aggregation work.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
from typing import Any

from generate_lean_cell import (
    Brick,
    BRICK_KEYS,
    MODEL,
    ROOT_KEYS,
    SCHEMA,
    fail,
    lean_q,
    parse_q,
    read_brick,
    render,
    semantic_hash,
)

MANIFEST_SCHEMA = "cmv-middle-face-tiling-manifest-v1"
MANIFEST_KEYS = {
    "adjacency",
    "arithmetic",
    "brick_count",
    "bricks",
    "left_prototype_overlap",
    "model",
    "payload_sha256",
    "right_prototype_overlap",
    "schema",
    "target_lambda",
}
ENTRY_KEYS = {"brick_id", "certificate_sha256", "path"}
HEX_HASH = re.compile(r"[0-9a-f]{64}")
MODULE_NAME = re.compile(r"[A-Z][A-Za-z0-9_]*")


def read_manifest(path: Path) -> list[Path]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    fail(isinstance(raw, dict) and set(raw) == MANIFEST_KEYS,
         "manifest root keys mismatch")
    fail(raw["schema"] == MANIFEST_SCHEMA, "manifest schema mismatch")
    fail(raw["model"] == MODEL, "manifest model mismatch")
    fail(raw["adjacency"] == "exact-equality", "manifest adjacency mismatch")
    fail(isinstance(raw["payload_sha256"], str) and
         HEX_HASH.fullmatch(raw["payload_sha256"]) is not None,
         "manifest payload_sha256 must be lowercase hexadecimal")
    fail(semantic_hash(raw) == raw["payload_sha256"],
         "manifest payload hash mismatch")

    entries = raw["bricks"]
    fail(isinstance(entries, list) and entries,
         "manifest bricks must be a nonempty list")
    fail(isinstance(raw["brick_count"], int) and
         raw["brick_count"] == len(entries),
         "manifest brick_count mismatch")
    target = raw["target_lambda"]
    fail(isinstance(target, list) and len(target) == 2,
         "manifest target_lambda must contain two rationals")
    target_lo = parse_q(target[0], "manifest.target_lambda[0]")
    target_hi = parse_q(target[1], "manifest.target_lambda[1]")
    fail(parse_q(raw["left_prototype_overlap"],
                 "manifest.left_prototype_overlap") == target_lo,
         "left prototype overlap does not match target endpoint")
    fail(parse_q(raw["right_prototype_overlap"],
                 "manifest.right_prototype_overlap") == target_hi,
         "right prototype overlap does not match target endpoint")

    root = path.parent.resolve()
    result: list[Path] = []
    prior_hi = None
    for index, entry in enumerate(entries):
        fail(isinstance(entry, dict) and set(entry) == ENTRY_KEYS,
             f"manifest brick entry {index} keys mismatch")
        expected_id = f"B{index:04d}"
        fail(entry["brick_id"] == expected_id,
             f"manifest brick {index} must be {expected_id}")
        fail(isinstance(entry["path"], str),
             f"manifest brick {expected_id} path must be a string")
        shard_path = (root / entry["path"]).resolve()
        fail(shard_path.is_relative_to(root),
             f"manifest brick {expected_id} escapes the manifest directory")
        fail(shard_path.is_file(),
             f"manifest brick {expected_id} shard does not exist")
        expected_hash = entry["certificate_sha256"]
        fail(isinstance(expected_hash, str) and
             HEX_HASH.fullmatch(expected_hash) is not None,
             f"manifest brick {expected_id} hash must be lowercase hexadecimal")
        actual_hash = hashlib.sha256(shard_path.read_bytes()).hexdigest()
        fail(actual_hash == expected_hash,
             f"manifest brick {expected_id} byte hash mismatch")
        fail(shard_path.stem == expected_id,
             f"manifest brick {expected_id} path stem mismatch")

        shard_raw: Any = json.loads(shard_path.read_text(encoding="utf-8"))
        fail(isinstance(shard_raw, dict) and set(shard_raw) == ROOT_KEYS,
             f"manifest brick {expected_id} shard root keys mismatch")
        fail(shard_raw["brick_id"] == expected_id,
             f"manifest brick {expected_id} shard id mismatch")
        fail(shard_raw["schema"] == SCHEMA,
             f"manifest brick {expected_id} shard schema mismatch")
        fail(shard_raw["model"] == MODEL,
             f"manifest brick {expected_id} shard model mismatch")
        fail(isinstance(shard_raw["payload_sha256"], str) and
             HEX_HASH.fullmatch(shard_raw["payload_sha256"]) is not None,
             f"manifest brick {expected_id} shard payload hash malformed")
        fail(semantic_hash(shard_raw) == shard_raw["payload_sha256"],
             f"manifest brick {expected_id} shard payload hash mismatch")
        body = shard_raw["brick"]
        fail(isinstance(body, dict) and set(body) == BRICK_KEYS,
             f"manifest brick {expected_id} data keys mismatch")
        lam_raw = body["lambda"]
        fail(isinstance(lam_raw, list) and len(lam_raw) == 2,
             f"manifest brick {expected_id} lambda interval malformed")
        lo = parse_q(lam_raw[0], f"{expected_id}.lambda[0]")
        hi = parse_q(lam_raw[1], f"{expected_id}.lambda[1]")
        fail(lo < hi, f"manifest brick {expected_id} lambda interval is empty")
        if prior_hi is None:
            fail(lo == target_lo, "first brick does not start at target endpoint")
        else:
            fail(lo == prior_hi,
                 f"manifest seam before brick {expected_id} is not exact")
        prior_hi = hi

        # The terminal narrow shard is intentionally not renderable yet.  Keep
        # it in the manifest audit while deferring template-specific checks to
        # the selected range below.
        result.append(shard_path)

    fail(prior_hi == target_hi, "last brick does not end at target endpoint")
    return result


def indent(lines: list[str], spaces: int) -> list[str]:
    prefix = " " * spaces
    return [prefix + line if line else line for line in lines]


def leaf_proof(brick: Brick, lower_name: str, upper_name: str) -> list[str]:
    cell = brick.cell_number
    namespace = f"MiddleFaceCell{cell}"
    return [
        f"have hcell : {namespace}.lamInterval.RealContains lam := by",
        f"  norm_num [{namespace}.lamInterval, {namespace}.brick,",
        "    LeanSuffixReflective.QInterval.RealContains]",
        f"      at {lower_name} {upper_name} ⊢",
        f"  exact ⟨{lower_name}, {upper_name}⟩",
        "exact",
        f"  {namespace}.candidate_not_isWeightedPerimeterMinimizer",
        "    hcell candidate hcandidate",
    ]


def balanced_proof(bricks: list[Brick], lower_name: str,
                   upper_name: str) -> list[str]:
    if len(bricks) == 1:
        return leaf_proof(bricks[0], lower_name, upper_name)
    left_size = len(bricks) // 2
    left = bricks[:left_size]
    right = bricks[left_size:]
    split_cell = right[0].cell_number
    split_name = f"hsplit{split_cell}"
    right_lower = f"hlower{split_cell}"
    boundary = lean_q(left[-1].lam[1])
    lines = [f"by_cases {split_name} : lam ≤ ({boundary} : ℝ)"]
    left_lines = balanced_proof(left, lower_name, split_name)
    lines.extend(["· " + left_lines[0]])
    lines.extend(indent(left_lines[1:], 2))
    lines.append(f"· have {right_lower} : ({boundary} : ℝ) ≤ lam :=")
    lines.append(f"    (not_le.mp {split_name}).le")
    right_lines = balanced_proof(right, right_lower, upper_name)
    lines.extend(indent(right_lines, 2))
    return lines


def aggregate_source(bricks: list[Brick], namespace: str,
                     manifest_hash: str) -> str:
    first = bricks[0]
    last = bricks[-1]
    first_id = first.brick_id
    last_id = last.brick_id
    imports = "\n".join(
        f"import MiddleFaceCell{brick.cell_number}" for brick in bricks)
    proof = "\n".join(indent(balanced_proof(bricks, "hlower", "hupper"), 2))
    return f"""/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
{imports}

/-!
# Middle-face cells {first_id} through {last_id}

Balanced branch-complete candidate exclusion over the closed union of exact
inventory bricks `{first_id}` through `{last_id}`.  Generated by
`middle_face_tiling/generate_lean_batch.py` from manifest payload hash
`{manifest_hash}`.
-/

noncomputable section

namespace {namespace}

/-- Every modeled type-(iv) candidate in this closed batch fails
weighted-perimeter minimality. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    {{lam : ℝ}}
    (hlower : ({lean_q(first.lam[0])} : ℝ) ≤ lam)
    (hupper : lam ≤ ({lean_q(last.lam[1])} : ℝ))
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
{proof}

end {namespace}
"""


def main() -> int:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=here / "manifest.json")
    parser.add_argument("--first", type=int, required=True,
                        help="first zero-based brick number, inclusive")
    parser.add_argument("--last", type=int, required=True,
                        help="last zero-based brick number, inclusive")
    parser.add_argument("--template", type=Path,
                        default=here.parent / "MiddleFaceCell19.lean")
    parser.add_argument("--template-input", type=Path,
                        default=here / "bricks" / "B0019.json")
    parser.add_argument("--output-dir", type=Path, default=here.parent)
    parser.add_argument("--aggregate-output", type=Path)
    parser.add_argument("--namespace")
    parser.add_argument("--aggregate-only", action="store_true",
                        help="emit only the aggregate over existing cell modules")
    args = parser.parse_args()

    fail(0 <= args.first <= args.last, "invalid selected brick range")
    manifest_path = args.manifest.resolve()
    manifest_raw = json.loads(manifest_path.read_text(encoding="utf-8"))
    entries = read_manifest(manifest_path)
    fail(args.last < len(entries), "selected brick range exceeds the manifest")

    selected: list[tuple[Path, Brick]] = []
    for index in range(args.first, args.last + 1):
        shard_path = entries[index]
        selected.append((shard_path, read_brick(shard_path)))
    for left, right in zip(selected, selected[1:]):
        fail(left[1].lam[1] == right[1].lam[0],
             f"selected seam before {right[1].brick_id} is not exact")

    default_namespace = f"MiddleFaceCells{args.first}To{args.last}"
    namespace = args.namespace or default_namespace
    fail(MODULE_NAME.fullmatch(namespace) is not None,
         "namespace must be a Lean module identifier")
    aggregate_path = (args.aggregate_output or
                      (args.output_dir / f"{namespace}.lean")).resolve()
    fail(aggregate_path.stem == namespace,
         "aggregate output filename must match its namespace")
    fail(aggregate_path.parent.is_dir(),
         "aggregate output directory does not exist")

    rendered: list[tuple[Path, str]] = []
    if not args.aggregate_only:
        fail(args.output_dir.resolve().is_dir(), "cell output directory does not exist")
        template_path = args.template.resolve()
        template_input_path = args.template_input.resolve()
        for shard_path, brick in selected:
            output_path = (args.output_dir.resolve() /
                           f"MiddleFaceCell{brick.cell_number}.lean")
            rendered.append((output_path, render(
                shard_path, template_path, template_input_path)))

    aggregate = aggregate_source(
        [brick for _, brick in selected], namespace,
        manifest_raw["payload_sha256"])
    for forbidden in ("sorry", "admit", "axiom", "native_decide"):
        fail(re.search(rf"\b{forbidden}\b", aggregate) is None,
             f"generated aggregate contains forbidden token {forbidden}")

    for output_path, source in rendered:
        output_path.write_text(source, encoding="utf-8")
        digest = hashlib.sha256(source.encode()).hexdigest()
        print(f"wrote {output_path} ({len(source.encode())} bytes, sha256 {digest})")
    aggregate_path.write_text(aggregate, encoding="utf-8")
    digest = hashlib.sha256(aggregate.encode()).hexdigest()
    print(f"wrote {aggregate_path} ({len(aggregate.encode())} bytes, sha256 {digest})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
