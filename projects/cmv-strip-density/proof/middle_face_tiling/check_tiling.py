#!/usr/bin/env python3
"""Fail-closed exact-rational checker for the middle face-brick tiling."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import platform
import sys
from fractions import Fraction as Q
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
PROOF_ROOT = ROOT.parent
KERNEL_PATH = PROOF_ROOT / "face_bridge_pilot" / "check_bridge.py"
PILOT_CERT = PROOF_ROOT / "face_bridge_pilot" / "bridge_certificate.json"
spec = importlib.util.spec_from_file_location("face_bridge_kernel", KERNEL_PATH)
if spec is None or spec.loader is None:
    raise RuntimeError("cannot load canonical face bridge kernel")
k = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = k
spec.loader.exec_module(k)

SCHEMA = "cmv-middle-face-tiling-manifest-v1"
BRICK_SCHEMA = "cmv-middle-face-brick-v1"
MODEL = "cmv-angle-fold-equal-area-v1"
TARGET_LO = Q(102001, 100000)
TARGET_HI = Q(25781, 25000)
ARITHMETIC = {"atan_terms": 36, "trig_terms": 14, "pi_formula": "16*atan(1/5)-4*atan(1/239)", "decision_type": "fractions.Fraction mean-value intervals"}
KERNEL_SHA256 = "c4731e14afee8ed097e8f24b27412464050633b1c9a4c56e0624954441d0b0fd"


def fail(code: str, phase: str, brick: int | None, detail: str, value: k.I | None = None) -> None:
    raise k.CheckFailure(code, phase, brick, detail, value)


def require(ok: bool, code: str, phase: str, brick: int | None, detail: str, value: k.I | None = None) -> None:
    if not ok:
        fail(code, phase, brick, detail, value)


def exact_keys(value: Any, keys: set[str], code: str, phase: str, brick: int | None = None) -> None:
    require(isinstance(value, dict), code, phase, brick, "object required")
    require(set(value) == keys, code, phase, brick, f"expected {sorted(keys)}, got {sorted(value)}")


def semantic_hash(raw: dict[str, Any]) -> str:
    payload = {key: value for key, value in raw.items() if key != "payload_sha256"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def byte_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path) -> dict[str, Any]:
    return k.load_json(path)


def endpoint_box(brick: k.Brick, side: int) -> tuple[k.I, k.I, k.I, k.I]:
    t = Q(side) * brick.t_radius
    xi = k.I(-brick.radii[0], brick.radii[0])
    eta = k.I(-brick.radii[1], brick.radii[1])
    rho = k.I(-brick.radii[2], brick.radii[2])
    sigma = k.I(-brick.radii[3], brick.radii[3])
    x = brick.centers[0] + brick.slopes[0] * t + xi
    y = brick.centers[1] + brick.slopes[1] * t + brick.y_xi_slope * xi + eta
    w = brick.centers[2] + brick.slopes[2] * t + rho
    v = brick.centers[3] + brick.slopes[3] * t + brick.v_rho_slope * rho + sigma
    return x, y, w, v


def hull(a: k.I, b: k.I) -> k.I:
    return k.I(min(a.lo, b.lo), max(a.hi, b.hi))


def overlap(a: k.I, b: k.I) -> bool:
    return max(a.lo, b.lo) <= min(a.hi, b.hi)


def seam_check(left: k.Brick, right: k.Brick, lam: Q, seam_index: int, label: str) -> dict[str, str]:
    left_box, right_box = endpoint_box(left, +1), endpoint_box(right, -1)
    names = ("x", "y", "w", "v")
    for name, a, b in zip(names, left_box, right_box):
        require(overlap(a, b), "SEAM_ANGLE_BOX_DISJOINT", "seams", seam_index, f"{label}:{name}; left={a}, right={b}")
    boxes = tuple(hull(a, b) for a, b in zip(left_box, right_box))
    centers = tuple((box.lo + box.hi) / 2 for box in boxes)
    radii = tuple((box.hi - box.lo) / 2 for box in boxes)
    synthetic = k.Brick(lam, lam, centers, (Q(0),) * 4, Q(0), Q(0), radii)
    bounds, _ = k.base_bounds(synthetic)
    try:
        values = k.model(synthetic, bounds)
    except k.CheckFailure as exc:
        raise k.CheckFailure(exc.code, exc.phase, seam_index, f"{label}: {exc.detail}", exc.value) from exc
    require(values["y"].v.lo > values["x"].v.hi, "SEAM_TYPE4_ORDER", "seams", seam_index, label)
    require(values["v"].v.lo > values["w"].v.hi, "SEAM_TYPE3_ORDER", "seams", seam_index, label)
    k3 = values["K3"].v
    require(k3.hi < 0, "SEAM_K3_NOT_NEGATIVE", "seams", seam_index, label, k3)
    return {"label": label, "lambda": str(lam), "k3_margin": str(-k3.hi)}


def positive_guards(brick: k.Brick, index: int) -> dict[str, str]:
    bounds, _ = k.base_bounds(brick)
    try:
        values = k.model(brick, bounds)
        factors = {
            "lambda": values["lambda"].v,
            "sin_x": k.sin_i(values["x"].v),
            "sin_y": k.sin_i(values["y"].v),
            "cos_x": k.cos_i(values["x"].v),
            "cos_y": k.cos_i(values["y"].v),
            "sin_w": k.sin_i(values["w"].v),
            "sin_v": k.sin_i(values["v"].v),
            "cos_w": k.cos_i(values["w"].v),
            "one_plus_cos_w": 1 + k.cos_i(values["w"].v),
        }
    except k.CheckFailure as exc:
        raise k.CheckFailure(exc.code, exc.phase, index, exc.detail, exc.value) from exc
    margins: dict[str, str] = {}
    for name, value in factors.items():
        require(value.lo > 0, "POSITIVE_FACTOR_GUARD", "denominators", index, name, value)
        margins[f"positive_{name}"] = str(value.lo)
    droot3 = factors["lambda"] * factors["sin_v"]
    require(droot3.lo > 0, "DROOT3_DENOMINATOR_GUARD", "denominators", index, "lambda*sin(v)", droot3)
    margins["positive_droot3"] = str(droot3.lo)
    return margins


def load_shard(path: Path, entry: dict[str, Any], index: int) -> tuple[k.Brick, str]:
    expected_id = f"B{index:04d}"
    exact_keys(entry, {"brick_id", "path", "certificate_sha256"}, "MANIFEST_BRICK_FIELDS", "schema", index)
    require(entry["brick_id"] == expected_id, "BRICK_ID_SEQUENCE", "ordering", index, expected_id)
    expected_relative = f"bricks/{expected_id}.json"
    require(entry["path"] == expected_relative, "BRICK_PATH_MISMATCH", "integrity", index, expected_relative)
    require(isinstance(entry["certificate_sha256"], str) and len(entry["certificate_sha256"]) == 64, "BAD_CERTIFICATE_HASH", "integrity", index, expected_id)
    shard_path = path.parent / expected_relative
    require(shard_path.is_file() and not shard_path.is_symlink(), "MISSING_OR_SYMLINK_SHARD", "integrity", index, expected_relative)
    require(shard_path.resolve().parent == (path.parent / "bricks").resolve(), "SHARD_PATH_ESCAPE", "integrity", index, expected_relative)
    actual_hash = byte_hash(shard_path)
    require(actual_hash == entry["certificate_sha256"], "CERTIFICATE_HASH_MISMATCH", "integrity", index, expected_id)
    raw = load(shard_path)
    exact_keys(raw, {"schema", "model", "brick_id", "brick", "payload_sha256"}, "SHARD_FIELDS", "schema", index)
    require(raw["schema"] == BRICK_SCHEMA, "BRICK_SCHEMA_MISMATCH", "schema", index, str(raw["schema"]))
    require(raw["model"] == MODEL, "MODEL_MISMATCH", "schema", index, str(raw["model"]))
    require(raw["brick_id"] == expected_id, "SHARD_ID_MISMATCH", "schema", index, expected_id)
    require(isinstance(raw["payload_sha256"], str) and raw["payload_sha256"] == semantic_hash(raw), "SHARD_PAYLOAD_HASH_MISMATCH", "integrity", index, expected_id)
    return k.parse_brick(raw["brick"], index), actual_hash


def check_mathematics(brick: k.Brick, index: int) -> dict[str, str]:
    try:
        margins = k.check_brick(brick, index)
        margins.update(positive_guards(brick, index))
        return margins
    except k.CheckFailure as exc:
        if exc.brick is None:
            raise k.CheckFailure(exc.code, exc.phase, index, exc.detail, exc.value) from exc
        raise


def compact_margin_summary(results: list[dict[str, str]]) -> dict[str, dict[str, str | int]]:
    keys = sorted(results[0])
    require(all(set(result) == set(keys) for result in results), "MARGIN_SCHEMA_DRIFT", "aggregation", None, "per-brick margins")
    summary: dict[str, dict[str, str | int]] = {}
    for key in keys:
        values = [Q(result[key]) for result in results]
        minimum = min(values)
        summary[key] = {"minimum": str(minimum), "brick_index": values.index(minimum)}
    return summary


def write_receipt(index: int, brick: k.Brick, margins: dict[str, str], shard_hash: str) -> str:
    receipt = {
        "status": "PASS",
        "schema": "cmv-middle-face-brick-check-receipt-v1",
        "brick_id": f"B{index:04d}",
        "lambda": [str(brick.lam_lo), str(brick.lam_hi)],
        "strict_margins": margins,
        "certificate_sha256": shard_hash,
        "checker_sha256": byte_hash(Path(__file__)),
        "kernel_sha256": byte_hash(KERNEL_PATH),
    }
    receipt_path = ROOT / "receipts" / f"B{index:04d}.json"
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    return byte_hash(receipt_path)


def check(path: Path, retain_receipts: bool = False) -> dict[str, Any]:
    raw = load(path)
    exact_keys(raw, {"schema", "model", "arithmetic", "target_lambda", "left_prototype_overlap", "right_prototype_overlap", "adjacency", "brick_count", "bricks", "payload_sha256"}, "TOP_LEVEL_FIELDS", "schema")
    require(raw["schema"] == SCHEMA, "SCHEMA_MISMATCH", "schema", None, str(raw["schema"]))
    require(raw["model"] == MODEL, "MODEL_MISMATCH", "schema", None, str(raw["model"]))
    require(raw["arithmetic"] == ARITHMETIC, "ARITHMETIC_MISMATCH", "schema", None, "pinned arithmetic")
    require(raw["target_lambda"] == [str(TARGET_LO), str(TARGET_HI)], "TARGET_ENDPOINT_MISMATCH", "coverage", None, "pinned middle interval")
    require(raw["left_prototype_overlap"] == str(TARGET_LO), "LEFT_PROTOTYPE_ENDPOINT_MISMATCH", "coverage", None, str(TARGET_LO))
    require(raw["right_prototype_overlap"] == str(TARGET_HI), "RIGHT_PROTOTYPE_ENDPOINT_MISMATCH", "coverage", None, str(TARGET_HI))
    require(raw["adjacency"] == "exact-equality", "ADJACENCY_MODE_MISMATCH", "coverage", None, "exact-equality")
    require(isinstance(raw["brick_count"], int) and not isinstance(raw["brick_count"], bool) and raw["brick_count"] > 0, "BAD_BRICK_COUNT", "schema", None, "positive integer")
    require(isinstance(raw["bricks"], list) and len(raw["bricks"]) == raw["brick_count"], "BRICK_COUNT_MISMATCH", "coverage", None, "manifest count")
    require(isinstance(raw["payload_sha256"], str) and raw["payload_sha256"] == semantic_hash(raw), "PAYLOAD_HASH_MISMATCH", "integrity", None, "manifest semantic hash")
    require(byte_hash(KERNEL_PATH) == KERNEL_SHA256, "KERNEL_HASH_MISMATCH", "dependencies", None, "canonical exact arithmetic/model kernel")

    pilot_raw = load(PILOT_CERT)
    require(byte_hash(PILOT_CERT) == "30593dc3d0b8ba283f709f0585f8f461839793a8f9013a32600cec2c9e0e0147", "PILOT_CERTIFICATE_HASH_MISMATCH", "dependencies", None, "canonical retained pilot")
    pilot_bricks = [k.parse_brick(item, j) for j, item in enumerate(pilot_raw["bricks"])]
    require(pilot_bricks[0].lam_hi == TARGET_LO, "LEFT_PROTOTYPE_ENDPOINT_MISMATCH", "coverage", None, str(pilot_bricks[0].lam_hi))
    require(pilot_bricks[1].lam_lo == TARGET_HI, "RIGHT_PROTOTYPE_ENDPOINT_MISMATCH", "coverage", None, str(pilot_bricks[1].lam_lo))

    bricks: list[k.Brick] = []
    shard_hashes: list[str] = []
    for index, entry in enumerate(raw["bricks"]):
        brick, shard_hash = load_shard(path, entry, index)
        bricks.append(brick)
        shard_hashes.append(shard_hash)

    require(bricks[0].lam_lo == TARGET_LO, "LEFT_ENDPOINT_NOT_INCLUDED", "coverage", 0, str(bricks[0].lam_lo))
    require(bricks[-1].lam_hi == TARGET_HI, "RIGHT_ENDPOINT_NOT_INCLUDED", "coverage", len(bricks) - 1, str(bricks[-1].lam_hi))
    for index, (left, right) in enumerate(zip(bricks, bricks[1:])):
        if right.lam_lo > left.lam_hi:
            fail("COVERAGE_GAP", "coverage", index + 1, f"{left.lam_hi} < {right.lam_lo}")
        if right.lam_lo < left.lam_hi:
            fail("COVERAGE_OVERLAP", "coverage", index + 1, f"{right.lam_lo} < {left.lam_hi}")

    results: list[dict[str, str]] = []
    receipt_hashes: list[str] = []
    for index, (brick, shard_hash) in enumerate(zip(bricks, shard_hashes)):
        margins = check_mathematics(brick, index)
        results.append(margins)
        if retain_receipts:
            receipt_hashes.append(write_receipt(index, brick, margins, shard_hash))

    seams = [seam_check(pilot_bricks[0], bricks[0], TARGET_LO, 0, "left-prototype")]
    seams.extend(seam_check(left, right, left.lam_hi, index + 1, f"internal-{index:04d}") for index, (left, right) in enumerate(zip(bricks, bricks[1:])))
    seams.append(seam_check(bricks[-1], pilot_bricks[1], TARGET_HI, len(bricks), "right-prototype"))
    result = {
        "status": "PASS",
        "schema": "cmv-middle-face-tiling-check-receipt-v1",
        "target_lambda": [str(TARGET_LO), str(TARGET_HI)],
        "closed_interval_covered": True,
        "adjacent_by_exact_equality": True,
        "brick_count": len(bricks),
        "certified_brick_intervals": [[str(brick.lam_lo), str(brick.lam_hi)] for brick in bricks],
        "per_brick_decisions": "all branch, denominator, C4, fold, C3, equal-area, K3, and G decisions strict",
        "minimum_strict_margins": compact_margin_summary(results),
        "seam_count_including_prototypes": len(seams),
        "seams": seams,
        "pi_interval": [str(k.PI.lo), str(k.PI.hi)],
        "proof_method": "sequential opposite faces plus scalar derivative uniqueness; no interval Jacobian",
        "python": platform.python_version(),
        "manifest_sha256": byte_hash(path),
        "checker_sha256": byte_hash(Path(__file__)),
        "kernel_sha256": byte_hash(KERNEL_PATH),
        "pilot_certificate_sha256": byte_hash(PILOT_CERT),
    }
    if retain_receipts:
        result["per_brick_receipt_sha256"] = receipt_hashes
    return result


def failure_json(exc: k.CheckFailure) -> dict[str, Any]:
    result: dict[str, Any] = {"status": "FAIL", "failure": {"code": exc.code, "phase": exc.phase, "brick_index": exc.brick, "detail": exc.detail}}
    if exc.value is not None:
        result["failure"]["interval"] = [str(exc.value.lo), str(exc.value.hi)]
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("manifest", nargs="?", default=str(ROOT / "manifest.json"))
    parser.add_argument("--output")
    parser.add_argument("--retain-brick-receipts", action="store_true")
    args = parser.parse_args()
    try:
        result = check(Path(args.manifest), args.retain_brick_receipts)
        status = 0
    except k.CheckFailure as exc:
        result, status = failure_json(exc), 1
    except Exception as exc:
        result, status = {"status": "FAIL", "failure": {"code": "UNEXPECTED_CHECKER_EXCEPTION", "phase": "internal", "brick_index": None, "detail": f"{type(exc).__name__}: {exc}"}}, 1
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(text)
    print(text, end="")
    raise SystemExit(status)


if __name__ == "__main__":
    main()
