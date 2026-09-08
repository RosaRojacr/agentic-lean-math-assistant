#!/usr/bin/env python3
"""Untrusted high-precision producer for exact middle face-brick witnesses."""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
from decimal import Decimal
from fractions import Fraction as Q
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parent
TARGET_LO = Q(102001, 100000)
TARGET_HI = Q(25781, 25000)
STEP = Q(1, 10000)
mp.mp.dps = 100


def type3(lam: mp.mpf, h: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    q = 2 * h - 1
    u = mp.sqrt(1 - q * q)
    droot = mp.sqrt(lam * lam - q * q)
    angle = lam * mp.acos(q / lam) + mp.asin(q)
    delta = droot / lam - u
    return (angle + mp.pi / 2 + (q + 2) * delta) / h**2, 2 * (angle + mp.pi / 2 + delta) / h


def type4(lam: mp.mpf, h: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
    u = mp.sqrt(1 - h * h)
    droot = mp.sqrt(lam * lam - h * h)
    angle = lam * mp.acos(h / lam) + mp.asin(h)
    delta = droot / lam - u
    return 2 * (angle + h * delta) / h**2, 4 * angle / h


def k4(lam: mp.mpf, h: mp.mpf) -> mp.mpf:
    u = mp.sqrt(1 - h * h)
    droot = mp.sqrt(lam * lam - h * h)
    angle = lam * mp.acos(h / lam) + mp.asin(h)
    return 4 * (h * (1 / u - lam / droot) - angle)


def bisect(function, lo: mp.mpf, hi: mp.mpf) -> mp.mpf:
    f_lo, f_hi = function(lo), function(hi)
    if not f_lo < 0 < f_hi:
        raise ValueError(f"invalid increasing-root bracket: {f_lo}, {f_hi}")
    for _ in range(400):
        mid = (lo + hi) / 2
        if function(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def solution(lam: mp.mpf) -> tuple[mp.mpf, ...]:
    h4 = bisect(lambda h: k4(lam, h), mp.mpf("0.9"), mp.mpf("0.999999"))
    area4, perimeter4 = type4(lam, h4)
    h3 = bisect(lambda h: area4 - type3(lam, h)[0], mp.mpf("0.8"), mp.mpf("0.98"))
    x = mp.acos(h4)
    y = mp.acos(h4 / lam)
    w = mp.acos(2 * h3 - 1)
    v = mp.acos((2 * h3 - 1) / lam)
    gap = type3(lam, h3)[1] - perimeter4
    return x, y, w, v, gap


def mpq(value: Q) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def rational(value: mp.mpf, digits: int = 19) -> str:
    return str(Q(Decimal(mp.nstr(value, digits))))


def semantic_hash(raw: dict) -> str:
    payload = {key: value for key, value in raw.items() if key != "payload_sha256"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def byte_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def endpoints() -> list[Q]:
    result = [TARGET_LO]
    while result[-1] + STEP < TARGET_HI:
        result.append(result[-1] + STEP)
    result.append(TARGET_HI)
    return result


def build(write: bool) -> dict:
    points = endpoints()
    solutions = [solution(mpq(point)) for point in points]
    entries: list[dict] = []
    for index, (lo_q, hi_q, left, right) in enumerate(zip(points, points[1:], solutions, solutions[1:])):
        lo, hi = mpq(lo_q), mpq(hi_q)
        centers = [(left[j] + right[j]) / 2 for j in range(4)]
        slopes = [(right[j] - left[j]) / (hi - lo) for j in range(4)]
        mid = (lo + hi) / 2
        midpoint = solution(mid)
        y_shear = mp.sin(midpoint[0]) / (mid * mp.sin(midpoint[1]))
        v_shear = mp.sin(midpoint[2]) / (mid * mp.sin(midpoint[3]))
        brick_id = f"B{index:04d}"
        brick = {
            "lambda": [str(lo_q), str(hi_q)],
            "centers": [rational(value) for value in centers],
            "slopes": [rational(value) for value in slopes],
            "y_xi_slope": rational(y_shear, 8),
            "v_rho_slope": rational(v_shear, 8),
            "radii": ["1/100000", "1/1000000", "1/100000", "1/1000000"],
        }
        shard = {"schema": "cmv-middle-face-brick-v1", "model": "cmv-angle-fold-equal-area-v1", "brick_id": brick_id, "brick": brick}
        shard["payload_sha256"] = semantic_hash(shard)
        shard_path = ROOT / "bricks" / f"{brick_id}.json"
        shard_text = json.dumps(shard, indent=2, sort_keys=True) + "\n"
        if write:
            shard_path.write_text(shard_text)
        elif not shard_path.exists() or shard_path.read_text() != shard_text:
            raise RuntimeError(f"retained shard differs: {brick_id}")
        diagnostic = {
            "schema": "cmv-middle-face-brick-producer-diagnostic-v1",
            "brick_id": brick_id,
            "producer_is_proof_decision": False,
            "precision_decimal_digits": mp.mp.dps,
            "lambda": [str(lo_q), str(hi_q)],
            "endpoint_gap_decimal": [mp.nstr(left[4], 40), mp.nstr(right[4], 40)],
            "endpoint_angles_decimal": [[mp.nstr(left[j], 40), mp.nstr(right[j], 40)] for j in range(4)],
            "shard_sha256": hashlib.sha256(shard_text.encode()).hexdigest(),
        }
        diagnostic_path = ROOT / "diagnostics" / f"{brick_id}.json"
        diagnostic_text = json.dumps(diagnostic, indent=2, sort_keys=True) + "\n"
        if write:
            diagnostic_path.write_text(diagnostic_text)
        elif not diagnostic_path.exists() or diagnostic_path.read_text() != diagnostic_text:
            raise RuntimeError(f"retained diagnostic differs: {brick_id}")
        entries.append({"brick_id": brick_id, "path": f"bricks/{brick_id}.json", "certificate_sha256": hashlib.sha256(shard_text.encode()).hexdigest()})
    manifest = {
        "schema": "cmv-middle-face-tiling-manifest-v1",
        "model": "cmv-angle-fold-equal-area-v1",
        "arithmetic": {"atan_terms": 36, "trig_terms": 14, "pi_formula": "16*atan(1/5)-4*atan(1/239)", "decision_type": "fractions.Fraction mean-value intervals"},
        "target_lambda": [str(TARGET_LO), str(TARGET_HI)],
        "left_prototype_overlap": str(TARGET_LO),
        "right_prototype_overlap": str(TARGET_HI),
        "adjacency": "exact-equality",
        "brick_count": len(entries),
        "bricks": entries,
    }
    manifest["payload_sha256"] = semantic_hash(manifest)
    text = json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    manifest_path = ROOT / "manifest.json"
    if write:
        manifest_path.write_text(text)
    identical = manifest_path.exists() and manifest_path.read_text() == text
    receipt = {
        "status": "PASS" if identical else "FAIL",
        "schema": "cmv-middle-face-tiling-generation-receipt-v1",
        "retained_manifest_identical": identical,
        "retained_bricks": len(entries),
        "target_lambda": [str(TARGET_LO), str(TARGET_HI)],
        "precision_decimal_digits": mp.mp.dps,
        "mpmath_version": mp.__version__,
        "python": platform.python_version(),
        "producer_is_proof_decision": False,
        "manifest_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "generator_sha256": byte_hash(Path(__file__)),
    }
    receipt_text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    (ROOT / "generation_receipt.json").write_text(receipt_text)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    receipt = build(args.write)
    print(json.dumps(receipt, indent=2, sort_keys=True))
    raise SystemExit(0 if receipt["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
