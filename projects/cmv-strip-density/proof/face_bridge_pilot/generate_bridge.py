#!/usr/bin/env python3
"""Untrusted high-precision producer for the retained exact bridge witnesses."""
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
        f_mid = function(mid)
        if f_mid < 0:
            lo, f_lo = mid, f_mid
        else:
            hi, f_hi = mid, f_mid
    return (lo + hi) / 2


def solution(lam: mp.mpf) -> tuple[mp.mpf, ...]:
    h4 = bisect(lambda h: k4(lam, h), mp.mpf("0.9"), mp.mpf("0.999999"))
    area4, perimeter4 = type4(lam, h4)
    # A3 is decreasing on this descending branch, so negate for bisect.
    h3 = bisect(lambda h: area4 - type3(lam, h)[0], mp.mpf("0.8"), mp.mpf("0.98"))
    x = mp.acos(h4)
    y = mp.acos(h4 / lam)
    w = mp.acos(2 * h3 - 1)
    v = mp.acos((2 * h3 - 1) / lam)
    gap = type3(lam, h3)[1] - perimeter4
    return x, y, w, v, gap


def rational19(value: mp.mpf) -> str:
    return str(Q(Decimal(mp.nstr(value, 19))))


def semantic_hash(raw: dict) -> str:
    encoded = json.dumps(raw, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def build() -> tuple[dict, list[dict]]:
    specs = [
        ((Q(51, 50), Q(102001, 100000)), Q(67, 100), Q(112, 125)),
        ((Q(25781, 25000), Q(33, 32)), Q(13, 20), Q(219, 250)),
    ]
    bricks, diagnostics = [], []
    for (lo_q, hi_q), y_slope, v_slope in specs:
        lo, hi = mp.mpf(lo_q.numerator) / lo_q.denominator, mp.mpf(hi_q.numerator) / hi_q.denominator
        left, right = solution(lo), solution(hi)
        centers = [(left[j] + right[j]) / 2 for j in range(4)]
        slopes = [(right[j] - left[j]) / (hi - lo) for j in range(4)]
        bricks.append({
            "lambda": [str(lo_q), str(hi_q)],
            "centers": [rational19(value) for value in centers],
            "slopes": [rational19(value) for value in slopes],
            "y_xi_slope": str(y_slope),
            "v_rho_slope": str(v_slope),
            "radii": ["1/10000000", "1/100000000", "1/10000000", "1/100000000"],
        })
        diagnostics.append({
            "lambda": [str(lo_q), str(hi_q)],
            "endpoint_gap_decimal": [mp.nstr(left[4], 40), mp.nstr(right[4], 40)],
            "endpoint_angles_decimal": [[mp.nstr(left[j], 40), mp.nstr(right[j], 40)] for j in range(4)],
        })
    payload = {
        "schema": "cmv-opposite-face-bridge-pilot-v1",
        "model": "cmv-angle-fold-equal-area-v1",
        "arithmetic": {"atan_terms": 36, "trig_terms": 14, "pi_formula": "16*atan(1/5)-4*atan(1/239)", "decision_type": "fractions.Fraction mean-value intervals"},
        "prototype_scope": {"near_one_proposed_overlap": "51/50", "compact_overlap": "33/32", "uncovered_lambda_intervals": [["102001/100000", "25781/25000"]], "claim": "prototype bricks only; not contiguous bridge coverage"},
        "bricks": bricks,
    }
    payload["payload_sha256"] = semantic_hash(payload)
    return payload, diagnostics


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--receipt", default="generation_receipt.json")
    args = parser.parse_args()
    certificate, diagnostics = build()
    text = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    retained = ROOT / "bridge_certificate.json"
    identical = retained.exists() and retained.read_text() == text
    if args.write:
        retained.write_text(text)
        identical = True
    receipt = {
        "status": "PASS" if identical else "FAIL",
        "retained_certificate_identical": identical,
        "precision_decimal_digits": mp.mp.dps,
        "mpmath_version": mp.__version__,
        "python": platform.python_version(),
        "producer_is_proof_decision": False,
        "diagnostics": diagnostics,
        "generated_certificate_sha256": hashlib.sha256(text.encode()).hexdigest(),
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    receipt_text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    (ROOT / args.receipt).write_text(receipt_text)
    print(receipt_text, end="")
    raise SystemExit(0 if identical else 1)


if __name__ == "__main__":
    main()
