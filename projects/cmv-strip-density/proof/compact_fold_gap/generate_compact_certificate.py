#!/usr/bin/env python3
"""Produce rational root slabs for the independent compact checker.

This producer uses mpmath only to locate candidate roots.  It contains no
checker interval implementation and emits no sign claims or transcendental
bounds.  Proof status is obtained only by running check_compact_certificate.py
as a separate process over the serialized rational payload.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

import mpmath as mp

SCHEMA = "cmv-compact-rational-certificate-v1"
LOWER = Q(33, 32)
UPPER = Q(9, 7)
DEFAULT_CELLS = 1024
ROOT_DENOMINATOR_BITS = 48
H4_ROOT_PADDING = Q(1, 1 << 15)
H3_ROOT_PADDING = Q(1, 1 << 9)


def mpq(value: Q) -> mp.mpf:
    return mp.mpf(value.numerator) / value.denominator


def type3(lam: mp.mpf, h: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    q = 2 * h - 1
    u = mp.sqrt(1 - q * q)
    droot = mp.sqrt(lam * lam - q * q)
    alpha = mp.acos(q / lam)
    angle = lam * alpha + mp.asin(q)
    delta = droot / lam - u
    area = (angle + mp.pi / 2 + (q + 2) * delta) / (h * h)
    perimeter = 2 * (angle + mp.pi / 2 + delta) / h
    fold = 4 * h * ((1 + q) / u - (lam * lam + q) / (lam * droot))
    fold -= 2 * (angle + mp.pi / 2 + delta)
    return area, perimeter, fold


def type4(lam: mp.mpf, h: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    u = mp.sqrt(1 - h * h)
    droot = mp.sqrt(lam * lam - h * h)
    alpha = mp.acos(h / lam)
    angle = lam * alpha + mp.asin(h)
    delta = droot / lam - u
    area = 2 * (angle + h * delta) / (h * h)
    perimeter = 4 * angle / h
    fold = 4 * (h * (1 / u - lam / droot) - angle)
    return area, perimeter, fold


def bisect_increasing(function, low: mp.mpf, high: mp.mpf) -> mp.mpf:
    f_low = function(low)
    f_high = function(high)
    if not (f_low < 0 < f_high):
        raise RuntimeError(f"root bracket is not increasing: {f_low}, {f_high}")
    for _ in range(260):
        middle = (low + high) / 2
        if function(middle) < 0:
            low = middle
        else:
            high = middle
    return (low + high) / 2


def fold_root(lam: mp.mpf) -> mp.mpf:
    return bisect_increasing(
        lambda h: type4(lam, h)[2], mp.mpf("0.5000000001"), mp.mpf(1) - mp.mpf("1e-70")
    )


def descending_equal_area_root(lam: mp.mpf, h4: mp.mpf) -> mp.mpf:
    target = type4(lam, h4)[0]
    upper = bisect_increasing(
        lambda h: type3(lam, h)[2],
        mp.mpf("0.5000000001"),
        mp.mpf(1) - mp.mpf("1e-70"),
    )
    # A3 decreases up to its K3 fold, so target-A3 is increasing there.
    return bisect_increasing(
        lambda h: target - type3(lam, h)[0],
        mp.mpf("0.5000000001"),
        upper,
    )


def floor_dyadic(value: mp.mpf) -> Q:
    scale = 1 << ROOT_DENOMINATOR_BITS
    return Q(int(mp.floor(value * scale)), scale)


def ceil_dyadic(value: mp.mpf) -> Q:
    scale = 1 << ROOT_DENOMINATOR_BITS
    return Q(int(mp.ceil(value * scale)), scale)


def qstr(value: Q) -> str:
    return str(value)


def payload_hash(boxes: list[dict[str, object]]) -> str:
    encoded = json.dumps(boxes, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def file_hash(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build_boxes(cells: int) -> list[dict[str, object]]:
    boundaries = [LOWER + (UPPER - LOWER) * Q(index, cells) for index in range(cells + 1)]
    # Roots at all exact cell boundaries are shared.  Midpoint roots guard
    # against an unnoticed nonmonotonic excursion; the exact checker remains
    # the authority on every resulting slab.
    endpoint_roots: list[tuple[mp.mpf, mp.mpf]] = []
    for boundary in boundaries:
        lam = mpq(boundary)
        h4 = fold_root(lam)
        h3 = descending_equal_area_root(lam, h4)
        endpoint_roots.append((h4, h3))

    boxes: list[dict[str, object]] = []
    for index in range(cells):
        lam_low, lam_high = boundaries[index], boundaries[index + 1]
        lam_middle = mpq((lam_low + lam_high) / 2)
        h4_middle = fold_root(lam_middle)
        h3_middle = descending_equal_area_root(lam_middle, h4_middle)
        h4_values = [endpoint_roots[index][0], h4_middle, endpoint_roots[index + 1][0]]
        h3_values = [endpoint_roots[index][1], h3_middle, endpoint_roots[index + 1][1]]
        h4_low = floor_dyadic(min(h4_values)) - H4_ROOT_PADDING
        h4_high = ceil_dyadic(max(h4_values)) + H4_ROOT_PADDING
        h3_low = floor_dyadic(min(h3_values)) - H3_ROOT_PADDING
        h3_high = ceil_dyadic(max(h3_values)) + H3_ROOT_PADDING
        boxes.append({
            "lambda": [qstr(lam_low), qstr(lam_high)],
            "h4_root": [qstr(h4_low), qstr(h4_high)],
            "h3_root": [qstr(h3_low), qstr(h3_high)],
        })
    return boxes


def main() -> int:
    parser = argparse.ArgumentParser()
    here = Path(__file__).resolve().parent
    parser.add_argument("--cells", type=int, default=DEFAULT_CELLS)
    parser.add_argument("--output", type=Path, default=here / "compact_certificate.json")
    parser.add_argument("--receipt", type=Path, default=here / "generation_receipt.json")
    parser.add_argument("--checker-receipt", type=Path, default=here / "checker_receipt.json")
    args = parser.parse_args()
    if args.cells <= 0:
        raise SystemExit("--cells must be positive")

    mp.mp.dps = 110
    boxes = build_boxes(args.cells)
    certificate = {
        "schema": SCHEMA,
        "target": {"lambda_lower": qstr(LOWER), "lambda_upper": qstr(UPPER)},
        "precision": {"sqrt_bits": 80, "atan_terms": 36, "trig_terms": 14},
        "boxes": boxes,
        "payload_sha256": payload_hash(boxes),
    }
    args.output.write_text(json.dumps(certificate, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    checker = here / "check_compact_certificate.py"
    command = [sys.executable, str(checker), str(args.output), "--receipt", str(args.checker_receipt)]
    completed = subprocess.run(command, text=True, capture_output=True, check=False)
    if completed.returncode != 0:
        print(completed.stdout, end="")
        print(completed.stderr, end="", file=sys.stderr)
        return completed.returncode

    receipt = {
        "status": "GENERATED_AND_INDEPENDENTLY_CHECKED",
        "python": platform.python_version(),
        "mpmath": mp.__version__,
        "mpmath_decimal_digits": mp.mp.dps,
        "h4_root_padding": qstr(H4_ROOT_PADDING),
        "h3_root_padding": qstr(H3_ROOT_PADDING),
        "cells": args.cells,
        "root_denominator_bits": ROOT_DENOMINATOR_BITS,
        "producer_sha256": file_hash(Path(__file__)),
        "checker_sha256": file_hash(checker),
        "certificate_sha256": file_hash(args.output),
        "payload_sha256": certificate["payload_sha256"],
        "checker_command": command,
        "checker_stdout_sha256": hashlib.sha256(completed.stdout.encode()).hexdigest(),
    }
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(completed.stdout, end="")
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
