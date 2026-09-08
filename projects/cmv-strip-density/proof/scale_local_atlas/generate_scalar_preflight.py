#!/usr/bin/env python3
"""Untrusted moving-bracket producer for the source-native scalar preflight."""
from __future__ import annotations

import argparse
import json
import time
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

import mpmath as mp

import check_scalar_preflight as check

mp.mp.dps = 90
DYADIC_BITS = 120
INITIAL_EPS_RADIUS = Q(1, 1 << 20)
MAX_DOUBLINGS = 20


def real(x: Q) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


def rationalize(x: mp.mpf) -> Q:
    scale = 1 << DYADIC_BITS
    return Q(int(mp.nint(x * scale)), scale)


def aq(x: mp.mpf) -> mp.mpf:
    return mp.atan(x) / x if x else mp.mpf(1)


def source_values(t: mp.mpf, a: mp.mpf, b: mp.mpf):
    lam = 1 + t ** 3

    def atom(c):
        x = 1 - t ** 2 * c
        ui = 2 * c - t ** 2 * c ** 2
        vi = 2 * c + 2 * t - t ** 2 * c ** 2 + t ** 4
        u = mp.sqrt(ui)
        v = mp.sqrt(vi)
        k = x ** 2 * (2 + t ** 3) / (u * v * (v + lam * u))
        d = x ** 2 * (2 + t ** 3) / (lam * (v + lam * u))
        rho = x * (2 + t ** 3) / ((u + v) * (x ** 2 + t ** 2 * u * v))
        h = t ** 2 * (v / x) * aq(t * v / x) + rho * aq(t ** 2 * rho)
        return x, k, d, h

    h4, k4, d4, h_angle4 = atom(a)
    _, _, d3, h_angle3 = atom(2 * b)
    h3 = 1 - t ** 2 * b
    fold = h4 * k4 - mp.pi / 2 - t ** 2 * h_angle4
    area = (mp.pi * (b - a) * (h4 + h3)
            + h4 ** 2 * (h_angle3 + (2 * h3 + 1) * d3)
            - 2 * h3 ** 2 * (h_angle4 + h4 * d4))
    gap = (a - b) * k4 + h3 * d4 - h4 * d3
    return fold, area, gap


@lru_cache(maxsize=None)
def root_at(t_q: Q) -> tuple[mp.mpf, mp.mpf]:
    t = real(t_q)
    a = mp.findroot(lambda x: source_values(t, x, mp.mpf("0.74"))[0],
                    (mp.mpf("0.30"), mp.mpf("0.40")), tol=mp.mpf("1e-75"))
    b = mp.findroot(lambda x: source_values(t, a, x)[1],
                    (mp.mpf("0.65"), mp.mpf("0.80")), tol=mp.mpf("1e-75"))
    fold, area, _ = source_values(t, a, b)
    if abs(fold) > mp.mpf("1e-70") or abs(area) > mp.mpf("1e-70"):
        raise ValueError("untrusted scalar root solve did not converge")
    return a, b


def secant(lo: Q, hi: Q, selector: int) -> tuple[Q, Q]:
    y_lo = root_at(lo)[selector]
    y_hi = root_at(hi)[selector]
    slope = rationalize((y_hi - y_lo) / real(hi - lo))
    intercept = rationalize(y_lo - real(lo) * real(slope))
    return intercept, slope


def make_cell(lo: Q, hi: Q) -> dict:
    return {
        "t": (lo, hi),
        "p4": secant(lo, hi, 0),
        "p3": secant(lo, hi, 1),
        "eps4": (-INITIAL_EPS_RADIUS, INITIAL_EPS_RADIUS),
        "eps3": (-INITIAL_EPS_RADIUS, INITIAL_EPS_RADIUS),
    }


def tune(cell: dict) -> tuple[dict, dict]:
    fold_doublings = 0
    area_doublings = 0
    last = None
    for _ in range(2 * MAX_DOUBLINGS + 3):
        last = check.check_cell(cell)
        if last["status"] == "SCALAR_CELL_PASS":
            return last, {"fold_doublings": fold_doublings,
                          "area_doublings": area_doublings}
        fold = last.get("fold_faces", {})
        area = last.get("area_faces", {})
        fold_failed = (not fold or Q(fold["eps_lower"][0]) <= 0
                       or Q(fold["eps_upper"][1]) >= 0)
        area_failed = (not area or Q(area["eps_lower"][1]) >= 0
                       or Q(area["eps_upper"][0]) <= 0)
        if fold_failed and fold_doublings < MAX_DOUBLINGS:
            fold_doublings += 1
            radius = INITIAL_EPS_RADIUS * 2 ** fold_doublings
            cell["eps4"] = (-radius, radius)
            continue
        if area_failed and area_doublings < MAX_DOUBLINGS:
            area_doublings += 1
            radius = INITIAL_EPS_RADIUS * 2 ** area_doublings
            cell["eps3"] = (-radius, radius)
            continue
        break
    raise ValueError({"message": "unable to tune scalar bracket",
                      "t": list(map(str, cell["t"])),
                      "fold_doublings": fold_doublings,
                      "area_doublings": area_doublings,
                      "last": last})


def serialized_cell(cell: dict) -> dict:
    return {key: [str(value) for value in cell[key]]
            for key in ["t", "p4", "p3", "eps4", "eps3"]}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    cpu_started = time.process_time()
    bands = []
    attempts = []
    for j in range(13):
        rows = []
        logs = []
        for k in range(64):
            cell_started = time.process_time()
            lo, hi = check.expected_cell(j, k)
            cell = make_cell(lo, hi)
            result, log = tune(cell)
            rows.append(serialized_cell(cell))
            logs.append({"index": k, **log, "status": result["status"],
                         "producer_cpu_seconds": time.process_time() - cell_started})
        band_lo, band_hi = check.expected_band(j)
        bands.append({"t": [str(band_lo), str(band_hi)], "cells": rows})
        attempts.append({"band": j, "cells": logs})
        print(f"band {j}: {sum(x['status'] == 'SCALAR_CELL_PASS' for x in logs)}/64",
              flush=True)
    remote_started = time.process_time()
    remote = make_cell(Q(1, 10), Q(101, 1000))
    remote_result, remote_log = tune(remote)
    remote_cpu_seconds = time.process_time() - remote_started
    manifest = {"schema": check.SCHEMA, "contract": check.EXPECTED_CONTRACT,
                "bands": bands, "remote": serialized_cell(remote)}
    args.output.write_text(json.dumps(manifest, indent=2) + "\n")
    elapsed = time.monotonic() - started
    cpu_elapsed = time.process_time() - cpu_started
    maximum_cell_cpu = max(
        [cell["producer_cpu_seconds"]
         for band in attempts for cell in band["cells"]] + [remote_cpu_seconds])
    receipt = {
        "status": "UNTRUSTED_PRODUCER_COMPLETE",
        "proof_status": "NOT_KERNEL_REPLAYED",
        "schema": check.SCHEMA,
        "target_cells": 832,
        "remote_cells": 1,
        "mpmath_decimal_digits": 90,
        "predictor_dyadic_bits": DYADIC_BITS,
        "retained_predictor_degree": 1,
        "initial_epsilon_radius": str(INITIAL_EPS_RADIUS),
        "maximum_face_directed_doublings": MAX_DOUBLINGS,
        "distinct_root_endpoints": root_at.cache_info().currsize,
        "elapsed_seconds": elapsed,
        "cpu_seconds": cpu_elapsed,
        "maximum_producer_cpu_seconds_per_cell": maximum_cell_cpu,
        "attempts": attempts,
        "remote": {**remote_log, "status": remote_result["status"],
                   "producer_cpu_seconds": remote_cpu_seconds},
    }
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items() if key != "attempts"}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
