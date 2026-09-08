#!/usr/bin/env python3
"""Independent audit of the source-native scalar preflight artifacts."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import time
from fractions import Fraction as Q
from pathlib import Path

import mpmath as mp

mp.mp.dps = 80
SCHEMA = "cmv-source-native-scalar-preflight-v1"
N = Q(126334)
REQUIRED_GUARDS = {
    "t_pos", "t_lt_half", "lambda_sub_one", "lambda_pos", "t_sq",
    "a_pos", "b_pos", "height_order_b_sub_a", "height_order_hFour_sub_hThree",
    "hFour_pos", "hFour_gt_half", "hFour_lt_one", "hThree_pos",
    "hThree_gt_half", "hThree_lt_one", "typeThreeShape_pos",
    "typeThreeShape_lt_one", "positive_area_factor", "uInner_four",
    "vInner_four", "uInner_three", "vInner_three", "U_four", "V_four",
    "U_three", "V_three", "radical_sum_four", "radical_sum_three",
    "K_den_four", "K_den_three", "D_den_four", "D_den_three",
    "rho_den_four", "rho_den_three", "rho_four", "rho_three",
    "atan_linear_four_pos", "atan_quadratic_four_pos",
    "atan_linear_three_pos", "atan_quadratic_three_pos",
    "atan_linear_four_lt_half", "atan_quadratic_four_lt_half",
    "atan_linear_three_lt_half", "atan_quadratic_three_lt_half",
}
REQUIRED_ARGUMENTS = {"linear_four", "quadratic_four", "linear_three", "quadratic_three"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def real(x: Q) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


def pair(raw, where: str) -> tuple[Q, Q]:
    if not isinstance(raw, list) or len(raw) != 2:
        raise ValueError(f"malformed interval at {where}")
    value = (Q(raw[0]), Q(raw[1]))
    if value[0] > value[1]:
        raise ValueError(f"reversed interval at {where}")
    return value


def expected_band(j: int) -> tuple[Q, Q]:
    return Q(2 ** (j + 1), N), min(Q(2 ** (j + 2), N), Q(1, 10))


def expected_cell(j: int, k: int) -> tuple[Q, Q]:
    lo, hi = expected_band(j)
    return lo + Q(k, 64) * (hi - lo), lo + Q(k + 1, 64) * (hi - lo)


def aq(x: mp.mpf) -> mp.mpf:
    return mp.atan(x) / x if x else mp.mpf(1)


def literal_source(t: mp.mpf, a: mp.mpf, b: mp.mpf):
    lam = 1 + t ** 3

    def atom(c):
        x = 1 - t ** 2 * c
        ui = 2 * c - t ** 2 * c ** 2
        vi = 2 * c + 2 * t - t ** 2 * c ** 2 + t ** 4
        u = mp.sqrt(ui)
        v = mp.sqrt(vi)
        radical_sum = v + lam * u
        k_den = u * v * radical_sum
        d_den = lam * radical_sum
        rho_den = (u + v) * (x ** 2 + t ** 2 * u * v)
        k = x ** 2 * (2 + t ** 3) / k_den
        d = x ** 2 * (2 + t ** 3) / d_den
        rho = x * (2 + t ** 3) / rho_den
        arg1 = t * v / x
        arg2 = t ** 2 * rho
        h = t ** 2 * (v / x) * aq(arg1) + rho * aq(arg2)
        return {"x": x, "ui": ui, "vi": vi, "u": u, "v": v,
                "radical_sum": radical_sum, "k_den": k_den, "d_den": d_den,
                "rho_den": rho_den, "k": k, "d": d, "rho": rho,
                "arg1": arg1, "arg2": arg2, "h": h}

    four = atom(a)
    three = atom(2 * b)
    h4 = four["x"]
    h3 = 1 - t ** 2 * b
    fold = h4 * four["k"] - mp.pi / 2 - t ** 2 * four["h"]
    area = (mp.pi * (b - a) * (h4 + h3)
            + h4 ** 2 * (three["h"] + (2 * h3 + 1) * three["d"])
            - 2 * h3 ** 2 * (four["h"] + h4 * four["d"]))
    gap = (a - b) * four["k"] + h3 * four["d"] - h4 * three["d"]
    guards = [t, mp.mpf("0.5") - t, t ** 3, lam, t ** 2, a, b, b - a,
              h4 - h3, h4, h4 - mp.mpf("0.5"), 1 - h4, h3,
              h3 - mp.mpf("0.5"), 1 - h3, three["x"], 1 - three["x"],
              h3 ** 2 * h4 ** 2, four["ui"], four["vi"], three["ui"], three["vi"],
              four["u"], four["v"], three["u"], three["v"],
              four["radical_sum"], three["radical_sum"],
              four["k_den"], three["k_den"], four["d_den"], three["d_den"],
              four["rho_den"], three["rho_den"], four["rho"], three["rho"],
              four["arg1"], four["arg2"], three["arg1"], three["arg2"],
              mp.mpf("0.5") - four["arg1"], mp.mpf("0.5") - four["arg2"],
              mp.mpf("0.5") - three["arg1"], mp.mpf("0.5") - three["arg2"]]
    return fold, area, gap, guards


def coefficient_value(coefficients, t: Q) -> Q:
    return Q(coefficients[0]) + Q(coefficients[1]) * t


def physical(cell: dict, t: Q, e4: Q, e3: Q):
    a = coefficient_value(cell["p4"], t) + t ** 2 * e4
    b = coefficient_value(cell["p3"], t) + t ** 2 * e3
    return real(t), real(a), real(b)


def strict_margin(interval, positive: bool) -> Q:
    lo, hi = pair(interval, "result")
    return lo if positive else -hi


def alternating_atan_bounds(inv: int, terms: int = 36) -> tuple[Q, Q]:
    x = Q(1, inv)
    partial = sum(((-1) ** k * x ** (2 * k + 1) / (2 * k + 1)
                   for k in range(terms)), Q(0))
    tail = x ** (2 * terms + 1) / (2 * terms + 1)
    return partial, partial + tail


def machin_pi_bounds() -> tuple[Q, Q]:
    lo5, hi5 = alternating_atan_bounds(5)
    lo239, hi239 = alternating_atan_bounds(239)
    return 16 * lo5 - 4 * hi239, 16 * hi5 - 4 * lo239


def validate_inventory(manifest: dict, result: dict) -> list[tuple[str, dict, dict]]:
    if manifest.get("schema") != SCHEMA or result.get("schema") != SCHEMA:
        raise ValueError("schema mismatch")
    if set(manifest) != {"schema", "contract", "bands", "remote"}:
        raise ValueError("manifest keys changed")
    contract = manifest["contract"]
    required_contract = {
        "density_parameter": "lambda=1+t^3", "target_bands": 13,
        "cells_per_band": 64, "target_cells": 832, "remote_cells": 1,
        "retained_predictor_degree": 1, "maximum_predictor_degree": 12,
        "maximum_transient_polynomial_degree": 24, "arithmetic_bits": 160,
        "maximum_arithmetic_bits": 512, "atan_quotient_polynomial_terms": 7,
        "additional_subdivision": 0,
    }
    if contract != required_contract:
        raise ValueError("frozen scalar contract changed")
    if (result.get("dependency_enclosure") !=
            "centered first-order Taylor interval"
            or result.get("retained_predictor_degree") != 1
            or result.get("outward_bits") != 160
            or result.get("atan_quotient_polynomial_terms") != 7):
        raise ValueError("checker method or complexity cap changed")
    if len(manifest["bands"]) != 13 or len(result.get("bands", [])) != 13:
        raise ValueError("band count changed")
    records = []
    for j, (band, output_band) in enumerate(zip(manifest["bands"], result["bands"])):
        if pair(band["t"], f"band {j}") != expected_band(j):
            raise ValueError("band endpoint mismatch")
        if len(band["cells"]) != 64 or len(output_band["cells"]) != 64:
            raise ValueError("cell count changed")
        for k, (cell, output) in enumerate(zip(band["cells"], output_band["cells"])):
            if pair(cell["t"], f"band {j} cell {k}") != expected_cell(j, k):
                raise ValueError("cell endpoint mismatch")
            records.append((f"band-{j}-cell-{k}", cell, output))
    if pair(manifest["remote"]["t"], "remote") != (Q(1, 10), Q(101, 1000)):
        raise ValueError("remote interval changed")
    records.append(("remote", manifest["remote"], result["remote"]))
    if len(records) != 833:
        raise ValueError("complete inventory missing")
    return records


def validate_result_record(name: str, output: dict) -> dict[str, Q]:
    if output.get("status") != "SCALAR_CELL_PASS":
        raise ValueError(f"nonpassing result at {name}")
    if set(output.get("guards", {})) != REQUIRED_GUARDS:
        raise ValueError(f"guard inventory changed at {name}")
    if set(output.get("atan_error_budgets", {})) != REQUIRED_ARGUMENTS:
        raise ValueError(f"atan budget inventory changed at {name}")
    margins = {
        "fold": min(strict_margin(output["fold_faces"]["eps_lower"], True),
                    strict_margin(output["fold_faces"]["eps_upper"], False)),
        "area": min(strict_margin(output["area_faces"]["eps_lower"], False),
                    strict_margin(output["area_faces"]["eps_upper"], True)),
        "gap": strict_margin(output["gap"], False),
        "guard": min(strict_margin(value, True) for value in output["guards"].values()),
    }
    if min(margins.values()) <= 0:
        raise ValueError(f"nonstrict saved enclosure at {name}")
    for row in output["atan_error_budgets"].values():
        b = Q(row["argument_bound"])
        if not 0 <= b <= Q(1, 2):
            raise ValueError(f"atan domain budget failed at {name}")
        if Q(row["value_tail_error"]) != b ** 14 / 15:
            raise ValueError(f"atan value tail changed at {name}")
        if Q(row["derivative_tail_error"]) != 14 * b ** 13 / 15 + 2 * b ** 15 / 17:
            raise ValueError(f"atan derivative tail changed at {name}")
    radical_names = {"U_four", "V_four", "U_three", "V_three"}
    if (set(output.get("sqrt_enclosures", {})) != radical_names
            or set(output.get("radicand_enclosures", {})) != radical_names):
        raise ValueError(f"sqrt witness inventory changed at {name}")
    for radical_name in radical_names:
        root_lo, root_hi = pair(
            output["sqrt_enclosures"][radical_name], f"sqrt at {name}")
        radicand_lo, radicand_hi = pair(
            output["radicand_enclosures"][radical_name], f"radicand at {name}")
        if not (0 < root_lo and root_lo ** 2 <= radicand_lo
                and radicand_hi <= root_hi ** 2):
            raise ValueError(f"invalid sqrt square witness at {name}")
    reciprocal_names = {
        "K_den_four", "D_den_four", "rho_den_four", "x_four",
        "K_den_three", "D_den_three", "rho_den_three", "x_three"}
    if set(output.get("reciprocal_witnesses", {})) != reciprocal_names:
        raise ValueError(f"reciprocal witness inventory changed at {name}")
    for reciprocal_name, witness in output["reciprocal_witnesses"].items():
        if set(witness) != {"denominator", "reciprocal"}:
            raise ValueError(f"malformed reciprocal witness at {name}")
        denominator_lo, denominator_hi = pair(
            witness["denominator"], f"reciprocal denominator at {name}")
        reciprocal_lo, reciprocal_hi = pair(
            witness["reciprocal"], f"reciprocal enclosure at {name}")
        if not (0 < denominator_lo and 0 < reciprocal_lo
                and reciprocal_lo * denominator_hi <= 1
                and 1 <= reciprocal_hi * denominator_lo):
            raise ValueError(f"invalid reciprocal product witness at {name}")
    if Q(output.get("sqrt_rounding_endpoint_error_bound", "0")) != Q(1, 2 ** 160):
        raise ValueError(f"sqrt rounding budget changed at {name}")
    if Q(output.get("dyadic_operation_rounding_ulp", "0")) != Q(1, 2 ** 160):
        raise ValueError(f"dyadic rounding budget changed at {name}")
    if output.get("discarded_predictor_terms") != "none":
        raise ValueError(f"unbudgeted predictor truncation at {name}")
    return margins


def diagnostic_record(cell: dict) -> tuple[Q, Q, Q, Q]:
    tlo, thi = pair(cell["t"], "diagnostic cell")
    tmid = (tlo + thi) / 2
    e4lo, e4hi = pair(cell["eps4"], "eps4")
    e3lo, e3hi = pair(cell["eps3"], "eps3")
    e4mid = (e4lo + e4hi) / 2
    e3mid = (e3lo + e3hi) / 2
    fold_margin = mp.inf
    area_margin = mp.inf
    gap_margin = mp.inf
    guard_margin = mp.inf
    for t in [tlo, tmid, thi]:
        for e4, positive in [(e4lo, True), (e4hi, False)]:
            f = literal_source(*physical(cell, t, e4, e3mid))[0]
            fold_margin = min(fold_margin, f if positive else -f)
        for e3, positive in [(e3lo, False), (e3hi, True)]:
            for e4 in [e4lo, e4mid, e4hi]:
                e = literal_source(*physical(cell, t, e4, e3))[1]
                area_margin = min(area_margin, e if positive else -e)
        for e4 in [e4lo, e4hi]:
            for e3 in [e3lo, e3hi]:
                _, _, gap, guards = literal_source(*physical(cell, t, e4, e3))
                gap_margin = min(gap_margin, -gap)
                guard_margin = min(guard_margin, *guards)
    if min(fold_margin, area_margin, gap_margin, guard_margin) <= 0:
        raise ValueError("independent literal-source diagnostic failed")
    scale = Q(10) ** 60
    def lower(x):
        return Q(int(mp.floor(x * scale)), scale)
    return tuple(lower(x) for x in [fold_margin, area_margin, gap_margin, guard_margin])


def expect_checker_failure(checker: Path, mutated: dict) -> bool:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        source = root / "bad.json"
        output = root / "out.json"
        source.write_text(json.dumps(mutated) + "\n")
        process = subprocess.run([sys.executable, str(checker), str(source),
                                  "--output", str(output)],
                                 stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                                 check=False, timeout=30)
        return process.returncode != 0


def mutation_checks(checker: Path, manifest: dict) -> dict[str, bool]:
    mutations = {}
    bad = copy.deepcopy(manifest); del bad["remote"]
    mutations["missing_remote"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["bands"][0]["cells"].pop()
    mutations["missing_cell"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["bands"][0]["cells"][0]["t"][0] = "1/126334"
    mutations["wrong_endpoint"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["bands"][0]["cells"][0]["t"][0] = 0.1
    mutations["floating_endpoint"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["bands"][0]["cells"][0]["p4"][0] = "0/1"
    mutations["noncanonical_rational"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["contract"]["maximum_arithmetic_bits"] = 513
    mutations["precision_escalation"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["contract"]["atan_quotient_polynomial_terms"] = 8
    mutations["atan_escalation"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["bands"][0]["cells"][0]["eps4"] = ["1", "-1"]
    mutations["reversed_bracket"] = expect_checker_failure(checker, bad)
    bad = copy.deepcopy(manifest); bad["contract"]["additional_subdivision"] = 1
    mutations["additional_subdivision"] = expect_checker_failure(checker, bad)
    if not all(mutations.values()):
        raise ValueError("one or more fail-closed mutation checks passed invalid input")
    return mutations


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--enclosures", type=Path, required=True)
    parser.add_argument("--checker", type=Path, required=True)
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.process_time()
    manifest = json.loads(args.manifest.read_text())
    result = json.loads(args.enclosures.read_text())
    if result.get("status") != "SCALAR_PREFLIGHT_PASS" or result.get("proof_status") != "NOT_KERNEL_REPLAYED":
        raise ValueError("top-level preflight status is not a numerical pass")
    if result.get("manifest_sha256") != sha256(args.manifest):
        raise ValueError("result is not bound to this manifest")
    records = validate_inventory(manifest, result)
    weakest = {key: None for key in ["fold", "area", "gap", "guard"]}
    diagnostic_weakest = {key: None for key in ["fold", "area", "gap", "guard"]}
    per_cell_cpu = []
    stress = {"band-0-cell-10", "band-10-cell-32", "band-10-cell-33",
              "band-10-cell-34", "remote"}
    stress_rows = {}
    for name, cell, output in records:
        cell_started = time.process_time()
        margins = validate_result_record(name, output)
        diagnostic = diagnostic_record(cell)
        for key, value in margins.items():
            if weakest[key] is None or value < weakest[key]["margin"]:
                weakest[key] = {"cell": name, "margin": value}
        for key, value in zip(diagnostic_weakest, diagnostic):
            if diagnostic_weakest[key] is None or value < diagnostic_weakest[key]["margin"]:
                diagnostic_weakest[key] = {"cell": name, "margin": value}
        elapsed = time.process_time() - cell_started
        per_cell_cpu.append({"cell": name, "audit_cpu_seconds": elapsed})
        if name in stress:
            stress_rows[name] = {"saved_margins": {k: str(v) for k, v in margins.items()},
                                 "literal_source_sample_margins": [str(x) for x in diagnostic]}
    if set(stress_rows) != stress:
        raise ValueError("compulsory stress inventory incomplete")
    pi_lo, pi_hi = machin_pi_bounds()
    saved_pi = pair(result.get("pi_interval"), "saved pi")
    if not (saved_pi[0] <= pi_lo and pi_hi <= saved_pi[1]):
        raise ValueError("saved dyadic pi interval does not contain the Machin enclosure")
    mutations = mutation_checks(args.checker, manifest)
    metrics = {
        "status": "SCALAR_METRICS_PASS",
        "proof_status": "NOT_KERNEL_REPLAYED",
        "cells": len(records),
        "weakest_exact_enclosure_margins": {
            key: {"cell": row["cell"], "margin": str(row["margin"])}
            for key, row in weakest.items()},
        "weakest_literal_source_sample_margins": {
            key: {"cell": row["cell"], "margin": str(row["margin"])}
            for key, row in diagnostic_weakest.items()},
        "stress_samples": stress_rows,
        "machin_pi_interval": [str(pi_lo), str(pi_hi)],
        "maximum_audit_cpu_seconds_per_cell": max(row["audit_cpu_seconds"] for row in per_cell_cpu),
        "per_cell_audit_cpu_seconds": per_cell_cpu,
    }
    args.metrics.write_text(json.dumps(metrics, indent=2) + "\n")
    diagnostics = {
        "status": "INDEPENDENT_SCALAR_AUDIT_PASS",
        "proof_status": "NOT_KERNEL_REPLAYED",
        "enclosure_method": "source-native centered first-order Taylor interval",
        "density_coverage_added": False,
        "inventory_records": len(records),
        "literal_source_records": len(records),
        "literal_source_sample_evaluations": len(records) * 36,
        "required_guard_count_per_cell": len(REQUIRED_GUARDS),
        "atan_budget_count_per_cell": len(REQUIRED_ARGUMENTS),
        "sqrt_square_witnesses_per_cell": 4,
        "reciprocal_product_witnesses_per_cell": 8,
        "machin_terms_per_arctangent": 36,
        "mutation_checks": mutations,
        "cpu_seconds": time.process_time() - started,
        "sha256": {"manifest": sha256(args.manifest),
                   "enclosures": sha256(args.enclosures),
                   "checker": sha256(args.checker)},
    }
    args.output.write_text(json.dumps(diagnostics, indent=2) + "\n")
    print(json.dumps(diagnostics))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
