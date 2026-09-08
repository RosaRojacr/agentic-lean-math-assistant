#!/usr/bin/env python3
"""Independently cross-check the numeric claims in ``Certificate.lean``."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

from mpmath import cos, findroot, mp, mpf, pi, sin

mp.dps = 60

GREEN, RED, DIM, RESET = "\033[32m", "\033[31m", "\033[2m", "\033[0m"
EXPECTED_BOUNDS = frozenset(
    {
        "sin_s_ge",
        "sin_s_le",
        "sin_r_ge",
        "sin_r_le",
        "cos_r_ge",
        "cos_r_le",
        "sin_q_ge",
        "sin_q_le",
        "cos_q_le",
        "sin_h_le",
        "cos_h_le",
    }
)


class CertificateInputError(ValueError):
    """The certificate could not be parsed into the expected claims."""


def ok(value: bool) -> str:
    return f"{GREEN}pass{RESET}" if value else f"{RED}FAIL{RESET}"


def _required_match(pattern: str, source: str, description: str) -> re.Match[str]:
    match = re.search(pattern, source, re.S)
    if match is None:
        raise CertificateInputError(f"missing or malformed {description}")
    return match


def parse(path: Path) -> dict[str, Any]:
    """Pull the required numerals straight out of the Lean source."""
    try:
        source = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise CertificateInputError(f"cannot read {path}: {exc}") from exc

    out: dict[str, Any] = {}
    out["pi_lo"] = mpf(
        _required_match(
            r"lemma\s+pi_lb\s*:\s*\(([\d.]+)\s*:", source, "pi_lb"
        ).group(1)
    )
    out["pi_hi"] = mpf(
        _required_match(
            r"lemma\s+pi_ub\s*:\s*π\s*<\s*\(([\d.]+)\s*:",
            source,
            "pi_ub",
        ).group(1)
    )
    out["t0"] = mpf(
        _required_match(
            r"lemma\s+F_at_witness\s*:\s*0\s*<\s*F\s*\(([\d.]+)\s*:",
            source,
            "F_at_witness",
        ).group(1)
    )

    bounds: dict[str, tuple[int, str, Any]] = {}
    bound_pattern = (
        r"lemma\s+(sin|cos)_([a-z])_(ge|le)\s*:.*?"
        r"(?:\(([\d.]+)\s*:\s*ℝ\)\s*≤\s*)?"
        r"(?:sin|cos)\s*\(\(π\s*-\s*[\d.]+\)\s*/\s*(\d+)\)"
        r"(?:\s*≤\s*([\d.]+))?"
    )
    for fn, level, direction, lhs, divisor, rhs in re.findall(
        bound_pattern, source, re.S
    ):
        name = f"{fn}_{level}_{direction}"
        if name in bounds:
            raise CertificateInputError(f"duplicate bound lemma {name}")
        literal = lhs or rhs
        if not literal:
            raise CertificateInputError(f"missing numeric value in {name}")
        bounds[name] = (int(divisor), direction, mpf(literal))

    missing = sorted(EXPECTED_BOUNDS - bounds.keys())
    unexpected = sorted(bounds.keys() - EXPECTED_BOUNDS)
    if missing or unexpected:
        details = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if unexpected:
            details.append("unexpected " + ", ".join(unexpected))
        raise CertificateInputError("malformed bound set: " + "; ".join(details))
    out["bounds"] = bounds

    final_match = _required_match(
        r"lemma\s+sin_witness_lt\s*:\s*sin\s*\(([\d.]+)\s*:\s*ℝ\)"
        r"\s*<\s*([\d.]+)",
        source,
        "sin_witness_lt",
    )
    out["two_t0"] = mpf(final_match.group(1))
    out["sin_final"] = mpf(final_match.group(2))

    optimized_cos = _required_match(
        r"lemma\s+opt_cos_witness_lower\s*:\s*"
        r"\(([\d.]+)\s*:\s*ℝ\)\s*≤\s*cos\s*\(([\d.]+)\s*:\s*ℝ\)",
        source,
        "opt_cos_witness_lower",
    )
    out["optimized_cos_lower"] = mpf(optimized_cos.group(1))
    out["optimized_witness"] = mpf(optimized_cos.group(2))
    optimized_inverse = _required_match(
        r"lemma\s+opt_inv_candidate_lt_three_cos_witness\s*:\s*"
        r"1\s*/\s*\(([\d.]+)\s*:\s*ℝ\)\s*<\s*"
        r"3\s*\*\s*cos\s*\(([\d.]+)\s*:\s*ℝ\)",
        source,
        "opt_inv_candidate_lt_three_cos_witness",
    )
    out["optimized_cutoff"] = mpf(optimized_inverse.group(1))
    inverse_witness = mpf(optimized_inverse.group(2))
    if inverse_witness != out["optimized_witness"]:
        raise CertificateInputError(
            "optimized certificate uses inconsistent witness literals"
        )
    return out


def _number(value: Any, digits: int = 60) -> str:
    return mp.nstr(value, digits)


def evaluate(data: dict[str, Any]) -> dict[str, Any]:
    """Compute all displayed assertions and their combined verdict."""
    pi_lo, pi_hi, t0 = data["pi_lo"], data["pi_hi"], data["t0"]
    checks: list[dict[str, Any]] = []

    def record(check_id: str, passed: bool, **details: Any) -> bool:
        checks.append({"check_id": check_id, "passed": bool(passed), **details})
        return bool(passed)

    record(
        "pi_bounds_sound",
        pi_lo < pi < pi_hi,
        lower=_number(pi_lo),
        upper=_number(pi_hi),
        actual=_number(pi),
    )
    record(
        "doubled_witness_consistent",
        2 * t0 == data["two_t0"],
        expected=_number(2 * t0),
        literal=_number(data["two_t0"]),
    )

    intervals: dict[int, tuple[Any, Any]] = {}
    for divisor in (2, 4, 8, 16):
        intervals[divisor] = (
            (pi_lo - 2 * t0) / divisor,
            (pi_hi - 2 * t0) / divisor,
        )

    bound_rows: list[dict[str, Any]] = []
    for name, (divisor, direction, value) in sorted(data["bounds"].items()):
        lo, hi = intervals[divisor]
        function = sin if name.startswith("sin") else cos
        true_value = (
            min(function(lo), function(hi))
            if direction == "ge"
            else max(function(lo), function(hi))
        )
        passed = value <= true_value if direction == "ge" else value >= true_value
        row = {
            "name": name,
            "divisor": divisor,
            "direction": direction,
            "value": value,
            "true": true_value,
            "slack": abs(value - true_value),
            "passed": passed,
        }
        bound_rows.append(row)
        record(
            f"individual_bound:{name}",
            passed,
            direction=direction,
            value=_number(value),
            worst_case=_number(true_value),
            slack=_number(row["slack"]),
        )

    needed = (3 * t0 - pi_hi) / mpf("1.5")
    final_bound = data["sin_final"]
    true_sin = sin(2 * t0)
    record(
        "final_sine_bound_sound",
        final_bound > true_sin,
        claimed_upper=_number(final_bound),
        actual=_number(true_sin),
    )
    record(
        "final_sine_bound_sufficient",
        final_bound < needed,
        claimed_upper=_number(final_bound),
        required_upper=_number(needed),
        margin=_number(needed - final_bound),
    )

    try:
        theta_star = findroot(
            lambda t: 3 * t - mpf(3) / 2 * sin(2 * t) - pi, mpf("1.3")
        )
    except Exception as exc:  # mpmath exposes several solver failure types
        raise CertificateInputError(f"cannot evaluate certificate numerics: {exc}") from exc
    k_cert, k_sharp = 3 * cos(t0), 3 * cos(theta_star)
    threshold, sharp_threshold = 1 / k_cert, 1 / k_sharp
    record(
        "witness_above_root",
        t0 > theta_star,
        witness=_number(t0),
        root=_number(theta_star),
    )
    record(
        "threshold_beats_four_over_pi",
        threshold < 4 / pi,
        threshold=_number(threshold),
        four_over_pi=_number(4 / pi),
    )
    optimized_witness = data["optimized_witness"]
    optimized_cos_lower = data["optimized_cos_lower"]
    optimized_cutoff = data["optimized_cutoff"]
    true_optimized_cos = cos(optimized_witness)
    optimized_threshold = 1 / (3 * true_optimized_cos)
    record(
        "optimized_cos_lower_sound",
        optimized_cos_lower <= true_optimized_cos,
        claimed_lower=_number(optimized_cos_lower),
        actual=_number(true_optimized_cos),
        slack=_number(true_optimized_cos - optimized_cos_lower),
    )
    record(
        "optimized_inverse_bound_sufficient",
        1 / optimized_cutoff < 3 * optimized_cos_lower,
        reciprocal_cutoff=_number(1 / optimized_cutoff),
        certified_three_cos_lower=_number(3 * optimized_cos_lower),
        margin=_number(3 * optimized_cos_lower - 1 / optimized_cutoff),
    )
    record(
        "optimized_witness_above_root",
        optimized_witness > theta_star,
        witness=_number(optimized_witness),
        root=_number(theta_star),
    )
    record(
        "optimized_cutoff_sound",
        optimized_cutoff > optimized_threshold,
        cutoff=_number(optimized_cutoff),
        witness_threshold=_number(optimized_threshold),
        margin=_number(optimized_cutoff - optimized_threshold),
    )

    return {
        "checks": checks,
        "intervals": intervals,
        "bound_rows": bound_rows,
        "needed": needed,
        "true_sin": true_sin,
        "theta_star": theta_star,
        "k_cert": k_cert,
        "k_sharp": k_sharp,
        "threshold": threshold,
        "sharp_threshold": sharp_threshold,
        "optimized_witness": optimized_witness,
        "optimized_cos_lower": optimized_cos_lower,
        "true_optimized_cos": true_optimized_cos,
        "optimized_cutoff": optimized_cutoff,
        "optimized_threshold": optimized_threshold,
        "verdict": all(check["passed"] for check in checks),
    }


def print_human(path: Path, data: dict[str, Any], result: dict[str, Any]) -> None:
    pi_lo, pi_hi, t0 = data["pi_lo"], data["pi_hi"], data["t0"]
    checks = {check["check_id"]: check for check in result["checks"]}

    print(f"file          {path}")
    print(f"pi bounds     ({pi_lo}, {pi_hi})   width {float(pi_hi - pi_lo):.1e}")
    print(f"witness t0    {t0}")
    print(
        "\n[1] pi bounds sound                       "
        f"{ok(checks['pi_bounds_sound']['passed'])}"
    )
    print(
        "[2] 2*t0 literal consistent               "
        f"{ok(checks['doubled_witness_consistent']['passed'])}  "
        f"{DIM}{data['two_t0']}{RESET}"
    )

    print("\n[3] interval endpoints (exact, from pi bounds):")
    for divisor, (lo, hi) in result["intervals"].items():
        print(
            f"    y/{divisor:<3} ({mp.nstr(lo, 12)}, {mp.nstr(hi, 12)})"
            f"   width {float(hi - lo):.2e}"
        )

    print("\n[4] individual bounds (slack = waste vs the true value):")
    for row in result["bound_rows"]:
        arrow = "≥" if row["direction"] == "ge" else "≤"
        print(
            f"    {row['name']:<12} {arrow} {mp.nstr(row['value'], 13):<16}"
            f" slack {float(row['slack']):.2e}   {ok(row['passed'])}"
        )

    final_bound = data["sin_final"]
    print("\n[5] final step")
    print(f"    claimed  sin({data['two_t0']}) < {final_bound}")
    print(
        f"    true                        {mp.nstr(result['true_sin'], 15)}"
        f"   {ok(checks['final_sine_bound_sound']['passed'])}"
    )
    print(
        f"    required                  < {mp.nstr(result['needed'], 15)}"
        f"   {ok(checks['final_sine_bound_sufficient']['passed'])}"
    )
    print(f"    margin                      {float(result['needed'] - final_bound):+.3e}")

    print("\n[6] result")
    print(f"    theta*        {mp.nstr(result['theta_star'], 15)}")
    print(
        "    t0 > theta*   "
        f"{ok(checks['witness_above_root']['passed'])}   "
        "(required: certificate is valid)"
    )
    print(f"    3 cos t0      {mp.nstr(result['k_cert'], 15)}")
    print(f"    3 cos theta*  {mp.nstr(result['k_sharp'], 15)}   (sharp)")
    print(f"    threshold     {mp.nstr(result['threshold'], 15)}")
    print(f"    sharp         {mp.nstr(result['sharp_threshold'], 15)}")
    print(f"    gap           {float(result['threshold'] - result['sharp_threshold']):.2e}")
    print(
        "    beats 4/pi    "
        f"{ok(checks['threshold_beats_four_over_pi']['passed'])}   "
        f"(4/pi = {mp.nstr(4 / pi, 12)})"
    )

    print("\n[7] optimized cutoff")
    print(f"    witness       {mp.nstr(result['optimized_witness'], 15)}")
    print(
        "    cos lower     "
        f"{mp.nstr(result['optimized_cos_lower'], 15)}   "
        f"{ok(checks['optimized_cos_lower_sound']['passed'])}"
    )
    print(
        "    inverse bound "
        f"{ok(checks['optimized_inverse_bound_sufficient']['passed'])}   "
        f"(margin = {float(3 * result['optimized_cos_lower'] - 1 / result['optimized_cutoff']):+.3e})"
    )
    print(
        "    witness > θ*  "
        f"{ok(checks['optimized_witness_above_root']['passed'])}"
    )
    print(f"    claimed cutoff {mp.nstr(result['optimized_cutoff'], 15)}")
    print(f"    witness cutoff {mp.nstr(result['optimized_threshold'], 15)}")
    print(
        "    cutoff valid   "
        f"{ok(checks['optimized_cutoff_sound']['passed'])}   "
        f"(margin = {float(result['optimized_cutoff'] - result['optimized_threshold']):+.3e})"
    )
    print(f"\n{'ALL CHECKS PASS' if result['verdict'] else 'SOME CHECKS FAILED'}")


def json_report(path: Path, data: dict[str, Any], result: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "file": str(path),
        "status": "passed" if result["verdict"] else "failed",
        "checks": result["checks"],
        "result": {
            "witness": _number(data["t0"]),
            "root": _number(result["theta_star"]),
            "threshold": _number(result["threshold"]),
            "sharp_threshold": _number(result["sharp_threshold"]),
            "gap": _number(result["threshold"] - result["sharp_threshold"]),
            "optimized_witness": _number(result["optimized_witness"]),
            "optimized_cos_lower": _number(result["optimized_cos_lower"]),
            "optimized_cutoff": _number(result["optimized_cutoff"]),
            "optimized_threshold": _number(result["optimized_threshold"]),
            "optimized_gap": _number(
                result["optimized_cutoff"] - result["sharp_threshold"]
            ),
        },
    }


def _print_json(payload: dict[str, Any]) -> None:
    print(json.dumps(payload, ensure_ascii=True, separators=(",", ":"), sort_keys=True))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", default="Certificate.lean", type=Path)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    try:
        data = parse(args.certificate)
        result = evaluate(data)
    except (CertificateInputError, ValueError, ArithmeticError) as exc:
        if args.as_json:
            _print_json(
                {
                    "schema_version": 1,
                    "file": str(args.certificate),
                    "status": "error",
                    "error": {"kind": "input", "message": str(exc)},
                }
            )
        else:
            print(f"input error: {exc}", file=sys.stderr)
        return 2

    if args.as_json:
        _print_json(json_report(args.certificate, data, result))
    else:
        print_human(args.certificate, data, result)
    return 0 if result["verdict"] else 1


if __name__ == "__main__":
    sys.exit(main())
