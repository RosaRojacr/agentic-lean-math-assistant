#!/usr/bin/env python3
"""Run the accepted certificate and four fail-closed mutation classes."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import platform
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def payload_hash(boxes: list[dict[str, Any]]) -> str:
    payload = json.dumps(boxes, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def apply_mutation(data: dict[str, Any], fixture: dict[str, Any]) -> None:
    operation = fixture["operation"]
    first = data["boxes"][0]
    if operation == "add_first_box_gap_sign":
        first["gap_sign"] = -1
    elif operation == "replace_first_h4_root":
        first["h4_root"] = fixture["value"]
    elif operation == "replace_first_lambda_lower":
        first["lambda"][0] = fixture["value"]
    elif operation == "delete_first_h3_root":
        del first["h3_root"]
    else:
        raise ValueError(f"unknown mutation operation: {operation}")
    # Rehash so each mutation reaches its semantic checker guard rather than
    # being rejected only by the generic payload-integrity guard.
    data["payload_sha256"] = payload_hash(data["boxes"])


def invoke(checker: Path, certificate: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(checker), str(certificate)],
        text=True,
        capture_output=True,
        check=False,
        timeout=1800,
    )


def main() -> int:
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=here / "compact_certificate.json")
    parser.add_argument("--fixtures", type=Path, default=here / "mutation_fixtures.json")
    parser.add_argument("--receipt", type=Path, default=here / "mutation_receipt.json")
    parser.add_argument("--skip-baseline", action="store_true")
    args = parser.parse_args()

    checker = here / "check_compact_certificate.py"
    data = json.loads(args.certificate.read_text(encoding="utf-8"))
    fixtures = json.loads(args.fixtures.read_text(encoding="utf-8"))
    if set(fixtures) != {"schema", "mutations"}:
        raise SystemExit("fixture root fields rejected")
    if fixtures["schema"] != "cmv-compact-rational-mutations-v1":
        raise SystemExit("fixture schema rejected")

    baseline: dict[str, Any]
    if args.skip_baseline:
        baseline = {"status": "SKIPPED"}
    else:
        result = invoke(checker, args.certificate)
        if result.returncode != 0 or '"status":"PASS"' not in result.stdout:
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
            return 1
        baseline = {
            "status": "PASS",
            "returncode": result.returncode,
            "stdout_sha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
        }

    rows: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="cmv-compact-mutations-") as directory:
        root = Path(directory)
        for index, fixture in enumerate(fixtures["mutations"]):
            mutated = copy.deepcopy(data)
            apply_mutation(mutated, fixture)
            path = root / f"mutation-{index}.json"
            path.write_text(json.dumps(mutated, sort_keys=True), encoding="utf-8")
            result = invoke(checker, path)
            expected = fixture["expected_error"]
            rejected = result.returncode != 0 and expected in result.stderr
            rows.append({
                "id": fixture["id"],
                "kind": fixture["kind"],
                "status": "REJECTED" if rejected else "UNEXPECTED",
                "returncode": result.returncode,
                "expected_error": expected,
                "stderr": result.stderr.strip(),
            })
            if not rejected:
                print(json.dumps(rows[-1], sort_keys=True), file=sys.stderr)
                return 1

    receipt = {
        "status": "PASS",
        "python": platform.python_version(),
        "baseline": baseline,
        "mutations_rejected": len(rows),
        "mutation_total": len(rows),
        "results": rows,
        "certificate_sha256": sha256(args.certificate),
        "checker_sha256": sha256(checker),
        "fixtures_sha256": sha256(args.fixtures),
        "runner_sha256": sha256(Path(__file__)),
    }
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
