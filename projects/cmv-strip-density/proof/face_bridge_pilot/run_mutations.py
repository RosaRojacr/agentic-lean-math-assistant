#!/usr/bin/env python3
"""Exercise semantic bridge-certificate mutations through the real checker."""
from __future__ import annotations

import hashlib
import json
import platform
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
CERT = ROOT / "bridge_certificate.json"
CHECKER = ROOT / "check_bridge.py"
FIXTURES = ROOT / "mutation_fixtures.json"


def semantic_hash(raw: dict) -> str:
    payload = {key: value for key, value in raw.items() if key != "payload_sha256"}
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()
    return hashlib.sha256(encoded).hexdigest()


def run(path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["python3", str(CHECKER), str(path)], text=True, capture_output=True, check=False)


def main() -> None:
    baseline = run(CERT)
    if baseline.returncode != 0 or json.loads(baseline.stdout).get("status") != "PASS":
        raise SystemExit("baseline checker failed")
    fixtures = json.loads(FIXTURES.read_text())
    if set(fixtures) != {"schema", "mutations"} or fixtures["schema"] != "cmv-opposite-face-bridge-mutations-v1":
        raise SystemExit("mutation fixture schema failed")
    results = []
    with tempfile.TemporaryDirectory() as directory:
        for mutation in fixtures["mutations"]:
            if set(mutation) != {"id", "brick", "field", "index", "replacement", "expected_code"}:
                raise SystemExit(f"mutation fields failed: {mutation}")
            raw = json.loads(CERT.read_text())
            raw["bricks"][mutation["brick"]][mutation["field"]][mutation["index"]] = mutation["replacement"]
            raw["payload_sha256"] = semantic_hash(raw)
            path = Path(directory) / f"{mutation['id']}.json"
            path.write_text(json.dumps(raw, indent=2, sort_keys=True) + "\n")
            process = run(path)
            try:
                receipt = json.loads(process.stdout)
                actual = receipt["failure"]["code"]
            except Exception as exc:
                raise SystemExit(f"{mutation['id']}: non-JSON checker failure: {process.stdout} {process.stderr}") from exc
            accepted = process.returncode != 0 and receipt.get("status") == "FAIL" and actual == mutation["expected_code"]
            if not accepted:
                raise SystemExit(f"{mutation['id']}: expected {mutation['expected_code']}, got rc={process.returncode}, code={actual}")
            results.append({
                "id": mutation["id"],
                "expected_code": mutation["expected_code"],
                "actual_code": actual,
                "first_failure": receipt["failure"],
                "rejected": True,
            })
    output = {
        "status": "PASS",
        "schema": "cmv-opposite-face-bridge-mutation-receipt-v1",
        "rejected": len(results),
        "total": len(fixtures["mutations"]),
        "results": results,
        "python": platform.python_version(),
        "certificate_sha256": hashlib.sha256(CERT.read_bytes()).hexdigest(),
        "checker_sha256": hashlib.sha256(CHECKER.read_bytes()).hexdigest(),
        "fixtures_sha256": hashlib.sha256(FIXTURES.read_bytes()).hexdigest(),
        "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    text = json.dumps(output, indent=2, sort_keys=True) + "\n"
    (ROOT / "mutation_receipt.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
