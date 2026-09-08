from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

ROOT = Path.cwd()
PROOF = ROOT / "proof"
DELIVERABLE = ROOT / "deliverable"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"{path} must contain a JSON object")
    return value


def run(command: list[str], *, cwd: Path) -> None:
    subprocess.run(command, cwd=cwd, check=True, timeout=1800)



def main() -> int:
    run([sys.executable, "verify_certificate.py"], cwd=PROOF)
    run([sys.executable, "tools/verify_report.py"], cwd=ROOT)

    proof_manifest = load_object(PROOF / "proof-manifest.json")
    if proof_manifest.get("declarations") != [
        "cmv_range_reduction",
        "cmv_type_four_range_reduction",
        "cmv_type_three_branch_contract",
    ]:
        raise ValueError("proof manifest declaration surface changed")
    report = load_object(DELIVERABLE / "verification" / "report-verification.json")
    if report.get("status") != "passed" or report.get("claim_count") != 19:
        raise ValueError("document verification receipt did not close all 19 claims")

    result = {
        "schema_version": 1,
        "status": "passed",
        "checks": [
            "proof manifest and source hash binding",
            "exact certificate",
            "citation-complete report",
        ],
        "artifacts": {
            "RangeReduction.lean": sha256(PROOF / "RangeReduction.lean"),
            "proof-manifest.json": sha256(PROOF / "proof-manifest.json"),
            "citations.json": sha256(DELIVERABLE / "citations.json"),
            "Proof.pdf": sha256(DELIVERABLE / "Proof.pdf"),
            "Portfolio.pdf": sha256(DELIVERABLE / "Portfolio.pdf"),
        },
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
