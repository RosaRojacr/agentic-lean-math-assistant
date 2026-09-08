from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / "projects" / "cmv-strip-density" / "proof"
CHECKER = PROOF / "verify_certificate.py"
FULL_DOMAIN_CHECKER = PROOF / "verify_full_domain.py"
CERTIFICATE = PROOF / "Certificate.lean"


def test_checker_covers_published_optimized_cutoff() -> None:
    completed = subprocess.run(
        [sys.executable, str(CHECKER), str(CERTIFICATE), "--json"],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )

    assert completed.returncode == 0, completed.stderr
    report = json.loads(completed.stdout)
    checks = {check["check_id"]: check for check in report["checks"]}
    assert checks["optimized_cos_lower_sound"]["passed"] is True
    assert checks["optimized_inverse_bound_sufficient"]["passed"] is True
    assert checks["optimized_witness_above_root"]["passed"] is True
    assert checks["optimized_cutoff_sound"]["passed"] is True
    assert report["result"]["optimized_cutoff"] == "1.2581840884"


def test_full_domain_scalar_certificate_closes_every_density_regime() -> None:
    completed = subprocess.run(
        [sys.executable, str(FULL_DOMAIN_CHECKER)],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )

    assert completed.returncode == 0, completed.stderr
    assert "EXACT low_t=[0,13/32]" in completed.stdout
    assert "EXACT compact_lambda=[17/16,3/2]" in completed.stdout
    assert "EXACT large_lambda_tail=" in completed.stdout
    assert "FULL_DOMAIN_LEDGER_RESULT=PASS" in completed.stdout


def test_checker_rejects_certificate_without_optimized_claim(
    tmp_path: Path,
) -> None:
    malformed = tmp_path / "Certificate.lean"
    malformed.write_text(
        CERTIFICATE.read_text(encoding="utf-8").replace(
            "opt_cos_witness_lower", "removed_optimized_cos_bound"
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        [sys.executable, str(CHECKER), str(malformed), "--json"],
        check=False,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )

    assert completed.returncode == 2
    report = json.loads(completed.stdout)
    assert report["status"] == "error"
    assert "opt_cos_witness_lower" in report["error"]["message"]
