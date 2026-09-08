from __future__ import annotations

import json
import stat
import time
from pathlib import Path

from agentic_lean_math_assistant.cli import main
from agentic_lean_math_assistant.lean import run_proof_gate


def _executable(path: Path, source: str) -> Path:
    path.write_text(source, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


def _project(tmp_path: Path) -> tuple[Path, Path, Path]:
    project = tmp_path / "proof"
    project.mkdir()
    candidate = project / "Candidate.lean"
    candidate.write_text(
        "namespace Candidate\ntheorem proof : True := by trivial\nend Candidate\n",
        encoding="utf-8",
    )
    contract = tmp_path / "contract.lean"
    contract.write_text(
        "import Candidate\n"
        "theorem Trusted.target : True := Candidate.proof\n"
        "#print axioms Trusted.target\n",
        encoding="utf-8",
    )
    return project, candidate, contract


def test_candidate_cli_retains_typed_consumer_and_axiom_evidence(
    tmp_path: Path,
) -> None:
    project, candidate, contract = _project(tmp_path)
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import json, pathlib, sys
if sys.argv[1:] == ["build"]: pass
elif sys.argv[1:] == ["env", "which", "lean"]: print(pathlib.Path(sys.argv[0]).resolve())
elif "--run" in sys.argv:
    print(json.dumps({"declaration": "Trusted.target", "axioms": []}))
else: pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"olean")
""",
    )
    receipt = tmp_path / "receipt.json"

    exit_code = main(
        [
            "proof-attempt",
            "--project",
            str(project),
            "--candidate",
            str(candidate),
            "--contract",
            str(contract),
            "--trusted-declaration",
            "Trusted.target",
            "--lake",
            str(lake),
            "--timeout",
            "10",
            "--receipt",
            str(receipt),
        ]
    )

    value = json.loads(receipt.read_text(encoding="utf-8"))
    assert exit_code == 0
    assert value["status"] == "passed"
    assert value["inputs_unchanged"] is True
    assert value["gate"]["axiom_reports"] == [
        {"declaration": "Trusted.target", "axioms": []}
    ]


def test_proof_gate_timeout_is_one_aggregate_stage_deadline(tmp_path: Path) -> None:
    project, _candidate, contract = _project(tmp_path)
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import pathlib, sys, time
if sys.argv[1:] == ["build"]: time.sleep(0.25)
elif sys.argv[1:] == ["env", "which", "lean"]:
    time.sleep(2)
    print(pathlib.Path(sys.argv[0]).resolve())
""",
    )
    started = time.monotonic()

    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=(),
        lake=str(lake),
        timeout=0.6,
    )

    elapsed = time.monotonic() - started
    assert result.status == "failed"
    assert len(result.command_receipts) == 2
    assert result.command_receipts[1].exit_code == 124
    assert result.command_receipts[1].duration_seconds < 0.5
    assert elapsed < 1.0
    assert any("timed out" in error for error in result.errors)


def test_candidate_cli_rejects_native_decide(tmp_path: Path) -> None:
    project, candidate, contract = _project(tmp_path)
    candidate.write_text(
        "namespace Candidate\ntheorem proof : True := by native_decide\nend Candidate\n",
        encoding="utf-8",
    )
    marker = tmp_path / "lake-ran"
    lake = _executable(
        tmp_path / "lake",
        f"#!/usr/bin/env python3\nimport pathlib\npathlib.Path({str(marker)!r}).touch()\n",
    )
    receipt = tmp_path / "receipt.json"

    exit_code = main(
        [
            "proof-attempt",
            "--project",
            str(project),
            "--candidate",
            str(candidate),
            "--contract",
            str(contract),
            "--trusted-declaration",
            "Trusted.target",
            "--lake",
            str(lake),
            "--receipt",
            str(receipt),
        ]
    )

    value = json.loads(receipt.read_text(encoding="utf-8"))
    assert exit_code == 1
    assert value["status"] == "failed"
    assert any("native_decide" in issue for issue in value["gate"]["source_issues"])
