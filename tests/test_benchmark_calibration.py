from __future__ import annotations

import io
import json
import subprocess
import sys
from dataclasses import replace
from pathlib import Path

from agentic_lean_math_assistant.benchmark import BenchmarkSuite
from agentic_lean_math_assistant.project import ProjectSpec
from agentic_lean_math_assistant.regime import RegimeOptions, RegimeRunner

ROOT = Path(__file__).resolve().parents[1]
CALIBRATION = ROOT / "benchmarks" / "autonomy-calibration"


def test_calibration_ground_truth_certificates() -> None:
    completed = subprocess.run(
        [sys.executable, str(CALIBRATION / "validation" / "validate_cases.py")],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=60,
    )

    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert "validated 12 blind cases" in completed.stdout


def test_calibration_expected_outcomes_are_outside_agent_snapshots(
    tmp_path: Path,
) -> None:
    suite = BenchmarkSuite.load(CALIBRATION / "benchmark.toml")
    expected = json.loads(
        (CALIBRATION / "validation" / "expected-outcomes.json").read_text(
            encoding="utf-8"
        )
    )
    certificates = tuple(item["certificate"] for item in expected["cases"])

    assert len(suite.cases) == 12
    for case in suite.cases:
        project = replace(
            ProjectSpec.load(case.project_manifest),
            runs_dir=tmp_path / case.case_id,
        )
        runner = RegimeRunner(
            project,
            RegimeOptions(
                missing_source_policy=case.missing_source_policy,
                focus=False,
                output=io.StringIO(),
            ),
        )
        runner._initialize_run()
        assert runner.pre_workspace is not None
        snapshot = runner.pre_workspace
        assert {path.name for path in snapshot.iterdir()} == {
            "knowledge",
            "problem.md",
            "project-inputs",
            "references",
        }
        assert not (snapshot / "benchmark.toml").exists()
        assert not (snapshot / "validation").exists()
        visible_text = "\n".join(
            path.read_text(encoding="utf-8")
            for path in snapshot.rglob("*")
            if path.is_file()
        )
        assert all(certificate not in visible_text for certificate in certificates)
