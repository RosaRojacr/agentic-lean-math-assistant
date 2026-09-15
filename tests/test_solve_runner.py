from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any

from agentic_lean_math_assistant.cli import main
from agentic_lean_math_assistant.command import CapturedCommand
from agentic_lean_math_assistant.forecast import CompletionForecast
from agentic_lean_math_assistant.proof_builder import (
    ProofPackageResult,
    ProofPackageSpec,
)
from agentic_lean_math_assistant.solve import SolveSpec
from agentic_lean_math_assistant.solve_runner import SolveRunner, solve_status

SEMANTIC_CONTRACT = {
    "schema_version": 1,
    "title": "Truth",
    "question": "Prove True.",
    "definitions": [],
    "domains": ["Propositions"],
    "quantifiers": [],
    "boundary_cases": [],
    "acceptable_outcomes": ["A Lean-verified proof of True."],
    "source_dependent_claims": [],
    "prohibited_scope_changes": ["Do not replace True with another proposition."],
    "ambiguities": [],
    "completion_description": "The retained theorem target has type True.",
}

FORMAL_CONTRACT = {
    "schema_version": 1,
    "title": "Truth",
    "lakefile": "lakefile.toml",
    "author": "Automated solver",
    "audience": "Mathematicians",
    "informal_claim": "True is provable.",
    "closing_scope": "The theorem is exactly the proposition True.",
    "roots": [
        {
            "module": "Solution.Main",
            "declaration": "target",
            "role": "primary",
            "type": "True",
            "informal_statement": "True is provable.",
        }
    ],
    "build_command": ["lake", "build"],
    "verification_commands": [["lake", "build"]],
    "allowed_axioms": [],
    "support_files": ["lean-toolchain"],
}


def test_folder_solve_reaches_verified_publication(
    tmp_path: Path, monkeypatch: Any, capsys: Any
) -> None:
    folder = tmp_path / "truth-problem"
    folder.mkdir()
    (folder / "problem.md").write_text("Prove True.\n", encoding="utf-8")
    autonomy_options: list[Any] = []

    def fake_execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        role = request["role_id"]
        output = Path(request["output"])
        output.parent.mkdir(parents=True, exist_ok=True)
        if role == "solve_semantic_contract_author":
            marker = "SEMANTIC_CONTRACT_JSON: " + json.dumps(SEMANTIC_CONTRACT)
        elif role == "solve_semantic_contract_reviewer":
            marker = 'SEMANTIC_REVIEW_JSON: {"schema_version":1,"accepted":true,"relation":"equivalent","issues":[],"reason":"faithful"}'
        elif role == "solve_formal_contract_author":
            workspace = Path(request["workspace"])
            proof = workspace / "proof"
            (proof / "Solution").mkdir(parents=True, exist_ok=True)
            (proof / "Solution" / "Main.lean").write_text(
                "theorem target : True := True.intro\n", encoding="utf-8"
            )
            (proof / "lakefile.toml").write_text(
                'name = "truth"\n[[lean_lib]]\nname = "Solution"\n',
                encoding="utf-8",
            )
            (proof / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n")
            marker = "FORMAL_CONTRACT_JSON: " + json.dumps(FORMAL_CONTRACT)
        elif role == "solve_formal_contract_reviewer":
            marker = 'FORMAL_REVIEW_JSON: {"schema_version":1,"accepted":true,"relation":"equivalent","issues":[],"reason":"equivalent"}'
        else:
            raise AssertionError(f"unexpected fake agent role: {role}")
        output.write_text(marker + "\n", encoding="utf-8")
        return 0

    class FakeAutonomyRunner:
        def __init__(self, project: Any, options: Any) -> None:
            self.project = project
            autonomy_options.append(options)

        def start(self) -> Path:
            session = self.project.runs_dir / "autonomy-runs" / "session"
            session.mkdir(parents=True, exist_ok=True)
            (session / "solve-status.json").write_text(
                json.dumps({"status": "running"}), encoding="utf-8"
            )
            return session

        def step(self, session: Path) -> dict[str, object]:
            state = {"status": "solved", "result": "verifier accepted target"}
            (session / "solve-status.json").write_text(
                json.dumps(state), encoding="utf-8"
            )
            return state

    def fake_autonomy_status(session: Path) -> dict[str, object]:
        return json.loads((session / "solve-status.json").read_text(encoding="utf-8"))

    def fake_build(manifest: Path, **kwargs: object) -> ProofPackageResult:
        package = folder / "result" / "proof-package"
        package.mkdir(parents=True, exist_ok=True)
        return ProofPackageResult("verified", package, 4, ())

    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.execute_agent_request", fake_execute
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.run_captured_command",
        lambda *args, **kwargs: CapturedCommand(
            0, "", "", False, False, None, "", "", {}
        ),
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.AutonomyRunner", FakeAutonomyRunner
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.autonomy_status",
        fake_autonomy_status,
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.discover_lean_declarations",
        lambda *args, **kwargs: [
            {
                "declaration": "target",
                "kind": "theorem",
                "module": "Solution.Main",
                "source": "Solution/Main.lean",
                "line": 1,
                "type": "True",
                "axioms": [],
            }
        ],
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.build_proof_package", fake_build
    )

    result = SolveRunner(
        SolveSpec.load(folder, runtime_limit="1h", headless=True),
        omp=sys.executable,
    ).run()

    assert result.status == "complete"
    assert result.mathematical_status == "verified"
    assert result.publication_status == "verified"
    assert result.proof_package == folder / "result" / "proof-package"
    assert autonomy_options[0].direct_agents is True
    assert (
        json.loads((folder / ".alma" / "state.json").read_text(encoding="utf-8"))[
            "runtime"
        ]["active_since"]
        is None
    )
    status = solve_status(folder)
    assert len(status["checkpoints"]) == 1
    semantic_lock = json.loads(
        (folder / ".alma" / "contracts" / "semantic-contract.lock.json").read_text(
            encoding="utf-8"
        )
    )
    assert semantic_lock["contract"] == SEMANTIC_CONTRACT
    package_spec = ProofPackageSpec.load(
        folder / ".alma" / "generated" / "proof-package.toml"
    )
    assert package_spec.workspace == folder / ".alma" / "publication-proof"
    assert package_spec.roots[0].declaration == "target"
    assert (folder / "result" / "status.json").is_file()
    assert main(["solve-status", str(folder)]) == 0
    assert '"status": "complete"' in capsys.readouterr().out
    assert (
        main(["solve-resume", str(folder), "--omp", sys.executable, "--headless"]) == 0
    )
    assert "solve status: complete" in capsys.readouterr().out
    assert (
        json.loads((folder / ".alma" / "state.json").read_text(encoding="utf-8"))[
            "runtime"
        ]["active_since"]
        is None
    )
    assert main(["solve-stop", str(folder)]) == 0
    assert "solve stop requested" in capsys.readouterr().out
    assert (folder / ".alma" / "STOP").is_file()


def test_resume_retries_verified_publication_failure(tmp_path: Path) -> None:
    folder = tmp_path / "publication-retry"
    folder.mkdir()
    (folder / "problem.md").write_text("Prove True.\n", encoding="utf-8")
    initial = SolveRunner(SolveSpec.load(folder, runtime_limit="1h"))
    initial._prepare_state_root()
    initial._initialize_or_resume()
    failed = initial._state()
    failed["status"] = "publication_failed"
    failed["mathematical_status"] = "verified"
    failed["publication_status"] = "failed"
    failed["checkpoints"] = [{"path": str(folder / ".alma" / "checkpoint")}]
    failed["error"] = "missing publication models"
    failed["runtime"] = {"active_seconds": 0, "active_since": None, "model_calls": 0}
    initial._save(failed, "test:publication-failed")

    resumed = SolveRunner(
        SolveSpec.load(
            folder,
            runtime_limit="1h",
            proof_author_model="provider/author",
            proof_reviewer_model="provider/reviewer",
        )
    )
    resumed._prepare_state_root()
    resumed._initialize_or_resume()

    state = resumed._state()
    assert state["status"] == "publishing"
    assert state["publication_status"] == "pending"
    assert state["error"] is None
    assert resumed.spec.models.proof_author == "provider/author"
    assert resumed.spec.models.proof_reviewer == "provider/reviewer"


def test_resume_retries_failed_solve_from_retained_progress(tmp_path: Path) -> None:
    folder = tmp_path / "solve-retry"
    folder.mkdir()
    (folder / "problem.md").write_text("Prove True.\n", encoding="utf-8")
    initial = SolveRunner(SolveSpec.load(folder, runtime_limit="1h"))
    initial._prepare_state_root()
    initial._initialize_or_resume()
    failed = initial._state()
    failed["status"] = "failed"
    failed["error"] = "agent resource exhausted"
    failed["runtime"] = {"active_seconds": 5, "active_since": None, "model_calls": 1}
    initial._save(failed, "test:solve-failed")

    resumed = SolveRunner(SolveSpec.load(folder, runtime_limit="1h"))
    resumed._prepare_state_root()
    resumed._initialize_or_resume()

    state = resumed._state()
    assert state["status"] == "contracting"
    assert state["error"] is None
    assert state["runtime"]["active_since"] is not None


def test_contract_rejection_pauses_after_five_attempts(
    tmp_path: Path, monkeypatch: Any
) -> None:
    folder = tmp_path / "ambiguous-problem"
    folder.mkdir()
    (folder / "problem.md").write_text(
        "Determine the unspecified value.\n", encoding="utf-8"
    )

    def fake_execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        output = Path(request["output"])
        role = request["role_id"]
        if role == "solve_semantic_contract_author":
            marker = "SEMANTIC_CONTRACT_JSON: " + json.dumps(SEMANTIC_CONTRACT)
        elif role == "solve_semantic_contract_reviewer":
            marker = (
                'SEMANTIC_REVIEW_JSON: {"schema_version":1,"accepted":false,'
                '"relation":"ambiguous","issues":["The input does not identify a value."],'
                '"reason":"The question remains underdetermined."}'
            )
        else:
            raise AssertionError(f"unexpected fake agent role: {role}")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(marker + "\n", encoding="utf-8")
        return 0

    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_runner.execute_agent_request", fake_execute
    )
    result = SolveRunner(
        SolveSpec.load(folder, runtime_limit="1h", max_model_calls=20),
        omp=sys.executable,
    ).run()

    assert result.status == "needs_input"
    assert result.error is not None and "five attempts" in result.error
    reviews = tuple((folder / ".alma" / "contracts").glob("semantic-review-*.json"))
    assert len(reviews) == 5
    state = json.loads((folder / ".alma" / "state.json").read_text(encoding="utf-8"))
    assert state["runtime"]["active_since"] is None


def test_prediction_limit_requires_configured_independent_confirmations(
    tmp_path: Path, monkeypatch: Any
) -> None:
    folder = tmp_path / "forecast-problem"
    folder.mkdir()
    (folder / "problem.md").write_text("Prove True.\n", encoding="utf-8")
    (folder / "solve.toml").write_text(
        """
[resources]
runtime_limit = "1h"

[forecast]
predicted_runtime_limit = "100s"
initial_after = "1s"
interval = "2h"
minimum_interval = "30m"
breach_confirmations = 3
""".strip()
        + "\n",
        encoding="utf-8",
    )
    runner = SolveRunner(SolveSpec.load(folder), omp=sys.executable)
    runner._prepare_state_root()
    runner._initialize_or_resume()
    state = runner._state()
    state["runtime"] = {
        "active_seconds": 10,
        "active_since": None,
        "model_calls": 0,
    }
    runner._save(state, "test:forecast-due")
    forecast = CompletionForecast.parse(
        {
            "schema_version": 1,
            "assessment": "stalled",
            "completion_probability": 0.1,
            "current_result_publishable": True,
            "strongest_verified_result_summary": "A verified lemma.",
            "strongest_verified_roots": ["Result.lemma"],
            "next_publishable_runtime_seconds": {
                "p50": 150,
                "p80": 200,
                "p95": 300,
            },
            "complete_solution_runtime_seconds": {
                "p50": 500,
                "p80": 800,
                "p95": 1200,
            },
            "confidence": "high",
            "evidence_quality": "sufficient",
            "verified_progress": ["Result.lemma"],
            "critical_path": ["close the main theorem"],
            "blocking_risks": ["missing invariant"],
            "reason": "Both remaining paths exceed the configured total.",
            "recommended_review_after_seconds": 1800,
        }
    )
    calls: list[int] = []
    checkpoints: list[str] = []
    terminations: list[str] = []

    def fake_forecast(
        current: dict[str, Any], *, allow_after_budget: bool = False
    ) -> tuple[CompletionForecast, Path]:
        index = len(calls) + 1
        calls.append(index)
        return forecast, folder / ".alma" / f"forecast-{index}.json"

    monkeypatch.setattr(runner, "_run_forecast", fake_forecast)
    monkeypatch.setattr(
        runner,
        "_create_checkpoint",
        lambda state, value, path, complete: checkpoints.append(str(path)),
    )
    monkeypatch.setattr(
        runner,
        "_terminate_solve",
        lambda state, status, error: terminations.append(status),
    )

    runner._forecast_if_due(runner._state())

    assert calls == [1, 2, 3]
    assert len(checkpoints) == 3
    assert terminations == ["prediction_limit_reached"]


def test_approved_inconclusive_result_advances_to_publication(
    tmp_path: Path, monkeypatch: Any
) -> None:
    folder = tmp_path / "approved-partial"
    folder.mkdir()
    (folder / "problem.md").write_text("Prove the open claim.\n", encoding="utf-8")
    runner = SolveRunner(
        SolveSpec.load(
            folder,
            runtime_limit="1h",
            publish_inconclusive=True,
            headless=True,
        ),
        omp=sys.executable,
    )
    runner._prepare_state_root()
    runner._initialize_or_resume()
    candidate = {
        "summary": "A verified partial theorem.",
        "roots": ["Partial.result"],
        "forecast": str(folder / ".alma" / "forecast.json"),
    }
    monkeypatch.setattr(runner, "_latest_verified_candidate", lambda state: candidate)

    def fake_snapshot(
        state: dict[str, Any],
        *,
        roots: tuple[str, ...],
        summary: str,
        complete: bool,
        evidence: dict[str, object],
    ) -> None:
        current = runner._state()
        current["checkpoints"] = [
            {
                "index": 1,
                "digest": "abc",
                "path": str(folder / ".alma" / "checkpoints" / "checkpoint-0001"),
                "summary": summary,
                "complete": complete,
            }
        ]
        runner._save(current, "test:partial-checkpoint")

    monkeypatch.setattr(runner, "_snapshot_checkpoint", fake_snapshot)
    runner._terminate_solve(runner._state(), "resource_limit_reached", "limit")

    state = runner._state()
    assert state["status"] == "publishing"
    assert state["publication_status"] == "pending"
    assert state["pending_decision"] is None
    assert state["checkpoints"][0]["summary"] == "A verified partial theorem."
