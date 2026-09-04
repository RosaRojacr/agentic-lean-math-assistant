from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import ClassVar

import pytest

from agentic_lean_math_assistant.autonomy import (
    AutonomyError,
    AutonomyRunner,
    AutonomyRuntimeOptions,
    InterCampaignAnalysis,
    SuccessValidation,
)
from agentic_lean_math_assistant.command import CapturedCommand
from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.models import CampaignOutcome
from agentic_lean_math_assistant.project import ProjectSpec
from agentic_lean_math_assistant.regime import RegimeOptions


def write_autonomy_project(tmp_path: Path) -> Path:
    project = tmp_path / "project"
    project.mkdir()
    (project / "problem.md").write_text(
        "# Problem\n\nProve the exact target.\n", encoding="utf-8"
    )
    (project / "references").mkdir()
    (project / "knowledge").mkdir()
    proof = project / "proof"
    proof.mkdir()
    (proof / "seed.txt").write_text("retained seed\n", encoding="utf-8")
    manifest = project / "project.toml"
    manifest.write_text(
        """schema_version = 1

[project]
id = "autonomy-fixture"
title = "Autonomy Fixture"
problem = "problem.md"
references = "references"
knowledge = "knowledge"
runs = "runs"

[regime]
omp = "omp"
planner_model = "openai-codex/gpt-5.6-sol"
execution_model = "openai-codex/gpt-5.6-luna"
analysis_model = "openai-codex/gpt-5.6-terra"
invention_model = "openai-codex/gpt-5.6-sol"
audit_model = "openai-codex/gpt-5.6-terra"
strategy_reflection_model = "openai-codex/gpt-6-astra"
targeted_task_model = "openai-codex/gpt-6-astra"
max_tasks = 4
max_parallel = 2
max_restarts = 1
default_agent_time = 60
allowed_tools = ["read", "write"]
pilot_agent_seconds = 60
research_agent_seconds = 60
formalization_agent_seconds = 60
max_attempts_total = 8
max_invention_tasks = 1
max_targeted_tasks = 1
execution_thinking = "medium"
analysis_thinking = "high"
invention_thinking = "xhigh"
audit_thinking = "xhigh"

[[compute_profiles]]
id = "fixture-profile"
omp = "fixture-omp"
max_parallel = 1
max_restarts = 0
analysis_thinking = "medium"

[autonomy]
enabled = true
approval_timeout_minutes = 0
afk_autonomy = true
max_campaigns = 3
max_elapsed_minutes = 60
max_consecutive_failures = 2
analysis_agent_seconds = 60
compute_profile = "fixture-profile"

[autonomy.success]
workspace = "proof"
build_command = ["lake", "build"]
allowed_axioms = ["propext", "Quot.sound", "Classical.choice"]
verification_commands = [["python", "verify.py"]]
required_artifacts = ["CMVConjecture.lean"]

[[autonomy.success.theorems]]
module = "CMVConjecture"
declaration = "cmv_conjecture_3_12"
type = "True"

[[autonomy.success.theorems]]
module = "Auxiliary"
declaration = "auxiliary_contract"
type = "1 = 1"

[[inputs]]
path = "proof"
target = "proof"
""",
        encoding="utf-8",
    )
    return manifest


def optimizer_output(strategy: str = "repair-success-validation") -> dict[str, object]:
    return {
        "schema_version": 1,
        "summary": "The proof claim needs one contract repair.",
        "progress": ["The campaign retained a candidate proof."],
        "failed_approaches": [],
        "remaining_obligations": ["Pass the exact theorem contract."],
        "evidence_gaps": ["The named theorem has not passed the axiom audit."],
        "compute_assessment": ["One focused campaign is sufficient."],
        "action": "continue",
        "recommended_strategy": strategy,
        "rationale": "Repair the formal declaration without weakening its statement.",
        "campaign_directive": "Create and audit the exact required theorem.",
        "contract_preserved": True,
    }


def solved_outcome() -> dict[str, object]:
    value: dict[str, object] = {
        "schema_version": 2,
        "status": "solved",
        "summary": "The campaign claims the fixture is solved.",
        "evidence": [],
        "limitations": [],
        "obligation_dispositions": [],
        "knowledge_promotions": [],
        "strategies": [],
    }
    CampaignOutcome.parse(value)
    return value


def test_project_parses_success_contract_and_overlays_compute_profile(
    tmp_path: Path,
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))

    assert project.autonomy.success is not None
    assert [item.declaration for item in project.autonomy.success.theorems] == [
        "cmv_conjecture_3_12",
        "auxiliary_contract",
    ]
    assert project.autonomy.max_elapsed_minutes == 60
    assert project.model_for("execution") == "openai-codex/gpt-5.6-luna"
    assert project.model_for("analysis") == "openai-codex/gpt-5.6-terra"
    assert project.model_for("invention") == "openai-codex/gpt-5.6-sol"
    assert project.model_for("audit") == "openai-codex/gpt-5.6-terra"
    assert project.strategy_reflection_model == "openai-codex/gpt-6-astra"
    assert project.targeted_task_model == "openai-codex/gpt-6-astra"
    assert project.max_targeted_tasks == 1
    profiled = project.with_compute_profile("fixture-profile")
    assert profiled.omp == "fixture-omp"
    assert profiled.max_parallel == 1
    assert profiled.max_restarts == 0
    assert profiled.analysis_thinking == "medium"
    assert profiled.audit_thinking == "xhigh"
    assert profiled.model_for("analysis") == "openai-codex/gpt-5.6-terra"
    assert profiled.max_targeted_tasks == 1

    with pytest.raises(ConfigurationError, match="unknown compute profile"):
        project.with_compute_profile("missing")


def test_success_contract_rejects_duplicate_theorem_declarations(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    text = manifest.read_text(encoding="utf-8").replace(
        'module = "Auxiliary"\ndeclaration = "auxiliary_contract"',
        'module = "CMVConjecture"\ndeclaration = "cmv_conjecture_3_12"',
    )
    manifest.write_text(text, encoding="utf-8")

    with pytest.raises(ConfigurationError, match="must name unique declarations"):
        ProjectSpec.load(manifest)


def test_optimizer_rejects_success_contract_weakening() -> None:
    value = optimizer_output()
    value["contract_preserved"] = False

    with pytest.raises(ConfigurationError, match="attempted to change"):
        InterCampaignAnalysis.parse(value)


def test_success_validation_checks_named_theorem_and_axioms(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    runner = AutonomyRunner(
        project,
        AutonomyRuntimeOptions(lake="fixture-lake", approval_timeout_minutes=0),
    )
    runner.session_dir = tmp_path / "session"
    campaign = tmp_path / "campaign"
    proof = campaign / "workspace" / "proof"
    proof.mkdir(parents=True)
    (proof / "CMVConjecture.lean").write_text(
        "theorem cmv_conjecture_3_12 : True := by trivial\n", encoding="utf-8"
    )
    observed: list[tuple[str, ...]] = []

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autonomy.verify_evidence_index", lambda _run: ()
    )

    def captured(argv: tuple[str, ...], **_kwargs: object) -> CapturedCommand:
        observed.append(argv)
        stdout = (
            "'cmv_conjecture_3_12' depends on axioms: "
            "[propext, Quot.sound, Classical.choice]\n"
            "'auxiliary_contract' does not depend on any axioms\n"
            if "lean" in argv
            else "ok\n"
        )
        return CapturedCommand(
            exit_code=0,
            stdout=stdout,
            stderr="",
            stdout_truncated=False,
            stderr_truncated=False,
            error=None,
            stdout_sha256="stdout",
            stderr_sha256="stderr",
            sandbox={},
        )

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autonomy.run_captured_command", captured
    )

    result = runner._validate_success(campaign, 1)

    assert result.passed is True
    assert observed[0] == ("fixture-lake", "build")
    assert observed[1][:3] == ("fixture-lake", "env", "lean")
    contract_check = Path(observed[1][3]).read_text(encoding="utf-8")
    assert contract_check == (
        "import CMVConjecture\n"
        "import Auxiliary\n"
        "\n"
        "#check cmv_conjecture_3_12\n"
        "example : True := cmv_conjecture_3_12\n"
        "#print axioms cmv_conjecture_3_12\n"
        "\n"
        "#check auxiliary_contract\n"
        "example : 1 = 1 := auxiliary_contract\n"
        "#print axioms auxiliary_contract\n"
    )
    assert observed[2] == ("python", "verify.py")


def test_axiom_audit_requires_one_report_per_theorem(tmp_path: Path) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    success = project.autonomy.success
    assert success is not None

    failures = AutonomyRunner._validate_axiom_output(
        "'cmv_conjecture_3_12' does not depend on any axioms\n",
        success,
    )

    assert failures == ["axiom audit report count differs: expected=2, observed=1"]


def test_elapsed_budget_stops_before_starting_another_campaign(
    tmp_path: Path,
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    runner = AutonomyRunner(project, AutonomyRuntimeOptions())
    runner.session_dir = runner._initialize_session()
    state = runner._state()
    state["created_at"] = "2000-01-01T00:00:00Z"

    runner._execute_or_resume_round(state)

    retained = runner._state()
    assert retained["status"] == "budget_exhausted"
    assert retained["rounds"] == []
    assert retained["error"] == "maximum autonomous wall time reached without proof"


@pytest.mark.parametrize(
    (("status", "expected")),
    [
        ("research_gate", True),
        ("research", True),
        ("planning", True),
        ("orchestration_planning", False),
        ("awaiting_sources", True),
        ("executing", True),
    ],
)
def test_only_supported_regime_checkpoints_are_resumed(
    tmp_path: Path, status: str, expected: bool
) -> None:
    run = tmp_path / status
    pre = run / "pre-campaign"
    pre.mkdir(parents=True)
    (pre / "state.json").write_text(
        json.dumps({"schema_version": 1, "status": status}), encoding="utf-8"
    )

    assert AutonomyRunner._regime_run_resumable(run) is expected


def test_optimizer_failure_checkpoints_and_explicit_resume_recovers(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    runner = AutonomyRunner(project, AutonomyRuntimeOptions())
    runner.session_dir = runner._initialize_session()
    state = runner._state()
    active = {
        "index": 1,
        "status": "running",
        "campaign_run": None,
        "campaign_outcome": None,
        "campaign_error": "transport failed",
        "analysis": None,
        "analysis_error": None,
        "decision": None,
        "success_validation": None,
        "started_at": state["created_at"],
        "completed_at": None,
    }
    state["rounds"] = [active]
    state["current_round"] = 1
    state["status"] = "campaign_running"
    runner._save_state(state, "test:campaign-failed")
    attempts = 0

    def fail_optimizer(*_args: object, **_kwargs: object) -> InterCampaignAnalysis:
        nonlocal attempts
        attempts += 1
        raise AutonomyError("optimizer transport failed")

    monkeypatch.setattr(runner, "_run_analysis", fail_optimizer)
    runner._prepare_analysis(
        state,
        active,
        None,
        outcome=None,
        validation=None,
        synthetic_strategy="recover-campaign-failure",
    )

    checkpoint = runner._state()
    assert attempts == 2
    assert checkpoint["status"] == "checkpoint"
    assert checkpoint["checkpoint_kind"] == "optimizer"
    assert "attempt 2: optimizer transport failed" in checkpoint["error"]

    session = runner.session_dir
    assert session is not None
    monkeypatch.setattr(runner, "_drive", lambda: session)
    assert runner.resume(session) == session
    resumed = runner._state()
    assert resumed["status"] == "analysis_retry"
    assert resumed["checkpoint_kind"] is None
    assert resumed["rounds"][0]["status"] == "analysis_retry"

    recovered = optimizer_output("recover-campaign-failure")
    recovered["action"] = "checkpoint"
    monkeypatch.setattr(
        runner,
        "_run_analysis",
        lambda *_args, **_kwargs: InterCampaignAnalysis.parse(recovered),
    )
    runner._retry_analysis(resumed)
    retried = runner._state()
    assert retried["status"] == "checkpoint"
    assert retried["checkpoint_kind"] == "optimizer"


def test_autonomous_loop_retains_analysis_and_uses_afk_successor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))

    class FakeRegimeRunner:
        calls = 0
        directives: ClassVar[list[Path | None]] = []
        overrides: ClassVar[list[tuple[tuple[str, Path], ...]]] = []

        def __init__(self, selected: ProjectSpec, options: RegimeOptions) -> None:
            self.project = selected
            self.options = options
            self.run_dir: Path | None = None
            FakeRegimeRunner.directives.append(options.campaign_directive)
            FakeRegimeRunner.overrides.append(options.input_overrides)

        def run(self) -> Path:
            FakeRegimeRunner.calls += 1
            run = self.project.runs_dir / f"fake-{FakeRegimeRunner.calls:02d}"
            source = dict(self.options.input_overrides).get(
                "proof", self.project.inputs[0].source
            )
            shutil.copytree(source, run / "workspace" / "proof")
            (run / "state.json").write_text(
                json.dumps({"schema_version": 1, "status": "complete"}),
                encoding="utf-8",
            )
            (run / "outcome.json").write_text(
                json.dumps(solved_outcome()), encoding="utf-8"
            )
            self.run_dir = run
            return run

        def resume(self, run_dir: Path) -> Path:
            self.run_dir = run_dir
            return run_dir

    validation_calls = 0

    def validate(
        active_runner: AutonomyRunner, campaign_run: Path, index: int
    ) -> SuccessValidation:
        nonlocal validation_calls
        validation_calls += 1
        receipt = active_runner._round_dir(index) / "success-validation.json"
        passed = validation_calls == 2
        receipt.write_text(json.dumps({"passed": passed}), encoding="utf-8")
        return SuccessValidation(
            passed, "passed" if passed else "missing theorem", receipt
        )

    def execute_optimizer(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        Path(request["output"]).write_text(
            json.dumps(optimizer_output()), encoding="utf-8"
        )
        Path(request["receipt"]).write_text(
            json.dumps({"status": "succeeded"}), encoding="utf-8"
        )
        return 0

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autonomy.RegimeRunner", FakeRegimeRunner
    )
    monkeypatch.setattr(AutonomyRunner, "_validate_success", validate)
    monkeypatch.setattr(
        "agentic_lean_math_assistant.autonomy.execute_agent_request", execute_optimizer
    )

    runner = AutonomyRunner(
        project,
        AutonomyRuntimeOptions(
            approval_timeout_minutes=0,
            afk_autonomy=True,
            decision_poll_seconds=0.001,
        ),
    )
    session = runner.run()
    state = json.loads((session / "state.json").read_text(encoding="utf-8"))

    assert state["status"] == "solved"
    assert len(state["rounds"]) == 2
    assert state["rounds"][0]["decision"] == {
        "strategy": "repair-success-validation",
        "source": "afk-timeout",
        "at": state["rounds"][0]["decision"]["at"],
    }
    assert FakeRegimeRunner.directives[0] is None
    assert FakeRegimeRunner.directives[1] is not None
    directive = FakeRegimeRunner.directives[1]
    assert directive is not None
    assert "Do not change or weaken" in directive.read_text(encoding="utf-8")
    assert FakeRegimeRunner.overrides[1][0][0] == "proof"
    analysis = Path(state["rounds"][0]["analysis"])
    assert "attempt-001" in analysis.parts
    assert (
        json.loads(analysis.read_text(encoding="utf-8"))["contract_preserved"] is True
    )


def test_optimizer_attempts_are_append_only(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    runner = AutonomyRunner(project, AutonomyRuntimeOptions())
    runner.session_dir = runner._initialize_session()
    state = runner._state()
    active = {
        "index": 1,
        "status": "running",
        "campaign_run": None,
        "campaign_outcome": None,
        "campaign_error": "transport failed",
        "analysis": None,
        "analysis_error": None,
        "decision": None,
        "success_validation": None,
        "started_at": state["created_at"],
        "completed_at": None,
    }
    state["rounds"] = [active]
    state["current_round"] = 1
    state["status"] = "campaign_running"
    calls = 0

    def execute_optimizer(request_path: Path) -> int:
        nonlocal calls
        calls += 1
        request = json.loads(request_path.read_text(encoding="utf-8"))
        Path(request["receipt"]).write_text(
            json.dumps({"status": "failed" if calls == 1 else "succeeded"}),
            encoding="utf-8",
        )
        if calls == 1:
            return 1
        Path(request["output"]).write_text(
            json.dumps(optimizer_output("recover-campaign-failure")),
            encoding="utf-8",
        )
        return 0

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autonomy.execute_agent_request", execute_optimizer
    )
    runner._prepare_analysis(
        state,
        active,
        None,
        outcome=None,
        validation=None,
        synthetic_strategy="recover-campaign-failure",
    )

    analysis_root = runner._round_dir(1) / "analysis"
    assert (
        json.loads(
            (analysis_root / "attempt-001" / "receipt.json").read_text(encoding="utf-8")
        )["status"]
        == "failed"
    )
    assert (
        json.loads(
            (analysis_root / "attempt-002" / "receipt.json").read_text(encoding="utf-8")
        )["status"]
        == "succeeded"
    )
    assert Path(active["analysis"]) == analysis_root / "attempt-002" / "analysis.json"


def test_afk_decision_uses_retained_deadline_after_resume(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    runner = AutonomyRunner(
        project,
        AutonomyRuntimeOptions(
            approval_timeout_minutes=60,
            afk_autonomy=True,
            decision_poll_seconds=10,
        ),
    )
    runner.session_dir = runner._initialize_session()
    state = runner._state()
    state["current_round"] = 1
    state["rounds"] = [{"index": 1, "status": "awaiting_approval"}]
    state["status"] = "awaiting_approval"
    runner._save_state(state, "test:awaiting-approval")
    request_dir = runner._round_dir(1) / "decision"
    request_dir.mkdir()
    (request_dir / "request.json").write_text(
        json.dumps(
            {
                "recommended_strategy": "continue",
                "deadline_at": "2000-01-01T00:00:00Z",
            }
        ),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.autonomy.time.sleep",
        lambda _seconds: pytest.fail("expired retained deadline must not sleep"),
    )

    assert runner._await_decision(state) == ("continue", "afk-timeout")
