from __future__ import annotations

import io
import json
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

import agentic_lean_math_assistant.benchmark as benchmark_module
import agentic_lean_math_assistant.regime as regime_module
from agentic_lean_math_assistant.agent_runner import RunnerInterrupted
from agentic_lean_math_assistant.artifacts import verify_evidence_index
from agentic_lean_math_assistant.benchmark import (
    BenchmarkRuntime,
    BenchmarkSuite,
    run_benchmark_suite,
)
from agentic_lean_math_assistant.cli import main as campaign_main
from agentic_lean_math_assistant.config import CampaignSpec, ConfigurationError
from agentic_lean_math_assistant.journal import append_state_snapshot
from agentic_lean_math_assistant.models import OrchestrationPlan, ResearchResult
from agentic_lean_math_assistant.process_registry import (
    registered_run_processes,
    registered_run_units,
)
from agentic_lean_math_assistant.processes import stop_all_campaigns
from agentic_lean_math_assistant.project import ProjectSpec
from agentic_lean_math_assistant.regime import (
    RegimeError,
    RegimeOptions,
    RegimeRunner,
    choose_strategy,
)
from agentic_lean_math_assistant.runtime import (
    campaign_state,
    refresh_campaign_evidence,
)
from agentic_lean_math_assistant.sandbox import SandboxInvocation


def project_fixture(tmp_path: Path, *, execution: str = "") -> ProjectSpec:
    (tmp_path / "problem.md").write_text(
        "# Fixture theorem\n\nShow that the retained premise implies the result.\n",
        encoding="utf-8",
    )
    references = tmp_path / "references"
    references.mkdir()
    (references / "source.txt").write_text("premise -> result\n", encoding="utf-8")
    (tmp_path / "knowledge").mkdir()
    manifest = tmp_path / "project.toml"
    manifest.write_text(
        f"""schema_version = 1
{execution}
[project]
id = "fixture-theorem"
title = "Fixture Theorem"
problem = "problem.md"
references = "references"
knowledge = "knowledge"
runs = "runs"
[regime]
max_tasks = 4
max_parallel = 2
max_restarts = 1
default_agent_time = 30
allowed_tools = ["read", "write"]
""",
        encoding="utf-8",
    )
    return ProjectSpec.load(manifest)


def benchmark_fixture(tmp_path: Path) -> BenchmarkSuite:
    suite_path = tmp_path / "benchmark.toml"
    suite_path.write_text(
        """schema_version = 1
[suite]
id = "resume-fixture"
runs_dir = "benchmark-runs"

[[cases]]
id = "first"
project = "project.toml"
expected_outcome = "solved"
missing_source_policy = "checkpoint"

[[cases]]
id = "second"
project = "project.toml"
expected_outcome = "solved"
missing_source_policy = "checkpoint"
""",
        encoding="utf-8",
    )
    return BenchmarkSuite.load(suite_path)


def test_regime_runs_gate_plan_agent_and_final_assessment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    output = io.StringIO()

    run_dir = RegimeRunner(
        project_fixture(
            tmp_path,
            execution="""[execution]
sandbox = false
network = true
""",
        ),
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=output,
        ),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    plan = json.loads(
        (run_dir / "pre-campaign/orchestration-plan.json").read_text(encoding="utf-8")
    )
    assert state["status"] == "complete"
    assert state["outcome"] == "solved"
    assert [item["id"] for item in plan["tasks"]] == ["analyst", "auditor"]
    assert (run_dir / "final-report.md").is_file()
    assert (run_dir / "compute-ledger.json").is_file()
    knowledge_records = list((tmp_path / "knowledge/analytic").glob("*-analyst.json"))
    assert knowledge_records
    assert json.loads(knowledge_records[0].read_text(encoding="utf-8"))["status"] == (
        "accepted"
    )
    assert verify_evidence_index(run_dir)
    requests = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in (run_dir / "pre-campaign/roles").glob("*/*/request.json")
    ]
    agent_requests = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in run_dir.glob("agents/*/*/attempt-*-request.json")
    ]
    thinking_by_role = {
        request["role_id"]: request["thinking"] for request in agent_requests
    }
    assert thinking_by_role == {"analyst": "high", "auditor": "xhigh"}
    ledger = json.loads((run_dir / "compute-ledger.json").read_text(encoding="utf-8"))
    assert ledger["yield"]["obligations_disposed"] == 1
    assert ledger["yield"]["knowledge_promotions"] == 1
    assert {
        attempt["role_id"]
        for attempt in ledger["attempts"]
        if attempt["phase"] == "meta"
    } == {"research_gate", "orchestration_planner", "main_assessment"}
    assert requests
    assert all(request["execution"]["sandbox"] is False for request in requests)
    generated = CampaignSpec.load(run_dir / "pre-campaign/generated/campaign.toml")
    assert generated.execution.sandbox is False
    assert generated.execution.network is True
    assessment = next(
        request for request in requests if request["role_id"] == "main_assessment"
    )
    assert Path(assessment["workspace"]) != run_dir
    assert str(run_dir) in assessment["sandbox_read_paths"]
    assert "research gate: skip" in output.getvalue()
    assert "The fixture problem is solved" in output.getvalue()


def test_regime_retries_failed_research_gate_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    project.problem_path.write_text(
        project.problem_path.read_text(encoding="utf-8")
        + "\nTrigger research gate execution failure.\n",
        encoding="utf-8",
    )

    run_dir = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()

    retry_prompt = (
        run_dir / "pre-campaign/roles/research_gate_retry/attempt-001/prompt.md"
    ).read_text(encoding="utf-8")
    assert (
        json.loads((run_dir / "state.json").read_text(encoding="utf-8"))["outcome"]
        == "solved"
    )
    assert "meta-agent 'research_gate' failed" in retry_prompt


def test_regime_resumes_research_gate_after_controller_failure(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(
        tmp_path,
        execution="""[execution]
sandbox = false
network = true
""",
    )
    failed = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(tmp_path / "missing-omp"),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    )
    with pytest.raises(RegimeError, match="research gate failed again"):
        failed.run()
    run_dir = failed.run_dir
    assert run_dir is not None
    assert (
        json.loads((run_dir / "pre-campaign/state.json").read_text(encoding="utf-8"))[
            "status"
        ]
        == "research_gate"
    )

    resumed = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).resume(run_dir)

    assert resumed == run_dir
    gate_attempts = run_dir / "pre-campaign/roles/research_gate"
    assert (
        json.loads(
            (gate_attempts / "attempt-001/receipt.json").read_text(encoding="utf-8")
        )["status"]
        == "failed"
    )
    assert (
        json.loads(
            (gate_attempts / "attempt-002/receipt.json").read_text(encoding="utf-8")
        )["status"]
        == "succeeded"
    )
    assert campaign_state(run_dir)["status"] == "complete"


@pytest.mark.parametrize("phase", ["research", "planning"])
def test_regime_resumes_each_preparation_phase(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    phase: str,
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(
        tmp_path,
        execution="""[execution]
sandbox = false
network = true
""",
    )
    if phase == "research":
        (project.references_dir / ".request-missing-source").touch()
    options = RegimeOptions(
        missing_source_policy="continue",
        omp=str(fake_omp),
        herdr=str(fake_herdr),
        focus=False,
        output=io.StringIO(),
    )
    failed = RegimeRunner(project, options)

    def interrupt(*_args: object, **_kwargs: object) -> object:
        raise RegimeError(f"interrupted during {phase}")

    monkeypatch.setattr(
        failed,
        "_research" if phase == "research" else "_plan",
        interrupt,
    )
    with pytest.raises(RegimeError, match=f"interrupted during {phase}"):
        failed.run()
    run_dir = failed.run_dir
    assert run_dir is not None
    assert (
        json.loads((run_dir / "pre-campaign/state.json").read_text(encoding="utf-8"))[
            "status"
        ]
        == phase
    )
    if phase == "planning":
        (run_dir / "pre-campaign/state.json").write_text(
            '{"truncated":', encoding="utf-8"
        )
    resumed = RegimeRunner(project, options).resume(run_dir)

    assert resumed == run_dir
    assert campaign_state(run_dir)["status"] == "complete"


def test_repeated_regime_runs_are_isolated_and_leave_no_processes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    monkeypatch.setenv(
        "AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(tmp_path / "runtime")
    )
    project = project_fixture(
        tmp_path,
        execution="""[execution]
sandbox = false
network = true
""",
    )
    options = RegimeOptions(
        missing_source_policy="checkpoint",
        omp=str(fake_omp),
        herdr=str(fake_herdr),
        focus=False,
        output=io.StringIO(),
    )

    runs = tuple(RegimeRunner(project, options).run() for _ in range(3))

    assert len(set(runs)) == 3
    for run_dir in runs:
        assert campaign_state(run_dir)["status"] == "complete"
        assert verify_evidence_index(run_dir)
        assert registered_run_processes(run_dir) == ()
        assert registered_run_units(run_dir) == ()


def test_pre_campaign_journal_rejects_retained_history_tampering(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    options = RegimeOptions(
        missing_source_policy="checkpoint",
        omp=str(fake_omp),
        herdr=str(fake_herdr),
        focus=False,
        output=io.StringIO(),
    )
    failed = RegimeRunner(project, options)

    def interrupt(*_args: object, **_kwargs: object) -> object:
        raise RegimeError("interrupted during planning")

    monkeypatch.setattr(failed, "_plan", interrupt)
    with pytest.raises(RegimeError, match="interrupted during planning"):
        failed.run()
    run_dir = failed.run_dir
    assert run_dir is not None
    journal = run_dir / "pre-campaign/events.jsonl"
    content = journal.read_text(encoding="utf-8")
    journal.write_text(
        content.replace('"sequence":1', '"sequence":9', 1), encoding="utf-8"
    )

    with pytest.raises(RegimeError, match="pre-campaign state journal"):
        RegimeRunner(project, options).resume(run_dir)


def test_pre_campaign_lock_wait_is_bounded(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = RegimeRunner(
        project_fixture(tmp_path), RegimeOptions(missing_source_policy="checkpoint")
    )
    runner.pre_dir = tmp_path / "pre-campaign"
    moments = iter((0.0, 31.0))

    class HeldLock:
        def __enter__(self) -> None:
            raise regime_module.CampaignRunError(
                "another controller holds the campaign run lock"
            )

        def __exit__(self, *_args: object) -> None:
            pytest.fail("unacquired lock must not be exited")

    monkeypatch.setattr(regime_module, "campaign_run_lock", lambda _path: HeldLock())
    monkeypatch.setattr(regime_module.time, "monotonic", lambda: next(moments))

    with (
        pytest.raises(
            RegimeError, match="timed out acquiring pre-campaign controller lock"
        ),
        runner._serialized_pre_campaign_lock(),
    ):
        pytest.fail("held lock must not enter")


def test_regime_repairs_invalid_final_assessment_once(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    project.problem_path.write_text(
        project.problem_path.read_text(encoding="utf-8")
        + "\nTrigger invalid assessment.\n",
        encoding="utf-8",
    )
    run_dir = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    outcome = json.loads((run_dir / "outcome.json").read_text(encoding="utf-8"))
    repair_prompt = (
        run_dir / "pre-campaign/roles/main_assessment_repair/attempt-001/prompt.md"
    ).read_text(encoding="utf-8")
    assert state["outcome"] == "solved"
    assert outcome["knowledge_promotions"][0]["task_id"] == "analyst"
    assert "unknown task 'historical_analyst'" in repair_prompt


def test_regime_retries_failed_final_assessment_execution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    project.problem_path.write_text(
        project.problem_path.read_text(encoding="utf-8")
        + "\nTrigger assessment execution failure.\n",
        encoding="utf-8",
    )

    run_dir = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()

    repair_prompt = (
        run_dir / "pre-campaign/roles/main_assessment_repair/attempt-001/prompt.md"
    ).read_text(encoding="utf-8")
    assert (
        json.loads((run_dir / "state.json").read_text(encoding="utf-8"))["outcome"]
        == "solved"
    )
    assert "meta-agent 'main_assessment' failed" in repair_prompt


def test_regime_repairs_invalid_orchestration_plan_once(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    project.problem_path.write_text(
        project.problem_path.read_text(encoding="utf-8")
        + "\nTrigger invalid orchestration plan.\n",
        encoding="utf-8",
    )

    run_dir = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()

    repair_prompt = (
        run_dir
        / "pre-campaign/roles/orchestration_planner_repair/attempt-001/prompt.md"
    ).read_text(encoding="utf-8")
    plan = json.loads(
        (run_dir / "pre-campaign/orchestration-plan.json").read_text(encoding="utf-8")
    )
    assert {task["strategy_id"] for task in plan["tasks"]} == {"direct"}
    assert "strategy portfolio entries have no tasks" in repair_prompt


def test_regime_resume_reuses_successful_planner_candidates(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(
        tmp_path,
        execution="""[execution]
sandbox = false
network = true
""",
    )
    options = RegimeOptions(
        missing_source_policy="checkpoint",
        omp=str(fake_omp),
        herdr=str(fake_herdr),
        focus=False,
        output=io.StringIO(),
    )
    failed = RegimeRunner(project, options)

    def reject_plan(_plan: OrchestrationPlan) -> None:
        raise RegimeError("temporary phase budget rejection")

    monkeypatch.setattr(failed, "_validate_plan_policy", reject_plan)
    with pytest.raises(RegimeError, match="temporary phase budget rejection"):
        failed.run()
    run_dir = failed.run_dir
    assert run_dir is not None
    original_execute = regime_module.execute_agent_request

    def reject_reinvoked_planner(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        if str(request["role_id"]).startswith("orchestration_planner"):
            pytest.fail("resume must reuse the retained successful planner output")
        return original_execute(request_path)

    monkeypatch.setattr(
        regime_module, "execute_agent_request", reject_reinvoked_planner
    )

    resumed = RegimeRunner(project, options).resume(run_dir)

    assert resumed == run_dir
    assert campaign_state(run_dir)["status"] == "complete"
    assert (
        run_dir
        / "pre-campaign/roles/orchestration_planner_repair_2/attempt-001/output.json"
    ).is_file()


def test_regime_isolates_research_writes_from_frozen_inputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    original_problem = project.problem_path.read_text(encoding="utf-8")
    (project.references_dir / ".attempt-protected-mutation").write_text(
        "attempt\n", encoding="utf-8"
    )

    run_dir = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()

    assert project.problem_path.read_text(encoding="utf-8") == original_problem
    assert (project.references_dir / "added.pdf").read_bytes() == (
        b"retained publication"
    )
    assert (run_dir / "input-snapshot/problem.md").read_text(
        encoding="utf-8"
    ) == original_problem
    pre_workspace = run_dir / "pre-campaign" / "workspace"
    requests = [
        json.loads(path.read_text(encoding="utf-8"))
        for path in (run_dir / "pre-campaign/roles").glob("*/*/request.json")
    ]
    assert all(Path(request["workspace"]) != pre_workspace for request in requests)
    research = next(
        request for request in requests if request["role_id"] == "publication_research"
    )
    assert str(pre_workspace / "problem.md") in research["sandbox_read_paths"]
    assert str(pre_workspace / "references") in research["sandbox_read_paths"]


def test_pre_campaign_input_copy_honors_exclusions(
    tmp_path: Path,
) -> None:
    source = tmp_path / "source"
    source.mkdir()
    (source / "keep.txt").write_text("keep\n", encoding="utf-8")
    excluded = source / ".lake"
    excluded.mkdir()
    (excluded / "link").symlink_to(tmp_path / "outside")
    destination = tmp_path / "destination"

    RegimeRunner._copy_regular_source(
        source,
        destination,
        excludes=(".lake", ".lake/**"),
    )

    assert (destination / "keep.txt").read_text(encoding="utf-8") == "keep\n"
    assert not (destination / ".lake").exists()
    RegimeRunner._reject_snapshot_symlinks(destination)


def test_research_promotion_rejects_conflicts_and_symlink_escapes(
    tmp_path: Path,
) -> None:
    project = project_fixture(tmp_path)
    runner = RegimeRunner(project, RegimeOptions(missing_source_policy="checkpoint"))
    runner.pre_workspace = tmp_path / "pre-workspace"
    source_root = runner.pre_workspace / "references"
    (source_root / "nested").mkdir(parents=True)
    (source_root / "nested/source.pdf").write_bytes(b"new source")
    result = ResearchResult.parse(
        {
            "schema_version": 1,
            "status": "complete",
            "summary": "fixture",
            "sources_added": ["nested/source.pdf"],
            "missing_sources": [],
            "limitations": [],
        }
    )
    outside = tmp_path / "outside"
    outside.mkdir()
    (project.references_dir / "nested").symlink_to(outside, target_is_directory=True)

    with pytest.raises(RegimeError, match="escapes references"):
        runner._promote_research_sources(result)
    assert not (outside / "source.pdf").exists()

    (project.references_dir / "nested").unlink()
    (project.references_dir / "nested").mkdir()
    destination = project.references_dir / "nested/source.pdf"
    destination.write_bytes(b"retained source")
    with pytest.raises(RegimeError, match="conflicts with a retained reference"):
        runner._promote_research_sources(result)
    assert destination.read_bytes() == b"retained source"


def test_regime_resumes_after_campaign_finishes_before_assessment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    options = RegimeOptions(
        missing_source_policy="checkpoint",
        omp=str(fake_omp),
        herdr=str(fake_herdr),
        focus=False,
        output=io.StringIO(),
    )
    assess = RegimeRunner._final_assessment

    def interrupt_assessment(self: RegimeRunner, _plan: object, _status: str) -> object:
        raise RuntimeError("injected assessment interruption")

    monkeypatch.setattr(RegimeRunner, "_final_assessment", interrupt_assessment)
    with pytest.raises(RuntimeError, match="assessment interruption"):
        RegimeRunner(project, options).run()
    run_dir = next(project.runs_dir.iterdir())
    pre_state = json.loads(
        (run_dir / "pre-campaign/state.json").read_text(encoding="utf-8")
    )
    campaign_state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert pre_state["status"] == "executing"
    assert campaign_state["status"] == "complete"
    assert "outcome" not in campaign_state

    monkeypatch.setattr(RegimeRunner, "_final_assessment", assess)
    resumed = RegimeRunner(project, options).resume(run_dir)
    recovered = json.loads((resumed / "state.json").read_text(encoding="utf-8"))

    assert recovered["status"] == "complete"
    assert recovered["outcome"] == "solved"
    assert verify_evidence_index(resumed)


def test_regime_checkpoints_when_a_critical_source_needs_manual_acquisition(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    project = project_fixture(tmp_path)
    (project.references_dir / ".request-missing-source").write_text(
        "fixture\n", encoding="utf-8"
    )
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    output = io.StringIO()

    run_dir = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=output,
        ),
    ).run()

    pre_state = json.loads(
        (run_dir / "pre-campaign/state.json").read_text(encoding="utf-8")
    )
    request = json.loads(
        (run_dir / "pre-campaign/source-request.json").read_text(encoding="utf-8")
    )
    assert pre_state["status"] == "awaiting_sources"
    assert request["sources"][0]["title"] == "Missing fixture paper"
    assert not (run_dir / "state.json").exists()
    assert "critical publications require user input" in output.getvalue()
    assert campaign_main(["status", "--run", str(run_dir)]) == 3

    (tmp_path / "references/missing.pdf").write_bytes(b"fixture")
    resumed = RegimeRunner(
        ProjectSpec.load(tmp_path / "project.toml"),
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=output,
        ),
    ).resume(run_dir)
    resumed_state = json.loads((resumed / "state.json").read_text(encoding="utf-8"))
    assert resumed_state["status"] == "complete"
    current_research = json.loads(
        (resumed / "pre-campaign/research-result.json").read_text(encoding="utf-8")
    )
    assert current_research["status"] == "complete"
    assert current_research["summary"] == (
        "Observed the manually supplied fixture publication."
    )
    assert current_research["missing_sources"] == []


def test_regime_executes_frozen_pre_campaign_inputs(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    original = RegimeRunner._execute_campaign

    def mutate_live_inputs(
        self: RegimeRunner, campaign: object, plan: object, *, resume_existing: bool
    ) -> Path:
        project.problem_path.write_text("mutated live problem\n", encoding="utf-8")
        (project.references_dir / "source.txt").write_text(
            "mutated live reference\n", encoding="utf-8"
        )
        return original(
            self,
            campaign,
            plan,
            resume_existing=resume_existing,  # type: ignore[arg-type]
        )

    monkeypatch.setattr(RegimeRunner, "_execute_campaign", mutate_live_inputs)
    run = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()

    assert "Fixture theorem" in (run / "input-snapshot/problem.md").read_text(
        encoding="utf-8"
    )
    assert (run / "input-snapshot/references/source.txt").read_text(
        encoding="utf-8"
    ) == "premise -> result\n"


def test_concurrent_resume_commits_one_terminal_assessment(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    options = RegimeOptions(
        missing_source_policy="checkpoint",
        omp=str(fake_omp),
        herdr=str(fake_herdr),
        focus=False,
        output=io.StringIO(),
    )
    assessment = RegimeRunner._final_assessment

    def interrupt(self: RegimeRunner, _plan: object, _status: str) -> object:
        raise RuntimeError("injected assessment interruption")

    monkeypatch.setattr(RegimeRunner, "_final_assessment", interrupt)
    with pytest.raises(RuntimeError, match="assessment interruption"):
        RegimeRunner(project, options).run()
    run = next(project.runs_dir.iterdir())
    calls = 0
    counter_lock = threading.Lock()

    def counted(self: RegimeRunner, plan: object, status: str) -> object:
        nonlocal calls
        with counter_lock:
            calls += 1
        time.sleep(0.05)
        return assessment(self, plan, status)  # type: ignore[arg-type]

    monkeypatch.setattr(RegimeRunner, "_final_assessment", counted)
    with ThreadPoolExecutor(max_workers=2) as executor:
        resumed = list(
            executor.map(lambda _: RegimeRunner(project, options).resume(run), range(2))
        )

    assert resumed == [run, run]
    assert calls == 1
    assert campaign_state(run)["outcome"] == "solved"


def test_strategy_intent_recovers_missing_and_stale_artifacts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project = project_fixture(tmp_path)
    run = RegimeRunner(
        project,
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    ).run()
    outcome = {
        "schema_version": 2,
        "status": "unsolved",
        "summary": "More work is required.",
        "evidence": ["final-report.md"],
        "limitations": ["fixture"],
        "obligation_dispositions": [
            {
                "id": "fixture_result",
                "status": "unresolved",
                "reason": "The injected outcome requests more work.",
                "evidence": [],
            }
        ],
        "knowledge_promotions": [],
        "strategies": [
            {
                "id": "deepen",
                "title": "Deepen analysis",
                "rationale": "Inspect the remaining case.",
                "next_prompt": "Inspect the remaining case.",
                "recommended": True,
            }
        ],
    }
    regime_module.atomic_write_json(run / "outcome.json", outcome)
    state = campaign_state(run)
    state["status"] = "awaiting_strategy"
    state["outcome"] = "unsolved"
    state["error"] = outcome["summary"]
    append_state_snapshot(run, state, reason="test:awaiting-strategy")
    regime_module.atomic_write_json(run / "state.json", state)
    refresh_campaign_evidence(run)
    retained_atomic_write = regime_module.atomic_write_json

    def interrupt_selection(path: Path, value: object) -> None:
        if path.name == "strategy-selection.json":
            raise OSError("injected selection interruption")
        retained_atomic_write(path, value)

    monkeypatch.setattr(regime_module, "atomic_write_json", interrupt_selection)
    with pytest.raises(OSError, match="selection interruption"):
        choose_strategy(run, "deepen")

    monkeypatch.setattr(regime_module, "atomic_write_json", retained_atomic_write)
    assert choose_strategy(run, "deepen") == "Selected strategy: Deepen analysis"
    (run / "strategy-selection.json").write_text("{}", encoding="utf-8")
    (run / "next-campaign.md").write_text("stale\n", encoding="utf-8")
    assert choose_strategy(run, "deepen") == "Selected strategy: Deepen analysis"
    selection = json.loads(
        (run / "strategy-selection.json").read_text(encoding="utf-8")
    )
    assert selection["selected"]["id"] == "deepen"
    assert (run / "next-campaign.md").read_text(
        encoding="utf-8"
    ) == "Inspect the remaining case.\n"
    reasons = [
        json.loads(line)["reason"]
        for line in (run / "events.jsonl").read_text(encoding="utf-8").splitlines()
    ]
    assert reasons.count("strategy:receipt:deepen") == 1
    assert verify_evidence_index(run)


def test_stop_all_discovers_fixed_regime_meta_agent_without_campaign_registration(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime_dir = tmp_path / "runtime"
    monkeypatch.setenv("AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(runtime_dir))
    sleeper = tmp_path / "sleeping-omp"
    sleeper.write_text(
        "#!/usr/bin/env python3\nimport time\ntime.sleep(30)\n",
        encoding="utf-8",
    )
    sleeper.chmod(0o755)
    systemctl = tmp_path / "systemctl"
    unit = "campaign-123-0123456789ab.service"
    terminated_units: list[tuple[str, str]] = []

    monkeypatch.setattr(
        "agentic_lean_math_assistant.agent_runner.prepare_sandbox",
        lambda command, **kwargs: SandboxInvocation(
            tuple(command),
            unit,
            str(systemctl),
            {"enabled": True, "backend": "test"},
            kwargs["environment"],
        ),
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.agent_runner.terminate_sandbox",
        lambda invocation: None,
    )

    def terminate_unit(unit_name: str, systemctl_path: str) -> None:
        terminated_units.append((unit_name, systemctl_path))

    monkeypatch.setattr(
        "agentic_lean_math_assistant.processes.terminate_sandbox_unit", terminate_unit
    )
    runner = RegimeRunner(
        project_fixture(tmp_path),
        RegimeOptions(
            missing_source_policy="checkpoint",
            omp=str(sleeper),
            focus=False,
            output=io.StringIO(),
        ),
    )
    runner._initialize_run()
    assert runner.run_dir is not None
    run_dir = runner.run_dir
    failures: list[RegimeError] = []

    def run_meta_agent() -> None:
        try:
            runner._run_meta_agent(
                "research_gate",
                "Run until externally stopped.",
                tools=("read",),
                max_time=30,
            )
        except RegimeError as exc:
            failures.append(exc)

    thread = threading.Thread(target=run_meta_agent)
    thread.start()
    deadline = time.monotonic() + 5
    while time.monotonic() < deadline:
        units = registered_run_units(run_dir)
        processes = registered_run_processes(run_dir)
        if units and processes:
            break
        time.sleep(0.01)
    assert tuple(record.unit for record in units) == (unit,)
    assert len(processes) == 1
    pid = processes[0].pid

    report = stop_all_campaigns(runtime_dir=runtime_dir, terminate_timeout=1)
    thread.join(timeout=5)

    assert not thread.is_alive()
    assert failures and isinstance(failures[0], regime_module.RegimeError)
    assert report.ok
    assert report.registrations == 0
    assert pid in report.terminated_pids
    assert terminated_units == [(unit, str(systemctl))]
    assert registered_run_units(run_dir) == ()
    assert registered_run_processes(run_dir) == ()


def test_blind_benchmark_scores_outcome_without_leaking_expectation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project_fixture(tmp_path)
    suite_path = tmp_path / "benchmark.toml"
    suite_path.write_text(
        """schema_version = 1
[suite]
id = "fixture-benchmark"
runs_dir = "benchmark-runs"

[[cases]]
id = "known-implication"
project = "project.toml"
expected_outcome = "solved"
missing_source_policy = "checkpoint"
""",
        encoding="utf-8",
    )

    report_path = run_benchmark_suite(
        BenchmarkSuite.load(suite_path),
        BenchmarkRuntime(
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    )

    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert report["summary"] == {
        "cases": 1,
        "completed": 1,
        "passed": 1,
        "failed": 0,
        "errors": 0,
        "false_closures": 0,
        "accepted": True,
    }
    campaign_run = Path(report["cases"][0]["run_dir"])
    prompts = tuple((campaign_run / "pre-campaign").glob("roles/*/*/prompt.md"))
    assert prompts
    assert all(
        "expected_outcome" not in prompt.read_text(encoding="utf-8")
        for prompt in prompts
    )


@pytest.mark.parametrize(
    ("validator_status", "matched", "false_closure"),
    (("passed", True, False), ("failed", False, True)),
)
def test_blind_benchmark_runs_hidden_validator_after_campaign(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    validator_status: str,
    matched: bool,
    false_closure: bool,
) -> None:
    fake_omp = Path(__file__).with_name("fake_campaign_omp.py").resolve()
    fake_herdr = Path(__file__).with_name("fake_herdr.py").resolve()
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr-state.json"))
    project_fixture(tmp_path)
    validation = tmp_path / "validation"
    validation.mkdir()
    validator = validation / "validator.py"
    validator.write_text(
        "import argparse, json\n"
        "parser = argparse.ArgumentParser()\n"
        "parser.add_argument('--run-dir', required=True)\n"
        "parser.add_argument('--lake', required=True)\n"
        "args = parser.parse_args()\n"
        "print(json.dumps({"
        f"'checks': [{{'id': 'fixture', 'passed': {validator_status == 'passed'}}}], "
        f"'status': {validator_status!r}, "
        "'summary': 'hidden fixture validator'}))\n",
        encoding="utf-8",
    )
    suite_path = tmp_path / "benchmark.toml"
    suite_path.write_text(
        """schema_version = 1
[suite]
id = "hidden-validator"
runs_dir = "benchmark-runs"

[[cases]]
id = "validated-result"
project = "project.toml"
expected_outcome = "solved"
missing_source_policy = "checkpoint"
validator = "validation/validator.py"
validator_timeout = 30
""",
        encoding="utf-8",
    )

    report_path = run_benchmark_suite(
        BenchmarkSuite.load(suite_path),
        BenchmarkRuntime(
            omp=str(fake_omp),
            herdr=str(fake_herdr),
            focus=False,
            output=io.StringIO(),
        ),
    )

    report = json.loads(report_path.read_text(encoding="utf-8"))
    result = report["cases"][0]
    assert report["schema_version"] == 3
    assert result["matched"] is matched
    assert result["false_closure"] is false_closure
    assert result["validator_status"] == validator_status
    receipt = Path(result["validator_receipt"])
    retained = json.loads(receipt.read_text(encoding="utf-8"))
    assert retained["result"]["status"] == validator_status
    campaign_run = Path(result["run_dir"])
    prompts = tuple((campaign_run / "pre-campaign").glob("roles/*/*/prompt.md"))
    assert prompts
    assert all(
        "hidden fixture validator" not in prompt.read_text(encoding="utf-8")
        for prompt in prompts
    )


def test_blind_benchmark_records_case_error_and_continues(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project_fixture(tmp_path)
    suite_path = tmp_path / "benchmark.toml"
    suite_path.write_text(
        """schema_version = 1
[suite]
id = "failure-isolation"
runs_dir = "benchmark-runs"

[[cases]]
id = "transport-failure"
project = "project.toml"
expected_outcome = "solved"
missing_source_policy = "checkpoint"

[[cases]]
id = "subsequent-result"
project = "project.toml"
expected_outcome = "blocked"
missing_source_policy = "checkpoint"
""",
        encoding="utf-8",
    )
    invocation = 0

    def run_or_fail(self: RegimeRunner) -> Path:
        nonlocal invocation
        invocation += 1
        if invocation == 1:
            raise RuntimeError("agent transport failed")
        interim_paths = tuple(
            (tmp_path / "benchmark-runs").glob("*/benchmark-report.json")
        )
        assert len(interim_paths) == 1
        interim = json.loads(interim_paths[0].read_text(encoding="utf-8"))
        assert interim["status"] == "running"
        assert interim["summary"]["completed"] == 1
        assert interim["summary"]["errors"] == 1
        run = tmp_path / "runs" / "subsequent-result"
        run.mkdir(parents=True)
        (run / "outcome.json").write_text(
            json.dumps({"status": "blocked"}), encoding="utf-8"
        )
        return run

    monkeypatch.setattr(benchmark_module.RegimeRunner, "run", run_or_fail)

    report_path = run_benchmark_suite(BenchmarkSuite.load(suite_path))

    report = json.loads(report_path.read_text(encoding="utf-8"))
    assert invocation == 2
    assert report["schema_version"] == 3
    assert report["status"] == "complete"
    assert report["summary"] == {
        "cases": 2,
        "completed": 2,
        "passed": 1,
        "failed": 1,
        "errors": 1,
        "false_closures": 0,
        "accepted": False,
    }
    assert report["cases"][0]["observed_outcome"] == "error"
    assert report["cases"][0]["error"] == "RuntimeError: agent transport failed"
    assert report["cases"][1]["observed_outcome"] == "blocked"


def test_blind_benchmark_resumes_only_unrecorded_cases(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project_fixture(tmp_path)
    suite = benchmark_fixture(tmp_path)
    initial_invocations = 0

    def run_then_interrupt(self: RegimeRunner) -> Path:
        nonlocal initial_invocations
        initial_invocations += 1
        if initial_invocations == 2:
            raise RunnerInterrupted(15)
        run = tmp_path / "runs" / "first"
        run.mkdir(parents=True)
        (run / "outcome.json").write_text(
            json.dumps({"status": "solved"}), encoding="utf-8"
        )
        return run

    monkeypatch.setattr(benchmark_module.RegimeRunner, "run", run_then_interrupt)
    with pytest.raises(RunnerInterrupted):
        run_benchmark_suite(suite)
    report_path = next((tmp_path / "benchmark-runs").glob("*/benchmark-report.json"))
    checkpoint = json.loads(report_path.read_text(encoding="utf-8"))
    assert checkpoint["status"] == "running"
    assert checkpoint["summary"]["completed"] == 1
    started_at = checkpoint["started_at"]
    resumed_invocations = 0

    def finish_remaining(self: RegimeRunner) -> Path:
        nonlocal resumed_invocations
        resumed_invocations += 1
        run = tmp_path / "runs" / "second"
        run.mkdir(parents=True)
        (run / "outcome.json").write_text(
            json.dumps({"status": "solved"}), encoding="utf-8"
        )
        return run

    monkeypatch.setattr(benchmark_module.RegimeRunner, "run", finish_remaining)

    resumed_path = benchmark_module.resume_benchmark_suite(report_path)

    report = json.loads(resumed_path.read_text(encoding="utf-8"))
    assert resumed_path == report_path
    assert initial_invocations == 2
    assert resumed_invocations == 1
    assert report["started_at"] == started_at
    assert report["status"] == "complete"
    assert report["summary"]["completed"] == 2
    assert report["summary"]["accepted"] is True
    assert [item["case_id"] for item in report["cases"]] == ["first", "second"]


def test_blind_benchmark_resume_rejects_modified_suite(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project_fixture(tmp_path)
    suite = benchmark_fixture(tmp_path)

    def interrupt(self: RegimeRunner) -> Path:
        raise RunnerInterrupted(15)

    monkeypatch.setattr(benchmark_module.RegimeRunner, "run", interrupt)
    with pytest.raises(RunnerInterrupted):
        run_benchmark_suite(suite)
    report_path = next((tmp_path / "benchmark-runs").glob("*/benchmark-report.json"))
    suite.manifest_path.write_text(
        suite.manifest_path.read_text(encoding="utf-8") + "\n# changed\n",
        encoding="utf-8",
    )

    with pytest.raises(ConfigurationError, match="suite changed"):
        benchmark_module.resume_benchmark_suite(report_path)


def test_regime_rejects_plan_above_phase_budget(tmp_path: Path) -> None:
    project = project_fixture(tmp_path)
    value = {
        "schema_version": 3,
        "goal": "Attempt an over-budget derivation.",
        "rationale": "Exercise the hard budget.",
        "max_parallel": 1,
        "capability_decisions": [
            {
                "capability": "regression_assess",
                "decision": "skip",
                "task_id": None,
                "rationale": "The fixture has no numeric arrays.",
            },
            {
                "capability": "regression_fit",
                "decision": "skip",
                "task_id": None,
                "rationale": "The fixture requests an exact derivation.",
            },
        ],
        "strategy_portfolio": [],
        "obligations": [
            {
                "id": "result",
                "statement": "The result holds.",
                "evidence_tasks": ["analysis"],
            }
        ],
        "tasks": [
            {
                "id": "analysis",
                "title": "Analysis",
                "category": "analytic",
                "instructions": "Attempt the result.",
                "phase": "pilot",
                "strategy_id": None,
                "reasoning_class": "analysis",
                "novelty": "Try the retained fixture as an independent derivation.",
                "expected_evidence": ["A retained derivation."],
                "continuation_gate": False,
                "depends_on": [],
                "tools": ["read"],
                "model": None,
                "timeout": 4000,
                "max_attempts": 1,
                "required": True,
                "failure_policy": "abort",
            }
        ],
    }
    plan = OrchestrationPlan.parse(value)
    runner = RegimeRunner(
        project,
        RegimeOptions(missing_source_policy="checkpoint", output=io.StringIO()),
    )

    with pytest.raises(RegimeError, match="phase agent-second budgets"):
        runner._validate_plan_policy(plan)

    normalized_value, normalized, receipt = runner._normalize_plan_budgets(value, plan)

    assert normalized_value != value
    assert normalized.tasks[0].timeout < plan.tasks[0].timeout
    assert receipt is not None
    assert receipt["formula"] == "sum(2 * timeout * max_attempts)"
    runner._validate_plan_policy(normalized)


def test_regime_requires_regression_fit_to_descend_from_assessment(
    tmp_path: Path,
) -> None:
    project = project_fixture(tmp_path)
    runner = RegimeRunner(
        project,
        RegimeOptions(missing_source_policy="checkpoint", output=io.StringIO()),
    )
    runner.pre_workspace = tmp_path / "pre-workspace"
    (runner.pre_workspace / "project-inputs").mkdir(parents=True)

    def make_task(
        task_id: str, instructions: str, depends_on: list[str]
    ) -> dict[str, object]:
        return {
            "id": task_id,
            "title": task_id.title(),
            "category": "numeric",
            "instructions": instructions,
            "phase": "pilot",
            "strategy_id": None,
            "reasoning_class": "execution",
            "novelty": "Exercise the retained regression capability.",
            "expected_evidence": ["A retained exploratory numeric receipt."],
            "continuation_gate": False,
            "depends_on": depends_on,
            "tools": ["bash"],
            "model": None,
            "timeout": 30,
            "max_attempts": 1,
            "required": True,
            "failure_policy": "abort",
        }

    def make_plan(fit_depends_on: list[str]) -> OrchestrationPlan:
        return OrchestrationPlan.parse(
            {
                "schema_version": 3,
                "goal": "Assess and fit a retained numeric relationship.",
                "rationale": "Assessment prevents an unjustified fit.",
                "max_parallel": 2,
                "capability_decisions": [
                    {
                        "capability": "regression_assess",
                        "decision": "use",
                        "task_id": "assessment",
                        "rationale": "The campaign has retained numeric observations.",
                    },
                    {
                        "capability": "regression_fit",
                        "decision": "use",
                        "task_id": "fit",
                        "rationale": "A held-out surrogate directly answers the numeric question.",
                    },
                ],
                "strategy_portfolio": [],
                "obligations": [
                    {
                        "id": "numeric_result",
                        "statement": "The retained arrays support a held-out relationship.",
                        "evidence_tasks": ["assessment", "fit"],
                    }
                ],
                "tasks": [
                    make_task(
                        "assessment",
                        "Run agentic-lean-math-assistant regression-assess on the retained arrays.",
                        [],
                    ),
                    make_task(
                        "fit",
                        "Run agentic-lean-math-assistant regression-fit only after a positive assessment.",
                        fit_depends_on,
                    ),
                ],
            }
        )

    runner._validate_plan_policy(make_plan(["assessment"]))
    with pytest.raises(RegimeError, match="must descend"):
        runner._validate_plan_policy(make_plan([]))
