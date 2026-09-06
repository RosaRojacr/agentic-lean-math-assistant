from __future__ import annotations

import io
import json
import os
from pathlib import Path

import pytest
from test_autonomy import write_autonomy_project

import agentic_lean_math_assistant.autorun as autorun_module
from agentic_lean_math_assistant.autorun import (
    AutoRunError,
    AutoRunOptions,
    AutoRunRunner,
    autorun_status,
    discover_project,
    follow_autorun_events,
    follow_autorun_output,
    follow_autorun_status,
    request_autorun_stop,
)
from agentic_lean_math_assistant.project import ProjectSpec
from agentic_lean_math_assistant.terminal_status import LiveStatusDisplay


def write_master_prompt(manifest: Path, text: str = "Prove the exact target.") -> Path:
    prompt = manifest.parent / "MASTER_PROMPT.md"
    prompt.write_text(f"# Master Prompt\n\n{text}\n", encoding="utf-8")
    return prompt


def successful_agent(request_path: Path) -> int:
    request = json.loads(request_path.read_text(encoding="utf-8"))
    if request["role_id"] == "autorun_strategy_reflection":
        output = (
            "The current approach remains proportionate after comparing alternatives.\n"
            "MEANINGFUL_PROGRESS_LIKELIHOOD: 70\n"
            "MINIMUM_WORTHWHILE_LIKELIHOOD: 30\n"
            "CURRENT_COURSE_WORTHWHILE: yes\n"
            "STRATEGY_DECISION: continue\n"
            "STRATEGY_PLAN_STATUS: ready\n"
            "REPLACEMENT_MEANINGFUL_PROGRESS_LIKELIHOOD: 70\n"
            "EXPECTED_ROUNDS_TO_FIRST_EVIDENCE: 2\n"
            "EXPECTED_COMPUTE_COST: low\n"
            "COURSE_TO_ABANDON: n/a\n"
            "CANDIDATE_STRATEGIES: scalable lemma || finite enumeration\n"
            "SELECTED_METHOD: prove the scalable lemma interface\n"
            "STRATEGY_MILESTONES: 2::checked scalable lemma; 6::target coverage\n"
            "FIRST_FALSIFIABLE_CHECK: compile the scalable lemma\n"
            "STRATEGY_KILL_CRITERIA: lemma cannot state required bound || counterexample\n"
            "REFLECTION_NEXT: prove the next scalable lemma\n"
        )
    elif request["role_id"] == "autorun_progress_adjudicator":
        output = (
            "ADJUDICATED_PROGRESS: incremental\n"
            "STRATEGY_ALIGNMENT: aligned\n"
            "MILESTONE_RESULT: complete\n"
            "MILESTONE_INDEX: 1\n"
            "ADJUDICATION_REASON: the checked step is real but not load-bearing\n"
            "VERIFIED_SCOPE_DELTA: one local obligation was discharged\n"
        )
    else:
        output = (
            "AUTORUN_RESULT: meaningful\n"
            "AUTORUN_SUMMARY: completed one checked step\n"
            "AUTORUN_NEXT: prove the next lemma\n"
            "STRATEGY_ID: strategy-00001\n"
            "STRATEGY_MILESTONE: 1\n"
            "MILESTONE_RESULT: advanced\n"
            "EVIDENCE: focused check passed\n"
        )
    Path(request["output"]).write_text(output, encoding="utf-8")
    Path(request["receipt"]).write_text(
        json.dumps({"schema_version": 1, "status": "succeeded"}),
        encoding="utf-8",
    )
    return 0


def test_autorun_executes_one_self_prompted_round_and_retains_state(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    observed_prompts: list[str] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        observed_prompts.append(Path(request["prompt"]).read_text(encoding="utf-8"))
        return successful_agent(request_path)

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    runner = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )

    session = runner.run()
    state = autorun_status(session)

    assert state["status"] == "paused"
    assert state["round_count"] == 1
    assert state["consecutive_execution_failures"] == 0
    assert state["last_progress_claim"] == "meaningful"
    assert state["last_progress_class"] == "incremental"
    assert state["incremental_round_count"] == 1
    assert state["meaningful_round_count"] == 0
    assert state["last_output"].endswith("round-00001/output.md")
    conductor_prompt = next(
        prompt for prompt in observed_prompts if "choose your own next" in prompt
    )
    assert "Prove the exact target." in conductor_prompt
    assert state["active_strategy"]["first_evidence_observed"] is True
    assert state["active_strategy"]["milestones"][0]["status"] == "complete"
    assert "choose your own next" in conductor_prompt
    assert (
        "Keep every command inside the inherited resource-control cgroup"
        in conductor_prompt
    )
    assert (session / "events.jsonl").is_file()


def test_autorun_runs_trusted_metric_before_independent_adjudication(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    text = manifest.read_text(encoding="utf-8")
    manifest.write_text(
        text.replace(
            "[autonomy]",
            """[autorun]
worthwhile_likelihood_threshold = 30
strategy_horizon_rounds = 12
adjudication_minutes = 5

[[autorun.progress_metrics]]
id = "coverage"
command = ["python3", "-c", 'import json; print(json.dumps({"covered": 7}))']
timeout = 10

[autonomy]""",
        ),
        encoding="utf-8",
    )
    master = write_master_prompt(manifest)
    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request",
        successful_agent,
    )
    session = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    ).run()

    metric = json.loads(
        (
            session / "rounds" / "round-00001" / "progress-metric-coverage.json"
        ).read_text(encoding="utf-8")
    )
    state = autorun_status(session)
    assert metric["error"] is None
    assert metric["value"] == {"covered": 7}
    assert state["last_progress_claim"] == "meaningful"
    assert state["last_progress_class"] == "incremental"
    assert state["last_adjudication_model"] == "openai-codex/gpt-5.6-terra"


def test_adjudicated_strategy_falsification_forces_next_reflection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        if request["role_id"] != "autorun_progress_adjudicator":
            return successful_agent(request_path)
        Path(request["output"]).write_text(
            "ADJUDICATED_PROGRESS: blocked\n"
            "STRATEGY_ALIGNMENT: falsified\n"
            "MILESTONE_RESULT: falsified\n"
            "MILESTONE_INDEX: 1\n"
            "ADJUDICATION_REASON: the required estimate has a checked counterexample\n"
            "VERIFIED_SCOPE_DELTA: no target coverage was added\n",
            encoding="utf-8",
        )
        Path(request["receipt"]).write_text(
            json.dumps({"schema_version": 1, "status": "succeeded"}),
            encoding="utf-8",
        )
        return 0

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    session = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    ).run()

    state = autorun_status(session)
    assert state["last_progress_class"] == "blocked"
    assert state["mathematical_blocker_count"] == 1
    assert state["strategy_change_required"] is True
    assert state["active_strategy"]["status"] == "falsified"
    assert state["active_strategy"]["milestones"][0]["status"] == "falsified"
    assert AutoRunRunner._strategy_requires_review(state) is True


def test_autorun_migrates_v1_state_and_separates_attempts(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    runner = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = runner._select_session()
    state = json.loads((session / "state.json").read_text(encoding="utf-8"))
    state["schema_version"] = 1
    state["consecutive_failures"] = 2
    for name in (
        "blocked_round_count",
        "complete_round_count",
        "unclassified_round_count",
        "attempt_count",
        "controller_failure_count",
        "agent_execution_failure_count",
        "verification_failure_count",
        "strategy_gate_failure_count",
        "mathematical_blocker_count",
        "consecutive_execution_failures",
        "last_failure_class",
        "active_strategy",
        "strategy_history",
        "last_progress_claim",
        "last_progress_adjudication",
        "last_adjudication_review",
        "last_adjudication_model",
    ):
        state.pop(name, None)
    rounds = session / "rounds"
    (rounds / "round-00007").mkdir(parents=True)
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")

    migrated = autorun_status(session)
    assert migrated["schema_version"] == 2
    assert migrated["attempt_count"] == 7
    assert migrated["consecutive_execution_failures"] == 2
    assert "consecutive_failures" not in migrated
    assert migrated["blocked_round_count"] == 0
    assert migrated["complete_round_count"] == 0
    assert migrated["unclassified_round_count"] == 0


def test_round_monitor_paths_are_strategy_pass_aware(tmp_path: Path) -> None:
    round_dir = tmp_path / "rounds" / "round-00003"
    round_dir.mkdir(parents=True)
    receipt = round_dir / "strategy-reflection-pass-02-receipt.json"
    stdout = round_dir / "strategy-reflection-pass-02-stdout.log"
    receipt.write_text('{"status": "running"}', encoding="utf-8")
    stdout.write_text("pass two\n", encoding="utf-8")

    assert autorun_module._round_receipt(tmp_path, 3, "strategy_reflection", 2) == {
        "status": "running"
    }
    assert (
        autorun_module._round_stdout_path(tmp_path, 3, "strategy_reflection", 2)
        == stdout
    )


def test_autorun_routes_only_strategy_reflections_to_astra(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    observed_requests: list[dict[str, object]] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        observed_requests.append(request)
        return successful_agent(request_path)

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    first = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )
    session = first.run()
    state = autorun_status(session)
    state["next_reflection_at"] = "2000-01-01T00:00:00Z"
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")

    resumed = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=2,
        ),
    )
    resumed.run()

    assert [request["model"] for request in observed_requests] == [
        "openai-codex/gpt-6-astra",
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-5.6-terra",
        "openai-codex/gpt-6-astra",
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-5.6-terra",
    ]
    reflection_request = observed_requests[3]
    assert reflection_request["role_id"] == "autorun_strategy_reflection"
    assert "strategy_pass" not in reflection_request
    assert reflection_request["max_time"] == 15 * 60
    assert reflection_request["empty_output_retries"] == 0
    assert reflection_request["tools"] == ["read"]
    assert reflection_request["workspace_executables"] is True
    main_prompt = (session / "rounds" / "round-00002" / "prompt.md").read_text(
        encoding="utf-8"
    )
    assert "Meaningful-progress strategy gate" in main_prompt
    final_state = autorun_status(session)
    assert final_state["reflection_count"] == 2
    assert final_state["last_model"] == "openai-codex/gpt-5.6-sol"
    assert final_state["last_reflection_model"] == "openai-codex/gpt-6-astra"
    assert final_state["last_strategy_likelihood"] == 70
    assert final_state["last_strategy_threshold"] == 30
    assert final_state["last_strategy_worthwhile"] is True
    assert final_state["last_strategy_decision"] == "continue"
    assert final_state["last_strategy_plan_status"] == "ready"


def test_strategy_gate_iterates_astra_until_course_change_plan_is_ready(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    observed_requests: list[dict[str, object]] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        observed_requests.append(request)
        if request["role_id"] != "autorun_strategy_reflection":
            return successful_agent(request_path)
        pass_number = sum(
            item["role_id"] == "autorun_strategy_reflection"
            for item in observed_requests
        )
        plan_status = "revise" if pass_number == 1 else "ready"
        selected = "derive a continuation theorem instead of enumerating tiny cells"
        output = (
            "The current cell-by-cell course cannot cover the remaining domain.\n"
            "MEANINGFUL_PROGRESS_LIKELIHOOD: 5\n"
            "MINIMUM_WORTHWHILE_LIKELIHOOD: 30\n"
            "CURRENT_COURSE_WORTHWHILE: no\n"
            "STRATEGY_DECISION: change_course\n"
            f"STRATEGY_PLAN_STATUS: {plan_status}\n"
            "REPLACEMENT_MEANINGFUL_PROGRESS_LIKELIHOOD: 65\n"
            "EXPECTED_ROUNDS_TO_FIRST_EVIDENCE: 2\n"
            "EXPECTED_COMPUTE_COST: medium\n"
            "COURSE_TO_ABANDON: stop adding adjacent tiny cells\n"
            "CANDIDATE_STRATEGIES: continuation theorem || interval atlas\n"
            f"SELECTED_METHOD: {selected}\n"
            "STRATEGY_MILESTONES: 2::derive local step; 6::prove propagation\n"
            "FIRST_FALSIFIABLE_CHECK: prove a uniform continuation step\n"
            "STRATEGY_KILL_CRITERIA: cannot cross ten cells || constants diverge\n"
            "REFLECTION_NEXT: test the continuation lemma on the retained branch\n"
        )
        Path(request["output"]).write_text(output, encoding="utf-8")
        Path(request["receipt"]).write_text(
            json.dumps({"schema_version": 1, "status": "succeeded"}),
            encoding="utf-8",
        )
        return 0

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    first = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )
    session = first.run()
    final_state = autorun_status(session)

    assert [request["model"] for request in observed_requests] == [
        "openai-codex/gpt-6-astra",
        "openai-codex/gpt-6-astra",
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-5.6-terra",
    ]
    reflection_requests = [
        request
        for request in observed_requests
        if request["role_id"] == "autorun_strategy_reflection"
    ]
    assert [Path(str(request["prompt"])).name for request in reflection_requests] == [
        "strategy-reflection-prompt.md",
        "strategy-reflection-pass-02-prompt.md",
    ]
    conductor_prompt = (session / "rounds" / "round-00001" / "prompt.md").read_text(
        encoding="utf-8"
    )
    assert "derive a continuation theorem instead of enumerating tiny cells" in (
        conductor_prompt
    )
    assert "abandon the rejected course" in " ".join(conductor_prompt.split())
    assert final_state["last_strategy_likelihood"] == 5
    assert final_state["last_strategy_threshold"] == 30
    assert final_state["last_strategy_worthwhile"] is False
    assert final_state["last_strategy_decision"] == "change_course"
    assert final_state["last_strategy_plan_status"] == "ready"
    assert final_state["strategy_change_required"] is False
    assert final_state["active_strategy"]["selected_likelihood"] == 65
    assert len(final_state["active_strategy"]["candidate_strategies"]) == 2
    assert final_state["active_strategy"]["milestones"][0]["deadline_execution"] == 2


def test_strategy_gate_never_runs_conductor_without_a_ready_plan(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    runner = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
        ),
    )
    session = runner._select_session()
    runner.session_dir = session
    round_dir = session / "rounds" / "round-00001"
    round_dir.mkdir(parents=True)
    passes: list[int] = []

    def unready_review(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        passes.append(len(passes) + 1)
        Path(request["output"]).write_text(
            "MEANINGFUL_PROGRESS_LIKELIHOOD: 5\n"
            "MINIMUM_WORTHWHILE_LIKELIHOOD: 30\n"
            "CURRENT_COURSE_WORTHWHILE: no\n"
            "STRATEGY_DECISION: change_course\n"
            "STRATEGY_PLAN_STATUS: revise\n"
            "REPLACEMENT_MEANINGFUL_PROGRESS_LIKELIHOOD: 60\n"
            "EXPECTED_ROUNDS_TO_FIRST_EVIDENCE: 2\n"
            "EXPECTED_COMPUTE_COST: medium\n"
            "COURSE_TO_ABANDON: stop enumerating cells\n"
            "CANDIDATE_STRATEGIES: continuation theorem || interval atlas\n"
            "SELECTED_METHOD: derive a global continuation theorem\n"
            "STRATEGY_MILESTONES: 2::local step; 6::full interval\n"
            "FIRST_FALSIFIABLE_CHECK: test the local continuation estimate\n"
            "STRATEGY_KILL_CRITERIA: estimate fails || constants diverge\n"
            "REFLECTION_NEXT: refine the continuation plan\n",
            encoding="utf-8",
        )
        return 0

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request",
        unready_review,
    )

    with pytest.raises(AutoRunError, match="did not produce an approved strategy"):
        runner._run_strategy_reflection(
            1,
            autorun_status(session),
            master.read_text(encoding="utf-8"),
            round_dir,
        )

    assert passes == [1, 2, 3]
    assert autorun_status(session)["strategy_change_required"] is True


def test_autorun_resume_reloads_edited_master_prompt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest, "First objective.")
    project = ProjectSpec.load(manifest)
    observed_prompts: list[str] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        observed_prompts.append(Path(request["prompt"]).read_text(encoding="utf-8"))
        return successful_agent(request_path)

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    first = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )
    session = first.run()
    master.write_text("# Master Prompt\n\nChanged objective.\n", encoding="utf-8")

    resumed = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=2,
        ),
    )
    assert resumed.run() == session

    conductor_prompts = [
        prompt for prompt in observed_prompts if "choose your own next" in prompt
    ]
    assert "First objective." in conductor_prompts[0]
    assert "Changed objective." in conductor_prompts[1]
    assert autorun_status(session)["round_count"] == 2


def test_autorun_recovers_after_failed_agent_round(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    conductor_attempts = 0
    session_path: Path | None = None
    retry_deadlines: list[str | None] = []
    accepted_before_failure: list[bool] = []

    def execute(request_path: Path) -> int:
        nonlocal conductor_attempts, session_path
        request = json.loads(request_path.read_text(encoding="utf-8"))
        session_path = Path(str(request["run_dir"]))
        if request["role_id"] != "autorun_conductor":
            return successful_agent(request_path)
        conductor_attempts += 1
        if conductor_attempts == 1:
            retained = autorun_status(session_path)
            accepted_before_failure.append(
                retained["reflection_count"] == 1
                and isinstance(retained["active_strategy"], dict)
            )
            return 1
        return successful_agent(request_path)

    def observe_retry_deadline(_seconds: float) -> None:
        assert session_path is not None
        retry_deadlines.append(autorun_status(session_path).get("next_retry_at"))

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    monkeypatch.setattr(autorun_module.time, "sleep", observe_retry_deadline)
    runner = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=1,
            max_rounds=2,
        ),
    )

    session = runner.run()
    state = autorun_status(session)

    assert conductor_attempts == 2
    assert state["status"] == "paused"
    assert state["attempt_count"] == 2
    assert state["round_count"] == 1
    assert state["agent_execution_failure_count"] == 1
    assert state["consecutive_execution_failures"] == 0
    assert len(retry_deadlines) == 1
    assert isinstance(retry_deadlines[0], str)
    assert state["next_retry_at"] is None
    assert accepted_before_failure == [True]
    assert "Previous controller/agent error" in (
        session / "rounds" / "round-00002" / "prompt.md"
    ).read_text(encoding="utf-8")


def test_autorun_bounds_targeted_model_recovery_attempts(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    conductor_models: list[str] = []
    conductor_routes: list[str] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        if request["role_id"] != "autorun_conductor":
            return successful_agent(request_path)
        conductor_models.append(str(request["model"]))
        state = autorun_status(Path(str(request["run_dir"])))
        conductor_routes.append(str(state["active_model_route"]))
        return 1

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request", execute
    )
    runner = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=5,
        ),
    )

    session = runner.run()

    assert conductor_models == [
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-6-astra",
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-5.6-sol",
    ]
    assert conductor_routes == [
        "primary",
        "primary",
        "targeted_recovery",
        "primary",
        "primary",
    ]
    state = autorun_status(session)
    assert state["attempt_count"] == 5
    assert state["round_count"] == 0
    assert state["agent_execution_failure_count"] == 5
    assert state["consecutive_execution_failures"] == 5


def test_autorun_skips_an_interrupted_round_directory_on_resume(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request",
        successful_agent,
    )
    first = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )
    session = first.run()
    orphan = session / "rounds" / "round-00002"
    orphan.mkdir()
    (orphan / "interrupted.txt").write_text("partial work retained\n", encoding="utf-8")

    resumed = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=3,
        ),
    )

    assert resumed.run() == session
    state = autorun_status(session)
    assert state["attempt_count"] == 3
    assert state["round_count"] == 2
    assert (session / "rounds" / "round-00003" / "output.md").is_file()
    assert (orphan / "interrupted.txt").read_text(encoding="utf-8") == (
        "partial work retained\n"
    )


def test_autorun_stop_request_is_durable(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    initializer = AutoRunRunner(
        project,
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()

    assert request_autorun_stop(session).startswith("autorun stop requested:")
    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.execute_agent_request",
        lambda _request: pytest.fail("stopped autorun must not start an agent"),
    )
    runner = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
        ),
    )

    assert runner.run() == session
    assert autorun_status(session)["status"] == "stopped"


def test_follow_monitor_renders_graphical_status_and_verbal_recap(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(
        manifest,
        """## Primary objective

The immediate milestone is theorem `target_51_50`.

## Current evidence

- The high-density baseline theorem is kernel checked.
- The latest audit rejected the target because the geometric bridge is absent.

## Current critical path

1. Prove the exact weighted-perimeter identity.
2. Construct the arbitrary-candidate geometric bridge.
3. Only after those proofs, compose the full cell inventory theorem.
4. Close the complete conjecture over the near-one interval.

Prefer a small vertical slice before bulk generation.
""",
    )
    project = ProjectSpec.load(manifest)
    initializer = AutoRunRunner(
        project,
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    state = autorun_status(session)
    state["status"] = "paused"
    state["active_round"] = None
    (session / "state.json").write_text(
        json.dumps(state),
        encoding="utf-8",
    )
    output = io.StringIO()

    follow_autorun_status(
        session,
        interval_seconds=0.001,
        output=output,
    )

    rendered = output.getvalue()
    assert rendered.startswith("◆ AUTORUN paused · ")
    assert "controller up · round - · agent idle" in rendered
    assert "PROGRESS UPDATE" in rendered
    assert "No conductor round is currently active." in rendered
    assert "The next automatic update is scheduled for" in rendered
    assert "IMMEDIATE MILESTONE" in rendered
    assert "theorem `target_51_50`" in rendered
    assert (
        "1. NEXT PREREQUISITE — Prove the exact weighted-perimeter identity."
        in rendered
    )
    assert "2. OPEN — Construct the arbitrary-candidate geometric bridge." in rendered
    assert "3. GATED — Only after those proofs" in rendered
    assert "4. QUEUED — Close the complete conjecture" in rendered
    assert "VERIFIED BASELINE" in rendered
    assert "CURRENT AUDIT BLOCKER" in rendered
    assert "Prefer a small vertical slice" not in rendered


def test_follow_monitor_adds_detailed_astra_strategy_report(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    review = session / "strategy-review.md"
    review.write_text(
        "ABANDON_CURRENT_COURSE: stop enumerating adjacent cells\n"
        "ALTERNATIVE_METHOD: derive a scale-local certificate atlas\n"
        "STRATEGY_MILESTONES: pilot two bands; replay the consumer; fill coverage\n"
        "FIRST_FALSIFIABLE_CHECK: certify both pilot bands within two rounds\n"
        "STRATEGY_KILL_CRITERIA: stop if either pilot band needs bespoke tuning\n"
        "REFLECTION_NEXT: run the bounded two-band pilot\n",
        encoding="utf-8",
    )
    state = autorun_status(session)
    state.update(
        {
            "status": "paused",
            "last_strategy_decision": "change_course",
            "last_strategy_likelihood": 5,
            "last_strategy_threshold": 30,
            "last_strategy_plan_status": "ready",
            "last_strategy_review": str(review),
        }
    )
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")
    output = io.StringIO()

    follow_autorun_status(
        session,
        interval_seconds=0.001,
        output=output,
    )

    rendered = output.getvalue()
    assert "ASTRA STRATEGY REPORT" in rendered
    assert "5% against a 30% worthwhile threshold" in rendered
    assert "REJECTED COURSE\n\nstop enumerating adjacent cells" in rendered
    assert "REPLACEMENT METHOD\n\nderive a scale-local certificate atlas" in rendered
    assert "STRATEGY MILESTONES" in rendered
    assert "FIRST FALSIFIABLE CHECK" in rendered
    assert "KILL CRITERIA" in rendered
    assert "STRATEGY NEXT ACTION\n\nrun the bounded two-band pilot" in rendered


def test_persistent_status_monitor_shows_recovery_deadline_until_resume(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    state_path = session / "state.json"
    state = autorun_status(session)
    state.update(
        {
            "status": "recovering",
            "active_round": None,
            "next_retry_at": "2099-01-01T00:00:00Z",
        }
    )
    state_path.write_text(json.dumps(state), encoding="utf-8")
    sleeps = 0

    def resume_then_interrupt(_seconds: float) -> None:
        nonlocal sleeps
        sleeps += 1
        if sleeps == 1:
            resumed = autorun_status(session)
            resumed.update(
                {
                    "status": "running",
                    "active_round": 4,
                    "active_model_route": "primary",
                    "active_model": "openai-codex/gpt-5.6-sol",
                    "next_retry_at": None,
                }
            )
            state_path.write_text(json.dumps(resumed), encoding="utf-8")
            return
        raise KeyboardInterrupt

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.time.sleep", resume_then_interrupt
    )
    output = io.StringIO()
    follow_autorun_status(
        session,
        interval_seconds=0.001,
        output=output,
        persistent=True,
    )

    rendered = output.getvalue()
    assert "AUTORUN recovering" in rendered
    assert "retry at 2099-01-01T00:00:00Z" in rendered
    assert "AUTORUN running" in rendered
    assert "round 4" in rendered


def test_persistent_status_monitor_recovers_from_unreadable_state(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    state_path = session / "state.json"
    retained_state = state_path.read_text(encoding="utf-8")
    state_path.unlink()
    sleeps = 0

    def restore_then_interrupt(_seconds: float) -> None:
        nonlocal sleeps
        sleeps += 1
        if sleeps == 1:
            state_path.write_text(retained_state, encoding="utf-8")
            return
        raise KeyboardInterrupt

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.time.sleep", restore_then_interrupt
    )
    output = io.StringIO()
    follow_autorun_status(
        session,
        interval_seconds=0.001,
        output=output,
        persistent=True,
    )

    rendered = output.getvalue()
    assert "AUTORUN recovering" in rendered
    assert "state unavailable · reconnecting" in rendered
    assert "AUTORUN running" in rendered


def test_round_output_monitor_switches_to_the_active_round(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    class InteractiveStream(io.StringIO):
        def isatty(self) -> bool:
            return True

    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    state_path = session / "state.json"
    state = autorun_status(session)
    state.update(
        {
            "status": "running",
            "active_round": 3,
            "active_model_route": "primary",
            "active_model": "openai-codex/gpt-5.6-sol",
        }
    )
    state_path.write_text(json.dumps(state), encoding="utf-8")
    round_three = session / "rounds" / "round-00003"
    round_three.mkdir(parents=True)
    (round_three / "stdout.log").write_text("round three output\n", encoding="utf-8")
    sleeps = 0

    def advance_then_interrupt(_seconds: float) -> None:
        nonlocal sleeps
        sleeps += 1
        if sleeps == 1:
            advanced = autorun_status(session)
            advanced["active_round"] = 4
            state_path.write_text(json.dumps(advanced), encoding="utf-8")
            round_four = session / "rounds" / "round-00004"
            round_four.mkdir(parents=True)
            (round_four / "stdout.log").write_text(
                "round four output\n", encoding="utf-8"
            )
            return
        raise KeyboardInterrupt

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.time.sleep", advance_then_interrupt
    )
    output = InteractiveStream()
    follow_autorun_output(session, interval_seconds=0.001, output=output)

    rendered = output.getvalue()
    assert "\x1b]0;Round 3 Output\x07" in rendered
    assert "\x1b]0;Round 4 Output\x07" in rendered
    assert "round three output" in rendered
    assert "round four output" in rendered


def test_raw_event_monitor_tracks_the_active_round(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    class InteractiveStream(io.StringIO):
        def isatty(self) -> bool:
            return True

    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    state_path = session / "state.json"
    state = autorun_status(session)
    state.update(
        {
            "status": "running",
            "active_round": 3,
            "active_model_route": "primary",
        }
    )
    state_path.write_text(json.dumps(state), encoding="utf-8")
    AutoRunRunner._event(session, "round_started", "round 3")
    sleeps = 0

    def advance_then_interrupt(_seconds: float) -> None:
        nonlocal sleeps
        sleeps += 1
        if sleeps == 1:
            advanced = autorun_status(session)
            advanced["active_round"] = 4
            state_path.write_text(json.dumps(advanced), encoding="utf-8")
            AutoRunRunner._event(session, "round_started", "round 4")
            return
        raise KeyboardInterrupt

    monkeypatch.setattr(
        "agentic_lean_math_assistant.autorun.time.sleep", advance_then_interrupt
    )
    output = InteractiveStream()
    follow_autorun_events(session, interval_seconds=0.001, output=output)

    rendered = output.getvalue()
    assert "\x1b]0;Round 3 Raw events\x07" in rendered
    assert "\x1b]0;Round 4 Raw events\x07" in rendered
    assert '"detail": "round 3"' in rendered
    assert '"detail": "round 4"' in rendered


def test_herdr_pane_label_updates_once_per_round(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    labels: list[tuple[str, str]] = []
    monkeypatch.setenv("HERDR_PANE_ID", "w2:p3")
    autorun_module._HERDR_PANE_LABELS.clear()
    autorun_module._HERDR_LABEL_ATTEMPTS.clear()
    monkeypatch.setattr(
        autorun_module.HerdrClient,
        "rename_pane",
        lambda _client, pane_id, label: labels.append((pane_id, label)),
    )

    autorun_module._sync_herdr_pane_label("Round 3 Raw events")
    autorun_module._sync_herdr_pane_label("Round 3 Raw events")
    autorun_module._sync_herdr_pane_label("Round 138 Raw events")

    assert labels == [
        ("w2:p3", "Round 3 Raw events"),
        ("w2:p3", "Round 138 Raw events"),
    ]


def test_terminal_title_is_written_only_when_it_changes() -> None:
    class InteractiveStream(io.StringIO):
        def isatty(self) -> bool:
            return True

    output = InteractiveStream()
    autorun_module._TERMINAL_TITLES.clear()

    autorun_module._set_terminal_title(output, "Autorun round 138 status")
    autorun_module._set_terminal_title(output, "Autorun round 138 status")
    autorun_module._set_terminal_title(output, "Autorun round 139 status")

    assert output.getvalue().count("\x1b]0;") == 2


def test_live_status_display_erases_scrollback_in_an_alternate_screen(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class InteractiveStream(io.StringIO):
        def isatty(self) -> bool:
            return True

    monkeypatch.setenv("TERM", "xterm-256color")
    monkeypatch.delenv("NO_COLOR", raising=False)

    output = InteractiveStream()
    display = LiveStatusDisplay(stream=output)

    display.render(status="running", detail="obsolete long status")
    first_render = output.getvalue()
    display.render(status="running", detail="current status")
    second_render = output.getvalue()[len(first_render) :]
    display.finish()
    finish = output.getvalue()[len(first_render) + len(second_render) :]

    assert first_render.startswith("\u001b[3J\u001b[?1049h")
    assert "\u001b[?25l\u001b[?7l\u001b[2J\u001b[H" in first_render
    assert second_render.startswith("\u001b[H\r\u001b[2K")
    assert "current status" in second_render
    assert "obsolete long status" not in second_render
    assert second_render.endswith("\u001b[J")
    assert "\u001b[1A" not in second_render
    assert finish.endswith("\u001b[?25h\u001b[?1049l")


def test_live_status_display_wraps_complete_sections_within_pane(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class NarrowInteractiveStream(io.StringIO):
        def isatty(self) -> bool:
            return True

        def fileno(self) -> int:
            return 1

    monkeypatch.setenv("TERM", "xterm-256color")
    monkeypatch.delenv("NO_COLOR", raising=False)
    monkeypatch.setattr(
        os,
        "get_terminal_size",
        lambda _descriptor: os.terminal_size((48, 10)),
    )
    output = NarrowInteractiveStream()
    display = LiveStatusDisplay(stream=output)
    detail = "controller up · round 123 · agent running · completed 45 · failures 0"

    recap = (
        "PROGRESS UPDATE\n\n"
        "This complete progress update fits in the pane.\n\n"
        "DETAIL\n\n"
        "This deliberately oversized detail must not be rendered partially "
        "when the complete section cannot fit in the remaining pane rows."
    )
    display.render(status="running", detail=detail, recap=recap)
    first_render = output.getvalue()
    display.render(status="running", detail=detail, recap=recap)
    second_render = output.getvalue()[len(first_render) :]

    assert "\r\n" in first_render
    assert "…" not in first_render
    assert "completed 45" in first_render
    assert "failures 0" in first_render
    rendered_rows = first_render.count("\r\n") + 1
    assert rendered_rows <= 9
    assert "PROGRESS UPDATE" in first_render
    assert "This complete progress update fits in the pane." in first_render
    assert "DETAIL" not in first_render
    assert second_render.startswith("\u001b[H\r\u001b[2K")
    assert second_render.count("\u001b[2K") == rendered_rows
    assert "PROGRESS UPDATE" in second_render
    assert "DETAIL" not in second_render


def test_discover_project_walks_to_nearest_manifest(tmp_path: Path) -> None:
    manifest = write_autonomy_project(tmp_path)
    nested = manifest.parent / "proof" / "nested"
    nested.mkdir()

    assert discover_project(nested) == manifest


def test_autorun_rejects_reflection_outside_two_to_four_hours(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)

    with pytest.raises(ValueError, match="between 120 and 240"):
        AutoRunRunner(project, AutoRunOptions(reflection_minutes=119))
