from __future__ import annotations

import hashlib
import io
import json
import os
from contextlib import nullcontext
from datetime import UTC, datetime, timedelta
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
    restore_autorun_workspace,
)
from agentic_lean_math_assistant.cli import main as cli_main
from agentic_lean_math_assistant.herdr import HerdrWorkspace, HerdrWorkspaceRecord
from agentic_lean_math_assistant.project import ProjectSpec
from agentic_lean_math_assistant.runtime import campaign_run_lock
from agentic_lean_math_assistant.terminal_status import LiveStatusDisplay


def write_master_prompt(manifest: Path, text: str = "Prove the exact target.") -> Path:
    prompt = manifest.parent / "MASTER_PROMPT.md"
    prompt.write_text(f"# Master Prompt\n\n{text}\n", encoding="utf-8")
    return prompt


def _proposal(
    *,
    decision: str = "select",
    base_strategy_id: str | None = None,
    base_revision: int | None = None,
    review_after: int = 3,
    checkpoint_after: int = 2,
    checkpoint_id: str = "first_check",
) -> str:
    value = {
        "schema_version": 1,
        "decision": decision,
        "base_strategy_id": base_strategy_id,
        "base_revision": base_revision,
        "selected_method": "Use the retained interface to discharge the target.",
        "decision_reason": "This course has an observable bounded next step.",
        "next_action": "Implement and verify the bounded next step.",
        "review_after_executions": review_after,
        "checkpoints": [
            {
                "id": checkpoint_id,
                "after_executions": checkpoint_after,
                "observable": "The named acceptance obligation is discharged.",
            }
        ],
        "stop_conditions": [
            {
                "id": "method_breaks",
                "observable": "The retained interface contradicts the required result.",
            }
        ],
    }
    return "STRATEGY_PROPOSAL_JSON: " + json.dumps(value, separators=(",", ":"))


def _claim(
    *,
    strategy_id: str = "strategy-00001",
    revision: int = 1,
    checkpoint_id: str | None = "first_check",
) -> str:
    return "CONDUCTOR_RESULT_JSON: " + json.dumps(
        {
            "schema_version": 1,
            "strategy_id": strategy_id,
            "strategy_revision": revision,
            "checkpoint_id": checkpoint_id,
            "progress_class": "meaningful",
            "summary": "The bounded acceptance obligation was verified.",
            "evidence": "proof/verified-artifact",
        },
        separators=(",", ":"),
    )


def _adjudication(
    *,
    strategy_id: str = "strategy-00001",
    revision: int = 1,
    progress_class: str = "meaningful",
    alignment: str = "aligned",
    checkpoint_id: str | None = "first_check",
    checkpoint_result: str = "satisfied",
    stop_id: str | None = None,
) -> str:
    return "PROGRESS_ADJUDICATION_JSON: " + json.dumps(
        {
            "schema_version": 1,
            "strategy_id": strategy_id,
            "strategy_revision": revision,
            "progress_class": progress_class,
            "alignment": alignment,
            "checkpoint_id": checkpoint_id,
            "checkpoint_result": checkpoint_result,
            "triggered_stop_condition_id": stop_id,
            "reason": "Repository evidence matches the active observable.",
            "verified_scope_delta": "One named acceptance obligation is now verified.",
        },
        separators=(",", ":"),
    )


def successful_agent(request_path: Path) -> int:
    request = json.loads(request_path.read_text(encoding="utf-8"))
    if request["role_id"] == "autorun_strategy_reflection":
        output = _proposal()
    elif request["role_id"] == "autorun_conductor":
        output = autorun_module.conductor_claim_marker(
            request_path,
            checkpoint_id="first_check",
            progress_class="meaningful",
            summary="The bounded acceptance obligation was verified.",
            evidence="proof/verified-artifact",
        )
    elif request["role_id"] == "autorun_progress_adjudicator":
        output = _adjudication()
    else:
        raise AssertionError(f"unexpected role {request['role_id']}")
    Path(request["output"]).write_text(output + "\n", encoding="utf-8")
    Path(request["receipt"]).write_text(
        json.dumps({"schema_version": 1, "status": "succeeded"}),
        encoding="utf-8",
    )
    return 0


def _contract(
    *,
    revision: int = 1,
    accepted_execution: int = 0,
    hard_deadline: int = 10,
    review_due: int = 3,
    checkpoint_due: int = 2,
    status: str = "active",
    checkpoint_status: str = "pending",
) -> dict[str, object]:
    return {
        "schema_version": 2,
        "strategy_id": "strategy-00001",
        "revision": revision,
        "status": status,
        "selected_method": "Use the retained interface.",
        "decision_reason": "It exposes an observable next step.",
        "accepted_attempt": revision,
        "accepted_execution": accepted_execution,
        "lineage_started_execution": 0,
        "hard_deadline_execution": hard_deadline,
        "review_due_execution": review_due,
        "next_action": "Discharge the next obligation.",
        "checkpoints": [
            {
                "id": "first_check",
                "due_execution": checkpoint_due,
                "observable": "The named obligation is verified.",
                "status": checkpoint_status,
                "last_result": None,
                "last_adjudication_execution": None,
            }
        ],
        "stop_conditions": [
            {
                "id": "method_breaks",
                "observable": "The interface contradicts the required result.",
                "triggered": False,
                "last_adjudication_execution": None,
            }
        ],
        "last_alignment": None,
        "last_checkpoint_result": None,
    }


def _strategy_state(
    strategy: dict[str, object] | None = None,
    *,
    execution: int = 0,
) -> dict[str, object]:
    return {
        "round_count": execution,
        "attempt_count": execution,
        "reflection_count": 0,
        "active_strategy": strategy,
        "strategy_history": [],
        "adjudication_history": [],
        "strategy_change_required": False,
    }


def _runner(tmp_path: Path) -> AutoRunRunner:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    return AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )


def _stopped_autorun_fixture(
    tmp_path: Path,
) -> tuple[ProjectSpec, Path, Path, str]:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    initializer = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
        ),
    )
    session = initializer._select_session()
    (session / "controller").mkdir()
    retained_artifact = session / "rounds" / "round-00004" / "receipt.json"
    retained_artifact.parent.mkdir(parents=True)
    retained_artifact.write_text('{"status":"retained"}\n', encoding="utf-8")
    state = autorun_status(session)
    state.update(
        {
            "status": "stopped",
            "pid": None,
            "round_count": 3,
            "attempt_count": 4,
            "active_round": None,
            "active_prompt": None,
            "active_model": None,
            "active_model_route": None,
            "active_strategy": _contract(
                accepted_execution=3,
                review_due=5,
                checkpoint_due=4,
            ),
            "strategy_history": [{"retained": "strategy history"}],
            "last_receipt": str(retained_artifact),
            "stop_requested": False,
        }
    )
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")
    response = request_autorun_stop(session)
    token = response.rsplit(" ", 1)[-1]
    assert len(token) == 32
    int(token, 16)
    return project, master, session, token


def test_stop_request_preserves_controller_state_projection(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
        ),
    )
    session = initializer._select_session()
    (session / "controller").mkdir()
    state_path = session / "state.json"
    before = state_path.read_bytes()

    response = request_autorun_stop(session)
    token = response.rsplit(" ", 1)[-1]

    assert state_path.read_bytes() == before
    marker = session / "controller" / "stop-requests" / token
    ledger = session / "controller" / "stop-token-ledger" / token
    assert marker.is_file()
    assert ledger.is_file()
    assert os.path.samefile(marker, ledger)
    assert not (session / "STOP").exists()


def test_first_stop_publication_fsyncs_its_controller_namespace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
        ),
    )
    session = initializer._select_session()
    controller = session / "controller"
    controller.mkdir()
    fsynced: list[Path] = []
    original_fsync = AutoRunRunner._fsync_directory

    def record_fsync(path: Path) -> None:
        fsynced.append(path)
        original_fsync(path)

    monkeypatch.setattr(AutoRunRunner, "_fsync_directory", staticmethod(record_fsync))
    request_autorun_stop(session)

    ledger = controller / "stop-token-ledger"
    pending = controller / "stop-requests"
    assert controller in fsynced
    assert ledger in fsynced
    assert pending in fsynced
    assert fsynced.index(controller) < fsynced.index(ledger)
    assert fsynced.index(controller) < fsynced.index(pending)


def test_new_controller_directory_is_durably_published(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    initializer = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
        ),
    )
    session = initializer._select_session()
    fsynced: list[Path] = []
    original_fsync = AutoRunRunner._fsync_directory

    def record_fsync(path: Path) -> None:
        fsynced.append(path)
        original_fsync(path)

    runner = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
            output=io.StringIO(),
        ),
    )
    monkeypatch.setattr(AutoRunRunner, "_fsync_directory", staticmethod(record_fsync))
    monkeypatch.setattr(runner, "_drive", lambda: session)

    assert runner.run() == session
    assert session in fsynced
    assert (session / "controller").is_dir()


def test_ordinary_startup_honors_legacy_stop_sentinel(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    initializer = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
        ),
    )
    session = initializer._select_session()
    state = autorun_status(session)
    state.update({"status": "stopped", "pid": None, "stop_requested": False})
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")
    (session / "STOP").write_text("legacy stop requested\n", encoding="utf-8")
    monkeypatch.setattr(
        autorun_module,
        "execute_agent_request",
        lambda _path: pytest.fail("legacy STOP dispatched a model"),
    )

    runner = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
            max_rounds=1,
            output=io.StringIO(),
        ),
    )
    assert runner.run() == session
    stopped = autorun_status(session)
    assert stopped["status"] == "stopped"
    assert stopped["pid"] is None
    assert stopped["stop_requested"] is True
    assert (session / "STOP").read_text(encoding="utf-8") == ("legacy stop requested\n")


def test_resume_cli_requires_explicit_session(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    manifest = write_autonomy_project(tmp_path)
    write_master_prompt(manifest)

    with pytest.raises(SystemExit) as raised:
        cli_main(
            [
                "autorun",
                "--project",
                str(manifest),
                "--resume-stopped",
                "a" * 32,
            ]
        )

    assert raised.value.code == 2
    assert "--resume-stopped requires an explicit --session" in capsys.readouterr().err


def _explicit_resume_runner(
    project: ProjectSpec,
    master: Path,
    session: Path,
    token: str,
) -> AutoRunRunner:
    return AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            resume_stopped=token,
            reflection_minutes=120,
            round_minutes=1,
            max_rounds=4,
            output=io.StringIO(),
        ),
    )


def test_durable_stop_requires_one_use_explicit_same_session_resume(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project, master, session, token = _stopped_autorun_fixture(tmp_path)
    stop_marker = session / "controller" / "stop-requests" / token
    stopped = autorun_status(session)
    protected = {
        name: value
        for name, value in stopped.items()
        if name
        not in {
            "status",
            "pid",
            "stop_requested",
            "heartbeat_at",
            "updated_at",
            "next_retry_at",
            "last_error",
        }
    }
    monkeypatch.setattr(
        autorun_module,
        "execute_agent_request",
        lambda _path: pytest.fail("durable-stop lifecycle dispatched a model"),
    )

    ordinary = AutoRunRunner(
        project,
        AutoRunOptions(
            master_prompt=master,
            session=session,
            reflection_minutes=120,
            round_minutes=1,
            max_rounds=4,
            output=io.StringIO(),
        ),
    )
    assert ordinary.run() == session
    still_stopped = autorun_status(session)
    assert still_stopped["status"] == "stopped"
    assert still_stopped["pid"] is None
    assert still_stopped["stop_requested"] is True
    assert not (session / "STOP").exists()
    assert stop_marker.is_file()

    explicit = _explicit_resume_runner(project, master, session, token)
    assert explicit.run() == session
    resumed = autorun_status(session)
    assert resumed["status"] == "paused"
    assert resumed["pid"] is None
    assert resumed["stop_requested"] is False
    assert not (session / "STOP").exists()
    assert not stop_marker.exists()
    assert {
        name: value for name, value in resumed.items() if name in protected
    } == protected
    assert json.loads(Path(resumed["last_receipt"]).read_text(encoding="utf-8")) == {
        "status": "retained"
    }
    events = (session / "events.jsonl").read_text(encoding="utf-8")
    assert "autorun controller explicitly resumed stopped session" in events

    later_response = request_autorun_stop(session)
    later_token = later_response.rsplit(" ", 1)[-1]
    later_state = autorun_status(session)
    later_state["status"] = "stopped"
    (session / "state.json").write_text(json.dumps(later_state), encoding="utf-8")
    before_replay = (session / "state.json").read_bytes()
    with pytest.raises(AutoRunError, match="does not identify"):
        _explicit_resume_runner(project, master, session, token).run()
    assert (session / "state.json").read_bytes() == before_replay
    assert (session / "controller" / "stop-requests" / later_token).is_file()
    assert not (session / "STOP").exists()


def test_interrupted_resume_transaction_reuses_only_its_original_token(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project, master, session, token = _stopped_autorun_fixture(tmp_path)
    stop_marker = session / "controller" / "stop-requests" / token
    resume_dir = session / "controller" / "resume-in-progress"
    resume_marker = resume_dir / token
    os.replace(stop_marker, resume_marker)
    (session / "STOP").unlink(missing_ok=True)
    state = autorun_status(session)
    state["stop_requested"] = True
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")
    monkeypatch.setattr(
        autorun_module,
        "execute_agent_request",
        lambda _path: pytest.fail("transaction recovery dispatched a model"),
    )

    assert _explicit_resume_runner(project, master, session, token).run() == session
    resumed = autorun_status(session)
    consumed = session / "controller" / "consumed-stop-requests" / token
    ledger = session / "controller" / "stop-token-ledger" / token
    assert resumed["status"] == "paused"
    assert resumed["stop_requested"] is False
    assert not resume_marker.exists()
    assert consumed.is_file()
    assert os.path.samefile(consumed, ledger)


def test_stop_arriving_during_explicit_resume_remains_pending(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project, master, session, token = _stopped_autorun_fixture(tmp_path)
    runner = _explicit_resume_runner(project, master, session, token)
    original_mark_running = runner._mark_running
    later_token: str | None = None

    def stop_before_running(*, explicit_stopped_resume: bool = False) -> bool:
        nonlocal later_token
        response = request_autorun_stop(session)
        later_token = response.rsplit(" ", 1)[-1]
        return original_mark_running(explicit_stopped_resume=explicit_stopped_resume)

    monkeypatch.setattr(runner, "_mark_running", stop_before_running)
    monkeypatch.setattr(
        autorun_module,
        "execute_agent_request",
        lambda _path: pytest.fail("pending stop dispatched a model"),
    )

    assert runner.run() == session
    state = autorun_status(session)
    assert state["status"] == "stopped"
    assert state["pid"] is None
    assert state["stop_requested"] is True
    assert later_token is not None
    assert (session / "controller" / "stop-requests" / later_token).is_file()
    assert not (session / "STOP").exists()
    assert not (session / "controller" / "stop-requests" / token).exists()
    events = (session / "events.jsonl").read_text(encoding="utf-8")
    assert "autorun controller explicitly resumed stopped session" not in events


def test_multiple_stop_tokens_are_consumed_one_at_a_time(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project, master, session, first_token = _stopped_autorun_fixture(tmp_path)
    second_token = request_autorun_stop(session).rsplit(" ", 1)[-1]
    monkeypatch.setattr(
        autorun_module,
        "execute_agent_request",
        lambda _path: pytest.fail("multiple pending stops dispatched a model"),
    )

    assert (
        _explicit_resume_runner(project, master, session, first_token).run() == session
    )
    after_first = autorun_status(session)
    assert after_first["status"] == "stopped"
    assert after_first["stop_requested"] is True
    assert not (session / "controller" / "stop-requests" / first_token).exists()
    assert (session / "controller" / "consumed-stop-requests" / first_token).is_file()
    assert (session / "controller" / "stop-requests" / second_token).is_file()

    assert (
        _explicit_resume_runner(project, master, session, second_token).run() == session
    )
    after_second = autorun_status(session)
    assert after_second["status"] == "paused"
    assert after_second["stop_requested"] is False
    assert (session / "controller" / "consumed-stop-requests" / second_token).is_file()


def test_interrupted_resume_preserves_a_later_pending_token(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project, master, session, first_token = _stopped_autorun_fixture(tmp_path)
    first_pending = session / "controller" / "stop-requests" / first_token
    first_transaction = session / "controller" / "resume-in-progress" / first_token
    os.replace(first_pending, first_transaction)
    second_token = request_autorun_stop(session).rsplit(" ", 1)[-1]
    monkeypatch.setattr(
        autorun_module,
        "execute_agent_request",
        lambda _path: pytest.fail("interrupted resume dispatched a model"),
    )

    assert (
        _explicit_resume_runner(project, master, session, first_token).run() == session
    )
    after_first = autorun_status(session)
    assert after_first["status"] == "stopped"
    assert not first_transaction.exists()
    assert (session / "controller" / "stop-requests" / second_token).is_file()

    assert (
        _explicit_resume_runner(project, master, session, second_token).run() == session
    )
    assert autorun_status(session)["status"] == "paused"


@pytest.mark.parametrize(
    ("invalid_state", "message"),
    [
        ("running", "requires a stopped session"),
        ("recovering", "requires a stopped session"),
        ("paused", "requires a stopped session"),
        ("retained_owner", "requires no retained owner"),
        ("active_work", "requires no active retained work"),
        ("foreign_project", "different project"),
        ("foreign_prompt", "different Master Prompt"),
        ("complete", "completed autorun session cannot be resumed"),
    ],
)
def test_explicit_resume_rejects_ineligible_session_without_mutation(
    tmp_path: Path,
    invalid_state: str,
    message: str,
) -> None:
    project, master, session, token = _stopped_autorun_fixture(tmp_path)
    state_path = session / "state.json"
    state = autorun_status(session)
    if invalid_state in {"running", "recovering", "paused"}:
        state["status"] = invalid_state
    elif invalid_state == "retained_owner":
        state["pid"] = os.getpid()
    elif invalid_state == "active_work":
        state["active_round"] = 4
    elif invalid_state == "foreign_project":
        state["project_manifest"] = "/foreign/project.toml"
    elif invalid_state == "foreign_prompt":
        state["master_prompt"] = "/foreign/MASTER_PROMPT.md"
    else:
        state["active_strategy"]["status"] = "complete"
    state_path.write_text(json.dumps(state), encoding="utf-8")
    state_before = state_path.read_bytes()
    stop_before = os.path.lexists(session / "STOP")
    marker = session / "controller" / "stop-requests" / token
    marker_before = marker.read_bytes()

    with pytest.raises(AutoRunError, match=message):
        _explicit_resume_runner(project, master, session, token).run()

    assert state_path.read_bytes() == state_before
    assert os.path.lexists(session / "STOP") is stop_before
    assert marker.read_bytes() == marker_before


def test_explicit_resume_lock_contention_preserves_stop(
    tmp_path: Path,
) -> None:
    project, master, session, token = _stopped_autorun_fixture(tmp_path)
    state_path = session / "state.json"
    state_before = state_path.read_bytes()
    stop_before = os.path.lexists(session / "STOP")
    marker = session / "controller" / "stop-requests" / token

    with (
        campaign_run_lock(session / "controller"),
        pytest.raises(AutoRunError, match="another autorun controller owns"),
    ):
        _explicit_resume_runner(project, master, session, token).run()

    assert state_path.read_bytes() == state_before
    assert os.path.lexists(session / "STOP") is stop_before
    assert marker.is_file()


def _write_active_conductor_request(
    tmp_path: Path,
    *,
    attempt: int = 7,
) -> Path:
    session = tmp_path / "autorun-runs" / "session-fixture"
    (session / "controller").mkdir(parents=True)
    round_dir = session / "rounds" / f"round-{attempt:05d}"
    round_dir.mkdir(parents=True)
    prompt = round_dir / "prompt.md"
    prompt.write_text("Frozen conductor prompt.\n", encoding="utf-8")
    strategy = _contract()
    now = datetime.now(UTC).isoformat()
    (session / "state.json").write_text(
        json.dumps(
            {
                "schema_version": 3,
                "session_id": "session-fixture",
                "status": "running",
                "created_at": now,
                "updated_at": now,
                "heartbeat_at": now,
                "next_reflection_at": now,
                "pid": os.getpid(),
                "round_count": 0,
                "attempt_count": attempt,
                "active_round": attempt,
                "active_prompt": str(prompt),
                "active_strategy": strategy,
            }
        ),
        encoding="utf-8",
    )
    request = round_dir / "request.json"
    request.write_text(
        json.dumps(
            {
                "role_id": "autorun_conductor",
                "attempt": attempt,
                "run_dir": str(session),
                "prompt": str(prompt),
                "omp": "omp",
                "workspace": str(tmp_path),
                "output": str(round_dir / "output.md"),
                "stdout_log": str(round_dir / "stdout.log"),
                "stderr_log": str(round_dir / "stderr.log"),
                "receipt": str(round_dir / "receipt.json"),
                "tools": [],
                "model": None,
                "thinking": None,
                "max_time": 60,
                "conductor_claim_context": {
                    "schema_version": 1,
                    "session_id": "session-fixture",
                    "attempt": attempt,
                    "strategy_id": strategy["strategy_id"],
                    "strategy_revision": strategy["revision"],
                    "prompt_sha256": hashlib.sha256(prompt.read_bytes()).hexdigest(),
                },
            }
        ),
        encoding="utf-8",
    )
    return request


def test_autorun_report_cli_emits_one_strict_bound_marker(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    request = _write_active_conductor_request(tmp_path)
    state_path = request.parents[2] / "state.json"
    request_before = request.read_bytes()
    state_before = state_path.read_bytes()

    with campaign_run_lock(request.parents[2] / "controller"):
        assert (
            cli_main(
                [
                    "autorun-report",
                    "--request",
                    str(request),
                    "--checkpoint-id",
                    "first_check",
                    "--progress-class",
                    "meaningful",
                    "--summary",
                    "The retained consumer was verified.",
                    "--evidence",
                    "proof/retained-consumer",
                ]
            )
            == 0
        )

    lines = capsys.readouterr().out.splitlines()
    assert len(lines) == 1
    claim = AutoRunRunner._parse_conductor_claim(lines[0])
    assert claim == {
        "schema_version": 1,
        "strategy_id": "strategy-00001",
        "strategy_revision": 1,
        "checkpoint_id": "first_check",
        "progress_class": "meaningful",
        "summary": "The retained consumer was verified.",
        "evidence": "proof/retained-consumer",
    }
    receipt = json.loads(
        (request.parent / "conductor-claim-emission.json").read_text(encoding="utf-8")
    )
    assert receipt["claim"] == claim
    assert set(claim) == {
        "schema_version",
        "strategy_id",
        "strategy_revision",
        "checkpoint_id",
        "progress_class",
        "summary",
        "evidence",
    }
    assert request.read_bytes() == request_before
    assert state_path.read_bytes() == state_before


def test_controller_accepts_strict_claim_without_emission_receipt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _runner(tmp_path)
    adjudication_prompts: list[str] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        role = request["role_id"]
        if role == "autorun_strategy_reflection":
            output = _proposal()
        elif role == "autorun_conductor":
            output = _claim()
        elif role == "autorun_progress_adjudicator":
            adjudication_prompts.append(
                Path(request["prompt"]).read_text(encoding="utf-8")
            )
            output = _adjudication()
        else:
            raise AssertionError(f"unexpected role {role}")
        Path(request["output"]).write_text(output + "\n", encoding="utf-8")
        return 0

    monkeypatch.setattr(autorun_module, "execute_agent_request", execute)
    session = runner.run()
    state = autorun_status(session)

    assert not (session / "rounds/round-00001/conductor-claim-emission.json").exists()
    assert state["last_progress_claim"] == "meaningful"
    assert state["active_strategy"]["checkpoints"][0]["status"] == "satisfied"
    assert len(adjudication_prompts) == 1
    assert "Identity mismatch: false" in adjudication_prompts[0]


def test_last_round_claim_reads_strict_output_without_emission_receipt(
    tmp_path: Path,
) -> None:
    output = tmp_path / "round-00001/output.md"
    output.parent.mkdir()
    output.write_text(_claim() + "\n", encoding="utf-8")

    assert autorun_module._last_round_claim({"last_output": str(output)}) == (
        AutoRunRunner._parse_conductor_claim(output.read_text(encoding="utf-8"))
    )


def test_identity_mismatched_report_retains_drift_adjudication(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _runner(tmp_path)
    adjudication_prompts: list[str] = []

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        role = request["role_id"]
        if role == "autorun_strategy_reflection":
            output = _proposal()
        elif role == "autorun_conductor":
            output = _claim(strategy_id="strategy-99999")
        elif role == "autorun_progress_adjudicator":
            adjudication_prompts.append(
                Path(request["prompt"]).read_text(encoding="utf-8")
            )
            output = _adjudication(
                alignment="drifted",
                checkpoint_id=None,
                checkpoint_result="n/a",
            )
        else:
            raise AssertionError(f"unexpected role {role}")
        Path(request["output"]).write_text(output + "\n", encoding="utf-8")
        return 0

    monkeypatch.setattr(autorun_module, "execute_agent_request", execute)
    state = autorun_status(runner.run())

    assert state["last_progress_claim"] == "meaningful"
    assert state["active_strategy"]["status"] == "drifted"
    assert state["strategy_change_required"] is True
    assert len(adjudication_prompts) == 1
    assert "Identity mismatch: true" in adjudication_prompts[0]


@pytest.mark.parametrize(
    "mismatch",
    [
        "stale_revision",
        "foreign_strategy",
        "foreign_round",
        "modified_prompt",
        "dead_controller",
        "stale_heartbeat",
        "missing_controller_lock",
        "future_heartbeat",
        "foreign_lock_owner",
    ],
)
def test_autorun_report_rejects_noncurrent_frozen_invocation(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    mismatch: str,
) -> None:
    request_path = _write_active_conductor_request(tmp_path)
    request = json.loads(request_path.read_text(encoding="utf-8"))
    session = Path(request["run_dir"])
    state_path = session / "state.json"
    state = json.loads(state_path.read_text(encoding="utf-8"))
    if mismatch == "stale_revision":
        state["active_strategy"]["revision"] = 2
    elif mismatch == "foreign_strategy":
        request["conductor_claim_context"]["strategy_id"] = "strategy-99999"
    elif mismatch == "foreign_round":
        request["conductor_claim_context"]["attempt"] += 1
    elif mismatch == "modified_prompt":
        Path(request["prompt"]).write_text(
            "Changed after the invocation was frozen.\n", encoding="utf-8"
        )
    elif mismatch == "dead_controller":
        state["pid"] = 2**31 - 1
    elif mismatch == "stale_heartbeat":
        state["heartbeat_at"] = "2020-01-01T00:00:00Z"
    elif mismatch == "future_heartbeat":
        state["heartbeat_at"] = (datetime.now(UTC) + timedelta(days=1)).isoformat()
    elif mismatch == "foreign_lock_owner":
        state["pid"] = os.getppid()
    state_path.write_text(json.dumps(state), encoding="utf-8")
    request_path.write_text(json.dumps(request), encoding="utf-8")

    lock_scope = (
        nullcontext()
        if mismatch == "missing_controller_lock"
        else campaign_run_lock(session / "controller")
    )
    with lock_scope, pytest.raises(SystemExit) as raised:
        cli_main(
            [
                "autorun-report",
                "--request",
                str(request_path),
                "--no-checkpoint",
                "--progress-class",
                "incremental",
                "--summary",
                "Verified work.",
                "--evidence",
                "retained evidence",
            ]
        )

    assert raised.value.code == 2
    captured = capsys.readouterr()
    assert "CONDUCTOR_RESULT_JSON:" not in captured.out
    assert "CONDUCTOR_RESULT_JSON:" not in captured.err
    if mismatch == "missing_controller_lock":
        assert not (session / "controller/.campaign.lock").exists()


def test_autorun_report_rejects_invalid_claim_content_without_marker(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    request = _write_active_conductor_request(tmp_path)

    with (
        campaign_run_lock(request.parents[2] / "controller"),
        pytest.raises(SystemExit) as raised,
    ):
        cli_main(
            [
                "autorun-report",
                "--request",
                str(request),
                "--checkpoint-id",
                "unknown_checkpoint",
                "--progress-class",
                "meaningful",
                "--summary",
                "Verified work.",
                "--evidence",
                "retained evidence",
            ]
        )

    assert raised.value.code == 2
    assert "CONDUCTOR_RESULT_JSON:" not in capsys.readouterr().out


def test_legacy_conductor_report_remains_rejected() -> None:
    legacy_report = (
        'CONDUCTOR_RESULT_JSON: {"round":435,"strategy":"strategy-00095",'
        '"revision":1,"checkpoint_id":"ambient_transport_sharp_local_increment",'
        '"status":"blocked","progress_class":"meaningful","summary":"Verified work.",'
        '"artifacts":["proof/CMVSmoothAmbientTransport.lean"],'
        '"verification":["lake build: success"],'
        '"blockers":["The coefficient-one estimate remains unavailable."],'
        '"next_action":"Prove the localized transport theorem."}'
    )

    assert AutoRunRunner._parse_conductor_claim(legacy_report) is None


def test_first_round_selects_strategy_before_sol_and_adjudicates_afterward(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _runner(tmp_path)
    requests: list[dict[str, object]] = []

    def execute(path: Path) -> int:
        requests.append(json.loads(path.read_text(encoding="utf-8")))
        return successful_agent(path)

    monkeypatch.setattr(autorun_module, "execute_agent_request", execute)
    session = runner.run()
    state = autorun_status(session)

    assert [item["role_id"] for item in requests] == [
        "autorun_strategy_reflection",
        "autorun_conductor",
        "autorun_progress_adjudicator",
    ]
    assert requests[0]["model"] == "openai-codex/gpt-6-astra"
    assert requests[0]["tools"] == ["read"]
    assert requests[1]["model"] == "openai-codex/gpt-5.6-sol"
    assert requests[1]["tools"] == ["read", "write"]
    claim_context = requests[1]["conductor_claim_context"]
    assert claim_context["session_id"] == state["session_id"]
    assert claim_context["attempt"] == 1
    assert claim_context["strategy_id"] == "strategy-00001"
    assert claim_context["strategy_revision"] == 1
    assert (
        claim_context["prompt_sha256"]
        == hashlib.sha256(Path(requests[1]["prompt"]).read_bytes()).hexdigest()
    )
    assert requests[2]["model"] == "openai-codex/gpt-5.6-terra"
    assert requests[2]["tools"] == ["read"]
    assert state["schema_version"] == 3
    assert state["active_strategy"]["schema_version"] == 2
    assert state["active_strategy"]["checkpoints"][0]["status"] == "satisfied"
    assert state["adjudication_history"][0]["execution"] == 1


def test_invalid_strategy_json_fails_closed_without_launching_sol(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _runner(tmp_path)
    requests: list[dict[str, object]] = []

    def execute(path: Path) -> int:
        request = json.loads(path.read_text(encoding="utf-8"))
        requests.append(request)
        Path(request["output"]).write_text(
            "STRATEGY_PROPOSAL_JSON: {bad}\n", encoding="utf-8"
        )
        return 0

    monkeypatch.setattr(autorun_module, "execute_agent_request", execute)
    state = autorun_status(runner.run())
    assert [item["role_id"] for item in requests] == ["autorun_strategy_reflection"]
    assert state["active_strategy"] is None
    assert state["active_prompt"] is None
    assert state["active_model"] is None
    assert "invalid JSON" in state["last_error"]


def test_governor_selects_review_and_checkpoint_offsets_below_operator_ceiling(
    tmp_path: Path,
) -> None:
    runner = _runner(tmp_path)
    state = _strategy_state()
    proposal, errors = runner._parse_strategy_proposal(
        _proposal(review_after=7, checkpoint_after=4),
        state=state,
        max_strategy_executions=10,
    )
    assert errors == []
    assert proposal is not None
    contract = runner._materialize_strategy_contract(1, state, proposal)
    assert contract["review_due_execution"] == 7
    assert contract["checkpoints"][0]["due_execution"] == 4
    state["active_strategy"] = contract
    assert not runner._strategy_requires_review(state)


def test_checkpoint_or_adaptive_review_due_triggers_reflection_not_falsification() -> (
    None
):
    strategy = _contract(review_due=2, checkpoint_due=3)
    state = _strategy_state(strategy, execution=2)
    assert AutoRunRunner._strategy_requires_review(state)
    assert strategy["status"] == "active"
    strategy["review_due_execution"] = 5
    strategy["checkpoints"][0]["due_execution"] = 2
    assert AutoRunRunner._strategy_requires_review(state)
    assert strategy["checkpoints"][0]["status"] == "pending"


def test_continued_strategy_keeps_deadline_and_prompt_identity(
    tmp_path: Path,
) -> None:
    runner = _runner(tmp_path)
    runner.session_dir = tmp_path
    strategy = _contract(review_due=2, checkpoint_due=2, checkpoint_status="advanced")
    state = _strategy_state(strategy, execution=2)
    state["adjudication_history"] = [
        {
            "strategy_id": "strategy-00001",
            "strategy_revision": 1,
            "execution": 2,
            "alignment": "aligned",
            "checkpoint_result": "advanced",
        }
    ]
    proposal, errors = runner._parse_strategy_proposal(
        _proposal(
            decision="continue",
            base_strategy_id="strategy-00001",
            base_revision=1,
            review_after=2,
            checkpoint_after=1,
        ),
        state=state,
        max_strategy_executions=100,
    )
    assert errors == []
    assert proposal is not None
    revised = runner._materialize_strategy_contract(3, state, proposal)
    assert revised["strategy_id"] == "strategy-00001"
    assert revised["revision"] == 2
    assert revised["lineage_started_execution"] == 0
    assert revised["hard_deadline_execution"] == 10
    assert state["strategy_history"][-1]["checkpoints"][0]["status"] == "revised"
    state["active_strategy"] = revised
    prompt = runner._round_prompt(3, state, "Prove the exact target.")
    assert "uv run agentic-lean-math-assistant autorun-report" in prompt
    assert f'--request "{tmp_path / "rounds/round-00003/request.json"}"' in prompt
    assert '--checkpoint-id "first_check"' in prompt
    assert "Never construct the\nmarker manually." in prompt
    assert f'"strategy_id": "{revised["strategy_id"]}"' in prompt
    assert f'"revision": {revised["revision"]}' in prompt
    assert "CONDUCTOR_RESULT_JSON: {" not in prompt


@pytest.mark.parametrize("checkpoint_result", ["advanced", "satisfied"])
def test_overdue_soft_gate_requires_current_revision_aligned_progress(
    tmp_path: Path,
    checkpoint_result: str,
) -> None:
    runner = _runner(tmp_path)
    strategy = _contract(
        revision=2,
        accepted_execution=1,
        review_due=2,
        checkpoint_due=2,
    )
    state = _strategy_state(strategy, execution=2)
    proposal_text = _proposal(
        decision="continue",
        base_strategy_id="strategy-00001",
        base_revision=2,
        review_after=1,
        checkpoint_after=1,
    )

    assert "- Replacement is mandatory: true" in runner._strategy_reflection_prompt(
        state, "Prove the exact target."
    )
    proposal, errors = AutoRunRunner._parse_strategy_proposal(
        proposal_text,
        state=state,
        max_strategy_executions=100,
    )
    assert proposal is None
    assert any("replacement is required" in item for item in errors)

    state["adjudication_history"] = [
        {
            "strategy_id": "strategy-00001",
            "strategy_revision": 1,
            "execution": 2,
            "alignment": "aligned",
            "checkpoint_result": checkpoint_result,
        }
    ]
    assert "- Replacement is mandatory: true" in runner._strategy_reflection_prompt(
        state, "Prove the exact target."
    )
    proposal, errors = AutoRunRunner._parse_strategy_proposal(
        proposal_text,
        state=state,
        max_strategy_executions=100,
    )
    assert proposal is None
    assert any("replacement is required" in item for item in errors)

    state["adjudication_history"].append(
        {
            "strategy_id": "strategy-00001",
            "strategy_revision": 2,
            "execution": 2,
            "alignment": "aligned",
            "checkpoint_result": checkpoint_result,
        }
    )
    assert "- Replacement is mandatory: false" in runner._strategy_reflection_prompt(
        state, "Prove the exact target."
    )
    proposal, errors = AutoRunRunner._parse_strategy_proposal(
        proposal_text,
        state=state,
        max_strategy_executions=100,
    )
    assert errors == []
    assert proposal is not None


def test_hard_lineage_deadline_cannot_be_extended_by_continue() -> None:
    strategy = _contract(hard_deadline=2, review_due=2, checkpoint_due=2)
    state = _strategy_state(strategy, execution=2)
    state["adjudication_history"] = [
        {
            "strategy_id": "strategy-00001",
            "strategy_revision": 1,
            "execution": 2,
            "alignment": "aligned",
            "checkpoint_result": "advanced",
        }
    ]
    proposal, errors = AutoRunRunner._parse_strategy_proposal(
        _proposal(
            decision="continue",
            base_strategy_id="strategy-00001",
            base_revision=1,
            review_after=1,
            checkpoint_after=1,
        ),
        state=state,
        max_strategy_executions=100,
    )
    assert proposal is None
    assert any("replacement is required" in item for item in errors)


def test_expired_lineage_replacement_gets_fresh_operator_ceiling(
    tmp_path: Path,
) -> None:
    runner = _runner(tmp_path)
    strategy = _contract(
        hard_deadline=2,
        review_due=2,
        checkpoint_due=2,
        status="expired",
    )
    state = _strategy_state(strategy, execution=2)
    state["strategy_change_required"] = True
    proposal, errors = AutoRunRunner._parse_strategy_proposal(
        _proposal(
            decision="change_course",
            base_strategy_id="strategy-00001",
            base_revision=1,
            review_after=75,
            checkpoint_after=50,
        ),
        state=state,
        max_strategy_executions=100,
    )
    assert errors == []
    assert proposal is not None
    replacement = runner._materialize_strategy_contract(3, state, proposal)
    assert replacement["hard_deadline_execution"] == 102
    assert replacement["review_due_execution"] == 77
    assert replacement["checkpoints"][0]["due_execution"] == 52


def test_change_course_allocates_new_lineage_and_archives_old_contract(
    tmp_path: Path,
) -> None:
    runner = _runner(tmp_path)
    strategy = _contract(status="falsified")
    state = _strategy_state(strategy, execution=4)
    state["strategy_change_required"] = True
    proposal, errors = runner._parse_strategy_proposal(
        _proposal(
            decision="change_course",
            base_strategy_id="strategy-00001",
            base_revision=1,
        ),
        state=state,
        max_strategy_executions=100,
    )
    assert errors == []
    assert proposal is not None
    replacement = runner._materialize_strategy_contract(5, state, proposal)
    assert replacement["strategy_id"] == "strategy-00002"
    assert replacement["revision"] == 1
    assert replacement["lineage_started_execution"] == 4
    assert replacement["hard_deadline_execution"] == 104
    assert state["strategy_history"][-1]["status"] == "falsified"


@pytest.mark.parametrize(
    ("alignment", "checkpoint_result", "stop_id", "expected"),
    [
        ("drifted", "n/a", None, "drifted"),
        ("falsified", "falsified", None, "falsified"),
        ("falsified", "n/a", "method_breaks", "falsified"),
    ],
)
def test_falsification_drift_and_triggered_stop_condition_each_require_change(
    alignment: str,
    checkpoint_result: str,
    stop_id: str | None,
    expected: str,
) -> None:
    checkpoint_id = "first_check" if checkpoint_result == "falsified" else None
    parsed = AutoRunRunner._parse_progress_adjudication(
        _adjudication(
            alignment=alignment,
            checkpoint_id=checkpoint_id,
            checkpoint_result=checkpoint_result,
            stop_id=stop_id,
        ),
        strategy=_contract(),
    )
    assert parsed is not None
    state = _strategy_state(_contract(), execution=1)
    AutoRunRunner._apply_adjudication_to_strategy(
        state, parsed, attempt=1, execution=1, artifact="adjudication.json"
    )
    assert state["strategy_change_required"] is True
    assert state["active_strategy"]["status"] == expected


@pytest.mark.parametrize(
    "text",
    [
        _adjudication(revision=2),
        _adjudication(checkpoint_id="unknown"),
        _adjudication(checkpoint_id="first_check", checkpoint_result="n/a"),
    ],
)
def test_invalid_or_wrong_strategy_adjudication_cannot_advance_checkpoint(
    text: str,
) -> None:
    strategy = _contract()
    strategy["checkpoints"].append(
        {
            "id": "second_check",
            "due_execution": 4,
            "observable": "A later obligation is verified.",
            "status": "pending",
            "last_result": None,
            "last_adjudication_execution": None,
        }
    )
    assert AutoRunRunner._parse_progress_adjudication(text, strategy=strategy) is None
    assert strategy["checkpoints"][0]["status"] == "pending"


def test_round_adjudication_prompt_matches_earliest_checkpoint_parser_order(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = _runner(tmp_path)
    runner.session_dir = tmp_path
    strategy = _contract(revision=2)
    strategy["checkpoints"].append(
        {
            "id": "second_check",
            "due_execution": 4,
            "observable": "A later obligation is verified.",
            "status": "pending",
            "last_result": None,
            "last_adjudication_execution": None,
        }
    )
    state = _strategy_state(strategy, execution=1)
    monkeypatch.setattr(runner, "_state", lambda: state)
    monkeypatch.setattr(runner, "_save", lambda _state: None)

    round_dir = tmp_path / "round-00302"
    round_dir.mkdir()
    conductor_output = round_dir / "response.md"
    conductor_output.write_text(
        _claim(revision=2, checkpoint_id="second_check"), encoding="utf-8"
    )

    def execute(request_path: Path) -> int:
        request = json.loads(request_path.read_text(encoding="utf-8"))
        Path(request["output"]).write_text(
            _adjudication(revision=2, checkpoint_id="first_check"),
            encoding="utf-8",
        )
        return 0

    monkeypatch.setattr(runner, "_execute_with_heartbeat", execute)
    adjudication, _, _ = runner._run_progress_adjudication(
        302,
        round_dir,
        conductor_output,
        [],
        AutoRunRunner._parse_conductor_claim(
            conductor_output.read_text(encoding="utf-8")
        ),
    )

    assert adjudication is not None
    assert adjudication.checkpoint_id == "first_check"
    prompt = (round_dir / "progress-adjudication-prompt.md").read_text(encoding="utf-8")
    assert "Active strategy ID: `strategy-00001`" in prompt
    assert "Active strategy revision: `2`" in prompt
    assert "Earliest admissible checkpoint ID: `first_check`" in prompt
    assert (
        'Earliest admissible checkpoint observable: "The named obligation is verified."'
        in prompt
    )
    assert '`checkpoint_id="first_check"`' in prompt
    normalized_prompt = " ".join(prompt.split())
    assert (
        '`progress_class="complete"` and `alignment="complete"` each mean that '
        "the entire Living Master Prompt is complete"
    ) in normalized_prompt
    assert (
        "If all strategy checkpoints are complete but any global obligation in "
        'the Living Master Prompt remains, use `progress_class="meaningful"`, '
        'not `"complete"`'
    ) in normalized_prompt
    assert (
        AutoRunRunner._parse_progress_adjudication(
            _adjudication(revision=2, checkpoint_id="second_check"),
            strategy=strategy,
        )
        is None
    )


def test_unchanged_checkpoint_remains_pending_and_overdue() -> None:
    strategy = _contract(review_due=2, checkpoint_due=1)
    parsed = AutoRunRunner._parse_progress_adjudication(
        _adjudication(checkpoint_result="unchanged"),
        strategy=strategy,
    )
    assert parsed is not None
    state = _strategy_state(strategy, execution=1)
    AutoRunRunner._apply_adjudication_to_strategy(
        state, parsed, attempt=1, execution=1, artifact="adjudication.json"
    )
    assert state["active_strategy"]["checkpoints"][0]["status"] == "pending"
    assert AutoRunRunner._strategy_requires_review(state)


def test_only_aligned_indexed_advanced_or_satisfied_result_records_evidence() -> None:
    state = _strategy_state(_contract(accepted_execution=1), execution=2)
    state["adjudication_history"] = [
        {
            "strategy_id": "strategy-00001",
            "strategy_revision": 1,
            "execution": 2,
            "alignment": "drifted",
            "checkpoint_result": "advanced",
        }
    ]
    assert not AutoRunRunner._has_aligned_revision_progress(state)
    state["adjudication_history"][0]["alignment"] = "aligned"
    assert AutoRunRunner._has_aligned_revision_progress(state)


def test_reflection_trajectory_contains_adjudicated_delta_not_conductor_claim(
    tmp_path: Path,
) -> None:
    runner = _runner(tmp_path)
    runner.session_dir = tmp_path
    state = _strategy_state(_contract(), execution=1)
    state["adjudication_history"] = [
        {
            "attempt": 1,
            "execution": 1,
            "strategy_id": "strategy-00001",
            "strategy_revision": 1,
            "progress_class": "meaningful",
            "alignment": "aligned",
            "checkpoint_id": "first_check",
            "checkpoint_result": "advanced",
            "reason": "independent reason",
            "verified_scope_delta": "independent delta",
        }
    ]
    history = runner._recent_progress_history(state)
    assert "independent delta" in history
    assert "conductor claim" not in history


def test_repeated_execution_failures_never_route_conductor_to_governor_model(
    tmp_path: Path,
) -> None:
    runner = _runner(tmp_path)
    assert runner._conductor_model({"consecutive_execution_failures": 20}) == (
        "openai-codex/gpt-5.6-sol",
        "primary",
    )


def test_complete_adjudication_stops_without_another_reflection() -> None:
    parsed = AutoRunRunner._parse_progress_adjudication(
        _adjudication(
            progress_class="complete",
            alignment="complete",
            checkpoint_id=None,
            checkpoint_result="n/a",
        ),
        strategy=_contract(),
    )
    assert parsed is not None
    state = _strategy_state(_contract(), execution=1)
    state["status"] = "running"
    AutoRunRunner._apply_adjudication_to_strategy(
        state, parsed, attempt=1, execution=1, artifact="adjudication.json"
    )
    assert state["status"] == "stopped"
    assert state["active_strategy"]["status"] == "complete"


def _retained_state(schema_version: int) -> dict[str, object]:
    return {
        "schema_version": schema_version,
        "session_id": "session",
        "project_manifest": "/project/project.toml",
        "master_prompt": "/project/MASTER_PROMPT.md",
        "master_prompt_sha256": "digest",
        "status": "paused",
        "pid": None,
        "created_at": "2026-01-01T00:00:00Z",
        "updated_at": "2026-01-01T00:00:00Z",
        "heartbeat_at": "2026-01-01T00:00:00Z",
        "next_reflection_at": "2026-01-01T01:00:00Z",
        "reflection_minutes": 120,
        "reflection_round_minutes": 15,
        "round_minutes": 90,
        "round_count": 1,
        "attempt_count": 2,
        "reflection_count": 1,
        "meaningful_round_count": 1,
        "incremental_round_count": 0,
        "blocked_round_count": 0,
        "complete_round_count": 0,
        "unclassified_round_count": 0,
        "controller_failure_count": 0,
        "agent_execution_failure_count": 1,
        "verification_failure_count": 0,
        "strategy_gate_failure_count": 0,
        "mathematical_blocker_count": 0,
        "consecutive_execution_failures": 0,
        "last_failure_class": None,
        "active_strategy": {"schema_version": 1, "status": "active"},
        "strategy_history": [{"raw": "retained"}],
        "last_progress_claim": "meaningful",
        "last_progress_adjudication": None,
        "last_adjudication_review": "/session/adjudication.md",
        "last_adjudication_model": "analysis",
        "last_progress_class": "meaningful",
        "last_strategy_decision": "continue",
        "last_strategy_review": "/session/reflection.md",
        "last_strategy_round": 1,
        "strategy_change_required": False,
        "next_retry_at": None,
        "repeated_output_count": 0,
        "last_output_sha256": "digest",
        "last_output": "/session/output.md",
        "last_receipt": "/session/receipt.json",
        "active_round": None,
        "active_prompt": None,
        "active_model": None,
        "active_model_route": None,
        "active_strategy_pass": 2,
        "last_model": "primary",
        "last_reflection_model": "governor",
        "last_error": None,
        "stop_requested": False,
    }


@pytest.mark.parametrize("schema_version", [1, 2])
def test_schema_1_and_2_sessions_upgrade_to_3_and_reflect_before_execution(
    tmp_path: Path, schema_version: int
) -> None:
    session = tmp_path / f"schema-{schema_version}"
    (session / "rounds" / "round-00002").mkdir(parents=True)
    retained = _retained_state(schema_version)
    if schema_version == 1:
        retained.pop("attempt_count")
        retained["consecutive_failures"] = retained.pop(
            "consecutive_execution_failures"
        )
    (session / "state.json").write_text(json.dumps(retained), encoding="utf-8")
    state = AutoRunRunner._read_state_from(session)
    assert state["schema_version"] == 3
    assert state["round_count"] == 1
    assert state["attempt_count"] == 2
    assert state["last_output"] == "/session/output.md"
    assert state["active_strategy"] is None
    assert state["strategy_change_required"] is True
    assert "active_strategy_pass" not in state
    if schema_version == 2:
        assert state["legacy_strategy_state"]["active_strategy"]["schema_version"] == 1
    else:
        assert state["legacy_strategy_state"]["active_strategy"] is None


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("revision", True),
        ("status", "ready"),
        ("strategy_id", "bad id"),
        ("review_due_execution", 0),
        ("hard_deadline_execution", 101),
        ("checkpoints", {}),
        ("stop_conditions", {}),
    ],
)
def test_malformed_schema_3_nested_contract_is_rejected(
    field: str, value: object
) -> None:
    strategy = _contract()
    strategy[field] = value
    with pytest.raises(AutoRunError):
        AutoRunRunner._validate_strategy_contract(
            strategy, completed_execution=0, require_active=False
        )


def test_resume_preserves_absolute_soft_and_hard_gate_deadlines() -> None:
    strategy = _contract(review_due=7, checkpoint_due=5, hard_deadline=10)
    AutoRunRunner._validate_strategy_contract(
        strategy, completed_execution=3, require_active=True
    )
    assert strategy["review_due_execution"] == 7
    assert strategy["checkpoints"][0]["due_execution"] == 5
    assert strategy["hard_deadline_execution"] == 10


def test_status_renders_persisted_contract_instead_of_raw_governor_markers() -> None:
    report = "\n".join(
        autorun_module._strategy_report_sections(
            _strategy_state(_contract(review_due=7, checkpoint_due=5))
        )
    )
    assert "strategy-00001 revision 1" in report
    assert "first_check at execution 5" in report
    assert "Due at successful execution 7" in report
    assert "hard deadline 10" in report


def test_generic_governor_conductor_and_adjudicator_prompts_have_no_project_vocabulary(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    master_text = "LIVING CONTRACT SENTINEL"
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest, master_text)
    runner = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(
            master_prompt=master,
            reflection_minutes=120,
            round_minutes=1,
            retry_delay_seconds=0,
            max_rounds=1,
        ),
    )
    prompts: list[str] = []

    def execute(path: Path) -> int:
        request = json.loads(path.read_text(encoding="utf-8"))
        prompts.append(Path(request["prompt"]).read_text(encoding="utf-8"))
        return successful_agent(path)

    monkeypatch.setattr(autorun_module, "execute_agent_request", execute)
    runner.run()
    assert len(prompts) == 3
    for prompt in prompts:
        assert master_text in prompt
        for forbidden in (
            "CMV",
            "Lean",
            "ALMA",
            "Astra",
            "tiny cells",
            "sorry",
            "admit",
            "native_decide",
        ):
            assert forbidden not in prompt


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


def test_follow_monitor_renders_persisted_strategy_contract(
    tmp_path: Path,
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    initializer = AutoRunRunner(
        ProjectSpec.load(manifest),
        AutoRunOptions(master_prompt=master, reflection_minutes=120, round_minutes=1),
    )
    session = initializer._select_session()
    state = autorun_status(session)
    state["status"] = "paused"
    state["attempt_count"] = 1
    state["active_strategy"] = _contract(review_due=7, checkpoint_due=5)
    (session / "state.json").write_text(json.dumps(state), encoding="utf-8")
    output = io.StringIO()

    follow_autorun_status(
        session,
        interval_seconds=0.001,
        output=output,
    )

    rendered = output.getvalue()
    assert "ACTIVE STRATEGY CONTRACT" in rendered
    assert "strategy-00001 revision 1 is active" in rendered
    assert "NEXT CHECKPOINT" in rendered
    assert "first_check at execution 5" in rendered
    assert "ADAPTIVE REVIEW" in rendered
    assert "Due at successful execution 7" in rendered
    assert "IMMUTABLE LINEAGE CEILING" in rendered
    assert "hard deadline 10" in rendered


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
    assert "Controller: recovering and responding." in rendered
    assert "Controller: running and responding." in rendered


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


def test_restore_autorun_workspace_replaces_stale_layout_after_live_panes_render(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    project = ProjectSpec.load(write_autonomy_project(tmp_path))
    session = project.root / "autorun-runs" / "retained-session"
    session.mkdir(parents=True)
    (session.parent / "active.json").write_text(
        json.dumps({"schema_version": 1, "session": str(session)}),
        encoding="utf-8",
    )
    monkeypatch.setattr(
        AutoRunRunner,
        "_read_state_from",
        staticmethod(lambda path: {"status": "running"}),
    )
    actions: list[tuple[object, ...]] = []

    class RecordingHerdr:
        def __init__(self, executable: str) -> None:
            actions.append(("client", executable))

        def list_workspaces(self) -> tuple[HerdrWorkspaceRecord, ...]:
            return (
                HerdrWorkspaceRecord("old", "CMV Autorun Overnight"),
                HerdrWorkspaceRecord("other", "Other"),
            )

        def create_workspace(
            self,
            *,
            cwd: Path,
            label: str,
            focus: bool,
        ) -> HerdrWorkspace:
            actions.append(("create", cwd, label, focus))
            return HerdrWorkspace("new", "new:p1")

        def split_pane(
            self,
            pane_id: str,
            *,
            cwd: Path,
            direction: str,
            ratio: float,
        ) -> str:
            actions.append(("split", pane_id, cwd, direction, ratio))
            return "new:p2" if pane_id == "new:p1" else "new:p3"

        def run_in_pane(self, pane_id: str, command: tuple[str, ...]) -> None:
            actions.append(("run", pane_id, command))

        def wait_for_output(self, pane_id: str, text: str) -> None:
            actions.append(("wait", pane_id, text))

        def close_workspace(self, workspace_id: str) -> None:
            actions.append(("close", workspace_id))

        def focus_workspace(self, workspace_id: str) -> None:
            actions.append(("focus", workspace_id))

    monkeypatch.setattr(autorun_module, "HerdrClient", RecordingHerdr)

    workspace = restore_autorun_workspace(
        project,
        label="CMV Autorun Overnight",
        herdr_executable="/opt/herdr",
        python_executable="/opt/venv/bin/python",
    )

    assert workspace == HerdrWorkspace("new", "new:p1")
    assert ("create", project.root, "CMV Autorun Overnight", False) in actions
    assert (
        "split",
        "new:p1",
        project.root,
        "right",
        0.5,
    ) in actions
    assert ("split", "new:p2", project.root, "down", 0.5) in actions
    pane_commands = {
        action[1]: action[2][3] for action in actions if action[0] == "run"
    }
    assert pane_commands == {
        "new:p1": "autorun-status",
        "new:p2": "autorun-output",
        "new:p3": "autorun-events",
    }
    assert actions.index(("close", "old")) > actions.index(
        ("wait", "new:p3", "RAW EVENTS")
    )
    assert ("close", "other") not in actions
    assert actions[-1] == ("focus", "new")


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
