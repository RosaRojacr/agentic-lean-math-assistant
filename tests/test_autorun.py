from __future__ import annotations

import io
import json
import os
from pathlib import Path

import pytest
from test_autonomy import write_autonomy_project

import agentic_lean_math_assistant.autorun as autorun_module
from agentic_lean_math_assistant.autorun import (
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
    Path(request["output"]).write_text(
        "AUTORUN_RESULT: progress\n"
        "AUTORUN_SUMMARY: completed one checked step\n"
        "AUTORUN_NEXT: prove the next lemma\n",
        encoding="utf-8",
    )
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
    assert state["consecutive_failures"] == 0
    assert state["last_output"].endswith("round-00001/output.md")
    assert "Prove the exact target." in observed_prompts[0]
    assert "choose your own next" in observed_prompts[0]
    assert (session / "events.jsonl").is_file()


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
        "openai-codex/gpt-5.6-sol",
        "openai-codex/gpt-6-astra",
        "openai-codex/gpt-5.6-sol",
    ]
    reflection_request = observed_requests[1]
    assert reflection_request["role_id"] == "autorun_strategy_reflection"
    assert reflection_request["max_time"] == 15 * 60
    assert reflection_request["empty_output_retries"] == 0
    assert reflection_request["tools"] == ["read"]
    assert reflection_request["workspace_executables"] is True
    main_prompt = (session / "rounds" / "round-00002" / "prompt.md").read_text(
        encoding="utf-8"
    )
    assert "Bounded strategy reflection" in main_prompt
    final_state = autorun_status(session)
    assert final_state["reflection_count"] == 1
    assert final_state["last_model"] == "openai-codex/gpt-5.6-sol"
    assert final_state["last_reflection_model"] == "openai-codex/gpt-6-astra"


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

    assert "First objective." in observed_prompts[0]
    assert "Changed objective." in observed_prompts[1]
    assert autorun_status(session)["round_count"] == 2


def test_autorun_recovers_after_failed_agent_round(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = write_autonomy_project(tmp_path)
    master = write_master_prompt(manifest)
    project = ProjectSpec.load(manifest)
    attempts = 0

    def execute(request_path: Path) -> int:
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            return 1
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
            max_rounds=2,
        ),
    )

    session = runner.run()
    state = autorun_status(session)

    assert attempts == 2
    assert state["status"] == "paused"
    assert state["round_count"] == 2
    assert state["consecutive_failures"] == 0
    assert "Previous controller/agent error" in (
        session / "rounds" / "round-00002" / "prompt.md"
    ).read_text(encoding="utf-8")


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
    assert autorun_status(session)["round_count"] == 3
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


def test_persistent_status_monitor_waits_for_controller_resume(
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
    state.update({"status": "paused", "active_round": None})
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
    assert "AUTORUN paused" in rendered
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


def test_live_status_display_replaces_the_current_terminal_line(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class InteractiveStream(io.StringIO):
        def isatty(self) -> bool:
            return True

    monkeypatch.setenv("TERM", "xterm-256color")
    monkeypatch.delenv("NO_COLOR", raising=False)

    output = InteractiveStream()
    display = LiveStatusDisplay(stream=output)

    display.render(status="running", detail="round 3 · agent running")
    display.render(status="running", detail="round 3 · agent running")

    rendered = output.getvalue()
    assert rendered.count("\r\u001b[2K") >= 2
    assert "\u001b[38;2;187;154;247m" in rendered
    assert "\n" not in rendered


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
    assert f"\u001b[{rendered_rows - 1}A" in second_render
    assert second_render.count("\u001b[2K") >= rendered_rows + 1


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
