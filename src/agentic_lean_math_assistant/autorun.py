"""Persistent self-prompting mode for unattended project work."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
from dataclasses import dataclass
from datetime import UTC, datetime, timedelta
from pathlib import Path
from typing import Any, NoReturn, TextIO

from .agent_runner import RunnerInterrupted
from .agent_runner import execute as execute_agent_request
from .artifacts import atomic_write_json, atomic_write_text, utc_now
from .config import ConfigurationError
from .herdr import HerdrClient, HerdrError
from .project import ProjectSpec
from .runtime import CampaignRunError, campaign_run_lock
from .terminal_status import LiveStatusDisplay

_HERDR_PANE_LABELS: dict[str, str] = {}
_HERDR_LABEL_ATTEMPTS: dict[str, tuple[str, float]] = {}
_TERMINAL_TITLES: dict[int, tuple[TextIO, str]] = {}


class AutoRunError(RuntimeError):
    """The persistent autorun controller has an invalid retained state."""


@dataclass(frozen=True, slots=True)
class AutoRunOptions:
    """Runtime settings for one persistent autorun session."""

    master_prompt: Path | None = None
    session: Path | None = None
    reflection_minutes: int = 150
    reflection_round_minutes: int = 15
    round_minutes: int = 90
    retry_delay_seconds: float = 30.0
    max_rounds: int | None = None
    omp: str | None = None
    model: str | None = None
    reflection_model: str | None = None
    thinking: str | None = None
    output: TextIO | None = None


class AutoRunRunner:
    """Repeatedly ask an OMP conductor to choose and execute the next useful task."""

    def __init__(
        self, project: ProjectSpec, options: AutoRunOptions | None = None
    ) -> None:
        self.base_project = project
        self.options = options or AutoRunOptions()
        profile = project.autonomy.compute_profile if project.autonomy.enabled else None
        self.project = project.with_compute_profile(profile)
        self.output = self.options.output or sys.stdout
        if not 120 <= self.options.reflection_minutes <= 240:
            raise ValueError("reflection interval must be between 120 and 240 minutes")
        if not 1 <= self.options.reflection_round_minutes <= 30:
            raise ValueError(
                "autorun strategy reflection length must be between 1 and 30 minutes"
            )
        if not 1 <= self.options.round_minutes <= 120:
            raise ValueError("autorun round length must be between 1 and 120 minutes")
        if self.options.retry_delay_seconds < 0:
            raise ValueError("autorun retry delay must not be negative")
        if self.options.max_rounds is not None and self.options.max_rounds < 1:
            raise ValueError("autorun max rounds must be positive")
        prompt = self.options.master_prompt or project.root / "MASTER_PROMPT.md"
        self.master_prompt = prompt.expanduser().resolve()
        if not self.master_prompt.is_file() or self.master_prompt.is_symlink():
            raise AutoRunError(
                f"Master Prompt must be a regular file: {self.master_prompt}"
            )
        self.session_dir: Path | None = None

    def run(self) -> Path:
        """Create or resume the active session and drive it until explicitly stopped."""

        self.session_dir = self._select_session()
        controller = self.session_dir / "controller"
        controller.mkdir(exist_ok=True)
        try:
            with campaign_run_lock(controller):
                self._mark_running()
                return self._drive()
        except CampaignRunError as exc:
            raise AutoRunError(
                f"another autorun controller owns this session: {exc}"
            ) from exc

    def _select_session(self) -> Path:
        if self.options.session is not None:
            session = self.options.session.expanduser().resolve()
            if not (session / "state.json").is_file():
                raise AutoRunError(f"autorun session has no state.json: {session}")
            return session
        root = self.project.root / "autorun-runs"
        root.mkdir(parents=True, exist_ok=True)
        active_path = root / "active.json"
        if active_path.is_file():
            try:
                active = json.loads(active_path.read_text(encoding="utf-8"))
                session_value = active.get("session")
                retained_session = (
                    Path(session_value) if isinstance(session_value, str) else None
                )
                if (
                    retained_session is not None
                    and (retained_session / "state.json").is_file()
                ):
                    retained_state = self._read_state_from(retained_session)
                    if retained_state.get("status") in {
                        "running",
                        "recovering",
                        "paused",
                    }:
                        return retained_session
            except (OSError, json.JSONDecodeError, AutoRunError):
                pass
        session_id = (
            datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + f"-{os.urandom(3).hex()}"
        )
        session = root / session_id
        session.mkdir()
        now = datetime.now(UTC)
        state: dict[str, Any] = {
            "schema_version": 1,
            "session_id": session_id,
            "project_manifest": str(self.base_project.manifest_path),
            "master_prompt": str(self.master_prompt),
            "master_prompt_sha256": self._master_prompt_digest(),
            "status": "running",
            "pid": os.getpid(),
            "created_at": self._format_time(now),
            "updated_at": self._format_time(now),
            "heartbeat_at": self._format_time(now),
            "next_reflection_at": self._format_time(
                now + timedelta(minutes=self.options.reflection_minutes)
            ),
            "reflection_minutes": self.options.reflection_minutes,
            "reflection_round_minutes": self.options.reflection_round_minutes,
            "round_minutes": self.options.round_minutes,
            "round_count": 0,
            "reflection_count": 0,
            "consecutive_failures": 0,
            "next_retry_at": None,
            "repeated_output_count": 0,
            "last_output_sha256": None,
            "last_output": None,
            "last_receipt": None,
            "active_model": None,
            "active_model_route": None,
            "last_model": None,
            "last_reflection_model": None,
            "last_error": None,
            "stop_requested": False,
        }
        atomic_write_json(session / "state.json", state)
        atomic_write_json(active_path, {"schema_version": 1, "session": str(session)})
        self._event(session, "initialized", "autorun session created")
        return session

    def _mark_running(self) -> None:
        state = self._state()
        if state.get("project_manifest") != str(self.base_project.manifest_path):
            raise AutoRunError("autorun session belongs to a different project")
        retained_prompt = state.get("master_prompt")
        if retained_prompt != str(self.master_prompt):
            raise AutoRunError("autorun session uses a different Master Prompt")
        state["status"] = "running"
        state["pid"] = os.getpid()
        state["stop_requested"] = False
        state["next_retry_at"] = None
        state["last_error"] = None
        self._save(state)
        self._event(self._session(), "resumed", "autorun controller running")
        self._emit(f"AUTORUN_READY session={self._session()}")

    def _drive(self) -> Path:
        while True:
            state = self._state()
            if state.get("stop_requested") or (self._session() / "STOP").exists():
                state["status"] = "stopped"
                state["pid"] = None
                self._save(state)
                self._event(self._session(), "stopped", "stop requested")
                self._emit("AUTORUN_STOPPED")
                return self._session()
            if (
                self.options.max_rounds is not None
                and int(state["round_count"]) >= self.options.max_rounds
            ):
                state["status"] = "paused"
                state["pid"] = None
                self._save(state)
                self._event(self._session(), "paused", "configured round limit reached")
                return self._session()
            try:
                self._run_round(state)
            except RunnerInterrupted:
                interrupted = self._state()
                interrupted["status"] = "recovering"
                interrupted["pid"] = None
                interrupted["last_error"] = (
                    "controller interrupted during an agent round"
                )
                self._save(interrupted)
                self._event(self._session(), "interrupted", interrupted["last_error"])
                raise
            except Exception as exc:  # noqa: BLE001 - the supervisor must recover.
                failed = self._state()
                failed["status"] = "recovering"
                failed["consecutive_failures"] = (
                    int(failed.get("consecutive_failures", 0)) + 1
                )
                failed["last_error"] = f"{type(exc).__name__}: {exc}"
                self._save(failed)
                self._event(self._session(), "controller_error", failed["last_error"])
                self._emit(
                    f"autorun recovered from controller error: {failed['last_error']}"
                )
                self._sleep_after_failure(int(failed["consecutive_failures"]))

    def _run_round(self, state: dict[str, Any]) -> None:
        rounds_root = self._session() / "rounds"
        rounds_root.mkdir(parents=True, exist_ok=True)
        retained_indices = [
            int(path.name.removeprefix("round-"))
            for path in rounds_root.glob("round-*")
            if path.is_dir() and path.name.removeprefix("round-").isdigit()
        ]
        index = max([int(state["round_count"]), *retained_indices], default=0) + 1
        round_dir = rounds_root / f"round-{index:05d}"
        round_dir.mkdir()
        now = datetime.now(UTC)
        reflection_due = now >= self._parse_time(str(state["next_reflection_at"]))
        reflection_due = (
            reflection_due or int(state.get("consecutive_failures", 0)) >= 2
        )
        reflection_due = (
            reflection_due or int(state.get("repeated_output_count", 0)) >= 2
        )
        master_text = self.master_prompt.read_text(encoding="utf-8").strip()
        if not master_text:
            raise AutoRunError("Master Prompt is empty")
        master_digest = hashlib.sha256(master_text.encode("utf-8")).hexdigest()
        state["status"] = "running"
        state["next_retry_at"] = None
        state["heartbeat_at"] = utc_now()
        state["master_prompt_sha256"] = master_digest
        state["active_round"] = index
        self._save(state)

        reflection_output = (
            self._run_strategy_reflection(index, state, master_text, round_dir)
            if reflection_due
            else None
        )
        prompt = self._round_prompt(
            index,
            state,
            master_text,
            reflection_output=reflection_output,
        )
        prompt_path = round_dir / "prompt.md"
        output_path = round_dir / "output.md"
        receipt_path = round_dir / "receipt.json"
        conductor_model, model_route = self._conductor_model(state)
        atomic_write_text(prompt_path, prompt)
        request_path = round_dir / "request.json"
        atomic_write_json(
            request_path,
            {
                "role_id": "autorun_conductor",
                "attempt": index,
                "omp": self.options.omp or self.project.omp,
                "workspace": str(self.project.root),
                "run_dir": str(self._session()),
                "prompt": str(prompt_path),
                "output": str(output_path),
                "stdout_log": str(round_dir / "stdout.log"),
                "stderr_log": str(round_dir / "stderr.log"),
                "receipt": str(receipt_path),
                "tools": list(self.project.allowed_tools),
                "model": conductor_model,
                "thinking": self.options.thinking or self.project.planner_thinking,
                "max_time": self.options.round_minutes * 60,
                "empty_output_retries": 1,
                "execution": self.project.execution.to_dict(),
                "sandbox_read_paths": [
                    str(self.project.root),
                    str(self._session()),
                    str(self.master_prompt),
                ],
                "workspace_executables": True,
            },
        )
        state = self._state()
        state["active_prompt"] = str(prompt_path)
        state["active_model"] = conductor_model
        state["active_model_route"] = model_route
        self._save(state)
        self._event(self._session(), "round_started", f"round {index}")
        self._emit(f"autorun round {index} starting")
        exit_code = execute_agent_request(request_path)
        latest = self._state()
        latest["round_count"] = index
        latest["active_round"] = None
        latest["active_prompt"] = None
        latest["last_model"] = conductor_model
        latest["active_model"] = None
        latest["active_model_route"] = None
        latest["last_receipt"] = str(receipt_path)
        latest["last_output"] = str(output_path) if output_path.is_file() else None
        latest["heartbeat_at"] = utc_now()
        if reflection_due:
            latest["reflection_count"] = int(latest["reflection_count"]) + 1
            latest["next_reflection_at"] = self._format_time(
                datetime.now(UTC) + timedelta(minutes=int(latest["reflection_minutes"]))
            )
        if exit_code == 0 and output_path.is_file():
            digest = hashlib.sha256(output_path.read_bytes()).hexdigest()
            repeated = (
                int(latest.get("repeated_output_count", 0)) + 1
                if digest == latest.get("last_output_sha256")
                else 0
            )
            latest["last_output_sha256"] = digest
            latest["repeated_output_count"] = repeated
            latest["consecutive_failures"] = 0
            latest["last_error"] = None
            latest["status"] = "running"
            self._event(self._session(), "round_completed", f"round {index} succeeded")
        else:
            latest["status"] = "recovering"
            latest["consecutive_failures"] = (
                int(latest.get("consecutive_failures", 0)) + 1
            )
            latest["last_error"] = f"agent round {index} failed; see {receipt_path}"
            self._event(self._session(), "round_failed", latest["last_error"])
        self._save(latest)
        if exit_code != 0:
            self._sleep_after_failure(int(latest["consecutive_failures"]))

    def _run_strategy_reflection(
        self,
        index: int,
        state: dict[str, Any],
        master_text: str,
        round_dir: Path,
    ) -> Path | None:
        model = (
            self.options.reflection_model
            or self.project.strategy_reflection_model
            or self.options.model
            or self.project.planner_model
        )
        prompt_path = round_dir / "strategy-reflection-prompt.md"
        output_path = round_dir / "strategy-reflection.md"
        receipt_path = round_dir / "strategy-reflection-receipt.json"
        prompt = f"""# Bounded autorun strategy reflection

Review the retained campaign state and recommend exactly one concrete next action
for the primary conductor. Do not execute the task, edit files, or claim progress.
Identify failed assumptions or repeated work to abandon. Prefer the shortest
credible route to the living mathematical contract.

## Living Master Prompt

{master_text}

## Retained state

- Session: `{self._session()}`
- Completed rounds: {int(state.get("round_count", 0))}
- Previous output: `{state.get("last_output") or "None"}`
- Previous receipt: `{state.get("last_receipt") or "None"}`
- Previous error: `{state.get("last_error") or "None"}`

Return concise strategy advice ending with:

REFLECTION_NEXT: one concrete action for the primary conductor
"""
        atomic_write_text(prompt_path, prompt)
        request_path = round_dir / "strategy-reflection-request.json"
        read_only_tools = [
            tool
            for tool in self.project.allowed_tools
            if tool in {"read", "grep", "glob", "web_search"}
        ]
        atomic_write_json(
            request_path,
            {
                "role_id": "autorun_strategy_reflection",
                "attempt": index,
                "omp": self.options.omp or self.project.omp,
                "workspace": str(self.project.root),
                "run_dir": str(self._session()),
                "prompt": str(prompt_path),
                "output": str(output_path),
                "stdout_log": str(round_dir / "strategy-reflection-stdout.log"),
                "stderr_log": str(round_dir / "strategy-reflection-stderr.log"),
                "receipt": str(receipt_path),
                "tools": read_only_tools,
                "model": model,
                "thinking": self.options.thinking or self.project.planner_thinking,
                "max_time": self.options.reflection_round_minutes * 60,
                "empty_output_retries": 0,
                "execution": self.project.execution.to_dict(),
                "sandbox_read_paths": [
                    str(self.project.root),
                    str(self._session()),
                    str(self.master_prompt),
                ],
                "workspace_executables": True,
            },
        )
        active = self._state()
        active["active_prompt"] = str(prompt_path)
        active["active_model"] = model
        active["active_model_route"] = "strategy_reflection"
        active["last_reflection_model"] = model
        self._save(active)
        self._event(self._session(), "reflection_started", f"round {index}")
        self._emit(f"autorun round {index} strategy reflection starting")
        exit_code = execute_agent_request(request_path)
        if exit_code == 0 and output_path.is_file():
            self._event(self._session(), "reflection_completed", f"round {index}")
            return output_path
        self._event(
            self._session(),
            "reflection_failed",
            f"round {index}; primary conductor will continue",
        )
        return None

    def _round_prompt(
        self,
        index: int,
        state: dict[str, Any],
        master_text: str,
        reflection_output: Path | None,
    ) -> str:
        prior_output = state.get("last_output") or "None"
        prior_receipt = state.get("last_receipt") or "None"
        failure = state.get("last_error") or "None"
        reflection = ""
        if reflection_output is not None:
            reflection_text = reflection_output.read_text(encoding="utf-8").strip()
            reflection = f"""

## Bounded strategy reflection

Source: `{reflection_output}`

{reflection_text}

Treat this as strategy advice, not verified evidence. Check it against the
repository, then execute the single highest-value reachable action with the
primary model.
"""
        return f"""# Autorun conductor round {index}

You are the autonomous conductor for an unattended Agentic Lean Math Assistant
session. Work directly in `{self.project.root}`. You must choose your own next
specific task from the living Master Prompt, execute it, and verify its effect.
Do not merely propose work for a later agent.

## Living Master Prompt

Source: `{self.master_prompt}`

{master_text}

## Retained context

- Autorun session: `{self._session()}`
- Previous output: `{prior_output}`
- Previous receipt: `{prior_receipt}`
- Previous controller/agent error: `{failure}`
- Consecutive failed rounds: {int(state.get("consecutive_failures", 0))}
- Completed rounds: {int(state.get("round_count", 0))}
{reflection}
## Operating protocol

1. Inspect the current repository and retained evidence before choosing work.
2. Formulate a precise self-prompt for the single highest-leverage reachable task.
3. Prefer a complete vertical slice that changes a named proof obligation or removes
   a demonstrated ALMA bottleneck.
4. Implement the task now. Preserve useful partial work in small compilable files.
5. Run focused verification for every significant behavioral or formal change.
6. Never claim mathematical closure from prose, process exit, unproved certificate
   data, or a theorem with unmatched hypotheses.
7. Do not retry an unchanged failed approach. Diagnose it, change strategy, or work
   on an independent critical-path obligation.
8. If blocked on one path, immediately choose another useful path. Do not wait for
   the sleeping operator and do not enter a polling loop.
9. Do not weaken the CMV theorem contract. No `sorry`, `admit`, project axioms,
   unchecked oracle, or `native_decide`.
10. Before returning, save all useful work and state exactly what was verified and
    what the next conductor round should attempt.

End with these machine-readable lines:

AUTORUN_RESULT: progress | blocked | complete
AUTORUN_SUMMARY: one factual sentence
AUTORUN_NEXT: one concrete next action
"""

    def _conductor_model(self, state: dict[str, Any]) -> tuple[str | None, str]:
        primary_model = self.options.model or self.project.planner_model
        targeted_model = self.project.targeted_task_model
        failures = int(state.get("consecutive_failures", 0))
        if (
            targeted_model is not None
            and targeted_model != primary_model
            and failures >= 2
            and failures % 3 == 2
        ):
            return targeted_model, "targeted_recovery"
        return primary_model, "primary"

    def _sleep_after_failure(self, failures: int) -> None:
        delay = min(
            300.0, self.options.retry_delay_seconds * (2 ** min(failures - 1, 4))
        )
        retry_at = (
            self._format_time(datetime.now(UTC) + timedelta(seconds=delay))
            if delay > 0
            else None
        )
        state = self._state()
        state["next_retry_at"] = retry_at
        self._save(state)
        if delay > 0:
            self._emit(f"autorun retrying after {delay:g} seconds")
            time.sleep(delay)
            state = self._state()
            if state.get("next_retry_at") == retry_at:
                state["next_retry_at"] = None
                self._save(state)

    def _master_prompt_digest(self) -> str:
        return hashlib.sha256(self.master_prompt.read_bytes()).hexdigest()

    def _session(self) -> Path:
        if self.session_dir is None:
            raise AutoRunError("autorun session is not initialized")
        return self.session_dir

    def _state(self) -> dict[str, Any]:
        return self._read_state_from(self._session())

    @staticmethod
    def _read_state_from(session: Path) -> dict[str, Any]:
        try:
            value = json.loads((session / "state.json").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise AutoRunError(f"cannot read autorun state: {exc}") from exc
        if not isinstance(value, dict) or value.get("schema_version") != 1:
            raise AutoRunError("autorun state is malformed")
        return value

    def _save(self, state: dict[str, Any]) -> None:
        state["updated_at"] = utc_now()
        atomic_write_json(self._session() / "state.json", state)

    @staticmethod
    def _event(session: Path, event: str, detail: str) -> None:
        path = session / "events.jsonl"
        line = json.dumps(
            {"at": utc_now(), "event": event, "detail": detail}, sort_keys=True
        )
        with path.open("a", encoding="utf-8") as stream:
            stream.write(line + "\n")
            stream.flush()
            os.fsync(stream.fileno())

    @staticmethod
    def _format_time(value: datetime) -> str:
        return (
            value.astimezone(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")
        )

    @staticmethod
    def _parse_time(value: str) -> datetime:
        parsed = datetime.fromisoformat(value)
        if parsed.tzinfo is None:
            raise AutoRunError("autorun timestamp has no timezone")
        return parsed

    def _emit(self, text: str) -> None:
        print(text, file=self.output, flush=True)


def discover_project(start: Path | None = None) -> Path:
    """Find the nearest project.toml from the current directory upward."""

    current = (start or Path.cwd()).expanduser().resolve()
    for directory in (current, *current.parents):
        candidate = directory / "project.toml"
        if candidate.is_file():
            return candidate
    raise AutoRunError("no project.toml found; run inside a project or pass --project")


def autorun_status(session_dir: Path) -> dict[str, Any]:
    """Read one retained autorun status."""

    return AutoRunRunner._read_state_from(session_dir.expanduser().resolve())


def _pid_is_alive(value: object) -> bool:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        return False
    try:
        os.kill(value, 0)
    except (OSError, ProcessLookupError):
        return False
    return True


def _round_receipt(
    session: Path, active_round: object, active_route: object
) -> dict[str, Any]:
    if not isinstance(active_round, int) or isinstance(active_round, bool):
        return {}
    name = (
        "strategy-reflection-receipt.json"
        if active_route == "strategy_reflection"
        else "receipt.json"
    )
    path = session / "rounds" / f"round-{active_round:05d}" / name
    if not path.is_file():
        return {}
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"status": "unreadable"}
    return value if isinstance(value, dict) else {"status": "unreadable"}


def _latest_autorun_event(session: Path) -> dict[str, Any]:
    path = session / "events.jsonl"
    latest: dict[str, Any] = {}
    try:
        with path.open("r", encoding="utf-8") as stream:
            for line in stream:
                try:
                    value = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(value, dict):
                    latest = value
    except OSError:
        return {}
    return latest


def _markdown_section(text: str, title: str) -> str:
    match = re.search(
        rf"^##\s+{re.escape(title)}\s*$",
        text,
        flags=re.MULTILINE | re.IGNORECASE,
    )
    if match is None:
        return ""
    remainder = text[match.end() :]
    next_heading = re.search(r"^##\s+", remainder, flags=re.MULTILINE)
    return remainder[: next_heading.start() if next_heading else None].strip()


def _numbered_items(section: str) -> list[str]:
    items: list[str] = []
    for line in section.splitlines():
        match = re.match(r"^\s*\d+\.\s+(.*)", line)
        if match is not None:
            items.append(match.group(1).strip())
        elif items and line[:1].isspace() and line.strip():
            items[-1] = f"{items[-1]} {line.strip()}"
    return items


def _bullet_items(section: str) -> list[str]:
    items: list[str] = []
    for line in section.splitlines():
        match = re.match(r"^\s*-\s+(.*)", line)
        if match is not None:
            items.append(match.group(1).strip())
        elif items and line[:1].isspace() and line.strip():
            items[-1] = f"{items[-1]} {line.strip()}"
    return items


def _master_prompt_progress(
    state: dict[str, Any],
) -> tuple[str, list[str], list[str]]:
    value = state.get("master_prompt")
    if not isinstance(value, str):
        return "", [], []
    try:
        text = Path(value).read_text(encoding="utf-8")
    except OSError:
        return "", [], []
    objective = _markdown_section(text, "Primary objective")
    immediate = next(
        (
            " ".join(paragraph.split()).partition("After that milestone")[0].strip()
            for paragraph in objective.split("\n\n")
            if "immediate milestone" in paragraph.casefold()
        ),
        "",
    )
    evidence = _bullet_items(_markdown_section(text, "Current evidence"))
    milestones = _numbered_items(_markdown_section(text, "Current critical path"))
    return immediate, evidence, milestones


def _last_round_markers(state: dict[str, Any]) -> dict[str, str]:
    value = state.get("last_output")
    if not isinstance(value, str):
        return {}
    try:
        lines = Path(value).read_text(encoding="utf-8").splitlines()
    except OSError:
        return {}
    markers: dict[str, str] = {}
    for line in lines:
        for name in ("AUTORUN_RESULT", "AUTORUN_SUMMARY", "AUTORUN_NEXT"):
            prefix = f"{name}:"
            if line.startswith(prefix):
                markers[name] = line.removeprefix(prefix).strip()
    return markers


def _progress_recap(
    session: Path,
    state: dict[str, Any],
    receipt: dict[str, Any],
    *,
    updated_at: datetime,
    next_update_at: datetime,
) -> str:
    status = str(state.get("status", "unknown"))
    active_round = state.get("active_round")
    controller_alive = _pid_is_alive(state.get("pid"))
    process_state = "responding" if controller_alive else "not responding"
    sections = [
        "PROGRESS UPDATE",
        (
            f"Updated {updated_at:%H:%M UTC}. The next automatic update is "
            f"scheduled for {next_update_at:%H:%M UTC}."
        ),
        "CURRENT RUN",
        (
            f"Controller: {status} and {process_state}. Session: "
            f"{state.get('round_count', 0)} completed rounds, "
            f"{state.get('consecutive_failures', 0)} consecutive failures, "
            f"{state.get('reflection_count', 0)} strategy reflections."
        ),
    ]
    if isinstance(active_round, int) and not isinstance(active_round, bool):
        receipt_status = str(receipt.get("status", "starting"))
        started_at = receipt.get("started_at")
        timing = (
            f" since {started_at[11:16]} UTC"
            if isinstance(started_at, str) and len(started_at) >= 16
            else ""
        )
        route = str(state.get("active_model_route") or "primary")
        stage = "strategy reflection" if route == "strategy_reflection" else "conductor"
        log_name = (
            "strategy-reflection-stdout.log"
            if route == "strategy_reflection"
            else "stdout.log"
        )
        output_path = session / "rounds" / f"round-{active_round:05d}" / log_name
        output_size = output_path.stat().st_size if output_path.is_file() else 0
        model = state.get("active_model") or "default"
        sections.append(
            f"Round {active_round}: {stage} {receipt_status}{timing} on {model}; "
            f"retained live output {output_size} bytes."
        )
    else:
        sections.append("No conductor round is currently active.")
    immediate, evidence, milestones = _master_prompt_progress(state)
    if immediate:
        sections.extend(["IMMEDIATE MILESTONE", immediate])
    if milestones:
        milestone_lines: list[str] = []
        for index, milestone in enumerate(milestones, start=1):
            normalized = milestone.casefold()
            if index == 1:
                milestone_state = "NEXT PREREQUISITE"
            elif "only after" in normalized:
                milestone_state = "GATED"
            elif index == len(milestones):
                milestone_state = "QUEUED"
            else:
                milestone_state = "OPEN"
            milestone_lines.append(f"{index}. {milestone_state} — {milestone}")
        sections.extend(["MILESTONE STATUS", "\n".join(milestone_lines)])
    if evidence:
        audit_finding = next(
            (
                item
                for item in reversed(evidence)
                if "rejected" in item.casefold() or "no concrete" in item.casefold()
            ),
            "",
        )
        if audit_finding:
            sections.extend(["CURRENT AUDIT BLOCKER", audit_finding])
        sections.extend(
            [
                "VERIFIED BASELINE",
                evidence[0],
            ]
        )
    markers = _last_round_markers(state)
    if markers:
        sections.append("LATEST COMPLETED ROUND")
        sections.append(
            "Result: "
            f"{markers.get('AUTORUN_RESULT', 'unspecified')}. "
            f"{markers.get('AUTORUN_SUMMARY', 'No retained summary.')}"
        )
        next_action = markers.get("AUTORUN_NEXT")
        if next_action:
            sections.extend(["NEXT CONDUCTOR ACTION", next_action])
    else:
        sections.extend(
            [
                "LATEST COMPLETED ROUND",
                "No conductor round has produced a retained result in this session yet.",
            ]
        )
    error = state.get("last_error")
    sections.extend(
        [
            "CONTROLLER EXCEPTIONS",
            (
                f"The latest controller error is: {error}"
                if isinstance(error, str) and error
                else "No controller error is currently recorded."
            ),
        ]
    )
    latest_event = _latest_autorun_event(session)
    event_name = latest_event.get("event")
    event_at = latest_event.get("at")
    event_detail = latest_event.get("detail")
    if isinstance(event_name, str):
        event_text = f"The latest retained event is {event_name}"
        if isinstance(event_at, str):
            event_text += f" at {event_at}"
        if isinstance(event_detail, str) and len(event_detail) <= 160:
            event_text += f": {event_detail}"
        sections.extend(["LATEST RETAINED EVENT", f"{event_text}."])
    sections.extend(
        [
            "STRATEGY SCHEDULE",
            (
                f"The next formal strategy reflection is scheduled for "
                f"{state.get('next_reflection_at', 'an unspecified time')}."
            ),
        ]
    )
    return "\n\n".join(sections)


def follow_autorun_status(
    session_dir: Path,
    *,
    interval_seconds: float = 1.0,
    recap_interval_seconds: float = 600.0,
    output: TextIO | None = None,
    persistent: bool = False,
) -> None:
    """Render a live readout with a periodically refreshed verbal recap."""

    if interval_seconds <= 0:
        raise ValueError("autorun monitor interval must be positive")
    if recap_interval_seconds <= 0:
        raise ValueError("autorun recap interval must be positive")
    session = session_dir.expanduser().resolve()
    stream = output or sys.stdout
    display = LiveStatusDisplay(stream=stream)
    recap = ""
    next_recap_deadline = 0.0
    try:
        while True:
            try:
                state = autorun_status(session)
            except AutoRunError as exc:
                display.render(
                    status="recovering",
                    detail=f"state unavailable · reconnecting · {exc}",
                )
                if not persistent:
                    raise
                time.sleep(interval_seconds)
                continue
            active_round = state.get("active_round")
            _set_terminal_title(stream, f"Autorun round {active_round or '-'} status")
            receipt = _round_receipt(
                session, active_round, state.get("active_model_route")
            )
            receipt_status = receipt.get(
                "status",
                "starting"
                if isinstance(active_round, int) and not isinstance(active_round, bool)
                else "idle",
            )
            controller = "up" if _pid_is_alive(state.get("pid")) else "down"
            status = str(state.get("status", "unknown"))
            route = str(state.get("active_model_route") or "primary")
            activity = "reflection" if route == "strategy_reflection" else "agent"
            model_value = state.get("active_model")
            model = (
                f" · {str(model_value).rsplit('/', 1)[-1]}"
                if isinstance(model_value, str)
                else ""
            )
            detail = (
                f"controller {controller} · round {active_round or '-'} · "
                f"{activity} {receipt_status}{model} · "
                f"completed {state.get('round_count', 0)} · "
                f"failures {state.get('consecutive_failures', 0)}"
            )
            retry_at = state.get("next_retry_at")
            if status == "recovering" and isinstance(retry_at, str):
                detail += f" · retry at {retry_at}"
            now = time.monotonic()
            if now >= next_recap_deadline:
                updated_at = datetime.now(UTC)
                next_update_at = updated_at + timedelta(seconds=recap_interval_seconds)
                recap = _progress_recap(
                    session,
                    state,
                    receipt,
                    updated_at=updated_at,
                    next_update_at=next_update_at,
                )
                next_recap_deadline = now + recap_interval_seconds
            display.render(status=status, detail=detail, recap=recap)
            if (
                not persistent
                and status in {"stopped", "paused"}
                and active_round is None
            ):
                return
            time.sleep(interval_seconds)
    except KeyboardInterrupt:
        return
    finally:
        display.finish()


def _sync_herdr_pane_label(title: str) -> None:
    pane_id = os.environ.get("HERDR_PANE_ID")
    if not pane_id or _HERDR_PANE_LABELS.get(pane_id) == title:
        return
    now = time.monotonic()
    attempted = _HERDR_LABEL_ATTEMPTS.get(pane_id)
    if attempted is not None and attempted[0] == title and now - attempted[1] < 10:
        return
    _HERDR_LABEL_ATTEMPTS[pane_id] = (title, now)
    try:
        HerdrClient(timeout=5.0).rename_pane(pane_id, title)
    except HerdrError:
        return
    _HERDR_PANE_LABELS[pane_id] = title


def _set_terminal_title(stream: TextIO, title: str) -> None:
    if not (hasattr(stream, "isatty") and stream.isatty()):
        return
    safe_title = title.replace("\x1b", "").replace("\x07", "").replace("\n", " ")
    cached = _TERMINAL_TITLES.get(id(stream))
    if cached is None or cached[0] is not stream or cached[1] != safe_title:
        stream.write(f"\x1b]0;{safe_title}\x07")
        stream.flush()
        _TERMINAL_TITLES[id(stream)] = (stream, safe_title)
    if stream is sys.stdout:
        _sync_herdr_pane_label(safe_title)


def _tail_lines(path: Path, count: int) -> list[str]:
    try:
        size = path.stat().st_size
        with path.open("rb") as stream:
            stream.seek(max(0, size - 64 * 1024))
            data = stream.read()
    except OSError:
        return []
    if size > len(data):
        _, _, data = data.partition(b"\n")
    lines = data.decode("utf-8", errors="replace").splitlines()
    return lines[-count:]


def _round_stdout_path(
    session: Path, active_round: object, route: object
) -> Path | None:
    if not isinstance(active_round, int) or isinstance(active_round, bool):
        return None
    name = (
        "strategy-reflection-stdout.log"
        if route == "strategy_reflection"
        else "stdout.log"
    )
    return session / "rounds" / f"round-{active_round:05d}" / name


def follow_autorun_output(
    session_dir: Path,
    *,
    interval_seconds: float = 1.0,
    output: TextIO | None = None,
) -> None:
    """Follow the active round's retained output, switching rounds automatically."""

    if interval_seconds <= 0:
        raise ValueError("autorun output interval must be positive")
    session = session_dir.expanduser().resolve()
    stream = output or sys.stdout
    display = LiveStatusDisplay(stream=stream)
    try:
        while True:
            try:
                state = autorun_status(session)
            except AutoRunError as exc:
                display.render(
                    status="recovering",
                    detail=f"state unavailable · reconnecting · {exc}",
                )
                time.sleep(interval_seconds)
                continue
            active_round = state.get("active_round")
            route = state.get("active_model_route")
            _set_terminal_title(stream, f"Round {active_round or '-'} Output")
            receipt = _round_receipt(session, active_round, route)
            path = _round_stdout_path(session, active_round, route)
            lines = _tail_lines(path, 5) if path is not None else []
            if lines:
                body = "\n".join(line[:120] for line in lines)
            elif path is None:
                body = "No round is active. Waiting for the controller to resume."
            else:
                body = f"{path.name} has no retained output yet."
            model = state.get("active_model")
            detail = (
                f"round {active_round or '-'} · "
                f"{'reflection' if route == 'strategy_reflection' else 'conductor'} "
                f"{receipt.get('status', 'idle')} · "
                f"{str(model).rsplit('/', 1)[-1] if isinstance(model, str) else 'default'}"
            )
            display.render(
                status=str(state.get("status", "unknown")),
                detail=detail,
                recap=f"CURRENT ROUND OUTPUT\n\n{body}",
            )
            time.sleep(interval_seconds)
    except KeyboardInterrupt:
        return
    finally:
        display.finish()


def follow_autorun_events(
    session_dir: Path,
    *,
    interval_seconds: float = 1.0,
    output: TextIO | None = None,
) -> None:
    """Follow raw controller events while tracking the active round."""

    if interval_seconds <= 0:
        raise ValueError("autorun events interval must be positive")
    session = session_dir.expanduser().resolve()
    stream = output or sys.stdout
    display = LiveStatusDisplay(stream=stream)
    try:
        while True:
            try:
                state = autorun_status(session)
            except AutoRunError as exc:
                display.render(
                    status="recovering",
                    detail=f"state unavailable · reconnecting · {exc}",
                )
                time.sleep(interval_seconds)
                continue
            active_round = state.get("active_round")
            route = state.get("active_model_route")
            _set_terminal_title(stream, f"Round {active_round or '-'} Raw events")
            receipt = _round_receipt(session, active_round, route)
            lines = _tail_lines(session / "events.jsonl", 5)
            body = (
                "\n".join(lines) if lines else "No controller events are retained yet."
            )
            detail = (
                f"round {active_round or '-'} · "
                f"{'reflection' if route == 'strategy_reflection' else 'conductor'} "
                f"{receipt.get('status', 'idle')} · controller "
                f"{'up' if _pid_is_alive(state.get('pid')) else 'down'}"
            )
            display.render(
                status=str(state.get("status", "unknown")),
                detail=detail,
                recap=f"RAW EVENTS\n\n{body}",
            )
            time.sleep(interval_seconds)
    except KeyboardInterrupt:
        return
    finally:
        display.finish()


def request_autorun_stop(session_dir: Path) -> str:
    """Durably request a running controller to stop between agent rounds."""

    session = session_dir.expanduser().resolve()
    state = AutoRunRunner._read_state_from(session)
    state["stop_requested"] = True
    state["updated_at"] = utc_now()
    atomic_write_json(session / "state.json", state)
    atomic_write_text(session / "STOP", "stop requested\n")
    return f"autorun stop requested: {session}"


def add_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--project", type=Path)
    parser.add_argument("--master-prompt", type=Path)
    parser.add_argument("--session", type=Path)
    parser.add_argument("--reflection-minutes", type=int, default=150)
    parser.add_argument("--reflection-round-minutes", type=int, default=15)
    parser.add_argument("--round-minutes", type=int, default=90)
    parser.add_argument("--retry-delay-seconds", type=float, default=30.0)
    parser.add_argument("--max-rounds", type=int)
    parser.add_argument("--omp")
    parser.add_argument("--model")
    parser.add_argument("--reflection-model")
    parser.add_argument("--thinking")


def options_from_args(args: argparse.Namespace) -> AutoRunOptions:
    return AutoRunOptions(
        master_prompt=args.master_prompt,
        session=args.session,
        reflection_minutes=args.reflection_minutes,
        reflection_round_minutes=args.reflection_round_minutes,
        round_minutes=args.round_minutes,
        retry_delay_seconds=args.retry_delay_seconds,
        max_rounds=args.max_rounds,
        omp=args.omp,
        model=args.model,
        reflection_model=args.reflection_model,
        thinking=args.thinking,
    )


def _fail(parser: argparse.ArgumentParser, message: str) -> NoReturn:
    parser.error(message)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="autorun",
        description="Run a persistent, self-prompting project conductor.",
    )
    add_arguments(parser)
    args = parser.parse_args(argv)
    try:
        project = ProjectSpec.load(args.project or discover_project())
        session = AutoRunRunner(project, options_from_args(args)).run()
        state = autorun_status(session)
        print(f"autorun status: {state.get('status')}")
        print(f"session directory: {session}")
        return 0 if state.get("status") in {"stopped", "paused"} else 1
    except (AutoRunError, ConfigurationError, OSError, ValueError) as exc:
        _fail(parser, str(exc))


if __name__ == "__main__":
    raise SystemExit(main())
