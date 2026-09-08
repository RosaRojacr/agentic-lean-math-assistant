"""Persistent self-prompting mode for unattended project work."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import threading
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import UTC, datetime, timedelta
from pathlib import Path
from typing import Any, NoReturn, TextIO, TypedDict

from .agent_runner import RunnerInterrupted
from .agent_runner import execute as execute_agent_request
from .artifacts import atomic_write_json, atomic_write_text, utc_now
from .command import run_captured_command
from .config import ConfigurationError
from .herdr import HerdrClient, HerdrError
from .project import ProjectSpec
from .runtime import CampaignRunError, campaign_run_lock
from .terminal_status import LiveStatusDisplay

_HERDR_PANE_LABELS: dict[str, str] = {}
_HERDR_LABEL_ATTEMPTS: dict[str, tuple[str, float]] = {}
_TERMINAL_TITLES: dict[int, tuple[TextIO, str]] = {}
_PROGRESS_CLASSES = {"incremental", "meaningful", "blocked", "complete"}
_ID_PATTERN = re.compile(r"^[a-z][a-z0-9_-]{0,63}$")
_TEXT_LIMIT = 2_000
_STRATEGY_HISTORY_LIMIT = 128


@dataclass(frozen=True, slots=True)
class _StrategyProposal:
    decision: str
    base_strategy_id: str | None
    base_revision: int | None
    selected_method: str
    decision_reason: str
    next_action: str
    review_after_executions: int
    checkpoints: tuple[dict[str, Any], ...]
    stop_conditions: tuple[dict[str, Any], ...]


@dataclass(frozen=True, slots=True)
class _ProgressAdjudication:
    strategy_id: str
    strategy_revision: int
    progress_class: str
    alignment: str
    checkpoint_id: str | None
    checkpoint_result: str
    triggered_stop_condition_id: str | None
    reason: str
    verified_scope_delta: str


class StrategyCheckpoint(TypedDict):
    id: str
    due_execution: int
    observable: str
    status: str
    last_result: str | None
    last_adjudication_execution: int | None


class StrategyStopCondition(TypedDict):
    id: str
    observable: str
    triggered: bool
    last_adjudication_execution: int | None


class StrategyContract(TypedDict):
    schema_version: int
    strategy_id: str
    revision: int
    status: str
    selected_method: str
    decision_reason: str
    accepted_attempt: int
    accepted_execution: int
    lineage_started_execution: int
    hard_deadline_execution: int
    review_due_execution: int
    next_action: str
    checkpoints: list[StrategyCheckpoint]
    stop_conditions: list[StrategyStopCondition]
    last_alignment: str | None
    last_checkpoint_result: str | None


class AutoRunState(TypedDict, total=False):
    schema_version: int
    session_id: str
    status: str
    pid: int | None
    project_manifest: str
    master_prompt: str
    master_prompt_sha256: str
    created_at: str
    updated_at: str
    heartbeat_at: str
    next_reflection_at: str
    reflection_minutes: int
    reflection_round_minutes: int
    round_minutes: int
    round_count: int
    attempt_count: int
    reflection_count: int
    meaningful_round_count: int
    incremental_round_count: int
    blocked_round_count: int
    complete_round_count: int
    unclassified_round_count: int
    controller_failure_count: int
    agent_execution_failure_count: int
    verification_failure_count: int
    strategy_gate_failure_count: int
    mathematical_blocker_count: int
    consecutive_execution_failures: int
    last_failure_class: str | None
    active_strategy: StrategyContract | None
    strategy_history: list[dict[str, Any]]
    adjudication_history: list[dict[str, Any]]
    legacy_strategy_state: dict[str, Any] | None
    last_progress_claim: str | None
    last_progress_class: str | None
    last_progress_adjudication: dict[str, Any] | None
    last_adjudication_review: str | None
    last_adjudication_model: str | None
    last_strategy_decision: str | None
    last_strategy_review: str | None
    last_strategy_round: int | None
    strategy_change_required: bool
    next_retry_at: str | None
    repeated_output_count: int
    last_output_sha256: str | None
    last_output: str | None
    last_receipt: str | None
    active_round: int | None
    active_prompt: str | None
    active_model: str | None
    active_model_route: str | None
    last_model: str | None
    last_reflection_model: str | None
    last_error: str | None
    stop_requested: bool


class AutoRunError(RuntimeError):
    """The persistent autorun controller has an invalid retained state."""


class StrategyGateError(AutoRunError):
    """The meaningful-progress gate failed before execution could resume."""


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
        self._state_lock = threading.RLock()

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
            "schema_version": 3,
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
            "attempt_count": 0,
            "meaningful_round_count": 0,
            "incremental_round_count": 0,
            "blocked_round_count": 0,
            "complete_round_count": 0,
            "unclassified_round_count": 0,
            "controller_failure_count": 0,
            "agent_execution_failure_count": 0,
            "verification_failure_count": 0,
            "strategy_gate_failure_count": 0,
            "mathematical_blocker_count": 0,
            "consecutive_execution_failures": 0,
            "last_failure_class": None,
            "active_strategy": None,
            "strategy_history": [],
            "adjudication_history": [],
            "legacy_strategy_state": None,
            "last_progress_claim": None,
            "last_progress_adjudication": None,
            "last_adjudication_review": None,
            "last_adjudication_model": None,
            "last_progress_class": None,
            "last_strategy_decision": None,
            "last_strategy_review": None,
            "last_strategy_round": None,
            "strategy_change_required": False,
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
        active_strategy = state.get("active_strategy")
        if (
            state.get("status") == "stopped"
            and isinstance(active_strategy, dict)
            and active_strategy.get("status") == "complete"
        ):
            state["pid"] = None
            self._save(state)
            return
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
            active_strategy = state.get("active_strategy")
            if (
                state.get("status") == "stopped"
                and isinstance(active_strategy, dict)
                and active_strategy.get("status") == "complete"
            ):
                state["pid"] = None
                self._save(state)
                return self._session()
            if state.get("stop_requested") or (self._session() / "STOP").exists():
                state["status"] = "stopped"
                state["pid"] = None
                self._save(state)
                self._event(self._session(), "stopped", "stop requested")
                self._emit("AUTORUN_STOPPED")
                return self._session()
            if (
                self.options.max_rounds is not None
                and int(state["attempt_count"]) >= self.options.max_rounds
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
            except StrategyGateError as exc:
                failed = self._state()
                failed["status"] = "recovering"
                failed["strategy_gate_failure_count"] = (
                    int(failed.get("strategy_gate_failure_count", 0)) + 1
                )
                failed["last_failure_class"] = "strategy_gate"
                failed["last_error"] = str(exc)
                self._save(failed)
                self._event(self._session(), "strategy_gate_error", str(exc))
                self._emit(f"autorun strategy gate rejected review: {exc}")
                self._sleep_after_failure(int(failed["strategy_gate_failure_count"]))
            except Exception as exc:  # noqa: BLE001 - the supervisor must recover.
                failed = self._state()
                failed["status"] = "recovering"
                failed["controller_failure_count"] = (
                    int(failed.get("controller_failure_count", 0)) + 1
                )
                failed["last_failure_class"] = "controller"
                failed["last_error"] = f"{type(exc).__name__}: {exc}"
                self._save(failed)
                self._event(self._session(), "controller_error", failed["last_error"])
                self._emit(
                    f"autorun recovered from controller error: {failed['last_error']}"
                )
                self._sleep_after_failure(int(failed["controller_failure_count"]))

    def _run_round(self, state: dict[str, Any]) -> None:
        rounds_root = self._session() / "rounds"
        rounds_root.mkdir(parents=True, exist_ok=True)
        retained_indices = [
            int(path.name.removeprefix("round-"))
            for path in rounds_root.glob("round-*")
            if path.is_dir() and path.name.removeprefix("round-").isdigit()
        ]
        index = (
            max([int(state.get("attempt_count", 0)), *retained_indices], default=0) + 1
        )
        round_dir = rounds_root / f"round-{index:05d}"
        round_dir.mkdir()
        now = datetime.now(UTC)
        reflection_due = (
            now >= self._parse_time(str(state["next_reflection_at"]))
            or int(state.get("consecutive_execution_failures", 0)) >= 2
            or int(state.get("repeated_output_count", 0)) >= 2
            or self._strategy_requires_review(state)
        )
        master_text = self.master_prompt.read_text(encoding="utf-8").strip()
        if not master_text:
            raise AutoRunError("Master Prompt is empty")
        state["status"] = "running"
        state["next_retry_at"] = None
        state["heartbeat_at"] = utc_now()
        state["master_prompt_sha256"] = hashlib.sha256(
            master_text.encode("utf-8")
        ).hexdigest()
        state["attempt_count"] = index
        state["active_round"] = index
        self._save(state)

        if reflection_due:
            self._run_strategy_reflection(index, state, master_text, round_dir)
            state = self._state()
        strategy = state.get("active_strategy")
        self._validate_strategy_contract(
            strategy,
            completed_execution=int(state.get("round_count", 0)),
            require_active=True,
        )
        prompt = self._round_prompt(index, state, master_text)
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
        active = self._state()
        active["active_prompt"] = str(prompt_path)
        active["active_model"] = conductor_model
        active["active_model_route"] = model_route
        self._save(active)
        self._event(self._session(), "round_started", f"round {index}")
        self._emit(f"autorun round {index} starting")
        exit_code = self._execute_with_heartbeat(request_path)
        latest = self._state()
        latest["active_round"] = None
        latest["active_prompt"] = None
        latest["last_model"] = conductor_model
        latest["active_model"] = None
        latest["active_model_route"] = None
        latest["last_receipt"] = str(receipt_path)
        latest["last_output"] = str(output_path) if output_path.is_file() else None
        latest["heartbeat_at"] = utc_now()
        if exit_code == 0 and output_path.is_file():
            claim = self._parse_conductor_claim(output_path.read_text(encoding="utf-8"))
            digest = hashlib.sha256(output_path.read_bytes()).hexdigest()
            latest["repeated_output_count"] = (
                int(latest.get("repeated_output_count", 0)) + 1
                if digest == latest.get("last_output_sha256")
                else 0
            )
            latest["last_output_sha256"] = digest
            latest["last_progress_claim"] = (
                claim.get("progress_class") if claim is not None else "unclassified"
            )
            latest["consecutive_execution_failures"] = 0
            latest["round_count"] = int(latest.get("round_count", 0)) + 1
            self._save(latest)

            metrics, metric_failures = self._run_progress_metrics(round_dir)
            adjudication, adjudication_path, adjudication_model = (
                self._run_progress_adjudication(index, round_dir, output_path, metrics)
            )
            latest = self._state()
            latest["active_round"] = None
            latest["active_prompt"] = None
            latest["active_model"] = None
            latest["active_model_route"] = None
            latest["last_adjudication_model"] = adjudication_model
            latest["verification_failure_count"] = (
                int(latest.get("verification_failure_count", 0)) + metric_failures
            )
            if adjudication is None:
                latest["last_progress_class"] = "unclassified"
                latest["unclassified_round_count"] = (
                    int(latest.get("unclassified_round_count", 0)) + 1
                )
                latest["verification_failure_count"] = (
                    int(latest.get("verification_failure_count", 0)) + 1
                )
                latest["last_progress_adjudication"] = None
                latest["last_adjudication_review"] = (
                    str(adjudication_path) if adjudication_path.is_file() else None
                )
                latest["last_failure_class"] = "verification"
                latest["last_error"] = (
                    f"progress adjudication for attempt {index} failed"
                )
                progress_class = "unclassified"
            else:
                progress_class = adjudication.progress_class
                latest["last_progress_class"] = progress_class
                latest["last_progress_adjudication"] = {
                    "strategy_id": adjudication.strategy_id,
                    "strategy_revision": adjudication.strategy_revision,
                    "progress_class": adjudication.progress_class,
                    "alignment": adjudication.alignment,
                    "checkpoint_id": adjudication.checkpoint_id,
                    "checkpoint_result": adjudication.checkpoint_result,
                    "triggered_stop_condition_id": (
                        adjudication.triggered_stop_condition_id
                    ),
                    "reason": adjudication.reason,
                    "verified_scope_delta": adjudication.verified_scope_delta,
                }
                latest["last_adjudication_review"] = str(adjudication_path)
                counter = f"{progress_class}_round_count"
                latest[counter] = int(latest.get(counter, 0)) + 1
                if progress_class == "blocked":
                    latest["mathematical_blocker_count"] = (
                        int(latest.get("mathematical_blocker_count", 0)) + 1
                    )
                self._apply_adjudication_to_strategy(
                    latest,
                    adjudication,
                    attempt=index,
                    execution=int(latest["round_count"]),
                    artifact=str(adjudication_path),
                )
                latest["last_failure_class"] = (
                    "verification" if metric_failures else None
                )
                latest["last_error"] = (
                    f"{metric_failures} trusted progress metric(s) failed"
                    if metric_failures
                    else None
                )
            if latest.get("status") != "stopped":
                latest["status"] = "running"
            self._event(
                self._session(),
                "round_completed",
                (
                    f"attempt {index} execution completed; conductor claimed "
                    f"{latest.get('last_progress_claim')}; adjudicated {progress_class}"
                ),
            )
        else:
            latest["status"] = "recovering"
            latest["agent_execution_failure_count"] = (
                int(latest.get("agent_execution_failure_count", 0)) + 1
            )
            latest["consecutive_execution_failures"] = (
                int(latest.get("consecutive_execution_failures", 0)) + 1
            )
            latest["last_failure_class"] = "agent_execution"
            latest["last_error"] = f"agent attempt {index} failed; see {receipt_path}"
            self._event(self._session(), "round_failed", latest["last_error"])
        self._save(latest)
        if exit_code != 0:
            self._sleep_after_failure(int(latest["consecutive_execution_failures"]))

    def _run_strategy_reflection(
        self,
        index: int,
        state: dict[str, Any],
        master_text: str,
        round_dir: Path,
    ) -> Path:
        model = (
            self.options.reflection_model
            or self.project.strategy_reflection_model
            or self.options.model
            or self.project.planner_model
        )
        read_only_tools = [
            tool
            for tool in self.project.allowed_tools
            if tool in {"read", "grep", "glob", "web_search"}
        ]
        current = self._state()
        current_strategy = current.get("active_strategy")
        if (
            isinstance(current_strategy, dict)
            and current_strategy.get("status") == "active"
            and int(current.get("round_count", 0))
            >= int(current_strategy.get("hard_deadline_execution", 0))
        ):
            expired = json.loads(json.dumps(current_strategy))
            expired["status"] = "expired"
            current["active_strategy"] = expired
            current["strategy_change_required"] = True
            self._save(current)
        state = self._state()
        prompt_path = round_dir / "strategy-reflection-prompt.md"
        output_path = round_dir / "strategy-reflection.md"
        receipt_path = round_dir / "strategy-reflection-receipt.json"
        request_path = round_dir / "strategy-reflection-request.json"
        atomic_write_text(
            prompt_path,
            self._strategy_reflection_prompt(state, master_text),
        )
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
        exit_code = self._execute_with_heartbeat(request_path)
        proposal: _StrategyProposal | None = None
        errors: list[str] = []
        if exit_code != 0 or not output_path.is_file():
            errors.append("strategy governor did not produce a retained response")
        else:
            proposal, errors = self._parse_strategy_proposal(
                output_path.read_text(encoding="utf-8"),
                state=self._state(),
                max_strategy_executions=self.project.autorun.max_strategy_executions,
            )
        if proposal is None or errors:
            failed = self._state()
            failed["active_round"] = None
            failed["active_prompt"] = None
            failed["active_model"] = None
            failed["active_model_route"] = None
            failed["last_strategy_review"] = (
                str(output_path) if output_path.is_file() else None
            )
            failed["last_error"] = "strategy proposal invalid: " + "; ".join(errors)
            self._save(failed)
            self._event(
                self._session(),
                "reflection_failed",
                f"round {index}; {failed['last_error']}",
            )
            raise StrategyGateError(str(failed["last_error"]))

        approved = self._state()
        approved["active_strategy"] = self._materialize_strategy_contract(
            index,
            approved,
            proposal,
        )
        approved["last_strategy_decision"] = proposal.decision
        approved["last_strategy_review"] = str(output_path)
        approved["last_strategy_round"] = index
        approved["strategy_change_required"] = False
        approved["reflection_count"] = int(approved["reflection_count"]) + 1
        approved["next_reflection_at"] = self._format_time(
            datetime.now(UTC)
            + timedelta(minutes=int(approved["reflection_minutes"]))
        )
        approved["last_failure_class"] = None
        approved["last_error"] = None
        approved["active_prompt"] = None
        approved["active_model"] = None
        approved["active_model_route"] = None
        self._save(approved)
        self._event(
            self._session(),
            "reflection_completed",
            f"round {index}; decision {proposal.decision}",
        )
        return output_path

    def _strategy_reflection_prompt(
        self,
        state: dict[str, Any],
        master_text: str,
    ) -> str:
        completed = int(state.get("round_count", 0))
        active = state.get("active_strategy")
        remaining = self.project.autorun.max_strategy_executions
        if isinstance(active, dict):
            remaining = max(
                0, int(active.get("hard_deadline_execution", completed)) - completed
            )
        replacement_required = self._strategy_replacement_required(state)
        return f"""# Strategy governance review

You are the read-only strategy governor. Select or revise the method and its
observable soft gates. Do not execute work, edit files, adjudicate progress, alter
operator policy, or weaken the living master contract. A due checkpoint or review
date requests a decision; it does not by itself falsify a method. When replacement
is required, select a genuinely different course rather than renaming the old one.

## Living Master Prompt

{master_text}

## Current retained contract

```json
{json.dumps(active, indent=2, sort_keys=True)}
```

## Immutable controller context

- Completed successful executions: {completed}
- Remaining executions in the current lineage: {remaining}
- Replacement is mandatory: {str(replacement_required).lower()}
- Operator maximum for a new lineage: {self.project.autorun.max_strategy_executions}
- Last execution output: `{state.get("last_output") or "None"}`
- Last independent adjudication: `{state.get("last_adjudication_review") or "None"}`
- Last controller error: `{state.get("last_error") or "None"}`

## Recent independently adjudicated trajectory

{self._recent_progress_history(state)}

## Required protocol

End with exactly one final single-line marker whose value is a JSON object:

STRATEGY_PROPOSAL_JSON: {{"schema_version":1,"decision":"select|continue|change_course","base_strategy_id":null,"base_revision":null,"selected_method":"method","decision_reason":"reason","next_action":"action","review_after_executions":1,"checkpoints":[{{"id":"check_id","after_executions":1,"observable":"observable effect"}}],"stop_conditions":[{{"id":"stop_id","observable":"observable trigger"}}]}}

Use `select` only when no active contract exists. For `continue` or
`change_course`, copy the exact active strategy ID and revision into the base
fields. Offsets are relative to the current successful-execution count and must be
strictly increasing. A continuation is bounded by the remaining current-lineage
budget; a selection or course change is bounded by the operator maximum for its
new lineage.
"""

    def _materialize_strategy_contract(
        self,
        attempt: int,
        state: dict[str, Any],
        proposal: _StrategyProposal,
    ) -> StrategyContract:
        completed = int(state.get("round_count", 0))
        previous = state.get("active_strategy")
        history = list(state.get("strategy_history", []))
        if isinstance(previous, dict):
            archived = json.loads(json.dumps(previous))
            if archived.get("status") == "active":
                archived["status"] = "superseded"
            if proposal.decision == "continue":
                for checkpoint in archived.get("checkpoints", []):
                    if (
                        isinstance(checkpoint, dict)
                        and checkpoint.get("status") in {"pending", "advanced"}
                    ):
                        checkpoint["status"] = "revised"
            history.append(archived)
        state["strategy_history"] = history[-_STRATEGY_HISTORY_LIMIT:]

        if proposal.decision == "continue":
            assert isinstance(previous, dict)
            strategy_id = str(previous["strategy_id"])
            revision = int(previous["revision"]) + 1
            lineage_started = int(previous["lineage_started_execution"])
            hard_deadline = int(previous["hard_deadline_execution"])
        else:
            used_numbers: list[int] = []
            for candidate in [*history, previous]:
                if isinstance(candidate, dict):
                    identifier = candidate.get("strategy_id")
                    if (
                        isinstance(identifier, str)
                        and identifier.startswith("strategy-")
                        and identifier.removeprefix("strategy-").isdigit()
                    ):
                        used_numbers.append(
                            int(identifier.removeprefix("strategy-"))
                        )
            strategy_id = f"strategy-{max(used_numbers, default=0) + 1:05d}"
            revision = 1
            lineage_started = completed
            hard_deadline = (
                completed + self.project.autorun.max_strategy_executions
            )
        return StrategyContract(
            schema_version=2,
            strategy_id=strategy_id,
            revision=revision,
            status="active",
            selected_method=proposal.selected_method,
            decision_reason=proposal.decision_reason,
            accepted_attempt=attempt,
            accepted_execution=completed,
            lineage_started_execution=lineage_started,
            hard_deadline_execution=hard_deadline,
            review_due_execution=completed + proposal.review_after_executions,
            next_action=proposal.next_action,
            checkpoints=[
                StrategyCheckpoint(
                    id=str(item["id"]),
                    due_execution=completed + int(item["after_executions"]),
                    observable=str(item["observable"]),
                    status="pending",
                    last_result=None,
                    last_adjudication_execution=None,
                )
                for item in proposal.checkpoints
            ],
            stop_conditions=[
                StrategyStopCondition(
                    id=str(item["id"]),
                    observable=str(item["observable"]),
                    triggered=False,
                    last_adjudication_execution=None,
                )
                for item in proposal.stop_conditions
            ],
            last_alignment=None,
            last_checkpoint_result=None,
        )

    @staticmethod
    def _soft_gate_due(state: dict[str, Any]) -> bool:
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict):
            return True
        completed = int(state.get("round_count", 0))
        if completed >= int(strategy.get("review_due_execution", completed)):
            return True
        checkpoints = strategy.get("checkpoints")
        return not isinstance(checkpoints, list) or any(
            isinstance(item, dict)
            and item.get("status") in {"pending", "advanced"}
            and completed >= int(item.get("due_execution", completed))
            for item in checkpoints
        )

    @staticmethod
    def _strategy_replacement_required(state: dict[str, Any]) -> bool:
        if bool(state.get("strategy_change_required", False)):
            return True
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict) or strategy.get("status") != "active":
            return True
        completed = int(state.get("round_count", 0))
        return completed >= int(
            strategy.get("hard_deadline_execution", completed)
        ) or (
            AutoRunRunner._soft_gate_due(state)
            and not AutoRunRunner._has_aligned_revision_progress(state)
        )


    @staticmethod
    def _strategy_requires_review(state: dict[str, Any]) -> bool:
        if bool(state.get("strategy_change_required", False)):
            return True
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict) or strategy.get("status") != "active":
            return True
        completed = int(state.get("round_count", 0))
        if completed >= int(strategy.get("hard_deadline_execution", completed)):
            return True
        return AutoRunRunner._soft_gate_due(state)

    @staticmethod
    def _has_aligned_revision_progress(state: dict[str, Any]) -> bool:
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict):
            return False
        accepted_execution = int(strategy.get("accepted_execution", 0))
        return any(
            isinstance(item, dict)
            and item.get("strategy_id") == strategy.get("strategy_id")
            and item.get("strategy_revision") == strategy.get("revision")
            and item.get("alignment") == "aligned"
            and item.get("checkpoint_result") in {"advanced", "satisfied"}
            and isinstance(item.get("execution"), int)
            and int(item["execution"]) > accepted_execution
            for item in state.get("adjudication_history", [])
        )

    def _recent_progress_history(self, state: dict[str, Any]) -> str:
        rows: list[str] = []
        for item in state.get("adjudication_history", [])[-20:]:
            if not isinstance(item, dict):
                continue
            rows.append(
                json.dumps(
                    {
                        "attempt": item.get("attempt"),
                        "execution": item.get("execution"),
                        "strategy_id": item.get("strategy_id"),
                        "strategy_revision": item.get("strategy_revision"),
                        "progress_class": item.get("progress_class"),
                        "alignment": item.get("alignment"),
                        "checkpoint_id": item.get("checkpoint_id"),
                        "checkpoint_result": item.get("checkpoint_result"),
                        "reason": item.get("reason"),
                        "verified_scope_delta": item.get("verified_scope_delta"),
                    },
                    sort_keys=True,
                )
            )
        return "\n".join(rows) if rows else "No retained independent adjudications."

    @staticmethod
    def _strict_json_marker(text: str, marker: str) -> tuple[object | None, list[str]]:
        prefix = f"{marker}:"
        lines = text.splitlines()
        matches = [line for line in lines if line.startswith(prefix)]
        if len(matches) != 1:
            return None, [f"expected exactly one {marker} marker line"]
        nonempty = [line for line in lines if line.strip()]
        if not nonempty or nonempty[-1] != matches[0]:
            return None, [f"{marker} must be the final nonempty line"]
        payload = matches[0].removeprefix(prefix)
        if not payload.startswith(" ") or payload != payload.rstrip():
            return None, [f"{marker} must contain one trimmed JSON value"]
        try:
            return json.loads(payload[1:]), []
        except json.JSONDecodeError as exc:
            return None, [f"{marker} contains invalid JSON: {exc.msg}"]

    @staticmethod
    def _parse_strategy_proposal(
        text: str,
        *,
        state: dict[str, Any],
        max_strategy_executions: int,
    ) -> tuple[_StrategyProposal | None, list[str]]:
        raw, errors = AutoRunRunner._strict_json_marker(
            text, "STRATEGY_PROPOSAL_JSON"
        )
        if errors:
            return None, errors
        if not isinstance(raw, dict):
            return None, ["strategy proposal must be a JSON object"]
        required = {
            "schema_version",
            "decision",
            "base_strategy_id",
            "base_revision",
            "selected_method",
            "decision_reason",
            "next_action",
            "review_after_executions",
            "checkpoints",
            "stop_conditions",
        }
        if set(raw) != required:
            missing = sorted(required - raw.keys())
            unknown = sorted(raw.keys() - required)
            return None, [
                f"strategy proposal keys mismatch; missing={missing}; unknown={unknown}"
            ]
        if type(raw["schema_version"]) is not int or raw["schema_version"] != 1:
            errors.append("strategy proposal schema_version must be integer 1")
        decision = raw["decision"]
        if (
            not isinstance(decision, str)
            or decision not in {"select", "continue", "change_course"}
        ):
            errors.append("strategy proposal decision is invalid")
        for name in ("selected_method", "decision_reason", "next_action"):
            item = raw[name]
            if (
                not isinstance(item, str)
                or not item
                or item != item.strip()
                or len(item) > _TEXT_LIMIT
            ):
                errors.append(f"strategy proposal {name} must be trimmed text")
        review_after = raw["review_after_executions"]
        if type(review_after) is not int:
            errors.append("review_after_executions must be an integer")
        active = state.get("active_strategy")
        completed = int(state.get("round_count", 0))
        if decision == "continue" and isinstance(active, dict):
            offset_limit = (
                int(active.get("hard_deadline_execution", completed)) - completed
            )
        else:
            offset_limit = max_strategy_executions
        if (
            type(review_after) is not int
            or not 1 <= review_after <= offset_limit
        ):
            errors.append(
                "review_after_executions exceeds the available lineage executions"
            )
        base_id = raw["base_strategy_id"]
        base_revision = raw["base_revision"]
        if decision == "select":
            if active is not None or base_id is not None or base_revision is not None:
                errors.append("select requires no active strategy and null base fields")
        elif decision in {"continue", "change_course"}:
            if not isinstance(active, dict):
                errors.append(f"{decision} requires an active strategy")
            elif (
                base_id != active.get("strategy_id")
                or base_revision != active.get("revision")
                or type(base_revision) is not int
            ):
                errors.append(f"{decision} base strategy ID and revision are stale")
        if decision == "change_course" and active is None:
            errors.append("change_course is invalid without a prior active strategy")
        if (
            decision == "continue"
            and AutoRunRunner._strategy_replacement_required(state)
        ):
            errors.append("continue is forbidden because course replacement is required")

        def validate_items(
            name: str, required_keys: set[str], with_offset: bool
        ) -> tuple[dict[str, Any], ...]:
            value = raw[name]
            if not isinstance(value, list) or not 1 <= len(value) <= 8:
                errors.append(f"{name} must contain 1 to 8 objects")
                return ()
            parsed: list[dict[str, Any]] = []
            ids: list[str] = []
            offsets: list[int] = []
            for index, item in enumerate(value):
                if not isinstance(item, dict) or set(item) != required_keys:
                    errors.append(f"{name}[{index}] has invalid keys")
                    continue
                item_id = item.get("id")
                observable = item.get("observable")
                if not isinstance(item_id, str) or _ID_PATTERN.fullmatch(item_id) is None:
                    errors.append(f"{name}[{index}].id is invalid")
                else:
                    ids.append(item_id)
                if (
                    not isinstance(observable, str)
                    or not observable
                    or observable != observable.strip()
                    or len(observable) > _TEXT_LIMIT
                ):
                    errors.append(f"{name}[{index}].observable must be trimmed text")
                if with_offset:
                    offset = item.get("after_executions")
                    if (
                        isinstance(offset, bool)
                        or not isinstance(offset, int)
                        or not 1 <= offset <= offset_limit
                    ):
                        errors.append(
                            f"{name}[{index}].after_executions is outside the lineage"
                        )
                    else:
                        offsets.append(offset)
                parsed.append(dict(item))
            if len(ids) != len(set(ids)):
                errors.append(f"{name} IDs must be unique")
            if with_offset and offsets != sorted(set(offsets)):
                errors.append("checkpoint offsets must be strictly increasing")
            return tuple(parsed)

        checkpoints = validate_items(
            "checkpoints", {"id", "after_executions", "observable"}, True
        )
        stop_conditions = validate_items(
            "stop_conditions", {"id", "observable"}, False
        )
        if errors:
            return None, errors
        return (
            _StrategyProposal(
                decision=str(decision),
                base_strategy_id=base_id,
                base_revision=base_revision,
                selected_method=str(raw["selected_method"]),
                decision_reason=str(raw["decision_reason"]),
                next_action=str(raw["next_action"]),
                review_after_executions=int(review_after),
                checkpoints=checkpoints,
                stop_conditions=stop_conditions,
            ),
            [],
        )

    @staticmethod
    def _parse_conductor_claim(text: str) -> dict[str, Any] | None:
        raw, errors = AutoRunRunner._strict_json_marker(text, "CONDUCTOR_RESULT_JSON")
        if errors or not isinstance(raw, dict):
            return None
        required = {
            "schema_version",
            "strategy_id",
            "strategy_revision",
            "checkpoint_id",
            "progress_class",
            "summary",
            "evidence",
        }
        if set(raw) != required:
            return None
        if (
            type(raw["schema_version"]) is not int
            or raw["schema_version"] != 1
            or not isinstance(raw["progress_class"], str)
            or raw["progress_class"] not in _PROGRESS_CLASSES
            or not isinstance(raw["strategy_id"], str)
            or type(raw["strategy_revision"]) is not int
            or (
                raw["checkpoint_id"] is not None
                and not isinstance(raw["checkpoint_id"], str)
            )
            or not isinstance(raw["summary"], str)
            or not isinstance(raw["evidence"], str)
        ):
            return None
        return raw

    def _round_prompt(
        self,
        index: int,
        state: dict[str, Any],
        master_text: str,
    ) -> str:
        strategy = state.get("active_strategy")
        assert isinstance(strategy, dict)
        active_strategy = json.dumps(strategy, indent=2, sort_keys=True)
        return f"""# Autorun conductor round {index}

You are the configured primary conductor for an unattended project session. Work
directly in `{self.project.root}` and execute the deeply validated active contract.
Preserve the living master contract and configured trust and resource policy.
Verify observable effects, do not silently drift, and do not weaken acceptance
criteria. Do not merely propose work for a later agent.

## Living Master Prompt

Source: `{self.master_prompt}`

{master_text}

## Retained context

- Autorun session: `{self._session()}`
- Previous output: `{state.get("last_output") or "None"}`
- Previous receipt: `{state.get("last_receipt") or "None"}`
- Previous controller or agent error: `{state.get("last_error") or "None"}`
- Consecutive execution failures: {int(state.get("consecutive_execution_failures", 0))}
- Completed successful executions: {int(state.get("round_count", 0))}

## Enforceable active strategy contract

```json
{active_strategy}
```

Execute the contract's next action and relevant current checkpoint. Inspect
retained evidence first, implement a complete reachable change now, and run
focused verification for significant changes. If observed evidence conflicts with
the method, checkpoint, stop conditions, or acceptance criteria, report that
conflict rather than substituting a nearby task. Keep commands inside the inherited
resource controls and save all useful work before returning.

End with exactly one final single-line claim. This report is evidence supplied to
the independent adjudicator and cannot mutate governance state:

CONDUCTOR_RESULT_JSON: {{"schema_version":1,"strategy_id":"{strategy['strategy_id']}","strategy_revision":{strategy['revision']},"checkpoint_id":null,"progress_class":"incremental|meaningful|blocked|complete","summary":"factual result","evidence":"retained artifact or verified observable"}}
"""

    def _conductor_model(self, state: dict[str, Any]) -> tuple[str | None, str]:
        del state
        return self.options.model or self.project.planner_model, "primary"

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
            with self._heartbeat():
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
        with self._state_lock:
            return self._read_state_from(self._session())

    @staticmethod
    def _read_state_from(session: Path) -> dict[str, Any]:
        try:
            loaded = json.loads((session / "state.json").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise AutoRunError(f"cannot read autorun state: {exc}") from exc
        if not isinstance(loaded, dict):
            raise AutoRunError("autorun state is malformed")
        value: dict[str, Any] = dict(loaded)
        version = value.get("schema_version")
        if type(version) is not int:
            raise AutoRunError(f"unsupported autorun state schema: {version!r}")
        if version == 1:
            retained_attempts = [
                int(path.name.removeprefix("round-"))
                for path in (session / "rounds").glob("round-*")
                if path.is_dir() and path.name.removeprefix("round-").isdigit()
            ]
            value["schema_version"] = 2
            value["attempt_count"] = max(
                [int(value.get("round_count", 0)), *retained_attempts], default=0
            )
            value["consecutive_execution_failures"] = int(
                value.pop("consecutive_failures", 0)
            )
            value.update(
                {
                    "meaningful_round_count": int(
                        value.get("meaningful_round_count", 0)
                    ),
                    "incremental_round_count": int(
                        value.get("incremental_round_count", 0)
                    ),
                    "blocked_round_count": int(value.get("blocked_round_count", 0)),
                    "complete_round_count": int(value.get("complete_round_count", 0)),
                    "unclassified_round_count": int(
                        value.get("unclassified_round_count", 0)
                    ),
                    "controller_failure_count": 0,
                    "agent_execution_failure_count": 0,
                    "verification_failure_count": 0,
                    "strategy_gate_failure_count": 0,
                    "mathematical_blocker_count": int(
                        value.get("blocked_round_count", 0)
                    ),
                    "last_failure_class": None,
                    "active_strategy": None,
                    "strategy_history": [],
                    "last_progress_claim": value.get("last_progress_class"),
                    "last_progress_adjudication": None,
                    "last_adjudication_review": None,
                    "last_adjudication_model": None,
                }
            )
            version = 2
        if version == 2:
            legacy_names = {
                "active_strategy",
                "strategy_history",
                "last_strategy_likelihood",
                "last_strategy_threshold",
                "last_strategy_worthwhile",
                "last_strategy_decision",
                "last_strategy_plan_status",
                "last_strategy_review",
                "last_strategy_round",
            }
            legacy = {
                name: value.get(name)
                for name in legacy_names
                if name in value
            }
            history = list(value.get("strategy_history", []))
            old_active = value.get("active_strategy")
            if isinstance(old_active, dict):
                archived = json.loads(json.dumps(old_active))
                archived["status"] = "superseded"
                archived["archive_reason"] = "state_schema_upgrade"
                history.append(archived)
            adjudication_history: list[dict[str, Any]] = []
            old_adjudication = value.get("last_progress_adjudication")
            required_adjudication = {
                "strategy_id",
                "strategy_revision",
                "progress_class",
                "alignment",
                "checkpoint_id",
                "checkpoint_result",
                "triggered_stop_condition_id",
                "reason",
                "verified_scope_delta",
            }
            if (
                isinstance(old_adjudication, dict)
                and required_adjudication <= old_adjudication.keys()
            ):
                adjudication_history.append(
                    {
                        "attempt": int(value.get("attempt_count", 0)),
                        "execution": int(value.get("round_count", 0)),
                        **{
                            name: old_adjudication[name]
                            for name in required_adjudication
                        },
                        "artifact": value.get("last_adjudication_review"),
                    }
                )
            for name in legacy_names:
                value.pop(name, None)
            value.update(
                {
                    "schema_version": 3,
                    "active_strategy": None,
                    "strategy_history": history[-_STRATEGY_HISTORY_LIMIT:],
                    "adjudication_history": adjudication_history,
                    "legacy_strategy_state": legacy,
                    "strategy_change_required": True,
                    "next_reflection_at": utc_now(),
                    "last_strategy_decision": None,
                    "last_strategy_review": None,
                    "last_strategy_round": None,
                }
            )
            version = 3
        if version != 3:
            raise AutoRunError(f"unsupported autorun state schema: {version!r}")
        value.pop("active_strategy_pass", None)

        defaults: dict[str, Any] = {
            "attempt_count": int(value.get("round_count", 0)),
            "reflection_count": 0,
            "meaningful_round_count": 0,
            "incremental_round_count": 0,
            "blocked_round_count": 0,
            "complete_round_count": 0,
            "unclassified_round_count": 0,
            "controller_failure_count": 0,
            "agent_execution_failure_count": 0,
            "verification_failure_count": 0,
            "strategy_gate_failure_count": 0,
            "mathematical_blocker_count": 0,
            "consecutive_execution_failures": 0,
            "strategy_history": [],
            "adjudication_history": [],
            "legacy_strategy_state": None,
            "active_strategy": None,
            "strategy_change_required": False,
            "repeated_output_count": 0,
            "stop_requested": False,
        }
        for name, default in defaults.items():
            value.setdefault(name, default)

        required_text = {
            "session_id",
            "status",
            "created_at",
            "updated_at",
            "heartbeat_at",
            "next_reflection_at",
        }
        if any(
            not isinstance(value.get(name), str) or not str(value[name]).strip()
            for name in required_text
        ):
            raise AutoRunError("autorun state has invalid text or timestamp fields")
        for name in ("created_at", "updated_at", "heartbeat_at", "next_reflection_at"):
            try:
                AutoRunRunner._parse_time(str(value[name]))
            except (TypeError, ValueError, AutoRunError) as exc:
                raise AutoRunError(f"autorun state field {name} is invalid") from exc
        if not isinstance(value["status"], str) or value["status"] not in {
            "running",
            "recovering",
            "paused",
            "stopped",
        }:
            raise AutoRunError("autorun state has an invalid status")
        count_fields = {
            "round_count",
            "attempt_count",
            "reflection_count",
            "meaningful_round_count",
            "incremental_round_count",
            "blocked_round_count",
            "complete_round_count",
            "unclassified_round_count",
            "controller_failure_count",
            "agent_execution_failure_count",
            "verification_failure_count",
            "strategy_gate_failure_count",
            "mathematical_blocker_count",
            "consecutive_execution_failures",
            "repeated_output_count",
        }
        for name in count_fields:
            item = value.get(name)
            if isinstance(item, bool) or not isinstance(item, int) or item < 0:
                raise AutoRunError(f"autorun state field {name} must be nonnegative")
        if int(value["attempt_count"]) < int(value["round_count"]):
            raise AutoRunError("autorun attempt count precedes completed executions")
        for name in ("strategy_change_required", "stop_requested"):
            if not isinstance(value.get(name), bool):
                raise AutoRunError(f"autorun state field {name} must be boolean")
        strategy = value.get("active_strategy")
        if strategy is not None:
            AutoRunRunner._validate_strategy_contract(
                strategy,
                completed_execution=int(value["round_count"]),
                require_active=False,
            )
            if int(strategy["accepted_attempt"]) > int(value["attempt_count"]):
                raise AutoRunError("active strategy acceptance attempt is in the future")
            if strategy["status"] in {"drifted", "falsified", "expired"} and not bool(
                value["strategy_change_required"]
            ):
                raise AutoRunError(
                    "terminal strategy rejection must require course replacement"
                )
            if strategy["status"] == "complete" and value["status"] != "stopped":
                raise AutoRunError("a complete strategy requires a stopped session")
        history = value.get("strategy_history")
        if not isinstance(history, list) or not all(
            isinstance(item, dict) for item in history
        ):
            raise AutoRunError("strategy history must be an array of objects")
        adjudications = value.get("adjudication_history")
        if not isinstance(adjudications, list):
            raise AutoRunError("adjudication history must be an array")
        for item in adjudications:
            AutoRunRunner._validate_adjudication_history_entry(
                item, int(value["round_count"]), int(value["attempt_count"])
            )
        if isinstance(strategy, dict):
            prior_revisions = [
                int(item["revision"])
                for item in history
                if item.get("schema_version") == 2
                and item.get("strategy_id") == strategy["strategy_id"]
                and isinstance(item.get("revision"), int)
                and not isinstance(item.get("revision"), bool)
            ]
            if prior_revisions and max(prior_revisions) >= int(strategy["revision"]):
                raise AutoRunError("active strategy revision does not follow history")
        return value

    @staticmethod
    def _validate_strategy_contract(
        strategy: object,
        *,
        completed_execution: int,
        require_active: bool,
    ) -> None:
        if not isinstance(strategy, dict):
            raise AutoRunError("active strategy contract must be an object")
        required = {
            "schema_version",
            "strategy_id",
            "revision",
            "status",
            "selected_method",
            "decision_reason",
            "accepted_attempt",
            "accepted_execution",
            "lineage_started_execution",
            "hard_deadline_execution",
            "review_due_execution",
            "next_action",
            "checkpoints",
            "stop_conditions",
            "last_alignment",
            "last_checkpoint_result",
        }
        if set(strategy) != required:
            raise AutoRunError("active strategy contract has unknown or missing fields")
        if (
            type(strategy["schema_version"]) is not int
            or strategy["schema_version"] != 2
        ):
            raise AutoRunError("active strategy contract schema must be integer 2")
        strategy_id = strategy["strategy_id"]
        if (
            not isinstance(strategy_id, str)
            or re.fullmatch(r"strategy-[0-9]{5}", strategy_id) is None
        ):
            raise AutoRunError("active strategy ID is invalid")
        revision = strategy["revision"]
        if type(revision) is not int or revision < 1:
            raise AutoRunError("active strategy revision must be positive")
        statuses = {
            "active",
            "drifted",
            "falsified",
            "complete",
            "superseded",
            "expired",
        }
        if (
            not isinstance(strategy["status"], str)
            or strategy["status"] not in statuses
        ):
            raise AutoRunError("active strategy contract has an invalid status")
        if require_active and strategy["status"] != "active":
            raise AutoRunError("execution requires an active strategy contract")
        for name in ("selected_method", "decision_reason", "next_action"):
            text = strategy[name]
            if (
                not isinstance(text, str)
                or not text
                or text != text.strip()
                or len(text) > _TEXT_LIMIT
            ):
                raise AutoRunError(f"active strategy field {name} is invalid")
        counters: dict[str, int] = {}
        for name in (
            "accepted_attempt",
            "accepted_execution",
            "lineage_started_execution",
            "hard_deadline_execution",
            "review_due_execution",
        ):
            item = strategy[name]
            if isinstance(item, bool) or not isinstance(item, int) or item < 0:
                raise AutoRunError(f"active strategy field {name} is invalid")
            counters[name] = item
        if not (
            counters["lineage_started_execution"]
            <= counters["accepted_execution"]
            <= completed_execution
        ):
            raise AutoRunError("active strategy base counters are inconsistent")
        if not (
            counters["accepted_execution"]
            < counters["review_due_execution"]
            <= counters["hard_deadline_execution"]
        ):
            raise AutoRunError("active strategy soft deadline ordering is invalid")
        lineage_budget = (
            counters["hard_deadline_execution"]
            - counters["lineage_started_execution"]
        )
        if not 1 <= lineage_budget <= 100:
            raise AutoRunError("active strategy hard lineage deadline is inconsistent")
        checkpoints = strategy["checkpoints"]
        if not isinstance(checkpoints, list) or not 1 <= len(checkpoints) <= 8:
            raise AutoRunError("active strategy checkpoints must contain 1 to 8 items")
        checkpoint_ids: list[str] = []
        checkpoint_deadlines: list[int] = []
        for checkpoint in checkpoints:
            if not isinstance(checkpoint, dict) or set(checkpoint) != {
                "id",
                "due_execution",
                "observable",
                "status",
                "last_result",
                "last_adjudication_execution",
            }:
                raise AutoRunError("active strategy checkpoint is malformed")
            checkpoint_id = checkpoint["id"]
            if (
                not isinstance(checkpoint_id, str)
                or _ID_PATTERN.fullmatch(checkpoint_id) is None
            ):
                raise AutoRunError("active strategy checkpoint ID is invalid")
            checkpoint_ids.append(checkpoint_id)
            due = checkpoint["due_execution"]
            if (
                isinstance(due, bool)
                or not isinstance(due, int)
                or not counters["accepted_execution"]
                < due
                <= counters["hard_deadline_execution"]
            ):
                raise AutoRunError("active strategy checkpoint deadline is invalid")
            checkpoint_deadlines.append(due)
            observable = checkpoint["observable"]
            if (
                not isinstance(observable, str)
                or not observable
                or observable != observable.strip()
                or len(observable) > _TEXT_LIMIT
            ):
                raise AutoRunError("active strategy checkpoint observable is invalid")
            if (
                not isinstance(checkpoint["status"], str)
                or checkpoint["status"]
                not in {
                    "pending",
                    "advanced",
                    "satisfied",
                    "revised",
                    "falsified",
                }
            ):
                raise AutoRunError("active strategy checkpoint status is invalid")
            result = checkpoint["last_result"]
            if (
                result is not None
                and (
                    not isinstance(result, str)
                    or result
                    not in {
                        "advanced",
                        "satisfied",
                        "unchanged",
                        "falsified",
                        "n/a",
                    }
                )
            ):
                raise AutoRunError("active strategy checkpoint result is invalid")
            adjudicated_at = checkpoint["last_adjudication_execution"]
            if adjudicated_at is not None and (
                isinstance(adjudicated_at, bool)
                or not isinstance(adjudicated_at, int)
                or not 0 <= adjudicated_at <= completed_execution
            ):
                raise AutoRunError("active strategy checkpoint adjudication is invalid")
        if (
            len(checkpoint_ids) != len(set(checkpoint_ids))
            or checkpoint_deadlines != sorted(set(checkpoint_deadlines))
        ):
            raise AutoRunError("active strategy checkpoints are not unique and ordered")
        stop_conditions = strategy["stop_conditions"]
        if not isinstance(stop_conditions, list) or not 1 <= len(stop_conditions) <= 8:
            raise AutoRunError(
                "active strategy stop conditions must contain 1 to 8 items"
            )
        stop_ids: list[str] = []
        for stop in stop_conditions:
            if not isinstance(stop, dict) or set(stop) != {
                "id",
                "observable",
                "triggered",
                "last_adjudication_execution",
            }:
                raise AutoRunError("active strategy stop condition is malformed")
            stop_id = stop["id"]
            if not isinstance(stop_id, str) or _ID_PATTERN.fullmatch(stop_id) is None:
                raise AutoRunError("active strategy stop condition ID is invalid")
            stop_ids.append(stop_id)
            observable = stop["observable"]
            if (
                not isinstance(observable, str)
                or not observable
                or observable != observable.strip()
                or len(observable) > _TEXT_LIMIT
            ):
                raise AutoRunError("active strategy stop condition observable is invalid")
            if not isinstance(stop["triggered"], bool):
                raise AutoRunError("active strategy stop trigger must be boolean")
            adjudicated_at = stop["last_adjudication_execution"]
            if adjudicated_at is not None and (
                isinstance(adjudicated_at, bool)
                or not isinstance(adjudicated_at, int)
                or not 0 <= adjudicated_at <= completed_execution
            ):
                raise AutoRunError("active strategy stop adjudication is invalid")
        if len(stop_ids) != len(set(stop_ids)):
            raise AutoRunError("active strategy stop condition IDs must be unique")
        last_alignment = strategy["last_alignment"]
        if (
            last_alignment is not None
            and (
                not isinstance(last_alignment, str)
                or last_alignment
                not in {"aligned", "drifted", "falsified", "complete", "n/a"}
            )
        ):
            raise AutoRunError("active strategy last alignment is invalid")
        last_result = strategy["last_checkpoint_result"]
        if (
            last_result is not None
            and (
                not isinstance(last_result, str)
                or last_result
                not in {
                    "advanced",
                    "satisfied",
                    "unchanged",
                    "falsified",
                    "n/a",
                }
            )
        ):
            raise AutoRunError("active strategy last checkpoint result is invalid")

    @staticmethod
    def _validate_adjudication_history_entry(
        entry: object, completed_execution: int, attempt_count: int
    ) -> None:
        if not isinstance(entry, dict):
            raise AutoRunError("adjudication history entry must be an object")
        required = {
            "attempt",
            "execution",
            "strategy_id",
            "strategy_revision",
            "progress_class",
            "alignment",
            "checkpoint_id",
            "checkpoint_result",
            "triggered_stop_condition_id",
            "reason",
            "verified_scope_delta",
            "artifact",
        }
        if set(entry) != required:
            raise AutoRunError("adjudication history entry has unknown or missing fields")
        for name, maximum in (
            ("attempt", attempt_count),
            ("execution", completed_execution),
        ):
            item = entry[name]
            if (
                isinstance(item, bool)
                or not isinstance(item, int)
                or not 0 <= item <= maximum
            ):
                raise AutoRunError(f"adjudication history {name} is invalid")
        if (
            not isinstance(entry["strategy_id"], str)
            or re.fullmatch(r"strategy-[0-9]{5}", entry["strategy_id"]) is None
            or type(entry["strategy_revision"]) is not int
            or entry["strategy_revision"] < 1
            or not isinstance(entry["progress_class"], str)
            or entry["progress_class"] not in _PROGRESS_CLASSES
            or not isinstance(entry["alignment"], str)
            or entry["alignment"]
            not in {"aligned", "drifted", "falsified", "complete", "n/a"}
            or not isinstance(entry["checkpoint_result"], str)
            or entry["checkpoint_result"]
            not in {"advanced", "satisfied", "unchanged", "falsified", "n/a"}
        ):
            raise AutoRunError("adjudication history classification is invalid")
        for name in ("checkpoint_id", "triggered_stop_condition_id"):
            item = entry[name]
            if item is not None and (
                not isinstance(item, str) or _ID_PATTERN.fullmatch(item) is None
            ):
                raise AutoRunError(f"adjudication history {name} is invalid")
        for name in ("reason", "verified_scope_delta"):
            item = entry[name]
            if (
                not isinstance(item, str)
                or not item
                or item != item.strip()
                or len(item) > _TEXT_LIMIT
            ):
                raise AutoRunError(f"adjudication history {name} is invalid")
        if entry["artifact"] is not None and not isinstance(entry["artifact"], str):
            raise AutoRunError("adjudication history artifact is invalid")

    def _save(self, state: dict[str, Any]) -> None:
        with self._state_lock:
            state["updated_at"] = utc_now()
            atomic_write_json(self._session() / "state.json", state)

    @contextmanager
    def _heartbeat(self) -> Iterator[None]:
        stopped = threading.Event()

        def update_heartbeat() -> None:
            while not stopped.wait(15):
                current = self._state()
                current["heartbeat_at"] = utc_now()
                self._save(current)

        heartbeat = threading.Thread(target=update_heartbeat, daemon=True)
        heartbeat.start()
        try:
            yield
        finally:
            stopped.set()
            heartbeat.join()

    def _execute_with_heartbeat(self, request_path: Path) -> int:
        with self._heartbeat():
            return execute_agent_request(request_path)

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

    def _run_progress_metrics(
        self, round_dir: Path
    ) -> tuple[list[dict[str, Any]], int]:
        results: list[dict[str, Any]] = []
        failures = 0
        for metric in self.project.autorun.progress_metrics:
            with self._heartbeat():
                captured = run_captured_command(
                    metric.command,
                    cwd=self.project.root,
                    env=os.environ,
                    timeout=metric.timeout,
                    execution=self.project.execution,
                    workspace=self.project.root,
                    allow_workspace_executables=True,
                    run_dir=self._session(),
                    read_paths=(self.project.root, self._session()),
                )
            parsed: object | None = None
            parse_error: str | None = None
            if captured.exit_code == 0 and captured.error is None:
                try:
                    parsed = json.loads(captured.stdout)
                    if not isinstance(parsed, dict):
                        raise TypeError("metric output is not a JSON object")
                except (json.JSONDecodeError, TypeError) as exc:
                    parse_error = str(exc)
            else:
                parse_error = captured.error or f"exit code {captured.exit_code}"
            if parse_error is not None:
                failures += 1
            retained = {
                "schema_version": 1,
                "metric_id": metric.metric_id,
                "command": list(metric.command),
                "exit_code": captured.exit_code,
                "error": parse_error,
                "value": parsed,
                "stdout": captured.stdout,
                "stderr": captured.stderr,
                "stdout_sha256": captured.stdout_sha256,
                "stderr_sha256": captured.stderr_sha256,
                "stdout_truncated": captured.stdout_truncated,
                "stderr_truncated": captured.stderr_truncated,
            }
            atomic_write_json(
                round_dir / f"progress-metric-{metric.metric_id}.json", retained
            )
            results.append(retained)
        atomic_write_json(round_dir / "progress-metrics.json", results)
        return results, failures

    @staticmethod
    def _earliest_admissible_checkpoint(
        strategy: dict[str, Any],
    ) -> dict[str, Any] | None:
        return next(
            (
                item
                for item in strategy.get("checkpoints", [])
                if isinstance(item, dict)
                and item.get("status") in {"pending", "advanced"}
            ),
            None,
        )

    def _run_progress_adjudication(
        self,
        index: int,
        round_dir: Path,
        conductor_output: Path,
        metrics: list[dict[str, Any]],
    ) -> tuple[_ProgressAdjudication | None, Path, str | None]:
        prompt_path = round_dir / "progress-adjudication-prompt.md"
        output_path = round_dir / "progress-adjudication.md"
        receipt_path = round_dir / "progress-adjudication-receipt.json"
        request_path = round_dir / "progress-adjudication-request.json"
        current = self._state()
        strategy = current.get("active_strategy")
        self._validate_strategy_contract(
            strategy,
            completed_execution=int(current.get("round_count", 0)),
            require_active=True,
        )
        assert isinstance(strategy, dict)
        model = (
            self.project.analysis_model
            or self.options.model
            or self.project.planner_model
        )
        conductor_text = conductor_output.read_text(encoding="utf-8").strip()
        claim = self._parse_conductor_claim(conductor_text)
        claim_mismatch = claim is None or (
            claim.get("strategy_id") != strategy["strategy_id"]
            or claim.get("strategy_revision") != strategy["revision"]
            or (
                claim.get("checkpoint_id") is not None
                and claim.get("checkpoint_id")
                not in {
                    item["id"]
                    for item in strategy["checkpoints"]
                    if isinstance(item, dict)
                }
            )
        )
        expected_checkpoint = self._earliest_admissible_checkpoint(strategy)
        if expected_checkpoint is None:
            checkpoint_instructions = """- Earliest admissible checkpoint: none.
- Observable: none; the active strategy has no pending or advanced checkpoint.
- No non-`n/a` checkpoint result is admissible. Use `checkpoint_result="n/a"`
  with `checkpoint_id=null`."""
        else:
            expected_checkpoint_id = expected_checkpoint["id"]
            expected_checkpoint_observable = expected_checkpoint["observable"]
            checkpoint_instructions = f"""- Earliest admissible checkpoint ID: `{expected_checkpoint_id}`.
- Earliest admissible checkpoint observable: {json.dumps(expected_checkpoint_observable)}
- Every non-`n/a` `checkpoint_result` must use exactly
  `checkpoint_id="{expected_checkpoint_id}"`. A result naming any later checkpoint
  will be rejected, even when that later checkpoint was verified."""
        prompt = f"""# Independent autorun progress adjudication

You are a read-only adjudicator independent of both the strategy governor and the
conductor. Inspect retained artifacts, the repository, the active contract, and
trusted project metrics. Do not edit files. The conductor report is a claim, not
authority. Classify only verified observable progress toward the living master
contract. A report with a missing or mismatched strategy identity must be treated
as drift rather than credited to the active contract.

The required active strategy identity and checkpoint ordering are:

- Active strategy ID: `{strategy["strategy_id"]}`.
- Active strategy revision: `{strategy["revision"]}`.
{checkpoint_instructions}

`progress_class="complete"` and `alignment="complete"` each mean that the entire
Living Master Prompt is complete. They do not mean merely that the active
strategy, or even all of its checkpoints, is complete. If all strategy
checkpoints are complete but any global obligation in the Living Master Prompt
remains, use `progress_class="meaningful"`, not `"complete"`, and do not use
`alignment="complete"`.

## Living Master Prompt

{self.master_prompt.read_text(encoding="utf-8").strip()}

## Active strategy contract

```json
{json.dumps(strategy, indent=2, sort_keys=True)}
```

## Trusted project progress metrics

```json
{json.dumps(metrics, indent=2, sort_keys=True)}
```

## Conductor report

Source: `{conductor_output}`
Identity mismatch: {str(claim_mismatch).lower()}

{conductor_text[-30000:]}

End with exactly one final single-line marker:

PROGRESS_ADJUDICATION_JSON: {{"schema_version":1,"strategy_id":"{strategy['strategy_id']}","strategy_revision":{strategy['revision']},"progress_class":"incremental|meaningful|blocked|complete","alignment":"aligned|drifted|falsified|complete|n/a","checkpoint_id":null,"checkpoint_result":"advanced|satisfied|unchanged|falsified|n/a","triggered_stop_condition_id":null,"reason":"evidence-based reason","verified_scope_delta":"verified change in contract coverage"}}
"""
        atomic_write_text(prompt_path, prompt)
        read_only_tools = [
            tool
            for tool in self.project.allowed_tools
            if tool in {"read", "grep", "glob", "web_search"}
        ]
        atomic_write_json(
            request_path,
            {
                "role_id": "autorun_progress_adjudicator",
                "attempt": index,
                "omp": self.options.omp or self.project.omp,
                "workspace": str(self.project.root),
                "run_dir": str(self._session()),
                "prompt": str(prompt_path),
                "output": str(output_path),
                "stdout_log": str(round_dir / "progress-adjudication-stdout.log"),
                "stderr_log": str(round_dir / "progress-adjudication-stderr.log"),
                "receipt": str(receipt_path),
                "tools": read_only_tools,
                "model": model,
                "thinking": self.options.thinking or self.project.analysis_thinking,
                "max_time": self.project.autorun.adjudication_minutes * 60,
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
        active["active_model_route"] = "progress_adjudication"
        self._save(active)
        self._event(self._session(), "progress_adjudication_started", f"round {index}")
        exit_code = self._execute_with_heartbeat(request_path)
        if exit_code != 0 or not output_path.is_file():
            if claim_mismatch:
                blocked = self._state()
                blocked["strategy_change_required"] = True
                blocked["next_reflection_at"] = utc_now()
                self._save(blocked)
            return None, output_path, model
        adjudication = self._parse_progress_adjudication(
            output_path.read_text(encoding="utf-8"),
            strategy=strategy,
            claim_mismatch=claim_mismatch,
        )
        if adjudication is None and claim_mismatch:
            blocked = self._state()
            blocked["strategy_change_required"] = True
            blocked["next_reflection_at"] = utc_now()
            self._save(blocked)
        return adjudication, output_path, model

    @staticmethod
    def _parse_progress_adjudication(
        text: str,
        *,
        strategy: dict[str, Any],
        claim_mismatch: bool = False,
    ) -> _ProgressAdjudication | None:
        raw, errors = AutoRunRunner._strict_json_marker(
            text, "PROGRESS_ADJUDICATION_JSON"
        )
        if errors or not isinstance(raw, dict):
            return None
        required = {
            "schema_version",
            "strategy_id",
            "strategy_revision",
            "progress_class",
            "alignment",
            "checkpoint_id",
            "checkpoint_result",
            "triggered_stop_condition_id",
            "reason",
            "verified_scope_delta",
        }
        if set(raw) != required:
            return None
        if type(raw["schema_version"]) is not int or raw["schema_version"] != 1:
            return None
        if (
            raw["strategy_id"] != strategy.get("strategy_id")
            or type(raw["strategy_revision"]) is not int
            or raw["strategy_revision"] != strategy.get("revision")
        ):
            return None
        progress = raw["progress_class"]
        alignment = raw["alignment"]
        checkpoint_result = raw["checkpoint_result"]
        if not isinstance(progress, str) or progress not in _PROGRESS_CLASSES:
            return None
        if (
            not isinstance(alignment, str)
            or alignment
            not in {
                "aligned",
                "drifted",
                "falsified",
                "complete",
                "n/a",
            }
        ):
            return None
        if (
            not isinstance(checkpoint_result, str)
            or checkpoint_result
            not in {
                "advanced",
                "satisfied",
                "unchanged",
                "falsified",
                "n/a",
            }
        ):
            return None
        if claim_mismatch and alignment not in {"drifted", "falsified"}:
            return None
        if progress == "complete" and alignment != "complete":
            return None
        if alignment == "complete" and progress != "complete":
            return None
        checkpoint_id = raw["checkpoint_id"]
        expected = AutoRunRunner._earliest_admissible_checkpoint(strategy)
        if checkpoint_result == "n/a":
            if checkpoint_id is not None:
                return None
        elif (
            not isinstance(checkpoint_id, str)
            or not isinstance(expected, dict)
            or checkpoint_id != expected.get("id")
        ):
            return None
        if checkpoint_result == "falsified" and alignment != "falsified":
            return None
        stop_id = raw["triggered_stop_condition_id"]
        known_stop_ids = {
            item["id"]
            for item in strategy.get("stop_conditions", [])
            if isinstance(item, dict)
        }
        if stop_id is not None and (
            not isinstance(stop_id, str)
            or stop_id not in known_stop_ids
            or alignment != "falsified"
        ):
            return None
        if alignment == "falsified" and (
            checkpoint_result != "falsified" and stop_id is None
        ):
            return None
        for name in ("reason", "verified_scope_delta"):
            value = raw[name]
            if (
                not isinstance(value, str)
                or not value
                or value != value.strip()
                or len(value) > _TEXT_LIMIT
            ):
                return None
        return _ProgressAdjudication(
            strategy_id=str(raw["strategy_id"]),
            strategy_revision=int(raw["strategy_revision"]),
            progress_class=str(progress),
            alignment=str(alignment),
            checkpoint_id=checkpoint_id,
            checkpoint_result=str(checkpoint_result),
            triggered_stop_condition_id=stop_id,
            reason=str(raw["reason"]),
            verified_scope_delta=str(raw["verified_scope_delta"]),
        )

    @staticmethod
    def _apply_adjudication_to_strategy(
        state: dict[str, Any],
        adjudication: _ProgressAdjudication,
        *,
        attempt: int,
        execution: int,
        artifact: str,
    ) -> None:
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict):
            return
        if (
            adjudication.strategy_id != strategy.get("strategy_id")
            or adjudication.strategy_revision != strategy.get("revision")
        ):
            return
        retained = {
            "attempt": attempt,
            "execution": execution,
            "strategy_id": adjudication.strategy_id,
            "strategy_revision": adjudication.strategy_revision,
            "progress_class": adjudication.progress_class,
            "alignment": adjudication.alignment,
            "checkpoint_id": adjudication.checkpoint_id,
            "checkpoint_result": adjudication.checkpoint_result,
            "triggered_stop_condition_id": (
                adjudication.triggered_stop_condition_id
            ),
            "reason": adjudication.reason,
            "verified_scope_delta": adjudication.verified_scope_delta,
            "artifact": artifact,
        }
        state["adjudication_history"] = [
            *state.get("adjudication_history", []),
            retained,
        ]
        strategy = json.loads(json.dumps(strategy))
        strategy["last_alignment"] = adjudication.alignment
        strategy["last_checkpoint_result"] = adjudication.checkpoint_result
        if adjudication.checkpoint_id is not None and adjudication.alignment in {
            "aligned",
            "falsified",
        }:
            checkpoint = next(
                (
                    item
                    for item in strategy["checkpoints"]
                    if item["id"] == adjudication.checkpoint_id
                ),
                None,
            )
            if checkpoint is not None:
                checkpoint["last_result"] = adjudication.checkpoint_result
                checkpoint["last_adjudication_execution"] = execution
                if adjudication.checkpoint_result == "advanced":
                    checkpoint["status"] = "advanced"
                elif adjudication.checkpoint_result == "satisfied":
                    checkpoint["status"] = "satisfied"
                elif adjudication.checkpoint_result == "falsified":
                    checkpoint["status"] = "falsified"
        if adjudication.triggered_stop_condition_id is not None:
            stop = next(
                (
                    item
                    for item in strategy["stop_conditions"]
                    if item["id"] == adjudication.triggered_stop_condition_id
                ),
                None,
            )
            if stop is not None:
                stop["triggered"] = True
                stop["last_adjudication_execution"] = execution
        if (
            adjudication.alignment in {"drifted", "falsified"}
            or adjudication.checkpoint_result == "falsified"
            or adjudication.triggered_stop_condition_id is not None
        ):
            strategy["status"] = (
                "drifted"
                if adjudication.alignment == "drifted"
                else "falsified"
            )
            state["strategy_change_required"] = True
            state["next_reflection_at"] = utc_now()
        elif adjudication.alignment == "complete":
            strategy["status"] = "complete"
            state["status"] = "stopped"
            state["pid"] = None
        state["active_strategy"] = strategy

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


def _heartbeat_is_fresh(value: object, *, maximum_age_seconds: int = 90) -> bool:
    if not isinstance(value, str):
        return False
    try:
        heartbeat = datetime.fromisoformat(value)
    except ValueError:
        return False
    return (datetime.now(UTC) - heartbeat.astimezone(UTC)).total_seconds() <= (
        maximum_age_seconds
    )


def _round_receipt(
    session: Path,
    active_round: object,
    active_route: object,
) -> dict[str, Any]:
    if not isinstance(active_round, int) or isinstance(active_round, bool):
        return {}
    if active_route == "strategy_reflection":
        name = "strategy-reflection-receipt.json"
    elif active_route == "progress_adjudication":
        name = "progress-adjudication-receipt.json"
    else:
        name = "receipt.json"
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


def _last_round_claim(state: dict[str, Any]) -> dict[str, Any]:
    value = state.get("last_output")
    if not isinstance(value, str):
        return {}
    try:
        text = Path(value).read_text(encoding="utf-8")
    except OSError:
        return {}
    return AutoRunRunner._parse_conductor_claim(text) or {}


def _compact_strategy_field(value: str, *, limit: int = 150) -> str:
    normalized = " ".join(value.split())
    if len(normalized) <= limit:
        return normalized
    prefix = normalized[: limit - 1].rsplit(" ", 1)[0]
    return f"{prefix or normalized[: limit - 1]}…"


def _strategy_report_sections(state: dict[str, Any]) -> list[str]:
    strategy = state.get("active_strategy")
    if not isinstance(strategy, dict):
        return []
    checkpoints = strategy.get("checkpoints")
    current_checkpoint = next(
        (
            item
            for item in checkpoints
            if isinstance(item, dict)
            and item.get("status") in {"pending", "advanced"}
        ),
        None,
    ) if isinstance(checkpoints, list) else None
    checkpoint_text = (
        (
            f"{current_checkpoint.get('id')} at execution "
            f"{current_checkpoint.get('due_execution')}: "
            f"{_compact_strategy_field(str(current_checkpoint.get('observable', '')))} "
            f"({current_checkpoint.get('status')})"
        )
        if isinstance(current_checkpoint, dict)
        else "No pending checkpoint."
    )
    return [
        "ACTIVE STRATEGY CONTRACT",
        (
            f"{strategy.get('strategy_id')} revision {strategy.get('revision')} "
            f"is {strategy.get('status')}. "
            f"Method: {_compact_strategy_field(str(strategy.get('selected_method', '')))}"
        ),
        "NEXT ACTION",
        _compact_strategy_field(str(strategy.get("next_action", ""))),
        "NEXT CHECKPOINT",
        checkpoint_text,
        "ADAPTIVE REVIEW",
        f"Due at successful execution {strategy.get('review_due_execution')}.",
        "IMMUTABLE LINEAGE CEILING",
        (
            f"Started at execution {strategy.get('lineage_started_execution')}; "
            f"hard deadline {strategy.get('hard_deadline_execution')}."
        ),
    ]


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
    process_state = (
        "responding" if _pid_is_alive(state.get("pid")) else "not responding"
    )
    sections = [
        "PROGRESS UPDATE",
        (
            f"Updated {updated_at:%H:%M UTC}. The next automatic update is "
            f"scheduled for {next_update_at:%H:%M UTC}."
        ),
        "CURRENT RUN",
        (
            f"Controller: {status} and {process_state}. Session: "
            f"{state.get('round_count', 0)} completed executions, "
            f"{state.get('attempt_count', 0)} attempts, "
            f"{state.get('consecutive_execution_failures', 0)} consecutive "
            f"execution failures, {state.get('controller_failure_count', 0)} "
            f"controller failures, {state.get('verification_failure_count', 0)} "
            f"verification failures, and {state.get('reflection_count', 0)} "
            "strategy reviews."
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
        if route == "strategy_reflection":
            stage = "strategy reflection"
            log_name = "strategy-reflection-stdout.log"
        elif route == "progress_adjudication":
            stage = "progress adjudication"
            log_name = "progress-adjudication-stdout.log"
        else:
            stage = "conductor"
            log_name = "stdout.log"
        output_path = session / "rounds" / f"round-{active_round:05d}" / log_name
        output_size = output_path.stat().st_size if output_path.is_file() else 0
        model = state.get("active_model") or "default"
        sections.append(
            f"Round {active_round}: {stage} {receipt_status}{timing} on {model}; "
            f"retained live output {output_size} bytes."
        )
    else:
        sections.append("No conductor round is currently active.")
    sections.extend(_strategy_report_sections(state))
    sections.extend(
        [
            "INDEPENDENT PROGRESS",
            (
                "Retained adjudicated executions: "
                f"{state.get('meaningful_round_count', 0)} meaningful, "
                f"{state.get('incremental_round_count', 0)} incremental, "
                f"{state.get('blocked_round_count', 0)} blocked, "
                f"{state.get('complete_round_count', 0)} complete, "
                f"{state.get('unclassified_round_count', 0)} unclassified."
            ),
        ]
    )
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
        sections.extend(["VERIFIED BASELINE", evidence[0]])
    claim = _last_round_claim(state)
    if claim:
        sections.extend(
            [
                "LATEST COMPLETED EXECUTION",
                (
                    f"Conductor claim: {claim.get('progress_class', 'unclassified')}. "
                    f"{claim.get('summary', 'No retained summary.')}"
                ),
            ]
        )
        claimed_evidence = claim.get("evidence")
        if isinstance(claimed_evidence, str) and claimed_evidence:
            sections.extend(["CLAIMED EVIDENCE", claimed_evidence])
    else:
        sections.extend(
            [
                "LATEST COMPLETED EXECUTION",
                "No conductor execution has produced a retained result yet.",
            ]
        )
    error = state.get("last_error")
    sections.extend(
        [
            "CONTROLLER EXCEPTIONS",
            (
                str(error)
                if isinstance(error, str) and error
                else "No controller exception is currently retained."
            ),
        ]
    )
    latest_event = _latest_autorun_event(session)
    event_name = latest_event.get("event")
    if isinstance(event_name, str):
        event_text = f"The latest retained event is {event_name}"
        event_at = latest_event.get("at")
        event_detail = latest_event.get("detail")
        if isinstance(event_at, str):
            event_text += f" at {event_at}"
        if isinstance(event_detail, str) and len(event_detail) <= 160:
            event_text += f": {event_detail}"
        sections.extend(["LATEST RETAINED EVENT", f"{event_text}."])
    sections.extend(
        [
            "STRATEGY SCHEDULE",
            (
                "The next wall-clock strategy health review is scheduled for "
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
    recap_signature: tuple[object, ...] | None = None
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
                session,
                active_round,
                state.get("active_model_route"),
            )
            receipt_status = receipt.get(
                "status",
                "starting"
                if isinstance(active_round, int) and not isinstance(active_round, bool)
                else "idle",
            )
            pid_alive = _pid_is_alive(state.get("pid"))
            heartbeat_fresh = _heartbeat_is_fresh(state.get("heartbeat_at"))
            controller = (
                "up"
                if pid_alive and heartbeat_fresh
                else "stalled"
                if pid_alive
                else "down"
            )
            status = str(state.get("status", "unknown"))
            route = str(state.get("active_model_route") or "primary")
            activity = {
                "strategy_reflection": "reflection",
                "progress_adjudication": "adjudication",
            }.get(route, "agent")
            model_value = state.get("active_model")
            model = (
                f" · {str(model_value).rsplit('/', 1)[-1]}"
                if isinstance(model_value, str)
                else ""
            )
            detail = (
                f"controller {controller} · round {active_round or '-'} · "
                f"{activity} {receipt_status}{model} · "
                f"executions {state.get('round_count', 0)} · "
                f"exec/controller/verify failures "
                f"{state.get('consecutive_execution_failures', 0)}/"
                f"{state.get('controller_failure_count', 0)}/"
                f"{state.get('verification_failure_count', 0)}"
            )
            retry_at = state.get("next_retry_at")
            if status == "recovering" and isinstance(retry_at, str):
                detail += f" · retry at {retry_at}"
            strategy = state.get("active_strategy")
            strategy_signature = (
                json.dumps(strategy, sort_keys=True)
                if isinstance(strategy, dict)
                else None
            )
            current_recap_signature = (
                status,
                active_round,
                route,
                state.get("active_model"),
                receipt_status,
                state.get("round_count"),
                state.get("attempt_count"),
                state.get("reflection_count"),
                state.get("meaningful_round_count"),
                state.get("incremental_round_count"),
                state.get("blocked_round_count"),
                state.get("complete_round_count"),
                state.get("unclassified_round_count"),
                state.get("consecutive_execution_failures"),
                state.get("controller_failure_count"),
                state.get("verification_failure_count"),
                state.get("last_error"),
                state.get("next_retry_at"),
                state.get("last_output"),
                state.get("master_prompt_sha256"),
                strategy_signature,
            )
            now = time.monotonic()
            if (
                now >= next_recap_deadline
                or current_recap_signature != recap_signature
            ):
                updated_at = datetime.now(UTC)
                next_update_at = updated_at + timedelta(
                    seconds=recap_interval_seconds
                )
                recap = _progress_recap(
                    session,
                    state,
                    receipt,
                    updated_at=updated_at,
                    next_update_at=next_update_at,
                )
                recap_signature = current_recap_signature
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
    session: Path,
    active_round: object,
    route: object,
) -> Path | None:
    if not isinstance(active_round, int) or isinstance(active_round, bool):
        return None
    if route == "strategy_reflection":
        name = "strategy-reflection-stdout.log"
    elif route == "progress_adjudication":
        name = "progress-adjudication-stdout.log"
    else:
        name = "stdout.log"
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
