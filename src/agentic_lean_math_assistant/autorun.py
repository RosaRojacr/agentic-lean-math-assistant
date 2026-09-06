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
_STRATEGY_REVIEW_MAX_PASSES = 3
_PROGRESS_CLASSES = {"incremental", "meaningful", "blocked", "complete"}


@dataclass(frozen=True, slots=True)
class _StrategyAssessment:
    likelihood: int
    threshold: int
    worthwhile: bool
    decision: str
    plan_status: str
    replacement_likelihood: int | None
    first_evidence_rounds: int | None
    compute_cost: str | None
    alternatives: tuple[str, ...]
    milestones: tuple[tuple[int, str], ...]
    markers: dict[str, str]


@dataclass(frozen=True, slots=True)
class _ProgressAdjudication:
    progress_class: str
    strategy_alignment: str
    milestone_result: str
    reason: str
    verified_scope_delta: str
    milestone_index: int | None


class StrategyMilestone(TypedDict):
    index: int
    deadline_execution: int
    observable: str
    status: str


class StrategyContract(TypedDict):
    schema_version: int
    strategy_id: str
    status: str
    decision: str
    accepted_attempt: int
    accepted_execution: int
    horizon_rounds: int
    deadline_execution: int
    first_evidence_deadline_execution: int
    first_evidence_observed: bool
    course_to_abandon: str
    selected_method: str
    selected_likelihood: int | None
    worthwhile_threshold: int
    expected_compute_cost: str | None
    candidate_strategies: list[str]
    milestones: list[StrategyMilestone]
    first_falsifiable_check: str
    kill_criteria: list[str]
    next_action: str
    last_alignment: str | None
    last_milestone_result: str | None


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
    last_progress_claim: str | None
    last_progress_class: str | None
    last_progress_adjudication: dict[str, str] | None
    last_adjudication_review: str | None
    last_adjudication_model: str | None
    last_strategy_likelihood: int | None
    last_strategy_threshold: int | None
    last_strategy_worthwhile: bool | None
    last_strategy_decision: str | None
    last_strategy_plan_status: str | None
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
    active_strategy_pass: int | None
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
            "schema_version": 2,
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
            "last_progress_claim": None,
            "last_progress_adjudication": None,
            "last_adjudication_review": None,
            "last_adjudication_model": None,
            "last_progress_class": None,
            "last_strategy_likelihood": None,
            "last_strategy_threshold": None,
            "last_strategy_worthwhile": None,
            "last_strategy_decision": None,
            "last_strategy_plan_status": None,
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
        reflection_due = now >= self._parse_time(str(state["next_reflection_at"]))
        reflection_due = reflection_due or (
            int(state.get("consecutive_execution_failures", 0)) >= 2
        )
        reflection_due = (
            reflection_due or int(state.get("repeated_output_count", 0)) >= 2
        )
        reflection_due = reflection_due or self._strategy_requires_review(state)
        master_text = self.master_prompt.read_text(encoding="utf-8").strip()
        if not master_text:
            raise AutoRunError("Master Prompt is empty")
        master_digest = hashlib.sha256(master_text.encode("utf-8")).hexdigest()
        state["status"] = "running"
        state["next_retry_at"] = None
        state["heartbeat_at"] = utc_now()
        state["master_prompt_sha256"] = master_digest
        state["attempt_count"] = index
        state["active_round"] = index
        self._save(state)

        reflection_output = (
            self._run_strategy_reflection(index, state, master_text, round_dir)
            if reflection_due
            else None
        )
        if reflection_output is not None:
            state = self._state()
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
            claim = self._round_progress_class(output_path)
            digest = hashlib.sha256(output_path.read_bytes()).hexdigest()
            repeated = (
                int(latest.get("repeated_output_count", 0)) + 1
                if digest == latest.get("last_output_sha256")
                else 0
            )
            latest["last_output_sha256"] = digest
            latest["repeated_output_count"] = repeated
            latest["last_progress_claim"] = claim
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
                    "reason": adjudication.reason,
                    "verified_scope_delta": adjudication.verified_scope_delta,
                    "strategy_alignment": adjudication.strategy_alignment,
                    "milestone_result": adjudication.milestone_result,
                }
                latest["last_adjudication_review"] = str(adjudication_path)
                counter = f"{progress_class}_round_count"
                latest[counter] = int(latest.get(counter, 0)) + 1
                if progress_class == "blocked":
                    latest["mathematical_blocker_count"] = (
                        int(latest.get("mathematical_blocker_count", 0)) + 1
                    )
                self._apply_adjudication_to_strategy(latest, adjudication)
                latest["last_failure_class"] = (
                    "verification" if metric_failures else None
                )
                latest["last_error"] = (
                    f"{metric_failures} trusted progress metric(s) failed"
                    if metric_failures
                    else None
                )
            latest["status"] = "running"
            self._event(
                self._session(),
                "round_completed",
                (
                    f"attempt {index} execution completed; conductor claimed {claim}; "
                    f"adjudicated {progress_class}"
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
        required_change = bool(state.get("strategy_change_required", False))
        prior_review = ""
        validation_feedback = ""
        self._event(self._session(), "reflection_started", f"round {index}")
        self._emit(f"autorun round {index} strategy reflection starting")

        for pass_number in range(1, _STRATEGY_REVIEW_MAX_PASSES + 1):
            stem = (
                "strategy-reflection"
                if pass_number == 1
                else f"strategy-reflection-pass-{pass_number:02d}"
            )
            prompt_path = round_dir / f"{stem}-prompt.md"
            output_path = round_dir / f"{stem}.md"
            receipt_path = round_dir / f"{stem}-receipt.json"
            prompt = self._strategy_reflection_prompt(
                state,
                master_text,
                pass_number=pass_number,
                required_change=required_change,
                prior_review=prior_review,
                validation_feedback=validation_feedback,
            )
            atomic_write_text(prompt_path, prompt)
            request_path = round_dir / f"{stem}-request.json"
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
                    "stdout_log": str(round_dir / f"{stem}-stdout.log"),
                    "stderr_log": str(round_dir / f"{stem}-stderr.log"),
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
            active["active_strategy_pass"] = pass_number
            active["last_reflection_model"] = model
            self._save(active)
            self._event(
                self._session(),
                "reflection_pass_started",
                f"round {index}; pass {pass_number}",
            )
            exit_code = self._execute_with_heartbeat(request_path)
            if exit_code != 0 or not output_path.is_file():
                validation_feedback = (
                    f"Strategy pass {pass_number} failed to produce a retained review."
                )
                continue

            prior_review = output_path.read_text(encoding="utf-8").strip()
            assessment, errors = self._parse_strategy_assessment(
                prior_review,
                policy_threshold=self.project.autorun.worthwhile_likelihood_threshold,
                horizon_rounds=self.project.autorun.strategy_horizon_rounds,
            )
            decision_marker = self._marker_values_from_text(
                prior_review, {"STRATEGY_DECISION"}
            ).get("STRATEGY_DECISION")
            if decision_marker == "change_course":
                required_change = True
                pending = self._state()
                pending["strategy_change_required"] = True
                self._save(pending)
            if (
                assessment is not None
                and required_change
                and assessment.decision != "change_course"
            ):
                errors.append(
                    "A prior pass rejected the current course; later passes must "
                    "refine a replacement rather than reinstate it."
                )
            if (
                assessment is not None
                and assessment.decision == "change_course"
                and pass_number == 1
            ):
                errors.append(
                    "A course change requires a second Astra pass to challenge and "
                    "solidify the replacement plan."
                )
            if assessment is not None and not errors:
                approved = self._state()
                previous = approved.get("active_strategy")
                history = list(approved.get("strategy_history", []))
                if isinstance(previous, dict):
                    prior_contract = dict(previous)
                    prior_contract["status"] = "superseded"
                    history.append(prior_contract)
                approved["active_strategy"] = self._strategy_contract(
                    index, approved, assessment
                )
                approved["strategy_history"] = history[-20:]
                approved["active_strategy_pass"] = None
                approved["last_strategy_likelihood"] = assessment.likelihood
                approved["last_strategy_threshold"] = assessment.threshold
                approved["last_strategy_worthwhile"] = assessment.worthwhile
                approved["last_strategy_decision"] = assessment.decision
                approved["last_strategy_plan_status"] = assessment.plan_status
                approved["last_strategy_review"] = str(output_path)
                approved["last_strategy_round"] = index
                approved["strategy_change_required"] = False
                approved["reflection_count"] = int(approved["reflection_count"]) + 1
                approved["next_reflection_at"] = self._format_time(
                    datetime.now(UTC)
                    + timedelta(minutes=int(approved["reflection_minutes"]))
                )
                approved["last_failure_class"] = None
                self._save(approved)
                self._event(
                    self._session(),
                    "reflection_completed",
                    (
                        f"round {index}; decision {assessment.decision}; "
                        f"selected likelihood {assessment.replacement_likelihood}%"
                    ),
                )
                return output_path
            validation_feedback = " ".join(errors)

        failed = self._state()
        failed["active_strategy_pass"] = None
        failed["strategy_change_required"] = required_change
        self._save(failed)
        self._event(
            self._session(),
            "reflection_failed",
            f"round {index}; meaningful-progress gate has no approved plan",
        )
        raise StrategyGateError(
            "meaningful-progress gate did not produce an approved strategy after "
            f"{_STRATEGY_REVIEW_MAX_PASSES} Astra passes"
        )

    def _strategy_reflection_prompt(
        self,
        state: dict[str, Any],
        master_text: str,
        *,
        pass_number: int,
        required_change: bool,
        prior_review: str,
        validation_feedback: str,
    ) -> str:
        history = self._recent_progress_history(state)
        policy = self.project.autorun
        revision = ""
        if prior_review:
            revision = f"""
## Previous Astra review

{prior_review[-20000:]}

## Required revision

{validation_feedback or "Adversarially challenge and strengthen this plan."}
"""
        course_constraint = (
            "A previous pass or missed strategy deadline has rejected the current "
            "course. Keep `STRATEGY_DECISION: change_course` and develop a replacement."
            if required_change
            else "No earlier pass in this gate has mandated a course change."
        )
        active_strategy = json.dumps(
            state.get("active_strategy"), indent=2, sort_keys=True
        )
        return f"""# Autorun meaningful-progress gate — pass {pass_number}

You are the strategic governor, not an execution agent. Judge whether the current
course is likely to produce a meaningful result within the next
{policy.strategy_horizon_rounds} completed conductor rounds. Meaningful means
materially reducing distance to the living master contract, discharging a
load-bearing final obligation, or establishing a method that scales to the
remaining domain. Local lemmas, slightly better constants, passing builds, and
activity are only incremental unless they unlock that path.

The minimum worthwhile likelihood is project policy:
{policy.worthwhile_likelihood_threshold}%. You may not choose or relax it. Compare
at least two concrete candidate strategies, including the current course when it
remains viable. Estimate likelihood, rounds to first observable evidence, and
compute cost for the selected strategy. The replacement must beat a rejected
course and clear policy.

Produce an enforceable contract: a selected method, ordered milestones with
deadlines relative to acceptance, a falsifiable first check, kill criteria, and
one next action. Do not execute tasks, edit files, or claim unverified progress.
Write a detailed report before the markers explaining evidence, candidate
comparison, governing interfaces, resource bounds, risks, and fallback.

{course_constraint}

## Living Master Prompt

{master_text}

## Current active strategy contract

```json
{active_strategy}
```

## Retained state

- Session: `{self._session()}`
- Completed executions: {int(state.get("round_count", 0))}
- Meaningful rounds: {int(state.get("meaningful_round_count", 0))}
- Incremental rounds: {int(state.get("incremental_round_count", 0))}
- Previous output: `{state.get("last_output") or "None"}`
- Previous adjudication: `{state.get("last_adjudication_review") or "None"}`
- Previous error: `{state.get("last_error") or "None"}`

## Recent adjudicated trajectory

{history}
{revision}
## Required machine-readable decision

End with each marker on one line. Separate candidates and kill criteria with
`||`. Encode milestones as `round_offset::observable`, separated by semicolons.

MEANINGFUL_PROGRESS_LIKELIHOOD: integer from 0 to 100 for current course
MINIMUM_WORTHWHILE_LIKELIHOOD: {policy.worthwhile_likelihood_threshold}
CURRENT_COURSE_WORTHWHILE: yes | no
STRATEGY_DECISION: continue | change_course
STRATEGY_PLAN_STATUS: ready | revise
REPLACEMENT_MEANINGFUL_PROGRESS_LIKELIHOOD: integer from 0 to 100 for selected strategy
EXPECTED_ROUNDS_TO_FIRST_EVIDENCE: integer from 1 to {policy.strategy_horizon_rounds}
EXPECTED_COMPUTE_COST: low | medium | high
COURSE_TO_ABANDON: required for change_course; otherwise n/a
CANDIDATE_STRATEGIES: at least two distinct concrete candidates separated by ||
SELECTED_METHOD: the selected method and governing interface
STRATEGY_MILESTONES: e.g. 2::observable first check; 6::load-bearing result
FIRST_FALSIFIABLE_CHECK: exact observable check
STRATEGY_KILL_CRITERIA: concrete criteria separated by ||
REFLECTION_NEXT: one concrete action required by this contract
"""

    def _strategy_contract(
        self,
        attempt: int,
        state: dict[str, Any],
        assessment: _StrategyAssessment,
    ) -> dict[str, Any]:
        accepted_execution = int(state.get("round_count", 0))
        horizon = self.project.autorun.strategy_horizon_rounds
        markers = assessment.markers
        return {
            "schema_version": 1,
            "strategy_id": f"strategy-{int(state.get('reflection_count', 0)) + 1:05d}",
            "status": "active",
            "decision": assessment.decision,
            "accepted_attempt": attempt,
            "accepted_execution": accepted_execution,
            "horizon_rounds": horizon,
            "deadline_execution": accepted_execution + horizon,
            "first_evidence_deadline_execution": (
                accepted_execution + int(assessment.first_evidence_rounds or 1)
            ),
            "first_evidence_observed": False,
            "course_to_abandon": markers["COURSE_TO_ABANDON"],
            "selected_method": markers["SELECTED_METHOD"],
            "selected_likelihood": assessment.replacement_likelihood,
            "worthwhile_threshold": assessment.threshold,
            "expected_compute_cost": assessment.compute_cost,
            "candidate_strategies": list(assessment.alternatives),
            "milestones": [
                {
                    "index": milestone_index,
                    "deadline_execution": accepted_execution + offset,
                    "observable": observable,
                    "status": "pending",
                }
                for milestone_index, (offset, observable) in enumerate(
                    assessment.milestones, start=1
                )
            ],
            "first_falsifiable_check": markers["FIRST_FALSIFIABLE_CHECK"],
            "kill_criteria": [
                item.strip()
                for item in markers["STRATEGY_KILL_CRITERIA"].split("||")
                if item.strip()
            ],
            "next_action": markers["REFLECTION_NEXT"],
            "last_alignment": None,
            "last_milestone_result": None,
        }

    @staticmethod
    def _strategy_requires_review(state: dict[str, Any]) -> bool:
        if bool(state.get("strategy_change_required", False)):
            return True
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict):
            return True
        if strategy.get("status") != "active":
            return True
        completed = int(state.get("round_count", 0))
        if completed >= int(strategy.get("deadline_execution", completed)):
            return True
        if not bool(
            strategy.get("first_evidence_observed", False)
        ) and completed >= int(
            strategy.get("first_evidence_deadline_execution", completed)
        ):
            return True
        milestones = strategy.get("milestones")
        if isinstance(milestones, list):
            return any(
                isinstance(item, dict)
                and item.get("status") == "pending"
                and completed >= int(item.get("deadline_execution", completed))
                for item in milestones
            )
        return True

    def _recent_progress_history(self, state: dict[str, Any]) -> str:
        round_count = int(state.get("round_count", 0))
        last_review = state.get("last_strategy_round")
        prior = (
            int(last_review)
            if isinstance(last_review, int) and not isinstance(last_review, bool)
            else 0
        )
        start = max(1, prior + 1, round_count - 19)
        rows: list[str] = []
        for round_index in range(start, round_count + 1):
            path = self._session() / "rounds" / f"round-{round_index:05d}" / "output.md"
            markers = self._marker_values(path, {"AUTORUN_RESULT", "AUTORUN_SUMMARY"})
            if markers:
                rows.append(
                    f"- Round {round_index}: "
                    f"{markers.get('AUTORUN_RESULT', 'unclassified')} — "
                    f"{markers.get('AUTORUN_SUMMARY', 'No retained summary.')}"
                )
        return "\n".join(rows) if rows else "No retained round summaries."

    @staticmethod
    def _parse_strategy_assessment(
        text: str,
        *,
        policy_threshold: int = 30,
        horizon_rounds: int = 12,
    ) -> tuple[_StrategyAssessment | None, list[str]]:
        names = {
            "MEANINGFUL_PROGRESS_LIKELIHOOD",
            "MINIMUM_WORTHWHILE_LIKELIHOOD",
            "CURRENT_COURSE_WORTHWHILE",
            "STRATEGY_DECISION",
            "STRATEGY_PLAN_STATUS",
            "REPLACEMENT_MEANINGFUL_PROGRESS_LIKELIHOOD",
            "EXPECTED_ROUNDS_TO_FIRST_EVIDENCE",
            "EXPECTED_COMPUTE_COST",
            "COURSE_TO_ABANDON",
            "CANDIDATE_STRATEGIES",
            "SELECTED_METHOD",
            "STRATEGY_MILESTONES",
            "FIRST_FALSIFIABLE_CHECK",
            "STRATEGY_KILL_CRITERIA",
            "REFLECTION_NEXT",
        }
        markers = AutoRunRunner._marker_values_from_text(text, names)
        missing = sorted(names - markers.keys())
        errors = [f"Missing marker {name}." for name in missing]
        try:
            likelihood = int(markers["MEANINGFUL_PROGRESS_LIKELIHOOD"])
            threshold = int(markers["MINIMUM_WORTHWHILE_LIKELIHOOD"])
            replacement_likelihood = int(
                markers["REPLACEMENT_MEANINGFUL_PROGRESS_LIKELIHOOD"]
            )
            first_evidence_rounds = int(markers["EXPECTED_ROUNDS_TO_FIRST_EVIDENCE"])
        except (KeyError, ValueError):
            return None, [
                *errors,
                "Likelihood and first-evidence markers must be integers.",
            ]
        if not 0 <= likelihood <= 100:
            errors.append("Meaningful-progress likelihood must be from 0 to 100.")
        if threshold != policy_threshold:
            errors.append(
                "MINIMUM_WORTHWHILE_LIKELIHOOD must equal the project policy "
                f"threshold of {policy_threshold}."
            )
        if not 0 <= replacement_likelihood <= 100:
            errors.append("Replacement likelihood must be from 0 to 100.")
        if replacement_likelihood < policy_threshold:
            errors.append("Selected strategy is below the policy threshold.")
        if not 1 <= first_evidence_rounds <= horizon_rounds:
            errors.append(
                f"First evidence must be due within 1 to {horizon_rounds} rounds."
            )
        worthwhile_text = markers.get("CURRENT_COURSE_WORTHWHILE")
        if worthwhile_text not in {"yes", "no"}:
            errors.append("CURRENT_COURSE_WORTHWHILE must be yes or no.")
        worthwhile = worthwhile_text == "yes"
        decision = markers.get("STRATEGY_DECISION", "")
        if decision not in {"continue", "change_course"}:
            errors.append("STRATEGY_DECISION must be continue or change_course.")
        plan_status = markers.get("STRATEGY_PLAN_STATUS", "")
        if plan_status not in {"ready", "revise"}:
            errors.append("STRATEGY_PLAN_STATUS must be ready or revise.")
        compute_cost = markers.get("EXPECTED_COMPUTE_COST")
        if compute_cost not in {"low", "medium", "high"}:
            errors.append("EXPECTED_COMPUTE_COST must be low, medium, or high.")
        if worthwhile != (likelihood >= policy_threshold):
            errors.append("Worthwhile judgment must match the policy-owned threshold.")
        if decision != ("continue" if worthwhile else "change_course"):
            errors.append("Strategy decision must match the worthwhile judgment.")
        if plan_status != "ready":
            errors.append("The strategy plan is not ready.")
        if decision == "change_course" and replacement_likelihood <= likelihood:
            errors.append(
                "A replacement must have a higher likelihood than the rejected course."
            )
        if decision == "change_course" and markers.get("COURSE_TO_ABANDON") in {
            None,
            "",
            "n/a",
        }:
            errors.append("A course change must name the course being abandoned.")
        for name in (
            "SELECTED_METHOD",
            "FIRST_FALSIFIABLE_CHECK",
            "STRATEGY_KILL_CRITERIA",
            "REFLECTION_NEXT",
        ):
            if markers.get(name) in {None, "", "n/a"}:
                errors.append(f"An enforceable strategy requires {name}.")
        alternatives = tuple(
            item.strip()
            for item in markers.get("CANDIDATE_STRATEGIES", "").split("||")
            if item.strip()
        )
        if len(alternatives) < 2 or len(set(alternatives)) != len(alternatives):
            errors.append(
                "CANDIDATE_STRATEGIES must contain at least two distinct candidates "
                "separated by `||`."
            )
        milestones: list[tuple[int, str]] = []
        for raw_milestone in markers.get("STRATEGY_MILESTONES", "").split(";"):
            raw_milestone = raw_milestone.strip()
            if not raw_milestone:
                continue
            try:
                offset_text, observable = raw_milestone.split("::", 1)
                offset = int(offset_text.strip())
            except ValueError:
                errors.append(
                    "Each milestone must use `round_offset::observable` syntax."
                )
                continue
            observable = observable.strip()
            if not observable or not 1 <= offset <= horizon_rounds:
                errors.append(
                    f"Milestone offsets must be within 1 to {horizon_rounds} "
                    "and observables must be nonempty."
                )
            milestones.append((offset, observable))
        offsets = [offset for offset, _ in milestones]
        if not milestones or offsets != sorted(set(offsets)):
            errors.append("Milestone offsets must be present, unique, and increasing.")
        elif offsets[0] > first_evidence_rounds:
            errors.append(
                "The first milestone must be due no later than first evidence."
            )
        return (
            _StrategyAssessment(
                likelihood=likelihood,
                threshold=threshold,
                worthwhile=worthwhile,
                decision=decision,
                plan_status=plan_status,
                replacement_likelihood=replacement_likelihood,
                first_evidence_rounds=first_evidence_rounds,
                compute_cost=compute_cost,
                alternatives=alternatives,
                milestones=tuple(milestones),
                markers=markers,
            ),
            errors,
        )

    @staticmethod
    def _marker_values(path: Path, names: set[str]) -> dict[str, str]:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            return {}
        return AutoRunRunner._marker_values_from_text(text, names)

    @staticmethod
    def _marker_values_from_text(text: str, names: set[str]) -> dict[str, str]:
        markers: dict[str, str] = {}
        for line in text.splitlines():
            for name in names:
                prefix = f"{name}:"
                if line.startswith(prefix):
                    markers[name] = line.removeprefix(prefix).strip()
        return markers

    @staticmethod
    def _round_progress_class(output_path: Path) -> str:
        markers = AutoRunRunner._marker_values(output_path, {"AUTORUN_RESULT"})
        value = markers.get("AUTORUN_RESULT", "unclassified")
        return value if value in _PROGRESS_CLASSES else "unclassified"

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
        active_strategy = json.dumps(
            state.get("active_strategy"), indent=2, sort_keys=True
        )
        reflection = ""
        if reflection_output is not None:
            reflection_text = reflection_output.read_text(encoding="utf-8").strip()
            reflection = f"""

## Meaningful-progress strategy gate

Source: `{reflection_output}`

{reflection_text}

This is the authoritative strategy decision, not verified mathematical evidence.
Check its repository claims. If it says `change_course`, abandon the rejected
course and execute the replacement plan's first falsifiable check; do not spend
this round making another incremental improvement to the rejected approach.
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
- Consecutive execution failures: {int(state.get("consecutive_execution_failures", 0))}
- Completed executions: {int(state.get("round_count", 0))}

## Enforceable active strategy

```json
{active_strategy}
```

Your task must implement this contract's next action or current pending milestone.
Do not silently drift. If evidence falsifies a kill criterion, report it instead
of substituting a nearby task.
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
10. Keep every command inside the inherited resource-control cgroup. Never use
    `systemd-run`, `nohup`, `disown`, `setsid`, or detached/background processes.
11. Classify the result as `meaningful` only if it materially advances the final
    contract or validates a scalable method. Local lemmas, tighter constants, and
    adjacent tiny cells are `incremental` even when fully verified.
12. Before returning, save all useful work and state exactly what was verified and
    what the next conductor round should attempt.

End with these machine-readable lines. `AUTORUN_RESULT` is your claim and will be
independently adjudicated:

AUTORUN_RESULT: incremental | meaningful | blocked | complete
AUTORUN_SUMMARY: one factual sentence
AUTORUN_NEXT: one concrete next action
STRATEGY_ID: exact active strategy ID
STRATEGY_MILESTONE: integer milestone index | n/a
MILESTONE_RESULT: advanced | unchanged | falsified | complete
EVIDENCE: retained artifact or verified observable supporting the milestone result

"""

    def _conductor_model(self, state: dict[str, Any]) -> tuple[str | None, str]:
        primary_model = self.options.model or self.project.planner_model
        targeted_model = self.project.targeted_task_model
        failures = int(state.get("consecutive_execution_failures", 0))
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
        elif version != 2:
            raise AutoRunError(f"unsupported autorun state schema: {version!r}")
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
        allowed_status = {"running", "recovering", "paused", "stopped"}
        if value["status"] not in allowed_status:
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
        }
        for name in count_fields:
            item = value.get(name)
            if isinstance(item, bool) or not isinstance(item, int) or item < 0:
                raise AutoRunError(f"autorun state field {name} must be nonnegative")
        if int(value["attempt_count"]) < int(value["round_count"]):
            raise AutoRunError("autorun attempt count precedes completed executions")
        strategy = value.get("active_strategy")
        if strategy is not None:
            if not isinstance(strategy, dict):
                raise AutoRunError("active strategy contract must be a table")
            required_strategy = {
                "strategy_id",
                "status",
                "deadline_execution",
                "first_evidence_deadline_execution",
                "milestones",
                "kill_criteria",
            }
            if required_strategy - strategy.keys():
                raise AutoRunError("active strategy contract is incomplete")
            if strategy["status"] not in {
                "active",
                "drifted",
                "falsified",
                "complete",
                "superseded",
            }:
                raise AutoRunError("active strategy contract has an invalid status")
            for name in ("deadline_execution", "first_evidence_deadline_execution"):
                item = strategy[name]
                if isinstance(item, bool) or not isinstance(item, int) or item < 0:
                    raise AutoRunError(
                        f"active strategy field {name} must be nonnegative"
                    )
            if not isinstance(strategy["milestones"], list) or not isinstance(
                strategy["kill_criteria"], list
            ):
                raise AutoRunError(
                    "active strategy milestones and kill criteria must be arrays"
                )
        history = value.get("strategy_history")
        if not isinstance(history, list):
            raise AutoRunError("strategy history must be an array")
        return value

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
        model = (
            self.project.analysis_model
            or self.options.reflection_model
            or self.project.strategy_reflection_model
            or self.options.model
            or self.project.planner_model
        )
        conductor_text = conductor_output.read_text(encoding="utf-8").strip()
        prompt = f"""# Independent autorun progress adjudication

You are a read-only adjudicator, independent of the conductor that performed the
work. Inspect the repository, retained artifacts, active strategy, and trusted
project metrics. Do not edit files. The conductor's `AUTORUN_RESULT` is a claim,
not evidence. Classify only verified observable progress toward the living master
contract. Local lemmas, tighter constants, passing builds, and activity are
incremental unless they discharge a load-bearing obligation or validate a method
that scales to the remaining domain.

## Living Master Prompt

{self.master_prompt.read_text(encoding="utf-8").strip()}

## Active strategy contract

```json
{json.dumps(current.get("active_strategy"), indent=2, sort_keys=True)}
```

## Trusted project progress metrics

```json
{json.dumps(metrics, indent=2, sort_keys=True)}
```

## Conductor report

Source: `{conductor_output}`

{conductor_text[-30000:]}

End with these exact markers:

ADJUDICATED_PROGRESS: incremental | meaningful | blocked | complete
STRATEGY_ALIGNMENT: aligned | drifted | falsified | complete | n/a
MILESTONE_RESULT: advanced | unchanged | falsified | complete | n/a
MILESTONE_INDEX: integer | n/a
ADJUDICATION_REASON: one evidence-based sentence
VERIFIED_SCOPE_DELTA: exact verified change in final-contract coverage
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
            return None, output_path, model
        return (
            self._parse_progress_adjudication(output_path.read_text(encoding="utf-8")),
            output_path,
            model,
        )

    @staticmethod
    def _parse_progress_adjudication(text: str) -> _ProgressAdjudication | None:
        names = {
            "ADJUDICATED_PROGRESS",
            "STRATEGY_ALIGNMENT",
            "MILESTONE_RESULT",
            "MILESTONE_INDEX",
            "ADJUDICATION_REASON",
            "VERIFIED_SCOPE_DELTA",
        }
        markers = AutoRunRunner._marker_values_from_text(text, names)
        if names - markers.keys():
            return None
        progress = markers["ADJUDICATED_PROGRESS"]
        alignment = markers["STRATEGY_ALIGNMENT"]
        milestone_result = markers["MILESTONE_RESULT"]
        if progress not in {"incremental", "meaningful", "blocked", "complete"}:
            return None
        if alignment not in {"aligned", "drifted", "falsified", "complete", "n/a"}:
            return None
        if milestone_result not in {
            "advanced",
            "unchanged",
            "falsified",
            "complete",
            "n/a",
        }:
            return None
        raw_index = markers["MILESTONE_INDEX"]
        try:
            milestone_index = None if raw_index == "n/a" else int(raw_index)
        except ValueError:
            return None
        if milestone_index is not None and milestone_index < 1:
            return None
        if not markers["ADJUDICATION_REASON"] or not markers["VERIFIED_SCOPE_DELTA"]:
            return None
        return _ProgressAdjudication(
            progress_class=progress,
            strategy_alignment=alignment,
            milestone_result=milestone_result,
            milestone_index=milestone_index,
            reason=markers["ADJUDICATION_REASON"],
            verified_scope_delta=markers["VERIFIED_SCOPE_DELTA"],
        )

    @staticmethod
    def _apply_adjudication_to_strategy(
        state: dict[str, Any], adjudication: _ProgressAdjudication
    ) -> None:
        strategy = state.get("active_strategy")
        if not isinstance(strategy, dict):
            return
        strategy = dict(strategy)
        strategy["last_alignment"] = adjudication.strategy_alignment
        strategy["last_milestone_result"] = adjudication.milestone_result
        if adjudication.strategy_alignment in {"drifted", "falsified"}:
            strategy["status"] = adjudication.strategy_alignment
            state["strategy_change_required"] = True
            state["next_reflection_at"] = utc_now()
        elif adjudication.strategy_alignment == "complete":
            strategy["status"] = "complete"
        if adjudication.milestone_result in {"advanced", "complete"}:
            strategy["first_evidence_observed"] = True
        milestones = strategy.get("milestones")
        if (
            adjudication.milestone_index is not None
            and isinstance(milestones, list)
            and adjudication.milestone_index <= len(milestones)
        ):
            milestone = milestones[adjudication.milestone_index - 1]
            if isinstance(milestone, dict):
                milestone["status"] = adjudication.milestone_result
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
    strategy_pass: object = None,
) -> dict[str, Any]:
    if not isinstance(active_round, int) or isinstance(active_round, bool):
        return {}
    if active_route == "strategy_reflection":
        suffix = (
            f"-pass-{strategy_pass:02d}"
            if isinstance(strategy_pass, int)
            and not isinstance(strategy_pass, bool)
            and strategy_pass > 1
            else ""
        )
        name = f"strategy-reflection{suffix}-receipt.json"
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


def _compact_strategy_field(value: str, *, limit: int = 150) -> str:
    normalized = " ".join(value.split())
    if len(normalized) <= limit:
        return normalized
    prefix = normalized[: limit - 1].rsplit(" ", 1)[0]
    return f"{prefix or normalized[: limit - 1]}…"


def _strategy_report_sections(state: dict[str, Any]) -> list[str]:
    value = state.get("last_strategy_review")
    if state.get("last_strategy_decision") != "change_course" or not isinstance(
        value, str
    ):
        return []
    markers = AutoRunRunner._marker_values(
        Path(value),
        {
            "ABANDON_CURRENT_COURSE",
            "ALTERNATIVE_METHOD",
            "STRATEGY_MILESTONES",
            "FIRST_FALSIFIABLE_CHECK",
            "STRATEGY_KILL_CRITERIA",
            "REFLECTION_NEXT",
        },
    )
    required = (
        "ABANDON_CURRENT_COURSE",
        "ALTERNATIVE_METHOD",
        "STRATEGY_MILESTONES",
        "FIRST_FALSIFIABLE_CHECK",
        "STRATEGY_KILL_CRITERIA",
        "REFLECTION_NEXT",
    )
    if any(markers.get(name) in {None, "", "n/a"} for name in required):
        return []
    return [
        "ASTRA STRATEGY REPORT",
        (
            "Astra changed course after estimating meaningful-progress likelihood "
            f"at {state.get('last_strategy_likelihood')}% against a "
            f"{state.get('last_strategy_threshold')}% worthwhile threshold. "
            f"Plan status: {state.get('last_strategy_plan_status', 'unknown')}. "
            "Classified executions since gate activation: "
            f"{state.get('meaningful_round_count', 0)} meaningful, "
            f"{state.get('incremental_round_count', 0)} incremental, "
            f"{state.get('blocked_round_count', 0)} blocked, "
            f"{state.get('complete_round_count', 0)} complete."
        ),
        "REJECTED COURSE",
        _compact_strategy_field(markers["ABANDON_CURRENT_COURSE"]),
        "REPLACEMENT METHOD",
        _compact_strategy_field(markers["ALTERNATIVE_METHOD"]),
        "STRATEGY MILESTONES",
        _compact_strategy_field(markers["STRATEGY_MILESTONES"]),
        "FIRST FALSIFIABLE CHECK",
        _compact_strategy_field(markers["FIRST_FALSIFIABLE_CHECK"]),
        "KILL CRITERIA",
        _compact_strategy_field(markers["STRATEGY_KILL_CRITERIA"]),
        "STRATEGY NEXT ACTION",
        _compact_strategy_field(markers["REFLECTION_NEXT"]),
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
            f"{state.get('round_count', 0)} completed executions, "
            f"{state.get('attempt_count', 0)} attempts, "
            f"{state.get('consecutive_execution_failures', 0)} consecutive "
            f"execution failures, {state.get('controller_failure_count', 0)} "
            f"controller failures, {state.get('verification_failure_count', 0)} "
            f"verification failures, and {state.get('reflection_count', 0)} "
            "meaningful-progress reviews."
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
    strategy_report = _strategy_report_sections(state)
    decision = state.get("last_strategy_decision")
    if strategy_report:
        sections.extend(strategy_report)
    elif isinstance(decision, str):
        sections.extend(
            [
                "MEANINGFUL-PROGRESS GATE",
                (
                    f"Latest decision: {decision}; estimated likelihood "
                    f"{state.get('last_strategy_likelihood')}% against a "
                    f"{state.get('last_strategy_threshold')}% worthwhile threshold. "
                    f"Plan status: {state.get('last_strategy_plan_status', 'unknown')}."
                ),
                (
                    "Classified executions since gate activation: "
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
        sections.extend(
            [
                "VERIFIED BASELINE",
                evidence[0],
            ]
        )
    markers = _last_round_markers(state)
    if markers:
        sections.append("LATEST COMPLETED EXECUTION")
        sections.append(
            "Progress classification: "
            f"{markers.get('AUTORUN_RESULT', 'unclassified')}. "
            f"{markers.get('AUTORUN_SUMMARY', 'No retained summary.')}"
        )
        next_action = markers.get("AUTORUN_NEXT")
        if next_action:
            sections.extend(["NEXT CONDUCTOR ACTION", next_action])
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
                session,
                active_round,
                state.get("active_model_route"),
                state.get("active_strategy_pass"),
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
    session: Path,
    active_round: object,
    route: object,
    strategy_pass: object = None,
) -> Path | None:
    if not isinstance(active_round, int) or isinstance(active_round, bool):
        return None
    if route == "strategy_reflection":
        suffix = (
            f"-pass-{strategy_pass:02d}"
            if isinstance(strategy_pass, int)
            and not isinstance(strategy_pass, bool)
            and strategy_pass > 1
            else ""
        )
        name = f"strategy-reflection{suffix}-stdout.log"
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
            receipt = _round_receipt(
                session, active_round, route, state.get("active_strategy_pass")
            )
            path = _round_stdout_path(
                session, active_round, route, state.get("active_strategy_pass")
            )
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
            receipt = _round_receipt(
                session, active_round, route, state.get("active_strategy_pass")
            )
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
