"""Bounded, evidence-driven optimization across successive regime campaigns."""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
import time
from dataclasses import asdict, dataclass
from datetime import UTC, datetime, timedelta
from pathlib import Path
from typing import Any, Literal, Self, TextIO

from .agent_runner import execute as execute_agent_request
from .artifacts import (
    atomic_write_json,
    atomic_write_text,
    utc_now,
    verify_evidence_index,
)
from .command import run_captured_command
from .config import ConfigurationError
from .journal import JournalError, append_state_snapshot, load_state_snapshot
from .models import CampaignOutcome
from .project import AutonomySuccessSpec, ProjectSpec
from .regime import RegimeError, RegimeOptions, RegimeRunner, choose_strategy
from .runtime import CampaignRunError, campaign_run_lock, campaign_state


class AutonomyError(RuntimeError):
    """An autonomous session violated its retained contract or safety policy."""


@dataclass(frozen=True, slots=True)
class AutonomyRuntimeOptions:
    """Runtime-only overrides for one autonomous session."""

    profile: str | None = None
    approval_timeout_minutes: int | None = None
    afk_autonomy: bool | None = None
    max_campaigns: int | None = None
    omp: str | None = None
    herdr: str = "herdr"
    lake: str = "lake"
    focus: bool = True
    close_herdr: bool = True
    output: TextIO | None = None
    waive_missing_sources: bool = False
    decision_poll_seconds: float = 1.0


@dataclass(frozen=True, slots=True)
class InterCampaignAnalysis:
    """Strict output of the read-only optimizer between two campaigns."""

    summary: str
    progress: tuple[str, ...]
    failed_approaches: tuple[str, ...]
    remaining_obligations: tuple[str, ...]
    evidence_gaps: tuple[str, ...]
    compute_assessment: tuple[str, ...]
    action: Literal["continue", "checkpoint"]
    recommended_strategy: str
    rationale: str
    campaign_directive: str
    contract_preserved: bool

    @classmethod
    def parse(cls, value: object) -> Self:
        if not isinstance(value, dict):
            raise ConfigurationError("inter-campaign analysis must be an object")
        required = {
            "schema_version",
            "summary",
            "progress",
            "failed_approaches",
            "remaining_obligations",
            "evidence_gaps",
            "compute_assessment",
            "action",
            "recommended_strategy",
            "rationale",
            "campaign_directive",
            "contract_preserved",
        }
        if set(value) != required:
            raise ConfigurationError(
                "inter-campaign analysis keys differ; "
                f"missing={sorted(required - value.keys())}, "
                f"extra={sorted(value.keys() - required)}"
            )
        if value["schema_version"] != 1:
            raise ConfigurationError("inter-campaign analysis schema_version must be 1")

        def text(name: str) -> str:
            item = value[name]
            if not isinstance(item, str) or not item.strip():
                raise ConfigurationError(
                    f"inter-campaign analysis {name} must be nonempty text"
                )
            return item.strip()

        def texts(name: str) -> tuple[str, ...]:
            item = value[name]
            if not isinstance(item, list) or not all(
                isinstance(entry, str) and entry.strip() for entry in item
            ):
                raise ConfigurationError(
                    f"inter-campaign analysis {name} must be a text array"
                )
            return tuple(entry.strip() for entry in item)

        action = value["action"]
        if action not in ("continue", "checkpoint"):
            raise ConfigurationError("inter-campaign analysis action is invalid")
        contract_preserved = value["contract_preserved"]
        if not isinstance(contract_preserved, bool):
            raise ConfigurationError(
                "inter-campaign analysis contract_preserved must be boolean"
            )
        if not contract_preserved:
            raise ConfigurationError(
                "inter-campaign optimizer attempted to change the success contract"
            )
        return cls(
            summary=text("summary"),
            progress=texts("progress"),
            failed_approaches=texts("failed_approaches"),
            remaining_obligations=texts("remaining_obligations"),
            evidence_gaps=texts("evidence_gaps"),
            compute_assessment=texts("compute_assessment"),
            action=action,
            recommended_strategy=text("recommended_strategy"),
            rationale=text("rationale"),
            campaign_directive=text("campaign_directive"),
            contract_preserved=contract_preserved,
        )


@dataclass(frozen=True, slots=True)
class SuccessValidation:
    passed: bool
    summary: str
    receipt: Path


class AutonomyRunner:
    """Run, assess, and adapt bounded campaigns until the strict contract passes."""

    def __init__(
        self, project: ProjectSpec, options: AutonomyRuntimeOptions | None = None
    ) -> None:
        self.base_project = project
        self.options = options or AutonomyRuntimeOptions()
        autonomy = project.autonomy
        if not autonomy.enabled:
            raise AutonomyError("autonomy is disabled in the project settings")
        if autonomy.success is None:
            raise AutonomyError("enabled autonomy has no success contract")
        profile = self.options.profile or autonomy.compute_profile
        self.project = project.with_compute_profile(profile)
        self.profile = profile
        self.output = self.options.output or sys.stdout
        timeout = self.options.approval_timeout_minutes
        self.approval_timeout_minutes = (
            autonomy.approval_timeout_minutes if timeout is None else timeout
        )
        if not 0 <= self.approval_timeout_minutes <= 1440:
            raise ValueError("approval timeout must be between 0 and 1440 minutes")
        self.afk_autonomy = (
            autonomy.afk_autonomy
            if self.options.afk_autonomy is None
            else self.options.afk_autonomy
        )
        self.max_campaigns = (
            autonomy.max_campaigns
            if self.options.max_campaigns is None
            else self.options.max_campaigns
        )
        if not 1 <= self.max_campaigns <= 1000:
            raise ValueError("max campaigns must be between 1 and 1000")
        if self.options.decision_poll_seconds <= 0:
            raise ValueError("decision poll interval must be positive")
        self.session_dir: Path | None = None

    def run(self) -> Path:
        """Create and drive one new retained autonomous session."""

        self.session_dir = self._initialize_session()
        return self._drive()

    def resume(self, session_dir: Path) -> Path:
        """Resume one interrupted or operator-unblocked autonomous session."""

        self.session_dir = session_dir.expanduser().resolve()
        state = self._state()
        if state.get("project_manifest") != str(self.base_project.manifest_path):
            raise AutonomyError("autonomous session belongs to a different project")
        self._verify_contract(state)
        status = state.get("status")
        if status in {"solved", "stopped", "budget_exhausted"}:
            return self.session_dir
        if status == "checkpoint":
            current = state.get("current_round")
            rounds = state.get("rounds")
            if (
                not isinstance(current, int)
                or not isinstance(rounds, list)
                or not 1 <= current <= len(rounds)
            ):
                raise AutonomyError("checkpoint has no resumable campaign round")
            active = rounds[current - 1]
            if not isinstance(active, dict):
                raise AutonomyError("checkpoint campaign round is malformed")
            checkpoint_kind = state.get("checkpoint_kind")
            if checkpoint_kind == "optimizer":
                active["status"] = "analysis_retry"
                state["status"] = "analysis_retry"
            elif checkpoint_kind in {"campaign_gate", "failure_limit", "sources"}:
                active["status"] = "running"
                state["status"] = "campaign_running"
            else:
                raise AutonomyError(
                    f"autonomous checkpoint kind is invalid: {checkpoint_kind!r}"
                )
            active["completed_at"] = None
            state["checkpoint_kind"] = None
            state["error"] = None
            self._save_state(state, f"autonomy:round-{current}:checkpoint-resumed")
        return self._drive()

    def _initialize_session(self) -> Path:
        root = self.project.root / "autonomy-runs"
        root.mkdir(parents=True, exist_ok=True)
        session_id = (
            datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + f"-{os.urandom(3).hex()}"
        )
        session = root / session_id
        session.mkdir()
        (session / "controller").mkdir()
        contract = self._contract_snapshot(self.base_project)
        state: dict[str, Any] = {
            "schema_version": 1,
            "session_id": session_id,
            "project_manifest": str(self.base_project.manifest_path),
            "contract": contract,
            "settings": {
                "profile": self.profile,
                "approval_timeout_minutes": self.approval_timeout_minutes,
                "afk_autonomy": self.afk_autonomy,
                "max_campaigns": self.max_campaigns,
                "max_elapsed_minutes": (self.base_project.autonomy.max_elapsed_minutes),
                "max_consecutive_failures": (
                    self.base_project.autonomy.max_consecutive_failures
                ),
                "analysis_agent_seconds": (
                    self.base_project.autonomy.analysis_agent_seconds
                ),
            },
            "status": "ready",
            "checkpoint_kind": None,
            "created_at": utc_now(),
            "updated_at": utc_now(),
            "completed_at": None,
            "current_round": None,
            "rounds": [],
            "input_lineage": {},
            "next_directive": None,
            "pending_operator_decision": None,
            "consecutive_failures": 0,
            "result": None,
            "error": None,
        }
        append_state_snapshot(session, state, reason="autonomy:initialized")
        atomic_write_json(session / "state.json", state)
        return session

    def _drive(self) -> Path:
        assert self.session_dir is not None
        controller = self.session_dir / "controller"
        try:
            with campaign_run_lock(controller):
                return self._drive_locked()
        except CampaignRunError as exc:
            raise AutonomyError(f"cannot acquire autonomous controller: {exc}") from exc

    def _drive_locked(self) -> Path:
        assert self.session_dir is not None
        while True:
            state = self._state()
            self._verify_contract(state)
            status = state.get("status")
            if status in {"solved", "stopped", "budget_exhausted", "checkpoint"}:
                return self.session_dir
            if status == "awaiting_approval":
                choice, source = self._await_decision(state)
                self._apply_decision(choice, source)
                continue
            if status == "analysis_retry":
                self._retry_analysis(state)
                continue
            if status not in {"ready", "campaign_running"}:
                raise AutonomyError(f"autonomous session status is invalid: {status!r}")
            self._execute_or_resume_round(state)

    def _execute_or_resume_round(self, state: dict[str, Any]) -> None:
        assert self.session_dir is not None
        rounds = state.get("rounds")
        if not isinstance(rounds, list):
            raise AutonomyError("autonomous rounds state is malformed")
        active = (
            rounds[-1] if rounds and rounds[-1].get("status") == "running" else None
        )
        if active is None:
            created_at = state.get("created_at")
            if not isinstance(created_at, str):
                raise AutonomyError("autonomous creation time is malformed")
            try:
                created = datetime.fromisoformat(created_at)
            except ValueError as exc:
                raise AutonomyError("autonomous creation time is malformed") from exc
            elapsed_limit = int(state["settings"]["max_elapsed_minutes"])
            if datetime.now(UTC) >= created + timedelta(minutes=elapsed_limit):
                state["status"] = "budget_exhausted"
                state["completed_at"] = utc_now()
                state["error"] = "maximum autonomous wall time reached without proof"
                self._save_state(state, "autonomy:time-budget-exhausted")
                return
            if len(rounds) >= self.max_campaigns:
                state["status"] = "budget_exhausted"
                state["completed_at"] = utc_now()
                state["error"] = "maximum campaign count reached without proof"
                self._save_state(state, "autonomy:budget-exhausted")
                return
            index = len(rounds) + 1
            active = {
                "index": index,
                "status": "running",
                "campaign_run": None,
                "campaign_outcome": None,
                "campaign_error": None,
                "analysis": None,
                "analysis_error": None,
                "decision": None,
                "success_validation": None,
                "started_at": utc_now(),
                "completed_at": None,
            }
            rounds.append(active)
            state["current_round"] = index
            state["status"] = "campaign_running"
            state["updated_at"] = utc_now()
            self._save_state(state, f"autonomy:round-{index}:started")

        index = int(active["index"])
        run_value = active.get("campaign_run")
        campaign_run = Path(run_value) if isinstance(run_value, str) else None
        runner = self._regime_runner(state)
        try:
            if campaign_run is None or not self._regime_run_resumable(campaign_run):
                campaign_run = runner.run()
            else:
                campaign_run = runner.resume(campaign_run)
            active["campaign_run"] = str(campaign_run)
            active["campaign_error"] = None
        except (OSError, ValueError, RegimeError, CampaignRunError) as exc:
            if runner.run_dir is not None:
                campaign_run = runner.run_dir
                active["campaign_run"] = str(campaign_run)
            active["campaign_error"] = f"{type(exc).__name__}: {exc}"
            state["consecutive_failures"] = int(state["consecutive_failures"]) + 1
            if int(state["consecutive_failures"]) >= int(
                state["settings"]["max_consecutive_failures"]
            ):
                active["status"] = "failed"
                active["completed_at"] = utc_now()
                state["status"] = "checkpoint"
                state["checkpoint_kind"] = "failure_limit"
                state["error"] = active["campaign_error"]
                self._save_state(state, f"autonomy:round-{index}:failure-limit")
                return
            self._save_state(state, f"autonomy:round-{index}:campaign-failed")
            self._prepare_analysis(
                state,
                active,
                campaign_run,
                outcome=None,
                validation=None,
                synthetic_strategy="recover-campaign-failure",
            )
            return

        if not (campaign_run / "state.json").is_file():
            active["status"] = "checkpoint"
            state["status"] = "checkpoint"
            state["checkpoint_kind"] = "sources"
            state["error"] = "campaign requires critical source input"
            self._save_state(state, f"autonomy:round-{index}:sources")
            return

        campaign_value = campaign_state(campaign_run)
        outcome_path = campaign_run / "outcome.json"
        if not outcome_path.is_file():
            campaign_status = campaign_value.get("status")
            if campaign_status in {"awaiting_approval", "awaiting_sources"}:
                active["status"] = "checkpoint"
                state["status"] = "checkpoint"
                state["checkpoint_kind"] = "campaign_gate"
                state["error"] = f"campaign stopped at {campaign_status}"
                self._save_state(state, f"autonomy:round-{index}:campaign-gate")
                return
            raise AutonomyError("campaign returned without a retained outcome")

        try:
            outcome_value = json.loads(outcome_path.read_text(encoding="utf-8"))
            outcome = CampaignOutcome.parse(outcome_value)
        except (OSError, json.JSONDecodeError, ConfigurationError) as exc:
            raise AutonomyError(f"cannot read campaign outcome: {exc}") from exc
        active["campaign_outcome"] = outcome.status
        state["input_lineage"] = self._capture_lineage(state, campaign_run)
        state["consecutive_failures"] = 0

        validation: SuccessValidation | None = None
        if outcome.status == "solved":
            validation = self._validate_success(campaign_run, index)
            active["success_validation"] = str(validation.receipt)
            if validation.passed:
                active["status"] = "solved"
                active["completed_at"] = utc_now()
                state["status"] = "solved"
                state["completed_at"] = utc_now()
                state["result"] = {
                    "campaign_run": str(campaign_run),
                    "success_validation": str(validation.receipt),
                    "summary": validation.summary,
                }
                state["error"] = None
                self._save_state(state, f"autonomy:round-{index}:solved")
                return
            synthetic = "repair-success-validation"
        else:
            synthetic = None
        self._save_state(state, f"autonomy:round-{index}:assessed")
        self._prepare_analysis(
            state,
            active,
            campaign_run,
            outcome=outcome,
            validation=validation,
            synthetic_strategy=synthetic,
        )

    def _retry_analysis(self, state: dict[str, Any]) -> None:
        rounds = state.get("rounds")
        current = state.get("current_round")
        if (
            not isinstance(rounds, list)
            or not isinstance(current, int)
            or not 1 <= current <= len(rounds)
        ):
            raise AutonomyError("analysis retry has no active campaign round")
        active = rounds[current - 1]
        if not isinstance(active, dict):
            raise AutonomyError("analysis retry campaign round is malformed")
        run_value = active.get("campaign_run")
        campaign_run = Path(run_value) if isinstance(run_value, str) else None
        outcome: CampaignOutcome | None = None
        validation: SuccessValidation | None = None
        if active.get("campaign_outcome") is not None:
            if campaign_run is None:
                raise AutonomyError("analysis retry has no retained campaign")
            outcome_path = campaign_run / "outcome.json"
            try:
                outcome = CampaignOutcome.parse(
                    json.loads(outcome_path.read_text(encoding="utf-8"))
                )
            except (OSError, json.JSONDecodeError, ConfigurationError) as exc:
                raise AutonomyError(
                    f"cannot reload campaign outcome for analysis retry: {exc}"
                ) from exc
        if outcome is not None and outcome.status == "solved":
            receipt_value = active.get("success_validation")
            if not isinstance(receipt_value, str):
                raise AutonomyError("analysis retry has no success-validation receipt")
            receipt = Path(receipt_value)
            try:
                value = json.loads(receipt.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise AutonomyError(
                    f"cannot reload success validation for analysis retry: {exc}"
                ) from exc
            failures = value.get("failures") if isinstance(value, dict) else None
            passed = value.get("passed") if isinstance(value, dict) else None
            if (
                not isinstance(passed, bool)
                or not isinstance(failures, list)
                or not all(isinstance(item, str) for item in failures)
            ):
                raise AutonomyError("success-validation receipt is malformed")
            summary = (
                "kernel-checked success contract passed"
                if passed
                else "; ".join(failures)
            )
            validation = SuccessValidation(passed, summary, receipt)
        synthetic = (
            "recover-campaign-failure"
            if outcome is None
            else (
                "repair-success-validation"
                if validation is not None and not validation.passed
                else None
            )
        )
        self._prepare_analysis(
            state,
            active,
            campaign_run,
            outcome=outcome,
            validation=validation,
            synthetic_strategy=synthetic,
        )

    @staticmethod
    def _regime_run_resumable(campaign_run: Path) -> bool:
        pre_state = campaign_run / "pre-campaign" / "state.json"
        try:
            value = json.loads(pre_state.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return False
        return (
            isinstance(value, dict)
            and value.get("schema_version") == 1
            and value.get("status")
            in {
                "research_gate",
                "research",
                "planning",
                "awaiting_sources",
                "executing",
            }
        )

    def _regime_runner(self, state: dict[str, Any]) -> RegimeRunner:
        directive_value = state.get("next_directive")
        directive = Path(directive_value) if isinstance(directive_value, str) else None
        lineage = state.get("input_lineage")
        if not isinstance(lineage, dict):
            raise AutonomyError("autonomous input lineage is malformed")
        overrides = tuple(
            (target, Path(source))
            for target, source in sorted(lineage.items())
            if isinstance(target, str) and isinstance(source, str)
        )
        return RegimeRunner(
            self.project,
            RegimeOptions(
                missing_source_policy="checkpoint",
                omp=self.options.omp,
                herdr=self.options.herdr,
                lake=self.options.lake,
                focus=self.options.focus,
                close_herdr=self.options.close_herdr,
                output=self.output,
                waive_missing_sources=self.options.waive_missing_sources,
                campaign_directive=directive,
                input_overrides=overrides,
            ),
        )

    def _capture_lineage(
        self, state: dict[str, Any], campaign_run: Path
    ) -> dict[str, str]:
        prior = state.get("input_lineage")
        result = dict(prior) if isinstance(prior, dict) else {}
        workspace = campaign_run / "workspace"
        for item in self.project.inputs:
            candidate = workspace / item.target
            if candidate.exists() and not candidate.is_symlink():
                result[item.target] = str(candidate.resolve())
        return result

    def _validate_success(self, campaign_run: Path, index: int) -> SuccessValidation:
        assert self.session_dir is not None
        success = self.base_project.autonomy.success
        assert success is not None
        receipt_dir = self._round_dir(index) / "success-validation"
        receipt_dir.mkdir(parents=True, exist_ok=True)
        failures: list[str] = []
        commands: list[dict[str, object]] = []
        try:
            verify_evidence_index(campaign_run)
        except (OSError, TypeError, ValueError) as exc:
            failures.append(f"campaign evidence verification failed: {exc}")
        workspace = campaign_run / "workspace"
        cwd = workspace / success.workspace
        if not cwd.is_dir() or cwd.is_symlink():
            failures.append(f"success workspace is not a regular directory: {cwd}")
        for relative in success.required_artifacts:
            artifact = cwd / relative
            if not artifact.is_file() or artifact.is_symlink():
                failures.append(f"required proof artifact is missing: {relative}")
        axiom_check = receipt_dir / "theorem-contract.lean"
        modules = tuple(dict.fromkeys(item.module for item in success.theorems))
        contract_lines = [*(f"import {module}" for module in modules), ""]
        for theorem in success.theorems:
            contract_lines.extend(
                (
                    f"#check {theorem.declaration}",
                    f"example : {theorem.theorem_type} := {theorem.declaration}",
                    f"#print axioms {theorem.declaration}",
                    "",
                )
            )
        atomic_write_text(axiom_check, "\n".join(contract_lines))
        command_specs = [
            ("build", success.build_command),
            (
                "axioms",
                (self.options.lake, "env", "lean", str(axiom_check)),
            ),
            *(
                (f"verify-{number:02d}", command)
                for number, command in enumerate(success.verification_commands, start=1)
            ),
        ]
        if cwd.is_dir() and not cwd.is_symlink():
            for command_id, configured_argv in command_specs:
                argv = (
                    (self.options.lake, *configured_argv[1:])
                    if configured_argv[0] == "lake"
                    else configured_argv
                )
                result = run_captured_command(
                    argv,
                    cwd=cwd,
                    env=os.environ.copy(),
                    timeout=float(self.base_project.autonomy.analysis_agent_seconds),
                    execution=self.project.execution,
                    workspace=workspace,
                    run_dir=self.session_dir,
                    read_paths=(campaign_run, receipt_dir),
                )
                stdout_path = receipt_dir / f"{command_id}.stdout.log"
                stderr_path = receipt_dir / f"{command_id}.stderr.log"
                atomic_write_text(stdout_path, result.stdout)
                atomic_write_text(stderr_path, result.stderr)
                commands.append(
                    {
                        "id": command_id,
                        "argv": list(argv),
                        "exit_code": result.exit_code,
                        "error": result.error,
                        "stdout": str(stdout_path),
                        "stderr": str(stderr_path),
                        "stdout_sha256": result.stdout_sha256,
                        "stderr_sha256": result.stderr_sha256,
                        "sandbox": dict(result.sandbox),
                    }
                )
                if result.exit_code != 0 or result.error is not None:
                    failures.append(
                        f"success command {command_id} failed: "
                        f"exit={result.exit_code}, error={result.error}"
                    )
                if command_id == "axioms" and result.exit_code == 0:
                    failures.extend(self._validate_axiom_output(result.stdout, success))
        receipt = receipt_dir / "receipt.json"
        value = {
            "schema_version": 1,
            "campaign_run": str(campaign_run),
            "contract_sha256": self._contract_snapshot(self.base_project)[
                "success_sha256"
            ],
            "passed": not failures,
            "failures": failures,
            "commands": commands,
            "completed_at": utc_now(),
        }
        atomic_write_json(receipt, value)
        summary = (
            "kernel-checked success contract passed"
            if not failures
            else "; ".join(failures)
        )
        return SuccessValidation(not failures, summary, receipt)

    @staticmethod
    def _validate_axiom_output(output: str, success: AutonomySuccessSpec) -> list[str]:
        reports = 0
        observed: set[str] = set()
        for line in output.splitlines():
            if "does not depend on any axioms" in line:
                reports += 1
                continue
            match = re.search(r"depends on axioms:\s*\[([^]]*)\]", line)
            if match is None:
                continue
            reports += 1
            observed.update(
                item.strip() for item in match.group(1).split(",") if item.strip()
            )
        failures: list[str] = []
        expected_reports = len(success.theorems)
        if reports != expected_reports:
            failures.append(
                "axiom audit report count differs: "
                f"expected={expected_reports}, observed={reports}"
            )
        unknown = observed - set(success.allowed_axioms)
        if unknown:
            failures.append(f"axiom audit found disallowed axioms: {sorted(unknown)}")
        return failures

    def _prepare_analysis(
        self,
        state: dict[str, Any],
        active: dict[str, Any],
        campaign_run: Path | None,
        *,
        outcome: CampaignOutcome | None,
        validation: SuccessValidation | None,
        synthetic_strategy: str | None,
    ) -> None:
        index = int(active["index"])
        offered = (
            [item.strategy_id for item in outcome.strategies]
            if outcome is not None
            else []
        )
        if synthetic_strategy is not None:
            offered = [synthetic_strategy]
        analysis: InterCampaignAnalysis | None = None
        analysis_errors: list[str] = []
        analysis_root = self._round_dir(index) / "analysis"
        retained_attempts = [
            int(path.name.removeprefix("attempt-"))
            for path in analysis_root.glob("attempt-*")
            if path.is_dir() and path.name.removeprefix("attempt-").isdigit()
        ]
        first_attempt = max(retained_attempts, default=0) + 1
        successful_attempt: int | None = None
        for attempt in range(first_attempt, first_attempt + 2):
            try:
                analysis = self._run_analysis(
                    index,
                    campaign_run,
                    outcome,
                    validation,
                    tuple(offered),
                    active.get("campaign_error"),
                    attempt=attempt,
                )
                successful_attempt = attempt
                break
            except AutonomyError as exc:
                analysis_errors.append(f"attempt {attempt}: {exc}")
                if attempt == first_attempt:
                    self._emit("inter-campaign optimizer failed; retrying once")
        if analysis is None:
            detail = "; ".join(analysis_errors)
            active["analysis_error"] = detail
            active["status"] = "checkpoint"
            active["completed_at"] = utc_now()
            state["status"] = "checkpoint"
            state["checkpoint_kind"] = "optimizer"
            state["error"] = detail
            self._save_state(state, f"autonomy:round-{index}:optimizer-failed")
            return
        assert successful_attempt is not None
        active["analysis_error"] = None
        analysis_path = (
            analysis_root / f"attempt-{successful_attempt:03d}" / "analysis.json"
        )
        active["analysis"] = str(analysis_path)
        if analysis.action == "checkpoint":
            active["status"] = "checkpoint"
            active["completed_at"] = utc_now()
            state["status"] = "checkpoint"
            state["checkpoint_kind"] = "optimizer"
            state["error"] = analysis.rationale
            self._save_state(state, f"autonomy:round-{index}:optimizer-checkpoint")
            return
        if analysis.recommended_strategy not in offered:
            raise AutonomyError(
                "inter-campaign optimizer recommended an unavailable strategy: "
                f"{analysis.recommended_strategy!r}; available={offered}"
            )
        request_dir = self._round_dir(index) / "decision"
        request_dir.mkdir(parents=True, exist_ok=True)
        deadline = None
        if self.afk_autonomy:
            deadline = (
                (datetime.now(UTC) + timedelta(minutes=self.approval_timeout_minutes))
                .isoformat(timespec="seconds")
                .replace("+00:00", "Z")
            )
        request = {
            "schema_version": 1,
            "session": str(self.session_dir),
            "round": index,
            "campaign_run": str(campaign_run) if campaign_run is not None else None,
            "allowed_strategies": [*offered, "stop"],
            "recommended_strategy": analysis.recommended_strategy,
            "rationale": analysis.rationale,
            "approval_timeout_minutes": self.approval_timeout_minutes,
            "afk_autonomy": self.afk_autonomy,
            "deadline_at": deadline,
            "decision_command": (
                "agentic-lean-math-assistant autonomy-decide --session "
                f"{self.session_dir} --strategy <id|recommended|stop>"
            ),
        }
        request_path = request_dir / "request.json"
        atomic_write_json(request_path, request)
        active["status"] = "awaiting_approval"
        state["status"] = "awaiting_approval"
        state["checkpoint_kind"] = None
        state["error"] = None
        state["pending_operator_decision"] = None
        state["updated_at"] = utc_now()
        self._save_state(state, f"autonomy:round-{index}:awaiting-approval")
        self._emit(
            f"round {index} analysis complete: {analysis.summary}\n"
            f"recommended strategy: {analysis.recommended_strategy}\n"
            f"decision: {request['decision_command']}"
        )
        if self.afk_autonomy:
            self._emit(
                f"AFK fallback will continue after {self.approval_timeout_minutes} "
                "minutes without a decision."
            )
        else:
            self._emit("AFK fallback is disabled; waiting for an explicit decision.")

    def _run_analysis(
        self,
        index: int,
        campaign_run: Path | None,
        outcome: CampaignOutcome | None,
        validation: SuccessValidation | None,
        offered: tuple[str, ...],
        campaign_error: object,
        *,
        attempt: int,
    ) -> InterCampaignAnalysis:
        assert self.session_dir is not None
        success = self.base_project.autonomy.success
        assert success is not None
        analysis_dir = self._round_dir(index) / "analysis" / f"attempt-{attempt:03d}"
        workspace = analysis_dir / "workspace"
        workspace.mkdir(parents=True, exist_ok=False)
        prompt_path = analysis_dir / "prompt.md"
        output_path = analysis_dir / "output.json"
        receipt_path = analysis_dir / "receipt.json"
        template = (
            Path(__file__).with_name("prompts") / "inter_campaign_optimizer.md"
        ).read_text(encoding="utf-8")
        assignment = {
            "immutable_problem": str(self.base_project.problem_path),
            "success_contract": asdict(success),
            "autonomy_session": str(self.session_dir),
            "current_campaign": str(campaign_run) if campaign_run else None,
            "campaign_outcome": asdict(outcome) if outcome else None,
            "campaign_error": campaign_error,
            "success_validation": (
                {
                    "passed": validation.passed,
                    "summary": validation.summary,
                    "receipt": str(validation.receipt),
                }
                if validation is not None
                else None
            ),
            "available_strategies": list(offered),
            "project_knowledge": str(self.base_project.knowledge_dir),
            "round": index,
            "optimizer_attempt": attempt,
            "max_campaigns": self.max_campaigns,
        }
        prompt = (
            template.rstrip()
            + "\n\n## Retained assignment\n\n```json\n"
            + json.dumps(assignment, indent=2, ensure_ascii=False, default=str)
            + "\n```\n"
        )
        atomic_write_text(prompt_path, prompt)
        request_path = analysis_dir / "request.json"
        read_paths = [self.session_dir, self.base_project.problem_path]
        if campaign_run is not None:
            read_paths.append(campaign_run)
        if self.base_project.knowledge_dir.exists():
            read_paths.append(self.base_project.knowledge_dir)
        atomic_write_json(
            request_path,
            {
                "role_id": "inter_campaign_optimizer",
                "attempt": attempt,
                "omp": self.options.omp or self.project.omp,
                "workspace": str(workspace),
                "run_dir": str(self.session_dir),
                "prompt": str(prompt_path),
                "output": str(output_path),
                "stdout_log": str(analysis_dir / "stdout.log"),
                "stderr_log": str(analysis_dir / "stderr.log"),
                "receipt": str(receipt_path),
                "tools": ["read", "grep", "glob"],
                "model": self.project.planner_model,
                "thinking": self.project.planner_thinking,
                "max_time": self.base_project.autonomy.analysis_agent_seconds,
                "empty_output_retries": 1,
                "execution": self.project.execution.to_dict(),
                "sandbox_read_paths": [str(path.resolve()) for path in read_paths],
            },
        )
        exit_code = execute_agent_request(request_path)
        if exit_code != 0 or not output_path.is_file():
            raise AutonomyError(f"inter-campaign optimizer failed; see {analysis_dir}")
        try:
            value = json.loads(output_path.read_text(encoding="utf-8"))
            analysis = InterCampaignAnalysis.parse(value)
        except (OSError, json.JSONDecodeError, ConfigurationError) as exc:
            raise AutonomyError(f"inter-campaign analysis is invalid: {exc}") from exc
        atomic_write_json(analysis_dir / "analysis.json", value)
        return analysis

    def _await_decision(self, state: dict[str, Any]) -> tuple[str, str]:
        assert self.session_dir is not None
        current = state.get("current_round")
        if not isinstance(current, int):
            raise AutonomyError("awaiting approval has no current round")
        request_path = self._round_dir(current) / "decision" / "request.json"
        try:
            request = json.loads(request_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise AutonomyError(f"cannot read decision request: {exc}") from exc
        recommended = request.get("recommended_strategy")
        if not isinstance(recommended, str):
            raise AutonomyError("decision request has no recommended strategy")
        timed = self.afk_autonomy
        deadline: datetime | None = None
        if timed:
            deadline_value = request.get("deadline_at")
            if not isinstance(deadline_value, str):
                raise AutonomyError("timed decision request has no deadline")
            try:
                deadline = datetime.fromisoformat(deadline_value)
            except ValueError as exc:
                raise AutonomyError("decision request deadline is malformed") from exc
            if deadline.tzinfo is None:
                raise AutonomyError("decision request deadline has no timezone")
        while True:
            latest = self._state()
            pending = latest.get("pending_operator_decision")
            if isinstance(pending, dict):
                strategy = pending.get("strategy")
                if isinstance(strategy, str):
                    return strategy, "operator"
            if deadline is not None and datetime.now(UTC) >= deadline:
                return recommended, "afk-timeout"
            remaining = (
                max(0.0, (deadline - datetime.now(UTC)).total_seconds())
                if deadline is not None
                else self.options.decision_poll_seconds
            )
            time.sleep(min(self.options.decision_poll_seconds, remaining))

    def _apply_decision(self, strategy: str, source: str) -> None:
        assert self.session_dir is not None
        state = self._state()
        current = state.get("current_round")
        rounds = state.get("rounds")
        if not isinstance(current, int) or not isinstance(rounds, list):
            raise AutonomyError("decision state is malformed")
        active = rounds[current - 1]
        request_path = self._round_dir(current) / "decision" / "request.json"
        request = json.loads(request_path.read_text(encoding="utf-8"))
        allowed = request.get("allowed_strategies")
        if not isinstance(allowed, list) or strategy not in allowed:
            raise AutonomyError(f"strategy {strategy!r} is not allowed")
        if strategy == "stop":
            active["decision"] = {
                "strategy": strategy,
                "source": source,
                "at": utc_now(),
            }
            active["status"] = "stopped"
            active["completed_at"] = utc_now()
            state["status"] = "stopped"
            state["completed_at"] = utc_now()
            state["pending_operator_decision"] = None
            state["error"] = "operator or policy selected stop"
            self._save_state(state, f"autonomy:round-{current}:stopped")
            return
        analysis_path = Path(str(active["analysis"]))
        analysis = InterCampaignAnalysis.parse(
            json.loads(analysis_path.read_text(encoding="utf-8"))
        )
        campaign_run_value = active.get("campaign_run")
        campaign_run = (
            Path(campaign_run_value) if isinstance(campaign_run_value, str) else None
        )
        selected_context = ""
        if campaign_run is not None and (campaign_run / "outcome.json").is_file():
            outcome = CampaignOutcome.parse(
                json.loads((campaign_run / "outcome.json").read_text(encoding="utf-8"))
            )
            selected = next(
                (item for item in outcome.strategies if item.strategy_id == strategy),
                None,
            )
            if selected is not None:
                choose_strategy(campaign_run, strategy)
                selected_context = (
                    f"## Selected campaign strategy\n\n"
                    f"**{selected.title}**\n\n{selected.rationale}\n\n"
                    f"{selected.next_prompt.rstrip()}\n\n"
                )
        directive_path = self._round_dir(current) / "next-campaign.md"
        contract_hash = state["contract"]["problem_sha256"]
        atomic_write_text(
            directive_path,
            "# Inter-campaign directive\n\n"
            f"Immutable problem contract SHA-256: `{contract_hash}`. Do not change or "
            "weaken the requested theorem, evidence rules, or success checks.\n\n"
            + selected_context
            + "## Optimizer analysis\n\n"
            + analysis.rationale.rstrip()
            + "\n\n## Required next campaign\n\n"
            + analysis.campaign_directive.rstrip()
            + "\n",
        )
        active["decision"] = {"strategy": strategy, "source": source, "at": utc_now()}
        active["status"] = "complete"
        active["completed_at"] = utc_now()
        state["status"] = "ready"
        state["next_directive"] = str(directive_path)
        state["pending_operator_decision"] = None
        state["current_round"] = None
        state["updated_at"] = utc_now()
        self._save_state(state, f"autonomy:round-{current}:decision:{strategy}")
        self._emit(f"continuing with strategy {strategy} ({source})")

    def _contract_snapshot(self, project: ProjectSpec) -> dict[str, str]:
        success = project.autonomy.success
        if success is None:
            raise AutonomyError("project has no autonomous success contract")
        try:
            problem_bytes = project.problem_path.read_bytes()
        except OSError as exc:
            raise AutonomyError(
                f"cannot read immutable problem contract: {exc}"
            ) from exc
        encoded_success = json.dumps(
            asdict(success), sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
        return {
            "problem_sha256": hashlib.sha256(problem_bytes).hexdigest(),
            "success_sha256": hashlib.sha256(encoded_success).hexdigest(),
        }

    def _verify_contract(self, state: dict[str, Any]) -> None:
        try:
            current = ProjectSpec.load(self.base_project.manifest_path)
        except ConfigurationError as exc:
            raise AutonomyError(f"cannot reload project contract: {exc}") from exc
        observed = self._contract_snapshot(current)
        if state.get("contract") != observed:
            raise AutonomyError(
                "immutable problem or success contract changed during autonomy session"
            )

    def _round_dir(self, index: int) -> Path:
        assert self.session_dir is not None
        path = self.session_dir / "rounds" / f"round-{index:03d}"
        path.mkdir(parents=True, exist_ok=True)
        return path

    def _state(self) -> dict[str, Any]:
        assert self.session_dir is not None
        try:
            state = load_state_snapshot(self.session_dir).state
        except JournalError as exc:
            raise AutonomyError(f"cannot read autonomous session state: {exc}") from exc
        if state.get("schema_version") != 1:
            raise AutonomyError("autonomous session state is malformed")
        return state

    def _save_state(self, state: dict[str, Any], reason: str) -> None:
        assert self.session_dir is not None
        state["updated_at"] = utc_now()
        try:
            with campaign_run_lock(self.session_dir):
                append_state_snapshot(self.session_dir, state, reason=reason)
                atomic_write_json(self.session_dir / "state.json", state)
        except CampaignRunError as exc:
            raise AutonomyError(f"cannot lock autonomous session state: {exc}") from exc

    def _emit(self, text: str) -> None:
        print(text, file=self.output, flush=True)


def record_autonomy_decision(session_dir: Path, strategy: str) -> str:
    """Durably submit an operator decision to a waiting autonomous controller."""

    session = session_dir.expanduser().resolve()
    selected = strategy.strip()
    if not selected:
        raise AutonomyError("autonomy decision must not be empty")
    try:
        with campaign_run_lock(session):
            state = load_state_snapshot(session).state
            if state.get("status") != "awaiting_approval":
                raise AutonomyError(
                    "autonomy decision requires an awaiting_approval session"
                )
            current = state.get("current_round")
            if not isinstance(current, int):
                raise AutonomyError("autonomy decision has no current round")
            request_path = (
                session
                / "rounds"
                / f"round-{current:03d}"
                / "decision"
                / "request.json"
            )
            try:
                request = json.loads(request_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise AutonomyError(
                    f"cannot read autonomy decision request: {exc}"
                ) from exc
            if selected == "recommended":
                recommended = request.get("recommended_strategy")
                if not isinstance(recommended, str):
                    raise AutonomyError("decision request has no recommended strategy")
                selected = recommended
            allowed = request.get("allowed_strategies")
            if not isinstance(allowed, list) or selected not in allowed:
                raise AutonomyError(
                    f"strategy {selected!r} is not allowed; choose from {allowed}"
                )
            pending = state.get("pending_operator_decision")
            if isinstance(pending, dict):
                retained = pending.get("strategy")
                if retained != selected:
                    raise AutonomyError(
                        f"operator decision {retained!r} is already retained"
                    )
                return f"retained autonomy decision: {selected}"
            decision = {"strategy": selected, "submitted_at": utc_now()}
            decision_path = request_path.with_name("operator-decision.json")
            atomic_write_json(decision_path, decision)
            state["pending_operator_decision"] = decision
            state["updated_at"] = utc_now()
            append_state_snapshot(
                session, state, reason=f"autonomy:operator-decision:{selected}"
            )
            atomic_write_json(session / "state.json", state)
    except (CampaignRunError, JournalError) as exc:
        raise AutonomyError(f"cannot retain autonomy decision: {exc}") from exc
    return f"retained autonomy decision: {selected}"


def autonomy_status(session_dir: Path) -> dict[str, Any]:
    """Return the verified authoritative state of one autonomous session."""

    session = session_dir.expanduser().resolve()
    try:
        return load_state_snapshot(session).state
    except JournalError as exc:
        raise AutonomyError(f"cannot read autonomous session state: {exc}") from exc
