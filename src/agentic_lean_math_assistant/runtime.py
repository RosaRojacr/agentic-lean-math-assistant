"""Resumable stage-DAG runtime for unified Research and Build campaigns."""

from __future__ import annotations

import errno
import fcntl
import filecmp
import fnmatch
import json
import os
import secrets
import shutil
import signal
import stat
import sys
import tempfile
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path, PurePosixPath
from typing import Any, TextIO

from .artifacts import (
    Artifact,
    atomic_write_json,
    digest_file,
    digest_tree,
    utc_now,
    verify_evidence_for_repair,
    verify_evidence_index,
)
from .command import run_captured_command
from .config import CampaignInput, CampaignSpec, ConfigurationError, StageSpec
from .features import (
    FeatureContext,
    FeatureRegistry,
    FeatureResult,
    snapshot_workspace_inputs,
)
from .handoff import digest_handoff
from .herdr import HerdrClient, HerdrError, HerdrWorkspace
from .journal import (
    JournalError,
    append_state_snapshot,
    journal_path,
    load_state_snapshot,
)
from .processes import (
    clear_workspace_creation,
    register_campaign,
    register_workspace,
    register_workspace_creation,
    registered_workspace_intents,
    registered_workspaces,
    terminate_run_processes,
    unregister_campaign,
)
from .sandbox import prepare_sandbox

_REPLAY_SECURITY_FIELDS = (
    "enabled",
    "backend",
    "network",
    "memory_max_mb",
    "cpu_quota_percent",
    "tasks_max",
    "file_size_max_mb",
    "workspace_max_mb",
    "runtime_max_seconds",
    "workspace_executables",
    "environment",
    "toolchain",
    "allowed_executable_paths",
    "writable_paths",
)

_CHECKPOINT_IGNORED_NAMES = (
    ".cache",
    ".elan",
    ".lake",
    ".mypy_cache",
    ".pytest_cache",
    ".ruff_cache",
    "__pycache__",
)


class CampaignRunError(RuntimeError):
    """The unified runtime or a required stage failed."""


@contextmanager
def campaign_run_lock(run_dir: Path) -> Iterator[None]:
    """Hold the exclusive controller lock for one retained campaign run."""

    lock_path = run_dir.expanduser().resolve() / ".campaign.lock"
    flags = os.O_CREAT | os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW
    try:
        descriptor = os.open(lock_path, flags, 0o600)
    except OSError as exc:
        raise CampaignRunError(f"cannot open campaign run lock: {exc}") from exc
    locked = False
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise CampaignRunError("campaign run lock is not a regular file")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            locked = True
        except OSError as exc:
            if exc.errno in (errno.EACCES, errno.EAGAIN):
                raise CampaignRunError(
                    "another controller holds the campaign run lock"
                ) from exc
            raise CampaignRunError(f"cannot acquire campaign run lock: {exc}") from exc
        yield
    finally:
        if locked:
            try:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            finally:
                os.close(descriptor)
        else:
            os.close(descriptor)


def _retained_state_error(detail: str) -> CampaignRunError:
    return CampaignRunError(f"retained state is malformed: {detail}")


def _validate_retained_artifact(value: object) -> bool:
    if not isinstance(value, str) or not value:
        return False
    relative = value.removeprefix("workspace:")
    if not relative:
        return False
    pure = PurePosixPath(relative)
    return not pure.is_absolute() and all(
        part not in ("", ".", "..") for part in pure.parts
    )


def _validate_retained_state(value: object, campaign: CampaignSpec) -> dict[str, Any]:
    if (
        not isinstance(value, dict)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != 1
    ):
        raise CampaignRunError("retained state has an unsupported schema")
    if value.get("campaign_id") != campaign.campaign_id:
        raise CampaignRunError("retained state belongs to a different campaign")

    string_fields = ("run_id", "campaign_manifest", "campaign_resolved", "created_at")
    for field in string_fields:
        if not isinstance(value.get(field), str) or not value[field]:
            raise _retained_state_error(f"{field} must be a nonempty string")
    status = value.get("status")
    if not isinstance(status, str) or status not in {
        "running",
        "awaiting_approval",
        "complete",
        "incomplete",
        "failed",
        "stopped",
        "awaiting_sources",
        "awaiting_strategy",
        "replan_required",
        "restart_required",
    }:
        raise _retained_state_error("status is invalid")
    completed_at = value.get("completed_at")
    if completed_at is not None and not isinstance(completed_at, str):
        raise _retained_state_error("completed_at must be a string or null")
    controller_pid = value.get("controller_pid")
    if type(controller_pid) is not int or controller_pid <= 0:
        raise _retained_state_error("controller_pid must be a positive integer")
    herdr_workspace_id = value.get("herdr_workspace_id")
    if herdr_workspace_id is not None and not isinstance(herdr_workspace_id, str):
        raise _retained_state_error("herdr_workspace_id must be a string or null")
    if not isinstance(value.get("herdr_closed"), bool):
        raise _retained_state_error("herdr_closed must be a boolean")
    herdr_creation_label = value.get("herdr_creation_label")
    if herdr_creation_label is not None and not isinstance(herdr_creation_label, str):
        raise _retained_state_error("herdr_creation_label must be a string or null")
    revisions = value.get("revisions")
    if type(revisions) is not int or revisions < 0:
        raise _retained_state_error("revisions must be a nonnegative integer")
    error = value.get("error")
    if error is not None and not isinstance(error, str):
        raise _retained_state_error("error must be a string or null")
    pending_output_cleanup = value.get("pending_output_cleanup", [])
    if not isinstance(pending_output_cleanup, list) or not all(
        isinstance(stage_id, str)
        and stage_id in campaign.by_id
        and campaign.by_id[stage_id].feature == "artifact_promote"
        for stage_id in pending_output_cleanup
    ):
        raise _retained_state_error(
            "pending_output_cleanup must contain artifact promotion stage IDs"
        )
    if len(pending_output_cleanup) != len(set(pending_output_cleanup)):
        raise _retained_state_error("pending_output_cleanup stage IDs must be unique")

    stages = value.get("stages")
    expected_stage_ids = set(campaign.by_id)
    if not isinstance(stages, dict) or set(stages) != expected_stage_ids:
        raise _retained_state_error("stage IDs do not match the campaign")
    stage_statuses = {"pending", "running", "succeeded", "failed", "skipped"}
    for stage_id, stage_state in stages.items():
        if not isinstance(stage_state, dict):
            raise _retained_state_error(f"stage {stage_id!r} must be an object")
        required_stage_fields = {
            "status",
            "attempts",
            "artifacts",
            "summary",
            "completed_at",
        }
        optional_stage_fields = {"feedback", "interruptions"}
        if not required_stage_fields <= stage_state.keys() or (
            stage_state.keys() - required_stage_fields - optional_stage_fields
        ):
            raise _retained_state_error(f"stage {stage_id!r} has an invalid structure")
        stage_status = stage_state.get("status")
        if not isinstance(stage_status, str) or stage_status not in stage_statuses:
            raise _retained_state_error(f"stage {stage_id!r} status is invalid")
        attempts = stage_state.get("attempts")
        if type(attempts) is not int or attempts < 0:
            raise _retained_state_error(
                f"stage {stage_id!r} attempts must be a nonnegative integer"
            )
        artifacts = stage_state.get("artifacts")
        if not isinstance(artifacts, list) or not all(
            _validate_retained_artifact(artifact) for artifact in artifacts
        ):
            raise _retained_state_error(
                f"stage {stage_id!r} artifacts must be safe retained paths"
            )
        if len(artifacts) != len(set(artifacts)):
            raise _retained_state_error(f"stage {stage_id!r} artifacts must be unique")
        summary = stage_state.get("summary")
        if summary is not None and not isinstance(summary, str):
            raise _retained_state_error(
                f"stage {stage_id!r} summary must be a string or null"
            )
        stage_completed_at = stage_state.get("completed_at")
        if stage_completed_at is not None and not isinstance(stage_completed_at, str):
            raise _retained_state_error(
                f"stage {stage_id!r} completed_at must be a string or null"
            )
        if "feedback" in stage_state:
            feedback = stage_state["feedback"]
            if not isinstance(feedback, list) or not all(
                isinstance(item, str) for item in feedback
            ):
                raise _retained_state_error(
                    f"stage {stage_id!r} feedback must be a list of strings"
                )
        interruptions = stage_state.get("interruptions", 0)
        if type(interruptions) is not int or interruptions < 0:
            raise _retained_state_error(
                f"stage {stage_id!r} interruptions must be a nonnegative integer"
            )
        if stage_status == "running" and attempts == 0:
            raise _retained_state_error(
                f"stage {stage_id!r} cannot run before its first attempt"
            )

    events = value.get("events")
    if not isinstance(events, list):
        raise _retained_state_error("events must be a list")
    for event in events:
        if (
            not isinstance(event, dict)
            or set(event) != {"at", "stage", "status", "summary"}
            or not all(
                isinstance(event.get(field), str)
                for field in ("at", "stage", "status", "summary")
            )
            or event["stage"]
            not in expected_stage_ids
            | {"run"}
            | ({"handoff"} if campaign.handoff is not None else set())
        ):
            raise _retained_state_error("events must contain valid event objects")

    handoff = value.get("handoff")
    configured_handoff = campaign.handoff
    if handoff is not None:
        if configured_handoff is None or not isinstance(handoff, dict):
            raise _retained_state_error("handoff is inconsistent with the campaign")
        if set(handoff) != {
            "producer",
            "path",
            "schema",
            "sha256",
            "approved",
            "approved_at",
        }:
            raise _retained_state_error("handoff has an invalid structure")
        if (
            handoff.get("producer") != configured_handoff.producer
            or handoff.get("path") != configured_handoff.artifact
            or handoff.get("schema") != configured_handoff.schema
        ):
            raise _retained_state_error("handoff does not match the campaign")
        digest = handoff.get("sha256")
        if (
            not isinstance(digest, str)
            or len(digest) != 64
            or any(character not in "0123456789abcdef" for character in digest)
        ):
            raise _retained_state_error("handoff sha256 is invalid")
        if not isinstance(handoff.get("approved"), bool):
            raise _retained_state_error("handoff approved must be a boolean")
        approved_at = handoff.get("approved_at")
        if approved_at is not None and not isinstance(approved_at, str):
            raise _retained_state_error("handoff approved_at must be a string or null")
        if handoff["approved"] != (approved_at is not None):
            raise _retained_state_error("handoff approved and approved_at must agree")
    return value


@dataclass(frozen=True, slots=True)
class CampaignOptions:
    herdr: str = "herdr"
    omp: str = "omp"
    lake: str = "lake"
    runs_dir: Path | None = None
    focus: bool = True
    close_herdr: bool = True
    output: TextIO | None = None
    retry_failed: bool = False
    retry_stages: tuple[str, ...] = ()
    retry_feedback: tuple[str, ...] = ()
    max_parallel: int | None = None


class CampaignBuilder:
    """Execute one strict campaign without problem-specific controller logic."""

    def __init__(
        self,
        campaign: CampaignSpec,
        *,
        options: CampaignOptions | None = None,
        registry: FeatureRegistry | None = None,
        herdr_client: HerdrClient | None = None,
        python_executable: str | None = None,
        run_dir: Path | None = None,
    ) -> None:
        self.campaign = campaign
        self.options = options or CampaignOptions()
        self.registry = registry or FeatureRegistry()
        self.configs = self.registry.validate(campaign)
        self.herdr = herdr_client or HerdrClient(self.options.herdr)
        self.python_executable = python_executable or sys.executable
        self.run_dir = run_dir.resolve() if run_dir is not None else None
        self.workspace: Path | None = None
        self.state: dict[str, Any] = {}
        self._terminal_recovered = False
        self.herdr_workspace: HerdrWorkspace | None = None
        self.panes: dict[str, str] = {}
        self.output = self.options.output or sys.stdout

    def run(self) -> Path:
        if self.run_dir is None:
            self._select_new_run()
        else:
            self.run_dir.mkdir(parents=True, exist_ok=True)
            if (self.run_dir / "configuration").exists():
                raise CampaignRunError("selected run directory is already initialized")
        assert self.run_dir is not None
        with campaign_run_lock(self.run_dir):
            self._prepare_new_run()
            return self._execute()

    def resume(self) -> Path:
        if self.run_dir is None:
            raise CampaignRunError("resume requires a run directory")
        with campaign_run_lock(self.run_dir):
            self._load_run()
            if self._terminal_recovered:
                return self.run_dir
            return self._execute()

    def _select_new_run(self) -> None:
        runs = (self.options.runs_dir or self.campaign.runs_dir).resolve()
        runs.mkdir(parents=True, exist_ok=True)
        token = secrets.token_hex(3)
        run_id = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + f"-{token}"
        self.run_dir = runs / run_id
        self.run_dir.mkdir(parents=True, exist_ok=False)

    def _prepare_new_run(self) -> None:
        assert self.run_dir is not None
        run_id = self.run_dir.name
        for name in (
            "configuration",
            "input-snapshot",
            "agents",
            "stages",
            "logs",
            "prompts",
            "recovery",
        ):
            (self.run_dir / name).mkdir()
        self._retain_configuration()
        self._create_inputs()
        self.workspace = self.run_dir / "workspace"
        self._create_workspace()
        self.state = {
            "schema_version": 1,
            "run_id": run_id,
            "campaign_id": self.campaign.campaign_id,
            "campaign_manifest": str(self.campaign.manifest_path),
            "campaign_resolved": "configuration/resolved.json",
            "status": "running",
            "created_at": utc_now(),
            "completed_at": None,
            "controller_pid": os.getpid(),
            "herdr_workspace_id": None,
            "herdr_closed": False,
            "herdr_creation_label": None,
            "revisions": 0,
            "handoff": None,
            "stages": {
                stage.stage_id: {
                    "status": "pending",
                    "attempts": 0,
                    "summary": None,
                    "artifacts": [],
                    "completed_at": None,
                }
                for stage in self.campaign.stages
            },
            "events": [],
            "error": None,
            "pending_output_cleanup": [],
        }
        self._event("run", "running", "campaign initialized")
        self._save_state()
        self._write_evidence()

    def _load_run(self) -> None:
        assert self.run_dir is not None
        retained_journal = journal_path(self.run_dir)
        recovered_tail = False
        if retained_journal.is_file():
            if retained_journal.is_symlink():
                raise CampaignRunError("retained event journal is a symlink")
            try:
                with tempfile.TemporaryDirectory(
                    prefix="campaign-journal-recovery-"
                ) as temporary:
                    temporary_run = Path(temporary)
                    shutil.copyfile(retained_journal, journal_path(temporary_run))
                    recovered = load_state_snapshot(temporary_run)
            except (JournalError, OSError) as exc:
                raise CampaignRunError(f"cannot recover retained state: {exc}") from exc
            value: object = recovered.state
            recovered_tail = recovered.repaired_truncated_tail
        else:
            state_path = self.run_dir / "state.json"
            try:
                value = json.loads(state_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise CampaignRunError(f"cannot read retained state: {exc}") from exc
        value = _validate_retained_state(value, self.campaign)
        _verify_configuration_manifest(self.run_dir)
        _verify_input_manifest(self.run_dir)
        self._verify_resume_evidence(value)
        if retained_journal.is_file():
            try:
                confirmed = load_state_snapshot(self.run_dir)
            except JournalError as exc:
                raise CampaignRunError(f"cannot recover retained state: {exc}") from exc
            if confirmed.state != value:
                raise CampaignRunError("retained event journal changed during recovery")
            recovered_tail = confirmed.repaired_truncated_tail
        self.state = value
        self.workspace = self.run_dir / "workspace"
        self._complete_pending_output_cleanup()
        retry_selected = bool(self.options.retry_stages)
        if self.options.retry_failed and retry_selected:
            raise CampaignRunError(
                "retry_failed and retry_stages are mutually exclusive"
            )
        if self.options.retry_feedback and not retry_selected:
            raise CampaignRunError("retry_feedback requires retry_stages")
        if value.get("status") == "complete" and not (
            self.options.retry_failed or retry_selected
        ):
            assert self.workspace is not None
            self._recover_interrupted_attempts(
                require_checkpoints=retained_journal.is_file()
            )
            if not self.workspace.is_dir():
                raise CampaignRunError("retained workspace is missing")
            self._save_state()
            self._write_evidence()
            self._terminal_recovered = True
            return
        resumable = {
            "running",
            "awaiting_approval",
            "incomplete",
            "stopped",
            "restart_required",
        }
        if retry_selected:
            resumable.add("complete")
        if value.get("status") not in resumable:
            raise CampaignRunError(
                f"run cannot resume from status {value.get('status')!r}"
            )
        assert self.workspace is not None
        self._recover_interrupted_attempts(
            require_checkpoints=retained_journal.is_file()
        )
        if not self.workspace.is_dir():
            raise CampaignRunError("retained workspace is missing")
        self.state["status"] = "running"
        self.state["completed_at"] = None
        self.state["controller_pid"] = os.getpid()
        self.state["error"] = None
        if self.options.retry_failed:
            self._retry_failed_stages()
        elif retry_selected:
            self._retry_selected_stages()
        if recovered_tail:
            self._event(
                "run",
                "recovered",
                "discarded one truncated event-journal tail",
            )
        self._event("run", "running", "campaign resumed")
        self._save_state()
        self._cleanup_orphan_checkpoints()
        self._write_evidence()

    def _verify_resume_evidence(self, state: dict[str, Any]) -> None:
        assert self.run_dir is not None
        evidence_path = self.run_dir / "evidence.json"
        try:
            evidence: object = json.loads(evidence_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise CampaignRunError(
                f"cannot verify retained evidence before resume: {exc}"
            ) from exc
        indexed_paths: set[str] = set()
        if isinstance(evidence, dict) and isinstance(evidence.get("artifacts"), list):
            for artifact in evidence["artifacts"]:
                if isinstance(artifact, dict) and isinstance(artifact.get("path"), str):
                    indexed_paths.add(artifact["path"])
        permitted = {"state.json", "events.jsonl"}
        permitted.update(
            self._recoverable_attempt_evidence_paths(state, indexed_paths=indexed_paths)
        )
        try:
            verify_evidence_for_repair(self.run_dir, permitted_paths=permitted)
        except (OSError, TypeError, ValueError) as exc:
            raise CampaignRunError(
                f"cannot verify retained evidence before resume: {exc}"
            ) from exc
        assert isinstance(evidence, dict)
        if evidence.get("campaign_id") != self.campaign.campaign_id:
            raise CampaignRunError(
                "cannot verify retained evidence before resume: "
                "evidence belongs to a different campaign"
            )
        if evidence.get("status") != state.get("status") and not (
            state.get("status") == "running"
            and isinstance(state.get("pending_output_cleanup"), list)
            and bool(state["pending_output_cleanup"])
        ):
            raise CampaignRunError(
                "cannot verify retained evidence before resume: "
                "evidence status does not match the retained journal"
            )

    def _recoverable_attempt_evidence_paths(
        self, state: dict[str, Any], *, indexed_paths: set[str]
    ) -> set[str]:
        assert self.run_dir is not None
        permitted: set[str] = set()
        for stage_id, stage_state in state["stages"].items():
            if stage_state["status"] != "running":
                continue
            attempt = int(stage_state["attempts"])
            attempt_name = f"attempt-{attempt:02d}"
            config = self.configs[stage_id]
            category = getattr(config, "category", None)
            stage_dir = (
                self.run_dir / "agents" / category / stage_id
                if isinstance(category, str)
                else self.run_dir / "stages" / stage_id
            )
            if stage_dir.is_dir():
                for path in stage_dir.rglob("*"):
                    if not path.is_file() or path.is_symlink():
                        continue
                    relative_attempt = path.relative_to(stage_dir)
                    if relative_attempt.parts[0].startswith(attempt_name):
                        permitted.add(path.relative_to(self.run_dir).as_posix())
            for path in (
                self.run_dir / "logs" / f"{stage_id}-{attempt_name}.stdout.log",
                self.run_dir / "logs" / f"{stage_id}-{attempt_name}.stderr.log",
                self.run_dir / "prompts" / f"{stage_id}-{attempt_name}.md",
            ):
                if path.is_file() and not path.is_symlink():
                    permitted.add(path.relative_to(self.run_dir).as_posix())
            checkpoint = self._checkpoint_path(stage_id, attempt)
            if checkpoint.is_dir() and not checkpoint.is_symlink():
                for path in checkpoint.rglob("*"):
                    if not path.is_file() or path.is_symlink():
                        continue
                    relative = path.relative_to(self.run_dir).as_posix()
                    if relative not in indexed_paths:
                        permitted.add(relative)
            stage = self.campaign.by_id[stage_id]
            if stage.feature == "artifact_promote":
                destination_value = stage.config.get("destination")
                if isinstance(destination_value, str):
                    destination = self.run_dir / destination_value
                    candidates = (
                        tuple(destination.rglob("*"))
                        if destination.is_dir() and not destination.is_symlink()
                        else (destination,)
                    )
                    permitted.update(
                        path.relative_to(self.run_dir).as_posix()
                        for path in candidates
                        if path.is_file() and not path.is_symlink()
                    )
                    if destination.parent.is_dir():
                        for temporary in destination.parent.glob(
                            f".{destination.name}.*"
                        ):
                            temporary_paths = (
                                temporary.rglob("*")
                                if temporary.is_dir() and not temporary.is_symlink()
                                else (temporary,)
                            )
                            permitted.update(
                                path.relative_to(self.run_dir).as_posix()
                                for path in temporary_paths
                                if path.is_file() and not path.is_symlink()
                            )
        return permitted

    def _retry_failed_stages(self) -> None:
        assert self.run_dir is not None
        failed = {
            stage_id
            for stage_id, stage_state in self.state["stages"].items()
            if stage_state["status"] == "failed"
        }
        if not failed:
            raise CampaignRunError("retained run has no failed stages to retry")
        self._reset_stages(
            failed,
            (),
            event_summary="failed stages and descendants",
        )

    def _retry_selected_stages(self) -> None:
        requested = set(self.options.retry_stages)
        unknown = requested - self.campaign.by_id.keys()
        if unknown:
            raise CampaignRunError(f"retry requested unknown stages: {sorted(unknown)}")
        self._reset_stages(
            requested,
            self.options.retry_feedback,
            event_summary="operator-selected stages and descendants",
        )

    def _reset_stages(
        self,
        targets: set[str],
        feedback: tuple[str, ...],
        *,
        event_summary: str,
    ) -> None:
        affected = set(targets)
        changed = True
        while changed:
            changed = False
            for stage in self.campaign.stages:
                if stage.stage_id not in affected and set(stage.depends_on) & affected:
                    affected.add(stage.stage_id)
                    changed = True
        for stage_id in affected:
            stage_state = self.state["stages"][stage_id]
            prior_summary = stage_state.get("summary")
            stage_state["status"] = "pending"
            stage_state["summary"] = None
            stage_state["artifacts"] = []
            stage_state["completed_at"] = None
            stage_state.pop("feedback", None)
            if stage_id in targets:
                retry_feedback = list(feedback)
                if not retry_feedback and isinstance(prior_summary, str):
                    retry_feedback = [
                        f"Operator-requested retry after: {prior_summary}"
                    ]
                if retry_feedback:
                    stage_state["feedback"] = retry_feedback
        handoff = self.campaign.handoff
        if handoff is not None and handoff.producer in affected:
            self.state["handoff"] = None
        self._event(
            "run",
            "retrying",
            f"{event_summary}: {', '.join(sorted(affected))}",
        )
        self._schedule_promotion_output_cleanup(affected)

    def _schedule_promotion_output_cleanup(self, affected: set[str]) -> None:
        self.state["pending_output_cleanup"] = sorted(
            stage.stage_id
            for stage in self.campaign.stages
            if stage.stage_id in affected and stage.feature == "artifact_promote"
        )
        self._save_state()
        self._write_evidence()
        self._complete_pending_output_cleanup()

    def _complete_pending_output_cleanup(self) -> None:
        assert self.run_dir is not None
        pending = self.state.get("pending_output_cleanup", [])
        if not pending:
            return
        for stage_id in pending:
            stage = self.campaign.by_id[stage_id]
            destination_value = stage.config.get("destination")
            if not isinstance(destination_value, str):
                continue
            destination = self.run_dir / destination_value
            try:
                destination.parent.resolve().relative_to(self.run_dir.resolve())
            except ValueError as exc:
                raise CampaignRunError(
                    f"promotion destination escapes run directory: {destination}"
                ) from exc
            if destination.is_symlink() or destination.is_file():
                destination.unlink()
            elif destination.is_dir():
                shutil.rmtree(destination)
        self.state["pending_output_cleanup"] = []
        self._save_state()
        self._write_evidence()

    def _execute(self) -> Path:
        assert self.run_dir is not None and self.workspace is not None
        interrupted = False
        previous_handlers: dict[int, Any] = {}

        def interrupt(_signal_number: int, _frame: object) -> None:
            nonlocal interrupted
            if interrupted:
                return
            interrupted = True
            raise KeyboardInterrupt

        try:
            for handled_signal in (
                signal.SIGHUP,
                signal.SIGQUIT,
                signal.SIGTERM,
            ):
                previous_handlers[handled_signal] = signal.signal(
                    handled_signal, interrupt
                )
        except ValueError:
            previous_handlers.clear()
        try:
            register_campaign(self.run_dir, self.options.herdr)
            if self._has_pending_agents():
                self._create_herdr_workspace()
            while True:
                if self._approval_needed():
                    self._await_approval()
                    return self.run_dir
                ready = self._ready_stages()
                if not ready:
                    break
                stage = ready[0]
                result = self._run_stage(stage)
                self._write_evidence()
                self._consume(stage, result)
                stage_state = self.state["stages"][stage.stage_id]
                if stage_state["status"] != "pending":
                    self._clear_stage_checkpoints(stage.stage_id)
                self._write_evidence()
                if self.state["status"] != "running":
                    break
            if self.state["status"] == "running":
                self._finish_from_stages()
        except KeyboardInterrupt:
            self.state["status"] = "stopped"
            self.state["error"] = "campaign interrupted"
            self._event("run", "stopped", "campaign interrupted")
        except Exception as exc:
            self.state["status"] = "failed"
            self.state["error"] = f"{type(exc).__name__}: {exc}"
            self._event("run", "failed", self.state["error"])
            raise
        finally:
            self._finalize_herdr()
            if self.state.get("status") != "running":
                self.state["completed_at"] = utc_now()
            self._save_state()
            self._write_evidence()
            workspace_id = self.state.get("herdr_workspace_id")
            if (
                not isinstance(workspace_id, str)
                or self.state.get("herdr_closed") is True
            ):
                unregister_campaign()
            for registered_signal, previous in previous_handlers.items():
                signal.signal(registered_signal, previous)
        return self.run_dir

    def _ready_stages(self) -> list[StageSpec]:
        stages = self.state["stages"]
        ready: list[StageSpec] = []
        for stage_id in self.campaign.stage_order:
            stage = self.campaign.by_id[stage_id]
            status = stages[stage_id]["status"]
            if status != "pending":
                continue
            dependency_statuses = [
                stages[dependency]["status"] for dependency in stage.depends_on
            ]
            if any(status in ("failed", "skipped") for status in dependency_statuses):
                stages[stage_id]["status"] = "skipped"
                stages[stage_id]["summary"] = "dependency did not succeed"
                self._event(stage_id, "skipped", "dependency did not succeed")
                self._save_state()
                continue
            if stage.mode == "build" and not self._build_handoff_ready():
                continue
            if all(status == "succeeded" for status in dependency_statuses):
                ready.append(stage)
        return ready

    def _checkpoint_path(self, stage_id: str, attempt: int) -> Path:
        assert self.run_dir is not None
        return self.run_dir / "recovery" / f"{stage_id}-attempt-{attempt:03d}"

    def _checkpoint_workspace(self, stage_id: str, attempt: int) -> None:
        assert self.run_dir is not None and self.workspace is not None
        recovery = self.run_dir / "recovery"
        recovery.mkdir(exist_ok=True)
        checkpoint = self._checkpoint_path(stage_id, attempt)
        if checkpoint.exists():
            shutil.rmtree(checkpoint)
        temporary = Path(tempfile.mkdtemp(prefix=f".{checkpoint.name}-", dir=recovery))
        snapshot = temporary / "workspace"
        try:
            shutil.copytree(
                self.workspace,
                snapshot,
                symlinks=True,
                ignore=shutil.ignore_patterns(*_CHECKPOINT_IGNORED_NAMES),
            )
            _fsync_tree(snapshot)
            os.replace(snapshot, checkpoint)
            _fsync_directory(recovery)
        finally:
            shutil.rmtree(temporary, ignore_errors=True)

    def _restore_checkpoint(self, stage_id: str, attempt: int) -> bool:
        assert self.run_dir is not None and self.workspace is not None
        checkpoint = self._checkpoint_path(stage_id, attempt)
        if checkpoint.is_symlink() or not checkpoint.is_dir():
            return False
        if self.workspace.is_symlink():
            raise CampaignRunError("retained workspace is a symlink")
        if self.workspace.exists():
            shutil.rmtree(self.workspace)
        shutil.copytree(checkpoint, self.workspace, symlinks=True)
        _fsync_tree(self.workspace)
        _fsync_directory(self.run_dir)
        return True

    def _clear_checkpoint(self, stage_id: str, attempt: int) -> None:
        assert self.run_dir is not None
        checkpoint = self._checkpoint_path(stage_id, attempt)
        if checkpoint.is_symlink() or checkpoint.is_file():
            checkpoint.unlink()
        elif checkpoint.is_dir():
            shutil.rmtree(checkpoint)
        _fsync_directory(self.run_dir / "recovery")

    def _clear_stage_checkpoints(self, stage_id: str) -> None:
        assert self.run_dir is not None
        recovery = self.run_dir / "recovery"
        for checkpoint in recovery.glob(f"{stage_id}-attempt-*"):
            if checkpoint.is_symlink() or checkpoint.is_file():
                checkpoint.unlink()
            elif checkpoint.is_dir():
                shutil.rmtree(checkpoint)
        _fsync_directory(recovery)

    def _cleanup_orphan_checkpoints(self) -> None:
        assert self.run_dir is not None
        recovery = self.run_dir / "recovery"
        if not recovery.is_dir():
            recovery.mkdir()
            _fsync_directory(self.run_dir)
            return
        for path in tuple(recovery.iterdir()):
            if path.is_symlink() or path.is_file():
                path.unlink()
            else:
                shutil.rmtree(path)
        _fsync_directory(recovery)

    def _recover_interrupted_attempts(self, *, require_checkpoints: bool) -> None:
        assert self.run_dir is not None
        stale_workspaces = set(registered_workspaces(self.run_dir))
        creation_intents = set(registered_workspace_intents(self.run_dir))
        creation_label = self.state.get("herdr_creation_label")
        if isinstance(creation_label, str):
            creation_intents.add((self.options.herdr, creation_label))
        report = terminate_run_processes(self.run_dir)
        if not report.ok:
            raise CampaignRunError(
                "stale run resources survived recovery: "
                f"pids={list(report.surviving_pids)}, "
                f"units={list(report.unit_errors)}"
            )
        workspace_id = self.state.get("herdr_workspace_id")
        if isinstance(workspace_id, str):
            stale_workspaces.add((self.options.herdr, workspace_id))
        for executable, retained_label in creation_intents:
            try:
                stale_workspaces.update(
                    (executable, workspace.workspace_id)
                    for workspace in HerdrClient(executable).list_workspaces()
                    if workspace.label == retained_label
                )
            except HerdrError as exc:
                raise CampaignRunError(
                    f"cannot discover stale Herdr workspace: {exc}"
                ) from exc
        for executable, stale_workspace_id in stale_workspaces:
            try:
                HerdrClient(executable).close_workspace(stale_workspace_id)
            except HerdrError as exc:
                if exc.code != "workspace_not_found":
                    raise CampaignRunError(
                        f"cannot close stale Herdr workspace: {exc}"
                    ) from exc
        if stale_workspaces or creation_intents:
            self.state["herdr_workspace_id"] = None
            self.state["herdr_creation_label"] = None
            self.state["herdr_closed"] = True
        stages = self.state["stages"]
        for stage_id, stage_state in stages.items():
            if stage_state["status"] != "running":
                continue
            attempt = int(stage_state["attempts"])
            restored = self._restore_checkpoint(stage_id, attempt)
            if require_checkpoints and not restored:
                raise CampaignRunError(
                    f"interrupted stage {stage_id!r} has no recovery checkpoint"
                )
            stage_state["status"] = "pending"
            stage_state["summary"] = (
                f"attempt {attempt} interrupted by controller termination"
            )
            stage_state["completed_at"] = utc_now()
            stage_state["interruptions"] = int(stage_state.get("interruptions", 0)) + 1
            self._event(
                stage_id,
                "interrupted",
                f"attempt {attempt} restored for deterministic retry",
            )

    def _run_stage(self, stage: StageSpec) -> FeatureResult:
        assert self.run_dir is not None and self.workspace is not None
        stage_state = self.state["stages"][stage.stage_id]
        config = self.configs[stage.stage_id]
        category = getattr(config, "category", None)
        stage_dir = (
            self.run_dir / "agents" / category / stage.stage_id
            if isinstance(category, str)
            else self.run_dir / "stages" / stage.stage_id
        )
        stage_dir.mkdir(parents=True, exist_ok=True)
        attempt = int(stage_state["attempts"]) + 1
        self._checkpoint_workspace(stage.stage_id, attempt)
        stage_state["attempts"] = attempt
        stage_state["status"] = "running"
        self._event(stage.stage_id, "running", f"attempt {attempt}")
        self._save_state()
        self._write_evidence()
        dependencies = tuple(
            path
            for dependency in stage.depends_on
            for path in self._report_paths(dependency)
        )
        feedback = tuple(stage_state.pop("feedback", []))
        context = FeatureContext(
            campaign=self.campaign,
            stage=stage,
            config=config,
            attempt=attempt,
            run_dir=self.run_dir,
            workspace=self.workspace,
            stage_dir=stage_dir,
            prompt_dir=self.run_dir / "prompts",
            log_dir=self.run_dir / "logs",
            feedback=feedback,
            dependency_reports=dependencies,
            dependency_artifacts={
                dependency: self._artifact_paths(dependency)
                for dependency in stage.depends_on
            },
            herdr=self.herdr if self.herdr_workspace is not None else None,
            pane_id=self.panes.get(stage.stage_id),
            omp=self.options.omp,
            lake=self.options.lake,
            python_executable=self.python_executable,
        )
        try:
            return self.registry.feature(stage.feature).execute(context)
        except (
            ConfigurationError,
            HerdrError,
            OSError,
            RuntimeError,
            ValueError,
        ) as exc:
            return FeatureResult("failed", f"{type(exc).__name__}: {exc}")

    def _consume(self, stage: StageSpec, result: FeatureResult) -> None:
        assert self.run_dir is not None
        cleanup = terminate_run_processes(self.run_dir)
        if not cleanup.ok:
            result = FeatureResult(
                "failed",
                "stage process cleanup failed: "
                f"survivors={list(cleanup.surviving_pids)}, "
                f"unit_errors={list(cleanup.unit_errors)}",
            )
        stage_state = self.state["stages"][stage.stage_id]
        stage_state["summary"] = result.summary
        prior_artifacts = tuple(stage_state["artifacts"])
        result_artifacts = tuple(self._retained_path(path) for path in result.artifacts)
        stage_state["artifacts"] = list(
            dict.fromkeys((*prior_artifacts, *result_artifacts))
        )
        stage_state["completed_at"] = utc_now()
        if result.succeeded:
            stage_state["status"] = "succeeded"
            self._event(stage.stage_id, "succeeded", result.summary)
            self._save_state()
            return
        if result.status == "revision_requested":
            if self.state["revisions"] >= self.campaign.max_revisions:
                self._restore_retry_checkpoint(stage)
                stage_state["status"] = "failed"
                self._event(stage.stage_id, "failed", "revision limit exhausted")
                self._fail_required(stage, "revision limit exhausted")
                return
            self.state["revisions"] += 1
            self._restore_retry_checkpoint(stage)
            self._route_retry(result.retry_targets, result.required_changes, stage)
            return
        if result.retry_targets and stage_state["attempts"] < stage.max_attempts:
            self._restore_retry_checkpoint(stage)
            self._route_retry(result.retry_targets, (result.summary,), stage)
            return
        if stage_state["attempts"] < stage.max_attempts:
            partial = self._retain_partial_agent_output(stage)
            stage_state["artifacts"].extend(
                self._retained_path(path) for path in partial
            )
            stage_state["status"] = "pending"
            stage_state["completed_at"] = None
            stage_state["feedback"] = [
                f"{result.summary}; continue from the retained partial workspace"
            ]
            self._event(
                stage.stage_id,
                "retrying",
                f"{result.summary}; continuing from partial workspace",
            )
            self._save_state()
            return
        self._restore_retry_checkpoint(stage)
        stage_state["status"] = "failed"
        self._event(stage.stage_id, "failed", result.summary)
        if stage.failure_policy == "replan":
            self.state["status"] = "replan_required"
            self.state["error"] = (
                f"stage {stage.stage_id!r} exhausted attempts and requires replanning"
            )
            self._save_state()
        elif stage.failure_policy == "restart":
            self.state["status"] = "restart_required"
            self.state["error"] = (
                f"stage {stage.stage_id!r} exhausted attempts and requires a restart"
            )
            self._save_state()
        elif stage.required:
            self._fail_required(stage, result.summary)
        else:
            self._save_state()

    def _retain_partial_agent_output(self, stage: StageSpec) -> tuple[Path, ...]:
        """Preserve an agent's useful partial files before restoring its checkpoint."""
        assert self.run_dir is not None and self.workspace is not None
        config = self.configs[stage.stage_id]
        category = getattr(config, "category", None)
        if not isinstance(category, str):
            return ()
        source = self.workspace / "agents" / category / stage.stage_id
        if source.is_symlink() or not source.is_dir():
            return ()
        attempt = int(self.state["stages"][stage.stage_id]["attempts"])
        stage_dir = self.run_dir / "agents" / category / stage.stage_id
        destination = stage_dir / f"attempt-{attempt:02d}-partial"
        receipt = stage_dir / f"attempt-{attempt:02d}-partial.json"
        if destination.exists() or receipt.exists():
            raise CampaignRunError(
                f"partial output already retained for stage {stage.stage_id!r} "
                f"attempt {attempt}"
            )
        stage_dir.mkdir(parents=True, exist_ok=True)
        temporary = Path(
            tempfile.mkdtemp(
                prefix=f".{destination.name}-",
                dir=stage_dir,
            )
        )
        retained: list[str] = []
        omitted: list[str] = []
        try:
            for path in sorted(source.rglob("*")):
                relative = path.relative_to(source)
                relative_name = relative.as_posix()
                target = temporary / relative
                if path.is_symlink():
                    omitted.append(relative_name)
                elif path.is_dir():
                    target.mkdir(parents=True, exist_ok=True)
                elif path.is_file():
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(path, target)
                    retained.append(relative_name)
                else:
                    omitted.append(relative_name)
            if not retained:
                return ()
            _fsync_tree(temporary)
            os.replace(temporary, destination)
            _fsync_directory(stage_dir)
            atomic_write_json(
                receipt,
                {
                    "schema_version": 1,
                    "stage": stage.stage_id,
                    "attempt": attempt,
                    "status": "partial",
                    "retained": retained,
                    "omitted": omitted,
                },
            )
            return (
                receipt,
                *(destination / relative for relative in retained),
            )
        finally:
            shutil.rmtree(temporary, ignore_errors=True)

    def _retain_partial_workspace(self, stage: StageSpec) -> tuple[Path, ...]:
        """Retain files changed by a failed final attempt before rollback."""
        assert self.run_dir is not None and self.workspace is not None
        config = self.configs[stage.stage_id]
        category = getattr(config, "category", None)
        if not isinstance(category, str):
            return ()
        attempt = int(self.state["stages"][stage.stage_id]["attempts"])
        checkpoints = tuple(
            self._checkpoint_path(stage.stage_id, candidate)
            for candidate in range(1, attempt + 1)
            if self._checkpoint_path(stage.stage_id, candidate).is_dir()
        )
        if not checkpoints:
            return ()
        baseline = checkpoints[0]
        stage_dir = self.run_dir / "agents" / category / stage.stage_id
        destination = stage_dir / f"attempt-{attempt:02d}-workspace-partial"
        receipt = stage_dir / f"attempt-{attempt:02d}-workspace-partial.json"
        if destination.exists() or receipt.exists():
            raise CampaignRunError(
                f"partial workspace already retained for stage {stage.stage_id!r} "
                f"attempt {attempt}"
            )
        stage_dir.mkdir(parents=True, exist_ok=True)
        temporary = Path(
            tempfile.mkdtemp(prefix=f".{destination.name}-", dir=stage_dir)
        )
        changed: list[str] = []
        deleted: list[str] = []

        def ignored(relative: Path) -> bool:
            return any(part in _CHECKPOINT_IGNORED_NAMES for part in relative.parts)

        try:
            for path in sorted(self.workspace.rglob("*")):
                relative = path.relative_to(self.workspace)
                if ignored(relative) or path.is_symlink() or not path.is_file():
                    continue
                original = baseline / relative
                if (
                    original.is_file()
                    and not original.is_symlink()
                    and filecmp.cmp(path, original, shallow=False)
                ):
                    continue
                target = temporary / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, target)
                changed.append(relative.as_posix())
            for original in sorted(baseline.rglob("*")):
                relative = original.relative_to(baseline)
                if (
                    ignored(relative)
                    or original.is_symlink()
                    or not original.is_file()
                    or (self.workspace / relative).exists()
                ):
                    continue
                deleted.append(relative.as_posix())
            if not changed and not deleted:
                return ()
            _fsync_tree(temporary)
            os.replace(temporary, destination)
            _fsync_directory(stage_dir)
            atomic_write_json(
                receipt,
                {
                    "schema_version": 1,
                    "stage": stage.stage_id,
                    "attempt": attempt,
                    "status": "partial-workspace",
                    "baseline_attempt": 1,
                    "changed": changed,
                    "deleted": deleted,
                },
            )
            return (
                receipt,
                *(destination / relative for relative in changed),
            )
        finally:
            shutil.rmtree(temporary, ignore_errors=True)

    def _restore_retry_checkpoint(self, stage: StageSpec) -> None:
        partial = (
            *self._retain_partial_agent_output(stage),
            *self._retain_partial_workspace(stage),
        )
        stage_state = self.state["stages"][stage.stage_id]
        stage_state["artifacts"].extend(self._retained_path(path) for path in partial)
        attempt = int(stage_state["attempts"])
        baseline_attempt = next(
            (
                candidate
                for candidate in range(1, attempt + 1)
                if self._checkpoint_path(stage.stage_id, candidate).is_dir()
            ),
            None,
        )
        if baseline_attempt is None or not self._restore_checkpoint(
            stage.stage_id, baseline_attempt
        ):
            raise CampaignRunError(
                f"retrying stage {stage.stage_id!r} has no recovery checkpoint"
            )

    def _route_retry(
        self,
        targets: tuple[str, ...],
        changes: tuple[str, ...],
        requesting_stage: StageSpec,
    ) -> None:
        unknown = set(targets) - self.campaign.by_id.keys()
        if unknown:
            self._fail_required(
                requesting_stage, f"retry requested unknown stages: {sorted(unknown)}"
            )
            return
        affected = set(targets)
        changed = True
        while changed:
            changed = False
            for stage in self.campaign.stages:
                if stage.stage_id not in affected and set(stage.depends_on) & affected:
                    affected.add(stage.stage_id)
                    changed = True
        self.state["pending_output_cleanup"] = sorted(
            stage.stage_id
            for stage in self.campaign.stages
            if stage.stage_id in affected and stage.feature == "artifact_promote"
        )
        handoff = self.campaign.handoff
        if handoff is not None and handoff.producer in affected:
            self.state["handoff"] = None
        for stage_id in affected:
            state = self.state["stages"][stage_id]
            state["status"] = "pending"
            state["completed_at"] = None
            if stage_id in targets:
                state["feedback"] = list(changes)
        self._event(
            requesting_stage.stage_id,
            "revision_routed",
            f"targets: {', '.join(sorted(targets))}",
        )
        self._save_state()
        self._complete_pending_output_cleanup()

    def _fail_required(self, stage: StageSpec, summary: str) -> None:
        self.state["status"] = "incomplete"
        self.state["error"] = f"required stage {stage.stage_id!r} failed: {summary}"
        self._save_state()

    def _finish_from_stages(self) -> None:
        required = [
            self.state["stages"][stage.stage_id]["status"]
            for stage in self.campaign.stages
            if stage.required
        ]
        if required and all(status == "succeeded" for status in required):
            self.state["status"] = "complete"
            self._event("run", "complete", "all required stages succeeded")
        else:
            self.state["status"] = "incomplete"
            self.state["error"] = "campaign has unresolved required stages"
            self._event("run", "incomplete", self.state["error"])

    def _approval_needed(self) -> bool:
        handoff = self.campaign.handoff
        if handoff is None:
            return False
        producer = self.state["stages"][handoff.producer]
        if producer["status"] != "succeeded":
            return False
        build_pending = any(
            stage.mode == "build"
            and self.state["stages"][stage.stage_id]["status"] == "pending"
            for stage in self.campaign.stages
        )
        if not build_pending:
            return False
        path = self._handoff_path()
        digest = digest_handoff(path, handoff.schema)
        recorded = self.state.get("handoff")
        if recorded is not None and recorded.get("sha256") != digest:
            raise CampaignRunError("approved research handoff changed")
        if recorded is None:
            self.state["handoff"] = {
                "producer": handoff.producer,
                "path": handoff.artifact,
                "schema": handoff.schema,
                "sha256": digest,
                "approved": handoff.approval == "automatic",
                "approved_at": utc_now() if handoff.approval == "automatic" else None,
            }
            self._save_state()
        return not bool(self.state["handoff"]["approved"])

    def _build_handoff_ready(self) -> bool:
        handoff = self.campaign.handoff
        if handoff is None:
            return True
        if self.state["stages"][handoff.producer]["status"] != "succeeded":
            return False
        recorded = self.state.get("handoff")
        return isinstance(recorded, dict) and recorded.get("approved") is True

    def _await_approval(self) -> None:
        self.state["status"] = "awaiting_approval"
        self._event("handoff", "awaiting_approval", "typed research handoff retained")
        self._save_state()

    def _handoff_path(self) -> Path:
        assert self.workspace is not None and self.campaign.handoff is not None
        path = (self.workspace / self.campaign.handoff.artifact).resolve()
        try:
            path.relative_to(self.workspace.resolve())
        except ValueError as exc:
            raise CampaignRunError("handoff artifact escapes the workspace") from exc
        if not path.is_file() or path.is_symlink():
            raise CampaignRunError(f"handoff artifact is missing: {path}")
        return path

    def _has_pending_agents(self) -> bool:
        return any(
            self.state["stages"][stage.stage_id]["status"] == "pending"
            and self.registry.feature(stage.feature).uses_agent
            for stage in self.campaign.stages
        )

    def _create_herdr_workspace(self) -> None:
        assert self.workspace is not None
        agent_stages = [
            stage
            for stage in self.campaign.stages
            if self.state["stages"][stage.stage_id]["status"] == "pending"
            and self.registry.feature(stage.feature).uses_agent
        ]
        label = f"campaign:{self.campaign.campaign_id}:{secrets.token_hex(8)}"
        self.state["herdr_creation_label"] = label
        self._save_state()
        register_workspace_creation(label)
        workspace = self.herdr.create_workspace(
            cwd=self.workspace,
            label=label,
            focus=self.options.focus,
            environment={"NO_COLOR": "1"} if not self.output.isatty() else None,
        )
        self.herdr_workspace = workspace
        register_workspace(workspace.workspace_id)
        self.state["herdr_workspace_id"] = workspace.workspace_id
        self.state["herdr_closed"] = False
        self.state["herdr_creation_label"] = None
        self._save_state()
        clear_workspace_creation()
        anchor = workspace.root_pane_id
        for index, stage in enumerate(agent_stages):
            pane = (
                anchor
                if index == 0
                else self.herdr.split_pane(anchor, cwd=self.workspace)
            )
            self.herdr.rename_pane(pane, stage.title)
            self.panes[stage.stage_id] = pane

    def _finalize_herdr(self) -> None:
        if self.herdr_workspace is None or not self.options.close_herdr:
            return
        try:
            self.herdr.close_workspace(self.herdr_workspace.workspace_id)
        except HerdrError as exc:
            self.state["herdr_close_error"] = str(exc)
        else:
            self.state["herdr_closed"] = True
        self.herdr_workspace = None
        self.panes.clear()

    def _retain_configuration(self) -> None:
        assert self.run_dir is not None
        destination = self.run_dir / "configuration"
        retained_manifest = destination / "campaign.toml"
        retained_campaign = destination / "campaign.md"
        shutil.copy2(self.campaign.manifest_path, retained_manifest)
        shutil.copy2(self.campaign.instructions_path, retained_campaign)
        instructions = destination / "stage-instructions"
        instructions.mkdir()
        stage_instructions: dict[str, Path] = {}
        for stage_id, config in self.configs.items():
            path = getattr(config, "instructions", None)
            if isinstance(path, Path):
                retained_path = instructions / f"{stage_id}{path.suffix}"
                shutil.copy2(path, retained_path)
                stage_instructions[stage_id] = retained_path.resolve()
        atomic_write_json(
            destination / "features.json",
            {
                "schema_version": 1,
                "registered": list(self.registry.feature_ids),
                "stages": {
                    stage.stage_id: stage.feature for stage in self.campaign.stages
                },
            },
        )
        atomic_write_json(
            destination / "resolved.json",
            self.campaign.to_resolved_dict(
                manifest_path=retained_manifest.resolve(),
                instructions_path=retained_campaign.resolve(),
                stage_instructions=stage_instructions,
            ),
        )
        artifacts = digest_tree(destination)
        atomic_write_json(
            destination / "manifest.json",
            {
                "schema_version": 1,
                "artifacts": [artifact.to_dict() for artifact in artifacts],
            },
        )

    def _create_inputs(self) -> None:
        assert self.run_dir is not None
        snapshot = self.run_dir / "input-snapshot"
        records: list[dict[str, object]] = []
        for item in self.campaign.inputs:
            if item.strategy == "symlink":
                records.append(
                    {
                        "target": item.target,
                        "strategy": "symlink",
                        "source": str(item.source),
                    }
                )
                continue
            destination = snapshot / item.target
            if item.strategy == "verified_artifact":
                _copy_verified_artifact(item, destination)
            else:
                _copy_input(item, destination)
            artifacts = (
                digest_tree(destination)
                if destination.is_dir()
                else (digest_file(destination, relative_to=snapshot),)
            )
            if item.strategy == "verified_artifact":
                records.append(
                    {
                        "target": item.target,
                        "strategy": "verified_artifact",
                        "source": str(item.source),
                        "artifact": item.artifact,
                        "expected_campaign_id": item.expected_campaign_id,
                        "expected_run_id": item.expected_run_id,
                        "evidence_sha256": item.evidence_sha256,
                        "artifacts": [artifact.to_dict() for artifact in artifacts],
                    }
                )
            else:
                records.append(
                    {
                        "target": item.target,
                        "strategy": "copy",
                        "artifacts": [artifact.to_dict() for artifact in artifacts],
                    }
                )
        atomic_write_json(
            self.run_dir / "input-manifest.json",
            {"schema_version": 1, "created_at": utc_now(), "inputs": records},
        )

    def _create_workspace(self) -> None:
        assert self.run_dir is not None and self.workspace is not None
        self.workspace.mkdir()
        shutil.copytree(
            self.run_dir / "input-snapshot", self.workspace, dirs_exist_ok=True
        )
        for item in self.campaign.inputs:
            if item.strategy != "symlink":
                continue
            destination = self.workspace / item.target
            destination.parent.mkdir(parents=True, exist_ok=True)
            if destination.exists() or destination.is_symlink():
                raise ConfigurationError(
                    f"symlink input target already exists: {item.target}"
                )
            destination.symlink_to(
                item.source, target_is_directory=item.source.is_dir()
            )

    def _artifact_paths(self, stage_id: str) -> tuple[Path, ...]:
        assert self.run_dir is not None and self.workspace is not None
        values = self.state["stages"][stage_id]["artifacts"]
        paths: list[Path] = []
        for value in values:
            if not isinstance(value, str):
                continue
            path = (
                self.workspace / value.removeprefix("workspace:")
                if value.startswith("workspace:")
                else self.run_dir / value
            )
            if path.is_file():
                paths.append(path)
        return tuple(paths)

    def _report_paths(self, stage_id: str) -> tuple[Path, ...]:
        return tuple(
            path
            for path in self._artifact_paths(stage_id)
            if path.suffix in (".md", ".json")
        )

    def _retained_path(self, path: Path) -> str:
        assert self.run_dir is not None and self.workspace is not None
        resolved = path.resolve()
        try:
            return resolved.relative_to(self.run_dir.resolve()).as_posix()
        except ValueError:
            try:
                relative = resolved.relative_to(self.workspace.resolve()).as_posix()
            except ValueError as exc:
                raise CampaignRunError(
                    f"feature returned an artifact outside the run: {path}"
                ) from exc
            return f"workspace:{relative}"

    def _event(self, stage: str, status: str, summary: str) -> None:
        rendered = " ".join(summary.split())
        if len(rendered) > 120:
            rendered = rendered[:117] + "..."
        event = {
            "at": utc_now(),
            "stage": stage,
            "status": status,
            "summary": rendered,
        }
        self.state.setdefault("events", []).append(event)
        self.output.write(f"{stage}: {status}: {rendered}\n")
        self.output.flush()

    def _save_state(self) -> None:
        assert self.run_dir is not None
        events = self.state.get("events")
        last = events[-1] if isinstance(events, list) and events else None
        reason = (
            f"{last.get('stage')}:{last.get('status')}"
            if isinstance(last, dict)
            else "state projection"
        )
        append_state_snapshot(self.run_dir, self.state, reason=reason)
        atomic_write_json(self.run_dir / "state.json", self.state)

    def _write_evidence(self) -> None:
        assert self.run_dir is not None
        _write_campaign_evidence(
            self.run_dir,
            campaign_id=self.campaign.campaign_id,
            status=str(self.state.get("status")),
        )


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _fsync_tree(root: Path) -> None:
    directories = [root]
    for path in root.rglob("*"):
        if path.is_symlink():
            continue
        if path.is_dir():
            directories.append(path)
        elif path.is_file():
            try:
                descriptor = os.open(path, os.O_RDONLY)
            except FileNotFoundError:
                continue
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
    for directory in sorted(
        directories, key=lambda value: len(value.parts), reverse=True
    ):
        try:
            _fsync_directory(directory)
        except FileNotFoundError:
            continue


def approve_handoff(run_dir: Path) -> str:
    """Approve the exact retained handoff digest and return it."""

    resolved = run_dir.expanduser().resolve()
    with campaign_run_lock(resolved):
        return _approve_handoff_locked(resolved)


def _approve_handoff_locked(run_dir: Path) -> str:
    state_path = run_dir / "state.json"
    if journal_path(run_dir).is_file():
        try:
            state = load_state_snapshot(run_dir).state
        except JournalError as exc:
            raise CampaignRunError(f"cannot recover retained state: {exc}") from exc
    else:
        try:
            state = json.loads(state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise CampaignRunError(f"cannot read retained state: {exc}") from exc
    if not isinstance(state, dict) or state.get("status") != "awaiting_approval":
        raise CampaignRunError("run is not awaiting approval")
    campaign_id = state.get("campaign_id")
    if not isinstance(campaign_id, str) or not campaign_id:
        raise CampaignRunError("retained state has no campaign ID")
    handoff = state.get("handoff")
    if not isinstance(handoff, dict) or handoff.get("approved") is not False:
        raise CampaignRunError("run has no unapproved handoff")
    path_value = handoff.get("path")
    schema = handoff.get("schema")
    expected = handoff.get("sha256")
    if (
        not isinstance(path_value, str)
        or not isinstance(schema, str)
        or not isinstance(expected, str)
    ):
        raise CampaignRunError("retained handoff state is malformed")
    path = run_dir / "workspace" / path_value
    observed = digest_handoff(path, schema)
    if observed != expected:
        raise CampaignRunError("research handoff changed before approval")
    handoff["approved"] = True
    handoff["approved_at"] = utc_now()
    append_state_snapshot(run_dir, state, reason="handoff:approved")
    atomic_write_json(state_path, state)
    _write_campaign_evidence(
        run_dir,
        campaign_id=campaign_id,
        status=str(state["status"]),
    )
    return observed


def verify_campaign_bundle(run_dir: Path) -> int:
    return len(verify_evidence_index(run_dir.expanduser().resolve()))


def replay_verifier_command(run_dir: Path, stage_id: str) -> Path:
    """Replay one frozen, explicitly allowlisted verifier command without a shell."""

    run = run_dir.expanduser().resolve()
    with campaign_run_lock(run):
        verify_evidence_index(run)
        if campaign_status(run) != "complete":
            raise CampaignRunError("verifier replay requires a complete campaign")
        campaign = CampaignSpec.load_resolved(campaign_resolved_for_run(run))
        stage = campaign.by_id.get(stage_id)
        if stage is None or stage.feature != "command":
            raise CampaignRunError(
                f"stage {stage_id!r} is not a retained command stage"
            )
        config = FeatureRegistry().validate(campaign)[stage_id]
        replayable = getattr(config, "replayable", None)
        argv = getattr(config, "argv", None)
        cwd_value = getattr(config, "cwd", None)
        timeout = getattr(config, "timeout", None)
        environment = getattr(config, "environment", None)
        evidence_inputs = getattr(config, "evidence_inputs", None)
        workspace_executables = getattr(config, "workspace_executables", None)
        if replayable is not True:
            raise CampaignRunError(
                f"stage {stage_id!r} is not allowlisted for verifier replay"
            )
        if (
            not isinstance(argv, tuple)
            or not all(isinstance(item, str) for item in argv)
            or not isinstance(cwd_value, str)
            or not isinstance(timeout, int)
            or not isinstance(environment, tuple)
            or not isinstance(evidence_inputs, tuple)
            or not isinstance(workspace_executables, bool)
        ):
            raise CampaignRunError("retained replay command is malformed")
        workspace = run / "workspace"
        cwd = (workspace / cwd_value).resolve()
        try:
            cwd.relative_to(workspace.resolve())
        except ValueError as exc:
            raise CampaignRunError("retained replay cwd escapes workspace") from exc
        observed_inputs = [
            artifact.to_dict()
            for artifact in snapshot_workspace_inputs(workspace, evidence_inputs)
        ]
        state_value = campaign_state(run)
        stage_state = state_value.get("stages", {}).get(stage_id, {})
        artifact_values = stage_state.get("artifacts", [])
        retained_receipts = [
            run / value
            for value in artifact_values
            if isinstance(value, str) and value.endswith(".json")
        ]
        if len(retained_receipts) != 1:
            raise CampaignRunError(
                f"stage {stage_id!r} has no unique retained command receipt"
            )
        retained_value = json.loads(retained_receipts[0].read_text(encoding="utf-8"))
        if retained_value.get("evidence_inputs") != observed_inputs:
            raise CampaignRunError(
                f"stage {stage_id!r} evidence inputs changed since execution"
            )
        env = os.environ.copy()
        env.update(dict(environment))
        original_sandbox = retained_value.get("sandbox")
        prospective_sandbox = prepare_sandbox(
            argv,
            cwd=cwd,
            workspace=workspace,
            environment=env,
            policy=campaign.execution,
            allow_workspace_executables=workspace_executables,
            runtime_max_seconds=timeout,
        ).metadata
        if not isinstance(original_sandbox, dict) or any(
            original_sandbox.get(field) != prospective_sandbox.get(field)
            for field in _REPLAY_SECURITY_FIELDS
        ):
            raise CampaignRunError(
                "verifier replay sandbox policy differs from original execution"
            )
        started = time.monotonic()
        completed = run_captured_command(
            argv,
            cwd=cwd,
            env=env,
            timeout=timeout,
            execution=campaign.execution,
            workspace=workspace,
            allow_workspace_executables=workspace_executables,
            run_dir=run,
        )
        observed_inputs_after = [
            artifact.to_dict()
            for artifact in snapshot_workspace_inputs(workspace, evidence_inputs)
        ]
        replay_dir = run / "replays"
        replay_dir.mkdir(exist_ok=True)
        receipt = replay_dir / (
            f"{utc_now().replace(':', '')}-{secrets.token_hex(6)}-{stage_id}.json"
        )
        value: dict[str, object] = {
            "schema_version": 2,
            "stage": stage_id,
            "argv": list(argv),
            "cwd": str(cwd),
            "duration_seconds": round(time.monotonic() - started, 3),
            "error": completed.error,
            "evidence_inputs": observed_inputs,
            "evidence_inputs_after": observed_inputs_after,
        }
        if completed.exit_code is not None:
            value.update(
                {
                    "exit_code": completed.exit_code,
                    "stdout": completed.stdout,
                    "stderr": completed.stderr,
                    "stdout_truncated": completed.stdout_truncated,
                    "stderr_truncated": completed.stderr_truncated,
                    "stdout_sha256": completed.stdout_sha256,
                    "stderr_sha256": completed.stderr_sha256,
                    "sandbox": dict(completed.sandbox),
                }
            )
        atomic_write_json(receipt, value)
        replay_sandbox = dict(completed.sandbox)
        if any(
            original_sandbox.get(field) != replay_sandbox.get(field)
            for field in _REPLAY_SECURITY_FIELDS
        ):
            refresh_campaign_evidence(run)
            raise CampaignRunError(
                "verifier replay sandbox policy changed during execution; "
                f"receipt: {receipt}"
            )
        if observed_inputs_after != observed_inputs:
            refresh_campaign_evidence(run)
            raise CampaignRunError(
                f"verifier replay changed declared evidence inputs; receipt: {receipt}"
            )
        refresh_campaign_evidence(run)
        if completed.error is not None:
            raise CampaignRunError(f"verifier replay could not run: {completed.error}")
        if completed.exit_code != 0:
            raise CampaignRunError(
                f"verifier replay exited with {completed.exit_code}; receipt: {receipt}"
            )
        return receipt


def campaign_state(run_dir: Path) -> dict[str, Any]:
    """Return the authoritative retained campaign state."""

    run = run_dir.expanduser().resolve()
    if journal_path(run).is_file():
        try:
            value = load_state_snapshot(run).state
        except JournalError as exc:
            raise CampaignRunError(f"cannot recover retained state: {exc}") from exc
    else:
        try:
            value = json.loads((run / "state.json").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise CampaignRunError(f"cannot read retained state: {exc}") from exc
    if not isinstance(value, dict) or value.get("schema_version") != 1:
        raise CampaignRunError("retained state has an unsupported schema")
    return value


def campaign_status(run_dir: Path) -> str:
    """Return the authoritative retained run status."""

    value = campaign_state(run_dir)
    status = value.get("status")
    allowed = {
        "running",
        "awaiting_approval",
        "complete",
        "incomplete",
        "failed",
        "stopped",
        "awaiting_sources",
        "awaiting_strategy",
        "replan_required",
        "restart_required",
    }
    if not isinstance(status, str) or status not in allowed:
        raise CampaignRunError("retained state has an invalid status")
    return status


def campaign_status_exit_code(status: str) -> int:
    """Map campaign state to the public run/resume/status exit contract."""

    if status == "complete":
        return 0
    if status in {"awaiting_approval", "awaiting_sources", "awaiting_strategy"}:
        return 3
    return 1


def refresh_campaign_evidence(run_dir: Path) -> None:
    """Re-index a run after a controller-owned durable receipt is added."""

    run_dir = run_dir.expanduser().resolve()
    status = campaign_status(run_dir)
    state = campaign_state(run_dir)
    campaign_id = state.get("campaign_id")
    if not isinstance(campaign_id, str) or not campaign_id:
        raise CampaignRunError("retained state has no campaign ID")
    _write_campaign_evidence(run_dir, campaign_id=campaign_id, status=status)


def campaign_resolved_for_run(run_dir: Path) -> Path:
    path = run_dir.expanduser().resolve() / "configuration" / "resolved.json"
    if not path.is_file():
        raise CampaignRunError("retained run has no resolved campaign")
    return path


def _write_campaign_evidence(run_dir: Path, *, campaign_id: str, status: str) -> None:
    evidence = run_dir / "evidence.json"
    artifacts = digest_tree(
        run_dir, exclude={"evidence.json", ".campaign.lock", "workspace"}
    )
    atomic_write_json(
        evidence,
        {
            "schema_version": 1,
            "campaign_id": campaign_id,
            "status": status,
            "generated_at": utc_now(),
            "artifacts": [artifact.to_dict() for artifact in artifacts],
        },
    )


def _verify_configuration_manifest(run_dir: Path) -> None:
    configuration = run_dir / "configuration"
    manifest_path = configuration / "manifest.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignRunError(f"cannot read configuration manifest: {exc}") from exc
    if not isinstance(manifest, dict) or not isinstance(
        manifest.get("artifacts"), list
    ):
        raise CampaignRunError("configuration manifest has invalid structure")
    observed = [
        artifact.to_dict()
        for artifact in digest_tree(configuration, exclude={"manifest.json"})
    ]
    if observed != manifest["artifacts"]:
        raise CampaignRunError("retained campaign configuration changed")


def _copy_input(item: CampaignInput, destination: Path) -> None:
    if item.source.is_symlink():
        raise ConfigurationError(f"copy input cannot be a symlink: {item.source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    if item.source.is_file():
        shutil.copy2(item.source, destination)
        return
    if not item.source.is_dir():
        raise ConfigurationError(f"unsupported campaign input: {item.source}")
    destination.mkdir()
    for current, directories, files in os.walk(
        item.source, topdown=True, followlinks=False
    ):
        current_path = Path(current)
        relative = current_path.relative_to(item.source)
        kept: list[str] = []
        for name in sorted(directories):
            child = current_path / name
            child_relative = (relative / name).as_posix()
            if path_is_excluded(child_relative, item.excludes):
                continue
            if child.is_symlink():
                raise ConfigurationError(f"copy input contains a symlink: {child}")
            kept.append(name)
            (destination / relative / name).mkdir(parents=True, exist_ok=True)
        directories[:] = kept
        for name in sorted(files):
            child = current_path / name
            child_relative = (relative / name).as_posix()
            if path_is_excluded(child_relative, item.excludes):
                continue
            if child.is_symlink():
                raise ConfigurationError(f"copy input contains a symlink: {child}")
            target = destination / relative / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(child, target)


def _copy_verified_artifact(item: CampaignInput, destination: Path) -> None:
    source = item.source
    if source.is_symlink() or not source.is_dir():
        raise CampaignRunError(
            f"verified artifact source is not a regular run directory: {source}"
        )
    if (
        item.artifact is None
        or item.expected_campaign_id is None
        or item.expected_run_id is None
        or item.evidence_sha256 is None
    ):
        raise CampaignRunError("verified artifact input has incomplete provenance pins")
    if source.name != item.expected_run_id:
        raise CampaignRunError(
            "verified artifact source directory does not match expected run ID"
        )

    state_path = _path_without_symlinks(source, PurePosixPath("state.json"))
    evidence_path = _path_without_symlinks(source, PurePosixPath("evidence.json"))
    if not state_path.is_file():
        raise CampaignRunError("verified artifact source has no regular state.json")
    if not evidence_path.is_file():
        raise CampaignRunError("verified artifact source has no regular evidence.json")
    try:
        observed_evidence_sha256 = digest_file(evidence_path, relative_to=source).sha256
    except OSError as exc:
        raise CampaignRunError(
            f"cannot hash verified artifact evidence: {exc}"
        ) from exc
    if observed_evidence_sha256 != item.evidence_sha256:
        raise CampaignRunError(
            "verified artifact evidence SHA-256 does not match provenance pin"
        )
    try:
        evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignRunError(
            f"cannot read verified artifact evidence: {exc}"
        ) from exc
    if not isinstance(evidence, dict) or evidence.get("status") != "complete":
        raise CampaignRunError("verified source evidence status is not complete")
    if evidence.get("campaign_id") != item.expected_campaign_id:
        raise CampaignRunError(
            "verified source evidence campaign ID does not match provenance pin"
        )
    if isinstance(evidence, dict) and isinstance(evidence.get("artifacts"), list):
        for raw in evidence["artifacts"]:
            if not isinstance(raw, dict) or not isinstance(raw.get("path"), str):
                continue
            relative = PurePosixPath(raw["path"])
            if relative.is_absolute() or any(
                part in ("", ".", "..") for part in relative.parts
            ):
                continue
            indexed_path = _path_without_symlinks(source, relative)
            if not indexed_path.is_file():
                raise CampaignRunError(
                    f"verified evidence artifact is not a regular file: {relative}"
                )
    try:
        verified = verify_evidence_index(source)
    except (OSError, TypeError, ValueError) as exc:
        raise CampaignRunError(f"cannot verify source evidence bundle: {exc}") from exc
    verified_paths = {artifact.path for artifact in verified}
    if "state.json" not in verified_paths:
        raise CampaignRunError("verified source evidence does not index state.json")
    try:
        state = json.loads(state_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignRunError(f"cannot read verified source state: {exc}") from exc
    if (
        not isinstance(state, dict)
        or state.get("schema_version") != 1
        or state.get("status") != "complete"
    ):
        raise CampaignRunError("verified artifact source state is not complete")
    if state.get("campaign_id") != item.expected_campaign_id:
        raise CampaignRunError(
            "verified source state campaign ID does not match provenance pin"
        )
    if state.get("run_id") != item.expected_run_id:
        raise CampaignRunError(
            "verified source state run ID does not match provenance pin"
        )

    prefix = PurePosixPath(item.artifact)
    selected = sorted(
        (
            artifact
            for artifact in verified
            if (relative := PurePosixPath(artifact.path)) == prefix
            or prefix in relative.parents
        ),
        key=lambda artifact: artifact.path,
    )
    if not selected:
        raise CampaignRunError(
            f"verified artifact has no indexed files under {item.artifact!r}"
        )
    selected_paths = [artifact.path for artifact in selected]
    if len(set(selected_paths)) != len(selected_paths):
        raise CampaignRunError("verified artifact evidence contains duplicate paths")

    artifact_source = _path_without_symlinks(source, prefix)
    exact = selected[0].path == item.artifact
    destination.parent.mkdir(parents=True, exist_ok=True)
    if exact:
        if len(selected) != 1 or not artifact_source.is_file():
            raise CampaignRunError(
                f"verified artifact prefix is not a regular file: {item.artifact}"
            )
        _copy_verified_file(artifact_source, destination, selected[0])
        return
    if not artifact_source.is_dir():
        raise CampaignRunError(
            f"verified artifact prefix is not a directory: {item.artifact}"
        )
    destination.mkdir()
    for artifact in selected:
        relative = PurePosixPath(artifact.path)
        child = _path_without_symlinks(source, relative)
        if not child.is_file():
            raise CampaignRunError(
                f"verified artifact is not a regular file: {artifact.path}"
            )
        target = destination.joinpath(*relative.relative_to(prefix).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        _copy_verified_file(child, target, artifact)


def _copy_verified_file(source: Path, destination: Path, artifact: Artifact) -> None:
    shutil.copy2(source, destination)
    observed = digest_file(destination, relative_to=destination.parent)
    if observed.sha256 != artifact.sha256 or observed.size != artifact.size:
        destination.unlink(missing_ok=True)
        raise CampaignRunError(
            f"verified artifact changed while being imported: {artifact.path}"
        )


def _path_without_symlinks(root: Path, relative: PurePosixPath) -> Path:
    current = root
    if current.is_symlink():
        raise CampaignRunError(f"verified artifact path has symlink ancestry: {root}")
    for part in relative.parts:
        current /= part
        if current.is_symlink():
            raise CampaignRunError(
                f"verified artifact path has symlink ancestry: {current}"
            )
    return current


def path_is_excluded(path: str, patterns: tuple[str, ...]) -> bool:
    for pattern in patterns:
        normalized = pattern.replace("\\", "/").removeprefix("./")
        if fnmatch.fnmatchcase(path, normalized):
            return True
        if normalized.endswith("/**"):
            prefix = normalized[:-3].rstrip("/")
            if path == prefix or path.startswith(f"{prefix}/"):
                return True
    return False


def _verify_input_manifest(run_dir: Path) -> None:
    try:
        manifest = json.loads(
            (run_dir / "input-manifest.json").read_text(encoding="utf-8")
        )
    except (OSError, json.JSONDecodeError) as exc:
        raise CampaignRunError(f"cannot read input manifest: {exc}") from exc
    if not isinstance(manifest, dict) or not isinstance(manifest.get("inputs"), list):
        raise CampaignRunError("input manifest has invalid structure")
    for item in manifest["inputs"]:
        if not isinstance(item, dict) or item.get("strategy") not in (
            "copy",
            "verified_artifact",
        ):
            continue
        target = item.get("target")
        expected = item.get("artifacts")
        if not isinstance(target, str) or not isinstance(expected, list):
            strategy = item.get("strategy")
            raise CampaignRunError(f"input manifest {strategy} record is malformed")
        path = run_dir / "input-snapshot" / target
        observed = (
            [artifact.to_dict() for artifact in digest_tree(path)]
            if path.is_dir()
            else [digest_file(path, relative_to=run_dir / "input-snapshot").to_dict()]
        )
        if observed != expected:
            raise CampaignRunError(f"input snapshot changed: {target}")
