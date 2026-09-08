"""Typed reusable execution features for declarative campaigns."""

from __future__ import annotations

import fnmatch
import json
import os
import re
import shutil
import stat
import tempfile
import time
from collections.abc import Mapping
from dataclasses import dataclass, replace
from decimal import Decimal, InvalidOperation
from pathlib import Path, PurePosixPath
from typing import Any, Protocol

from .artifacts import Artifact, atomic_write_json, atomic_write_text, digest_file
from .claims import ClaimProposalBundle, ClaimVerdictBundle, build_claim_ledger
from .command import run_captured_command
from .config import CampaignSpec, ConfigurationError, StageSpec
from .handoff import (
    ReviewDecision,
    digest_handoff,
    handoff_prompt_contract,
)
from .herdr import HerdrClient
from .lean import run_proof_gate, validate_substitution_value
from .models import ContinuationDecision
from .semantic import SemanticReview

_CLAIM_ID = re.compile(r"[a-z][a-z0-9_-]*")
_LEAN_SUBSTITUTION_NAME = re.compile(r"[a-z][a-z0-9_]*")
_LEAN_SUBSTITUTION_KINDS = frozenset({"decimal", "identifier", "string", "token"})
_LEAN_METADATA_FIELD = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


@dataclass(frozen=True, slots=True)
class FeatureResult:
    """Normalized outcome consumed by the stage engine."""

    status: str
    summary: str
    artifacts: tuple[Path, ...] = ()
    retry_targets: tuple[str, ...] = ()
    required_changes: tuple[str, ...] = ()

    @property
    def succeeded(self) -> bool:
        return self.status == "succeeded"


@dataclass(frozen=True, slots=True)
class FeatureContext:
    campaign: CampaignSpec
    stage: StageSpec
    config: object
    attempt: int
    run_dir: Path
    workspace: Path
    stage_dir: Path
    prompt_dir: Path
    log_dir: Path
    feedback: tuple[str, ...]
    dependency_reports: tuple[Path, ...]
    dependency_artifacts: Mapping[str, tuple[Path, ...]]
    herdr: HerdrClient | None
    pane_id: str | None
    omp: str
    lake: str
    python_executable: str


class CampaignFeature(Protocol):
    feature_id: str
    uses_agent: bool

    def validate(self, stage: StageSpec, campaign: CampaignSpec) -> object: ...

    def execute(self, context: FeatureContext) -> FeatureResult: ...


def _table(
    value: Mapping[str, Any],
    label: str,
    *,
    required: set[str],
    optional: set[str] | None = None,
) -> dict[str, Any]:
    result = dict(value)
    allowed = required | (optional or set())
    missing = required - result.keys()
    unknown = result.keys() - allowed
    if missing:
        raise ConfigurationError(f"{label} is missing keys: {sorted(missing)}")
    if unknown:
        raise ConfigurationError(f"{label} has unknown keys: {sorted(unknown)}")
    return result


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be a nonempty string")
    return value.strip()


def _optional_string(value: object, label: str) -> str | None:
    if value is None:
        return None
    return _string(value, label)


def _relative(value: object, label: str) -> str:
    result = _string(value, label).replace("\\", "/")
    path = PurePosixPath(result)
    if path.is_absolute() or any(part in ("", ".", "..") for part in path.parts):
        raise ConfigurationError(f"{label} must be a safe relative path")
    return result


def _strings(value: object, label: str, *, empty: bool = True) -> tuple[str, ...]:
    if not isinstance(value, (list, tuple)) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ConfigurationError(f"{label} must be an array of nonempty strings")
    result = tuple(item.strip() for item in value)
    if not empty and not result:
        raise ConfigurationError(f"{label} must not be empty")
    return result


def _integer(value: object, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ConfigurationError(f"{label} must be an integer")
    if not minimum <= value <= maximum:
        raise ConfigurationError(f"{label} must be between {minimum} and {maximum}")
    return value


def _boolean(value: object, label: str) -> bool:
    if not isinstance(value, bool):
        raise ConfigurationError(f"{label} must be a boolean")
    return value


def _decimal(value: object, label: str) -> str:
    result = _string(value, label)
    try:
        parsed = Decimal(result)
    except InvalidOperation as exc:
        raise ConfigurationError(f"{label} must be an exact finite decimal") from exc
    if not parsed.is_finite():
        raise ConfigurationError(f"{label} must be an exact finite decimal")
    return result


def _workspace_path(workspace: Path, relative: str) -> Path:
    path = (workspace / relative).resolve()
    try:
        path.relative_to(workspace.resolve())
    except ValueError as exc:
        raise ConfigurationError(
            f"workspace path escapes workspace: {relative}"
        ) from exc
    return path


def _workspace_handoff_path(workspace: Path, relative: str) -> Path:
    path = workspace / relative
    try:
        path.parent.resolve().relative_to(workspace.resolve())
    except ValueError as exc:
        raise ConfigurationError(
            f"workspace path escapes workspace: {relative}"
        ) from exc
    return path


def snapshot_workspace_inputs(
    workspace: Path, relative_paths: tuple[str, ...]
) -> tuple[Artifact, ...]:
    """Digest configured regular-file inputs without following symlinks."""
    root = workspace.resolve()
    artifacts: dict[str, Artifact] = {}
    for relative in relative_paths:
        raw = workspace / relative
        if _has_symlink_ancestor(raw, workspace):
            raise ConfigurationError(f"evidence input cannot be a symlink: {relative}")
        path = _workspace_path(workspace, relative)
        if path.is_file():
            artifact = digest_file(path, relative_to=root)
            artifacts[artifact.path] = artifact
            continue
        if not path.is_dir():
            raise ConfigurationError(f"evidence input does not exist: {relative}")
        for item in sorted(path.rglob("*")):
            if item.is_symlink():
                raise ConfigurationError(
                    f"evidence input tree contains a symlink: "
                    f"{item.relative_to(root).as_posix()}"
                )
            if item.is_file():
                artifact = digest_file(item, relative_to=root)
                artifacts[artifact.path] = artifact
    if relative_paths and not artifacts:
        raise ConfigurationError("evidence inputs contain no regular files")
    return tuple(artifacts[path] for path in sorted(artifacts))


def _verifier_source_snapshot(
    workspace: Path, campaign: CampaignSpec
) -> dict[str, dict[str, str | int]]:
    handoffs = {
        value
        for stage in campaign.stages
        if stage.feature == "agent"
        for value in (stage.config.get("handoff"),)
        if isinstance(value, str)
    }
    snapshot: dict[str, dict[str, str | int]] = {}
    root = workspace.resolve()
    cache_names = {".lake", "__pycache__", ".pytest_cache", ".ruff_cache"}
    for path in sorted(workspace.rglob("*")):
        relative = path.relative_to(workspace)
        relative_text = relative.as_posix()
        if (
            not relative.parts
            or relative.parts[0] == "agents"
            or relative_text in handoffs
            or cache_names.intersection(relative.parts)
            or _has_symlink_ancestor(path, workspace)
        ):
            continue
        if path.is_file():
            snapshot[relative_text] = digest_file(
                path.resolve(), relative_to=root
            ).to_dict()
    return snapshot


def _snapshot_changes(
    before: Mapping[str, object], after: Mapping[str, object]
) -> tuple[str, ...]:
    return tuple(
        path
        for path in sorted(before.keys() | after.keys())
        if before.get(path) != after.get(path)
    )


def _retained_dependency_snapshot(
    context: FeatureContext,
) -> dict[str, dict[str, str | int]]:
    paths = {path for paths in context.dependency_artifacts.values() for path in paths}
    paths.update(context.dependency_reports)
    for directory_name in ("configuration", "input-snapshot"):
        directory = context.run_dir / directory_name
        if directory.is_dir():
            paths.update(path for path in directory.rglob("*") if path.is_file())
    snapshot: dict[str, dict[str, str | int]] = {}
    for path in sorted(paths):
        if path.is_file() and not path.is_symlink():
            artifact = digest_file(path, relative_to=context.run_dir)
            snapshot[artifact.path] = artifact.to_dict()
    return snapshot


def _remove_prior_handoff(path: Path) -> None:
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        return
    except OSError as exc:
        raise ConfigurationError(
            f"cannot inspect prior handoff at {path}: {exc}"
        ) from exc
    if not (stat.S_ISREG(mode) or stat.S_ISLNK(mode)):
        raise ConfigurationError(
            f"handoff path is not a regular file or symlink: {path}"
        )
    try:
        path.unlink()
    except OSError as exc:
        raise ConfigurationError(
            f"cannot remove prior handoff at {path}: {exc}"
        ) from exc


@dataclass(frozen=True, slots=True)
class AgentConfig:
    instructions: Path
    tools: tuple[str, ...]
    category: str
    verifier_type: str | None
    omp: str | None
    model: str | None
    thinking: str | None
    max_time: int
    empty_output_retries: int
    handoff: str | None
    handoff_schema: str | None
    review: bool
    workspace_executables: bool
    novelty_gate: bool
    continuation_gate: bool


class AgentFeature:
    feature_id = "agent"
    uses_agent = True

    def validate(self, stage: StageSpec, campaign: CampaignSpec) -> AgentConfig:
        label = f"stage {stage.stage_id!r} agent config"
        table = _table(
            stage.config,
            label,
            required={"instructions", "tools"},
            optional={
                "category",
                "omp",
                "model",
                "thinking",
                "max_time",
                "empty_output_retries",
                "handoff",
                "handoff_schema",
                "review",
                "verifier_type",
                "workspace_executables",
                "novelty_gate",
                "continuation_gate",
            },
        )
        instructions = (
            campaign.manifest_path.parent
            / _string(table["instructions"], f"{label}.instructions")
        ).resolve()
        if not instructions.is_file():
            raise ConfigurationError(
                f"{label}.instructions does not exist: {instructions}"
            )
        tools = _strings(table["tools"], f"{label}.tools")
        handoff = (
            _relative(table["handoff"], f"{label}.handoff")
            if table.get("handoff") is not None
            else None
        )
        handoff_schema = _optional_string(
            table.get("handoff_schema"), f"{label}.handoff_schema"
        )
        if (handoff is None) != (handoff_schema is None):
            raise ConfigurationError(
                f"{label} requires handoff and handoff_schema together"
            )
        if handoff is not None:
            missing = {"read", "write"} - set(tools)
            if missing:
                raise ConfigurationError(
                    f"{label} handoff requires tools: {sorted(missing)}"
                )
        review = _boolean(table.get("review", False), f"{label}.review")
        continuation_gate = _boolean(
            table.get("continuation_gate", False), f"{label}.continuation_gate"
        )
        if review and handoff is not None:
            raise ConfigurationError(f"{label} cannot be both review and handoff")
        if continuation_gate and (review or handoff is not None):
            raise ConfigurationError(
                f"{label} continuation gate cannot be a review or handoff stage"
            )
        verifier_type = _optional_string(
            table.get("verifier_type"), f"{label}.verifier_type"
        )
        if verifier_type not in {
            None,
            "source",
            "symbolic",
            "numerical",
            "lean",
            "semantic",
            "boundary",
            "global",
            "adjudication",
        }:
            raise ConfigurationError(f"{label}.verifier_type is invalid")
        if verifier_type is not None and not (
            review or handoff_schema in {"claim-verdicts-v1", "semantic-review-v1"}
        ):
            raise ConfigurationError(
                f"{label}.verifier_type is only valid for verifier stages"
            )
        return AgentConfig(
            instructions=instructions,
            category=_string(table.get("category", stage.mode), f"{label}.category"),
            verifier_type=verifier_type,
            tools=tools,
            omp=_optional_string(table.get("omp"), f"{label}.omp"),
            model=_optional_string(table.get("model"), f"{label}.model"),
            thinking=_optional_string(table.get("thinking"), f"{label}.thinking"),
            max_time=_integer(
                table.get("max_time", 1200), f"{label}.max_time", 30, 86400
            ),
            empty_output_retries=_integer(
                table.get("empty_output_retries", 0),
                f"{label}.empty_output_retries",
                0,
                3,
            ),
            handoff=handoff,
            handoff_schema=handoff_schema,
            review=review,
            workspace_executables=_boolean(
                table.get("workspace_executables", True),
                f"{label}.workspace_executables",
            ),
            novelty_gate=_boolean(
                table.get("novelty_gate", False), f"{label}.novelty_gate"
            ),
            continuation_gate=continuation_gate,
        )

    def execute(self, context: FeatureContext) -> FeatureResult:
        config = context.config
        assert isinstance(config, AgentConfig)
        if context.herdr is None or context.pane_id is None:
            return FeatureResult("failed", "agent feature has no Herdr pane")
        if config.verifier_type is None:
            return self._execute_agent(context, config)
        return self._execute_verifier(context, config)

    def _execute_verifier(
        self, context: FeatureContext, config: AgentConfig
    ) -> FeatureResult:
        attempt_name = f"attempt-{context.attempt:02d}"
        temporary_root = Path(
            tempfile.mkdtemp(prefix=f"{attempt_name}-verifier-", dir=context.stage_dir)
        )
        isolated_workspace = temporary_root / "workspace"
        canonical_personal = _workspace_path(
            context.workspace,
            f"agents/{config.category}/{context.stage.stage_id}",
        )
        canonical_handoff = (
            _workspace_handoff_path(context.workspace, config.handoff)
            if config.handoff is not None
            else None
        )
        if canonical_handoff is not None:
            _remove_prior_handoff(canonical_handoff)
        canonical_before = _verifier_source_snapshot(
            context.workspace, context.campaign
        )
        try:
            shutil.copytree(
                context.workspace,
                isolated_workspace,
                symlinks=True,
                ignore=shutil.ignore_patterns(
                    ".lake", "__pycache__", ".pytest_cache", ".ruff_cache", "agents"
                ),
            )
            isolated_context = replace(context, workspace=isolated_workspace)
            before = _verifier_source_snapshot(isolated_workspace, context.campaign)
            retained_before = _retained_dependency_snapshot(context)
            result = self._execute_agent(isolated_context, config)
            after = _verifier_source_snapshot(isolated_workspace, context.campaign)
            retained_after = _retained_dependency_snapshot(context)
            canonical_after = _verifier_source_snapshot(
                context.workspace, context.campaign
            )
            changed = _snapshot_changes(before, after)
            retained_changed = _snapshot_changes(retained_before, retained_after)
            canonical_changed = _snapshot_changes(canonical_before, canonical_after)
            isolated_personal = _workspace_path(
                isolated_workspace,
                f"agents/{config.category}/{context.stage.stage_id}",
            )
            if isolated_personal.is_dir():
                shutil.copytree(
                    isolated_personal, canonical_personal, dirs_exist_ok=True
                )
            if changed or canonical_changed or retained_changed:
                mutation = context.stage_dir / f"{attempt_name}-mutation.json"
                atomic_write_json(
                    mutation,
                    {
                        "schema_version": 1,
                        "stage": context.stage.stage_id,
                        "attempt": context.attempt,
                        "changed_paths": list(changed),
                        "changed_canonical_workspace": list(canonical_changed),
                        "changed_retained_dependencies": list(retained_changed),
                    },
                )
                if canonical_changed:
                    summary = (
                        "verifier modified protected canonical workspace sources: "
                        + ", ".join(canonical_changed)
                    )
                elif changed:
                    summary = (
                        "verifier modified protected workspace sources: "
                        + ", ".join(changed)
                    )
                else:
                    summary = (
                        "verifier modified retained dependency evidence: "
                        + ", ".join(retained_changed)
                    )
                return FeatureResult(
                    "failed",
                    summary,
                    (*result.artifacts, mutation),
                )
            if result.succeeded and canonical_handoff is not None:
                assert config.handoff is not None
                isolated_handoff = _workspace_handoff_path(
                    isolated_workspace, config.handoff
                )
                canonical_handoff.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(isolated_handoff, canonical_handoff)
            return result
        finally:
            shutil.rmtree(temporary_root, ignore_errors=True)

    def _execute_agent(
        self, context: FeatureContext, config: AgentConfig
    ) -> FeatureResult:
        assert context.herdr is not None and context.pane_id is not None
        personal_dir = _workspace_path(
            context.workspace,
            f"agents/{config.category}/{context.stage.stage_id}",
        )
        personal_dir.mkdir(parents=True, exist_ok=True)
        attempt_name = f"attempt-{context.attempt:02d}"
        output = context.stage_dir / f"{attempt_name}.md"
        receipt = context.stage_dir / f"{attempt_name}.json"
        stdout_log = (
            context.log_dir / f"{context.stage.stage_id}-{attempt_name}.stdout.log"
        )
        stderr_log = (
            context.log_dir / f"{context.stage.stage_id}-{attempt_name}.stderr.log"
        )
        prompt = context.prompt_dir / f"{context.stage.stage_id}-{attempt_name}.md"
        prior_candidate = context.stage_dir / f"attempt-{context.attempt - 1:02d}.md"
        prior_output = (
            prior_candidate
            if context.attempt > 1 and prior_candidate.is_file()
            else None
        )
        handoff = (
            _workspace_handoff_path(context.workspace, config.handoff)
            if config.handoff is not None
            else None
        )
        source_inventory: Path | None = None
        source_digests: frozenset[str] | None = None
        if handoff is not None:
            try:
                _remove_prior_handoff(handoff)
            except ConfigurationError as exc:
                return FeatureResult(
                    "failed",
                    str(exc),
                )
            source_inventory = context.stage_dir / f"{attempt_name}-sources.json"
            source_digests = _write_source_inventory(context, handoff, source_inventory)
        atomic_write_text(
            prompt,
            _render_agent_prompt(
                context,
                config,
                handoff,
                source_inventory,
                personal_dir,
                prior_output,
            ),
        )
        request = context.stage_dir / f"{attempt_name}-request.json"
        payload: dict[str, object] = {
            "role_id": context.stage.stage_id,
            "attempt": context.attempt,
            "omp": config.omp or context.omp,
            "workspace": str(context.workspace),
            "run_dir": str(context.run_dir),
            "prompt": str(prompt),
            "output": str(output),
            "stdout_log": str(stdout_log),
            "stderr_log": str(stderr_log),
            "receipt": str(receipt),
            "tools": list(config.tools),
            "model": config.model,
            "thinking": config.thinking,
            "max_time": config.max_time,
            "empty_output_retries": config.empty_output_retries,
            "execution": context.campaign.execution.to_dict(),
            "sandbox_read_paths": [
                str(path)
                for path in sorted(
                    {
                        prompt,
                        *(() if source_inventory is None else (source_inventory,)),
                        *(() if prior_output is None else (prior_output,)),
                        *context.dependency_reports,
                        *(
                            path
                            for paths in context.dependency_artifacts.values()
                            for path in paths
                        ),
                    }
                )
            ],
            "workspace_executables": config.workspace_executables,
        }
        if handoff is not None:
            payload["handoff"] = str(handoff)
        atomic_write_json(request, payload)
        context.herdr.run_in_pane(
            context.pane_id,
            (
                context.python_executable,
                "-m",
                "agentic_lean_math_assistant.agent_runner",
                "--request",
                str(request),
            ),
        )
        runner = _wait_for_receipt(
            receipt,
            (config.max_time + 70) * (config.empty_output_retries + 1) + 20,
        )
        evidence = [
            path
            for path in (output, receipt, source_inventory)
            if path is not None and path.is_file()
        ]
        if runner.get("status") != "succeeded" or not output.is_file():
            error = str(
                runner.get("error") or "agent did not produce a successful report"
            )
            failure = context.stage_dir / f"{attempt_name}-failure.json"
            failure_value = {
                "schema_version": 1,
                "stage": context.stage.stage_id,
                "category": config.category,
                "attempt": context.attempt,
                "error": error,
                "receipt": receipt.name,
            }
            atomic_write_json(failure, failure_value)
            atomic_write_json(personal_dir / "failure.json", failure_value)
            evidence.append(failure)
            return FeatureResult("failed", error, tuple(evidence))
        artifacts: list[Path] = list(evidence)
        text = output.read_text(encoding="utf-8")
        if config.novelty_gate and context.attempt > 1 and prior_output is not None:
            try:
                novelty = _validate_retry_novelty(
                    text, context.stage_dir, context.attempt
                )
            except ConfigurationError as exc:
                return FeatureResult(
                    "failed",
                    f"retry novelty gate rejected output: {exc}",
                    tuple(artifacts),
                )
            novelty_path = context.stage_dir / f"{attempt_name}-novelty.json"
            atomic_write_json(novelty_path, novelty)
            artifacts.append(novelty_path)
        if handoff is not None:
            if not handoff.is_file() or handoff.is_symlink():
                return FeatureResult(
                    "failed",
                    f"agent did not produce required handoff: {config.handoff}",
                    tuple(artifacts),
                )
            assert config.handoff_schema is not None
            assert config.handoff is not None
            try:
                digest_handoff(
                    handoff,
                    config.handoff_schema,
                    source_digests=source_digests,
                )
            except ConfigurationError as exc:
                invalid = context.stage_dir / f"{attempt_name}-{handoff.name}"
                shutil.copy2(handoff, invalid)
                artifacts.append(invalid)
                return FeatureResult(
                    "failed",
                    f"invalid {config.handoff_schema} handoff: {exc}",
                    tuple(artifacts),
                )
            retained = context.stage_dir / Path(config.handoff).name
            shutil.copy2(handoff, retained)
            artifacts.append(retained)
        shutil.copy2(output, personal_dir / "report.md")
        if config.continuation_gate:
            try:
                continuation = ContinuationDecision.parse_text(text)
            except ConfigurationError as exc:
                return FeatureResult(
                    "failed",
                    str(exc),
                    tuple(artifacts),
                )
            decision_path = context.stage_dir / f"{attempt_name}-continuation.json"
            atomic_write_json(
                decision_path,
                {
                    "schema_version": 1,
                    "decision": continuation.decision,
                    "reason": continuation.reason,
                    "evidence": list(continuation.evidence),
                },
            )
            artifacts.append(decision_path)
            if continuation.decision == "stop":
                return FeatureResult(
                    "failed",
                    f"continuation gate stopped campaign: {continuation.reason}",
                    tuple(artifacts),
                )
            return FeatureResult("succeeded", continuation.reason, tuple(artifacts))
        if config.review:
            decision = ReviewDecision.parse(text)
            decision_path = context.stage_dir / f"{attempt_name}-decision.json"
            atomic_write_json(
                decision_path,
                {
                    "decision": decision.decision,
                    "reason": decision.reason,
                    "target_stages": list(decision.target_stages),
                    "required_changes": list(decision.required_changes),
                },
            )
            artifacts.append(decision_path)
            if decision.decision == "revise":
                return FeatureResult(
                    "revision_requested",
                    decision.reason,
                    tuple(artifacts),
                    decision.target_stages,
                    decision.required_changes,
                )
            return FeatureResult("succeeded", decision.reason, tuple(artifacts))
        return FeatureResult("succeeded", "agent report retained", tuple(artifacts))


def _write_source_inventory(
    context: FeatureContext, handoff: Path, destination: Path
) -> frozenset[str]:
    workspace_sources: list[dict[str, str | int]] = []
    dependency_reports: list[dict[str, str | int]] = []
    digests: set[str] = set()
    handoff_relative = handoff.relative_to(context.workspace).as_posix()
    for path in sorted(context.workspace.rglob("*")):
        if (
            not path.is_file()
            or _has_symlink_ancestor(path, context.workspace)
            or path.relative_to(context.workspace).as_posix() == handoff_relative
        ):
            continue
        artifact = digest_file(path, relative_to=context.workspace)
        workspace_sources.append(artifact.to_dict())
        digests.add(artifact.sha256)
    for path in context.dependency_reports:
        artifact = digest_file(path, relative_to=context.run_dir)
        dependency_reports.append(artifact.to_dict())
        digests.add(artifact.sha256)
    atomic_write_json(
        destination,
        {
            "schema_version": 1,
            "workspace_sources": workspace_sources,
            "dependency_reports": dependency_reports,
        },
    )
    return frozenset(digests)


def _has_symlink_ancestor(path: Path, root: Path) -> bool:
    current = path
    while current != root:
        if current.is_symlink():
            return True
        current = current.parent
    return False


def _validate_retry_novelty(
    text: str, stage_dir: Path, attempt: int
) -> dict[str, object]:
    prior = stage_dir / f"attempt-{attempt - 1:02d}.md"
    current = stage_dir / f"attempt-{attempt:02d}.md"
    if not prior.is_file():
        raise ConfigurationError("prior attempt report is unavailable")
    if text == prior.read_text(encoding="utf-8"):
        raise ConfigurationError(
            "report is byte-for-byte identical to the prior attempt"
        )
    section = re.search(
        r"(?ms)^## Retry novelty\s*$\n(?P<body>.*?)(?=^##\s|\Z)",
        text,
    )
    if section is None:
        raise ConfigurationError("missing '## Retry novelty' section")
    fields: dict[str, str] = {}
    expected = {
        "Prior limitation": "prior_limitation",
        "New method": "new_method",
        "Expected new evidence": "expected_new_evidence",
    }
    for line in section.group("body").splitlines():
        match = re.fullmatch(r"- ([^:]+):\s*(.+)", line.strip())
        if match is not None and match.group(1) in expected:
            fields[expected[match.group(1)]] = match.group(2).strip()
    missing = set(expected.values()) - fields.keys()
    if missing:
        raise ConfigurationError(
            f"retry novelty declaration is missing fields: {sorted(missing)}"
        )
    too_short = sorted(name for name, value in fields.items() if len(value) < 12)
    if too_short:
        raise ConfigurationError(
            f"retry novelty fields are not specific enough: {too_short}"
        )
    return {
        "schema_version": 1,
        "attempt": attempt,
        "prior_report": prior.name,
        "report_sha256": digest_file(current, relative_to=stage_dir).sha256,
        **fields,
    }


def _render_agent_prompt(
    context: FeatureContext,
    config: AgentConfig,
    handoff: Path | None,
    source_inventory: Path | None,
    personal_dir: Path,
    prior_output: Path | None,
) -> str:
    dependencies = (
        "\n".join(f"- `{path}`" for path in context.dependency_reports) or "- None"
    )
    feedback = "\n".join(f"- {item}" for item in context.feedback) or "- None"
    novelty_requirement = ""
    if config.novelty_gate and context.attempt > 1 and prior_output is not None:
        assert prior_output is not None
        novelty_requirement = f"""
## Mandatory retry novelty declaration
Read the prior report at `{prior_output}`. Do not repeat its method. Your report
must contain this exact section with specific, nonempty values:

## Retry novelty
- Prior limitation: what prevented the prior attempt from closing the obligation
- New method: the materially different method used in this attempt
- Expected new evidence: the concrete retained evidence this method should produce
"""
    continuation_requirement = ""
    if config.continuation_gate:
        continuation_requirement = """
## Required continuation decision
Return exactly one JSON object and no Markdown:
{"schema_version":1,"decision":"continue or stop","reason":"evidence-based reason","evidence":["retained path"]}
Use `continue` only when the pilot produced a materially new certified result,
counterexample region, rigorous reduction, new signed competitor, or precise
lemma reducing the remaining domain. A continue decision requires evidence.
"""
    handoff_requirement = ""
    if handoff is not None:
        assert config.handoff_schema is not None
        assert source_inventory is not None
        handoff_requirement = f"""
## Frozen workspace inventory
Read `{source_inventory}` before writing the handoff. It identifies retained
workspace files and exact SHA-256 digests. Cite only material you actually
inspected. For `research-v1`, every source record must use a digest from this
inventory. For every schema, inaccessible or unretained material is a limitation,
not evidence.

## Required typed handoff
Write `{handoff}` as strict JSON matching `{config.handoff_schema}` before returning.
The Markdown response does not substitute for this file.

{handoff_prompt_contract(config.handoff_schema)}
"""
    review_requirement = ""
    if config.review:
        review_requirement = """
## Required final response
Return exactly one JSON object with keys `decision`, `reason`, `target_stages`, and
`required_changes`. `decision` is `accept` or `revise`. No Markdown fence.
"""
    frozen_contract = ""
    if context.campaign.targets or context.campaign.obligations:
        target_lines = (
            "\n".join(
                f"- `{target.target_id}` ({target.kind}): statement={target.statement!r}; "
                f"scope={target.scope!r}"
                for target in context.campaign.targets
            )
            or "- None"
        )
        obligation_lines = (
            "\n".join(
                f"- `{item.obligation_id}`: {item.description} "
                f"(evidence stages: {', '.join(item.evidence_stages)})"
                for item in context.campaign.obligations
            )
            or "- None"
        )
        frozen_contract = f"""
## Frozen targets and coverage obligations
Target IDs do not define their own meaning. Any proposed target claim must match
the configured kind, statement, and scope exactly.

Targets:
{target_lines}

Coverage obligations:
{obligation_lines}
"""

    return f"""# Campaign assignment: {context.stage.title}

## Campaign directive
{context.campaign.instructions_path.read_text(encoding="utf-8").rstrip()}

## Stage directive
{config.instructions.read_text(encoding="utf-8").rstrip()}

## Execution contract
- Campaign: `{context.campaign.campaign_id}`
- Stage: `{context.stage.stage_id}`
- Category: `{config.category}`
- Attempt: `{context.attempt}`
- Verifier type: `{config.verifier_type or "not-applicable"}`
- Read the accepted prior knowledge in `{context.workspace / "knowledge" / config.category}` before starting when that directory exists.
- Your personal folder is `{personal_dir}`. Keep scratch work and useful generated artifacts there.
- Work only inside `{context.workspace}`.
- Do not redo retained work unless independent reproduction is part of the stage directive.
- Retained dependency reports:
{dependencies}
- Repair or review feedback:
{feedback}
- Report exact commands, evidence, failures, limitations, and unresolved obligations.
- Do not expose private chain-of-thought. Record concise mathematical reasoning, decisions, and evidence instead.
{handoff_requirement}{review_requirement}{novelty_requirement}{continuation_requirement}{frozen_contract}
"""


def _wait_for_receipt(path: Path, timeout: float) -> dict[str, Any]:
    deadline = time.monotonic() + timeout
    last: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if path.is_file():
            try:
                value = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                value = None
            if isinstance(value, dict):
                last = value
                if value.get("status") != "running":
                    return value
        time.sleep(0.25)
    return last or {"status": "timed_out", "error": "runner receipt timed out"}


@dataclass(frozen=True, slots=True)
class CommandConfig:
    argv: tuple[str, ...]
    cwd: str
    timeout: int
    replayable: bool
    environment: tuple[tuple[str, str], ...]
    covers_targets: tuple[str, ...]
    evidence_inputs: tuple[str, ...]
    workspace_executables: bool


class CommandFeature:
    feature_id = "command"
    uses_agent = False

    def validate(self, stage: StageSpec, campaign: CampaignSpec) -> CommandConfig:
        label = f"stage {stage.stage_id!r} command config"
        table = _table(
            stage.config,
            label,
            required={"argv"},
            optional={
                "cwd",
                "timeout",
                "environment",
                "covers_targets",
                "replayable",
                "evidence_inputs",
                "workspace_executables",
            },
        )
        environment_value = table.get("environment", {})
        if not isinstance(environment_value, dict) or not all(
            isinstance(key, str) and key and isinstance(value, str)
            for key, value in environment_value.items()
        ):
            raise ConfigurationError(f"{label}.environment must map strings to strings")
        inline_secrets = set(environment_value) & set(
            campaign.execution.secret_environment
        )
        if inline_secrets:
            raise ConfigurationError(
                f"{label}.environment must not retain declared secrets inline: "
                f"{sorted(inline_secrets)}"
            )
        cwd_value = _string(table.get("cwd", "."), f"{label}.cwd")
        cwd = "" if cwd_value == "." else _relative(cwd_value, f"{label}.cwd")
        covers_targets = _strings(
            table.get("covers_targets", []), f"{label}.covers_targets"
        )
        evidence_inputs = _strings(
            table.get("evidence_inputs", []), f"{label}.evidence_inputs"
        )
        if len(set(evidence_inputs)) != len(evidence_inputs):
            raise ConfigurationError(f"{label}.evidence_inputs must be unique")
        if covers_targets and not evidence_inputs:
            raise ConfigurationError(
                f"{label}.evidence_inputs is required when covers_targets is set"
            )
        declared_targets = {target.target_id for target in campaign.targets}
        unknown_targets = set(covers_targets) - declared_targets
        if unknown_targets:
            raise ConfigurationError(
                f"{label}.covers_targets are not declared campaign targets: "
                f"{sorted(unknown_targets)}"
            )
        return CommandConfig(
            argv=_strings(table["argv"], f"{label}.argv", empty=False),
            cwd=cwd,
            timeout=_integer(table.get("timeout", 900), f"{label}.timeout", 1, 86400),
            environment=tuple(sorted(environment_value.items())),
            replayable=_boolean(table.get("replayable", False), f"{label}.replayable"),
            covers_targets=covers_targets,
            evidence_inputs=evidence_inputs,
            workspace_executables=_boolean(
                table.get("workspace_executables", False),
                f"{label}.workspace_executables",
            ),
        )

    def execute(self, context: FeatureContext) -> FeatureResult:
        config = context.config
        assert isinstance(config, CommandConfig)
        cwd = _workspace_path(context.workspace, config.cwd)
        receipt = context.stage_dir / f"attempt-{context.attempt:02d}.json"
        started = time.monotonic()
        if not cwd.is_dir():
            return FeatureResult("failed", f"command cwd does not exist: {config.cwd}")
        try:
            evidence_inputs = snapshot_workspace_inputs(
                context.workspace, config.evidence_inputs
            )
        except ConfigurationError as exc:
            atomic_write_json(
                receipt,
                {
                    "schema_version": 2,
                    "argv": list(config.argv),
                    "cwd": str(cwd),
                    "duration_seconds": round(time.monotonic() - started, 3),
                    "error": str(exc),
                    "replayable": config.replayable,
                    "covers_targets": list(config.covers_targets),
                    "evidence_inputs": [],
                },
            )
            return FeatureResult("failed", str(exc), (receipt,))
        env = os.environ.copy()
        env.update(config.environment)
        completed = run_captured_command(
            config.argv,
            cwd=cwd,
            env=env,
            timeout=config.timeout,
            execution=context.campaign.execution,
            workspace=context.workspace,
            allow_workspace_executables=config.workspace_executables,
            run_dir=context.run_dir,
        )
        payload: dict[str, object] = {
            "schema_version": 2,
            "argv": list(config.argv),
            "cwd": str(cwd),
            "duration_seconds": round(time.monotonic() - started, 3),
            "error": completed.error,
            "replayable": config.replayable,
            "covers_targets": list(config.covers_targets),
            "evidence_inputs": [artifact.to_dict() for artifact in evidence_inputs],
        }
        if completed.exit_code is not None:
            payload.update(
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
        atomic_write_json(receipt, payload)
        if completed.error is not None:
            return FeatureResult(
                "failed", f"command could not run: {completed.error}", (receipt,)
            )
        if completed.exit_code != 0:
            return FeatureResult(
                "failed", f"command exited with {completed.exit_code}", (receipt,)
            )
        return FeatureResult("succeeded", "command passed", (receipt,))


@dataclass(frozen=True, slots=True)
class ScalarBound:
    key: str
    objective: str
    baseline: str
    limit: str

    def accepts(self, value: str) -> bool:
        candidate = Decimal(value)
        baseline = Decimal(self.baseline)
        limit = Decimal(self.limit)
        if self.objective == "minimize":
            return limit < candidate < baseline
        return baseline < candidate < limit


@dataclass(frozen=True, slots=True)
class LeanSubstitutionConfig:
    name: str
    source: str
    kind: str


@dataclass(frozen=True, slots=True)
class LeanContractConfig:
    project: str
    contract: str
    substitutions: tuple[LeanSubstitutionConfig, ...]
    metadata: str | None
    allowed_axioms: tuple[str, ...]
    lake: str | None
    timeout: int
    bound: ScalarBound | None
    repair_target: str | None


class LeanContractFeature:
    feature_id = "lean_contract"
    uses_agent = False

    def validate(self, stage: StageSpec, campaign: CampaignSpec) -> LeanContractConfig:
        label = f"stage {stage.stage_id!r} lean_contract config"
        table = _table(
            stage.config,
            label,
            required={"project", "contract", "allowed_axioms"},
            optional={
                "substitutions",
                "metadata",
                "lake",
                "timeout",
                "bound",
                "repair_target",
            },
        )
        substitutions_value = table.get("substitutions", {})
        if not isinstance(substitutions_value, dict):
            raise ConfigurationError(f"{label}.substitutions must be a table")
        substitutions: list[LeanSubstitutionConfig] = []
        for name, raw_spec in substitutions_value.items():
            substitution_label = f"{label}.substitutions[{name!r}]"
            if (
                not isinstance(name, str)
                or _LEAN_SUBSTITUTION_NAME.fullmatch(name) is None
            ):
                raise ConfigurationError(
                    f"{label}.substitutions names must match [a-z][a-z0-9_]*"
                )
            if isinstance(raw_spec, str):
                source = _string(raw_spec, substitution_label)
                kind = "token"
            elif isinstance(raw_spec, dict):
                substitution_table = _table(
                    raw_spec,
                    substitution_label,
                    required={"source", "kind"},
                )
                source = _string(
                    substitution_table["source"], f"{substitution_label}.source"
                )
                kind = _string(substitution_table["kind"], f"{substitution_label}.kind")
            else:
                raise ConfigurationError(
                    f"{substitution_label} must be a string or typed table"
                )
            if kind not in _LEAN_SUBSTITUTION_KINDS:
                raise ConfigurationError(
                    f"{substitution_label}.kind must be one of "
                    f"{sorted(_LEAN_SUBSTITUTION_KINDS)}"
                )
            if source.startswith("$metadata."):
                field = source.removeprefix("$metadata.")
                if _LEAN_METADATA_FIELD.fullmatch(field) is None:
                    raise ConfigurationError(
                        f"{substitution_label}.source has an invalid metadata field"
                    )
            else:
                try:
                    validate_substitution_value(name, source, kind)
                except ValueError as exc:
                    raise ConfigurationError(str(exc)) from exc
            substitutions.append(
                LeanSubstitutionConfig(name=name, source=source, kind=kind)
            )
        metadata = (
            _relative(table["metadata"], f"{label}.metadata")
            if table.get("metadata") is not None
            else None
        )
        if metadata is None and any(
            substitution.source.startswith("$metadata.")
            for substitution in substitutions
        ):
            raise ConfigurationError(
                f"{label}.metadata is required by metadata substitutions"
            )
        bound = _load_bound(table.get("bound"), label)
        repair_target = _optional_string(
            table.get("repair_target"), f"{label}.repair_target"
        )
        if repair_target is not None and repair_target not in campaign.by_id:
            raise ConfigurationError(
                f"{label}.repair_target is not a campaign stage: {repair_target}"
            )
        return LeanContractConfig(
            project=_relative(table["project"], f"{label}.project"),
            contract=_relative(table["contract"], f"{label}.contract"),
            substitutions=tuple(sorted(substitutions, key=lambda item: item.name)),
            metadata=metadata,
            allowed_axioms=_strings(table["allowed_axioms"], f"{label}.allowed_axioms"),
            lake=_optional_string(table.get("lake"), f"{label}.lake"),
            timeout=_integer(table.get("timeout", 900), f"{label}.timeout", 1, 86400),
            bound=bound,
            repair_target=repair_target,
        )

    def execute(self, context: FeatureContext) -> FeatureResult:
        config = context.config
        assert isinstance(config, LeanContractConfig)
        project = _workspace_path(context.workspace, config.project)
        contract = _workspace_path(context.run_dir / "input-snapshot", config.contract)
        if not project.is_dir():
            return FeatureResult("failed", f"Lean project does not exist: {project}")
        if not contract.is_file():
            return FeatureResult("failed", f"Lean contract does not exist: {contract}")
        try:
            substitutions = _resolve_substitutions(context.workspace, config)
        except (ConfigurationError, OSError, json.JSONDecodeError) as exc:
            return FeatureResult("failed", str(exc))
        if config.bound is not None:
            value = substitutions.get(config.bound.key)
            if value is None or not config.bound.accepts(value):
                return FeatureResult(
                    "failed",
                    f"candidate {value!r} violates the configured {config.bound.objective} bound",
                )
        result = run_proof_gate(
            project,
            contract_path=contract,
            substitutions=substitutions,
            allowed_axioms=config.allowed_axioms,
            lake=config.lake or context.lake,
            timeout=config.timeout,
            execution=context.campaign.execution,
            run_dir=context.run_dir,
        )
        receipt = context.stage_dir / f"attempt-{context.attempt:02d}.json"
        atomic_write_json(receipt, result.to_dict())
        if not result.passed:
            summary = "; ".join(result.errors) or "Lean contract failed"
            targets = (
                (config.repair_target,) if config.repair_target is not None else ()
            )
            return FeatureResult("failed", summary, (receipt,), targets)
        return FeatureResult("succeeded", "Lean contract passed", (receipt,))


def _load_bound(value: object, label: str) -> ScalarBound | None:
    if value is None:
        return None
    if not isinstance(value, dict):
        raise ConfigurationError(f"{label}.bound must be a table")
    table = _table(
        value,
        f"{label}.bound",
        required={"key", "objective", "baseline", "limit"},
    )
    objective = _string(table["objective"], f"{label}.bound.objective")
    if objective not in ("minimize", "maximize"):
        raise ConfigurationError(
            f"{label}.bound.objective must be minimize or maximize"
        )
    return ScalarBound(
        key=_string(table["key"], f"{label}.bound.key"),
        objective=objective,
        baseline=_decimal(table["baseline"], f"{label}.bound.baseline"),
        limit=_decimal(table["limit"], f"{label}.bound.limit"),
    )


def _resolve_substitutions(
    workspace: Path, config: LeanContractConfig
) -> dict[str, str]:
    metadata: object = None
    if config.metadata is not None:
        metadata_path = _workspace_path(workspace, config.metadata)
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        if not isinstance(metadata, dict):
            raise ConfigurationError("Lean contract metadata must be a JSON object")
    result: dict[str, str] = {}
    for substitution in config.substitutions:
        source = substitution.source
        if source.startswith("$metadata."):
            field = source.removeprefix("$metadata.")
            if not isinstance(metadata, dict) or not isinstance(
                metadata.get(field), str
            ):
                raise ConfigurationError(
                    f"Lean contract metadata field {field!r} must be a string"
                )
            value = metadata[field]
        else:
            value = source
        try:
            result[substitution.name] = validate_substitution_value(
                substitution.name, value, substitution.kind
            )
        except ValueError as exc:
            raise ConfigurationError(str(exc)) from exc
    return result


@dataclass(frozen=True, slots=True)
class ClaimLedgerConfig:
    proposals_stage: str
    proposals_handoff: str
    verifier_stages: tuple[str, ...]
    verifier_handoffs: tuple[tuple[str, str], ...]
    required_targets: tuple[str, ...]
    receipt_stages: tuple[str, ...]
    adjudicator_stage: str | None
    require_model_diversity: bool


class ClaimLedgerFeature:
    """Promote content-addressed claims only after independent stage verdicts."""

    feature_id = "claim_ledger"
    uses_agent = False

    def validate(self, stage: StageSpec, campaign: CampaignSpec) -> ClaimLedgerConfig:
        label = f"stage {stage.stage_id!r} claim_ledger config"
        table = _table(
            stage.config,
            label,
            required={"proposals_stage", "verifier_stages", "required_targets"},
            optional={
                "receipt_stages",
                "adjudicator_stage",
                "require_model_diversity",
            },
        )
        if not stage.required:
            raise ConfigurationError(f"{label} stage must be required")
        proposals_stage = _string(table["proposals_stage"], f"{label}.proposals_stage")
        verifier_stages = _strings(
            table["verifier_stages"], f"{label}.verifier_stages", empty=False
        )
        required_targets = _strings(
            table["required_targets"], f"{label}.required_targets", empty=False
        )
        receipt_stages = _strings(
            table.get("receipt_stages", []), f"{label}.receipt_stages"
        )
        adjudicator_stage = _optional_string(
            table.get("adjudicator_stage"), f"{label}.adjudicator_stage"
        )
        require_model_diversity = _boolean(
            table.get("require_model_diversity", False),
            f"{label}.require_model_diversity",
        )
        if len(set(verifier_stages)) != len(verifier_stages):
            raise ConfigurationError(f"{label}.verifier_stages must be unique")
        if len(set(required_targets)) != len(required_targets):
            raise ConfigurationError(f"{label}.required_targets must be unique")
        by_id = campaign.by_id
        referenced = {proposals_stage, *verifier_stages, *receipt_stages}
        if adjudicator_stage is not None:
            referenced.add(adjudicator_stage)
        unknown = referenced - by_id.keys()
        if unknown:
            raise ConfigurationError(
                f"{label} references unknown stages: {sorted(unknown)}"
            )
        invalid_targets = [
            target for target in required_targets if _CLAIM_ID.fullmatch(target) is None
        ]
        if invalid_targets:
            raise ConfigurationError(
                f"{label}.required_targets contain invalid IDs: {invalid_targets}"
            )
        declared_targets = {target.target_id: target for target in campaign.targets}
        for receipt_stage in receipt_stages:
            receipt = by_id[receipt_stage]
            if proposals_stage not in receipt.depends_on:
                raise ConfigurationError(
                    f"{label} receipt stage {receipt_stage!r} must directly depend "
                    f"on proposal stage {proposals_stage!r}"
                )
            if receipt.feature != "command":
                raise ConfigurationError(
                    f"{label} receipt stage {receipt_stage!r} must use command"
                )
            receipt_config = dict(receipt.config)
            if receipt_config.get("replayable") is not True:
                raise ConfigurationError(
                    f"{label} receipt stage {receipt_stage!r} must be replayable"
                )
        if declared_targets:
            undeclared = set(required_targets) - declared_targets.keys()
            if undeclared:
                raise ConfigurationError(
                    f"{label}.required_targets are not declared: {sorted(undeclared)}"
                )
        if proposals_stage in verifier_stages:
            raise ConfigurationError(
                f"{label}.proposals_stage cannot also be a verifier"
            )
        required_dependencies = {
            proposals_stage,
            *verifier_stages,
            *receipt_stages,
        }
        if adjudicator_stage is not None:
            required_dependencies.add(adjudicator_stage)
        missing_dependencies = required_dependencies - set(stage.depends_on)
        if missing_dependencies:
            raise ConfigurationError(
                f"{label} must directly depend on its producers: "
                f"{sorted(missing_dependencies)}"
            )
        proposals_handoff = _claim_stage_handoff(
            by_id[proposals_stage],
            "claim-proposals-v1",
            f"{label}.proposals_stage",
        )
        verifier_handoffs: list[tuple[str, str]] = []
        for verifier_stage in verifier_stages:
            verifier = by_id[verifier_stage]
            if proposals_stage not in verifier.depends_on:
                raise ConfigurationError(
                    f"{label} verifier {verifier_stage!r} must directly depend on "
                    f"proposal stage {proposals_stage!r}"
                )
            verifier_handoffs.append(
                (
                    verifier_stage,
                    _claim_stage_handoff(
                        verifier,
                        "claim-verdicts-v1",
                        f"{label}.verifier_stages[{verifier_stage!r}]",
                    ),
                )
            )
        verifier_models: set[tuple[object, object]] = set()
        for verifier_stage in verifier_stages:
            verifier_config = dict(by_id[verifier_stage].config)
            verifier_type = verifier_config.get("verifier_type")
            if campaign.targets and not isinstance(verifier_type, str):
                raise ConfigurationError(
                    f"{label} verifier {verifier_stage!r} must declare verifier_type"
                )
            verifier_models.add(
                (verifier_config.get("omp"), verifier_config.get("model"))
            )
            missing_receipts = set(receipt_stages) - set(
                by_id[verifier_stage].depends_on
            )
            if missing_receipts:
                raise ConfigurationError(
                    f"{label} verifier {verifier_stage!r} must directly depend on "
                    f"receipt stages: {sorted(missing_receipts)}"
                )
        if require_model_diversity and len(verifier_models) < 2:
            raise ConfigurationError(
                f"{label} requires at least two distinct verifier model lanes"
            )
        if adjudicator_stage is not None:
            adjudicator = by_id[adjudicator_stage]
            _claim_stage_handoff(
                adjudicator,
                "claim-verdicts-v1",
                f"{label}.adjudicator_stage",
            )
            if not set(verifier_stages) <= set(adjudicator.depends_on):
                raise ConfigurationError(
                    f"{label}.adjudicator_stage must depend on every verifier stage"
                )
        return ClaimLedgerConfig(
            proposals_stage=proposals_stage,
            proposals_handoff=proposals_handoff,
            verifier_stages=verifier_stages,
            verifier_handoffs=tuple(verifier_handoffs),
            required_targets=required_targets,
            receipt_stages=receipt_stages,
            adjudicator_stage=adjudicator_stage,
            require_model_diversity=require_model_diversity,
        )

    def execute(self, context: FeatureContext) -> FeatureResult:
        config = context.config
        assert isinstance(config, ClaimLedgerConfig)
        proposal_path = _dependency_handoff(
            context, config.proposals_stage, config.proposals_handoff
        )
        proposals = ClaimProposalBundle.load(proposal_path)
        verdicts: dict[str, ClaimVerdictBundle] = {}
        paths = {config.proposals_stage: proposal_path}
        for verifier_stage, handoff in config.verifier_handoffs:
            verdict_path = _dependency_handoff(context, verifier_stage, handoff)
            verdicts[verifier_stage] = ClaimVerdictBundle.load(verdict_path)
            paths[verifier_stage] = verdict_path
        adjudicator: ClaimVerdictBundle | None = None
        if config.adjudicator_stage is not None:
            adjudicator_stage = context.campaign.by_id[config.adjudicator_stage]
            campaign_stage = adjudicator_stage
            adjudicator_handoff = _claim_stage_handoff(
                campaign_stage,
                "claim-verdicts-v1",
                f"stage {context.stage.stage_id!r}.adjudicator_stage",
            )
            adjudicator_path = _dependency_handoff(
                context, adjudicator_stage.stage_id, adjudicator_handoff
            )
            adjudicator = ClaimVerdictBundle.load(adjudicator_path)
            paths[adjudicator_stage.stage_id] = adjudicator_path
        receipt_evidence: dict[str, dict[str, object]] = {}
        for receipt_stage in config.receipt_stages:
            receipts = [
                path
                for path in context.dependency_artifacts.get(receipt_stage, ())
                if path.suffix == ".json"
            ]
            if len(receipts) != 1:
                raise ConfigurationError(
                    f"receipt stage {receipt_stage!r} must retain exactly one JSON receipt"
                )
            receipt_value = json.loads(receipts[0].read_text(encoding="utf-8"))
            if (
                not isinstance(receipt_value, dict)
                or receipt_value.get("exit_code") != 0
            ):
                raise ConfigurationError(
                    f"receipt stage {receipt_stage!r} did not pass"
                )
            receipt_spec = context.campaign.by_id[receipt_stage]
            configured_inputs = _strings(
                receipt_spec.config.get("evidence_inputs", []),
                f"receipt stage {receipt_stage!r}.evidence_inputs",
            )
            observed_inputs = [
                artifact.to_dict()
                for artifact in snapshot_workspace_inputs(
                    context.workspace, configured_inputs
                )
            ]
            expected_inputs = receipt_value.get("evidence_inputs")
            if expected_inputs != observed_inputs:
                raise ConfigurationError(
                    f"receipt stage {receipt_stage!r} evidence input changed "
                    "after deterministic execution"
                )
            artifact = digest_file(receipts[0], relative_to=context.run_dir)
            receipt_evidence[receipt_stage] = {
                "path": artifact.path,
                "sha256": artifact.sha256,
                "covers_targets": receipt_value.get("covers_targets", []),
                "evidence_inputs": expected_inputs,
            }

        def receipt_covers(item: dict[str, object], target: str) -> bool:
            covered = item.get("covers_targets")
            return isinstance(covered, list) and target in covered

        uncovered = {
            target
            for target in config.required_targets
            if config.receipt_stages
            and not any(
                receipt_covers(item, target) for item in receipt_evidence.values()
            )
        }
        if uncovered:
            raise ConfigurationError(
                f"required targets lack a passing deterministic receipt: {sorted(uncovered)}"
            )
        evidence: dict[str, dict[str, str]] = {}
        for producer, path in paths.items():
            artifact = digest_file(path, relative_to=context.run_dir)
            evidence[producer] = {
                "path": artifact.path,
                "sha256": artifact.sha256,
            }
        ledger, closed = build_claim_ledger(
            campaign_id=context.campaign.campaign_id,
            proposals=proposals,
            verdicts=verdicts,
            required_targets=config.required_targets,
            evidence=evidence,
            declared_targets={
                target.target_id: {
                    "kind": target.kind,
                    "statement": target.statement,
                    "scope": target.scope,
                }
                for target in context.campaign.targets
            },
            receipt_evidence=receipt_evidence,
            adjudicator=adjudicator,
        )
        output = context.stage_dir / f"attempt-{context.attempt:02d}-claim-ledger.json"
        atomic_write_json(output, ledger)
        if closed:
            return FeatureResult(
                "succeeded",
                f"verified {len(config.required_targets)} required claim targets",
                (output,),
            )
        targets = ledger["required_targets"]
        assert isinstance(targets, list)
        unresolved = tuple(
            f"target {target['target_id']} is {target['status']}"
            for target in targets
            if isinstance(target, dict) and target.get("status") != "verified"
        )
        return FeatureResult(
            "failed",
            "required claim targets are not verified",
            (output,),
            (config.proposals_stage, *config.verifier_stages),
            unresolved,
        )


def _claim_stage_handoff(stage: StageSpec, schema: str, label: str) -> str:
    if stage.feature != "agent":
        raise ConfigurationError(f"{label} must use the agent feature")
    config = dict(stage.config)
    if config.get("handoff_schema") != schema:
        raise ConfigurationError(f"{label} must produce a {schema} handoff")
    if "handoff" not in config:
        raise ConfigurationError(f"{label} must configure a handoff path")
    if schema in {"claim-verdicts-v1", "semantic-review-v1"}:
        if config.get("category") != "verification":
            raise ConfigurationError(
                f"{label} must use the explicit verification category"
            )
        tools = config.get("tools")
        if not isinstance(tools, (list, tuple)) or not all(
            isinstance(tool, str) for tool in tools
        ):
            raise ConfigurationError(f"{label}.tools must be an array of strings")
        forbidden = set(tools) - {"read", "grep", "glob", "write"}
        if forbidden:
            raise ConfigurationError(
                f"{label} verifier has mutating or execution tools: {sorted(forbidden)}"
            )
    return _relative(config["handoff"], f"{label}.handoff")


def _dependency_handoff(context: FeatureContext, stage_id: str, handoff: str) -> Path:
    name = Path(handoff).name
    matches = tuple(
        path
        for path in context.dependency_artifacts.get(stage_id, ())
        if path.name == name and path.is_file()
    )
    if len(matches) != 1:
        raise ConfigurationError(
            f"dependency {stage_id!r} must retain exactly one {name!r} handoff"
        )
    return matches[0]


@dataclass(frozen=True, slots=True)
class SemanticContractConfig:
    lean_stage: str
    reviewer_stage: str
    reviewer_handoff: str
    declaration: str
    informal_statement: str
    repair_target: str | None


class SemanticContractFeature:
    """Require both Lean acceptance and an independent equivalence judgment."""

    feature_id = "semantic_contract"
    uses_agent = False

    def validate(
        self, stage: StageSpec, campaign: CampaignSpec
    ) -> SemanticContractConfig:
        label = f"stage {stage.stage_id!r} semantic_contract config"
        table = _table(
            stage.config,
            label,
            required={
                "lean_stage",
                "reviewer_stage",
                "declaration",
                "informal_statement",
            },
            optional={"repair_target"},
        )
        if not stage.required:
            raise ConfigurationError(f"{label} stage must be required")
        lean_stage = _string(table["lean_stage"], f"{label}.lean_stage")
        reviewer_stage = _string(table["reviewer_stage"], f"{label}.reviewer_stage")
        repair_target = _optional_string(
            table.get("repair_target"), f"{label}.repair_target"
        )
        by_id = campaign.by_id
        unknown = {lean_stage, reviewer_stage} - by_id.keys()
        if repair_target is not None:
            unknown.add(repair_target)
        if unknown:
            raise ConfigurationError(
                f"{label} references unknown stages: {sorted(unknown)}"
            )
        required_dependencies = {lean_stage, reviewer_stage}
        missing = required_dependencies - set(stage.depends_on)
        if missing:
            raise ConfigurationError(
                f"{label} must directly depend on: {sorted(missing)}"
            )
        if by_id[lean_stage].feature != "lean_contract":
            raise ConfigurationError(
                f"{label}.lean_stage must use the lean_contract feature"
            )
        reviewer = by_id[reviewer_stage]
        if lean_stage not in reviewer.depends_on:
            raise ConfigurationError(
                f"{label} reviewer must directly depend on Lean stage {lean_stage!r}"
            )
        handoff = _claim_stage_handoff(
            reviewer, "semantic-review-v1", f"{label}.reviewer_stage"
        )
        return SemanticContractConfig(
            lean_stage=lean_stage,
            reviewer_stage=reviewer_stage,
            reviewer_handoff=handoff,
            declaration=_string(table["declaration"], f"{label}.declaration"),
            informal_statement=_string(
                table["informal_statement"], f"{label}.informal_statement"
            ),
            repair_target=repair_target,
        )

    def execute(self, context: FeatureContext) -> FeatureResult:
        config = context.config
        assert isinstance(config, SemanticContractConfig)
        review_path = _dependency_handoff(
            context, config.reviewer_stage, config.reviewer_handoff
        )
        review = SemanticReview.load(review_path)
        if review.declaration != config.declaration:
            raise ConfigurationError(
                f"semantic review names declaration {review.declaration!r}, expected "
                f"{config.declaration!r}"
            )
        if review.informal_statement != config.informal_statement:
            raise ConfigurationError(
                "semantic review informal statement does not match the frozen "
                "semantic contract"
            )
        lean_path, lean_receipt = _lean_dependency_receipt(context, config.lean_stage)
        axiom_report, identity_issue = _matching_lean_axiom_report(
            lean_receipt, config.declaration
        )
        lean_passed = (
            lean_receipt.get("schema_version") == 2
            and lean_receipt.get("status") == "passed"
            and lean_receipt.get("errors") == []
            and lean_receipt.get("source_issues") == []
            and identity_issue is None
        )
        accepted = lean_passed and review.relation == "equivalent" and not review.issues
        review_artifact = digest_file(review_path, relative_to=context.run_dir)
        lean_artifact = digest_file(lean_path, relative_to=context.run_dir)
        receipt: dict[str, object] = {
            "schema_version": 1,
            "status": "accepted" if accepted else "rejected",
            "declaration": config.declaration,
            "informal_statement": config.informal_statement,
            "lean_gate": {
                "stage": config.lean_stage,
                "path": lean_artifact.path,
                "sha256": lean_artifact.sha256,
                "passed": lean_passed,
                "axiom_report": axiom_report,
                "identity_error": identity_issue,
            },
            "semantic_review": {
                "stage": config.reviewer_stage,
                "path": review_artifact.path,
                "sha256": review_artifact.sha256,
                **review.to_dict(),
            },
        }
        output = context.stage_dir / f"attempt-{context.attempt:02d}-semantic.json"
        atomic_write_json(output, receipt)
        if accepted:
            return FeatureResult(
                "succeeded",
                f"Lean declaration {config.declaration} is semantically equivalent",
                (output,),
            )
        retry_targets = (
            (config.repair_target, config.reviewer_stage)
            if config.repair_target is not None
            else (config.reviewer_stage,)
        )
        gate_issue = identity_issue
        if gate_issue is None and not lean_passed:
            gate_issue = "Lean contract did not pass"
        issues = ((gate_issue,) if gate_issue is not None else ()) + review.issues
        return FeatureResult(
            "failed",
            f"semantic equivalence rejected: {review.relation}",
            (output,),
            retry_targets,
            issues,
        )


def _matching_lean_axiom_report(
    receipt: dict[str, Any], declaration: str
) -> tuple[dict[str, object] | None, str | None]:
    reports = receipt.get("axiom_reports")
    if not isinstance(reports, list):
        return None, "Lean proof-gate receipt has malformed axiom reports"
    matches = [
        report
        for report in reports
        if isinstance(report, dict) and report.get("declaration") == declaration
    ]
    if len(matches) != 1:
        return (
            None,
            (
                "Lean proof-gate receipt must contain exactly one axiom report for "
                f"configured declaration {declaration!r}; found {len(matches)}"
            ),
        )
    axioms = matches[0].get("axioms")
    if not isinstance(axioms, list) or not all(
        isinstance(axiom, str) for axiom in axioms
    ):
        return (
            None,
            "Lean proof-gate receipt has malformed axioms for configured declaration",
        )
    return {"declaration": declaration, "axioms": list(axioms)}, None


def _lean_dependency_receipt(
    context: FeatureContext, stage_id: str
) -> tuple[Path, dict[str, Any]]:
    matches: list[tuple[Path, dict[str, Any]]] = []
    for path in context.dependency_artifacts.get(stage_id, ()):
        if path.suffix != ".json":
            continue
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if (
            isinstance(value, dict)
            and value.get("schema_version") == 2
            and "axiom_reports" in value
        ):
            matches.append((path, value))
    if len(matches) != 1:
        raise ConfigurationError(
            f"Lean dependency {stage_id!r} must retain exactly one proof-gate receipt"
        )
    return matches[0]


@dataclass(frozen=True, slots=True)
class PromotionConfig:
    source: str
    destination: str
    excludes: tuple[str, ...]


class PromotionFeature:
    feature_id = "artifact_promote"
    uses_agent = False

    def validate(self, stage: StageSpec, campaign: CampaignSpec) -> PromotionConfig:
        del campaign
        label = f"stage {stage.stage_id!r} artifact_promote config"
        table = _table(
            stage.config,
            label,
            required={"source", "destination"},
            optional={"excludes"},
        )
        return PromotionConfig(
            source=_relative(table["source"], f"{label}.source"),
            destination=_relative(table["destination"], f"{label}.destination"),
            excludes=_strings(table.get("excludes", []), f"{label}.excludes"),
        )

    def execute(self, context: FeatureContext) -> FeatureResult:
        config = context.config
        assert isinstance(config, PromotionConfig)
        source = _workspace_path(context.workspace, config.source)
        destination = (context.run_dir / config.destination).resolve()
        try:
            destination.relative_to(context.run_dir.resolve())
        except ValueError:
            return FeatureResult(
                "failed", "promotion destination escapes run directory"
            )
        if not source.exists() or source.is_symlink():
            return FeatureResult(
                "failed", f"promotion source is missing or linked: {source}"
            )
        if destination.exists():
            return FeatureResult(
                "failed", f"promotion destination exists: {destination}"
            )
        destination.parent.mkdir(parents=True, exist_ok=True)
        artifacts: tuple[Path, ...]
        if source.is_file():
            descriptor, temporary = tempfile.mkstemp(
                prefix=f".{destination.name}.", dir=destination.parent
            )
            os.close(descriptor)
            staging = Path(temporary)
            try:
                shutil.copy2(source, staging)
                staging.replace(destination)
            except Exception:
                staging.unlink(missing_ok=True)
                raise
            artifacts = (destination,)
        else:
            staging = Path(
                tempfile.mkdtemp(prefix=f".{destination.name}.", dir=destination.parent)
            )
            try:
                _copy_promoted_tree(source, staging, config.excludes)
                staging.replace(destination)
            except Exception:
                shutil.rmtree(staging, ignore_errors=True)
                raise
            artifacts = tuple(path for path in destination.rglob("*") if path.is_file())
        receipt = context.stage_dir / f"attempt-{context.attempt:02d}.json"
        atomic_write_json(
            receipt,
            {
                "schema_version": 1,
                "source": config.source,
                "destination": config.destination,
                "files": [
                    path.relative_to(context.run_dir).as_posix() for path in artifacts
                ],
            },
        )
        return FeatureResult(
            "succeeded", f"promoted {len(artifacts)} artifacts", (*artifacts, receipt)
        )


def _copy_promoted_tree(
    source: Path, destination: Path, excludes: tuple[str, ...]
) -> None:
    for current, directories, files in os.walk(source, topdown=True, followlinks=False):
        current_path = Path(current)
        relative = current_path.relative_to(source)
        kept: list[str] = []
        for name in sorted(directories):
            child = current_path / name
            child_relative = (relative / name).as_posix()
            if _matches(child_relative, excludes):
                continue
            if child.is_symlink():
                raise ConfigurationError(f"promotion cannot retain a symlink: {child}")
            kept.append(name)
            (destination / relative / name).mkdir(parents=True, exist_ok=True)
        directories[:] = kept
        for name in sorted(files):
            child = current_path / name
            child_relative = (relative / name).as_posix()
            if _matches(child_relative, excludes):
                continue
            if child.is_symlink():
                raise ConfigurationError(f"promotion cannot retain a symlink: {child}")
            target = destination / relative / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(child, target)


def _matches(path: str, patterns: tuple[str, ...]) -> bool:
    for pattern in patterns:
        if fnmatch.fnmatchcase(path, pattern):
            return True
        if pattern.endswith("/**") and path == pattern.removesuffix("/**"):
            return True
    return False


class FeatureRegistry:
    """Closed, typed registry; campaign data selects features by stable ID."""

    def __init__(self, features: tuple[CampaignFeature, ...] | None = None) -> None:
        registered = features or (
            AgentFeature(),
            CommandFeature(),
            LeanContractFeature(),
            ClaimLedgerFeature(),
            SemanticContractFeature(),
            PromotionFeature(),
        )
        self._features = {feature.feature_id: feature for feature in registered}
        if len(self._features) != len(registered):
            raise ValueError("campaign feature IDs must be unique")

    @property
    def feature_ids(self) -> tuple[str, ...]:
        return tuple(sorted(self._features))

    def feature(self, feature_id: str) -> CampaignFeature:
        try:
            return self._features[feature_id]
        except KeyError as exc:
            raise ConfigurationError(f"unknown campaign feature: {feature_id}") from exc

    def validate(self, campaign: CampaignSpec) -> dict[str, object]:
        return {
            stage.stage_id: self.feature(stage.feature).validate(stage, campaign)
            for stage in campaign.stages
        }
