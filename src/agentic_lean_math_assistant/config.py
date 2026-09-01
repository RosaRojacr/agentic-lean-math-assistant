"""Strict declarative campaigns shared by research and build modes."""

from __future__ import annotations

import json
import os
import re
import tomllib
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from types import MappingProxyType
from typing import Any, Literal, Self


class ConfigurationError(ValueError):
    """A campaign or project configuration is malformed or inconsistent."""


CampaignMode = Literal["research", "build"]
ApprovalPolicy = Literal["required", "automatic"]
FailurePolicy = Literal["continue", "abort", "replan", "restart"]
InputStrategy = Literal["copy", "symlink", "verified_artifact"]
_ID = re.compile(r"[a-z][a-z0-9_-]*")
_SAFE_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_-]*")
_SHA256 = re.compile(r"[0-9a-f]{64}")
_ENV_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_DEFAULT_ENVIRONMENT_ALLOW = (
    "HOME",
    "LANG",
    "LC_ALL",
    "PATH",
    "SSL_CERT_DIR",
    "SSL_CERT_FILE",
    "TZ",
    "XDG_CONFIG_HOME",
)


def _table(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ConfigurationError(f"{label} must be a TOML table")
    return value


def _keys(
    value: object,
    label: str,
    *,
    required: set[str],
    optional: set[str] | None = None,
) -> dict[str, Any]:
    table = _table(value, label)
    allowed = required | (optional or set())
    missing = required - table.keys()
    unknown = table.keys() - allowed
    if missing:
        raise ConfigurationError(f"{label} is missing keys: {sorted(missing)}")
    if unknown:
        raise ConfigurationError(f"{label} has unknown keys: {sorted(unknown)}")
    return table


def _string(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be a nonempty string")
    return value.strip()


def _identifier(value: object, label: str) -> str:
    result = _string(value, label)
    if _ID.fullmatch(result) is None:
        raise ConfigurationError(f"{label} must match {_ID.pattern!r}")
    if len(result) > 64:
        raise ConfigurationError(f"{label} must not exceed 64 characters")
    return result


def _safe_identifier(value: object, label: str) -> str:
    result = _string(value, label)
    if _SAFE_ID.fullmatch(result) is None:
        raise ConfigurationError(f"{label} must match {_SAFE_ID.pattern!r}")
    if len(result) > 64:
        raise ConfigurationError(f"{label} must not exceed 64 characters")
    return result


def _sha256(value: object, label: str) -> str:
    result = _string(value, label)
    if _SHA256.fullmatch(result) is None:
        raise ConfigurationError(f"{label} must be a lowercase SHA-256 digest")
    return result


def _relative(value: object, label: str) -> str:
    result = _string(value, label).replace("\\", "/")
    path = PurePosixPath(result)
    if path.is_absolute() or any(part in ("", ".", "..") for part in path.parts):
        raise ConfigurationError(f"{label} must be a safe relative path")
    return result


def _strings(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ConfigurationError(f"{label} must be an array of nonempty strings")
    return tuple(item.strip() for item in value)


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


def _read_toml(path: Path) -> dict[str, Any]:
    try:
        value = tomllib.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ConfigurationError(f"cannot read campaign manifest: {exc}") from exc
    except tomllib.TOMLDecodeError as exc:
        raise ConfigurationError(f"campaign manifest is invalid TOML: {exc}") from exc
    return _table(value, "campaign manifest")


def _resolve_file(base: Path, value: object, label: str) -> Path:
    path = (base / _relative(value, label)).resolve()
    if not path.is_file():
        raise ConfigurationError(f"{label} does not exist: {path}")
    return path


@dataclass(frozen=True, slots=True)
class CampaignInput:
    """One immutable campaign input copied, linked, or verified into the workspace."""

    source: Path
    target: str
    strategy: InputStrategy
    excludes: tuple[str, ...]
    artifact: str | None = None
    expected_campaign_id: str | None = None
    expected_run_id: str | None = None
    evidence_sha256: str | None = None

    @classmethod
    def from_table(cls, value: object, index: int, base: Path) -> Self:
        label = f"inputs[{index}]"
        table = _keys(
            value,
            label,
            required={"source", "target"},
            optional={
                "strategy",
                "excludes",
                "artifact",
                "expected_campaign_id",
                "expected_run_id",
                "evidence_sha256",
            },
        )
        source = (base / _string(table["source"], f"{label}.source")).resolve()
        if not source.exists():
            raise ConfigurationError(f"{label}.source does not exist: {source}")
        strategy = _string(table.get("strategy", "copy"), f"{label}.strategy")
        if strategy not in ("copy", "symlink", "verified_artifact"):
            raise ConfigurationError(
                f"{label}.strategy must be copy, symlink, or verified_artifact"
            )
        artifact: str | None = None
        expected_campaign_id: str | None = None
        expected_run_id: str | None = None
        evidence_sha256: str | None = None
        provenance_keys = {
            "expected_campaign_id",
            "expected_run_id",
            "evidence_sha256",
        }
        if strategy == "verified_artifact":
            if "artifact" not in table:
                raise ConfigurationError(
                    f"{label}.artifact is required for a verified_artifact input"
                )
            if "excludes" in table:
                raise ConfigurationError(
                    f"{label}.excludes is invalid for a verified_artifact input"
                )
            artifact = _relative(table["artifact"], f"{label}.artifact")
            missing_provenance = provenance_keys - table.keys()
            if missing_provenance:
                raise ConfigurationError(
                    f"{label} is missing verified provenance keys: "
                    f"{sorted(missing_provenance)}"
                )
            expected_campaign_id = _identifier(
                table["expected_campaign_id"], f"{label}.expected_campaign_id"
            )
            expected_run_id = _safe_identifier(
                table["expected_run_id"], f"{label}.expected_run_id"
            )
            evidence_sha256 = _sha256(
                table["evidence_sha256"], f"{label}.evidence_sha256"
            )
        else:
            if "artifact" in table:
                raise ConfigurationError(
                    f"{label}.artifact is only valid for a verified_artifact input"
                )
            invalid_provenance = provenance_keys & table.keys()
            if invalid_provenance:
                raise ConfigurationError(
                    f"{label} provenance pins are only valid for a verified_artifact "
                    "input"
                )
        if strategy == "symlink" and table.get("excludes"):
            raise ConfigurationError(f"{label}.excludes is invalid for a symlink input")
        return cls(
            source=source,
            target=_relative(table["target"], f"{label}.target"),
            strategy=strategy,  # type: ignore[arg-type]
            excludes=_strings(table.get("excludes", []), f"{label}.excludes"),
            artifact=artifact,
            expected_campaign_id=expected_campaign_id,
            expected_run_id=expected_run_id,
            evidence_sha256=evidence_sha256,
        )


@dataclass(frozen=True, slots=True)
class StageSpec:
    """One feature invocation in the campaign DAG."""

    stage_id: str
    title: str
    mode: CampaignMode
    feature: str
    depends_on: tuple[str, ...]
    required: bool
    max_attempts: int
    failure_policy: FailurePolicy
    config: Mapping[str, Any]

    @classmethod
    def from_table(cls, value: object, index: int) -> Self:
        label = f"stages[{index}]"
        table = _keys(
            value,
            label,
            required={"id", "title", "mode", "feature", "depends_on"},
            optional={"required", "max_attempts", "failure_policy", "config"},
        )
        mode = _string(table["mode"], f"{label}.mode")
        if mode not in ("research", "build"):
            raise ConfigurationError(f"{label}.mode must be research or build")
        config = _table(table.get("config", {}), f"{label}.config")
        failure_policy = _string(
            table.get(
                "failure_policy", "abort" if table.get("required", True) else "continue"
            ),
            f"{label}.failure_policy",
        )
        if failure_policy not in ("continue", "abort", "replan", "restart"):
            raise ConfigurationError(f"{label}.failure_policy is invalid")
        required = _boolean(table.get("required", True), f"{label}.required")
        if failure_policy == "continue" and required:
            raise ConfigurationError(
                f"{label}.failure_policy continue requires required=false"
            )
        if failure_policy != "continue" and not required:
            raise ConfigurationError(
                f"{label}.failure_policy {failure_policy} requires required=true"
            )
        return cls(
            stage_id=_identifier(table["id"], f"{label}.id"),
            title=_string(table["title"], f"{label}.title"),
            mode=mode,  # type: ignore[arg-type]
            feature=_identifier(table["feature"], f"{label}.feature"),
            depends_on=_strings(table["depends_on"], f"{label}.depends_on"),
            required=required,
            max_attempts=_integer(
                table.get("max_attempts", 1), f"{label}.max_attempts", 1, 10
            ),
            failure_policy=failure_policy,  # type: ignore[arg-type]
            config=MappingProxyType(config.copy()),
        )


@dataclass(frozen=True, slots=True)
class HandoffSpec:
    """Typed trust boundary between research and build stages."""

    producer: str
    artifact: str
    schema: str
    approval: ApprovalPolicy

    @classmethod
    def from_table(cls, value: object) -> Self:
        table = _keys(
            value,
            "handoff",
            required={"producer", "artifact", "schema", "approval"},
        )
        approval = _string(table["approval"], "handoff.approval")
        if approval not in ("required", "automatic"):
            raise ConfigurationError("handoff.approval must be required or automatic")
        return cls(
            producer=_identifier(table["producer"], "handoff.producer"),
            artifact=_relative(table["artifact"], "handoff.artifact"),
            schema=_identifier(table["schema"], "handoff.schema"),
            approval=approval,  # type: ignore[arg-type]
        )


@dataclass(frozen=True, slots=True)
class PublishSpec:
    """Explicit allowlist and filesystem boundary for publishing one run artifact."""

    source: str
    root: Path
    destination: Path
    preserve: tuple[str, ...]

    @classmethod
    def from_table(cls, value: object, base: Path) -> Self:
        table = _keys(
            value,
            "publish",
            required={"source", "root", "destination"},
            optional={"preserve"},
        )
        root = _manifest_relative_absolute(table["root"], base, "publish.root")
        destination = _manifest_relative_absolute(
            table["destination"], base, "publish.destination"
        )
        _validate_publish_boundary(root, destination, "publish.destination")
        return cls(
            source=_relative(table["source"], "publish.source"),
            root=root,
            destination=destination,
            preserve=_preserve_names(table.get("preserve", []), "publish.preserve"),
        )

    @classmethod
    def from_resolved_table(cls, value: object) -> Self:
        table = _keys(
            value,
            "resolved campaign.publish",
            required={"source", "root", "destination", "preserve"},
        )
        root = Path(_string(table["root"], "resolved campaign.publish.root"))
        destination = Path(
            _string(table["destination"], "resolved campaign.publish.destination")
        )
        if not root.is_absolute():
            raise ConfigurationError("resolved campaign.publish.root must be absolute")
        if not destination.is_absolute():
            raise ConfigurationError(
                "resolved campaign.publish.destination must be absolute"
            )
        _validate_publish_boundary(
            root, destination, "resolved campaign.publish.destination"
        )
        return cls(
            source=_relative(table["source"], "resolved campaign.publish.source"),
            root=root,
            destination=destination,
            preserve=_preserve_names(
                table["preserve"], "resolved campaign.publish.preserve"
            ),
        )


def _manifest_relative_absolute(value: object, base: Path, label: str) -> Path:
    raw = _string(value, label).replace("\\", "/")
    if PurePosixPath(raw).is_absolute():
        raise ConfigurationError(f"{label} must be relative to the campaign manifest")
    return Path(os.path.abspath(base / raw))


def _validate_publish_boundary(root: Path, destination: Path, label: str) -> None:
    try:
        relative = destination.relative_to(root)
    except ValueError as exc:
        raise ConfigurationError(
            f"{label} must be strictly below publish.root"
        ) from exc
    if not relative.parts:
        raise ConfigurationError(f"{label} must be strictly below publish.root")


def _preserve_names(value: object, label: str) -> tuple[str, ...]:
    names = _strings(value, label)
    for name in names:
        normalized = name.replace("\\", "/")
        path = PurePosixPath(normalized)
        if (
            path.is_absolute()
            or len(path.parts) != 1
            or path.parts[0] in ("", ".", "..")
            or normalized != path.as_posix()
        ):
            raise ConfigurationError(
                f"{label} entries must be exact safe top-level names"
            )
    if len(set(names)) != len(names):
        raise ConfigurationError(f"{label} entries must be unique")
    return names


@dataclass(frozen=True, slots=True)
class ExecutionSpec:
    """OS-enforced resource, filesystem, network, and environment policy."""

    sandbox: bool
    network: bool
    memory_max_mb: int
    cpu_quota_percent: int
    tasks_max: int
    file_size_max_mb: int
    workspace_max_mb: int
    allowed_executable_paths: tuple[Path, ...]
    environment_allow: tuple[str, ...]
    secret_environment: tuple[str, ...]

    @classmethod
    def from_table(
        cls,
        value: object | None,
        base: Path,
        *,
        resolved: bool = False,
    ) -> Self:
        label = "resolved campaign.execution" if resolved else "execution"
        table = _keys(
            value or {},
            label,
            required=set(),
            optional={
                "sandbox",
                "network",
                "memory_max_mb",
                "cpu_quota_percent",
                "tasks_max",
                "file_size_max_mb",
                "workspace_max_mb",
                "allowed_executable_paths",
                "environment_allow",
                "secret_environment",
            },
        )
        raw_paths = _strings(
            table.get("allowed_executable_paths", []),
            f"{label}.allowed_executable_paths",
        )
        paths: list[Path] = []
        for index, raw in enumerate(raw_paths):
            path = Path(raw).expanduser()
            if resolved and not path.is_absolute():
                raise ConfigurationError(
                    f"{label}.allowed_executable_paths[{index}] must be absolute"
                )
            if not path.is_absolute():
                path = base / path
            path = path.resolve()
            if not path.exists():
                raise ConfigurationError(
                    f"{label}.allowed_executable_paths[{index}] does not exist: {path}"
                )
            paths.append(path)
        if len(set(paths)) != len(paths):
            raise ConfigurationError(f"{label}.allowed_executable_paths must be unique")
        environment_allow = _environment_names(
            table.get("environment_allow", list(_DEFAULT_ENVIRONMENT_ALLOW)),
            f"{label}.environment_allow",
        )
        secret_environment = _environment_names(
            table.get("secret_environment", []),
            f"{label}.secret_environment",
        )
        sandbox = _boolean(table.get("sandbox", True), f"{label}.sandbox")
        unknown_secrets = set(secret_environment) - set(environment_allow)
        if unknown_secrets:
            raise ConfigurationError(
                f"{label}.secret_environment must also be allowed: "
                f"{sorted(unknown_secrets)}"
            )
        if sandbox and secret_environment:
            raise ConfigurationError(
                f"{label}.secret_environment requires sandbox=false because "
                "untrusted stages can transform or encode credentials in retained "
                "artifacts"
            )
        return cls(
            sandbox=sandbox,
            network=_boolean(table.get("network", False), f"{label}.network"),
            memory_max_mb=_integer(
                table.get("memory_max_mb", 4096),
                f"{label}.memory_max_mb",
                64,
                1_048_576,
            ),
            cpu_quota_percent=_integer(
                table.get("cpu_quota_percent", 800),
                f"{label}.cpu_quota_percent",
                1,
                100_000,
            ),
            tasks_max=_integer(
                table.get("tasks_max", 256),
                f"{label}.tasks_max",
                1,
                1_048_576,
            ),
            file_size_max_mb=_integer(
                table.get("file_size_max_mb", 1024),
                f"{label}.file_size_max_mb",
                1,
                1_048_576,
            ),
            workspace_max_mb=_integer(
                table.get("workspace_max_mb", 8192),
                f"{label}.workspace_max_mb",
                1,
                1_048_576,
            ),
            allowed_executable_paths=tuple(paths),
            environment_allow=environment_allow,
            secret_environment=secret_environment,
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "sandbox": self.sandbox,
            "network": self.network,
            "memory_max_mb": self.memory_max_mb,
            "cpu_quota_percent": self.cpu_quota_percent,
            "tasks_max": self.tasks_max,
            "file_size_max_mb": self.file_size_max_mb,
            "workspace_max_mb": self.workspace_max_mb,
            "allowed_executable_paths": [
                str(path) for path in self.allowed_executable_paths
            ],
            "environment_allow": list(self.environment_allow),
            "secret_environment": list(self.secret_environment),
        }


def _environment_names(value: object, label: str) -> tuple[str, ...]:
    names = _strings(value, label)
    invalid = sorted(name for name in names if _ENV_NAME.fullmatch(name) is None)
    if invalid:
        raise ConfigurationError(
            f"{label} entries must be environment variable names: {invalid}"
        )
    if len(set(names)) != len(names):
        raise ConfigurationError(f"{label} entries must be unique")
    return names


@dataclass(frozen=True, slots=True)
class TargetSpec:
    """Frozen meaning for one verifier-gated campaign target."""

    target_id: str
    kind: str
    statement: str
    scope: str

    @classmethod
    def from_table(cls, value: object, index: int) -> Self:
        label = f"targets[{index}]"
        table = _keys(
            value,
            label,
            required={"id", "kind", "statement", "scope"},
        )
        return cls(
            target_id=_identifier(table["id"], f"{label}.id"),
            kind=_identifier(table["kind"], f"{label}.kind"),
            statement=_string(table["statement"], f"{label}.statement"),
            scope=_string(table["scope"], f"{label}.scope"),
        )


@dataclass(frozen=True, slots=True)
class ObligationSpec:
    """One machine-readable review obligation whose disposition is required."""

    obligation_id: str
    description: str
    evidence_stages: tuple[str, ...]

    @classmethod
    def from_table(cls, value: object, index: int) -> Self:
        label = f"obligations[{index}]"
        table = _keys(
            value,
            label,
            required={"id", "description", "evidence_stages"},
        )
        stages = _strings(table["evidence_stages"], f"{label}.evidence_stages")
        if not stages:
            raise ConfigurationError(f"{label}.evidence_stages must not be empty")
        return cls(
            obligation_id=_identifier(table["id"], f"{label}.id"),
            description=_string(table["description"], f"{label}.description"),
            evidence_stages=stages,
        )


@dataclass(frozen=True, slots=True)
class CampaignSpec:
    """Validated problem-agnostic Research/Build campaign."""

    manifest_path: Path
    campaign_id: str
    title: str
    instructions_path: Path
    runs_dir: Path
    max_revisions: int
    inputs: tuple[CampaignInput, ...]
    stages: tuple[StageSpec, ...]
    handoff: HandoffSpec | None
    targets: tuple[TargetSpec, ...] = ()
    obligations: tuple[ObligationSpec, ...] = ()
    publish: PublishSpec | None = None
    execution: ExecutionSpec = ExecutionSpec(
        sandbox=True,
        network=False,
        memory_max_mb=4096,
        cpu_quota_percent=800,
        tasks_max=256,
        file_size_max_mb=1024,
        workspace_max_mb=8192,
        allowed_executable_paths=(),
        environment_allow=_DEFAULT_ENVIRONMENT_ALLOW,
        secret_environment=(),
    )

    @property
    def by_id(self) -> dict[str, StageSpec]:
        return {stage.stage_id: stage for stage in self.stages}

    @property
    def stage_order(self) -> tuple[str, ...]:
        unresolved = {stage.stage_id: set(stage.depends_on) for stage in self.stages}
        ordered: list[str] = []
        while unresolved:
            ready = sorted(
                stage_id
                for stage_id, dependencies in unresolved.items()
                if dependencies <= set(ordered)
            )
            if not ready:
                raise AssertionError("validated campaign DAG became cyclic")
            ordered.extend(ready)
            for stage_id in ready:
                del unresolved[stage_id]
        return tuple(ordered)

    @classmethod
    def load(cls, path: str | Path) -> Self:
        manifest_path = Path(path).expanduser().resolve()
        data = _keys(
            _read_toml(manifest_path),
            "campaign manifest",
            required={"schema_version", "campaign", "inputs", "stages"},
            optional={
                "execution",
                "handoff",
                "publish",
                "targets",
                "obligations",
            },
        )
        if data["schema_version"] != 1:
            raise ConfigurationError("campaign schema_version must be 1")
        campaign = _keys(
            data["campaign"],
            "campaign",
            required={"id", "title", "instructions", "runs_dir"},
            optional={"max_revisions"},
        )
        base = manifest_path.parent
        inputs_value = data["inputs"]
        if not isinstance(inputs_value, list) or not inputs_value:
            raise ConfigurationError("inputs must be a nonempty array of tables")
        inputs = tuple(
            CampaignInput.from_table(value, index, base)
            for index, value in enumerate(inputs_value)
        )
        if len({item.target for item in inputs}) != len(inputs):
            raise ConfigurationError("campaign input targets must be unique")
        stages_value = data["stages"]
        if not isinstance(stages_value, list) or not stages_value:
            raise ConfigurationError("stages must be a nonempty array of tables")
        stages = tuple(
            StageSpec.from_table(value, index)
            for index, value in enumerate(stages_value)
        )
        _validate_stages(stages)
        targets_value = data.get("targets", [])
        if not isinstance(targets_value, list):
            raise ConfigurationError("targets must be an array of tables")
        targets = tuple(
            TargetSpec.from_table(value, index)
            for index, value in enumerate(targets_value)
        )
        if len({target.target_id for target in targets}) != len(targets):
            raise ConfigurationError("campaign target IDs must be unique")
        obligations_value = data.get("obligations", [])
        if not isinstance(obligations_value, list):
            raise ConfigurationError("obligations must be an array of tables")
        obligations = tuple(
            ObligationSpec.from_table(value, index)
            for index, value in enumerate(obligations_value)
        )
        if len({item.obligation_id for item in obligations}) != len(obligations):
            raise ConfigurationError("campaign obligation IDs must be unique")
        unknown_obligation_stages = {
            stage_id
            for obligation in obligations
            for stage_id in obligation.evidence_stages
            if stage_id not in {stage.stage_id for stage in stages}
        }
        if unknown_obligation_stages:
            raise ConfigurationError(
                "campaign obligations name unknown evidence stages: "
                f"{sorted(unknown_obligation_stages)}"
            )
        handoff = (
            HandoffSpec.from_table(data["handoff"])
            if data.get("handoff") is not None
            else None
        )
        _validate_handoff(stages, handoff)
        publish = (
            PublishSpec.from_table(data["publish"], base)
            if data.get("publish") is not None
            else None
        )
        execution = ExecutionSpec.from_table(data.get("execution"), base)
        _reject_inline_secret_values(stages, execution)
        runs = Path(_string(campaign["runs_dir"], "campaign.runs_dir")).expanduser()
        if not runs.is_absolute():
            runs = base / runs
        return cls(
            manifest_path=manifest_path,
            campaign_id=_identifier(campaign["id"], "campaign.id"),
            title=_string(campaign["title"], "campaign.title"),
            instructions_path=_resolve_file(
                base, campaign["instructions"], "campaign.instructions"
            ),
            runs_dir=runs.resolve(),
            max_revisions=_integer(
                campaign.get("max_revisions", 0),
                "campaign.max_revisions",
                0,
                10,
            ),
            inputs=inputs,
            stages=stages,
            handoff=handoff,
            targets=targets,
            obligations=obligations,
            publish=publish,
            execution=execution,
        )

    def to_resolved_dict(
        self,
        *,
        manifest_path: Path,
        instructions_path: Path,
        stage_instructions: Mapping[str, Path],
    ) -> dict[str, object]:
        """Serialize effective paths and feature settings for durable resume."""

        stages: list[dict[str, object]] = []
        for stage in self.stages:
            config = dict(stage.config)
            if stage.stage_id in stage_instructions:
                config["instructions"] = str(stage_instructions[stage.stage_id])
            stages.append(
                {
                    "id": stage.stage_id,
                    "title": stage.title,
                    "mode": stage.mode,
                    "feature": stage.feature,
                    "depends_on": list(stage.depends_on),
                    "required": stage.required,
                    "max_attempts": stage.max_attempts,
                    "failure_policy": stage.failure_policy,
                    "config": config,
                }
            )
        handoff = (
            {
                "producer": self.handoff.producer,
                "artifact": self.handoff.artifact,
                "schema": self.handoff.schema,
                "approval": self.handoff.approval,
            }
            if self.handoff is not None
            else None
        )
        publish = (
            {
                "source": self.publish.source,
                "root": str(self.publish.root),
                "destination": str(self.publish.destination),
                "preserve": list(self.publish.preserve),
            }
            if self.publish is not None
            else None
        )
        return {
            "schema_version": 1,
            "manifest_path": str(manifest_path),
            "campaign": {
                "id": self.campaign_id,
                "title": self.title,
                "instructions": str(instructions_path),
                "runs_dir": str(self.runs_dir),
                "max_revisions": self.max_revisions,
            },
            "inputs": [
                {
                    "source": str(item.source),
                    "target": item.target,
                    "strategy": item.strategy,
                    "excludes": list(item.excludes),
                    **(
                        {"artifact": item.artifact} if item.artifact is not None else {}
                    ),
                    **(
                        {"expected_campaign_id": item.expected_campaign_id}
                        if item.expected_campaign_id is not None
                        else {}
                    ),
                    **(
                        {"expected_run_id": item.expected_run_id}
                        if item.expected_run_id is not None
                        else {}
                    ),
                    **(
                        {"evidence_sha256": item.evidence_sha256}
                        if item.evidence_sha256 is not None
                        else {}
                    ),
                }
                for item in self.inputs
            ],
            "stages": stages,
            "targets": [
                {
                    "id": target.target_id,
                    "kind": target.kind,
                    "statement": target.statement,
                    "scope": target.scope,
                }
                for target in self.targets
            ],
            "obligations": [
                {
                    "id": obligation.obligation_id,
                    "description": obligation.description,
                    "evidence_stages": list(obligation.evidence_stages),
                }
                for obligation in self.obligations
            ],
            "handoff": handoff,
            "execution": self.execution.to_dict(),
            "publish": publish,
        }

    @classmethod
    def load_resolved(cls, path: str | Path) -> Self:
        """Load an effective retained campaign without consulting source files."""

        resolved_path = Path(path).expanduser().resolve()
        try:
            value = json.loads(resolved_path.read_text(encoding="utf-8"))
        except OSError as exc:
            raise ConfigurationError(f"cannot read resolved campaign: {exc}") from exc
        except json.JSONDecodeError as exc:
            raise ConfigurationError(
                f"resolved campaign is invalid JSON: {exc}"
            ) from exc
        data = _keys(
            value,
            "resolved campaign",
            required={
                "schema_version",
                "manifest_path",
                "campaign",
                "inputs",
                "stages",
                "handoff",
            },
            optional={"execution", "publish", "targets", "obligations"},
        )
        if data["schema_version"] != 1:
            raise ConfigurationError("resolved campaign schema_version must be 1")
        campaign = _keys(
            data["campaign"],
            "resolved campaign.campaign",
            required={"id", "title", "instructions", "runs_dir", "max_revisions"},
        )
        inputs_value = data["inputs"]
        if not isinstance(inputs_value, list) or not inputs_value:
            raise ConfigurationError(
                "resolved campaign inputs must be a nonempty array"
            )
        inputs: list[CampaignInput] = []
        for index, raw in enumerate(inputs_value):
            label = f"resolved campaign.inputs[{index}]"
            item = _keys(
                raw,
                label,
                required={"source", "target", "strategy", "excludes"},
                optional={
                    "artifact",
                    "expected_campaign_id",
                    "expected_run_id",
                    "evidence_sha256",
                },
            )
            strategy = _string(item["strategy"], f"{label}.strategy")
            if strategy not in ("copy", "symlink", "verified_artifact"):
                raise ConfigurationError(f"{label}.strategy is invalid")
            artifact: str | None = None
            expected_campaign_id: str | None = None
            expected_run_id: str | None = None
            evidence_sha256: str | None = None
            provenance_keys = {
                "expected_campaign_id",
                "expected_run_id",
                "evidence_sha256",
            }
            if strategy == "verified_artifact":
                if "artifact" not in item:
                    raise ConfigurationError(
                        f"{label}.artifact is required for a verified_artifact input"
                    )
                if _strings(item["excludes"], f"{label}.excludes"):
                    raise ConfigurationError(
                        f"{label}.excludes is invalid for a verified_artifact input"
                    )
                artifact = _relative(item["artifact"], f"{label}.artifact")
                missing_provenance = provenance_keys - item.keys()
                if missing_provenance:
                    raise ConfigurationError(
                        f"{label} is missing verified provenance keys: "
                        f"{sorted(missing_provenance)}"
                    )
                expected_campaign_id = _identifier(
                    item["expected_campaign_id"], f"{label}.expected_campaign_id"
                )
                expected_run_id = _safe_identifier(
                    item["expected_run_id"], f"{label}.expected_run_id"
                )
                evidence_sha256 = _sha256(
                    item["evidence_sha256"], f"{label}.evidence_sha256"
                )
            else:
                if "artifact" in item:
                    raise ConfigurationError(
                        f"{label}.artifact is only valid for a verified_artifact input"
                    )
                invalid_provenance = provenance_keys & item.keys()
                if invalid_provenance:
                    raise ConfigurationError(
                        f"{label} provenance pins are only valid for a "
                        "verified_artifact input"
                    )
            inputs.append(
                CampaignInput(
                    source=Path(_string(item["source"], f"{label}.source")),
                    target=_relative(item["target"], f"{label}.target"),
                    strategy=strategy,  # type: ignore[arg-type]
                    excludes=_strings(item["excludes"], f"{label}.excludes"),
                    artifact=artifact,
                    expected_campaign_id=expected_campaign_id,
                    expected_run_id=expected_run_id,
                    evidence_sha256=evidence_sha256,
                )
            )
        stages_value = data["stages"]
        if not isinstance(stages_value, list) or not stages_value:
            raise ConfigurationError(
                "resolved campaign stages must be a nonempty array"
            )
        stages = tuple(
            StageSpec.from_table(item, index) for index, item in enumerate(stages_value)
        )
        _validate_stages(stages)
        targets_value = data.get("targets", [])
        if not isinstance(targets_value, list):
            raise ConfigurationError("resolved campaign targets must be an array")
        targets = tuple(
            TargetSpec.from_table(item, index)
            for index, item in enumerate(targets_value)
        )
        if len({target.target_id for target in targets}) != len(targets):
            raise ConfigurationError("resolved campaign target IDs must be unique")
        obligations_value = data.get("obligations", [])
        if not isinstance(obligations_value, list):
            raise ConfigurationError("resolved campaign obligations must be an array")
        obligations = tuple(
            ObligationSpec.from_table(item, index)
            for index, item in enumerate(obligations_value)
        )
        if len({item.obligation_id for item in obligations}) != len(obligations):
            raise ConfigurationError("resolved campaign obligation IDs must be unique")
        unknown_obligation_stages = {
            stage_id
            for obligation in obligations
            for stage_id in obligation.evidence_stages
            if stage_id not in {stage.stage_id for stage in stages}
        }
        if unknown_obligation_stages:
            raise ConfigurationError(
                "resolved obligations name unknown evidence stages: "
                f"{sorted(unknown_obligation_stages)}"
            )
        handoff = (
            HandoffSpec.from_table(data["handoff"])
            if data["handoff"] is not None
            else None
        )
        _validate_handoff(stages, handoff)
        publish = (
            PublishSpec.from_resolved_table(data["publish"])
            if data.get("publish") is not None
            else None
        )
        execution = ExecutionSpec.from_table(
            data.get("execution"), resolved_path.parent, resolved=True
        )
        _reject_inline_secret_values(stages, execution)
        instructions_path = Path(
            _string(campaign["instructions"], "resolved campaign.instructions")
        )
        if not instructions_path.is_file():
            raise ConfigurationError(
                f"retained campaign instructions are missing: {instructions_path}"
            )
        return cls(
            manifest_path=Path(
                _string(data["manifest_path"], "resolved campaign.manifest_path")
            ),
            campaign_id=_identifier(campaign["id"], "resolved campaign.id"),
            title=_string(campaign["title"], "resolved campaign.title"),
            instructions_path=instructions_path,
            runs_dir=Path(_string(campaign["runs_dir"], "resolved campaign.runs_dir")),
            max_revisions=_integer(
                campaign["max_revisions"],
                "resolved campaign.max_revisions",
                0,
                10,
            ),
            inputs=tuple(inputs),
            stages=stages,
            handoff=handoff,
            targets=targets,
            obligations=obligations,
            publish=publish,
            execution=execution,
        )


def _validate_stages(stages: tuple[StageSpec, ...]) -> None:
    by_id = {stage.stage_id: stage for stage in stages}
    if len(by_id) != len(stages):
        raise ConfigurationError("campaign stage IDs must be unique")
    resolved: set[str] = set()
    while len(resolved) < len(stages):
        ready = {
            stage.stage_id
            for stage in stages
            if stage.stage_id not in resolved and set(stage.depends_on) <= resolved
        }
        unknown = {
            dependency
            for stage in stages
            for dependency in stage.depends_on
            if dependency not in by_id
        }
        if unknown:
            raise ConfigurationError(
                f"campaign stages have unknown dependencies: {sorted(unknown)}"
            )
        if not ready:
            blocked = sorted(set(by_id) - resolved)
            raise ConfigurationError(f"campaign stage DAG contains a cycle: {blocked}")
        resolved.update(ready)
    for stage in stages:
        if stage.stage_id in stage.depends_on:
            raise ConfigurationError(f"stage {stage.stage_id!r} depends on itself")
        if stage.mode == "research" and any(
            by_id[dependency].mode == "build" for dependency in stage.depends_on
        ):
            raise ConfigurationError(
                f"research stage {stage.stage_id!r} cannot depend on a build stage"
            )


def _reject_inline_secret_values(
    stages: tuple[StageSpec, ...], execution: ExecutionSpec
) -> None:
    secrets = tuple(
        value
        for name in execution.secret_environment
        if (value := os.environ.get(name))
    )
    if not secrets:
        return
    for stage in stages:
        if stage.feature != "command":
            continue
        argv = stage.config.get("argv", ())
        environment = stage.config.get("environment", {})
        configured: list[str] = []
        if isinstance(argv, list):
            configured.extend(item for item in argv if isinstance(item, str))
        if isinstance(environment, dict):
            configured.extend(
                item for item in environment.values() if isinstance(item, str)
            )
        if any(secret in item for secret in secrets for item in configured):
            raise ConfigurationError(
                f"stage {stage.stage_id!r} embeds a declared secret value"
            )


def _validate_handoff(
    stages: tuple[StageSpec, ...], handoff: HandoffSpec | None
) -> None:
    by_id = {stage.stage_id: stage for stage in stages}
    crosses_boundary = any(
        stage.mode == "build"
        and any(by_id[dependency].mode == "research" for dependency in stage.depends_on)
        for stage in stages
    )
    if crosses_boundary and handoff is None:
        raise ConfigurationError(
            "campaigns with research-to-build dependencies require a handoff"
        )
    if handoff is None:
        return
    producer = by_id.get(handoff.producer)
    if producer is None:
        raise ConfigurationError("handoff.producer is not a campaign stage")
    if producer.mode != "research":
        raise ConfigurationError("handoff.producer must be a research stage")
