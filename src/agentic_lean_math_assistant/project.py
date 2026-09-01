"""Strict per-problem configuration for generated research campaigns."""

from __future__ import annotations

import tomllib
from dataclasses import dataclass, replace
from pathlib import Path, PurePosixPath
from typing import Any, Self

from .config import ConfigurationError, ExecutionSpec

_ALLOWED_TOOLS = frozenset(
    {"read", "grep", "glob", "bash", "eval", "write", "edit", "web_search"}
)


def _table(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ConfigurationError(f"{label} must be a TOML table")
    return value


def _keys(
    value: object, label: str, required: set[str], optional: set[str] | None = None
) -> dict[str, Any]:
    table = _table(value, label)
    missing = required - table.keys()
    extra = table.keys() - required - (optional or set())
    if missing or extra:
        raise ConfigurationError(
            f"{label} keys differ; missing={sorted(missing)}, extra={sorted(extra)}"
        )
    return table


def _text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be a nonempty string")
    return value.strip()


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


def _optional_integer(
    value: object, label: str, minimum: int, maximum: int
) -> int | None:
    if value is None:
        return None
    return _integer(value, label, minimum, maximum)


def _strings(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ConfigurationError(f"{label} must be an array of nonempty strings")
    result = tuple(item.strip() for item in value)
    if len(result) != len(set(result)):
        raise ConfigurationError(f"{label} must not contain duplicates")
    return result


def _safe_relative_text(value: object, label: str) -> str:
    raw = _text(value, label).replace("\\", "/")
    path = PurePosixPath(raw)
    if (
        path.is_absolute()
        or not path.parts
        or any(part in ("", ".", "..") for part in path.parts)
    ):
        raise ConfigurationError(f"{label} must be a safe relative path")
    return path.as_posix()


def _relative(root: Path, value: object, label: str) -> Path:
    raw = _text(value, label).replace("\\", "/")
    candidate = (root / raw).resolve()
    try:
        candidate.relative_to(root)
    except ValueError as exc:
        raise ConfigurationError(f"{label} escapes the project directory") from exc
    return candidate


def _optional(value: object, label: str) -> str | None:
    if value is None:
        return None
    return _text(value, label)


@dataclass(frozen=True, slots=True)
class ComputeProfile:
    profile_id: str
    omp: str | None
    planner_model: str | None
    planner_thinking: str | None
    max_tasks: int | None
    max_parallel: int | None
    max_restarts: int | None
    default_agent_time: int | None
    pilot_agent_seconds: int | None
    research_agent_seconds: int | None
    formalization_agent_seconds: int | None
    max_attempts_total: int | None
    max_invention_tasks: int | None
    execution_thinking: str | None
    analysis_thinking: str | None
    invention_thinking: str | None
    audit_thinking: str | None

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"compute_profiles[{index}]"
        table = _keys(
            value,
            label,
            {"id"},
            {
                "omp",
                "planner_model",
                "planner_thinking",
                "max_tasks",
                "max_parallel",
                "max_restarts",
                "default_agent_time",
                "pilot_agent_seconds",
                "research_agent_seconds",
                "formalization_agent_seconds",
                "max_attempts_total",
                "max_invention_tasks",
                "execution_thinking",
                "analysis_thinking",
                "invention_thinking",
                "audit_thinking",
            },
        )
        profile_id = _text(table["id"], f"{label}.id")
        if not profile_id.replace("-", "_").isidentifier() or profile_id[0] == "_":
            raise ConfigurationError(f"{label}.id must be a lowercase identifier")
        return cls(
            profile_id=profile_id,
            omp=_optional(table.get("omp"), f"{label}.omp"),
            planner_model=_optional(
                table.get("planner_model"), f"{label}.planner_model"
            ),
            planner_thinking=_optional(
                table.get("planner_thinking"), f"{label}.planner_thinking"
            ),
            max_tasks=_optional_integer(
                table.get("max_tasks"), f"{label}.max_tasks", 1, 32
            ),
            max_parallel=_optional_integer(
                table.get("max_parallel"), f"{label}.max_parallel", 1, 32
            ),
            max_restarts=_optional_integer(
                table.get("max_restarts"), f"{label}.max_restarts", 0, 10
            ),
            default_agent_time=_optional_integer(
                table.get("default_agent_time"),
                f"{label}.default_agent_time",
                30,
                86400,
            ),
            pilot_agent_seconds=_optional_integer(
                table.get("pilot_agent_seconds"),
                f"{label}.pilot_agent_seconds",
                30,
                1_000_000,
            ),
            research_agent_seconds=_optional_integer(
                table.get("research_agent_seconds"),
                f"{label}.research_agent_seconds",
                30,
                1_000_000,
            ),
            formalization_agent_seconds=_optional_integer(
                table.get("formalization_agent_seconds"),
                f"{label}.formalization_agent_seconds",
                30,
                1_000_000,
            ),
            max_attempts_total=_optional_integer(
                table.get("max_attempts_total"),
                f"{label}.max_attempts_total",
                1,
                160,
            ),
            max_invention_tasks=_optional_integer(
                table.get("max_invention_tasks"),
                f"{label}.max_invention_tasks",
                0,
                32,
            ),
            execution_thinking=_optional(
                table.get("execution_thinking"), f"{label}.execution_thinking"
            ),
            analysis_thinking=_optional(
                table.get("analysis_thinking"), f"{label}.analysis_thinking"
            ),
            invention_thinking=_optional(
                table.get("invention_thinking"), f"{label}.invention_thinking"
            ),
            audit_thinking=_optional(
                table.get("audit_thinking"), f"{label}.audit_thinking"
            ),
        )


def _lean_name(raw: object, label: str) -> str:
    name = _text(raw, label)
    if any(not part.replace("_", "a").isalnum() for part in name.split(".")):
        raise ConfigurationError(f"{label} must be a Lean identifier")
    return name


@dataclass(frozen=True, slots=True)
class LeanTheoremSpec:
    module: str
    declaration: str
    theorem_type: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"autonomy.success.theorems[{index}]"
        table = _keys(
            value,
            label,
            {"module", "declaration", "type"},
        )
        return cls(
            module=_lean_name(table["module"], f"{label}.module"),
            declaration=_lean_name(table["declaration"], f"{label}.declaration"),
            theorem_type=_text(table["type"], f"{label}.type"),
        )


@dataclass(frozen=True, slots=True)
class AutonomySuccessSpec:
    workspace: str
    theorems: tuple[LeanTheoremSpec, ...]
    build_command: tuple[str, ...]
    allowed_axioms: tuple[str, ...]
    verification_commands: tuple[tuple[str, ...], ...]
    required_artifacts: tuple[str, ...]

    @classmethod
    def parse(cls, value: object) -> Self:
        table = _keys(
            value,
            "autonomy.success",
            {
                "workspace",
                "theorems",
                "build_command",
                "allowed_axioms",
            },
            {"verification_commands", "required_artifacts"},
        )

        def command(raw: object, label: str) -> tuple[str, ...]:
            if (
                not isinstance(raw, list)
                or not raw
                or not all(isinstance(item, str) and item for item in raw)
            ):
                raise ConfigurationError(f"{label} must be a nonempty argument array")
            return tuple(raw)

        raw_verifiers = table.get("verification_commands", [])
        if not isinstance(raw_verifiers, list):
            raise ConfigurationError(
                "autonomy.success.verification_commands must be an array of commands"
            )

        raw_theorems = table["theorems"]
        if not isinstance(raw_theorems, list) or not raw_theorems:
            raise ConfigurationError(
                "autonomy.success.theorems must be a nonempty array of tables"
            )
        theorems = tuple(
            LeanTheoremSpec.parse(item, index)
            for index, item in enumerate(raw_theorems)
        )
        identities = {(item.module, item.declaration) for item in theorems}
        if len(identities) != len(theorems):
            raise ConfigurationError(
                "autonomy.success.theorems must name unique declarations"
            )

        required = _strings(
            table.get("required_artifacts", []),
            "autonomy.success.required_artifacts",
        )
        return cls(
            workspace=_safe_relative_text(
                table["workspace"], "autonomy.success.workspace"
            ),
            theorems=theorems,
            build_command=command(
                table["build_command"], "autonomy.success.build_command"
            ),
            allowed_axioms=_strings(
                table["allowed_axioms"], "autonomy.success.allowed_axioms"
            ),
            verification_commands=tuple(
                command(item, f"autonomy.success.verification_commands[{index}]")
                for index, item in enumerate(raw_verifiers)
            ),
            required_artifacts=tuple(
                _safe_relative_text(item, "autonomy.success.required_artifacts")
                for item in required
            ),
        )


@dataclass(frozen=True, slots=True)
class AutonomySpec:
    enabled: bool
    approval_timeout_minutes: int
    afk_autonomy: bool
    max_campaigns: int
    max_elapsed_minutes: int
    max_consecutive_failures: int
    analysis_agent_seconds: int
    compute_profile: str | None
    success: AutonomySuccessSpec | None

    @classmethod
    def parse(cls, value: object | None) -> Self:
        if value is None:
            return cls(False, 15, True, 24, 10080, 3, 2400, None, None)
        table = _keys(
            value,
            "autonomy",
            set(),
            {
                "enabled",
                "approval_timeout_minutes",
                "afk_autonomy",
                "max_campaigns",
                "max_elapsed_minutes",
                "max_consecutive_failures",
                "analysis_agent_seconds",
                "compute_profile",
                "success",
            },
        )
        enabled = _boolean(table.get("enabled", False), "autonomy.enabled")
        success_value = table.get("success")
        success = (
            AutonomySuccessSpec.parse(success_value)
            if success_value is not None
            else None
        )
        if enabled and success is None:
            raise ConfigurationError(
                "enabled autonomy requires an autonomy.success contract"
            )
        return cls(
            enabled=enabled,
            approval_timeout_minutes=_integer(
                table.get("approval_timeout_minutes", 15),
                "autonomy.approval_timeout_minutes",
                0,
                1440,
            ),
            afk_autonomy=_boolean(
                table.get("afk_autonomy", True), "autonomy.afk_autonomy"
            ),
            max_campaigns=_integer(
                table.get("max_campaigns", 24), "autonomy.max_campaigns", 1, 1000
            ),
            max_elapsed_minutes=_integer(
                table.get("max_elapsed_minutes", 10080),
                "autonomy.max_elapsed_minutes",
                1,
                525600,
            ),
            max_consecutive_failures=_integer(
                table.get("max_consecutive_failures", 3),
                "autonomy.max_consecutive_failures",
                1,
                20,
            ),
            analysis_agent_seconds=_integer(
                table.get("analysis_agent_seconds", 2400),
                "autonomy.analysis_agent_seconds",
                30,
                86400,
            ),
            compute_profile=_optional(
                table.get("compute_profile"), "autonomy.compute_profile"
            ),
            success=success,
        )


@dataclass(frozen=True, slots=True)
class ProjectInput:
    source: Path
    target: str
    excludes: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int, root: Path) -> Self:
        label = f"inputs[{index}]"
        table = _keys(value, label, {"path", "target"}, {"excludes"})
        target = _text(table["target"], f"{label}.target").replace("\\", "/")
        target_path = Path(target)
        if target_path.is_absolute() or ".." in target_path.parts:
            raise ConfigurationError(f"{label}.target must be a safe relative path")
        excludes_value = table.get("excludes", [])
        if not isinstance(excludes_value, list) or not all(
            isinstance(item, str) and item for item in excludes_value
        ):
            raise ConfigurationError(f"{label}.excludes must be an array of strings")
        source = _relative(root, table["path"], f"{label}.path")
        if not source.exists():
            raise ConfigurationError(f"{label}.path does not exist: {source}")
        return cls(source, target, tuple(excludes_value))


@dataclass(frozen=True, slots=True)
class ProjectSpec:
    manifest_path: Path
    project_id: str
    title: str
    problem_path: Path
    references_dir: Path
    knowledge_dir: Path
    runs_dir: Path
    inputs: tuple[ProjectInput, ...]
    omp: str
    planner_model: str | None
    planner_thinking: str | None
    max_tasks: int
    max_parallel: int
    max_restarts: int
    default_agent_time: int
    allowed_tools: tuple[str, ...]
    pilot_agent_seconds: int
    research_agent_seconds: int
    formalization_agent_seconds: int
    max_attempts_total: int
    max_invention_tasks: int
    execution_thinking: str
    analysis_thinking: str
    invention_thinking: str
    audit_thinking: str
    execution: ExecutionSpec
    compute_profiles: tuple[ComputeProfile, ...]
    autonomy: AutonomySpec

    def with_compute_profile(self, profile_id: str | None) -> Self:
        if profile_id is None:
            return self
        profile = next(
            (item for item in self.compute_profiles if item.profile_id == profile_id),
            None,
        )
        if profile is None:
            raise ConfigurationError(f"unknown compute profile: {profile_id!r}")
        return replace(
            self,
            omp=profile.omp if profile.omp is not None else self.omp,
            planner_model=(
                profile.planner_model
                if profile.planner_model is not None
                else self.planner_model
            ),
            planner_thinking=(
                profile.planner_thinking
                if profile.planner_thinking is not None
                else self.planner_thinking
            ),
            max_tasks=profile.max_tasks or self.max_tasks,
            max_parallel=profile.max_parallel or self.max_parallel,
            max_restarts=(
                profile.max_restarts
                if profile.max_restarts is not None
                else self.max_restarts
            ),
            default_agent_time=profile.default_agent_time or self.default_agent_time,
            pilot_agent_seconds=(
                profile.pilot_agent_seconds or self.pilot_agent_seconds
            ),
            research_agent_seconds=(
                profile.research_agent_seconds or self.research_agent_seconds
            ),
            formalization_agent_seconds=(
                profile.formalization_agent_seconds or self.formalization_agent_seconds
            ),
            max_attempts_total=profile.max_attempts_total or self.max_attempts_total,
            max_invention_tasks=(
                profile.max_invention_tasks
                if profile.max_invention_tasks is not None
                else self.max_invention_tasks
            ),
            execution_thinking=(profile.execution_thinking or self.execution_thinking),
            analysis_thinking=profile.analysis_thinking or self.analysis_thinking,
            invention_thinking=profile.invention_thinking or self.invention_thinking,
            audit_thinking=profile.audit_thinking or self.audit_thinking,
        )

    def thinking_for(self, reasoning_class: str) -> str:
        profiles = {
            "execution": self.execution_thinking,
            "analysis": self.analysis_thinking,
            "invention": self.invention_thinking,
            "audit": self.audit_thinking,
        }
        try:
            return profiles[reasoning_class]
        except KeyError as exc:
            raise ValueError(f"unknown reasoning class: {reasoning_class}") from exc

    @property
    def root(self) -> Path:
        return self.manifest_path.parent

    @classmethod
    def load(cls, path: str | Path) -> Self:
        manifest = Path(path).expanduser().resolve()
        try:
            value = tomllib.loads(manifest.read_text(encoding="utf-8"))
        except OSError as exc:
            raise ConfigurationError(f"cannot read project manifest: {exc}") from exc
        except tomllib.TOMLDecodeError as exc:
            raise ConfigurationError(
                f"project manifest is invalid TOML: {exc}"
            ) from exc
        root = manifest.parent.resolve()
        top = _keys(
            value,
            "project manifest",
            {"schema_version", "project"},
            {"regime", "inputs", "execution", "autonomy", "compute_profiles"},
        )
        if top["schema_version"] != 1:
            raise ConfigurationError("project schema_version must be 1")
        project = _keys(
            top["project"],
            "project",
            {"id", "title", "problem", "references", "knowledge", "runs"},
        )
        project_id = _text(project["id"], "project.id")
        if not project_id.replace("-", "_").isidentifier() or project_id[0] == "_":
            raise ConfigurationError("project.id must be a lowercase identifier")
        problem = _relative(root, project["problem"], "project.problem")
        if not problem.is_file():
            raise ConfigurationError(f"project.problem does not exist: {problem}")
        references = _relative(root, project["references"], "project.references")
        knowledge = _relative(root, project["knowledge"], "project.knowledge")
        runs = _relative(root, project["runs"], "project.runs")
        regime = _keys(
            top.get("regime", {}),
            "regime",
            set(),
            {
                "omp",
                "planner_model",
                "planner_thinking",
                "max_tasks",
                "max_parallel",
                "max_restarts",
                "default_agent_time",
                "allowed_tools",
                "pilot_agent_seconds",
                "research_agent_seconds",
                "formalization_agent_seconds",
                "max_attempts_total",
                "max_invention_tasks",
                "execution_thinking",
                "analysis_thinking",
                "invention_thinking",
                "audit_thinking",
            },
        )
        tools_value = regime.get(
            "allowed_tools", ["read", "grep", "glob", "bash", "eval", "write", "edit"]
        )
        if not isinstance(tools_value, list) or not all(
            isinstance(item, str) and item in _ALLOWED_TOOLS for item in tools_value
        ):
            raise ConfigurationError(
                f"regime.allowed_tools must use registered tools: {sorted(_ALLOWED_TOOLS)}"
            )
        if len(set(tools_value)) != len(tools_value):
            raise ConfigurationError("regime.allowed_tools must not contain duplicates")
        inputs_value = top.get("inputs", [])
        if not isinstance(inputs_value, list):
            raise ConfigurationError("inputs must be an array of tables")
        inputs = tuple(
            ProjectInput.parse(item, index, root)
            for index, item in enumerate(inputs_value)
        )
        targets = [item.target for item in inputs]
        if len(targets) != len(set(targets)):
            raise ConfigurationError("project input targets must be unique")
        reserved_targets = {"problem.md", "references", "knowledge", "pre-campaign"}
        conflicting = {
            target for target in targets if target.split("/", 1)[0] in reserved_targets
        }
        if conflicting:
            raise ConfigurationError(
                f"project inputs use a reserved target: {sorted(conflicting)}"
            )
        profiles_value = top.get("compute_profiles", [])
        if not isinstance(profiles_value, list):
            raise ConfigurationError("compute_profiles must be an array of tables")
        compute_profiles = tuple(
            ComputeProfile.parse(item, index)
            for index, item in enumerate(profiles_value)
        )
        profile_ids = [item.profile_id for item in compute_profiles]
        if len(profile_ids) != len(set(profile_ids)):
            raise ConfigurationError("compute profile IDs must be unique")
        autonomy = AutonomySpec.parse(top.get("autonomy"))
        if autonomy.compute_profile is not None and autonomy.compute_profile not in set(
            profile_ids
        ):
            raise ConfigurationError(
                "autonomy.compute_profile names an unknown compute profile"
            )
        return cls(
            manifest_path=manifest,
            project_id=project_id,
            title=_text(project["title"], "project.title"),
            problem_path=problem,
            references_dir=references,
            knowledge_dir=knowledge,
            runs_dir=runs,
            inputs=inputs,
            omp=_text(regime.get("omp", "omp"), "regime.omp"),
            planner_model=_optional(
                regime.get("planner_model"), "regime.planner_model"
            ),
            planner_thinking=_optional(
                regime.get("planner_thinking", "high"), "regime.planner_thinking"
            ),
            max_tasks=_integer(regime.get("max_tasks", 16), "regime.max_tasks", 1, 32),
            max_parallel=_integer(
                regime.get("max_parallel", 8), "regime.max_parallel", 1, 32
            ),
            max_restarts=_integer(
                regime.get("max_restarts", 1), "regime.max_restarts", 0, 3
            ),
            default_agent_time=_integer(
                regime.get("default_agent_time", 1800),
                "regime.default_agent_time",
                30,
                86400,
            ),
            allowed_tools=tuple(tools_value),
            pilot_agent_seconds=_integer(
                regime.get("pilot_agent_seconds", 7200),
                "regime.pilot_agent_seconds",
                30,
                1_000_000,
            ),
            research_agent_seconds=_integer(
                regime.get("research_agent_seconds", 28800),
                "regime.research_agent_seconds",
                30,
                1_000_000,
            ),
            formalization_agent_seconds=_integer(
                regime.get("formalization_agent_seconds", 14400),
                "regime.formalization_agent_seconds",
                30,
                1_000_000,
            ),
            max_attempts_total=_integer(
                regime.get("max_attempts_total", 32),
                "regime.max_attempts_total",
                1,
                160,
            ),
            max_invention_tasks=_integer(
                regime.get("max_invention_tasks", 4),
                "regime.max_invention_tasks",
                0,
                32,
            ),
            execution_thinking=_text(
                regime.get("execution_thinking", "medium"),
                "regime.execution_thinking",
            ),
            analysis_thinking=_text(
                regime.get("analysis_thinking", "high"),
                "regime.analysis_thinking",
            ),
            invention_thinking=_text(
                regime.get("invention_thinking", "xhigh"),
                "regime.invention_thinking",
            ),
            audit_thinking=_text(
                regime.get("audit_thinking", "xhigh"),
                "regime.audit_thinking",
            ),
            execution=ExecutionSpec.from_table(top.get("execution"), root),
            compute_profiles=compute_profiles,
            autonomy=autonomy,
        )
