"""One-command folder-to-verified-publication orchestration."""

from __future__ import annotations

import hashlib
import json
import re
import shutil
import tomllib
from dataclasses import dataclass, replace
from datetime import UTC, datetime
from pathlib import Path, PurePosixPath
from typing import Any, Literal, Self

from .artifacts import atomic_write_json, digest_file, utc_now
from .config import ConfigurationError
from .forecast import CompletionForecast, predicted_limit_breached

SolveStatus = Literal[
    "new",
    "contracting",
    "preflighting",
    "solving",
    "prediction_limit_reached",
    "resource_limit_reached",
    "needs_input",
    "publishing",
    "complete",
    "publication_failed",
    "failed",
    "stopped",
]

_DURATION = re.compile(r"^(?P<amount>[1-9][0-9]*)(?P<unit>[smhdw])$")
_DURATION_FACTORS = {"s": 1, "m": 60, "h": 3600, "d": 86400, "w": 604800}
_INPUT_EXCLUDES = frozenset(
    {
        ".alma",
        "result",
        ".git",
        ".lake",
        "__pycache__",
        ".venv",
        "venv",
        "dist",
        "build",
    }
)
_CONFIDENCE_RANK = {"low": 0, "medium": 1, "high": 2}


class SolveError(RuntimeError):
    """A folder solve violated its retained contract or execution policy."""


class SolveNeedsInput(SolveError):
    """The solve cannot continue without a user decision."""


@dataclass(frozen=True, slots=True)
class SolveModels:
    planner: str | None = None
    worker: str | None = None
    analysis: str | None = None
    forecaster: str | None = None
    escalation: str | None = None
    proof_author: str | None = None
    proof_reviewer: str | None = None


@dataclass(frozen=True, slots=True)
class ForecastPolicy:
    predicted_runtime_limit_seconds: int | None = None
    initial_after_seconds: int = 3600
    interval_seconds: int = 7200
    minimum_interval_seconds: int = 1800
    percentile: int = 80
    breach_confirmations: int = 2
    minimum_confidence: Literal["low", "medium", "high"] = "medium"


@dataclass(frozen=True, slots=True)
class SolveSpec:
    folder: Path
    problem: Path
    runtime_limit_seconds: int
    approval_timeout_seconds: int
    max_model_calls: int | None
    allow_web: bool
    sandbox: bool
    profile: Literal["economical", "balanced", "max"]
    models: SolveModels
    forecast: ForecastPolicy
    restart: bool = False
    publish_inconclusive: bool | None = None
    headless: bool = False
    feedback: tuple[str, ...] = ()

    @property
    def state_root(self) -> Path:
        return self.folder / ".alma"

    @property
    def result_root(self) -> Path:
        return self.folder / "result"

    @classmethod
    def load(
        cls,
        folder: Path,
        *,
        problem: Path | None = None,
        runtime_limit: str | None = None,
        predicted_runtime_limit: str | None = None,
        forecast_interval: str | None = None,
        forecast_percentile: int | None = None,
        max_model_calls: int | None = None,
        profile: str | None = None,
        restart: bool = False,
        publish_inconclusive: bool | None = None,
        headless: bool = False,
        allow_web: bool | None = None,
        sandbox: bool | None = None,
        feedback: tuple[str, ...] = (),
    ) -> Self:
        root = folder.expanduser().resolve()
        if not root.is_dir() or root.is_symlink():
            raise ConfigurationError(f"solve folder is not a regular directory: {root}")
        config_path = root / "solve.toml"
        if config_path.is_file():
            try:
                raw = tomllib.loads(config_path.read_text(encoding="utf-8"))
            except (OSError, tomllib.TOMLDecodeError) as exc:
                raise ConfigurationError(f"cannot load solve.toml: {exc}") from exc
        else:
            raw = {}
        if not isinstance(raw, dict):
            raise ConfigurationError("solve.toml must be a TOML object")
        unknown_top = set(raw) - {
            "schema_version",
            "solve",
            "resources",
            "forecast",
            "models",
            "execution",
        }
        if unknown_top:
            raise ConfigurationError(
                f"solve.toml has unknown sections: {sorted(unknown_top)}"
            )
        if raw.get("schema_version", 1) != 1:
            raise ConfigurationError("solve.toml schema_version must be 1")
        solve_table = _object(raw.get("solve", {}), "solve")
        resource_table = _object(raw.get("resources", {}), "resources")
        forecast_table = _object(raw.get("forecast", {}), "forecast")
        model_table = _object(raw.get("models", {}), "models")
        execution_table = _object(raw.get("execution", {}), "execution")
        retained: dict[str, Any] = {}
        retained_path = root / ".alma" / "state.json"
        if not restart and retained_path.is_file():
            try:
                loaded = json.loads(retained_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as exc:
                raise ConfigurationError(
                    f"cannot load retained solve policy: {exc}"
                ) from exc
            if not isinstance(loaded, dict):
                raise ConfigurationError("retained solve policy must be an object")
            retained = loaded
        _known_keys(solve_table, "solve", {"problem", "profile", "allow_web"})
        _known_keys(
            resource_table,
            "resources",
            {"runtime_limit", "max_model_calls", "approval_timeout"},
        )
        _known_keys(
            forecast_table,
            "forecast",
            {
                "predicted_runtime_limit",
                "initial_after",
                "interval",
                "minimum_interval",
                "percentile",
                "breach_confirmations",
                "minimum_confidence",
            },
        )
        _known_keys(
            model_table,
            "models",
            {
                "planner",
                "worker",
                "analysis",
                "forecaster",
                "escalation",
                "proof_author",
                "proof_reviewer",
            },
        )
        _known_keys(execution_table, "execution", {"sandbox"})
        raw_problem = problem or Path(str(solve_table.get("problem", "problem.md")))
        resolved_problem = raw_problem.expanduser()
        if not resolved_problem.is_absolute():
            resolved_problem = root / resolved_problem
        resolved_problem = resolved_problem.resolve()
        if root not in resolved_problem.parents or not resolved_problem.is_file():
            raise ConfigurationError(
                f"solve problem must be a file inside the solve folder: {resolved_problem}"
            )
        runtime_text = runtime_limit or _optional_text(
            resource_table.get("runtime_limit"), "resources.runtime_limit"
        )
        predicted_text = predicted_runtime_limit or _optional_text(
            forecast_table.get("predicted_runtime_limit"),
            "forecast.predicted_runtime_limit",
        )
        retained_hard_raw = retained.get("runtime_limit_seconds")
        retained_predicted_raw = retained.get("predicted_runtime_limit_seconds")
        retained_hard = (
            retained_hard_raw
            if isinstance(retained_hard_raw, int)
            and not isinstance(retained_hard_raw, bool)
            else None
        )
        retained_predicted = (
            retained_predicted_raw
            if isinstance(retained_predicted_raw, int)
            and not isinstance(retained_predicted_raw, bool)
            else None
        )
        limit_text = runtime_text or predicted_text
        if limit_text is not None:
            hard_seconds = parse_duration(limit_text)
        elif retained_hard is not None:
            hard_seconds = retained_hard
        elif retained_predicted is not None:
            hard_seconds = retained_predicted
        else:
            raise ConfigurationError(
                "solve requires --runtime-limit, --predicted-runtime-limit, or a configured equivalent"
            )
        predicted_seconds = (
            parse_duration(predicted_text)
            if predicted_text is not None
            else retained_predicted
        )
        selected_profile = profile or str(solve_table.get("profile", "balanced"))
        if selected_profile not in {"economical", "balanced", "max"}:
            raise ConfigurationError(
                "solve profile must be economical, balanced, or max"
            )
        selected_percentile = forecast_percentile or _integer(
            forecast_table.get("percentile", 80), "forecast.percentile", 50, 95
        )
        if selected_percentile not in {50, 80, 95}:
            raise ConfigurationError("forecast.percentile must be 50, 80, or 95")
        selected_interval = parse_duration(
            forecast_interval
            or _optional_text(forecast_table.get("interval"), "forecast.interval")
            or "2h"
        )
        selected_models = SolveModels(
            **{
                name: _optional_text(model_table.get(name), f"models.{name}")
                for name in SolveModels.__dataclass_fields__
            }
        )
        configured_calls = resource_table.get(
            "max_model_calls", retained.get("max_model_calls")
        )
        selected_calls = (
            max_model_calls if max_model_calls is not None else configured_calls
        )
        if selected_calls is not None:
            selected_calls = _integer(
                selected_calls, "resources.max_model_calls", 1, 100_000
            )
        return cls(
            folder=root,
            problem=resolved_problem,
            runtime_limit_seconds=hard_seconds,
            approval_timeout_seconds=parse_duration(
                _optional_text(
                    resource_table.get("approval_timeout"), "resources.approval_timeout"
                )
                or "15m"
            ),
            max_model_calls=selected_calls,
            allow_web=(
                allow_web
                if allow_web is not None
                else _boolean(solve_table.get("allow_web", False), "solve.allow_web")
            ),
            sandbox=(
                sandbox
                if sandbox is not None
                else _boolean(execution_table.get("sandbox", True), "execution.sandbox")
            ),
            profile=selected_profile,  # type: ignore[arg-type]
            models=selected_models,
            forecast=ForecastPolicy(
                predicted_runtime_limit_seconds=predicted_seconds,
                initial_after_seconds=parse_duration(
                    _optional_text(
                        forecast_table.get("initial_after"), "forecast.initial_after"
                    )
                    or "1h"
                ),
                interval_seconds=selected_interval,
                minimum_interval_seconds=parse_duration(
                    _optional_text(
                        forecast_table.get("minimum_interval"),
                        "forecast.minimum_interval",
                    )
                    or "30m"
                ),
                percentile=selected_percentile,
                breach_confirmations=_integer(
                    forecast_table.get("breach_confirmations", 2),
                    "forecast.breach_confirmations",
                    1,
                    5,
                ),
                minimum_confidence=_confidence(
                    forecast_table.get("minimum_confidence", "medium")
                ),
            ),
            restart=restart,
            publish_inconclusive=publish_inconclusive,
            headless=headless,
            feedback=feedback,
        )


@dataclass(frozen=True, slots=True)
class InputSnapshot:
    fingerprint: str
    root: Path
    files: tuple[dict[str, object], ...]
    total_bytes: int


@dataclass(frozen=True, slots=True)
class RuntimeLedger:
    active_seconds: int
    active_since: str | None
    model_calls: int

    @classmethod
    def parse(cls, value: object) -> Self:
        if not isinstance(value, dict) or set(value) != {
            "active_seconds",
            "active_since",
            "model_calls",
        }:
            raise SolveError("solve runtime ledger is malformed")
        active = value["active_seconds"]
        calls = value["model_calls"]
        since = value["active_since"]
        if (
            isinstance(active, bool)
            or not isinstance(active, int)
            or active < 0
            or isinstance(calls, bool)
            or not isinstance(calls, int)
            or calls < 0
            or (since is not None and not isinstance(since, str))
        ):
            raise SolveError("solve runtime ledger values are malformed")
        if since is not None:
            _parse_timestamp(since, "runtime active_since")
        return cls(active, since, calls)

    def start(self, now: datetime | None = None) -> Self:
        if self.active_since is not None:
            return self
        return replace(self, active_since=_timestamp(now))

    def pause(self, now: datetime | None = None) -> Self:
        if self.active_since is None:
            return self
        current = now or datetime.now(UTC)
        started = _parse_timestamp(self.active_since, "runtime active_since")
        elapsed = max(0, int((current - started).total_seconds()))
        return replace(
            self, active_seconds=self.active_seconds + elapsed, active_since=None
        )

    def elapsed(self, now: datetime | None = None) -> int:
        if self.active_since is None:
            return self.active_seconds
        current = now or datetime.now(UTC)
        started = _parse_timestamp(self.active_since, "runtime active_since")
        return self.active_seconds + max(0, int((current - started).total_seconds()))

    def with_model_call(self) -> Self:
        return replace(self, model_calls=self.model_calls + 1)

    def to_dict(self) -> dict[str, object]:
        return {
            "active_seconds": self.active_seconds,
            "active_since": self.active_since,
            "model_calls": self.model_calls,
        }


@dataclass(frozen=True, slots=True)
class SemanticContract:
    title: str
    question: str
    definitions: tuple[str, ...]
    domains: tuple[str, ...]
    quantifiers: tuple[str, ...]
    boundary_cases: tuple[str, ...]
    acceptable_outcomes: tuple[str, ...]
    source_dependent_claims: tuple[str, ...]
    prohibited_scope_changes: tuple[str, ...]
    ambiguities: tuple[str, ...]
    completion_description: str

    @classmethod
    def parse(cls, value: object) -> Self:
        required = {
            "schema_version",
            "title",
            "question",
            "definitions",
            "domains",
            "quantifiers",
            "boundary_cases",
            "acceptable_outcomes",
            "source_dependent_claims",
            "prohibited_scope_changes",
            "ambiguities",
            "completion_description",
        }
        table = _strict_object(value, "semantic contract", required)
        if table["schema_version"] != 1:
            raise ConfigurationError("semantic contract schema_version must be 1")
        outcomes = _text_array(table["acceptable_outcomes"], "acceptable outcomes")
        if not outcomes:
            raise ConfigurationError("semantic contract needs an acceptable outcome")
        return cls(
            title=_text(table["title"], "semantic contract title"),
            question=_text(table["question"], "semantic contract question"),
            definitions=_text_array(
                table["definitions"], "semantic contract definitions"
            ),
            domains=_text_array(table["domains"], "semantic contract domains"),
            quantifiers=_text_array(
                table["quantifiers"], "semantic contract quantifiers"
            ),
            boundary_cases=_text_array(
                table["boundary_cases"], "semantic contract boundary cases"
            ),
            acceptable_outcomes=outcomes,
            source_dependent_claims=_text_array(
                table["source_dependent_claims"], "semantic contract source claims"
            ),
            prohibited_scope_changes=_text_array(
                table["prohibited_scope_changes"],
                "semantic contract prohibited changes",
            ),
            ambiguities=_text_array(
                table["ambiguities"], "semantic contract ambiguities"
            ),
            completion_description=_text(
                table["completion_description"],
                "semantic contract completion description",
            ),
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": 1,
            "title": self.title,
            "question": self.question,
            "definitions": list(self.definitions),
            "domains": list(self.domains),
            "quantifiers": list(self.quantifiers),
            "boundary_cases": list(self.boundary_cases),
            "acceptable_outcomes": list(self.acceptable_outcomes),
            "source_dependent_claims": list(self.source_dependent_claims),
            "prohibited_scope_changes": list(self.prohibited_scope_changes),
            "ambiguities": list(self.ambiguities),
            "completion_description": self.completion_description,
        }


@dataclass(frozen=True, slots=True)
class FormalRoot:
    module: str
    declaration: str
    role: Literal["primary", "secondary"]
    theorem_type: str
    informal_statement: str


@dataclass(frozen=True, slots=True)
class FormalContract:
    title: str
    lakefile: str
    author: str
    audience: str
    informal_claim: str
    closing_scope: str
    roots: tuple[FormalRoot, ...]
    build_command: tuple[str, ...]
    verification_commands: tuple[tuple[str, ...], ...]
    allowed_axioms: tuple[str, ...]
    support_files: tuple[str, ...]

    @classmethod
    def parse(cls, value: object) -> Self:
        required = {
            "schema_version",
            "title",
            "lakefile",
            "author",
            "audience",
            "informal_claim",
            "closing_scope",
            "roots",
            "build_command",
            "verification_commands",
            "allowed_axioms",
            "support_files",
        }
        table = _strict_object(value, "formal contract", required)
        if table["schema_version"] != 1:
            raise ConfigurationError("formal contract schema_version must be 1")
        raw_roots = table["roots"]
        if not isinstance(raw_roots, list) or not raw_roots:
            raise ConfigurationError("formal contract roots must be a nonempty array")
        roots: list[FormalRoot] = []
        for index, item in enumerate(raw_roots):
            root = _strict_object(
                item,
                f"formal contract roots[{index}]",
                {"module", "declaration", "role", "type", "informal_statement"},
            )
            role = root["role"]
            if role not in {"primary", "secondary"}:
                raise ConfigurationError(
                    f"formal contract roots[{index}].role is invalid"
                )
            roots.append(
                FormalRoot(
                    module=_lean_name(root["module"], f"roots[{index}].module"),
                    declaration=_lean_name(
                        root["declaration"], f"roots[{index}].declaration"
                    ),
                    role=role,
                    theorem_type=_text(root["type"], f"roots[{index}].type"),
                    informal_statement=_text(
                        root["informal_statement"], f"roots[{index}].informal_statement"
                    ),
                )
            )
        if sum(root.role == "primary" for root in roots) != 1:
            raise ConfigurationError(
                "formal contract must contain exactly one primary root"
            )
        return cls(
            title=_text(table["title"], "formal contract title"),
            lakefile=_safe_path(table["lakefile"], "formal contract lakefile"),
            author=_text(table["author"], "formal contract author"),
            audience=_text(table["audience"], "formal contract audience"),
            informal_claim=_text(
                table["informal_claim"], "formal contract informal claim"
            ),
            closing_scope=_text(
                table["closing_scope"], "formal contract closing scope"
            ),
            roots=tuple(roots),
            build_command=_command(
                table["build_command"], "formal contract build command"
            ),
            verification_commands=_commands(
                table["verification_commands"], "formal contract verification commands"
            ),
            allowed_axioms=_text_array(
                table["allowed_axioms"], "formal contract allowed axioms"
            ),
            support_files=_safe_paths(
                table["support_files"], "formal contract support files"
            ),
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": 1,
            "title": self.title,
            "lakefile": self.lakefile,
            "author": self.author,
            "audience": self.audience,
            "informal_claim": self.informal_claim,
            "closing_scope": self.closing_scope,
            "roots": [
                {
                    "module": root.module,
                    "declaration": root.declaration,
                    "role": root.role,
                    "type": root.theorem_type,
                    "informal_statement": root.informal_statement,
                }
                for root in self.roots
            ],
            "build_command": list(self.build_command),
            "verification_commands": [
                list(command) for command in self.verification_commands
            ],
            "allowed_axioms": list(self.allowed_axioms),
            "support_files": list(self.support_files),
        }


def parse_duration(value: str) -> int:
    match = _DURATION.fullmatch(value.strip())
    if match is None:
        raise ConfigurationError(
            f"invalid duration {value!r}; expected a positive integer followed by s, m, h, d, or w"
        )
    seconds = int(match.group("amount")) * _DURATION_FACTORS[match.group("unit")]
    if not 1 <= seconds <= 10 * 365 * 86400:
        raise ConfigurationError("duration must be between one second and ten years")
    return seconds


def create_input_snapshot(spec: SolveSpec) -> InputSnapshot:
    root = spec.folder
    files: list[Path] = []
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if any(part in _INPUT_EXCLUDES for part in relative.parts):
            continue
        if path.is_symlink():
            raise SolveError(f"solve inputs cannot contain symlinks: {relative}")
        if path.is_file():
            files.append(path)
    if spec.problem not in files:
        raise SolveError("configured problem file is excluded from the solve snapshot")
    digest = hashlib.sha256()
    records: list[dict[str, object]] = []
    total = 0
    for path in files:
        artifact = digest_file(path, relative_to=root)
        relative_bytes = artifact.path.encode("utf-8")
        digest.update(len(relative_bytes).to_bytes(8, "big"))
        digest.update(relative_bytes)
        digest.update(bytes.fromhex(artifact.sha256))
        record: dict[str, object] = {
            "path": artifact.path,
            "sha256": artifact.sha256,
            "size": artifact.size,
        }
        records.append(record)
        total += artifact.size
    if total > 32 * 1024 * 1024 * 1024:
        raise SolveError("solve input snapshot exceeds 32 GiB")
    fingerprint = digest.hexdigest()
    destination = spec.state_root / "input-snapshots" / fingerprint
    if destination.exists():
        if not destination.is_dir() or destination.is_symlink():
            raise SolveError(f"input snapshot path is unsafe: {destination}")
    else:
        destination.mkdir(parents=True)
        for source in files:
            relative = source.relative_to(root)
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
    observed = [
        digest_file(destination / str(item["path"]), relative_to=destination).to_dict()
        for item in records
    ]
    if observed != records:
        raise SolveError("retained input snapshot does not match its source manifest")
    manifest = {
        "schema_version": 1,
        "fingerprint": fingerprint,
        "created_at": utc_now(),
        "source": str(root),
        "problem": spec.problem.relative_to(root).as_posix(),
        "total_bytes": total,
        "files": records,
    }
    atomic_write_json(destination / "INPUTS.json", manifest)
    atomic_write_json(spec.state_root / "input-manifest.json", manifest)
    return InputSnapshot(fingerprint, destination, tuple(records), total)


def predicted_policy_breach(
    forecast: CompletionForecast,
    *,
    ledger: RuntimeLedger,
    policy: ForecastPolicy,
) -> bool:
    limit = policy.predicted_runtime_limit_seconds
    if (
        limit is None
        or _CONFIDENCE_RANK[forecast.confidence]
        < _CONFIDENCE_RANK[policy.minimum_confidence]
    ):
        return False
    return predicted_limit_breached(
        forecast,
        active_seconds=ledger.elapsed(),
        runtime_limit_seconds=limit,
        percentile=policy.percentile,
    )


def _object(value: object, label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ConfigurationError(f"{label} must be a TOML table")
    return value


def _known_keys(value: dict[str, Any], label: str, allowed: set[str]) -> None:
    unknown = set(value) - allowed
    if unknown:
        raise ConfigurationError(f"{label} has unknown keys: {sorted(unknown)}")


def _strict_object(value: object, label: str, keys: set[str]) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        observed = set(value) if isinstance(value, dict) else set()
        raise ConfigurationError(
            f"{label} keys differ; missing={sorted(keys - observed)}, extra={sorted(observed - keys)}"
        )
    return value


def _text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be nonempty text")
    return value.strip()


def _optional_text(value: object, label: str) -> str | None:
    if value is None:
        return None
    return _text(value, label)


def _text_array(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ConfigurationError(f"{label} must be a text array")
    return tuple(item.strip() for item in value)


def _command(value: object, label: str) -> tuple[str, ...]:
    command = _text_array(value, label)
    if not command:
        raise ConfigurationError(f"{label} must not be empty")
    return command


def _commands(value: object, label: str) -> tuple[tuple[str, ...], ...]:
    if not isinstance(value, list):
        raise ConfigurationError(f"{label} must be an array of commands")
    return tuple(
        _command(item, f"{label}[{index}]") for index, item in enumerate(value)
    )


def _safe_paths(value: object, label: str) -> tuple[str, ...]:
    paths = _text_array(value, label)
    for index, item in enumerate(paths):
        path = PurePosixPath(item)
        if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
            raise ConfigurationError(f"{label}[{index}] must be a safe relative path")
    return paths


def _integer(value: object, label: str, minimum: int, maximum: int) -> int:
    if (
        isinstance(value, bool)
        or not isinstance(value, int)
        or not minimum <= value <= maximum
    ):
        raise ConfigurationError(
            f"{label} must be an integer in [{minimum}, {maximum}]"
        )
    return value


def _boolean(value: object, label: str) -> bool:
    if not isinstance(value, bool):
        raise ConfigurationError(f"{label} must be boolean")
    return value


def _safe_path(value: object, label: str) -> str:
    return _safe_paths([value], label)[0]


def _confidence(value: object) -> Literal["low", "medium", "high"]:
    if value not in {"low", "medium", "high"}:
        raise ConfigurationError(
            "forecast.minimum_confidence must be low, medium, or high"
        )
    return value


def _lean_name(value: object, label: str) -> str:
    name = _text(value, label)
    if any(
        not part.replace("_", "a").replace("'", "a").isalnum()
        for part in name.split(".")
    ):
        raise ConfigurationError(f"{label} must be a Lean identifier")
    return name


def _timestamp(now: datetime | None = None) -> str:
    value = now or datetime.now(UTC)
    return value.astimezone(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def _parse_timestamp(value: str, label: str) -> datetime:
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError as exc:
        raise SolveError(f"{label} is malformed") from exc
    if parsed.tzinfo is None:
        raise SolveError(f"{label} has no timezone")
    return parsed.astimezone(UTC)
