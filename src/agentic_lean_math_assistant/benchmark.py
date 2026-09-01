"""Blind outcome benchmarks for the fixed autonomous research regime."""

from __future__ import annotations

import json
import os
import secrets
import sys
import tomllib
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Literal, Self, TextIO

from .agent_runner import RunnerInterrupted
from .artifacts import atomic_write_json, atomic_write_text, digest_file, utc_now
from .command import run_captured_command
from .config import ConfigurationError
from .project import ProjectSpec
from .regime import RegimeOptions, RegimeRunner

ExpectedOutcome = Literal["solved", "unsolved", "blocked"]
SourcePolicy = Literal["checkpoint", "continue"]


def _text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be a nonempty string")
    return value.strip()


def _relative(base: Path, value: object, label: str) -> Path:
    raw = _text(value, label).replace("\\", "/")
    candidate = (base / raw).resolve()
    try:
        candidate.relative_to(base)
    except ValueError as exc:
        raise ConfigurationError(f"{label} escapes the benchmark directory") from exc
    return candidate


@dataclass(frozen=True, slots=True)
class BenchmarkCase:
    case_id: str
    project_manifest: Path
    expected_outcome: ExpectedOutcome
    missing_source_policy: SourcePolicy
    validator: Path | None = None
    validator_timeout: int = 300


@dataclass(frozen=True, slots=True)
class BenchmarkSuite:
    manifest_path: Path
    suite_id: str
    runs_dir: Path
    cases: tuple[BenchmarkCase, ...]

    @classmethod
    def load(cls, path: str | Path) -> Self:
        manifest = Path(path).expanduser().resolve()
        try:
            value = tomllib.loads(manifest.read_text(encoding="utf-8"))
        except OSError as exc:
            raise ConfigurationError(f"cannot read benchmark manifest: {exc}") from exc
        except tomllib.TOMLDecodeError as exc:
            raise ConfigurationError(
                f"benchmark manifest is invalid TOML: {exc}"
            ) from exc
        if not isinstance(value, dict) or set(value) != {
            "schema_version",
            "suite",
            "cases",
        }:
            raise ConfigurationError(
                "benchmark manifest requires exactly schema_version, suite, and cases"
            )
        if value["schema_version"] != 1:
            raise ConfigurationError("benchmark schema_version must be 1")
        suite = value["suite"]
        if not isinstance(suite, dict) or set(suite) != {"id", "runs_dir"}:
            raise ConfigurationError("benchmark suite requires exactly id and runs_dir")
        raw_cases = value["cases"]
        if not isinstance(raw_cases, list) or not raw_cases:
            raise ConfigurationError("benchmark cases must be a nonempty array")
        base = manifest.parent.resolve()
        cases: list[BenchmarkCase] = []
        for index, raw in enumerate(raw_cases):
            label = f"cases[{index}]"
            required = {
                "id",
                "project",
                "expected_outcome",
                "missing_source_policy",
            }
            optional = {"validator", "validator_timeout"}
            if (
                not isinstance(raw, dict)
                or not required <= raw.keys()
                or raw.keys() - required - optional
            ):
                raise ConfigurationError(
                    f"{label} requires id, project, expected_outcome, and "
                    "missing_source_policy, with optional validator and "
                    "validator_timeout"
                )
            expected = raw["expected_outcome"]
            if expected not in ("solved", "unsolved", "blocked"):
                raise ConfigurationError(f"{label}.expected_outcome is invalid")
            policy = raw["missing_source_policy"]
            if policy not in ("checkpoint", "continue"):
                raise ConfigurationError(f"{label}.missing_source_policy is invalid")
            project = _relative(base, raw["project"], f"{label}.project")
            if not project.is_file() or project.is_symlink():
                raise ConfigurationError(
                    f"{label}.project must be a regular non-symlink file: {project}"
                )
            validator: Path | None = None
            timeout = raw.get("validator_timeout", 300)
            if not isinstance(timeout, int) or isinstance(timeout, bool) or timeout < 1:
                raise ConfigurationError(
                    f"{label}.validator_timeout must be a positive integer"
                )
            if "validator" in raw:
                validator = _relative(base, raw["validator"], f"{label}.validator")
                if not validator.is_file() or validator.is_symlink():
                    raise ConfigurationError(
                        f"{label}.validator must be a regular non-symlink file: "
                        f"{validator}"
                    )
            elif "validator_timeout" in raw:
                raise ConfigurationError(
                    f"{label}.validator_timeout requires a validator"
                )
            cases.append(
                BenchmarkCase(
                    case_id=_text(raw["id"], f"{label}.id"),
                    project_manifest=project,
                    expected_outcome=expected,
                    missing_source_policy=policy,
                    validator=validator,
                    validator_timeout=timeout,
                )
            )
        ids = [case.case_id for case in cases]
        if len(ids) != len(set(ids)):
            raise ConfigurationError("benchmark case IDs must be unique")
        return cls(
            manifest_path=manifest,
            suite_id=_text(suite["id"], "suite.id"),
            runs_dir=_relative(base, suite["runs_dir"], "suite.runs_dir"),
            cases=tuple(cases),
        )


@dataclass(frozen=True, slots=True)
class BenchmarkRuntime:
    omp: str = "omp"
    herdr: str = "herdr"
    lake: str = "lake"
    focus: bool = False
    close_herdr: bool = True
    output: TextIO | None = None


def _summary(results: list[dict[str, object]], total: int) -> dict[str, object]:
    completed = len(results)
    passed = sum(item["matched"] is True for item in results)
    errors = sum(item["observed_outcome"] == "error" for item in results)
    false_closures = sum(item["false_closure"] is True for item in results)
    return {
        "cases": total,
        "completed": completed,
        "passed": passed,
        "failed": completed - passed,
        "errors": errors,
        "false_closures": false_closures,
        "accepted": (
            completed == total
            and passed == total
            and errors == 0
            and false_closures == 0
        ),
    }


def _write_report(
    report: Path,
    *,
    suite: BenchmarkSuite,
    run_id: str,
    started_at: str,
    suite_manifest_sha256: str,
    status: Literal["running", "complete"],
    results: list[dict[str, object]],
) -> None:
    atomic_write_json(
        report,
        {
            "schema_version": 3,
            "suite_id": suite.suite_id,
            "suite_manifest": str(suite.manifest_path),
            "suite_manifest_snapshot": "suite.toml",
            "suite_manifest_sha256": suite_manifest_sha256,
            "run_id": run_id,
            "status": status,
            "started_at": started_at,
            "completed_at": utc_now() if status == "complete" else None,
            "summary": _summary(results, len(suite.cases)),
            "cases": results,
        },
    )


def _new_run(runs_dir: Path | None, existing: set[Path]) -> Path | None:
    if runs_dir is None:
        return None
    try:
        candidates = [
            path
            for path in runs_dir.iterdir()
            if path.is_dir() and path not in existing
        ]
    except OSError:
        return None
    return max(candidates, key=lambda path: path.name, default=None)


_CASE_RESULT_KEYS = frozenset(
    {
        "case_id",
        "project_manifest",
        "project_manifest_sha256",
        "expected_outcome",
        "observed_outcome",
        "matched",
        "false_closure",
        "error",
        "run_dir",
        "compute_ledger",
        "validator",
        "validator_sha256",
        "validator_status",
        "validator_receipt",
        "validator_receipt_sha256",
    }
)
_REPORT_KEYS = frozenset(
    {
        "schema_version",
        "suite_id",
        "suite_manifest",
        "suite_manifest_snapshot",
        "suite_manifest_sha256",
        "run_id",
        "status",
        "started_at",
        "completed_at",
        "summary",
        "cases",
    }
)


def _run_hidden_validator(
    case: BenchmarkCase,
    options: BenchmarkRuntime,
    *,
    run: Path,
    benchmark_dir: Path,
    case_index: int,
    expected_sha256: str,
) -> tuple[str, Path, str]:
    assert case.validator is not None
    current = digest_file(case.validator, relative_to=case.validator.parent).sha256
    if current != expected_sha256:
        raise ConfigurationError(
            f"benchmark validator changed during case {case.case_id!r}"
        )
    retained_dir = benchmark_dir / "validators" / f"case-{case_index:03d}"
    retained_dir.mkdir(parents=True, exist_ok=False)
    retained = retained_dir / "validator.py"
    retained.write_bytes(case.validator.read_bytes())
    retained_sha256 = digest_file(retained, relative_to=retained_dir).sha256
    if retained_sha256 != expected_sha256:
        raise ConfigurationError(
            f"retained validator differs for case {case.case_id!r}"
        )
    home = retained_dir / "home"
    home.mkdir()
    command = (
        sys.executable,
        "-I",
        str(retained),
        "--run-dir",
        str(run),
        "--lake",
        options.lake,
    )
    started_at = utc_now()
    captured = run_captured_command(
        command,
        cwd=run,
        env={
            "HOME": str(home),
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": os.environ.get("PATH", ""),
        },
        timeout=case.validator_timeout,
    )
    completed_at = utc_now()
    status = "error"
    result: object = None
    if captured.exit_code == 0 and captured.error is None:
        try:
            result = json.loads(captured.stdout)
        except json.JSONDecodeError:
            result = None
        if (
            isinstance(result, dict)
            and set(result) == {"checks", "status", "summary"}
            and result["status"] in {"passed", "failed"}
            and isinstance(result["summary"], str)
            and isinstance(result["checks"], list)
            and all(isinstance(item, dict) for item in result["checks"])
        ):
            status = result["status"]
    receipt = retained_dir / "receipt.json"
    atomic_write_json(
        receipt,
        {
            "schema_version": 1,
            "case_id": case.case_id,
            "validator_sha256": expected_sha256,
            "command": list(command),
            "started_at": started_at,
            "completed_at": completed_at,
            "exit_code": captured.exit_code,
            "error": captured.error,
            "stdout": captured.stdout,
            "stderr": captured.stderr,
            "stdout_sha256": captured.stdout_sha256,
            "stderr_sha256": captured.stderr_sha256,
            "stdout_truncated": captured.stdout_truncated,
            "stderr_truncated": captured.stderr_truncated,
            "result": result,
            "status": status,
        },
    )
    receipt_sha256 = digest_file(receipt, relative_to=retained_dir).sha256
    return status, receipt, receipt_sha256


def _run_remaining_cases(
    suite: BenchmarkSuite,
    options: BenchmarkRuntime,
    *,
    report: Path,
    run_id: str,
    started_at: str,
    suite_manifest_sha256: str,
    results: list[dict[str, object]],
) -> Path:
    for case_index, case in enumerate(
        suite.cases[len(results) :], start=len(results) + 1
    ):
        run: Path | None = None
        project_runs: Path | None = None
        existing_runs: set[Path] = set()
        error: str | None = None
        manifest_sha256: str | None = None
        validator_sha256: str | None = None
        validator_status: str | None = None
        validator_receipt: Path | None = None
        validator_receipt_sha256: str | None = None
        try:
            manifest_sha256 = digest_file(
                case.project_manifest, relative_to=case.project_manifest.parent
            ).sha256
            if case.validator is not None:
                validator_sha256 = digest_file(
                    case.validator, relative_to=case.validator.parent
                ).sha256
            project = ProjectSpec.load(case.project_manifest)
            project_runs = project.runs_dir
            if project_runs.is_dir():
                existing_runs = set(project_runs.iterdir())
            run = RegimeRunner(
                project,
                RegimeOptions(
                    missing_source_policy=case.missing_source_policy,
                    omp=options.omp,
                    herdr=options.herdr,
                    lake=options.lake,
                    focus=options.focus,
                    close_herdr=options.close_herdr,
                    output=options.output,
                ),
            ).run()
            outcome_path = run / "outcome.json"
            if outcome_path.is_file():
                outcome = json.loads(outcome_path.read_text(encoding="utf-8"))
                observed_value = (
                    outcome.get("status") if isinstance(outcome, dict) else None
                )
                observed = (
                    observed_value if isinstance(observed_value, str) else "invalid"
                )
            else:
                observed = "checkpoint"
            if case.validator is not None:
                assert validator_sha256 is not None
                (
                    validator_status,
                    validator_receipt,
                    validator_receipt_sha256,
                ) = _run_hidden_validator(
                    case,
                    options,
                    run=run,
                    benchmark_dir=report.parent,
                    case_index=case_index,
                    expected_sha256=validator_sha256,
                )
                if validator_status == "error":
                    observed = "error"
                    error = "hidden benchmark validator did not return a valid result"
        except RunnerInterrupted:
            raise
        except Exception as exc:  # noqa: BLE001 - each benchmark case is isolated
            run = run or _new_run(project_runs, existing_runs)
            observed = "error"
            error = f"{type(exc).__name__}: {exc}"
        validator_passed = case.validator is None or validator_status == "passed"
        matched = observed == case.expected_outcome and validator_passed
        false_closure = observed == "solved" and (
            case.expected_outcome != "solved" or not validator_passed
        )
        results.append(
            {
                "case_id": case.case_id,
                "project_manifest": str(case.project_manifest),
                "project_manifest_sha256": manifest_sha256,
                "expected_outcome": case.expected_outcome,
                "observed_outcome": observed,
                "matched": matched,
                "false_closure": false_closure,
                "error": error,
                "run_dir": str(run) if run is not None else None,
                "compute_ledger": (
                    str(run / "compute-ledger.json")
                    if run is not None and (run / "compute-ledger.json").is_file()
                    else None
                ),
                "validator": (
                    str(case.validator) if case.validator is not None else None
                ),
                "validator_sha256": validator_sha256,
                "validator_status": validator_status,
                "validator_receipt": (
                    str(validator_receipt) if validator_receipt is not None else None
                ),
                "validator_receipt_sha256": validator_receipt_sha256,
            }
        )
        _write_report(
            report,
            suite=suite,
            run_id=run_id,
            started_at=started_at,
            suite_manifest_sha256=suite_manifest_sha256,
            status="running",
            results=results,
        )
    _write_report(
        report,
        suite=suite,
        run_id=run_id,
        started_at=started_at,
        suite_manifest_sha256=suite_manifest_sha256,
        status="complete",
        results=results,
    )
    return report


def _optional_report_path(value: object, label: str) -> None:
    if value is not None and (not isinstance(value, str) or not value):
        raise ConfigurationError(f"{label} must be null or a nonempty path")


def _load_resume_state(
    report_path: str | Path,
) -> tuple[BenchmarkSuite, Path, str, str, str, list[dict[str, object]]]:
    report = Path(report_path).expanduser().resolve()
    try:
        value = json.loads(report.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ConfigurationError(f"cannot read benchmark report: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ConfigurationError(f"benchmark report is invalid JSON: {exc}") from exc
    if not isinstance(value, dict) or set(value) != _REPORT_KEYS:
        raise ConfigurationError(
            "benchmark report does not match the schema-v3 contract"
        )
    if value["schema_version"] != 3:
        raise ConfigurationError("benchmark report schema_version must be 3")
    if value["status"] != "running" or value["completed_at"] is not None:
        raise ConfigurationError("only an incomplete running benchmark can be resumed")
    run_id = _text(value["run_id"], "benchmark report run_id")
    if report.parent.name != run_id:
        raise ConfigurationError("benchmark report run_id does not match its directory")
    manifest = (
        Path(_text(value["suite_manifest"], "benchmark report suite_manifest"))
        .expanduser()
        .resolve()
    )
    snapshot = _relative(
        report.parent,
        value["suite_manifest_snapshot"],
        "benchmark report suite_manifest_snapshot",
    )
    if not snapshot.is_file() or snapshot.is_symlink():
        raise ConfigurationError(
            "benchmark suite snapshot must be a retained regular file"
        )
    manifest_sha256 = _text(
        value["suite_manifest_sha256"], "benchmark report suite_manifest_sha256"
    )
    try:
        current_manifest_sha256 = digest_file(
            manifest, relative_to=manifest.parent
        ).sha256
        snapshot_sha256 = digest_file(snapshot, relative_to=report.parent).sha256
    except OSError as exc:
        raise ConfigurationError(
            f"cannot verify benchmark suite identity: {exc}"
        ) from exc
    if current_manifest_sha256 != manifest_sha256 or snapshot_sha256 != manifest_sha256:
        raise ConfigurationError("benchmark suite changed after the run started")
    suite = BenchmarkSuite.load(manifest)
    if _text(value["suite_id"], "benchmark report suite_id") != suite.suite_id:
        raise ConfigurationError(
            "benchmark report suite_id does not match its manifest"
        )
    if report.parent.parent.resolve() != suite.runs_dir:
        raise ConfigurationError("benchmark report is outside its configured runs_dir")
    started_at = _text(value["started_at"], "benchmark report started_at")
    raw_results = value["cases"]
    if not isinstance(raw_results, list) or len(raw_results) >= len(suite.cases):
        raise ConfigurationError(
            "benchmark report must contain a strict prefix of suite cases"
        )
    results: list[dict[str, object]] = []
    for index, raw in enumerate(raw_results):
        label = f"benchmark report cases[{index}]"
        if not isinstance(raw, dict) or set(raw) != _CASE_RESULT_KEYS:
            raise ConfigurationError(f"{label} does not match the case-result contract")
        case = suite.cases[index]
        observed = _text(raw["observed_outcome"], f"{label}.observed_outcome")
        if (
            raw["case_id"] != case.case_id
            or raw["expected_outcome"] != case.expected_outcome
            or raw["project_manifest"] != str(case.project_manifest)
            or raw["validator"]
            != (str(case.validator) if case.validator is not None else None)
        ):
            raise ConfigurationError(f"{label} does not match the frozen suite prefix")
        validator_status = raw["validator_status"]
        if validator_status not in {None, "passed", "failed", "error"}:
            raise ConfigurationError(f"{label}.validator_status is invalid")
        validator_passed = case.validator is None or validator_status == "passed"
        expected_match = observed == case.expected_outcome and validator_passed
        expected_false_closure = observed == "solved" and (
            case.expected_outcome != "solved" or not validator_passed
        )
        if (
            not isinstance(raw["matched"], bool)
            or raw["matched"] != expected_match
            or not isinstance(raw["false_closure"], bool)
            or raw["false_closure"] != expected_false_closure
        ):
            raise ConfigurationError(f"{label} has inconsistent outcome scoring")
        if raw["error"] is not None and not isinstance(raw["error"], str):
            raise ConfigurationError(f"{label}.error must be null or a string")
        _optional_report_path(raw["run_dir"], f"{label}.run_dir")
        _optional_report_path(raw["compute_ledger"], f"{label}.compute_ledger")
        retained_sha256 = raw["project_manifest_sha256"]
        if retained_sha256 is None:
            if observed != "error":
                raise ConfigurationError(
                    f"{label}.project_manifest_sha256 is unexpectedly null"
                )
        elif not isinstance(retained_sha256, str):
            raise ConfigurationError(
                f"{label}.project_manifest_sha256 must be null or a string"
            )
        else:
            try:
                current_sha256 = digest_file(
                    case.project_manifest, relative_to=case.project_manifest.parent
                ).sha256
            except OSError as exc:
                raise ConfigurationError(
                    f"cannot verify {label} project manifest: {exc}"
                ) from exc
            if current_sha256 != retained_sha256:
                raise ConfigurationError(
                    f"{label} project manifest changed after completion"
                )
        validator_sha256 = raw["validator_sha256"]
        receipt_value = raw["validator_receipt"]
        receipt_sha256 = raw["validator_receipt_sha256"]
        if case.validator is None:
            if any(
                item is not None
                for item in (
                    validator_sha256,
                    validator_status,
                    receipt_value,
                    receipt_sha256,
                )
            ):
                raise ConfigurationError(
                    f"{label} unexpectedly retains validator evidence"
                )
        elif validator_sha256 is not None:
            if not isinstance(validator_sha256, str):
                raise ConfigurationError(
                    f"{label}.validator_sha256 must be null or a string"
                )
            current_validator_sha256 = digest_file(
                case.validator, relative_to=case.validator.parent
            ).sha256
            if current_validator_sha256 != validator_sha256:
                raise ConfigurationError(f"{label} validator changed after completion")
            if validator_status is not None:
                receipt = (
                    Path(_text(receipt_value, f"{label}.validator_receipt"))
                    .expanduser()
                    .resolve()
                )
                try:
                    receipt.relative_to(report.parent)
                except ValueError as exc:
                    raise ConfigurationError(
                        f"{label} validator receipt is outside the benchmark run"
                    ) from exc
                if not receipt.is_file() or receipt.is_symlink():
                    raise ConfigurationError(
                        f"{label} validator receipt is not a retained regular file"
                    )
                if (
                    not isinstance(receipt_sha256, str)
                    or digest_file(receipt, relative_to=report.parent).sha256
                    != receipt_sha256
                ):
                    raise ConfigurationError(
                        f"{label} validator receipt changed after completion"
                    )
        elif observed != "error":
            raise ConfigurationError(f"{label}.validator_sha256 is unexpectedly null")
        results.append(dict(raw))
    if value["summary"] != _summary(results, len(suite.cases)):
        raise ConfigurationError("benchmark report summary does not match its cases")
    return suite, report, run_id, started_at, manifest_sha256, results


def run_benchmark_suite(
    suite: BenchmarkSuite, runtime: BenchmarkRuntime | None = None
) -> Path:
    """Start a benchmark without exposing expected outcomes to campaign agents."""
    options = runtime or BenchmarkRuntime()
    suite.runs_dir.mkdir(parents=True, exist_ok=True)
    run_id = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + f"-{secrets.token_hex(3)}"
    benchmark_dir = suite.runs_dir / run_id
    benchmark_dir.mkdir()
    suite_snapshot = benchmark_dir / "suite.toml"
    atomic_write_text(suite_snapshot, suite.manifest_path.read_text(encoding="utf-8"))
    suite_manifest_sha256 = digest_file(
        suite_snapshot, relative_to=benchmark_dir
    ).sha256
    report = benchmark_dir / "benchmark-report.json"
    started_at = utc_now()
    results: list[dict[str, object]] = []
    _write_report(
        report,
        suite=suite,
        run_id=run_id,
        started_at=started_at,
        suite_manifest_sha256=suite_manifest_sha256,
        status="running",
        results=results,
    )
    return _run_remaining_cases(
        suite,
        options,
        report=report,
        run_id=run_id,
        started_at=started_at,
        suite_manifest_sha256=suite_manifest_sha256,
        results=results,
    )


def resume_benchmark_suite(
    report_path: str | Path, runtime: BenchmarkRuntime | None = None
) -> Path:
    """Resume only the unrecorded suffix of a verified running benchmark."""
    suite, report, run_id, started_at, manifest_sha256, results = _load_resume_state(
        report_path
    )
    return _run_remaining_cases(
        suite,
        runtime or BenchmarkRuntime(),
        report=report,
        run_id=run_id,
        started_at=started_at,
        suite_manifest_sha256=manifest_sha256,
        results=results,
    )
