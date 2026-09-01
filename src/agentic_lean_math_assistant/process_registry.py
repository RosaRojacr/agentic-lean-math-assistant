"""Durable child-process ownership records for crash recovery."""

from __future__ import annotations

import hashlib
import json
import os
import re
import tempfile
import time
from collections.abc import Callable
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path

from .artifacts import atomic_write_json

_SCHEMA_VERSION = 1
_RUNTIME_ENV = "AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR"
_UNIT_NAME = re.compile(r"campaign-\d+-[0-9a-f]{12}\.service")


@dataclass(frozen=True, slots=True)
class RegisteredRunUnit:
    run_dir: Path
    unit: str
    systemctl: str


@dataclass(frozen=True, slots=True)
class RegisteredRunProcess:
    run_dir: Path
    pid: int
    process_start_time: str
    process_group_id: int
    session_id: int


def _directory() -> Path:
    configured = os.environ.get(_RUNTIME_ENV)
    if configured:
        root = Path(configured).expanduser().resolve()
    else:
        root = Path(os.environ.get("XDG_RUNTIME_DIR", tempfile.gettempdir()))
        root = root / f"agentic-lean-math-assistant-{os.getuid()}"
    return root / "processes"


def _unit_directory() -> Path:
    return _directory().parent / "units"


def _unit_path(unit: str) -> Path:
    digest = hashlib.sha256(unit.encode("utf-8")).hexdigest()
    return _unit_directory() / f"{digest}.json"


def _read_unit(path: Path) -> RegisteredRunUnit:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or set(value) != {
        "schema_version",
        "run_dir",
        "unit",
        "systemctl",
        "registered_at",
    }:
        raise ValueError("sandbox unit registration has invalid keys")
    run_dir = value["run_dir"]
    unit = value["unit"]
    systemctl = value["systemctl"]
    if value["schema_version"] != _SCHEMA_VERSION:
        raise ValueError("sandbox unit registration has an unsupported schema")
    if not isinstance(run_dir, str) or not Path(run_dir).is_absolute():
        raise TypeError("sandbox unit run_dir must be an absolute path")
    if not isinstance(unit, str) or _UNIT_NAME.fullmatch(unit) is None:
        raise TypeError("sandbox unit name is invalid")
    if not isinstance(systemctl, str) or not Path(systemctl).is_absolute():
        raise TypeError("sandbox unit systemctl must be an absolute path")
    return RegisteredRunUnit(Path(run_dir).resolve(), unit, systemctl)


def register_run_unit(run_dir: Path, unit: str, systemctl: str) -> None:
    """Durably associate a not-yet-launched transient unit with its retained run."""
    resolved = run_dir.expanduser().resolve()
    if _UNIT_NAME.fullmatch(unit) is None:
        raise ValueError(f"invalid sandbox unit name: {unit}")
    resolved_systemctl = Path(systemctl).expanduser().resolve()
    if not resolved_systemctl.is_absolute():
        raise ValueError("systemctl path must be absolute")
    directory = _unit_directory()
    directory.mkdir(parents=True, exist_ok=True)
    atomic_write_json(
        _unit_path(unit),
        {
            "schema_version": _SCHEMA_VERSION,
            "run_dir": str(resolved),
            "unit": unit,
            "systemctl": str(resolved_systemctl),
            "registered_at": datetime.now(UTC)
            .isoformat(timespec="seconds")
            .replace("+00:00", "Z"),
        },
    )


def registered_run_units(run_dir: Path) -> tuple[RegisteredRunUnit, ...]:
    """Return every retained sandbox unit owned by one canonical run."""
    resolved = run_dir.expanduser().resolve()
    records: list[RegisteredRunUnit] = []
    directory = _unit_directory()
    for path in directory.glob("*.json") if directory.is_dir() else ():
        try:
            record = _read_unit(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if path == _unit_path(record.unit) and record.run_dir == resolved:
            records.append(record)
    return tuple(sorted(records, key=lambda record: record.unit))


def unregister_run_unit(run_dir: Path, unit: str, systemctl: str) -> bool:
    """Identity-safely remove one verified-inactive sandbox unit registration."""
    path = _unit_path(unit)
    try:
        record = _read_unit(path)
    except FileNotFoundError:
        return False
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        return False
    expected_systemctl = str(Path(systemctl).expanduser().resolve())
    if (
        record.run_dir != run_dir.expanduser().resolve()
        or record.unit != unit
        or record.systemctl != expected_systemctl
    ):
        return False
    path.unlink(missing_ok=True)
    return True


def _process_start_time(pid: int) -> str | None:
    try:
        fields = (
            (Path("/proc") / str(pid) / "stat")
            .read_text(encoding="utf-8")
            .rsplit(") ", maxsplit=1)[1]
            .split()
        )
    except (IndexError, OSError):
        return None
    return fields[19] if len(fields) > 19 else None


def _process_path(record: RegisteredRunProcess) -> Path:
    identity = (
        f"{record.run_dir}\0{record.pid}\0{record.process_start_time}\0"
        f"{record.process_group_id}\0{record.session_id}"
    )
    digest = hashlib.sha256(identity.encode("utf-8")).hexdigest()
    return _directory() / f"{record.pid}-{digest}.json"


def _read_process(path: Path) -> RegisteredRunProcess:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or set(value) != {
        "schema_version",
        "run_dir",
        "pid",
        "process_start_time",
        "process_group_id",
        "session_id",
        "registered_at",
    }:
        raise ValueError("process registration has invalid keys")
    if value["schema_version"] != _SCHEMA_VERSION:
        raise ValueError("process registration has an unsupported schema")
    run_dir = value["run_dir"]
    if not isinstance(run_dir, str) or not Path(run_dir).is_absolute():
        raise TypeError("process registration run_dir must be an absolute path")
    for key in ("pid", "process_group_id", "session_id"):
        if isinstance(value[key], bool) or not isinstance(value[key], int):
            raise TypeError(f"process registration {key} must be an integer")
        if value[key] <= 0:
            raise ValueError(f"process registration {key} must be positive")
    process_start_time = value["process_start_time"]
    if not isinstance(process_start_time, str) or not process_start_time:
        raise TypeError("process registration start time must be a nonempty string")
    return RegisteredRunProcess(
        run_dir=Path(run_dir).resolve(),
        pid=value["pid"],
        process_start_time=process_start_time,
        process_group_id=value["process_group_id"],
        session_id=value["session_id"],
    )


def _prune_dead_process_registrations() -> None:
    directory = _directory()
    for path in directory.glob("*.json") if directory.is_dir() else ():
        try:
            record = _read_process(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if path == _process_path(record):
            unregister_run_process(record)


def register_run_process(run_dir: Path, pid: int) -> RegisteredRunProcess:
    """Durably associate one new-session child process with its retained run."""

    process_start_time = _process_start_time(pid)
    if process_start_time is None:
        raise OSError(f"cannot identify child process {pid}")
    process_group_id = os.getpgid(pid)
    session_id = os.getsid(pid)
    if _process_start_time(pid) != process_start_time:
        raise OSError(f"child process {pid} identity changed during registration")
    if process_group_id != pid or session_id != pid:
        raise ValueError(f"child process {pid} does not own a new session")
    record = RegisteredRunProcess(
        run_dir=run_dir.expanduser().resolve(),
        pid=pid,
        process_start_time=process_start_time,
        process_group_id=process_group_id,
        session_id=session_id,
    )
    directory = _directory()
    directory.mkdir(parents=True, exist_ok=True)
    _prune_dead_process_registrations()
    atomic_write_json(
        _process_path(record),
        {
            "schema_version": _SCHEMA_VERSION,
            "run_dir": str(record.run_dir),
            "pid": record.pid,
            "process_start_time": record.process_start_time,
            "process_group_id": record.process_group_id,
            "session_id": record.session_id,
            "registered_at": datetime.now(UTC)
            .isoformat(timespec="seconds")
            .replace("+00:00", "Z"),
        },
    )
    return record


def _owned_group_is_alive(record: RegisteredRunProcess) -> bool:
    proc = Path("/proc")
    try:
        paths = tuple(proc.iterdir())
    except OSError:
        return True
    for path in paths:
        if not path.name.isdigit():
            continue
        try:
            fields = (
                path.joinpath("stat")
                .read_text(encoding="utf-8")
                .rsplit(") ", maxsplit=1)[1]
                .split()
            )
        except (IndexError, OSError):
            continue
        if (
            len(fields) > 3
            and fields[0] != "Z"
            and fields[2] == str(record.process_group_id)
            and fields[3] == str(record.session_id)
        ):
            return True
    return False


def unregister_run_process(
    record: RegisteredRunProcess, *, wait_timeout: float = 0.0
) -> bool:
    """Remove an exact registration after its owned group exits."""

    if wait_timeout < 0:
        raise ValueError("process unregister wait timeout must not be negative")
    path = _process_path(record)
    try:
        retained = _read_process(path)
    except FileNotFoundError:
        return False
    except (OSError, TypeError, ValueError, json.JSONDecodeError):
        return False
    if retained != record:
        return False
    deadline = time.monotonic() + wait_timeout
    while True:
        current_start = _process_start_time(record.pid)
        if current_start is not None and current_start != record.process_start_time:
            path.unlink(missing_ok=True)
            return True
        if not _owned_group_is_alive(record):
            path.unlink(missing_ok=True)
            return True
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return False
        time.sleep(min(0.02, remaining))


def registered_run_processes(run_dir: Path) -> tuple[RegisteredRunProcess, ...]:
    """Return registered new-session process identities owned by one run."""

    resolved = run_dir.expanduser().resolve()
    directory = _directory()
    result: list[RegisteredRunProcess] = []
    for path in directory.glob("*.json") if directory.is_dir() else ():
        try:
            record = _read_process(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if path == _process_path(record) and record.run_dir == resolved:
            result.append(record)
    return tuple(
        sorted(
            result,
            key=lambda record: (
                record.pid,
                record.process_start_time,
                record.process_group_id,
                record.session_id,
            ),
        )
    )


def registered_run_directories() -> tuple[Path, ...]:
    """Discover canonical runs from exact durable unit and process identities."""

    result: set[Path] = set()
    unit_directory = _unit_directory()
    for path in unit_directory.glob("*.json") if unit_directory.is_dir() else ():
        try:
            unit = _read_unit(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if path == _unit_path(unit.unit):
            result.add(unit.run_dir)
    process_directory = _directory()
    for path in process_directory.glob("*.json") if process_directory.is_dir() else ():
        try:
            process = _read_process(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if path == _process_path(process):
            result.add(process.run_dir)
    return tuple(sorted(result))


def remove_dead_run_registrations(run_dir: Path, alive: Callable[[int], bool]) -> None:
    """Remove exact ownership records only after their full group is gone."""

    del alive
    for record in registered_run_processes(run_dir):
        unregister_run_process(record)
