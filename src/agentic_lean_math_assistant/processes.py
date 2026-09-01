"""Runtime registration and one-call shutdown for unified campaigns."""

from __future__ import annotations

import errno
import fcntl
import hashlib
import json
import os
import select
import signal
import tempfile
import time
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from .artifacts import atomic_write_json, digest_tree
from .herdr import HerdrClient, HerdrError
from .journal import (
    JournalError,
    append_state_snapshot,
    journal_path,
    load_state_snapshot,
)
from .process_registry import (
    RegisteredRunProcess,
    registered_run_directories,
    registered_run_processes,
    registered_run_units,
    unregister_run_process,
    unregister_run_unit,
)
from .sandbox import terminate_sandbox_unit

_SCHEMA_VERSION = 1
_RUNTIME_ENV = "AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR"


@dataclass(frozen=True, slots=True)
class StopReport:
    registrations: int
    workspaces_closed: tuple[str, ...]
    terminated_pids: tuple[int, ...]
    killed_pids: tuple[int, ...]
    errors: tuple[str, ...]

    @property
    def ok(self) -> bool:
        return not self.errors

    def to_dict(self) -> dict[str, object]:
        return asdict(self)


@dataclass(frozen=True, slots=True)
class RunProcessReport:
    terminated_pids: tuple[int, ...]
    killed_pids: tuple[int, ...]
    surviving_pids: tuple[int, ...]
    unit_errors: tuple[str, ...]

    @property
    def ok(self) -> bool:
        return not self.surviving_pids and not self.unit_errors


def _runtime_dir(override: Path | None = None) -> Path:
    if override is not None:
        return override.expanduser().resolve()
    configured = os.environ.get(_RUNTIME_ENV)
    if configured:
        return Path(configured).expanduser().resolve()
    base = Path(os.environ.get("XDG_RUNTIME_DIR", tempfile.gettempdir()))
    return base / f"agentic-lean-math-assistant-{os.getuid()}"


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


def _registration_path(
    pid: int,
    process_start_time: str | None,
    run_dir: Path,
    runtime_dir: Path | None = None,
) -> Path:
    identity = f"{pid}\0{process_start_time}\0{run_dir.resolve()}".encode()
    suffix = hashlib.sha256(identity).hexdigest()[:24]
    return _runtime_dir(runtime_dir) / f"{pid}-{suffix}.json"


def _owned_registration_path(
    pid: int,
    runtime_dir: Path | None = None,
    *,
    required: bool = True,
) -> Path | None:
    registry = _runtime_dir(runtime_dir)
    current_start = _process_start_time(pid)
    matches: list[Path] = []
    for path in registry.glob("*.json") if registry.is_dir() else ():
        try:
            value = _read_registration(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if value["pid"] == pid and value["process_start_time"] == current_start:
            matches.append(path)
    if not matches and not required:
        return None
    if len(matches) != 1:
        raise RuntimeError(
            f"expected exactly one registration for process identity "
            f"{pid}/{current_start}; found {len(matches)}"
        )
    return matches[0]


def register_campaign(
    run_dir: Path,
    herdr_executable: str,
    *,
    pid: int | None = None,
    runtime_dir: Path | None = None,
) -> None:
    process_id = os.getpid() if pid is None else pid
    process_start_time = _process_start_time(process_id)
    atomic_write_json(
        _registration_path(process_id, process_start_time, run_dir, runtime_dir),
        {
            "schema_version": _SCHEMA_VERSION,
            "pid": process_id,
            "process_start_time": process_start_time,
            "run_dir": str(run_dir.resolve()),
            "herdr_executable": herdr_executable,
            "herdr_workspace_id": None,
            "herdr_creation_label": None,
        },
    )


def register_workspace_creation(
    label: str,
    *,
    pid: int | None = None,
    runtime_dir: Path | None = None,
) -> None:
    if not label:
        raise ValueError("Herdr creation label must not be empty")
    process_id = os.getpid() if pid is None else pid
    path = _owned_registration_path(process_id, runtime_dir)
    assert path is not None
    value = _read_registration(path)
    value["herdr_creation_label"] = label
    atomic_write_json(path, value)


def clear_workspace_creation(
    *, pid: int | None = None, runtime_dir: Path | None = None
) -> None:
    process_id = os.getpid() if pid is None else pid
    path = _owned_registration_path(process_id, runtime_dir)
    assert path is not None
    value = _read_registration(path)
    value["herdr_creation_label"] = None
    atomic_write_json(path, value)


def register_workspace(
    workspace_id: str,
    *,
    pid: int | None = None,
    runtime_dir: Path | None = None,
) -> None:
    process_id = os.getpid() if pid is None else pid
    path = _owned_registration_path(process_id, runtime_dir)
    assert path is not None
    value = _read_registration(path)
    value["herdr_workspace_id"] = workspace_id
    atomic_write_json(path, value)


def unregister_campaign(
    *, pid: int | None = None, runtime_dir: Path | None = None
) -> None:
    process_id = os.getpid() if pid is None else pid
    path = _owned_registration_path(process_id, runtime_dir, required=False)
    if path is not None:
        path.unlink(missing_ok=True)


def _read_registration(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    required = {
        "schema_version",
        "pid",
        "process_start_time",
        "run_dir",
        "herdr_executable",
        "herdr_workspace_id",
        "herdr_creation_label",
    }
    if not isinstance(value, dict) or set(value) != required:
        raise ValueError("registration has invalid keys")
    if value["schema_version"] != _SCHEMA_VERSION:
        raise ValueError("registration has an unsupported schema")
    if isinstance(value["pid"], bool) or not isinstance(value["pid"], int):
        raise TypeError("registration pid must be an integer")
    if not isinstance(value["run_dir"], str) or not value["run_dir"]:
        raise TypeError("registration run_dir must be a nonempty string")
    if not isinstance(value["herdr_executable"], str) or not value["herdr_executable"]:
        raise TypeError("registration herdr_executable must be a nonempty string")
    if value["process_start_time"] is not None and not isinstance(
        value["process_start_time"], str
    ):
        raise TypeError("registration process_start_time must be null or a string")
    if value["herdr_workspace_id"] is not None and not isinstance(
        value["herdr_workspace_id"], str
    ):
        raise TypeError("registration herdr_workspace_id must be null or a string")
    if value["herdr_creation_label"] is not None and not isinstance(
        value["herdr_creation_label"], str
    ):
        raise TypeError("registration herdr_creation_label must be null or a string")
    return value


def _process_arguments(pid: int) -> tuple[str, ...]:
    try:
        content = (Path("/proc") / str(pid) / "cmdline").read_bytes()
    except OSError:
        return ()
    return tuple(
        item.decode("utf-8", errors="replace") for item in content.split(b"\0") if item
    )


def _ancestors(pid: int) -> set[int]:
    result: set[int] = set()
    current = pid
    while current > 1:
        try:
            fields = (
                (Path("/proc") / str(current) / "stat")
                .read_text(encoding="utf-8")
                .rsplit(") ", maxsplit=1)[1]
                .split()
            )
            parent = int(fields[1])
        except (IndexError, OSError, ValueError):
            break
        if parent <= 1 or parent in result:
            break
        result.add(parent)
        current = parent
    return result


def registered_workspaces(run_dir: Path) -> tuple[tuple[str, str], ...]:
    """Return Herdr executable/workspace pairs retained for one run."""

    result: set[tuple[str, str]] = set()
    registry = _runtime_dir()
    for path in registry.glob("*.json") if registry.is_dir() else ():
        try:
            value = _read_registration(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if Path(value["run_dir"]).resolve() == run_dir.resolve() and isinstance(
            value["herdr_workspace_id"], str
        ):
            result.add((value["herdr_executable"], value["herdr_workspace_id"]))
    return tuple(sorted(result))


def registered_workspace_intents(run_dir: Path) -> tuple[tuple[str, str], ...]:
    """Return Herdr executable/label creation intents retained for one run."""

    result: set[tuple[str, str]] = set()
    registry = _runtime_dir()
    for path in registry.glob("*.json") if registry.is_dir() else ():
        try:
            value = _read_registration(path)
        except (OSError, TypeError, ValueError, json.JSONDecodeError):
            continue
        if Path(value["run_dir"]).resolve() == run_dir.resolve() and isinstance(
            value["herdr_creation_label"], str
        ):
            result.add((value["herdr_executable"], value["herdr_creation_label"]))
    return tuple(sorted(result))


@dataclass(frozen=True, slots=True)
class _ProcessTarget:
    pid: int
    process_start_time: str
    process_group_id: int | None = None
    session_id: int | None = None


def _run_processes(
    run_dir: Path,
) -> tuple[RegisteredRunProcess | _ProcessTarget, ...]:
    current = os.getpid()
    excluded = _ancestors(current) | {current}
    result: list[RegisteredRunProcess | _ProcessTarget] = [
        record
        for record in registered_run_processes(run_dir)
        if record.pid not in excluded
    ]
    registered_pids = {record.pid for record in result}
    workspace = (run_dir / "workspace").resolve()
    proc = Path("/proc")
    try:
        paths = tuple(proc.iterdir())
    except OSError:
        return tuple(result)
    for path in paths:
        if not path.name.isdigit():
            continue
        pid = int(path.name)
        if pid in excluded or pid in registered_pids:
            continue
        try:
            fields = (
                path.joinpath("stat")
                .read_text(encoding="utf-8")
                .rsplit(") ", maxsplit=1)[1]
                .split()
            )
            cwd = Path(os.readlink(path / "cwd")).resolve()
        except (IndexError, OSError):
            continue
        if (
            len(fields) > 19
            and fields[0] != "Z"
            and fields[1] == "1"
            and (cwd == workspace or cwd.is_relative_to(workspace))
        ):
            result.append(_ProcessTarget(pid=pid, process_start_time=fields[19]))
    return tuple(result)


def _is_alive(pid: int) -> bool:
    try:
        state = (
            (Path("/proc") / str(pid) / "stat")
            .read_text(encoding="utf-8")
            .rsplit(") ", maxsplit=1)[1][0]
        )
    except (IndexError, OSError):
        return False
    return state != "Z"


def _group_members(target: RegisteredRunProcess | _ProcessTarget) -> set[int] | None:
    if target.process_group_id is None or target.session_id is None:
        raise ValueError("process target has no group identity")
    try:
        paths = tuple(Path("/proc").iterdir())
    except OSError:
        return None
    members: set[int] = set()
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
            and fields[2] == str(target.process_group_id)
            and fields[3] == str(target.session_id)
        ):
            members.add(int(path.name))
    return members


def _terminate(
    identities: tuple[RegisteredRunProcess | _ProcessTarget, ...], timeout: float
) -> tuple[set[int], set[int], set[int]]:
    targets = tuple(identities)
    handles: dict[int, int] = {}
    unresolved: set[int] = set()
    pending: set[int] = set()

    for key, target in enumerate(targets):
        pid = target.pid
        try:
            descriptor = os.pidfd_open(pid)
        except ProcessLookupError:
            descriptor = None
        except OSError as exc:
            if exc.errno == errno.ESRCH:
                descriptor = None
            else:
                unresolved.add(key)
                continue
        if descriptor is not None:
            if _process_start_time(pid) != target.process_start_time:
                os.close(descriptor)
                continue
            handles[key] = descriptor
        if target.process_group_id is None:
            if descriptor is not None:
                pending.add(key)
            continue
        if descriptor is None:
            unresolved.add(key)
            continue
        members = _group_members(target)
        if members is None:
            unresolved.add(key)
        elif members:
            pending.add(key)

    def descriptor_alive(descriptor: int) -> bool:
        poller = select.poll()
        poller.register(descriptor, select.POLLIN)
        return not poller.poll(0)

    def alive(key: int) -> bool:
        target = targets[key]
        if target.process_group_id is not None:
            members = _group_members(target)
            if members is None:
                unresolved.add(key)
                return True
            return bool(members)
        descriptor = handles.get(key)
        if descriptor is None:
            return False
        return descriptor_alive(descriptor)

    def send(key: int, signal_number: int) -> bool:
        target = targets[key]
        if target.process_group_id is not None:
            if key not in handles:
                unresolved.add(key)
                return False
            if not descriptor_alive(handles[key]):
                unresolved.add(key)
                return False
            members = _group_members(target)
            if members is None:
                unresolved.add(key)
                return False
            for member in members:
                member_start = _process_start_time(member)
                if member_start is None:
                    continue
                try:
                    descriptor = os.pidfd_open(member)
                except ProcessLookupError:
                    continue
                except OSError as exc:
                    if exc.errno == errno.ESRCH:
                        continue
                    unresolved.add(key)
                    return False
                try:
                    if _process_start_time(member) != member_start:
                        continue
                    if not descriptor_alive(handles[key]):
                        unresolved.add(key)
                        return False
                    signal.pidfd_send_signal(descriptor, signal_number)
                except ProcessLookupError:
                    continue
                except PermissionError:
                    unresolved.add(key)
                    return False
                except OSError as exc:
                    if exc.errno != errno.ESRCH:
                        unresolved.add(key)
                        return False
                finally:
                    os.close(descriptor)
            return True
        try:
            if _process_start_time(target.pid) != target.process_start_time:
                pending.discard(key)
                return False
            signal.pidfd_send_signal(handles[key], signal_number)
        except ProcessLookupError:
            pending.discard(key)
            return True
        except PermissionError:
            unresolved.add(key)
            return False
        except OSError as exc:
            if exc.errno == errno.ESRCH:
                pending.discard(key)
                return True
            unresolved.add(key)
            return False
        return True

    killed: set[int] = set()
    try:
        for key in sorted(pending):
            send(key, signal.SIGTERM)
        deadline = time.monotonic() + timeout
        while pending and time.monotonic() < deadline:
            pending = {key for key in pending if alive(key)}
            if pending:
                time.sleep(0.05)
        for key in sorted(pending):
            if send(key, signal.SIGKILL):
                killed.add(key)
        if pending:
            deadline = time.monotonic() + timeout
            while pending and time.monotonic() < deadline:
                pending = {key for key in pending if alive(key)}
                if pending:
                    time.sleep(0.05)
        survivors = {key for key in pending if alive(key)} | unresolved
        surviving_pids = {targets[key].pid for key in survivors}
        terminated_pids = {
            target.pid for key, target in enumerate(targets) if key not in survivors
        } - surviving_pids
        killed_pids = {targets[key].pid for key in killed} - surviving_pids
        return terminated_pids, killed_pids, surviving_pids
    finally:
        for descriptor in handles.values():
            os.close(descriptor)


def _registered_process_survives(record: RegisteredRunProcess) -> bool:
    current_start = _process_start_time(record.pid)
    if current_start == record.process_start_time:
        if record.process_group_id is None:
            return _is_alive(record.pid)
        members = _group_members(record)
        return members is None or bool(members)
    if current_start is None and record.process_group_id is not None:
        members = _group_members(record)
        return members is None or bool(members)
    return False


def _terminate_registered_units(run_dir: Path) -> tuple[str, ...]:
    errors: list[str] = []
    for record in registered_run_units(run_dir):
        error = terminate_sandbox_unit(record.unit, record.systemctl)
        if error is not None:
            errors.append(error)
            continue
        if not unregister_run_unit(record.run_dir, record.unit, record.systemctl):
            errors.append(
                f"cannot unregister sandbox unit {record.unit}: ownership changed"
            )
    return tuple(errors)


def terminate_run_processes(
    run_dir: Path, *, terminate_timeout: float = 3.0
) -> RunProcessReport:
    if terminate_timeout <= 0:
        raise ValueError("terminate_timeout must be positive")
    unit_errors = _terminate_registered_units(run_dir)
    records = _run_processes(run_dir)
    terminated, killed, survivors = _terminate(records, terminate_timeout)
    registry = _runtime_dir()
    if registry.is_dir():
        for path in registry.glob("*.json"):
            try:
                registration = _read_registration(path)
            except (OSError, TypeError, ValueError, json.JSONDecodeError):
                continue
            expected = registration["process_start_time"]
            if Path(registration["run_dir"]).resolve() == run_dir.resolve() and (
                not isinstance(expected, str)
                or _process_start_time(registration["pid"]) != expected
                or not _is_alive(registration["pid"])
            ):
                path.unlink(missing_ok=True)
    for record in records:
        if isinstance(
            record, RegisteredRunProcess
        ) and not _registered_process_survives(record):
            unregister_run_process(record)
    return RunProcessReport(
        terminated_pids=tuple(sorted(terminated)),
        killed_pids=tuple(sorted(killed)),
        surviving_pids=tuple(sorted(survivors)),
        unit_errors=unit_errors,
    )


def _mark_stopped(run_dir: Path, herdr_closed: bool) -> None:
    lock_path = run_dir / ".campaign.lock"
    descriptor = os.open(
        lock_path, os.O_CREAT | os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW, 0o600
    )
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        _mark_stopped_locked(run_dir, herdr_closed)
    finally:
        os.close(descriptor)


def _mark_stopped_locked(run_dir: Path, herdr_closed: bool) -> None:
    state_path = run_dir / "state.json"
    if journal_path(run_dir).is_file():
        try:
            state = load_state_snapshot(run_dir).state
        except JournalError:
            return
    else:
        try:
            state = json.loads(state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return
    if not isinstance(state, dict):
        return
    status = state.get("status")
    if status in ("running", "awaiting_approval"):
        state["status"] = "stopped"
        state["completed_at"] = (
            datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")
        )
        state["error"] = "Stopped by stop_all_campaigns"
    elif not herdr_closed or state.get("herdr_closed") is True:
        return
    if herdr_closed:
        state["herdr_closed"] = True
    append_state_snapshot(run_dir, state, reason="run:stopped")
    atomic_write_json(state_path, state)
    evidence_path = run_dir / "evidence.json"
    campaign_id = state.get("campaign_id")
    if evidence_path.is_file() and isinstance(campaign_id, str):
        excluded = {
            "evidence.json",
            ".campaign.lock",
            *(
                path.relative_to(run_dir).as_posix()
                for path in (run_dir / "workspace").rglob("*")
                if path.is_file()
            ),
        }
        artifacts = digest_tree(run_dir, exclude=excluded)
        atomic_write_json(
            evidence_path,
            {
                "schema_version": 1,
                "campaign_id": campaign_id,
                "status": str(state.get("status")),
                "generated_at": datetime.now(UTC)
                .isoformat(timespec="seconds")
                .replace("+00:00", "Z"),
                "artifacts": [artifact.to_dict() for artifact in artifacts],
            },
        )


def stop_all_campaigns(
    *, runtime_dir: Path | None = None, terminate_timeout: float = 3.0
) -> StopReport:
    if terminate_timeout <= 0:
        raise ValueError("terminate_timeout must be positive")
    registry = _runtime_dir(runtime_dir)
    paths = sorted(registry.glob("*.json")) if registry.is_dir() else []
    registrations: list[tuple[Path, dict[str, Any]]] = []
    errors: list[str] = []
    for path in paths:
        try:
            registrations.append((path, _read_registration(path)))
        except (OSError, TypeError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"cannot read registration {path}: {exc}")
    closed: list[str] = []
    campaign_run_dirs = tuple(
        Path(value["run_dir"]).resolve() for _, value in registrations
    )
    process_registry_in_scope = runtime_dir is None or _runtime_dir() == registry
    discovered_run_dirs = (
        registered_run_directories() if process_registry_in_scope else ()
    )
    owned_run_dirs = tuple(sorted(set(campaign_run_dirs) | set(discovered_run_dirs)))
    for run_dir in owned_run_dirs:
        errors.extend(_terminate_registered_units(run_dir))
    controllers: list[_ProcessTarget] = []
    closed_by_run: dict[Path, bool] = {}
    for _, value in registrations:
        pid = value["pid"]
        expected = value["process_start_time"]
        if isinstance(expected, str):
            controllers.append(_ProcessTarget(pid, expected))
        run_dir = Path(value["run_dir"]).resolve()
        executable = value["herdr_executable"]
        workspace_ids: set[str] = set()
        workspace_id = value["herdr_workspace_id"]
        if isinstance(workspace_id, str):
            workspace_ids.add(workspace_id)
        creation_label = value["herdr_creation_label"]
        discovered_intent = creation_label is None
        if isinstance(creation_label, str):
            try:
                workspace_ids.update(
                    workspace.workspace_id
                    for workspace in HerdrClient(executable).list_workspaces()
                    if workspace.label == creation_label
                )
            except HerdrError as exc:
                errors.append(
                    f"cannot discover Herdr workspaces labeled {creation_label}: {exc}"
                )
            else:
                discovered_intent = True
        did_close = discovered_intent
        for retained_workspace_id in sorted(workspace_ids):
            try:
                HerdrClient(executable).close_workspace(retained_workspace_id)
            except HerdrError as exc:
                if exc.code != "workspace_not_found":
                    did_close = False
                    errors.append(
                        f"cannot close Herdr workspace {retained_workspace_id}: {exc}"
                    )
            else:
                closed.append(retained_workspace_id)
        closed_by_run[run_dir] = closed_by_run.get(run_dir, True) and did_close
    children: list[RegisteredRunProcess] = []
    for run_dir in owned_run_dirs:
        children.extend(registered_run_processes(run_dir))
    terminated, killed, survivors = _terminate(
        tuple(controllers) + tuple(children), terminate_timeout
    )
    for record in children:
        if not _registered_process_survives(record):
            unregister_run_process(record)
    if survivors:
        errors.append(f"processes survived shutdown: {sorted(survivors)}")
    for run_dir in sorted(set(campaign_run_dirs)):
        _mark_stopped(run_dir, closed_by_run[run_dir])
    for path, value in registrations:
        expected = value["process_start_time"]
        if (
            not isinstance(expected, str)
            or _process_start_time(value["pid"]) != expected
            or not _is_alive(value["pid"])
        ):
            path.unlink(missing_ok=True)
    return StopReport(
        registrations=len(registrations),
        workspaces_closed=tuple(sorted(closed)),
        terminated_pids=tuple(sorted(terminated)),
        killed_pids=tuple(sorted(killed)),
        errors=tuple(errors),
    )
