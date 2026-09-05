"""Bounded subprocess execution with complete process-group cleanup."""

from __future__ import annotations

import hashlib
import os
import signal
import subprocess
import threading
import time
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Protocol, TextIO

from .config import ExecutionSpec
from .process_registry import (
    RegisteredRunProcess,
    register_run_process,
    register_run_unit,
    unregister_run_process,
    unregister_run_unit,
)
from .sandbox import (
    SandboxError,
    SandboxInvocation,
    prepare_sandbox,
    redact_text,
    remove_secret_bearing_files,
    secret_values,
    terminate_sandbox,
    workspace_size_exceeds,
)

_MAX_CAPTURE = 1024 * 1024


class _Digest(Protocol):
    def update(self, value: bytes) -> None: ...

    def hexdigest(self) -> str: ...


@dataclass(slots=True)
class _BoundedCapture:
    chunks: list[str]
    size: int = 0
    truncated: bool = False

    def append(self, chunk: str) -> None:
        remaining = _MAX_CAPTURE - self.size
        if remaining > 0:
            retained = chunk[:remaining]
            self.chunks.append(retained)
            self.size += len(retained)
        if len(chunk) > remaining:
            self.truncated = True


@dataclass(frozen=True, slots=True)
class CapturedCommand:
    exit_code: int | None
    stdout: str
    stderr: str
    stdout_truncated: bool
    stderr_truncated: bool
    error: str | None
    stdout_sha256: str
    stderr_sha256: str
    sandbox: Mapping[str, object]


def _pump_capture(stream: TextIO, capture: _BoundedCapture, digest: _Digest) -> None:
    for chunk in iter(lambda: stream.read(64 * 1024), ""):
        digest.update(chunk.encode("utf-8"))
        capture.append(chunk)
    stream.close()


def _process_exited_without_reaping(process: subprocess.Popen[str]) -> bool:
    try:
        status = os.waitid(
            os.P_PID,
            process.pid,
            os.WEXITED | os.WNOHANG | os.WNOWAIT,
        )
    except ChildProcessError:
        return True
    return status is not None


def _wait_without_reaping(process: subprocess.Popen[str], timeout: float) -> bool:
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if _process_exited_without_reaping(process):
            return True
        time.sleep(0.05)
    return _process_exited_without_reaping(process)


def _signal_process_group(process: subprocess.Popen[str], signal_number: int) -> None:
    if process.returncode is not None:
        return
    try:
        os.killpg(process.pid, signal_number)
    except ProcessLookupError:
        pass


def run_captured_command(
    argv: tuple[str, ...],
    *,
    cwd: Path,
    env: Mapping[str, str],
    timeout: float,
    execution: ExecutionSpec | None = None,
    workspace: Path | None = None,
    allow_workspace_executables: bool = False,
    run_dir: Path | None = None,
    read_paths: tuple[Path, ...] = (),
) -> CapturedCommand:
    """Run one bounded command and reap its entire process group."""
    stdout = _BoundedCapture([])
    stderr = _BoundedCapture([])
    stdout_digest = hashlib.sha256()
    stderr_digest = hashlib.sha256()
    process: subprocess.Popen[str] | None = None
    registered_process: RegisteredRunProcess | None = None
    registered_unit: tuple[Path, str, str] | None = None
    error: str | None = None
    exit_code: int | None = None
    threads: tuple[threading.Thread, ...] = ()
    invocation = SandboxInvocation(
        argv=argv,
        unit=None,
        systemctl=None,
        metadata={
            "enabled": execution.sandbox if execution is not None else False,
            "backend": "preparation-failed" if execution is not None else None,
        },
    )
    cleanup_error: str | None = None
    redactions = secret_values(env, execution)

    def release_registered_unit() -> str | None:
        nonlocal registered_unit
        if registered_unit is None:
            return None
        owner, unit, systemctl = registered_unit
        unit_error = terminate_sandbox(invocation)
        if unit_error is not None:
            return unit_error
        if not unregister_run_unit(owner, unit, systemctl):
            return f"cannot unregister sandbox unit {unit}: ownership changed"
        registered_unit = None
        return None

    try:
        if execution is not None:
            if workspace is None:
                raise SandboxError("sandboxed command requires a workspace")
            invocation = prepare_sandbox(
                argv,
                cwd=cwd,
                workspace=workspace,
                environment=env,
                policy=execution,
                read_paths=read_paths,
                allow_workspace_executables=allow_workspace_executables,
                runtime_max_seconds=timeout,
            )
            if invocation.unit is not None and run_dir is not None:
                assert invocation.systemctl is not None
                register_run_unit(run_dir, invocation.unit, invocation.systemctl)
                registered_unit = (
                    run_dir.expanduser().resolve(),
                    invocation.unit,
                    invocation.systemctl,
                )
        process = subprocess.Popen(
            invocation.argv,
            cwd=cwd,
            env=(
                dict(invocation.environment)
                if invocation.environment is not None
                else dict(env)
            ),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            start_new_session=True,
        )
        if workspace is not None and invocation.unit is None:
            owner = run_dir if run_dir is not None else workspace.parent
            registered_process = register_run_process(owner, process.pid)
        assert process.stdout is not None
        assert process.stderr is not None
        threads = (
            threading.Thread(
                target=_pump_capture,
                args=(process.stdout, stdout, stdout_digest),
                daemon=True,
            ),
            threading.Thread(
                target=_pump_capture,
                args=(process.stderr, stderr, stderr_digest),
                daemon=True,
            ),
        )
        for thread in threads:
            thread.start()
        deadline = time.monotonic() + timeout
        next_workspace_check = 0.0
        while True:
            if _process_exited_without_reaping(process):
                if invocation.unit is None:
                    _signal_process_group(process, signal.SIGTERM)
                    _signal_process_group(process, signal.SIGKILL)
                exit_code = process.wait()
                break
            now = time.monotonic()
            if (
                execution is not None
                and workspace is not None
                and now >= next_workspace_check
            ):
                limit_bytes = execution.workspace_max_mb * 1024 * 1024
                exceeded, _observed = workspace_size_exceeds(workspace, limit_bytes)
                if exceeded:
                    cleanup_error = terminate_sandbox(invocation)
                    _signal_process_group(process, signal.SIGKILL)
                    process.wait()
                    exit_code = 125
                    error = (
                        "workspace exceeded sandbox limit of "
                        f"{execution.workspace_max_mb} MiB"
                    )
                    break
                next_workspace_check = now + 0.25
            if now >= deadline:
                cleanup_error = terminate_sandbox(invocation)
                if invocation.unit is None:
                    _signal_process_group(process, signal.SIGTERM)
                    _wait_without_reaping(process, 10)
                _signal_process_group(process, signal.SIGKILL)
                process.wait()
                exit_code = 124
                error = f"command timed out after {timeout} seconds"
                break
            time.sleep(min(0.25, max(0.0, deadline - now)))
        for thread in threads:
            thread.join(timeout=10)
        if execution is not None and workspace is not None:
            exceeded, _observed = workspace_size_exceeds(
                workspace, execution.workspace_max_mb * 1024 * 1024
            )
            if exceeded:
                exit_code = 125
                error = (
                    "workspace exceeded sandbox limit of "
                    f"{execution.workspace_max_mb} MiB"
                )
        removed = (
            remove_secret_bearing_files(workspace, redactions)
            if (workspace is not None)
            else ()
        )
        if removed:
            exit_code = 126
            error = "secret material was removed from workspace files: " + ", ".join(
                removed
            )
        if cleanup_error is not None:
            error = f"{error}; {cleanup_error}" if error else cleanup_error
    except (OSError, SandboxError) as exc:
        if process is not None:
            cleanup_error = terminate_sandbox(invocation)
            _signal_process_group(process, signal.SIGTERM)
            _signal_process_group(process, signal.SIGKILL)
        error = f"{exc}; {cleanup_error}" if cleanup_error else str(exc)
    except BaseException:
        if process is not None:
            cleanup_error = terminate_sandbox(invocation)
            _signal_process_group(process, signal.SIGTERM)
            _signal_process_group(process, signal.SIGKILL)
        unit_error = release_registered_unit()
        if unit_error is not None:
            cleanup_error = cleanup_error or unit_error
        if registered_process is not None:
            unregister_run_process(registered_process, wait_timeout=1.0)
        if cleanup_error is not None:
            raise SandboxError(cleanup_error)
        raise
    unit_error = release_registered_unit()
    if unit_error is not None:
        cleanup_error = cleanup_error or unit_error
        error = f"{error}; {unit_error}" if error else unit_error
    if registered_process is not None:
        unregister_run_process(registered_process, wait_timeout=1.0)
    return CapturedCommand(
        exit_code=exit_code,
        stdout=redact_text("".join(stdout.chunks), redactions) or "",
        stderr=redact_text("".join(stderr.chunks), redactions) or "",
        stdout_truncated=stdout.truncated,
        stderr_truncated=stderr.truncated,
        error=redact_text(error, redactions),
        stdout_sha256=(
            hashlib.sha256(
                (redact_text("".join(stdout.chunks), redactions) or "").encode()
            ).hexdigest()
            if redactions
            else stdout_digest.hexdigest()
        ),
        stderr_sha256=(
            hashlib.sha256(
                (redact_text("".join(stderr.chunks), redactions) or "").encode()
            ).hexdigest()
            if redactions
            else stderr_digest.hexdigest()
        ),
        sandbox=invocation.metadata,
    )
