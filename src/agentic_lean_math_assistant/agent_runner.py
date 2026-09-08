"""Pane-local OMP process runner with durable output and receipt capture."""

from __future__ import annotations

import argparse
import io
import json
import os
import signal
import subprocess
import sys
import tempfile
import threading
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, TextIO, cast

from .command import (
    _process_exited_without_reaping,
    _signal_process_group,
)
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
from .terminal_status import PaneHeartbeat

_MAX_CAPTURE = 1024 * 1024


class RunnerInterrupted(RuntimeError):
    def __init__(self, signal_number: int) -> None:
        super().__init__(f"runner interrupted by signal {signal_number}")
        self.signal_number = signal_number


def _timestamp() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def _atomic_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def _atomic_json(path: Path, value: object) -> None:
    _atomic_text(
        path,
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
    )


def _request(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read runner request {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise TypeError("runner request must be a JSON object")
    required = {
        "role_id",
        "attempt",
        "omp",
        "workspace",
        "run_dir",
        "prompt",
        "output",
        "stdout_log",
        "stderr_log",
        "receipt",
        "tools",
        "model",
        "thinking",
        "max_time",
    }
    optional = {
        "execution",
        "handoff",
        "empty_output_retries",
        "sandbox_read_paths",
        "workspace_executables",
    }
    if not required <= set(value) or set(value) - required - optional:
        raise ValueError(
            "runner request keys differ: expected required keys "
            f"{sorted(required)} and optional keys {sorted(optional)}, got {sorted(value)}"
        )
    return value


def _path(value: object, name: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a nonempty path string")
    return Path(value).expanduser().resolve()


class _StreamingRedactor:
    def __init__(self, secrets: tuple[str, ...]) -> None:
        self.secrets = secrets
        self.pending = ""
        self.max_length = max((len(secret) for secret in secrets), default=0)

    def feed(self, chunk: str, *, final: bool = False) -> str:
        if not self.secrets:
            return chunk
        data = self.pending + chunk
        safe_start_limit = (
            len(data) if final else max(0, len(data) - self.max_length + 1)
        )
        output: list[str] = []
        position = 0
        while position < safe_start_limit:
            matched = next(
                (
                    secret
                    for secret in self.secrets
                    if data.startswith(secret, position)
                ),
                None,
            )
            if matched is not None:
                output.append("[REDACTED]")
                position += len(matched)
            else:
                output.append(data[position])
                position += 1
        self.pending = data[position:]
        return "".join(output)


def _pump(
    stream: TextIO,
    destination: TextIO,
    chunks: list[str],
    captured: list[int],
    truncated: list[bool],
    heartbeat: PaneHeartbeat,
    redactions: tuple[str, ...],
    *,
    prefix: str,
) -> None:
    redactor = _StreamingRedactor(redactions)
    for raw in iter(lambda: stream.read(64 * 1024), ""):
        chunk = redactor.feed(raw)
        _retain_and_write(
            chunk, destination, chunks, captured, truncated, heartbeat, prefix
        )
    _retain_and_write(
        redactor.feed("", final=True),
        destination,
        chunks,
        captured,
        truncated,
        heartbeat,
        prefix,
    )
    stream.close()


def _retain_and_write(
    value: str,
    destination: TextIO,
    chunks: list[str],
    captured: list[int],
    truncated: list[bool],
    heartbeat: PaneHeartbeat,
    prefix: str,
) -> None:
    remaining = _MAX_CAPTURE - captured[0]
    if remaining > 0:
        retained = value[:remaining]
        chunks.append(retained)
        captured[0] += len(retained)
        if len(retained) != len(value):
            truncated[0] = True
    elif value:
        truncated[0] = True
    heartbeat.write(destination, f"{prefix}{value}")


class _LiveLog(io.TextIOBase):
    """Tee subprocess output to the console and a followable retained file."""

    def __init__(self, console: TextIO, path: Path) -> None:
        self.console = console
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text("", encoding="utf-8")

    def write(self, text: str) -> int:
        self.console.write(text)
        with self.path.open("a", encoding="utf-8") as stream:
            stream.write(text)
            stream.flush()
        return len(text)

    def flush(self) -> None:
        self.console.flush()


def _invoke(
    command: list[str],
    workspace: Path,
    heartbeat: PaneHeartbeat,
    max_time: int,
    execution: ExecutionSpec | None = None,
    read_paths: tuple[Path, ...] = (),
    allow_workspace_executables: bool = False,
    run_dir: Path | None = None,
    stdout_destination: TextIO | None = None,
    stderr_destination: TextIO | None = None,
) -> tuple[int, str, str, bool, bool, str | None, dict[str, object]]:
    stdout_chunks: list[str] = []
    stderr_chunks: list[str] = []
    stdout_truncated = [False]
    stderr_truncated = [False]
    exit_code = 1
    stdout_target = stdout_destination or sys.stdout
    stderr_target = stderr_destination or sys.stderr
    error: str | None = None
    process: subprocess.Popen[str] | None = None
    registered_process: RegisteredRunProcess | None = None
    registered_unit: tuple[Path, str, str] | None = None
    previous_handlers: dict[int, Any] = {}
    invocation = SandboxInvocation(
        argv=tuple(command),
        unit=None,
        systemctl=None,
        metadata={
            "enabled": execution.sandbox if execution is not None else False,
            "backend": "preparation-failed" if execution is not None else None,
        },
    )
    cgroup_error: str | None = None
    interrupted_signal: int | None = None
    redactions = secret_values(os.environ, execution)

    def interrupt(signal_number: int, _frame: object) -> None:
        raise RunnerInterrupted(signal_number)

    if threading.current_thread() is threading.main_thread():
        for handled_signal in (
            signal.SIGHUP,
            signal.SIGINT,
            signal.SIGQUIT,
            signal.SIGTERM,
        ):
            previous_handlers[handled_signal] = signal.signal(handled_signal, interrupt)
    try:
        if execution is not None:
            invocation = prepare_sandbox(
                tuple(command),
                cwd=workspace,
                workspace=workspace,
                environment=os.environ,
                policy=execution,
                read_paths=read_paths,
                allow_workspace_executables=allow_workspace_executables,
                runtime_max_seconds=max_time + 60,
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
            cwd=workspace,
            env=(
                dict(invocation.environment)
                if invocation.environment is not None
                else dict(os.environ)
            ),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            start_new_session=True,
        )
        owner = run_dir if run_dir is not None else workspace.parent
        registered_process = register_run_process(owner, process.pid)
        assert process.stdout is not None
        assert process.stderr is not None
        stdout_thread = threading.Thread(
            target=_pump,
            args=(
                process.stdout,
                stdout_target,
                stdout_chunks,
                [0],
                stdout_truncated,
                heartbeat,
                redactions,
            ),
            kwargs={"prefix": ""},
            daemon=True,
        )
        stderr_thread = threading.Thread(
            target=_pump,
            args=(
                process.stderr,
                stderr_target,
                stderr_chunks,
                [0],
                stderr_truncated,
                heartbeat,
                redactions,
            ),
            kwargs={"prefix": ""},
            daemon=True,
        )
        stdout_thread.start()
        stderr_thread.start()
        deadline = time.monotonic() + max_time + 60
        next_workspace_check = 0.0
        while True:
            if _process_exited_without_reaping(process):
                if invocation.unit is None:
                    _signal_process_group(process, signal.SIGTERM)
                    _signal_process_group(process, signal.SIGKILL)
                exit_code = process.wait()
                break
            now = time.monotonic()
            if now >= deadline:
                cgroup_error = terminate_sandbox(invocation)
                _signal_process_group(process, signal.SIGKILL)
                process.wait()
                exit_code = 124
                error = f"OMP exceeded the runner deadline of {max_time + 60} seconds"
                break
            if execution is not None and now >= next_workspace_check:
                exceeded, _observed = workspace_size_exceeds(
                    workspace, execution.workspace_max_mb * 1024 * 1024
                )
                if exceeded:
                    cgroup_error = terminate_sandbox(invocation)
                    _signal_process_group(process, signal.SIGKILL)
                    process.wait()
                    exit_code = 125
                    error = (
                        "workspace exceeded sandbox limit of "
                        f"{execution.workspace_max_mb} MiB"
                    )
                    break
                next_workspace_check = time.monotonic() + 1.0
            time.sleep(min(0.25, max(0.0, deadline - now)))
        stdout_thread.join(timeout=10)
        stderr_thread.join(timeout=10)
        if execution is not None:
            exceeded, _observed = workspace_size_exceeds(
                workspace, execution.workspace_max_mb * 1024 * 1024
            )
            if exceeded:
                exit_code = 125
                error = (
                    "workspace exceeded sandbox limit of "
                    f"{execution.workspace_max_mb} MiB"
                )
    except RunnerInterrupted as exc:
        if process is not None:
            cgroup_error = terminate_sandbox(invocation)
            try:
                os.killpg(process.pid, signal.SIGTERM)
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            if process.poll() is None:
                process.wait()
        error = str(exc)
        exit_code = 128 + exc.signal_number
        interrupted_signal = exc.signal_number
    except (OSError, SandboxError) as exc:
        if process is not None:
            cgroup_error = terminate_sandbox(invocation)
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        error = f"cannot execute OMP: {exc}"
        exit_code = 127
    except BaseException:
        if process is not None:
            cgroup_error = terminate_sandbox(invocation)
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        if cgroup_error is not None:
            raise SandboxError(cgroup_error)
        raise
    finally:
        if registered_unit is not None:
            owner, unit, systemctl = registered_unit
            unit_error = terminate_sandbox(invocation)
            if unit_error is None:
                if not unregister_run_unit(owner, unit, systemctl):
                    unit_error = (
                        f"cannot unregister sandbox unit {unit}: ownership changed"
                    )
                else:
                    registered_unit = None
            if unit_error is not None:
                cgroup_error = cgroup_error or unit_error
        if registered_process is not None:
            unregister_run_process(registered_process, wait_timeout=1.0)
        for registered_signal, previous in previous_handlers.items():
            signal.signal(registered_signal, previous)
        removed = remove_secret_bearing_files(workspace, redactions)
        if removed:
            exit_code = 126
            cleanup_error = (
                "secret material was removed from workspace files: "
                + ", ".join(removed)
            )
            error = f"{error}; {cleanup_error}" if error else cleanup_error
        if cgroup_error is not None:
            error = f"{error}; {cgroup_error}" if error else cgroup_error
    invocation_metadata = dict(invocation.metadata)
    if interrupted_signal is not None:
        invocation_metadata["interrupted_signal"] = interrupted_signal
    return (
        exit_code,
        "".join(stdout_chunks),
        "".join(stderr_chunks),
        stdout_truncated[0],
        stderr_truncated[0],
        redact_text(error, redactions),
        invocation_metadata,
    )


def _bounded_capture(chunks: list[str]) -> tuple[str, bool]:
    retained: list[str] = []
    remaining = _MAX_CAPTURE
    truncated = False
    for chunk in chunks:
        if remaining <= 0:
            truncated = truncated or bool(chunk)
            continue
        part = chunk[:remaining]
        retained.append(part)
        remaining -= len(part)
        truncated = truncated or len(part) != len(chunk)
    return "".join(retained), truncated


def execute(request_path: Path) -> int:
    request = _request(request_path)
    role_id = request["role_id"]
    attempt = request["attempt"]
    if not isinstance(role_id, str) or not role_id:
        raise ValueError("role_id must be a nonempty string")
    if isinstance(attempt, bool) or not isinstance(attempt, int) or attempt < 1:
        raise ValueError("attempt must be a positive integer")
    omp = request["omp"]
    if not isinstance(omp, str) or not omp:
        raise ValueError("omp must be a nonempty executable string")
    workspace = _path(request["workspace"], "workspace")
    run_dir = _path(request["run_dir"], "run_dir")
    prompt = _path(request["prompt"], "prompt")
    output = _path(request["output"], "output")
    handoff_value = request.get("handoff")
    handoff = _path(handoff_value, "handoff") if handoff_value is not None else None
    if handoff is not None:
        try:
            handoff.relative_to(workspace)
        except ValueError as exc:
            raise ValueError("handoff must be inside workspace") from exc
    stdout_log = _path(request["stdout_log"], "stdout_log")
    stderr_log = _path(request["stderr_log"], "stderr_log")
    receipt = _path(request["receipt"], "receipt")
    tools = request["tools"]
    if not isinstance(tools, list) or not all(
        isinstance(tool, str) and tool for tool in tools
    ):
        raise ValueError("tools must be an array of nonempty strings")
    model = request["model"]
    thinking = request["thinking"]
    if model is not None and (not isinstance(model, str) or not model):
        raise ValueError("model must be null or a nonempty string")
    if thinking is not None and (not isinstance(thinking, str) or not thinking):
        raise ValueError("thinking must be null or a nonempty string")
    max_time = request["max_time"]
    if isinstance(max_time, bool) or not isinstance(max_time, int) or max_time < 30:
        raise ValueError("max_time must be an integer of at least 30 seconds")
    empty_output_retries = request.get("empty_output_retries", 0)
    if (
        isinstance(empty_output_retries, bool)
        or not isinstance(empty_output_retries, int)
        or not 0 <= empty_output_retries <= 3
    ):
        raise ValueError("empty_output_retries must be an integer from 0 to 3")
    execution_value = request.get("execution")
    execution = (
        ExecutionSpec.from_table(execution_value, request_path.parent, resolved=True)
        if execution_value is not None
        else None
    )
    sandbox_read_value = request.get("sandbox_read_paths", [])
    if not isinstance(sandbox_read_value, list) or not all(
        isinstance(value, str) and value for value in sandbox_read_value
    ):
        raise ValueError("sandbox_read_paths must be an array of path strings")
    sandbox_read_paths = tuple(
        _path(value, "sandbox_read_paths entry") for value in sandbox_read_value
    )
    workspace_executables = request.get("workspace_executables", True)
    if not isinstance(workspace_executables, bool):
        raise TypeError("workspace_executables must be a boolean")

    command = [
        omp,
        "--mode=text",
        "--print",
        "--no-session",
        "--auto-approve",
        f"--max-time={max_time}",
        f"--cwd={workspace}",
    ]
    if tools:
        command.append(f"--tools={','.join(tools)}")
    else:
        command.append("--no-tools")
    if model is not None:
        command.append(f"--model={model}")
    if thinking is not None:
        command.append(f"--thinking={thinking}")
    command.append(f"@{prompt}")

    started_at = _timestamp()
    started = time.monotonic()
    invocations: list[dict[str, object]] = []
    receipt_base: dict[str, object] = {
        "schema_version": 1,
        "role_id": role_id,
        "attempt": attempt,
        "started_at": started_at,
        "command": command,
        "handoff": str(handoff) if handoff is not None else None,
        "empty_output_retries": empty_output_retries,
    }
    _atomic_json(receipt, {**receipt_base, "status": "running", "invocations": []})
    print(f"[{role_id}] attempt {attempt} starting", flush=True)
    heartbeat = PaneHeartbeat(role_id)
    heartbeat.start()
    live_stdout = cast(TextIO, _LiveLog(sys.stdout, stdout_log))
    live_stderr = cast(TextIO, _LiveLog(sys.stderr, stderr_log))
    stdout_captures: list[str] = []
    stderr_captures: list[str] = []
    final_stdout = ""
    exit_code = 1
    status = "failed"
    error: str | None = None
    interrupted_signal: int | None = None
    for ordinal in range(1, empty_output_retries + 2):
        invocation_started = time.monotonic()
        (
            exit_code,
            invocation_stdout,
            invocation_stderr,
            invocation_stdout_truncated,
            invocation_stderr_truncated,
            error,
            sandbox,
        ) = _invoke(
            command,
            workspace,
            heartbeat,
            max_time,
            execution,
            sandbox_read_paths,
            workspace_executables,
            run_dir,
            stdout_destination=live_stdout,
            stderr_destination=live_stderr,
        )
        signal_value = sandbox.get("interrupted_signal")
        if isinstance(signal_value, int) and not isinstance(signal_value, bool):
            interrupted_signal = signal_value
        stdout_captures.append(invocation_stdout)
        stderr_captures.append(invocation_stderr)
        final_stdout = invocation_stdout
        deadline_exceeded = (
            exit_code == 124 or "deadline exceeded" in invocation_stderr.casefold()
        )
        if exit_code == 0 and invocation_stdout.strip():
            status = "succeeded"
            error = None
        elif deadline_exceeded:
            status = "timed_out"
            error = f"OMP deadline exceeded after {max_time} seconds"
        else:
            status = "failed"
            if error is None:
                error = (
                    f"OMP exited with {exit_code}"
                    if invocation_stdout.strip()
                    else f"OMP exited with {exit_code} and produced no output"
                )
        invocations.append(
            {
                "ordinal": ordinal,
                "exit_code": exit_code,
                "status": status,
                "error": error,
                "duration_seconds": round(time.monotonic() - invocation_started, 3),
                "stdout_truncated": invocation_stdout_truncated,
                "stderr_truncated": invocation_stderr_truncated,
                "sandbox": sandbox,
            }
        )
        blank_output = (
            exit_code >= 0
            and not invocation_stdout.strip()
            and not deadline_exceeded
            and interrupted_signal is None
        )
        if blank_output and ordinal <= empty_output_retries:
            _atomic_json(
                receipt,
                {
                    **receipt_base,
                    "status": "running",
                    "invocations": invocations,
                },
            )
            print(
                f"[{role_id}] attempt {attempt} produced no output; "
                f"retrying OMP ({ordinal}/{empty_output_retries})",
                flush=True,
            )
            continue
        break

    stdout, stdout_truncated = _bounded_capture(stdout_captures)
    stderr, stderr_truncated = _bounded_capture(stderr_captures)
    stdout_truncated = stdout_truncated or any(
        bool(invocation["stdout_truncated"]) for invocation in invocations
    )
    stderr_truncated = stderr_truncated or any(
        bool(invocation["stderr_truncated"]) for invocation in invocations
    )
    _atomic_text(stdout_log, stdout)
    _atomic_text(stderr_log, stderr)
    if final_stdout.strip():
        _atomic_text(output, final_stdout.rstrip() + "\n")
    completed_at = _timestamp()
    _atomic_json(
        receipt,
        {
            **receipt_base,
            "status": status,
            "completed_at": completed_at,
            "duration_seconds": round(time.monotonic() - started, 3),
            "exit_code": exit_code,
            "output": str(output),
            "handoff_available": (
                handoff is not None and handoff.is_file() and not handoff.is_symlink()
            ),
            "stdout_log": str(stdout_log),
            "stderr_log": str(stderr_log),
            "stdout_truncated": stdout_truncated,
            "stderr_truncated": stderr_truncated,
            "error": error,
            "invocations": invocations,
        },
    )
    heartbeat.finish(status)
    if interrupted_signal is not None:
        raise RunnerInterrupted(interrupted_signal)
    return 0 if status == "succeeded" else 1


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="dossier-agent-runner")
    parser.add_argument("--request", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        return execute(args.request.expanduser().resolve())
    except (OSError, TypeError, ValueError) as exc:
        print(f"runner error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
