"""Linux process sandbox construction and cgroup lifecycle control."""

from __future__ import annotations

import hashlib
import json
import math
import os
import secrets
import shutil
import stat
import subprocess
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

from .config import ExecutionSpec

_MIB = 1024 * 1024
_SANDBOX_TASK_OVERHEAD = 8
_REGENERABLE_WORKSPACE_DIRECTORIES = frozenset(
    {".lake", "__pycache__", ".mypy_cache", ".pytest_cache", ".ruff_cache"}
)
_DEPENDENCY_MANIFESTS = frozenset(
    {
        "Cargo.lock",
        "Pipfile.lock",
        "bun.lock",
        "lake-manifest.json",
        "lakefile.lean",
        "lakefile.toml",
        "lean-toolchain",
        "package-lock.json",
        "poetry.lock",
        "pyproject.toml",
        "requirements.txt",
        "uv.lock",
    }
)


class SandboxError(RuntimeError):
    """The configured OS sandbox cannot be constructed or controlled."""


@dataclass(frozen=True, slots=True)
class SandboxInvocation:
    argv: tuple[str, ...]
    unit: str | None
    systemctl: str | None
    metadata: Mapping[str, object]
    environment: Mapping[str, str] | None = None


def _resource_properties(
    policy: ExecutionSpec, runtime_max_seconds: float | None
) -> tuple[str, ...]:
    if runtime_max_seconds is None or runtime_max_seconds <= 0:
        raise SandboxError("resource controls require a positive command deadline")
    return (
        "KillMode=control-group",
        f"MemoryMax={policy.memory_max_mb * _MIB}",
        "MemorySwapMax=0",
        f"TasksMax={policy.tasks_max + _SANDBOX_TASK_OVERHEAD}",
        f"LimitNPROC={_current_user_tasks() + policy.tasks_max + _SANDBOX_TASK_OVERHEAD}",
        f"CPUQuota={policy.cpu_quota_percent}%",
        f"RuntimeMaxSec={max(1, math.ceil(runtime_max_seconds))}s",
        f"LimitFSIZE={policy.file_size_max_mb * _MIB}",
    )


def prepare_sandbox(
    argv: tuple[str, ...],
    *,
    cwd: Path,
    workspace: Path,
    environment: Mapping[str, str],
    policy: ExecutionSpec,
    read_paths: tuple[Path, ...] = (),
    allow_workspace_executables: bool = False,
    runtime_max_seconds: float | None = None,
) -> SandboxInvocation:
    """Apply cgroup limits and, when enabled, a Bubblewrap mount namespace."""
    executable = _resolve_executable(argv[0], cwd, environment)
    workspace = workspace.resolve()
    if not workspace.is_dir():
        raise SandboxError(f"sandbox workspace does not exist: {workspace}")
    try:
        cwd.resolve().relative_to(workspace)
    except ValueError as exc:
        raise SandboxError(f"sandbox cwd escapes workspace: {cwd}") from exc
    systemd_run = _required_executable("systemd-run")
    systemctl = _required_executable("systemctl")
    unit = f"campaign-{os.getpid()}-{secrets.token_hex(6)}.service"
    if not policy.sandbox:
        executable_visibility = _executable_visibility(executable)
        allowed_paths = _deduplicate_paths(
            (
                Path("/usr"),
                *(
                    path if path.is_dir() else path.parent
                    for path in executable_visibility
                ),
                *policy.allowed_executable_paths,
            )
        )
        effective_environment = _sandbox_environment(
            environment,
            policy,
            workspace,
            executable,
            allowed_paths,
        )
        resource_properties = _resource_properties(policy, runtime_max_seconds)
        assert runtime_max_seconds is not None
        environment_tool = _required_executable("env")
        wrapped = [
            str(systemd_run),
            "--user",
            "--wait",
            "--pipe",
            "--quiet",
            "--collect",
            f"--unit={unit}",
            f"--working-directory={cwd}",
        ]
        for value in resource_properties:
            wrapped.extend(("--property", value))
        wrapped.extend(
            (
                "--",
                str(environment_tool),
                "-i",
                *(f"{name}={value}" for name, value in effective_environment.items()),
                *argv,
            )
        )
        return SandboxInvocation(
            argv=tuple(wrapped),
            unit=unit,
            systemctl=str(systemctl),
            metadata={
                "enabled": False,
                "backend": "systemd-cgroup",
                "unit": unit,
                "memory_max_mb": policy.memory_max_mb,
                "memory_swap_max_mb": 0,
                "cpu_quota_percent": policy.cpu_quota_percent,
                "tasks_max": policy.tasks_max,
                "file_size_max_mb": policy.file_size_max_mb,
                "runtime_max_seconds": max(1, math.ceil(runtime_max_seconds)),
                "environment": _environment_metadata(effective_environment, policy),
                "toolchain": _toolchain_metadata(executable, workspace),
            },
            environment=None,
        )
    bubblewrap = _required_executable("bwrap")
    if (
        _is_below(executable, workspace) or _is_lexically_below(executable, workspace)
    ) and not allow_workspace_executables:
        raise SandboxError("workspace executable requires workspace_executables=true")
    resource_properties = _resource_properties(policy, runtime_max_seconds)
    assert runtime_max_seconds is not None

    executable_visibility = _executable_visibility(executable)
    executable_paths: tuple[Path, ...] = (
        Path("/usr"),
        bubblewrap,
        *executable_visibility,
        *policy.allowed_executable_paths,
        *((workspace,) if allow_workspace_executables else ()),
    )
    allowed_paths = _deduplicate_paths(
        tuple(path if path.is_dir() else path.parent for path in executable_paths)
    )
    sandbox_environment = _sandbox_environment(
        environment,
        policy,
        workspace,
        executable,
        allowed_paths,
    )
    visible_paths = _deduplicate_lexical_paths(
        (
            *_executable_visibility(executable),
            *policy.allowed_executable_paths,
            *read_paths,
        )
    )
    properties = (
        *resource_properties,
        "NoExecPaths=/",
        "ExecPaths=" + " ".join(_systemd_path(path) for path in allowed_paths),
    )
    sandbox = [
        str(bubblewrap),
        "--die-with-parent",
        "--new-session",
        "--unshare-all",
        "--ro-bind",
        "/usr",
        "/usr",
        "--symlink",
        "usr/bin",
        "/bin",
        "--symlink",
        "usr/sbin",
        "/sbin",
        "--symlink",
        "usr/lib",
        "/lib",
        "--symlink",
        "usr/lib64",
        "/lib64",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--tmpfs",
        "/run",
        "--tmpfs",
        "/tmp",
        "--tmpfs",
        "/home",
        "--tmpfs",
        "/root",
    ]
    for path in _system_read_paths():
        sandbox.extend(("--ro-bind", str(path), str(path)))
    if policy.network:
        sandbox.append("--share-net")
    for path in visible_paths:
        if (
            _is_below(path, workspace)
            or _is_lexically_below(path, workspace)
            or _is_lexically_below(path, Path("/usr"))
        ):
            continue
        if not path.exists():
            raise SandboxError(f"sandbox read path does not exist: {path}")
        sandbox.extend(("--ro-bind", str(path), str(path)))
    sandbox.extend(("--bind", str(workspace), str(workspace)))
    sandbox.append("--clearenv")
    for name, value in sandbox_environment.items():
        sandbox.extend(("--setenv", name, value))
    sandbox.extend(("--chdir", str(cwd), "--", *argv))

    wrapped = [
        str(systemd_run),
        "--user",
        "--wait",
        "--pipe",
        "--quiet",
        "--collect",
        f"--unit={unit}",
    ]
    for value in properties:
        wrapped.extend(("--property", value))
    wrapped.extend(sandbox)
    metadata: dict[str, object] = {
        "enabled": True,
        "backend": "systemd-bwrap",
        "unit": unit,
        "network": policy.network,
        "memory_max_mb": policy.memory_max_mb,
        "memory_swap_max_mb": 0,
        "cpu_quota_percent": policy.cpu_quota_percent,
        "tasks_max": policy.tasks_max,
        "file_size_max_mb": policy.file_size_max_mb,
        "workspace_max_mb": policy.workspace_max_mb,
        "runtime_max_seconds": max(1, math.ceil(runtime_max_seconds)),
        "allowed_executable_paths": [str(path) for path in allowed_paths],
        "writable_paths": [str(workspace)],
        "workspace_executables": allow_workspace_executables,
        "environment": _environment_metadata(sandbox_environment, policy),
        "toolchain": _toolchain_metadata(executable, workspace),
    }
    return SandboxInvocation(tuple(wrapped), unit, str(systemctl), metadata)


def terminate_sandbox(invocation: SandboxInvocation) -> str | None:
    """Kill a transient cgroup and return a cleanup error if it survives."""
    if invocation.unit is None:
        return None
    if invocation.systemctl is None:
        return f"cannot terminate sandbox unit {invocation.unit}: systemctl is unknown"
    return terminate_sandbox_unit(invocation.unit, invocation.systemctl)


def terminate_sandbox_unit(unit: str, systemctl: str) -> str | None:
    """Stop one retained transient unit and verify that it is inactive."""
    for arguments in (
        (
            systemctl,
            "--user",
            "kill",
            "--kill-whom=all",
            "--signal=SIGKILL",
            unit,
        ),
        (systemctl, "--user", "stop", unit),
    ):
        try:
            subprocess.run(
                arguments,
                check=False,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                timeout=10,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            return f"cannot terminate sandbox unit {unit}: {exc}"
    try:
        active = subprocess.run(
            (systemctl, "--user", "is-active", "--quiet", unit),
            check=False,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return f"cannot verify sandbox unit {unit} termination: {exc}"
    if active.returncode == 0:
        return f"sandbox unit {unit} survived termination"
    return None


def workspace_size_exceeds(root: Path, limit_bytes: int) -> tuple[bool, int]:
    """Bound durable regular bytes and entries without traversing caches."""
    total = 0
    pending = [root]
    while pending:
        directory = pending.pop()
        try:
            entries = _scandir_entries(directory)
        except (FileNotFoundError, NotADirectoryError):
            continue
        for entry in entries:
            if entry.name in _REGENERABLE_WORKSPACE_DIRECTORIES and entry.is_dir(
                follow_symlinks=False
            ):
                continue
            try:
                total += 4096
                if entry.is_dir(follow_symlinks=False):
                    pending.append(Path(entry.path))
                elif entry.is_file(follow_symlinks=False):
                    total += entry.stat(follow_symlinks=False).st_size
            except FileNotFoundError:
                continue
            except PermissionError:
                return True, limit_bytes + 1
            if total > limit_bytes:
                return True, total
    return False, total


def remove_secret_bearing_files(
    root: Path, secrets: tuple[str, ...]
) -> tuple[str, ...]:
    needles = tuple(secret.encode("utf-8") for secret in secrets)
    if not needles:
        return ()
    files, links, directories = _workspace_entries(root)
    removed: list[str] = []
    for path in files:
        relative = path.relative_to(root).as_posix()
        if any(secret in relative for secret in secrets) or _file_contains(
            path, needles
        ):
            path.unlink()
            removed.append(relative)
    for path in links:
        relative = path.relative_to(root).as_posix()
        target = os.readlink(path)
        if any(secret in relative or secret in target for secret in secrets):
            path.unlink()
            removed.append(relative)
    for path in sorted(directories, key=lambda value: len(value.parts), reverse=True):
        relative = path.relative_to(root).as_posix()
        if path.exists() and any(secret in relative for secret in secrets):
            shutil.rmtree(path)
            removed.append(f"{relative}/")
    return tuple(sorted(removed))


def _workspace_entries(
    root: Path,
) -> tuple[tuple[Path, ...], tuple[Path, ...], tuple[Path, ...]]:
    files: list[Path] = []
    links: list[Path] = []
    directories: list[Path] = []
    pending = [root]
    while pending:
        directory = pending.pop()
        try:
            entries = _scandir_entries(directory)
        except FileNotFoundError:
            continue
        for entry in entries:
            path = Path(entry.path)
            if entry.is_symlink():
                links.append(path)
            elif entry.is_dir(follow_symlinks=False):
                directories.append(path)
                pending.append(path)
            elif entry.is_file(follow_symlinks=False):
                files.append(path)
    return tuple(sorted(files)), tuple(sorted(links)), tuple(sorted(directories))


def _scandir_entries(directory: Path) -> tuple[os.DirEntry[str], ...]:
    try:
        return tuple(os.scandir(directory))
    except PermissionError:
        mode = directory.stat(follow_symlinks=False).st_mode
        directory.chmod(
            mode | stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR,
            follow_symlinks=False,
        )
        return tuple(os.scandir(directory))


def _file_contains(path: Path, needles: tuple[bytes, ...]) -> bool:
    overlap = max(len(needle) for needle in needles) - 1
    pending = b""
    try:
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(64 * 1024), b""):
                data = pending + chunk
                if any(needle in data for needle in needles):
                    return True
                pending = data[-overlap:] if overlap else b""
    except FileNotFoundError:
        return False
    except PermissionError:
        return True
    return False


def secret_values(
    environment: Mapping[str, str], policy: ExecutionSpec | None
) -> tuple[str, ...]:
    if policy is None:
        return ()
    return tuple(
        sorted(
            {
                environment[name]
                for name in policy.secret_environment
                if environment.get(name)
            },
            key=len,
            reverse=True,
        )
    )


def redact_text(value: str | None, secrets: tuple[str, ...]) -> str | None:
    if value is None:
        return None
    for secret in secrets:
        value = value.replace(secret, "[REDACTED]")
    return value


def _required_executable(name: str) -> Path:
    value = shutil.which(name)
    if value is None:
        raise SandboxError(f"required sandbox executable is unavailable: {name}")
    return Path(value).resolve()


def _system_read_paths() -> tuple[Path, ...]:
    candidates = (
        Path("/etc/alternatives"),
        Path("/etc/group"),
        Path("/etc/hosts"),
        Path("/etc/ld.so.cache"),
        Path("/etc/localtime"),
        Path("/etc/nsswitch.conf"),
        Path("/etc/passwd"),
        Path("/etc/pki"),
        Path("/etc/resolv.conf"),
        Path("/etc/ssl"),
    )
    return tuple(path for path in candidates if path.exists())


def _executable_visibility(executable: Path) -> tuple[Path, ...]:
    if _is_lexically_below(executable, Path("/usr")):
        return ()
    visible: list[Path] = []
    venv_root = executable.parent.parent
    if (venv_root / "pyvenv.cfg").is_file():
        visible.append(venv_root)
    if executable.is_symlink():
        target = Path(os.readlink(executable))
        if not target.is_absolute():
            target = executable.parent / target
        target = target.absolute()
        if not _is_lexically_below(target.resolve(), Path("/usr")):
            target_prefix = target.parent.parent
            target_libraries = target_prefix / "lib"
            if target.name.startswith("python") and any(
                target_libraries.glob("python*")
            ):
                visible.append(target_prefix)
            else:
                visible.append(target)

    resolved = executable.resolve()
    if not _is_lexically_below(resolved, Path("/usr")):
        runtime_prefix = resolved.parent.parent
        python_libraries = runtime_prefix / "lib"
        if resolved.name.startswith("python") and any(python_libraries.glob("python*")):
            visible.append(runtime_prefix)
        else:
            visible.append(resolved)
    if not visible:
        visible.append(executable)
    return _deduplicate_lexical_paths(tuple(visible))


def _resolve_executable(value: str, cwd: Path, environment: Mapping[str, str]) -> Path:
    if "/" in value:
        path = Path(value)
        if not path.is_absolute():
            path = cwd / path
        path = path.absolute()
    else:
        resolved = shutil.which(value, path=environment.get("PATH"))
        if resolved is None:
            raise SandboxError(f"command executable is unavailable: {value}")
        path = Path(resolved).absolute()
    if not path.is_file():
        raise SandboxError(f"command executable is not a file: {path}")
    return path


def _sandbox_environment(
    environment: Mapping[str, str],
    policy: ExecutionSpec,
    workspace: Path,
    executable: Path,
    allowed_paths: tuple[Path, ...],
) -> dict[str, str]:
    result = {
        name: environment[name]
        for name in policy.environment_allow
        if name in environment
    }
    normalized = {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TERM": "dumb",
        "TZ": "UTC",
        "USER": "campaign",
    }
    for name, value in normalized.items():
        if name in policy.environment_allow:
            result[name] = value
    if policy.sandbox and "HOME" in policy.environment_allow:
        result["HOME"] = str(workspace)
    if policy.sandbox and "XDG_CONFIG_HOME" in policy.environment_allow:
        result["XDG_CONFIG_HOME"] = str(workspace / ".config")
    if "PATH" in policy.environment_allow:
        directories: list[Path] = [
            executable.parent,
            Path("/usr/bin"),
            Path("/usr/sbin"),
        ]
        for path in allowed_paths:
            if path.is_dir():
                directories.append(path)
            else:
                directories.append(path.parent)
        result["PATH"] = os.pathsep.join(
            str(path) for path in _deduplicate_paths(tuple(directories))
        )
    return result


def _environment_metadata(
    environment: Mapping[str, str], policy: ExecutionSpec
) -> dict[str, object]:
    fingerprinted = {
        name: value
        for name, value in environment.items()
        if name not in policy.secret_environment
    }
    return {
        "allowed": sorted(environment),
        "secret": sorted(policy.secret_environment),
        "sha256": hashlib.sha256(
            json.dumps(
                fingerprinted,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest(),
    }


def _toolchain_metadata(executable: Path, workspace: Path) -> dict[str, object]:
    resolved = executable.resolve()
    executable_digest = _digest_path(resolved)
    manifests: list[dict[str, object]] = []
    for path in sorted(workspace.rglob("*")):
        if (
            path.is_symlink()
            or not path.is_file()
            or not _is_dependency_manifest(path.name)
        ):
            continue
        digest = _digest_path(path)
        manifests.append(
            {
                "path": path.relative_to(workspace).as_posix(),
                **digest,
            }
        )
    return {
        "executable": {
            "path": str(executable),
            "resolved_path": str(resolved),
            **executable_digest,
        },
        "dependency_manifests": manifests,
    }


def _is_dependency_manifest(name: str) -> bool:
    return name in _DEPENDENCY_MANIFESTS or (
        name.startswith("requirements-") and name.endswith(".txt")
    )


def _digest_path(path: Path) -> dict[str, object]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
            size += len(chunk)
    return {"sha256": digest.hexdigest(), "size": size}


def _deduplicate_paths(values: tuple[Path, ...]) -> tuple[Path, ...]:
    result: list[Path] = []
    seen: set[Path] = set()
    for value in values:
        path = value.resolve()
        if path in seen:
            continue
        seen.add(path)
        result.append(path)
    return tuple(result)


def _deduplicate_lexical_paths(values: tuple[Path, ...]) -> tuple[Path, ...]:
    result: list[Path] = []
    seen: set[Path] = set()
    for value in values:
        path = value.absolute()
        if path in seen:
            continue
        seen.add(path)
        result.append(path)
    return tuple(result)


def _is_lexically_below(path: Path, root: Path) -> bool:
    try:
        path.absolute().relative_to(root.absolute())
    except ValueError:
        return False
    return True


def _is_below(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root)
    except ValueError:
        return False
    return True


def _current_user_tasks() -> int:
    uid = os.getuid()
    total = 0
    for entry in os.scandir("/proc"):
        if not entry.name.isdigit():
            continue
        try:
            if entry.stat(follow_symlinks=False).st_uid != uid:
                continue
            total += sum(1 for _ in os.scandir(f"{entry.path}/task"))
        except (FileNotFoundError, PermissionError):
            continue
    return total


def _is_hidden_by_tmp(path: Path) -> bool:
    try:
        path.resolve().relative_to("/tmp")
    except ValueError:
        return False
    return True


def _systemd_path(path: Path) -> str:
    rendered = str(path).replace("\\", "\\\\").replace('"', '\\"')
    return f'"{rendered}"'
