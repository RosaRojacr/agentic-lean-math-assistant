"""Append-only, hash-chained persistence for authoritative campaign state."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .artifacts import utc_now

_SCHEMA_VERSION = 1
_JOURNAL_NAME = "events.jsonl"


class JournalError(ValueError):
    """A retained state journal is malformed, corrupt, or internally inconsistent."""


@dataclass(frozen=True, slots=True)
class JournalState:
    state: dict[str, Any]
    sequence: int
    repaired_truncated_tail: bool


def append_state_snapshot(
    run_dir: Path,
    state: dict[str, Any],
    *,
    reason: str,
) -> int:
    """Durably append one complete state projection and return its sequence."""
    path = run_dir / _JOURNAL_NAME
    created = not path.exists()
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        data = _read_all(descriptor)
        records, valid_size, _repaired = _decode(data, repair_truncated_tail=True)
        if valid_size != len(data):
            os.ftruncate(descriptor, valid_size)
        previous = records[-1] if records else None
        sequence = 1 if previous is None else int(previous["sequence"]) + 1
        record: dict[str, object] = {
            "schema_version": _SCHEMA_VERSION,
            "sequence": sequence,
            "at": utc_now(),
            "previous_sha256": None if previous is None else previous["sha256"],
            "kind": "state_snapshot",
            "reason": reason,
            "state": state,
        }
        record["sha256"] = _digest(record)
        encoded = (
            json.dumps(
                record,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n"
        ).encode("utf-8")
        os.lseek(descriptor, 0, os.SEEK_END)
        _write_all(descriptor, encoded)
        os.fsync(descriptor)
        if created:
            _fsync_directory(path.parent)
        return sequence
    finally:
        os.close(descriptor)


def load_state_snapshot(run_dir: Path) -> JournalState:
    """Verify the complete chain and recover the most recent state projection."""
    path = run_dir / _JOURNAL_NAME
    try:
        descriptor = os.open(path, os.O_RDWR)
    except OSError as exc:
        raise JournalError(f"cannot open retained event journal: {exc}") from exc
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        data = _read_all(descriptor)
        records, valid_size, repaired = _decode(data, repair_truncated_tail=True)
        if not records:
            raise JournalError("retained event journal has no complete records")
        if valid_size != len(data):
            os.ftruncate(descriptor, valid_size)
            os.fsync(descriptor)
        last = records[-1]
        state = last["state"]
        if not isinstance(state, dict):
            raise JournalError("retained event journal state is not an object")
        return JournalState(
            state=state,
            sequence=int(last["sequence"]),
            repaired_truncated_tail=repaired,
        )
    finally:
        os.close(descriptor)


def journal_path(run_dir: Path) -> Path:
    return run_dir / _JOURNAL_NAME


def _decode(
    data: bytes, *, repair_truncated_tail: bool
) -> tuple[list[dict[str, Any]], int, bool]:
    repaired = False
    valid_size = len(data)
    if data and not data.endswith(b"\n"):
        if not repair_truncated_tail:
            raise JournalError("retained event journal has a truncated final record")
        valid_size = data.rfind(b"\n") + 1
        data = data[:valid_size]
        repaired = True

    records: list[dict[str, Any]] = []
    expected_previous: str | None = None
    for index, raw in enumerate(data.splitlines(), start=1):
        try:
            value = json.loads(raw)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise JournalError(
                f"event journal record {index} is not valid JSON"
            ) from exc
        required = {
            "schema_version",
            "sequence",
            "at",
            "previous_sha256",
            "kind",
            "reason",
            "state",
            "sha256",
        }
        if not isinstance(value, dict) or set(value) != required:
            raise JournalError(f"event journal record {index} has invalid keys")
        if value["schema_version"] != _SCHEMA_VERSION:
            raise JournalError(
                f"event journal record {index} has an unsupported schema"
            )
        if value["sequence"] != index:
            raise JournalError(f"event journal record {index} is out of sequence")
        if value["previous_sha256"] != expected_previous:
            raise JournalError(f"event journal record {index} breaks the hash chain")
        if value["kind"] != "state_snapshot":
            raise JournalError(f"event journal record {index} has an invalid kind")
        if not isinstance(value["at"], str) or not value["at"]:
            raise JournalError(f"event journal record {index} has an invalid timestamp")
        if not isinstance(value["reason"], str) or not value["reason"]:
            raise JournalError(f"event journal record {index} has an invalid reason")
        if not isinstance(value["state"], dict):
            raise JournalError(f"event journal record {index} has an invalid state")
        observed = value["sha256"]
        if not isinstance(observed, str) or observed != _digest(value):
            raise JournalError(f"event journal record {index} has an invalid digest")
        records.append(value)
        expected_previous = observed
    return records, valid_size, repaired


def _digest(record: dict[str, object]) -> str:
    unsigned = {key: value for key, value in record.items() if key != "sha256"}
    canonical = json.dumps(
        unsigned,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _read_all(descriptor: int) -> bytes:
    os.lseek(descriptor, 0, os.SEEK_SET)
    chunks: list[bytes] = []
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            return b"".join(chunks)
        chunks.append(chunk)


def _write_all(descriptor: int, value: bytes) -> None:
    remaining = memoryview(value)
    while remaining:
        written = os.write(descriptor, remaining)
        if written <= 0:
            raise OSError("event journal append made no progress")
        remaining = remaining[written:]
