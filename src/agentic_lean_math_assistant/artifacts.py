"""Atomic writes and content-addressed campaign artifacts."""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path, PurePosixPath


@dataclass(frozen=True, slots=True)
class Artifact:
    """Digest and size of one retained regular file."""

    path: str
    sha256: str
    size: int

    def to_dict(self) -> dict[str, str | int]:
        return {"path": self.path, "sha256": self.sha256, "size": self.size}


def utc_now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds").replace("+00:00", "Z")


def atomic_write_text(path: Path, content: str) -> None:
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
        _fsync_directory(path.parent)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_write_json(path: Path, value: object) -> None:
    atomic_write_text(
        path,
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
    )


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def digest_file(path: Path, *, relative_to: Path) -> Artifact:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
            size += len(chunk)
    return Artifact(
        path=path.relative_to(relative_to).as_posix(),
        sha256=digest.hexdigest(),
        size=size,
    )


def digest_tree(root: Path, *, exclude: set[str] | None = None) -> tuple[Artifact, ...]:
    omitted = {PurePosixPath(path) for path in exclude or set()}
    files: list[Path] = []
    for current, directories, filenames in os.walk(root):
        directory = Path(current)
        relative_directory = PurePosixPath(directory.relative_to(root).as_posix())
        directories[:] = sorted(
            name
            for name in directories
            if not _path_is_excluded(relative_directory / name, omitted)
        )
        files.extend(
            path
            for name in sorted(filenames)
            if not _path_is_excluded(relative_directory / name, omitted)
            and (path := directory / name).is_file()
        )
    return tuple(digest_file(path, relative_to=root) for path in sorted(files))


def _path_is_excluded(relative: PurePosixPath, omitted: set[PurePosixPath]) -> bool:
    return any(
        excluded == relative or excluded in relative.parents for excluded in omitted
    )


def verify_evidence_index(run_dir: Path) -> tuple[Artifact, ...]:
    """Verify every regular file named by a retained evidence index."""

    return _verify_evidence_index(run_dir, permitted_receipts=frozenset())


def verify_evidence_for_repair(
    run_dir: Path, *, permitted_paths: set[str] | frozenset[str]
) -> tuple[Artifact, ...]:
    """Verify prior evidence while permitting explicit controller-owned paths."""

    permitted = frozenset(permitted_paths)
    if any(
        (pure := PurePosixPath(path)).is_absolute()
        or not pure.parts
        or any(part in ("", ".", "..") for part in pure.parts)
        for path in permitted
    ):
        raise ValueError("permitted evidence repair path is unsafe")
    return _verify_evidence_index(run_dir, permitted_receipts=permitted)


def _verify_evidence_index(
    run_dir: Path, *, permitted_receipts: frozenset[str]
) -> tuple[Artifact, ...]:
    evidence_path = run_dir / "evidence.json"
    try:
        evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read evidence index: {exc}") from exc
    if not isinstance(evidence, dict) or set(evidence) != {
        "schema_version",
        "campaign_id",
        "status",
        "generated_at",
        "artifacts",
    }:
        raise TypeError("evidence index has invalid structure")
    if evidence["schema_version"] != 1:
        raise ValueError("evidence index has an unsupported schema")
    if not all(
        isinstance(evidence[field], str) and bool(evidence[field])
        for field in ("campaign_id", "status", "generated_at")
    ):
        raise TypeError("evidence index has invalid metadata")
    if not isinstance(evidence["artifacts"], list):
        raise TypeError("evidence index artifacts must be a list")
    verified: list[Artifact] = []
    indexed_paths: set[str] = set()
    for index, value in enumerate(evidence["artifacts"]):
        if not isinstance(value, dict) or set(value) != {"path", "sha256", "size"}:
            raise ValueError(f"evidence artifact {index} has invalid structure")
        relative = value["path"]
        if not isinstance(relative, str):
            raise TypeError(f"evidence artifact {index} path must be a string")
        pure = PurePosixPath(relative)
        if pure.is_absolute() or any(part in ("", ".", "..") for part in pure.parts):
            raise ValueError(f"evidence artifact {index} has an unsafe path")
        if relative in indexed_paths:
            raise ValueError(f"evidence artifact path is duplicated: {relative}")
        indexed_paths.add(relative)
        if relative in permitted_receipts:
            continue
        path = run_dir / relative
        if not path.is_file() or path.is_symlink():
            raise ValueError(f"evidence artifact is missing or irregular: {relative}")
        observed = digest_file(path, relative_to=run_dir)
        if observed.to_dict() != value:
            raise ValueError(f"evidence artifact digest mismatch: {relative}")
        verified.append(observed)
    expected_paths = {
        path.relative_to(run_dir).as_posix()
        for path in run_dir.rglob("*")
        if path.is_file()
        and not path.is_symlink()
        and path.relative_to(run_dir).as_posix()
        not in {"evidence.json", ".campaign.lock"}
        and "workspace" not in path.relative_to(run_dir).parts[:1]
    }
    indexed_non_receipts = indexed_paths - permitted_receipts
    expected_non_receipts = expected_paths - permitted_receipts
    if indexed_non_receipts != expected_non_receipts:
        missing = sorted(expected_non_receipts - indexed_non_receipts)
        extra = sorted(indexed_non_receipts - expected_non_receipts)
        raise ValueError(
            f"evidence artifact set mismatch: missing={missing}, extra={extra}"
        )
    return tuple(verified)
