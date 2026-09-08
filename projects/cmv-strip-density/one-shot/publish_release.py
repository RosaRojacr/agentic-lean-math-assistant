from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

from agentic_lean_math_assistant.artifacts import verify_evidence_index


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def verify_bundle(bundle: Path) -> None:
    verifier = bundle / "verification" / "verify_bundle.py"
    if not verifier.is_file():
        raise ValueError("release bundle has no portable document verifier")
    subprocess.run(
        [sys.executable, str(verifier), "--bundle", str(bundle)],
        check=True,
        timeout=300,
    )
    subprocess.run(
        [sys.executable, "verify_certificate.py"],
        cwd=bundle / "proof",
        check=True,
        timeout=300,
    )


def deterministic_archive(bundle: Path, archive: Path) -> str:
    archive.parent.mkdir(parents=True, exist_ok=True)
    temporary = archive.with_name(f".{archive.name}.tmp")
    try:
        with (
            temporary.open("wb") as raw,
            gzip.GzipFile(fileobj=raw, mode="wb", mtime=0) as compressed,
            tarfile.open(fileobj=compressed, mode="w") as tar,
        ):
            for path in sorted(bundle.rglob("*")):
                relative = path.relative_to(bundle)
                info = tar.gettarinfo(path, arcname=str(Path(bundle.name) / relative))
                info.uid = 0
                info.gid = 0
                info.uname = ""
                info.gname = ""
                info.mtime = 0
                if path.is_file():
                    with path.open("rb") as stream:
                        tar.addfile(info, stream)
                else:
                    tar.addfile(info)
        temporary.replace(archive)
    finally:
        temporary.unlink(missing_ok=True)
    digest = sha256(archive)
    archive.with_suffix(archive.suffix + ".sha256").write_text(
        f"{digest}  {archive.name}\n", encoding="utf-8"
    )
    return digest


def publish(run: Path, destination: Path, *, archive: Path | None, replace: bool) -> dict[str, object]:
    run = run.expanduser().resolve()
    destination = destination.expanduser().resolve()
    state = json.loads((run / "state.json").read_text(encoding="utf-8"))
    if not isinstance(state, dict) or state.get("status") != "complete":
        raise ValueError("only a complete campaign run can be published")
    evidence = verify_evidence_index(run)
    source = run / "output"
    if not source.is_dir():
        raise ValueError("complete run has no promoted output directory")
    if destination.exists() and not replace:
        raise FileExistsError(f"destination already exists: {destination}")

    destination.parent.mkdir(parents=True, exist_ok=True)
    staging_root = Path(tempfile.mkdtemp(prefix=f".{destination.name}-", dir=destination.parent))
    staged = staging_root / destination.name
    backup = staging_root / ".previous"
    try:
        shutil.copytree(source, staged)
        verify_bundle(staged)
        if backup.exists():
            shutil.rmtree(backup)
        if destination.exists():
            destination.replace(backup)
        try:
            staged.replace(destination)
        except BaseException:
            if backup.exists() and not destination.exists():
                backup.replace(destination)
            raise
        if backup.exists():
            shutil.rmtree(backup)
    finally:
        shutil.rmtree(staging_root, ignore_errors=True)

    archive_digest = None
    if archive is not None:
        archive_digest = deterministic_archive(destination, archive.expanduser().resolve())
    return {
        "status": "published",
        "run": str(run),
        "destination": str(destination),
        "verified_evidence_artifacts": len(evidence),
        "archive": None if archive is None else str(archive.expanduser().resolve()),
        "archive_sha256": archive_digest,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Publish a verified one-shot portfolio bundle")
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--replace", action="store_true")
    args = parser.parse_args()
    print(
        json.dumps(
            publish(
                args.run,
                args.destination,
                archive=args.archive,
                replace=args.replace,
            ),
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
