from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import tomllib
import zipfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PROJECT_NAME = "agentic-lean-math-assistant"
PROOF_ARCHIVE = "CMV-One-Shot-Proof-Verified.tar.gz"
SOURCE_DATE_EPOCH = "315532800"  # 1980-01-01, also valid for ZIP metadata.


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def project_version() -> str:
    value = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))
    version = value.get("project", {}).get("version")
    if not isinstance(version, str) or not version:
        raise ValueError("pyproject.toml has no static project version")
    return version


def run(command: list[str], *, cwd: Path, env: dict[str, str] | None = None) -> None:
    subprocess.run(command, cwd=cwd, env=env, check=True, timeout=1800)


def artifact_record(path: Path, *, relative_to: Path) -> dict[str, object]:
    return {
        "path": path.relative_to(relative_to).as_posix(),
        "sha256": sha256(path),
        "size": path.stat().st_size,
    }


def safe_archive_names(archive: Path) -> list[str]:
    with tarfile.open(archive, "r:gz") as stream:
        names = stream.getnames()
    for name in names:
        member = Path(name)
        if member.is_absolute() or ".." in member.parts:
            raise ValueError(f"unsafe archive member: {name}")
    return names


def verify_candidate(candidate: Path) -> dict[str, Any]:
    candidate = candidate.expanduser().resolve()
    manifest_path = candidate / "release-manifest.json"
    checksum_path = candidate / "SHA256SUMS"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    expected_top = {"schema_version", "release", "proof", "artifacts"}
    if not isinstance(manifest, dict) or set(manifest) != expected_top:
        raise ValueError("release manifest has an unexpected schema")
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported release manifest schema")

    release = manifest.get("release")
    if not isinstance(release, dict):
        raise TypeError("release metadata must be an object")
    if (
        release.get("name") != PROJECT_NAME
        or release.get("version") != project_version()
    ):
        raise ValueError("release identity does not match pyproject.toml")
    if release.get("status") != "candidate":
        raise ValueError("release status must be candidate")

    records = manifest.get("artifacts")
    if not isinstance(records, list) or not records:
        raise ValueError("release manifest has no artifacts")
    expected_files = {
        path.relative_to(candidate).as_posix(): path
        for path in candidate.rglob("*")
        if path.is_file() and path.name not in {"release-manifest.json", "SHA256SUMS"}
    }
    recorded_paths: set[str] = set()
    for record in records:
        if not isinstance(record, dict) or set(record) != {"path", "sha256", "size"}:
            raise ValueError("release artifact record is malformed")
        relative = record["path"]
        if not isinstance(relative, str) or relative in recorded_paths:
            raise ValueError("release artifact path is invalid or duplicated")
        path = expected_files.get(relative)
        if path is None:
            raise ValueError(f"release artifact is absent: {relative}")
        if record["sha256"] != sha256(path) or record["size"] != path.stat().st_size:
            raise ValueError(f"release artifact digest mismatch: {relative}")
        recorded_paths.add(relative)
    if recorded_paths != set(expected_files):
        raise ValueError("release manifest does not cover every candidate artifact")

    checksum_lines = checksum_path.read_text(encoding="utf-8").splitlines()
    checksum_records: dict[str, str] = {}
    for line in checksum_lines:
        digest, separator, relative = line.partition("  ")
        if not separator or len(digest) != 64 or relative in checksum_records:
            raise ValueError("SHA256SUMS contains a malformed or duplicate entry")
        checksum_records[relative] = digest
    checksummed_files = {
        path.relative_to(candidate).as_posix(): path
        for path in candidate.rglob("*")
        if path.is_file() and path.name != "SHA256SUMS"
    }
    if set(checksum_records) != set(checksummed_files):
        raise ValueError("SHA256SUMS does not cover the complete candidate")
    for relative, path in checksummed_files.items():
        if checksum_records[relative] != sha256(path):
            raise ValueError(f"SHA256SUMS mismatch: {relative}")

    wheels = list(candidate.glob("*.whl"))
    source_archives = [
        path for path in candidate.glob("*.tar.gz") if path.name != PROOF_ARCHIVE
    ]
    if len(wheels) != 1 or len(source_archives) != 1:
        raise ValueError(
            "candidate must contain exactly one wheel and one source archive"
        )
    with zipfile.ZipFile(wheels[0]) as wheel:
        metadata_names = [
            name for name in wheel.namelist() if name.endswith(".dist-info/METADATA")
        ]
        entry_points = [
            name
            for name in wheel.namelist()
            if name.endswith(".dist-info/entry_points.txt")
        ]
        if len(metadata_names) != 1 or len(entry_points) != 1:
            raise ValueError("wheel is missing metadata or console entry points")
        metadata = wheel.read(metadata_names[0]).decode("utf-8")
        entry_point_text = wheel.read(entry_points[0]).decode("utf-8")
    normalized = PROJECT_NAME.replace("-", "_")
    if (
        f"Name: {PROJECT_NAME}" not in metadata
        or f"Version: {project_version()}" not in metadata
    ):
        raise ValueError("wheel metadata has the wrong project identity")
    if (
        "agentic-lean-math-assistant = agentic_lean_math_assistant.cli:main"
        not in entry_point_text
    ):
        raise ValueError("wheel does not expose agentic-lean-math-assistant")
    if normalized not in wheels[0].name:
        raise ValueError("wheel filename has the wrong project identity")

    with tarfile.open(source_archives[0], "r:gz") as source:
        source_names = source.getnames()
    forbidden = ("/projects/", "/tests/", "/.github/", "/V1_SUPPORT", "/V2_")
    if any(any(marker in f"/{name}" for marker in forbidden) for name in source_names):
        raise ValueError("source distribution contains repository-only material")
    required_suffixes = (
        "/pyproject.toml",
        "/README.md",
        "/CHANGELOG.md",
        "/LICENSE",
        "/src/agentic_lean_math_assistant/cli.py",
    )
    if any(
        not any(name.endswith(suffix) for name in source_names)
        for suffix in required_suffixes
    ):
        raise ValueError("source distribution is missing release material")

    proof_archive = candidate / PROOF_ARCHIVE
    proof_names = safe_archive_names(proof_archive)
    proof_required = (
        "/Proof.pdf",
        "/Portfolio.pdf",
        "/verification/verify_bundle.py",
        "/proof/proof-manifest.json",
    )
    if any(
        not any(name.endswith(suffix) for name in proof_names)
        for suffix in proof_required
    ):
        raise ValueError("proof archive is missing portable verification material")
    for filename in (
        "CMV-One-Shot-Proof-Portfolio.pdf",
        "CMV-One-Shot-Proof-Proof.pdf",
    ):
        path = candidate / filename
        if (
            not path.is_file()
            or path.stat().st_size < 10_000
            or not path.read_bytes().startswith(b"%PDF-")
        ):
            raise ValueError(f"release PDF is absent or malformed: {filename}")

    return manifest


def build_candidate(proof_run: Path, output: Path) -> Path:
    proof_run = proof_run.expanduser().resolve()
    output = output.expanduser().resolve()
    if output.exists():
        raise FileExistsError(f"release destination already exists: {output}")
    if not (proof_run / "state.json").is_file():
        raise FileNotFoundError(f"campaign run has no state.json: {proof_run}")

    output.parent.mkdir(parents=True, exist_ok=True)
    staging_root = Path(tempfile.mkdtemp(prefix=f".{output.name}-", dir=output.parent))
    candidate = staging_root / output.name
    python_artifacts = staging_root / "python"
    proof_bundle = staging_root / "proof-bundle"
    candidate.mkdir()
    try:
        uv = shutil.which("uv")
        if uv is None:
            raise FileNotFoundError("uv is unavailable on PATH")
        build_environment = dict(os.environ)
        build_environment["SOURCE_DATE_EPOCH"] = SOURCE_DATE_EPOCH
        run(
            [uv, "build", "--out-dir", str(python_artifacts)],
            cwd=ROOT,
            env=build_environment,
        )

        proof_archive = candidate / PROOF_ARCHIVE
        run(
            [
                sys.executable,
                str(ROOT / "projects/cmv-strip-density/one-shot/publish_release.py"),
                "--run",
                str(proof_run),
                "--destination",
                str(proof_bundle),
                "--archive",
                str(proof_archive),
            ],
            cwd=ROOT,
        )
        proof_archive.with_suffix(proof_archive.suffix + ".sha256").unlink(
            missing_ok=True
        )

        package_artifacts = [
            path
            for path in sorted(python_artifacts.iterdir())
            if path.is_file()
            and (path.suffix == ".whl" or path.name.endswith(".tar.gz"))
        ]
        if len(package_artifacts) != 2:
            raise ValueError("uv build did not produce exactly one wheel and one sdist")
        for artifact in package_artifacts:
            shutil.copy2(artifact, candidate / artifact.name)
        shutil.copy2(
            proof_bundle / "Portfolio.pdf",
            candidate / "CMV-One-Shot-Proof-Portfolio.pdf",
        )
        shutil.copy2(
            proof_bundle / "Proof.pdf", candidate / "CMV-One-Shot-Proof-Proof.pdf"
        )
        for name in ("README.md", "CHANGELOG.md", "LICENSE"):
            shutil.copy2(ROOT / name, candidate / name)

        artifacts = [
            artifact_record(path, relative_to=candidate)
            for path in sorted(candidate.rglob("*"))
            if path.is_file()
        ]
        manifest = {
            "schema_version": 1,
            "release": {
                "name": PROJECT_NAME,
                "version": project_version(),
                "status": "candidate",
                "license": "All rights reserved",
            },
            "proof": {
                "campaign_run_id": proof_run.name,
                "archive": PROOF_ARCHIVE,
                "scope": "modeled CMV range reduction; not the full CMV conjecture",
            },
            "artifacts": artifacts,
        }
        manifest_path = candidate / "release-manifest.json"
        manifest_path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        checksummed = [path for path in sorted(candidate.rglob("*")) if path.is_file()]
        (candidate / "SHA256SUMS").write_text(
            "".join(
                f"{sha256(path)}  {path.relative_to(candidate).as_posix()}\n"
                for path in checksummed
            ),
            encoding="utf-8",
        )
        verify_candidate(candidate)
        candidate.replace(output)
    finally:
        shutil.rmtree(staging_root, ignore_errors=True)
    return output


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Build the Agentic Lean Math Assistant release candidate"
    )
    parser.add_argument("--proof-run", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    version = project_version()
    output = args.output or ROOT / "dist" / f"{PROJECT_NAME}-{version}"
    result = build_candidate(args.proof_run, output)
    manifest = verify_candidate(result)
    print(
        json.dumps(
            {
                "status": "passed",
                "candidate": str(result),
                "version": version,
                "artifacts": len(manifest["artifacts"]),
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
