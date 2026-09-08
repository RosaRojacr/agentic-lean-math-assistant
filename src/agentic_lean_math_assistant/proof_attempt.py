"""Synchronous candidate-only entry point for immutable Lean proof contracts."""

from __future__ import annotations

import hashlib
import os
import shutil
from dataclasses import dataclass
from pathlib import Path

from .lean import ProofGateResult, run_proof_gate, validate_substitution_value


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _source_snapshot(project: Path) -> tuple[tuple[str, str], ...]:
    return tuple(
        (path.relative_to(project).as_posix(), _file_sha256(path))
        for path in sorted(project.rglob("*.lean"))
        if ".lake" not in path.parts
    )


def _trusted_executable(command: str, project: Path) -> Path:
    located = shutil.which(command) if os.sep not in command else command
    if located is None:
        raise ValueError(f"cannot locate Lake executable {command!r}")
    path = Path(located).expanduser().resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise ValueError(f"Lake executable is not a regular executable: {path}")
    if path.is_relative_to(project):
        raise ValueError("Lake executable must be outside the candidate project")
    return path


@dataclass(frozen=True, slots=True)
class CandidateProofResult:
    status: str
    project: str
    candidate: str
    candidate_sha256: str
    contract: str
    contract_sha256: str
    trusted_declaration: str
    project_sources: tuple[tuple[str, str], ...]
    inputs_unchanged: bool
    gate: ProofGateResult
    errors: tuple[str, ...]

    @property
    def passed(self) -> bool:
        return self.status == "passed"

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": 1,
            "status": self.status,
            "project": self.project,
            "candidate": self.candidate,
            "candidate_sha256": self.candidate_sha256,
            "contract": self.contract,
            "contract_sha256": self.contract_sha256,
            "trusted_declaration": self.trusted_declaration,
            "project_sources": [
                {"path": path, "sha256": digest}
                for path, digest in self.project_sources
            ],
            "inputs_unchanged": self.inputs_unchanged,
            "gate": self.gate.to_dict(),
            "errors": list(self.errors),
        }


def run_candidate_proof_gate(
    project: Path,
    *,
    candidate_path: Path,
    contract_path: Path,
    trusted_declaration: str,
    allowed_axioms: tuple[str, ...],
    lake: str = "lake",
    timeout: float = 180.0,
    run_dir: Path | None = None,
) -> CandidateProofResult:
    """Compile one retained candidate against a separately controlled typed consumer."""
    project = project.expanduser().resolve()
    candidate = candidate_path.expanduser().resolve()
    contract = contract_path.expanduser().resolve()
    if not project.is_dir() or project.is_symlink():
        raise ValueError(f"candidate project is not a regular directory: {project}")
    if (
        not candidate.is_file()
        or candidate.is_symlink()
        or candidate.suffix != ".lean"
        or not candidate.is_relative_to(project)
    ):
        raise ValueError("candidate must be one regular Lean file inside the project")
    if not contract.is_file() or contract.is_symlink():
        raise ValueError(f"contract is not a regular file: {contract}")
    if contract.is_relative_to(project):
        raise ValueError("trusted contract must be outside the candidate project")
    validate_substitution_value(
        "trusted_declaration", trusted_declaration, kind="identifier"
    )
    lake_path = _trusted_executable(lake, project)

    before_sources = _source_snapshot(project)
    candidate_digest = _file_sha256(candidate)
    contract_digest = _file_sha256(contract)
    gate = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=allowed_axioms,
        lake=str(lake_path),
        timeout=timeout,
        run_dir=run_dir,
    )
    inputs_unchanged = (
        before_sources == _source_snapshot(project)
        and candidate_digest == _file_sha256(candidate)
        and contract_digest == _file_sha256(contract)
    )
    errors: list[str] = []
    if not inputs_unchanged:
        errors.append(
            "candidate project or trusted contract changed during verification"
        )
    audited = tuple(report.declaration for report in gate.axiom_reports)
    if gate.passed and audited != (trusted_declaration,):
        errors.append(
            "trusted contract must audit exactly the declared typed consumer; "
            f"expected {(trusted_declaration,)!r}, found {audited!r}"
        )
    passed = gate.passed and not errors
    return CandidateProofResult(
        status="passed" if passed else "failed",
        project=str(project),
        candidate=str(candidate),
        candidate_sha256=candidate_digest,
        contract=str(contract),
        contract_sha256=contract_digest,
        trusted_declaration=trusted_declaration,
        project_sources=before_sources,
        inputs_unchanged=inputs_unchanged,
        gate=gate,
        errors=tuple(errors),
    )
