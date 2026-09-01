"""Deterministic Lean build, external-contract, and axiom acceptance gates."""

from __future__ import annotations

import hashlib
import json
import os
import re
import secrets
import shutil
import tempfile
import time
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType

from .command import CapturedCommand, run_captured_command
from .config import ExecutionSpec

_BANNED = re.compile(r"\b(sorry|admit)\b|\baxiom\s+|\bunsafe\s+(?:def|theorem)")
_PLACEHOLDER = re.compile(r"\{\{\s*(?P<name>[a-z][a-z0-9_]*)\s*\}\}")
_IDENTIFIER_COMPONENT = r"(?!\d)\w[\w']*"
_IDENTIFIER_TEXT = rf"{_IDENTIFIER_COMPONENT}(?:\.{_IDENTIFIER_COMPONENT})*"
_DECIMAL_TEXT = r"-?(?:0|[1-9][0-9]*)(?:\.[0-9]+)?"
_STRING_LITERAL_TEXT = r'"(?:[^"\\\r\n]|\\(?:["\\nrt0]|u\{[0-9A-Fa-f]+\}))*"'
_SUBSTITUTION_PATTERNS = MappingProxyType(
    {
        "decimal": re.compile(_DECIMAL_TEXT),
        "identifier": re.compile(_IDENTIFIER_TEXT),
        "string": re.compile(_STRING_LITERAL_TEXT),
        "token": re.compile(
            rf"(?:{_DECIMAL_TEXT}|{_IDENTIFIER_TEXT}|{_STRING_LITERAL_TEXT})"
        ),
    }
)
_PRINT_AXIOMS = re.compile(
    rf"(?m)^[ \t]*#print[ \t]+axioms[ \t]+"
    rf"(?P<declaration>{_IDENTIFIER_TEXT})[ \t]*$"
)


def _render_trusted_audit(
    rendered_contract: str,
    declarations: tuple[str, ...],
    token: str,
) -> tuple[str, str]:
    command = f"proof_builder_axiom_audit_{token}"
    prefix = f"ProofBuilderAudit_{token}"
    invocations = "\n".join(
        f"{command} {prefix}.report{index} {declaration}"
        for index, declaration in enumerate(declarations)
    )
    source = f"""import Lean
{rendered_contract.rstrip()}

open Lean Elab Command
syntax (name := {command}) "{command} " ident ident : command
elab_rules : command
  | `(command| {command} $_prefix $_declaration) => do
      let name := _declaration.getId
      let base := _prefix.getId
      let addMarker (marker : Name) : CommandElabM Unit :=
        liftCoreM <| addDecl <| Declaration.defnDecl {{
          name := marker
          levelParams := []
          type := mkConst ``Nat
          value := mkNatLit 0
          hints := .abbrev
          safety := DefinitionSafety.safe
        }}
      addMarker (base ++ `declaration ++ name)
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        addMarker (base ++ `axiom ++ ax)
{invocations}
"""
    return source, prefix


_TRUSTED_CERTIFICATE_READER = """import Lean

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let path :: prefixValue :: "--" :: declarations := args
    | IO.eprintln "usage: reader <olean> <prefix> -- <declaration>..."
      return 2
  let (data, _) ← readModuleData (System.FilePath.mk path)
  let names := data.constNames.map (·.toString)
  let declarations := declarations.toArray
  for h : index in [:declarations.size] do
    let declaration := declarations[index]
    let base := s!"{prefixValue}.report{index}"
    let declarationMarker := s!"{base}.declaration.{declaration}"
    unless names.contains declarationMarker do
      IO.eprintln s!"missing declaration certificate: {declaration}"
      return 3
    let axiomPrefix := s!"{base}.axiom."
    let axioms := names.filterMap fun (name : String) =>
      if String.startsWith name axiomPrefix then
        some (String.drop name axiomPrefix.length).toString
      else none
    let value := Json.mkObj [
      ("declaration", Json.str declaration),
      ("axioms", Json.arr (axioms.map Json.str))
    ]
    IO.println value.compress
  return 0
"""


@dataclass(frozen=True, slots=True)
class GateCommandReceipt:
    argv: tuple[str, ...]
    exit_code: int
    duration_seconds: float
    stdout: str
    stderr: str
    stdout_truncated: bool
    stderr_truncated: bool
    stdout_sha256: str
    stderr_sha256: str
    sandbox: Mapping[str, object]

    def to_dict(self) -> dict[str, object]:
        return {
            "argv": list(self.argv),
            "exit_code": self.exit_code,
            "duration_seconds": self.duration_seconds,
            "stdout": self.stdout,
            "stderr": self.stderr,
            "stdout_truncated": self.stdout_truncated,
            "stderr_truncated": self.stderr_truncated,
            "stdout_sha256": self.stdout_sha256,
            "stderr_sha256": self.stderr_sha256,
            "sandbox": dict(self.sandbox),
        }


@dataclass(frozen=True, slots=True)
class AxiomReport:
    declaration: str
    axioms: tuple[str, ...]

    def to_dict(self) -> dict[str, object]:
        return {"declaration": self.declaration, "axioms": list(self.axioms)}


@dataclass(frozen=True, slots=True)
class ProofGateResult:
    status: str
    contract_name: str
    contract_sha256: str
    rendered_contract_sha256: str
    substitutions: Mapping[str, str]
    axiom_reports: tuple[AxiomReport, ...]
    source_issues: tuple[str, ...]
    command_receipts: tuple[GateCommandReceipt, ...]
    errors: tuple[str, ...]

    @property
    def passed(self) -> bool:
        return self.status == "passed"

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": 2,
            "status": self.status,
            "contract_name": self.contract_name,
            "contract_sha256": self.contract_sha256,
            "rendered_contract_sha256": self.rendered_contract_sha256,
            "substitutions": dict(self.substitutions),
            "axiom_reports": [report.to_dict() for report in self.axiom_reports],
            "source_issues": list(self.source_issues),
            "commands": [receipt.to_dict() for receipt in self.command_receipts],
            "errors": list(self.errors),
        }


def _strip_lean_comments_and_strings(source: str) -> str:
    """Preserve token boundaries while removing nested comments and strings."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(source):
        pair = source[index : index + 2]
        char = source[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            if char == "\\" and index + 1 < len(source):
                output.extend("  ")
                index += 2
            elif char == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if pair == "/-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif pair == "--":
            newline = source.find("\n", index + 2)
            if newline == -1:
                output.extend(" " * (len(source) - index))
                break
            output.extend(" " * (newline - index))
            index = newline
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    return "".join(output)


def _scan_source(source: str, label: str) -> tuple[str, ...]:
    cleaned = _strip_lean_comments_and_strings(source)
    issues: list[str] = []
    for match in _BANNED.finditer(cleaned):
        line = cleaned.count("\n", 0, match.start()) + 1
        issues.append(f"{label}:{line}: banned token {match.group(0)!r}")
    return tuple(issues)


def scan_lean_sources(project: Path) -> tuple[str, ...]:
    issues: list[str] = []
    for path in sorted(project.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        relative = path.relative_to(project).as_posix()
        issues.extend(_scan_source(path.read_text(encoding="utf-8"), relative))
    return tuple(issues)


def validate_substitution_value(name: str, value: str, kind: str = "token") -> str:
    """Require one explicitly supported Lean token or literal."""
    pattern = _SUBSTITUTION_PATTERNS.get(kind)
    if pattern is None:
        raise ValueError(f"unknown Lean substitution kind {kind!r} for {name!r}")
    if not isinstance(value, str) or pattern.fullmatch(value) is None:
        raise ValueError(
            f"Lean substitution {name!r} must be one valid {kind} token or literal"
        )
    return value


def render_contract(
    source: str,
    substitutions: Mapping[str, str],
    substitution_kinds: Mapping[str, str] | None = None,
) -> str:
    """Render only declared, strictly typed token/literal placeholders."""
    placeholders = {match.group("name") for match in _PLACEHOLDER.finditer(source)}
    supplied = set(substitutions)
    missing = placeholders - supplied
    unused = supplied - placeholders
    if missing:
        raise ValueError(f"contract has unresolved placeholders: {sorted(missing)}")
    if unused:
        raise ValueError(f"contract substitutions are unused: {sorted(unused)}")
    kinds = substitution_kinds or {}
    unknown_kinds = set(kinds) - placeholders
    if unknown_kinds:
        raise ValueError(
            f"contract substitution kinds are unused: {sorted(unknown_kinds)}"
        )
    validated = {
        name: validate_substitution_value(
            name, substitutions[name], kinds.get(name, "token")
        )
        for name in placeholders
    }
    return _PLACEHOLDER.sub(lambda match: validated[match.group("name")], source)


def _receipt(
    argv: tuple[str, ...], completed: CapturedCommand, duration: float
) -> GateCommandReceipt:
    assert completed.exit_code is not None
    return GateCommandReceipt(
        argv=argv,
        exit_code=completed.exit_code,
        duration_seconds=round(duration, 3),
        stdout=completed.stdout,
        stderr=completed.stderr,
        stdout_truncated=completed.stdout_truncated,
        stderr_truncated=completed.stderr_truncated,
        stdout_sha256=completed.stdout_sha256,
        stderr_sha256=completed.stderr_sha256,
        sandbox=completed.sandbox,
    )


def _run(
    argv: tuple[str, ...],
    project: Path,
    timeout: float,
    execution: ExecutionSpec | None,
    run_dir: Path | None,
    *,
    read_paths: tuple[Path, ...] = (),
) -> tuple[GateCommandReceipt | None, str | None]:
    started = time.monotonic()
    completed = run_captured_command(
        argv,
        cwd=project,
        env=os.environ,
        timeout=timeout,
        execution=execution,
        workspace=project,
        run_dir=run_dir or project,
        read_paths=read_paths,
    )
    if completed.error is not None:
        return None, f"cannot execute {argv!r}: {completed.error}"
    receipt = _receipt(argv, completed, time.monotonic() - started)
    if completed.exit_code != 0:
        return receipt, f"command exited with {completed.exit_code}: {argv!r}"
    if "sorryAx" in completed.stdout or "sorryAx" in completed.stderr:
        return receipt, f"command reported sorryAx: {argv!r}"
    return receipt, None


def _parse_axiom_reports(
    output: str, expected_declarations: tuple[str, ...]
) -> tuple[tuple[AxiomReport, ...], tuple[str, ...]]:
    parsed: list[AxiomReport] = []
    errors: list[str] = []
    for index, line in enumerate(output.splitlines()):
        if not line.strip():
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            errors.append(f"trusted axiom audit line {index + 1} is not valid JSON")
            continue
        if (
            not isinstance(value, dict)
            or set(value) != {"declaration", "axioms"}
            or not isinstance(value.get("declaration"), str)
            or re.fullmatch(_IDENTIFIER_TEXT, value["declaration"]) is None
            or not isinstance(value.get("axioms"), list)
            or not all(
                isinstance(axiom, str)
                and re.fullmatch(_IDENTIFIER_TEXT, axiom) is not None
                for axiom in value["axioms"]
            )
        ):
            errors.append(f"trusted axiom audit line {index + 1} has invalid structure")
            continue
        parsed.append(
            AxiomReport(
                declaration=value["declaration"],
                axioms=tuple(value["axioms"]),
            )
        )

    unexpected = sorted(
        {
            report.declaration
            for report in parsed
            if report.declaration not in expected_declarations
        }
    )
    if unexpected:
        errors.append(
            f"trusted axiom audit reported unrequested declarations: {unexpected}"
        )
    reports: list[AxiomReport] = []
    for declaration in expected_declarations:
        matches = [report for report in parsed if report.declaration == declaration]
        if len(matches) != 1:
            errors.append(
                "trusted axiom audit must produce exactly one report for "
                f"{declaration!r}; found {len(matches)}"
            )
            continue
        reports.append(matches[0])
    return tuple(reports), tuple(errors)


def run_proof_gate(
    project: Path,
    *,
    contract_path: Path,
    substitutions: Mapping[str, str] | None,
    allowed_axioms: tuple[str, ...],
    lake: str = "lake",
    timeout: float = 900.0,
    execution: ExecutionSpec | None = None,
    run_dir: Path | None = None,
) -> ProofGateResult:
    """Build the project and compile an immutable external acceptance contract."""
    contract_source = contract_path.read_text(encoding="utf-8")
    effective_substitutions = dict(substitutions or {})
    rendered = render_contract(contract_source, effective_substitutions)
    contract_declarations = tuple(
        match.group("declaration")
        for match in _PRINT_AXIOMS.finditer(_strip_lean_comments_and_strings(rendered))
    )
    source_issues = (
        *scan_lean_sources(project),
        *_scan_source(rendered, f"contract:{contract_path.name}"),
    )
    contract_issues: list[str] = []
    if not contract_declarations:
        contract_issues.append("Lean contract contains no #print axioms declaration")
    duplicate_declarations = sorted(
        {
            declaration
            for declaration in contract_declarations
            if contract_declarations.count(declaration) > 1
        }
    )
    if duplicate_declarations:
        contract_issues.append(
            "Lean contract requests duplicate #print axioms declarations: "
            f"{duplicate_declarations}"
        )
    errors = [*source_issues, *contract_issues]
    receipts: list[GateCommandReceipt] = []
    build_receipt, build_error = _run(
        (lake, "build"), project, timeout, execution, run_dir
    )
    if build_receipt is not None:
        receipts.append(build_receipt)
    if build_error is not None:
        errors.append(build_error)

    lean_path: Path | None = None
    if build_error is None:
        which_receipt, which_error = _run(
            (lake, "env", "which", "lean"),
            project,
            timeout,
            execution,
            run_dir,
        )
        if which_receipt is not None:
            receipts.append(which_receipt)
        if which_error is not None:
            errors.append(which_error)
        elif which_receipt is not None:
            candidate = which_receipt.stdout.strip()
            candidate_path = Path(candidate)
            if (
                which_receipt.stdout_truncated
                or which_receipt.stderr_truncated
                or which_receipt.stderr.strip()
                or "\n" in candidate
                or not candidate_path.is_absolute()
                or not candidate_path.is_file()
                or not os.access(candidate_path, os.X_OK)
                or candidate_path.resolve().is_relative_to(project.resolve())
            ):
                errors.append("lake returned no trusted Lean executable")
            else:
                lean_path = candidate_path.resolve()

    reports: tuple[AxiomReport, ...] = ()
    if lean_path is not None:
        with tempfile.TemporaryDirectory(prefix="proof-builder-lean-audit-") as root:
            trusted_root = Path(root)
            token = secrets.token_hex(12)
            audit_path = trusted_root / f"_ProofBuilderContract_{token}.lean"
            reader_path = trusted_root / "_ProofBuilderCertificateReader.lean"
            staging_olean = project / f"_ProofBuilderContract_{token}.olean"
            trusted_olean = audit_path.with_suffix(".olean")
            audit_source, audit_prefix = _render_trusted_audit(
                rendered, contract_declarations, token
            )
            audit_path.write_text(audit_source, encoding="utf-8")
            reader_path.write_text(_TRUSTED_CERTIFICATE_READER, encoding="utf-8")
            try:
                compile_argv = (
                    lake,
                    "env",
                    "lean",
                    "-R",
                    str(trusted_root),
                    "-o",
                    staging_olean.name,
                    str(audit_path),
                )
                compile_receipt, compile_error = _run(
                    compile_argv,
                    project,
                    timeout,
                    execution,
                    run_dir,
                    read_paths=(trusted_root,),
                )
                if compile_receipt is not None:
                    receipts.append(compile_receipt)
                if compile_error is not None:
                    errors.append(compile_error)
                elif not staging_olean.is_file() or staging_olean.is_symlink():
                    errors.append(
                        "Lean contract compiler produced no regular certificate"
                    )
                else:
                    shutil.copyfile(staging_olean, trusted_olean)
                    reader_argv = (
                        str(lean_path),
                        "-R",
                        str(trusted_root),
                        "--run",
                        str(reader_path),
                        str(trusted_olean),
                        audit_prefix,
                        "--",
                        *contract_declarations,
                    )
                    reader_receipt, reader_error = _run(
                        reader_argv,
                        project,
                        timeout,
                        execution,
                        run_dir,
                        read_paths=(trusted_root,),
                    )
                    if reader_receipt is not None:
                        receipts.append(reader_receipt)
                    if reader_error is not None:
                        errors.append(reader_error)
                    elif reader_receipt is not None:
                        if (
                            reader_receipt.stdout_truncated
                            or reader_receipt.stderr_truncated
                            or reader_receipt.stderr.strip()
                        ):
                            errors.append(
                                "trusted axiom certificate output was invalid"
                            )
                        else:
                            reports, report_errors = _parse_axiom_reports(
                                reader_receipt.stdout, contract_declarations
                            )
                            errors.extend(report_errors)
            finally:
                staging_olean.unlink(missing_ok=True)
    unexpected = sorted(
        {
            axiom
            for report in reports
            for axiom in report.axioms
            if axiom not in allowed_axioms
        }
    )
    if unexpected:
        errors.append(f"contract declarations use unapproved axioms: {unexpected}")

    return ProofGateResult(
        status="failed" if errors else "passed",
        contract_name=contract_path.name,
        contract_sha256=hashlib.sha256(contract_source.encode("utf-8")).hexdigest(),
        rendered_contract_sha256=hashlib.sha256(rendered.encode("utf-8")).hexdigest(),
        substitutions=MappingProxyType(effective_substitutions),
        axiom_reports=reports,
        source_issues=tuple(source_issues),
        command_receipts=tuple(receipts),
        errors=tuple(errors),
    )


def failed_proof_gate(
    contract_path: Path,
    error: str,
    substitutions: Mapping[str, str] | None = None,
) -> ProofGateResult:
    """Create a retained gate failure before Lean execution is possible."""
    source = contract_path.read_text(encoding="utf-8")
    effective_substitutions = dict(substitutions or {})
    try:
        rendered = render_contract(source, effective_substitutions)
    except ValueError:
        rendered = source
    return ProofGateResult(
        status="failed",
        contract_name=contract_path.name,
        contract_sha256=hashlib.sha256(source.encode("utf-8")).hexdigest(),
        rendered_contract_sha256=hashlib.sha256(rendered.encode("utf-8")).hexdigest(),
        substitutions=MappingProxyType(effective_substitutions),
        axiom_reports=(),
        source_issues=(),
        command_receipts=(),
        errors=(error,),
    )
