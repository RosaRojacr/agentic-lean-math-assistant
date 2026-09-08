"""Hidden post-run evaluator for the cold CMV range-reduction benchmark."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from collections.abc import Callable
from decimal import Decimal, InvalidOperation
from pathlib import Path

TARGET_CUTOFF = Decimal("1.25819")
RESULT_KEYS = {
    "artifact_type",
    "certificate_checker",
    "cutoff",
    "declaration",
    "module",
    "report",
    "schema_version",
}
FORBIDDEN_INPUT_TOKENS = (
    b"1.25819",
    b"1.258185",
    b"1.258184",
    b"1.3026632",
    b"min_g_gt_witness",
    b"cmv_comparison_bound_optimized",
)
FORBIDDEN_LEAN = re.compile(r"(?m)^\s*(?:axiom|constant|extern|unsafe)\b")
ALLOWED_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}


def _canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _source_digest(root: Path) -> str:
    digest = hashlib.sha256()
    for path in sorted(item for item in root.rglob("*") if item.is_file()):
        relative = path.relative_to(root)
        if ".lake" in relative.parts or relative.name == "lake-manifest.json":
            continue
        digest.update(relative.as_posix().encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def _run(command: list[str], *, cwd: Path, timeout: int) -> tuple[int, str, str]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=timeout,
        check=False,
    )
    return completed.returncode, completed.stdout, completed.stderr


def _detail(stdout: str, stderr: str) -> str:
    text = (stdout + "\n" + stderr).strip()
    return text[-4000:]


def _exact_input_snapshot(run: Path) -> tuple[bool, str]:
    snapshot = run / "input-snapshot"
    proof = snapshot / "proof"
    references = snapshot / "references"
    if (
        not proof.is_dir()
        or proof.is_symlink()
        or not references.is_dir()
        or references.is_symlink()
    ):
        return False, "snapshot proof or references directory is missing or a symlink"
    expected_proof = {"lakefile.toml", "lean-toolchain"}
    proof_files = {
        path.relative_to(proof).as_posix()
        for path in proof.rglob("*")
        if path.is_file()
    }
    reference_files = {
        path.relative_to(references).as_posix()
        for path in references.rglob("*")
        if path.is_file()
    }
    if proof_files != expected_proof:
        return False, f"unexpected proof inputs: {sorted(proof_files)}"
    if reference_files != {"Canete2010.pdf"}:
        return False, f"unexpected reference inputs: {sorted(reference_files)}"
    unsafe = [
        str(path.relative_to(snapshot))
        for path in snapshot.rglob("*")
        if path.is_symlink()
    ]
    if unsafe:
        return False, f"snapshot contains symlinks: {unsafe}"
    for path in sorted(item for item in snapshot.rglob("*") if item.is_file()):
        data = path.read_bytes()
        found = [token.decode() for token in FORBIDDEN_INPUT_TOKENS if token in data]
        if found:
            return False, f"hidden result material occurs in {path.name}: {found}"
    return True, "snapshot contains only the blank Lean skeleton and primary paper"


def _load_result(proof: Path) -> tuple[dict[str, object], Decimal]:
    path = proof / "result.json"
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict) or set(value) != RESULT_KEYS:
        raise ValueError("result.json does not match its exact field contract")
    if raw != _canonical(value):
        raise ValueError("result.json is not canonical JSON")
    if (
        value["artifact_type"]
        != "application/vnd.agentic-lean.cmv-range-reduction.v1+json"
        or value["schema_version"] != 1
        or value["module"] != "RangeReduction"
        or value["declaration"] != "cmv_range_reduction"
        or value["certificate_checker"] != "verify_certificate.py"
        or value["report"] != "technical-report.md"
    ):
        raise ValueError("result.json identity is invalid")
    raw_cutoff = value["cutoff"]
    if not isinstance(raw_cutoff, str) or not re.fullmatch(
        r"[0-9]+\.[0-9]+", raw_cutoff
    ):
        raise ValueError("cutoff must be an unsigned finite decimal string")
    try:
        cutoff = Decimal(raw_cutoff)
    except InvalidOperation as exc:
        raise ValueError("cutoff is not a decimal") from exc
    if not cutoff.is_finite() or cutoff <= 1 or cutoff > TARGET_CUTOFF:
        raise ValueError(f"certified cutoff {cutoff} does not reach {TARGET_CUTOFF}")
    return value, cutoff


def _lean_contract(cutoff: Decimal) -> str:
    literal = format(cutoff, "f")
    return f"""import RangeReduction

open Real Set

example : ∀ θ : ℝ, ell θ = θ / Real.sin θ := ell_formula
example : ∀ θ : ℝ, area θ = (θ - Real.sin θ * Real.cos θ) / (4 * Real.sin θ ^ 2) := area_formula
example : ∀ {{x : ℝ}}, 0 < x → θOf x ∈ Set.Ioo 0 Real.pi := thetaOf_mem
example : ∀ {{x : ℝ}}, 0 < x → area (θOf x) = x := area_thetaOf
example : ∀ x : ℝ, arc x = ell (θOf x) := arc_formula
example : ∀ x : ℝ, g x = 2 * arc x - arc (2 * x) := g_formula
example : ∀ {{x : ℝ}}, 0 < x → HasDerivAt arc (2 * Real.sin (θOf x)) x := hasDerivAt_arc
example : ∀ {{x : ℝ}}, 0 < x → Real.pi / 4 < g x := min_g_gt_pi_div_four
example : ∀ {{lam x : ℝ}}, ({literal} : ℝ) ≤ lam → 0 < x → 1 / lam < g x := cmv_range_reduction

#print axioms ell_formula
#print axioms area_formula
#print axioms thetaOf_mem
#print axioms area_thetaOf
#print axioms arc_formula
#print axioms g_formula
#print axioms hasDerivAt_arc
#print axioms min_g_gt_pi_div_four
#print axioms cmv_range_reduction
"""


def _axioms_allowed(output: str) -> tuple[bool, str]:
    reports = re.findall(r"depends on axioms: \[([^\]]*)\]", output)
    if len(reports) < 9:
        return False, "Lean did not print all nine required axiom reports"
    observed: set[str] = set()
    for report in reports:
        observed.update(item.strip() for item in report.split(",") if item.strip())
    unexpected = observed - ALLOWED_AXIOMS
    if unexpected:
        return False, f"unexpected axioms: {sorted(unexpected)}"
    return True, f"allowed axioms only: {sorted(observed)}"


def evaluate(run: Path, lake: str) -> dict[str, object]:
    checks: list[dict[str, object]] = []

    def check(check_id: str, action: Callable[[], tuple[bool, str]]) -> bool:
        try:
            passed, detail = action()
        except Exception as exc:  # noqa: BLE001 - evaluator must report every failure
            passed, detail = False, f"{type(exc).__name__}: {exc}"
        checks.append({"id": check_id, "passed": passed, "detail": detail})
        return passed

    proof = run / "workspace" / "proof"
    result: dict[str, object] | None = None
    cutoff: Decimal | None = None

    check("cold-input-snapshot", lambda: _exact_input_snapshot(run))
    check(
        "proof-workspace",
        lambda: (
            proof.is_dir() and not proof.is_symlink(),
            f"proof workspace: {proof}",
        ),
    )

    def result_contract() -> tuple[bool, str]:
        nonlocal result, cutoff
        result, cutoff = _load_result(proof)
        return True, f"canonical result certifies cutoff {cutoff}"

    check("result-contract", result_contract)

    def required_files() -> tuple[bool, str]:
        paths = [
            proof / "RangeReduction.lean",
            proof / "verify_certificate.py",
            proof / "technical-report.md",
        ]
        invalid = [
            str(path) for path in paths if not path.is_file() or path.is_symlink()
        ]
        if invalid:
            return False, f"missing or unsafe required files: {invalid}"
        if len((proof / "technical-report.md").read_text(encoding="utf-8")) < 1000:
            return False, "technical report is too short to document the derivation"
        return True, "all required proof, certificate, and report files are retained"

    check("required-files", required_files)

    def forbidden_constructs() -> tuple[bool, str]:
        findings: list[str] = []
        for path in sorted(proof.rglob("*.lean")):
            if ".lake" in path.relative_to(proof).parts:
                continue
            match = FORBIDDEN_LEAN.search(path.read_text(encoding="utf-8"))
            if match:
                findings.append(f"{path.name}:{match.group(0)}")
        return not findings, "none" if not findings else f"forbidden: {findings}"

    check("forbidden-lean-constructs", forbidden_constructs)
    source_before = _source_digest(proof) if proof.is_dir() else ""

    def clean_build() -> tuple[bool, str]:
        lake_config = tomllib.loads(
            (proof / "lakefile.toml").read_text(encoding="utf-8")
        )
        package = lake_config.get("name")
        if not isinstance(package, str) or not package:
            return False, "lakefile.toml has no package name"
        clean_code, clean_stdout, clean_stderr = _run(
            [lake, "clean", package], cwd=proof, timeout=120
        )
        if clean_code != 0:
            return False, "lake clean failed:\n" + _detail(clean_stdout, clean_stderr)
        code, stdout, stderr = _run([lake, "build"], cwd=proof, timeout=1200)
        return code == 0, _detail(stdout, stderr)

    check("clean-lake-build", clean_build)

    def certificate() -> tuple[bool, str]:
        code, stdout, stderr = _run(
            [sys.executable, "-I", "verify_certificate.py"],
            cwd=proof,
            timeout=300,
        )
        if code == 0 and not stdout.strip():
            return False, "certificate checker produced no retained explanation"
        return code == 0, _detail(stdout, stderr)

    check("independent-certificate", certificate)

    lean_output = ""

    def theorem_contract() -> tuple[bool, str]:
        nonlocal lean_output
        if cutoff is None:
            return False, "result cutoff is unavailable"
        with tempfile.TemporaryDirectory(prefix="cmv-range-contract-") as temporary:
            contract = Path(temporary) / "ColdBenchmarkCheck.lean"
            contract.write_text(_lean_contract(cutoff), encoding="utf-8")
            code, stdout, stderr = _run(
                [lake, "env", "lean", str(contract)],
                cwd=proof,
                timeout=600,
            )
        lean_output = stdout + "\n" + stderr
        return code == 0, _detail(stdout, stderr)

    check("exact-lean-contract", theorem_contract)
    check("allowed-axioms", lambda: _axioms_allowed(lean_output))

    def source_unchanged() -> tuple[bool, str]:
        after = _source_digest(proof)
        return after == source_before, f"before={source_before} after={after}"

    check("validator-source-immutability", source_unchanged)
    passed = all(item["passed"] is True for item in checks)
    return {
        "checks": checks,
        "status": "passed" if passed else "failed",
        "summary": (
            f"cold CMV reconstruction verified at cutoff {cutoff}"
            if passed
            else "cold CMV reconstruction failed one or more hidden checks"
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--lake", required=True)
    args = parser.parse_args()
    try:
        result = evaluate(args.run_dir.expanduser().resolve(), args.lake)
    except Exception as exc:  # noqa: BLE001 - evaluator must always emit a result
        result = {
            "checks": [
                {
                    "id": "validator-internal-error",
                    "passed": False,
                    "detail": f"{type(exc).__name__}: {exc}",
                }
            ],
            "status": "failed",
            "summary": "hidden CMV evaluator encountered an internal error",
        }
    print(json.dumps(result, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
