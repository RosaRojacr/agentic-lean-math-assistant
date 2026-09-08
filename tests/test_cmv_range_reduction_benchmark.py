from __future__ import annotations

import importlib.util
import json
import shutil
from pathlib import Path
from types import ModuleType

import pytest

from agentic_lean_math_assistant.benchmark import BenchmarkSuite
from agentic_lean_math_assistant.project import ProjectSpec

ROOT = Path(__file__).resolve().parents[1]
BENCHMARK = ROOT / "benchmarks" / "cmv-range-reduction"
CASE = BENCHMARK / "case"


def _validator() -> ModuleType:
    path = BENCHMARK / "validation" / "validate_result.py"
    spec = importlib.util.spec_from_file_location("cmv_range_validator", path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _snapshot(tmp_path: Path) -> Path:
    run = tmp_path / "run"
    proof = run / "input-snapshot" / "proof"
    references = run / "input-snapshot" / "references"
    proof.mkdir(parents=True)
    references.mkdir(parents=True)
    shutil.copyfile(CASE / "proof" / "lakefile.toml", proof / "lakefile.toml")
    shutil.copyfile(CASE / "proof" / "lean-toolchain", proof / "lean-toolchain")
    shutil.copyfile(
        CASE / "references" / "Canete2010.pdf", references / "Canete2010.pdf"
    )
    return run


def _result(cutoff: str = "1.25819") -> dict[str, object]:
    return {
        "artifact_type": "application/vnd.agentic-lean.cmv-range-reduction.v1+json",
        "certificate_checker": "verify_certificate.py",
        "cutoff": cutoff,
        "declaration": "cmv_range_reduction",
        "module": "RangeReduction",
        "report": "technical-report.md",
        "schema_version": 1,
    }


def test_cmv_range_reduction_suite_loads_as_cold_case() -> None:
    suite = BenchmarkSuite.load(BENCHMARK / "benchmark.toml")
    project = ProjectSpec.load(suite.cases[0].project_manifest)

    assert suite.suite_id == "cmv-range-reduction"
    assert len(suite.cases) == 1
    assert suite.cases[0].expected_outcome == "solved"
    assert (
        suite.cases[0].validator
        == (BENCHMARK / "validation" / "validate_result.py").resolve()
    )
    assert project.project_id == "cold-cmv-range-reduction"
    assert [(item.target, item.source.name) for item in project.inputs] == [
        ("proof", "proof")
    ]
    assert sorted(path.name for path in (CASE / "proof").iterdir()) == [
        "lakefile.toml",
        "lean-toolchain",
    ]


def test_cmv_range_reduction_snapshot_accepts_only_blank_skeleton(
    tmp_path: Path,
) -> None:
    validator = _validator()
    run = _snapshot(tmp_path)

    accepted, detail = validator._exact_input_snapshot(run)

    assert accepted is True
    assert "blank Lean skeleton" in detail


@pytest.mark.parametrize("leak", ["1.25819", "1.3026632", "min_g_gt_witness"])
def test_cmv_range_reduction_snapshot_rejects_hidden_result_material(
    tmp_path: Path, leak: str
) -> None:
    validator = _validator()
    run = _snapshot(tmp_path)
    (run / "input-snapshot" / "proof" / "lakefile.toml").write_text(
        f"# {leak}\n", encoding="utf-8"
    )

    accepted, detail = validator._exact_input_snapshot(run)

    assert accepted is False
    assert "hidden result material" in detail


def test_cmv_range_reduction_snapshot_rejects_symlink(tmp_path: Path) -> None:
    validator = _validator()
    run = _snapshot(tmp_path)
    link = run / "input-snapshot" / "proof" / "leak"
    link.symlink_to(CASE / "problem.md")

    accepted, detail = validator._exact_input_snapshot(run)

    assert accepted is False
    assert "unexpected proof inputs" in detail or "symlinks" in detail


def test_cmv_range_reduction_result_accepts_hidden_threshold(tmp_path: Path) -> None:
    validator = _validator()
    proof = tmp_path / "proof"
    proof.mkdir()
    value = _result()
    (proof / "result.json").write_bytes(validator._canonical(value))

    loaded, cutoff = validator._load_result(proof)

    assert loaded == value
    assert str(cutoff) == "1.25819"


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ({"cutoff": "1.2581901"}, "does not reach"),
        ({"cutoff": "1"}, "unsigned finite decimal"),
        ({"extra": True}, "exact field contract"),
    ],
)
def test_cmv_range_reduction_result_rejects_false_closure(
    tmp_path: Path, mutation: dict[str, object], message: str
) -> None:
    validator = _validator()
    proof = tmp_path / "proof"
    proof.mkdir()
    value = _result()
    value.update(mutation)
    (proof / "result.json").write_bytes(validator._canonical(value))

    with pytest.raises(ValueError, match=message):
        validator._load_result(proof)


def test_cmv_range_reduction_result_rejects_noncanonical_json(tmp_path: Path) -> None:
    validator = _validator()
    proof = tmp_path / "proof"
    proof.mkdir()
    (proof / "result.json").write_text(json.dumps(_result()), encoding="utf-8")

    with pytest.raises(ValueError, match="canonical JSON"):
        validator._load_result(proof)


def test_cmv_range_reduction_axiom_gate_rejects_custom_axiom() -> None:
    validator = _validator()
    allowed = "\n".join(
        "'declaration' depends on axioms: [propext, Classical.choice, Quot.sound]"
        for _ in range(9)
    )
    rejected = allowed.replace("Quot.sound]", "Quot.sound, hiddenWitness]", 1)

    assert validator._axioms_allowed(allowed)[0] is True
    accepted, detail = validator._axioms_allowed(rejected)
    assert accepted is False
    assert "hiddenWitness" in detail


def test_cmv_range_reduction_evaluator_reports_missing_run_as_failure(
    tmp_path: Path,
) -> None:
    validator = _validator()

    result = validator.evaluate(tmp_path / "missing-run", "lake")

    assert result["status"] == "failed"
    assert any(check["passed"] is False for check in result["checks"])
