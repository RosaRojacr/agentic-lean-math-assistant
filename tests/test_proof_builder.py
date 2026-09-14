from __future__ import annotations

import json
from pathlib import Path

import pytest

import agentic_lean_math_assistant.proof_builder as proof_builder_module
from agentic_lean_math_assistant.cli import main
from agentic_lean_math_assistant.proof_builder import (
    ProofBuilderError,
    build_proof_package,
    collect_review_findings,
    compare_proof_packages,
    discover_lean_declarations,
    format_proof_failure,
    plan_proof_package,
    preflight_proof_package,
    preview_proof_package,
    proof_package_status,
    record_review_dispositions,
    resume_proof_package,
    verify_proof_package,
)


def _executable(path: Path, source: str) -> Path:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)
    return path


def _fake_lake(path: Path) -> Path:
    return _executable(
        path,
        r"""#!/usr/bin/env python3
import json
import pathlib
import re
import sys
cache = pathlib.Path.cwd() / ".lake" / "build"
cache.mkdir(parents=True, exist_ok=True)
(cache / "generated-artifact").write_bytes(b"generated")

if sys.argv[1:] in (["update"], ["exe", "cache", "get"]):
    print("Lake setup completed.")
elif sys.argv[1:] == ["build"] or (
    len(sys.argv) in (3, 4)
    and sys.argv[-2] == "build"
    and sys.argv[-1].startswith("+")
):
    print("Build completed successfully.")
elif sys.argv[1:] == ["env", "which", "lean"]:
    print(pathlib.Path(sys.argv[0]).resolve())
elif sys.argv[1:3] == ["env", "lean"] and sys.argv[-1] == "_ProofBuilderDependencies.lean":
    source = pathlib.Path(sys.argv[-1]).read_text(encoding="utf-8")
    output = pathlib.Path(
        json.loads(re.search(r'IO\.FS\.writeFile ("[^"]+") output', source).group(1))
    )
    inventory = json.loads(
        (pathlib.Path.cwd().parent / "declaration-inventory.json").read_text(
            encoding="utf-8"
        )
    )
    output.write_text(
        "".join(f"{item['declaration']}\n" for item in inventory["declarations"]),
        encoding="utf-8",
    )
elif sys.argv[1:3] == ["env", "lean"] and sys.argv[-1].endswith("Declarations.lean"):
    source = pathlib.Path(sys.argv[-1]).read_text(encoding="utf-8")
    output = pathlib.Path(
        json.loads(re.search(r'IO\.FS\.writeFile ("[^"]+")', source).group(1))
    )
    names_text = re.search(r"let names : List Name := \[([^\]]+)\]", source).group(1)
    names = [name.strip().lstrip("`") for name in names_text.split(",")]
    output.write_text(json.dumps([
        {"declaration": name, "type": "True",
         "axioms": ["propext", "Classical.choice", "Quot.sound"]}
        for name in names
    ]), encoding="utf-8")
elif "--run" in sys.argv:
    separator = sys.argv.index("--")
    for declaration in sys.argv[separator + 1:]:
        print(json.dumps({
            "declaration": declaration,
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        }))
else:
    pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"fake olean")
""",
    )


def _fake_omp(path: Path) -> Path:
    return _executable(
        path,
        r"""#!/usr/bin/env python3
import json
import pathlib
import re
import sys

prompt_path = pathlib.Path(next(value[1:] for value in sys.argv if value.startswith("@")))
prompt = prompt_path.read_text(encoding="utf-8")
handoff = pathlib.Path(re.search(r"Write `([^`]+)` as strict JSON", prompt).group(1))
handoff.parent.mkdir(parents=True, exist_ok=True)
package = prompt_path.parents[2]
inventory = json.loads(
    (package / "supporting-materials/declaration-inventory.json").read_text(encoding="utf-8")
)
conceptual = [item for item in inventory["declarations"] if item["generated_family"] is None]
attempt = int(prompt_path.name.split("-", 1)[0])
if prompt.startswith("# Isolated proof-package author pass"):
    handoff.write_text(json.dumps({
        "schema_version": 1,
        "main_markdown": (
            "## Theorem\n\nThe helper [@lean:Support.helper] proves the premise, and "
            "[@lean:Example.main_theorem] proves the stated result, while "
            "[@lean:Example.corollary] records its secondary formulation.\n\n"
            "## Published boundary\n\nNo stronger claim is made."
        ),
        "supplement_introduction": "Every conceptual declaration is reproduced below.",
        "classifications": [{
            "declaration": item["declaration"],
            "category": "main",
            "informal_statement": "The proposition True is inhabited.",
            "latex_explanation": "The conclusion is $\\mathrm{True}$, witnessed directly.",
        } for item in conceptual],
        "generated_families": [],
        "external_citations": [],
    }), encoding="utf-8")
else:
    author_path = pathlib.Path(
        re.search(r"author's structured claims at\n`([^`]+)`", prompt).group(1)
    )
    author = json.loads(author_path.read_text(encoding="utf-8"))
    statements = {
        item["declaration"]: item["informal_statement"]
        for item in author["classifications"]
    }
    reject = attempt == 1
    handoff.write_text(json.dumps({
        "schema_version": 1,
        "package_relation": "mismatch" if reject else "equivalent",
        "critical_errors": ["First-pass adversarial rejection."] if reject else [],
        "main_proof_critical_errors": [],
        "supplement_critical_errors": [],
        "external_citation_issues": [],
        "audit_markdown": "The declarations were compared against the exposition.",
        "reviews": [{
            "declaration": item["declaration"],
            "source_sha256": item["code_sha256"],
            "informal_statement": statements[item["declaration"]],
            "relation": "mismatch" if reject else "equivalent",
            "added_hypotheses": [],
            "omitted_hypotheses": [],
            "quantifier_issues": [],
            "domain_issues": [],
            "boundary_issues": [],
            "symbol_mismatches": [],
            "critical_errors": ["Deliberate first-pass finding."] if reject else [],
            "reason": "Rejected for repair." if reject else "The meanings agree.",
        } for item in conceptual],
        "generated_family_reviews": [],
    }), encoding="utf-8")
print("handoff complete")
""",
    )


def _fake_pandoc(path: Path) -> Path:
    return _executable(
        path,
        r"""#!/usr/bin/env python3
import pathlib
import sys
output = next(value.split("=", 1)[1] for value in sys.argv if value.startswith("--output="))
source = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
pathlib.Path(output).write_text("<html><body>" + source + "</body></html>", encoding="utf-8")
""",
    )


def _fake_chromium(path: Path) -> Path:
    return _executable(
        path,
        r"""#!/usr/bin/env python3
import pathlib
import sys
output = next(value.split("=", 1)[1] for value in sys.argv if value.startswith("--print-to-pdf="))
pathlib.Path(output).write_bytes(b"%PDF-1.4\nfixture\n%%EOF\n")
""",
    )


def _fixture(tmp_path: Path) -> tuple[Path, Path, Path]:
    project = tmp_path / "project"
    proof = project / "proof"
    reports = project / "reports"
    tools = tmp_path / "tools"
    proof.mkdir(parents=True)
    reports.mkdir()
    tools.mkdir()
    (project / "references").mkdir()
    (project / "knowledge").mkdir()
    (project / "runs").mkdir()
    (project / "problem.md").write_text("Prove True.\n", encoding="utf-8")
    (project / "project.toml").write_text(
        """schema_version = 1
[project]
id = "fixture"
title = "Fixture"
problem = "problem.md"
references = "references"
knowledge = "knowledge"
runs = "runs"
[regime]
omp = "omp"
strategy_reflection_model = "openai-codex/gpt-6-astra"
targeted_task_model = "openai-codex/gpt-6-astra"
[execution]
sandbox = false
""",
        encoding="utf-8",
    )
    (proof / "Support.lean").write_text(
        "namespace Support\n\ntheorem helper : True := by trivial\n\nend Support\n",
        encoding="utf-8",
    )
    (proof / "Example.lean").write_text(
        "import Support\n\nnamespace Example\n\n"
        "theorem main_theorem : True := Support.helper\n\n"
        "theorem corollary : True := main_theorem\n\nend Example\n",
        encoding="utf-8",
    )
    (proof / "lean-toolchain").write_text("leanprover/lean4:test\n", encoding="utf-8")
    (proof / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
    (proof / "lakefile.toml").write_text(
        """name = "Fixture"
version = "0.1.0"
defaultTargets = ["Example"]

[[lean_lib]]
name = "Fixture"
roots = ["Example", "Support"]
""",
        encoding="utf-8",
    )
    lake = _fake_lake(tools / "lake")
    omp = _fake_omp(tools / "omp")
    pandoc = _fake_pandoc(tools / "pandoc")
    chromium = _fake_chromium(tools / "chromium")
    manifest = reports / "proof-package.toml"
    manifest.write_text(
        f"""schema_version = 1
[package]
id = "fixture-proof"
version = "v1"
title = "Fixture Theorem"
author = "Test Author"
audience = "A mathematician with no Lean experience."
informal_claim = "The proposition True holds."
closing_scope = "State that no stronger theorem is claimed."
project = "../project.toml"
output = "fixture-proof-v1"
canonical_pdf = "fixture-proof.pdf"
references = []
[lean]
workspace = "../proof"
lakefile = "lakefile.toml"
support_files = ["lean-toolchain", "lake-manifest.json"]
generated_globs = []
forbidden_declarations = []
build_command = ["lake", "build"]
verification_commands = []
allowed_axioms = ["propext", "Quot.sound", "Classical.choice"]
timeout_seconds = 60
[[roots]]
module = "Example"
declaration = "Example.main_theorem"
role = "primary"
type = "True"
informal_statement = "The proposition True holds."
[[roots]]
module = "Example"
declaration = "Example.corollary"
role = "secondary"
type = "True"
informal_statement = "The secondary formulation also states that True holds."
[models]
max_revisions = 3
timeout_seconds = 60
[render]
pandoc = "{pandoc}"
chromium = "{chromium}"
timeout_seconds = 60
""",
        encoding="utf-8",
    )
    return manifest, omp, lake


def test_proof_builder_creates_clean_reviewed_package(tmp_path: Path) -> None:
    manifest, omp, lake = _fixture(tmp_path)

    result = build_proof_package(
        manifest,
        omp=str(omp),
        lake=str(lake),
        author_model="provider/economical-author",
        reviewer_model="provider/economical-reviewer",
        review_profile="economical",
        max_model_calls=4,
    )

    package = result.package_dir
    assert result.status == "verified"
    assert result.revision_attempts == 2
    assert {path.name for path in package.iterdir()} == {
        "README.md",
        "MainProof.pdf",
        "LemmaSupplement.pdf",
        "SemanticAudit.pdf",
        "supporting-materials",
    }
    assert (package / "supporting-materials/lean/Example.lean").is_file()
    assert (package / "supporting-materials/lean/Support.lean").is_file()
    assert not (package / "supporting-materials/manuscripts").exists()
    assert not (package / "supporting-materials/lean/.lake").exists()
    readme = (package / "README.md").read_text(encoding="utf-8")
    assert "rendering intermediates are discarded after PDF creation" in readme
    rendering = json.loads(
        (package / "supporting-materials/receipts/rendering.json").read_text(
            encoding="utf-8"
        )
    )
    rendered_arguments = {
        argument for receipt in rendering for argument in receipt["argv"]
    }
    assert any("proof-package-main.css" in value for value in rendered_arguments)
    assert any("proof-package-technical.css" in value for value in rendered_arguments)
    assert "Other" not in (
        package / "supporting-materials/lean/lakefile.toml"
    ).read_text(encoding="utf-8")
    exported_lakefile = (package / "supporting-materials/lean/lakefile.toml").read_text(
        encoding="utf-8"
    )
    assert 'defaultTargets = ["ProofPackage"]' in exported_lakefile
    assert '"Example"' in exported_lakefile
    assert '"Support"' in exported_lakefile
    lock = json.loads(
        (package / "supporting-materials/MANIFEST.lock.json").read_text(
            encoding="utf-8"
        )
    )
    assert [root["role"] for root in lock["roots"]] == ["primary", "secondary"]
    assert lock["models"]["author"]["route"] == "provider/economical-author"
    assert (
        lock["models"]["semantic_reviewer"]["route"] == "provider/economical-reviewer"
    )
    assert lock["models"]["review_profile"] == "economical"
    assert lock["models"]["fallback_policy"] == "disabled"
    assert (manifest.parent / "fixture-proof.pdf").read_bytes() == (
        package / "MainProof.pdf"
    ).read_bytes()
    assert verify_proof_package(package, lake=str(lake), mode="full") > 10


def test_proof_builder_integrity_rejects_tampering(tmp_path: Path) -> None:
    manifest, omp, lake = _fixture(tmp_path)
    package = build_proof_package(manifest, omp=str(omp), lake=str(lake)).package_dir
    (package / "MainProof.pdf").write_bytes(b"tampered")

    with pytest.raises(ProofBuilderError, match="digest mismatch"):
        verify_proof_package(package, lake=str(lake), mode="checksums")


def test_publication_boundary_rejects_forbidden_declaration(tmp_path: Path) -> None:
    manifest, omp, lake = _fixture(tmp_path)
    text = manifest.read_text(encoding="utf-8").replace(
        "forbidden_declarations = []",
        'forbidden_declarations = ["Support.helper"]',
    )
    manifest.write_text(text, encoding="utf-8")

    with pytest.raises(ProofBuilderError, match="forbidden declarations"):
        build_proof_package(manifest, omp=str(omp), lake=str(lake))


def test_proof_builder_resumes_unfinalized_crash(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest, omp, lake = _fixture(tmp_path)
    original_invoke = proof_builder_module._invoke_model

    def crash(**_kwargs: object) -> Path:
        raise ProofBuilderError("simulated crash")

    monkeypatch.setattr(proof_builder_module, "_invoke_model", crash)
    with pytest.raises(ProofBuilderError, match="simulated crash"):
        build_proof_package(manifest, omp=str(omp), lake=str(lake))

    monkeypatch.setattr(proof_builder_module, "_invoke_model", original_invoke)
    package = manifest.parent / "fixture-proof-v1"
    result = resume_proof_package(package, omp=str(omp), lake=str(lake))

    assert result.status == "verified"


def test_cli_initializes_manifest_without_overwrite(tmp_path: Path) -> None:
    manifest = tmp_path / "proof-package.toml"

    assert main(["proof-builder", "init", "--manifest", str(manifest)]) == 0
    assert "[[roots]]" in manifest.read_text(encoding="utf-8")
    with pytest.raises(SystemExit):
        main(["proof-builder", "init", "--manifest", str(manifest)])


def test_declaration_anchors_preserve_case_sensitive_identity() -> None:
    assert proof_builder_module._anchor("Namespace.rootProjection") != (
        proof_builder_module._anchor("Namespace.RootProjection")
    )


def test_planning_preflight_discovery_and_preview_are_model_free(
    tmp_path: Path,
) -> None:
    manifest, omp, lake = _fixture(tmp_path)

    plan = plan_proof_package(
        manifest,
        reviewer_model="provider/lower-tier-reviewer",
        review_profile="standard",
        max_model_calls=5,
    )
    assert plan["output_exists"] is False
    assert plan["limits"] == {
        "max_revisions": 2,
        "max_model_calls": 5,
        "planned_model_calls": 5,
    }
    models = plan["models"]
    assert isinstance(models, dict)
    reviewer = models["semantic_reviewer"]
    assert isinstance(reviewer, dict)
    assert reviewer["route"] == "provider/lower-tier-reviewer"
    report = preflight_proof_package(
        manifest,
        omp=str(omp),
        lake=str(lake),
        run_lean=False,
    )
    assert report["ok"] is True
    assert report["lean_verified"] is False

    declarations = discover_lean_declarations(
        manifest,
        lake=str(lake),
        contains="main_theorem",
    )
    assert declarations == [
        {
            "declaration": "Example.main_theorem",
            "kind": "theorem",
            "module": "Example",
            "source": "Example.lean",
            "line": 5,
            "type": "True",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
            "generated_family": None,
        }
    ]

    preview = preview_proof_package(manifest)
    assert {path.name for path in preview.iterdir()} == {
        "README.md",
        "MainProof.pdf",
        "LemmaSupplement.pdf",
        "SemanticAudit.pdf",
        "supporting-materials",
    }
    assert (
        json.loads(
            (preview / "supporting-materials/preview.json").read_text(encoding="utf-8")
        )["status"]
        == "unverified-preview"
    )


def test_failed_review_disposition_targeted_resume_and_status(tmp_path: Path) -> None:
    manifest, omp, lake = _fixture(tmp_path)
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            "max_revisions = 3", "max_revisions = 0"
        ),
        encoding="utf-8",
    )
    failed = build_proof_package(manifest, omp=str(omp), lake=str(lake))
    assert failed.status == "review_failed"
    assert "First-pass adversarial rejection." in format_proof_failure(failed)
    findings = collect_review_findings(failed.package_dir)
    assert findings[0]["finding"] == "First-pass adversarial rejection."

    sidecar = record_review_dispositions(
        failed.package_dir,
        decisions=("F001=repair:Correct the rejected explanation.",),
    )
    assert sidecar.is_file()
    rerendered = resume_proof_package(
        failed.package_dir,
        lake=str(lake),
        from_stage="pdf-render",
    )
    assert rerendered.status == "review_failed"
    checksum = failed.package_dir / "supporting-materials/CHECKSUMS.sha256"
    checksum.unlink()
    rechecksummed = resume_proof_package(
        failed.package_dir,
        from_stage="checksum-ledger",
    )
    assert rechecksummed.status == "review_failed"
    assert checksum.is_file()

    accepted = resume_proof_package(
        failed.package_dir,
        omp=str(omp),
        lake=str(lake),
        from_stage="semantic-review",
        review_profile="strict",
        max_model_calls=8,
        reviewer_model="provider/lower-tier-reviewer",
    )
    assert accepted.status == "verified"
    assert (
        accepted.package_dir / "supporting-materials/reviews/operator-dispositions.json"
    ).is_file()
    assert (
        len(
            tuple(
                (accepted.package_dir / "supporting-materials/receipts").glob(
                    "*-author.request.json"
                )
            )
        )
        == 1
    )
    health = proof_package_status(accepted.package_dir)
    assert health["status"] == "verified"
    assert health["ledger"] == "valid"
    assert (
        compare_proof_packages(accepted.package_dir, accepted.package_dir)["different"]
        is False
    )
    assert (
        verify_proof_package(
            accepted.package_dir,
            lake=str(lake),
            mode="lean",
        )
        == 0
    )


def test_model_call_budget_fails_before_unbudgeted_review(tmp_path: Path) -> None:
    manifest, omp, lake = _fixture(tmp_path)

    with pytest.raises(ProofBuilderError, match="model-call budget exhausted"):
        build_proof_package(
            manifest,
            omp=str(omp),
            lake=str(lake),
            max_model_calls=1,
        )


def test_cli_exposes_dry_run_status_and_structured_verification(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    manifest, omp, lake = _fixture(tmp_path)
    assert (
        main(
            [
                "proof-builder",
                "build",
                "--manifest",
                str(manifest),
                "--dry-run",
                "--format",
                "json",
                "--semantic-review-model",
                "provider/reviewer",
            ]
        )
        == 0
    )
    assert '"fallback_policy": "disabled"' in capsys.readouterr().out
    package = build_proof_package(manifest, omp=str(omp), lake=str(lake)).package_dir
    assert (
        main(
            [
                "proof-builder",
                "status",
                "--package",
                str(package),
                "--format",
                "json",
            ]
        )
        == 0
    )
    assert '"ledger": "valid"' in capsys.readouterr().out
    assert (
        main(
            [
                "proof-builder",
                "verify",
                "--package",
                str(package),
                "--checksums-only",
                "--format",
                "json",
            ]
        )
        == 0
    )
    assert '"mode": "checksums"' in capsys.readouterr().out
