from __future__ import annotations

import json
from pathlib import Path

import pytest

import agentic_lean_math_assistant.proof_builder as proof_builder_module
from agentic_lean_math_assistant.cli import main
from agentic_lean_math_assistant.proof_builder import (
    ProofBuilderError,
    build_proof_package,
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
if prompt.startswith("# Isolated Astra proof-package author pass"):
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

    result = build_proof_package(manifest, omp=str(omp), lake=str(lake))

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
    assert (manifest.parent / "fixture-proof.pdf").read_bytes() == (
        package / "MainProof.pdf"
    ).read_bytes()
    assert verify_proof_package(package, lake=str(lake), rerun_lean=True) > 10


def test_proof_builder_integrity_rejects_tampering(tmp_path: Path) -> None:
    manifest, omp, lake = _fixture(tmp_path)
    package = build_proof_package(manifest, omp=str(omp), lake=str(lake)).package_dir
    (package / "MainProof.pdf").write_bytes(b"tampered")

    with pytest.raises(ProofBuilderError, match="digest mismatch"):
        verify_proof_package(package, lake=str(lake), rerun_lean=False)


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
    original_invoke = proof_builder_module._invoke_astra

    def crash(**_kwargs: object) -> Path:
        raise ProofBuilderError("simulated crash")

    monkeypatch.setattr(proof_builder_module, "_invoke_astra", crash)
    with pytest.raises(ProofBuilderError, match="simulated crash"):
        build_proof_package(manifest, omp=str(omp), lake=str(lake))

    monkeypatch.setattr(proof_builder_module, "_invoke_astra", original_invoke)
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
