from __future__ import annotations

import os
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.solve import (
    FormalContract,
    RuntimeLedger,
    SemanticContract,
    SolveError,
    SolveSpec,
    create_input_snapshot,
    parse_duration,
)


def test_parse_duration_accepts_supported_units() -> None:
    assert parse_duration("2h") == 7200
    assert parse_duration("45s") == 45

    with pytest.raises(ConfigurationError, match="invalid duration"):
        parse_duration("soon")


def test_solve_spec_loads_defaults_and_overrides(tmp_path: Path) -> None:
    (tmp_path / "problem.md").write_text("Prove the claim.\n", encoding="utf-8")
    (tmp_path / "solve.toml").write_text(
        """
[solve]
allow_web = true

[resources]
runtime_limit = "3h"
max_model_calls = 17

[forecast]
initial_after = "45m"
interval = "90m"
minimum_interval = "15m"
percentile = 95
breach_confirmations = 2
minimum_confidence = "high"
""".strip()
        + "\n",
        encoding="utf-8",
    )

    spec = SolveSpec.load(tmp_path, headless=True)

    assert spec.problem == tmp_path / "problem.md"
    assert spec.runtime_limit_seconds == 10800
    assert spec.max_model_calls == 17
    assert spec.allow_web
    assert spec.headless
    assert spec.forecast.percentile == 95
    assert spec.forecast.breach_confirmations == 2


def test_solve_spec_requires_a_limit(tmp_path: Path) -> None:
    (tmp_path / "problem.md").write_text("Prove it.\n", encoding="utf-8")

    with pytest.raises(ConfigurationError, match="runtime-limit"):
        SolveSpec.load(tmp_path)


def test_runtime_ledger_excludes_paused_publication_time() -> None:
    started = datetime(2026, 1, 1, tzinfo=UTC)
    ledger = RuntimeLedger(0, None, 0).start(now=started)
    paused = ledger.pause(now=started + timedelta(seconds=10))
    resumed = paused.start(now=started + timedelta(seconds=100))

    assert paused.elapsed(now=started + timedelta(seconds=100)) == 10
    assert resumed.elapsed(now=started + timedelta(seconds=105)) == 15


def test_input_snapshot_is_content_addressed_and_excludes_runtime_state(
    tmp_path: Path,
) -> None:
    (tmp_path / "problem.md").write_text("Problem\n", encoding="utf-8")
    (tmp_path / "notes.txt").write_text("Notes\n", encoding="utf-8")
    (tmp_path / ".alma" / "old").mkdir(parents=True)
    (tmp_path / ".alma" / "old" / "state.json").write_text("{}", encoding="utf-8")
    spec = SolveSpec.load(tmp_path, runtime_limit="1h")

    first = create_input_snapshot(spec)
    second = create_input_snapshot(spec)

    assert first.fingerprint == second.fingerprint
    assert (first.root / "problem.md").read_text(encoding="utf-8") == "Problem\n"
    assert not (first.root / ".alma").exists()
    assert (first.root / "INPUTS.json").is_file()


def test_input_snapshot_rejects_symlinks(tmp_path: Path) -> None:
    (tmp_path / "problem.md").write_text("Problem\n", encoding="utf-8")
    os.symlink(tmp_path / "problem.md", tmp_path / "linked.md")
    spec = SolveSpec.load(tmp_path, runtime_limit="1h")

    with pytest.raises(SolveError, match="symlink"):
        create_input_snapshot(spec)


def test_contract_schemas_reject_unknown_fields() -> None:
    semantic = {
        "schema_version": 1,
        "title": "Claim",
        "question": "Prove True.",
        "definitions": [],
        "domains": [],
        "quantifiers": [],
        "boundary_cases": [],
        "acceptable_outcomes": ["A proof of True."],
        "source_dependent_claims": [],
        "prohibited_scope_changes": [],
        "ambiguities": [],
        "completion_description": "A checked proof of True.",
    }
    assert SemanticContract.parse(semantic).title == "Claim"
    semantic["unexpected"] = True
    with pytest.raises(ConfigurationError, match="extra"):
        SemanticContract.parse(semantic)

    formal = {
        "schema_version": 1,
        "title": "Claim",
        "lakefile": "lakefile.toml",
        "author": "Problem author",
        "audience": "Mathematicians",
        "informal_claim": "True.",
        "closing_scope": "The proposition True.",
        "roots": [
            {
                "module": "Solution.Main",
                "declaration": "target",
                "role": "primary",
                "type": "True",
                "informal_statement": "The proposition True.",
            }
        ],
        "build_command": ["lake", "build"],
        "verification_commands": [["lake", "build"]],
        "allowed_axioms": [],
        "support_files": [],
    }
    assert FormalContract.parse(formal).roots[0].declaration == "target"
