from __future__ import annotations

import json
from pathlib import Path

import pytest

from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.semantic import SemanticReview


def _review(tmp_path: Path, **overrides: object) -> Path:
    value: dict[str, object] = {
        "schema_version": 1,
        "declaration": "Fixture.main_theorem",
        "informal_statement": "Every retained fixture satisfies the theorem.",
        "relation": "equivalent",
        "added_hypotheses": [],
        "omitted_hypotheses": [],
        "quantifier_issues": [],
        "domain_issues": [],
        "boundary_issues": [],
        "symbol_mismatches": [],
        "critical_errors": [],
        "reason": "Quantifiers, hypotheses, domains, symbols, and boundaries match.",
    }
    value.update(overrides)
    path = tmp_path / "semantic.json"
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def test_clean_equivalence_review_is_accepted(tmp_path: Path) -> None:
    review = SemanticReview.load(_review(tmp_path))

    assert review.relation == "equivalent"
    assert review.issues == ()
    assert review.declaration == "Fixture.main_theorem"


def test_equivalence_cannot_hide_added_hypothesis(tmp_path: Path) -> None:
    path = _review(tmp_path, added_hypotheses=["Assumes the result as a premise."])

    with pytest.raises(ConfigurationError, match="cannot report mismatches"):
        SemanticReview.load(path)


def test_non_equivalence_requires_specific_finding(tmp_path: Path) -> None:
    path = _review(tmp_path, relation="conditional_fragment")

    with pytest.raises(ConfigurationError, match="must report a specific issue"):
        SemanticReview.load(path)


def test_conditional_fragment_retains_exact_scope_failure(tmp_path: Path) -> None:
    review = SemanticReview.load(
        _review(
            tmp_path,
            relation="conditional_fragment",
            added_hypotheses=["Adds global regularity not present informally."],
        )
    )

    assert review.relation == "conditional_fragment"
    assert review.issues == ("Adds global regularity not present informally.",)
