"""Strict semantic-equivalence reviews for informal-to-Lean formalizations."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Self

from .config import ConfigurationError

SemanticRelation = Literal[
    "equivalent",
    "formal_stronger",
    "formal_weaker",
    "conditional_fragment",
    "mismatch",
    "unclear",
]


def _object(value: object, label: str, required: set[str]) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ConfigurationError(f"{label} must be a JSON object")
    missing = required - value.keys()
    unknown = value.keys() - required
    if missing:
        raise ConfigurationError(f"{label} is missing keys: {sorted(missing)}")
    if unknown:
        raise ConfigurationError(f"{label} has unknown keys: {sorted(unknown)}")
    return value


def _text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be a nonempty string")
    return value.strip()


def _texts(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise ConfigurationError(f"{label} must be an array")
    return tuple(_text(item, f"{label}[{index}]") for index, item in enumerate(value))


@dataclass(frozen=True, slots=True)
class SemanticReview:
    """An independent comparison of an informal theorem and its Lean declaration."""

    declaration: str
    informal_statement: str
    relation: SemanticRelation
    added_hypotheses: tuple[str, ...]
    omitted_hypotheses: tuple[str, ...]
    quantifier_issues: tuple[str, ...]
    domain_issues: tuple[str, ...]
    boundary_issues: tuple[str, ...]
    symbol_mismatches: tuple[str, ...]
    critical_errors: tuple[str, ...]
    reason: str

    @classmethod
    def load(cls, path: Path) -> Self:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except OSError as exc:
            raise ConfigurationError(
                f"cannot read semantic review handoff: {exc}"
            ) from exc
        except json.JSONDecodeError as exc:
            raise ConfigurationError(
                f"semantic review handoff is invalid JSON: {exc}"
            ) from exc
        root = _object(
            value,
            "semantic review handoff",
            {
                "schema_version",
                "declaration",
                "informal_statement",
                "relation",
                "added_hypotheses",
                "omitted_hypotheses",
                "quantifier_issues",
                "domain_issues",
                "boundary_issues",
                "symbol_mismatches",
                "critical_errors",
                "reason",
            },
        )
        if type(root["schema_version"]) is not int or root["schema_version"] != 1:
            raise ConfigurationError("semantic review schema_version must be 1")
        relation = _text(root["relation"], "semantic review.relation")
        if relation not in (
            "equivalent",
            "formal_stronger",
            "formal_weaker",
            "conditional_fragment",
            "mismatch",
            "unclear",
        ):
            raise ConfigurationError("semantic review.relation is invalid")
        review = cls(
            declaration=_text(root["declaration"], "semantic review.declaration"),
            informal_statement=_text(
                root["informal_statement"], "semantic review.informal_statement"
            ),
            relation=relation,  # type: ignore[arg-type]
            added_hypotheses=_texts(
                root["added_hypotheses"], "semantic review.added_hypotheses"
            ),
            omitted_hypotheses=_texts(
                root["omitted_hypotheses"], "semantic review.omitted_hypotheses"
            ),
            quantifier_issues=_texts(
                root["quantifier_issues"], "semantic review.quantifier_issues"
            ),
            domain_issues=_texts(
                root["domain_issues"], "semantic review.domain_issues"
            ),
            boundary_issues=_texts(
                root["boundary_issues"], "semantic review.boundary_issues"
            ),
            symbol_mismatches=_texts(
                root["symbol_mismatches"], "semantic review.symbol_mismatches"
            ),
            critical_errors=_texts(
                root["critical_errors"], "semantic review.critical_errors"
            ),
            reason=_text(root["reason"], "semantic review.reason"),
        )
        if review.relation == "equivalent" and review.issues:
            raise ConfigurationError(
                "an equivalent semantic review cannot report mismatches or errors"
            )
        if review.relation != "equivalent" and not review.issues:
            raise ConfigurationError(
                "a non-equivalent semantic review must report a specific issue"
            )
        return review

    @property
    def issues(self) -> tuple[str, ...]:
        return (
            *self.added_hypotheses,
            *self.omitted_hypotheses,
            *self.quantifier_issues,
            *self.domain_issues,
            *self.boundary_issues,
            *self.symbol_mismatches,
            *self.critical_errors,
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "declaration": self.declaration,
            "informal_statement": self.informal_statement,
            "relation": self.relation,
            "added_hypotheses": list(self.added_hypotheses),
            "omitted_hypotheses": list(self.omitted_hypotheses),
            "quantifier_issues": list(self.quantifier_issues),
            "domain_issues": list(self.domain_issues),
            "boundary_issues": list(self.boundary_issues),
            "symbol_mismatches": list(self.symbol_mismatches),
            "critical_errors": list(self.critical_errors),
            "reason": self.reason,
        }
