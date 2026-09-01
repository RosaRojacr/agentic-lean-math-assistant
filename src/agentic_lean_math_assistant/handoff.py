"""Typed, hashable artifacts at campaign trust boundaries."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Self

from .claims import ClaimProposalBundle, ClaimVerdictBundle
from .config import ConfigurationError
from .semantic import SemanticReview

ClaimStatus = Literal["verified", "reproduced", "conjectured", "unresolved"]


def handoff_prompt_contract(schema: str) -> str:
    """Render the exact agent-facing contract for a registered handoff schema."""

    if schema == "research-v1":
        return """`research-v1` requires one JSON object with exactly these fields:
- `schema_version`: integer `1`.
- `goal` and `scope`: nonempty strings, not arrays.
- `sources`: an array of objects with exactly `id`, `locator`, `sha256`, `usage`,
  and `confidence`. `sha256` must be a real lowercase 64-hex digest from the
  frozen source inventory. Never use placeholders or fabricate a digest.
- `claims`: objects with exactly `id`, `statement`, `status`, `sources`, and
  `build_obligation`; status is `verified`, `reproduced`, `conjectured`, or
  `unresolved`.
- `definitions`: objects with exactly `name`, `description`, `domain`, and
  `source_claims`.
- `obligations`: objects with exactly `id`, `statement`, `dependencies`, and
  `acceptance`. Dependencies name claim or obligation IDs.
- `limitations` and `recommended_stages`: arrays containing only nonempty
  strings.
Unretained, inaccessible, or unhashed material is a limitation, not a source
record. Claims about such material must cite the retained report that records
the limitation."""
    if schema == "claim-proposals-v1":
        return """`claim-proposals-v1` requires one JSON object with exactly:
- `schema_version`: integer `1`.
- `claims`: a nonempty array. Each claim has exactly `id`, `kind`, `statement`,
  `scope`, `proof`, `depends_on`, `target`, and `limitations`.
- `id`, every dependency, and a non-null `target` match `[a-z][a-z0-9_-]*`.
- `kind` is `source`, `lemma`, `theorem`, `computation`, `counterexample`, or
  `formalization`.
- `statement`, `scope`, and `proof` are nonempty strings.
- `depends_on` names earlier or later claims in the same acyclic bundle.
- `target` is either null or a unique target ID.
- `limitations` contains only unresolved mathematical, source, domain, or scope
  qualifications inherent in the claim. Do not list pending verifier decisions or
  claim-ledger closure; the controller records those workflow states separately.
Submit exact claims and explicit scope. Do not mark claims verified; only the
controller's claim ledger can promote them after independent verdicts."""
    if schema == "claim-verdicts-v1":
        return """`claim-verdicts-v1` requires one JSON object with exactly:
- `schema_version`: integer `1`.
- `decisions`: one decision for every proposed claim. Each decision has exactly
  `claim`, `decision`, `reason`, `critical_errors`, and `gaps`.
- `decision` is `accept` only when both error arrays are empty; otherwise use
  `reject` and report at least one specific critical error or proof gap.
- `claim` names the proposal ID and `reason` is a nonempty independent judgment.
Judge every claim from the supplied proposal. Never repair or silently strengthen
the submitted statement."""
    if schema == "semantic-review-v1":
        return """`semantic-review-v1` requires one JSON object with exactly:
- `schema_version`: integer `1`.
- `declaration` and `informal_statement`: the exact Lean declaration name and
  informal theorem under review.
- `relation`: `equivalent`, `formal_stronger`, `formal_weaker`,
  `conditional_fragment`, `mismatch`, or `unclear`.
- `added_hypotheses`, `omitted_hypotheses`, `quantifier_issues`,
  `domain_issues`, `boundary_issues`, `symbol_mismatches`, and
  `critical_errors`: arrays of specific nonempty findings.
- `reason`: a concise independent comparison.
Use `equivalent` only when every issue array is empty. Every other relation must
report at least one concrete issue. Check quantifier order, hypotheses, domains,
definitions, branches, degeneracies, and boundary cases; Lean compilation alone
does not establish semantic equivalence."""
    raise ConfigurationError(f"unknown handoff schema: {schema}")


def _object(
    value: object, label: str, required: set[str], optional: set[str] | None = None
) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ConfigurationError(f"{label} must be a JSON object")
    allowed = required | (optional or set())
    missing = required - value.keys()
    unknown = value.keys() - allowed
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
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ConfigurationError(f"{label} must be an array of nonempty strings")
    return tuple(item.strip() for item in value)


def _array(value: object, label: str) -> list[object]:
    if not isinstance(value, list):
        raise ConfigurationError(f"{label} must be an array")
    return value


@dataclass(frozen=True, slots=True)
class SourceRecord:
    source_id: str
    locator: str
    sha256: str
    usage: str
    confidence: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"sources[{index}]"
        item = _object(
            value,
            label,
            {"id", "locator", "sha256", "usage", "confidence"},
        )
        digest = _text(item["sha256"], f"{label}.sha256")
        if len(digest) != 64 or any(
            character not in "0123456789abcdef" for character in digest
        ):
            raise ConfigurationError(f"{label}.sha256 must be a lowercase SHA-256")
        return cls(
            source_id=_text(item["id"], f"{label}.id"),
            locator=_text(item["locator"], f"{label}.locator"),
            sha256=digest,
            usage=_text(item["usage"], f"{label}.usage"),
            confidence=_text(item["confidence"], f"{label}.confidence"),
        )


@dataclass(frozen=True, slots=True)
class ClaimRecord:
    claim_id: str
    statement: str
    status: ClaimStatus
    source_ids: tuple[str, ...]
    build_obligation: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"claims[{index}]"
        item = _object(
            value,
            label,
            {"id", "statement", "status", "sources", "build_obligation"},
        )
        status = _text(item["status"], f"{label}.status")
        if status not in ("verified", "reproduced", "conjectured", "unresolved"):
            raise ConfigurationError(f"{label}.status is invalid")
        return cls(
            claim_id=_text(item["id"], f"{label}.id"),
            statement=_text(item["statement"], f"{label}.statement"),
            status=status,  # type: ignore[arg-type]
            source_ids=_texts(item["sources"], f"{label}.sources"),
            build_obligation=_text(
                item["build_obligation"], f"{label}.build_obligation"
            ),
        )


@dataclass(frozen=True, slots=True)
class DefinitionRecord:
    name: str
    description: str
    domain: str
    source_claims: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"definitions[{index}]"
        item = _object(
            value,
            label,
            {"name", "description", "domain", "source_claims"},
        )
        return cls(
            name=_text(item["name"], f"{label}.name"),
            description=_text(item["description"], f"{label}.description"),
            domain=_text(item["domain"], f"{label}.domain"),
            source_claims=_texts(item["source_claims"], f"{label}.source_claims"),
        )


@dataclass(frozen=True, slots=True)
class ObligationRecord:
    obligation_id: str
    statement: str
    dependencies: tuple[str, ...]
    acceptance: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"obligations[{index}]"
        item = _object(
            value,
            label,
            {"id", "statement", "dependencies", "acceptance"},
        )
        return cls(
            obligation_id=_text(item["id"], f"{label}.id"),
            statement=_text(item["statement"], f"{label}.statement"),
            dependencies=_texts(item["dependencies"], f"{label}.dependencies"),
            acceptance=_text(item["acceptance"], f"{label}.acceptance"),
        )


@dataclass(frozen=True, slots=True)
class ResearchHandoff:
    """Problem-independent research record consumed by build stages."""

    goal: str
    scope: str
    sources: tuple[SourceRecord, ...]
    claims: tuple[ClaimRecord, ...]
    definitions: tuple[DefinitionRecord, ...]
    obligations: tuple[ObligationRecord, ...]
    limitations: tuple[str, ...]
    recommended_stages: tuple[str, ...]

    @classmethod
    def load(cls, path: Path) -> Self:
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except OSError as exc:
            raise ConfigurationError(f"cannot read research handoff: {exc}") from exc
        except json.JSONDecodeError as exc:
            raise ConfigurationError(
                f"research handoff is invalid JSON: {exc}"
            ) from exc
        root = _object(
            value,
            "research handoff",
            {
                "schema_version",
                "goal",
                "scope",
                "sources",
                "claims",
                "definitions",
                "obligations",
                "limitations",
                "recommended_stages",
            },
        )
        if root["schema_version"] != 1:
            raise ConfigurationError("research handoff schema_version must be 1")
        sources = tuple(
            SourceRecord.parse(item, index)
            for index, item in enumerate(_array(root["sources"], "sources"))
        )
        claims = tuple(
            ClaimRecord.parse(item, index)
            for index, item in enumerate(_array(root["claims"], "claims"))
        )
        definitions = tuple(
            DefinitionRecord.parse(item, index)
            for index, item in enumerate(_array(root["definitions"], "definitions"))
        )
        obligations = tuple(
            ObligationRecord.parse(item, index)
            for index, item in enumerate(_array(root["obligations"], "obligations"))
        )
        _validate_references(sources, claims, definitions, obligations)
        if not claims:
            raise ConfigurationError("research handoff must contain at least one claim")
        if not obligations:
            raise ConfigurationError(
                "research handoff must contain at least one build obligation"
            )
        return cls(
            goal=_text(root["goal"], "goal"),
            scope=_text(root["scope"], "scope"),
            sources=sources,
            claims=claims,
            definitions=definitions,
            obligations=obligations,
            limitations=_texts(root["limitations"], "limitations"),
            recommended_stages=_texts(root["recommended_stages"], "recommended_stages"),
        )


def _validate_references(
    sources: tuple[SourceRecord, ...],
    claims: tuple[ClaimRecord, ...],
    definitions: tuple[DefinitionRecord, ...],
    obligations: tuple[ObligationRecord, ...],
) -> None:
    source_ids = {item.source_id for item in sources}
    claim_ids = {item.claim_id for item in claims}
    obligation_ids = {item.obligation_id for item in obligations}
    for label, values in (
        ("source", [item.source_id for item in sources]),
        ("claim", [item.claim_id for item in claims]),
        ("obligation", [item.obligation_id for item in obligations]),
    ):
        if len(set(values)) != len(values):
            raise ConfigurationError(f"research handoff {label} IDs must be unique")
    for claim in claims:
        unknown = set(claim.source_ids) - source_ids
        if unknown:
            raise ConfigurationError(
                f"claim {claim.claim_id!r} cites unknown sources: {sorted(unknown)}"
            )
    for definition in definitions:
        unknown = set(definition.source_claims) - claim_ids
        if unknown:
            raise ConfigurationError(
                f"definition {definition.name!r} cites unknown claims: {sorted(unknown)}"
            )
    known_dependencies = claim_ids | obligation_ids
    for obligation in obligations:
        unknown = set(obligation.dependencies) - known_dependencies
        if unknown:
            raise ConfigurationError(
                f"obligation {obligation.obligation_id!r} has unknown dependencies: "
                f"{sorted(unknown)}"
            )


def digest_handoff(
    path: Path,
    schema: str,
    *,
    source_digests: frozenset[str] | None = None,
) -> str:
    """Validate a registered handoff schema and return its content digest."""

    if schema == "research-v1":
        handoff = ResearchHandoff.load(path)
        if source_digests is not None:
            unknown = sorted(
                {source.sha256 for source in handoff.sources} - source_digests
            )
            if unknown:
                raise ConfigurationError(
                    "research handoff cites SHA-256 digests absent from the frozen "
                    f"source inventory: {unknown}"
                )
    elif schema == "claim-proposals-v1":
        ClaimProposalBundle.load(path)
    elif schema == "claim-verdicts-v1":
        ClaimVerdictBundle.load(path)
    elif schema == "semantic-review-v1":
        SemanticReview.load(path)
    else:
        raise ConfigurationError(f"unknown handoff schema: {schema}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


@dataclass(frozen=True, slots=True)
class ReviewDecision:
    decision: Literal["accept", "revise"]
    reason: str
    target_stages: tuple[str, ...]
    required_changes: tuple[str, ...]

    @classmethod
    def parse(cls, text: str) -> Self:
        try:
            value = json.loads(text)
        except json.JSONDecodeError as exc:
            raise ConfigurationError(f"review output is invalid JSON: {exc}") from exc
        item = _object(
            value,
            "review decision",
            {"decision", "reason", "target_stages", "required_changes"},
        )
        decision = _text(item["decision"], "review decision.decision")
        if decision not in ("accept", "revise"):
            raise ConfigurationError("review decision must be accept or revise")
        targets = _texts(item["target_stages"], "review decision.target_stages")
        changes = _texts(item["required_changes"], "review decision.required_changes")
        if decision == "accept" and (targets or changes):
            raise ConfigurationError(
                "accepted review decisions cannot contain targets or changes"
            )
        if decision == "revise" and (not targets or not changes):
            raise ConfigurationError(
                "revision decisions require target stages and changes"
            )
        return cls(
            decision=decision,  # type: ignore[arg-type]
            reason=_text(item["reason"], "review decision.reason"),
            target_stages=targets,
            required_changes=changes,
        )
