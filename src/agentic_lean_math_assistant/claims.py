"""Content-addressed mathematical claims and verifier-gated target closure."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Self

from .config import ConfigurationError

ClaimKind = Literal[
    "source",
    "lemma",
    "theorem",
    "computation",
    "counterexample",
    "formalization",
]
VerdictDecision = Literal["accept", "reject"]
ClaimStatus = Literal["verified", "rejected", "blocked"]

_ID = re.compile(r"[a-z][a-z0-9_-]*")


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


def _identifier(value: object, label: str) -> str:
    result = _text(value, label)
    if _ID.fullmatch(result) is None:
        raise ConfigurationError(f"{label} must match [a-z][a-z0-9_-]*")
    return result


def _texts(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise ConfigurationError(f"{label} must be an array")
    return tuple(_text(item, f"{label}[{index}]") for index, item in enumerate(value))


def _identifiers(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise ConfigurationError(f"{label} must be an array")
    return tuple(
        _identifier(item, f"{label}[{index}]") for index, item in enumerate(value)
    )


def _load_object(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ConfigurationError(f"cannot read {label}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ConfigurationError(f"{label} is invalid JSON: {exc}") from exc
    if not isinstance(value, dict):
        raise ConfigurationError(f"{label} must be a JSON object")
    return value


@dataclass(frozen=True, slots=True)
class ClaimProposal:
    """One exact claim submitted for independent verification."""

    alias: str
    kind: ClaimKind
    statement: str
    scope: str
    proof: str
    depends_on: tuple[str, ...]
    target: str | None
    limitations: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"claims[{index}]"
        item = _object(
            value,
            label,
            {
                "id",
                "kind",
                "statement",
                "scope",
                "proof",
                "depends_on",
                "target",
                "limitations",
            },
        )
        kind = _text(item["kind"], f"{label}.kind")
        if kind not in (
            "source",
            "lemma",
            "theorem",
            "computation",
            "counterexample",
            "formalization",
        ):
            raise ConfigurationError(f"{label}.kind is invalid")
        target_value = item["target"]
        target = (
            None
            if target_value is None
            else _identifier(target_value, f"{label}.target")
        )
        dependencies = _identifiers(item["depends_on"], f"{label}.depends_on")
        if len(set(dependencies)) != len(dependencies):
            raise ConfigurationError(f"{label}.depends_on must not contain duplicates")
        return cls(
            alias=_identifier(item["id"], f"{label}.id"),
            kind=kind,  # type: ignore[arg-type]
            statement=_text(item["statement"], f"{label}.statement"),
            scope=_text(item["scope"], f"{label}.scope"),
            proof=_text(item["proof"], f"{label}.proof"),
            depends_on=dependencies,
            target=target,
            limitations=_texts(item["limitations"], f"{label}.limitations"),
        )


@dataclass(frozen=True, slots=True)
class ClaimProposalBundle:
    """A finite acyclic set of candidate mathematical claims."""

    claims: tuple[ClaimProposal, ...]

    @classmethod
    def load(cls, path: Path) -> Self:
        root = _object(
            _load_object(path, "claim proposal handoff"),
            "claim proposal handoff",
            {"schema_version", "claims"},
        )
        if type(root["schema_version"]) is not int or root["schema_version"] != 1:
            raise ConfigurationError("claim proposal schema_version must be 1")
        values = root["claims"]
        if not isinstance(values, list) or not values:
            raise ConfigurationError(
                "claim proposal handoff requires a nonempty claims array"
            )
        claims = tuple(
            ClaimProposal.parse(value, index) for index, value in enumerate(values)
        )
        _validate_claim_graph(claims)
        return cls(claims=claims)

    @property
    def by_alias(self) -> dict[str, ClaimProposal]:
        return {claim.alias: claim for claim in self.claims}

    @property
    def topological_order(self) -> tuple[str, ...]:
        return _topological_order(self.claims)


@dataclass(frozen=True, slots=True)
class ClaimVerdict:
    """One cold verifier's decision about a candidate claim."""

    claim: str
    decision: VerdictDecision
    reason: str
    critical_errors: tuple[str, ...]
    gaps: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"decisions[{index}]"
        item = _object(
            value,
            label,
            {"claim", "decision", "reason", "critical_errors", "gaps"},
        )
        decision = _text(item["decision"], f"{label}.decision")
        if decision not in ("accept", "reject"):
            raise ConfigurationError(f"{label}.decision must be accept or reject")
        critical_errors = _texts(item["critical_errors"], f"{label}.critical_errors")
        gaps = _texts(item["gaps"], f"{label}.gaps")
        if decision == "accept" and (critical_errors or gaps):
            raise ConfigurationError(
                f"{label} cannot accept a claim while reporting errors or gaps"
            )
        if decision == "reject" and not (critical_errors or gaps):
            raise ConfigurationError(
                f"{label} must report at least one critical error or gap when rejecting"
            )
        return cls(
            claim=_identifier(item["claim"], f"{label}.claim"),
            decision=decision,  # type: ignore[arg-type]
            reason=_text(item["reason"], f"{label}.reason"),
            critical_errors=critical_errors,
            gaps=gaps,
        )


@dataclass(frozen=True, slots=True)
class ClaimVerdictBundle:
    """All decisions produced by one independently scheduled verifier stage."""

    decisions: tuple[ClaimVerdict, ...]

    @classmethod
    def load(cls, path: Path) -> Self:
        root = _object(
            _load_object(path, "claim verdict handoff"),
            "claim verdict handoff",
            {"schema_version", "decisions"},
        )
        if type(root["schema_version"]) is not int or root["schema_version"] != 1:
            raise ConfigurationError("claim verdict schema_version must be 1")
        values = root["decisions"]
        if not isinstance(values, list) or not values:
            raise ConfigurationError(
                "claim verdict handoff requires a nonempty decisions array"
            )
        decisions = tuple(
            ClaimVerdict.parse(value, index) for index, value in enumerate(values)
        )
        aliases = [decision.claim for decision in decisions]
        if len(set(aliases)) != len(aliases):
            raise ConfigurationError(
                "claim verdict decisions must name each claim once"
            )
        return cls(decisions=decisions)

    @property
    def by_claim(self) -> dict[str, ClaimVerdict]:
        return {decision.claim: decision for decision in self.decisions}


def _validate_claim_graph(claims: tuple[ClaimProposal, ...]) -> None:
    aliases = [claim.alias for claim in claims]
    if len(set(aliases)) != len(aliases):
        raise ConfigurationError("claim proposal IDs must be unique")
    known = set(aliases)
    targets = [claim.target for claim in claims if claim.target is not None]
    if len(set(targets)) != len(targets):
        raise ConfigurationError("each target may be assigned to only one claim")
    for claim in claims:
        unknown = set(claim.depends_on) - known
        if unknown:
            raise ConfigurationError(
                f"claim {claim.alias!r} has unknown dependencies: {sorted(unknown)}"
            )
        if claim.alias in claim.depends_on:
            raise ConfigurationError(f"claim {claim.alias!r} cannot depend on itself")
    _topological_order(claims)


def _topological_order(claims: tuple[ClaimProposal, ...]) -> tuple[str, ...]:
    dependencies = {claim.alias: set(claim.depends_on) for claim in claims}
    resolved: set[str] = set()
    order: list[str] = []
    while len(resolved) < len(dependencies):
        ready = sorted(
            alias
            for alias, required in dependencies.items()
            if alias not in resolved and required <= resolved
        )
        if not ready:
            blocked = sorted(set(dependencies) - resolved)
            raise ConfigurationError(
                f"claim proposal graph contains a cycle: {blocked}"
            )
        order.extend(ready)
        resolved.update(ready)
    return tuple(order)


def _claim_digest(
    campaign_id: str,
    claim: ClaimProposal,
    predecessor_ids: tuple[str, ...],
) -> str:
    canonical = {
        "campaign_id": campaign_id,
        "kind": claim.kind,
        "statement": claim.statement,
        "scope": claim.scope,
        "proof": claim.proof,
        "predecessors": sorted(predecessor_ids),
        "target": claim.target,
        "limitations": list(claim.limitations),
    }
    encoded = json.dumps(
        canonical, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _evidence_reference(
    stage: str, reference: dict[str, object] | dict[str, str]
) -> dict[str, object]:
    return {"stage": stage, **reference}


def _receipt_covers(reference: dict[str, object], target: str | None) -> bool:
    covered = reference.get("covers_targets")
    return target is None or (isinstance(covered, list) and target in covered)


def build_claim_ledger(
    *,
    campaign_id: str,
    proposals: ClaimProposalBundle,
    verdicts: dict[str, ClaimVerdictBundle],
    required_targets: tuple[str, ...],
    evidence: dict[str, dict[str, str]],
    declared_targets: dict[str, dict[str, str]] | None = None,
    receipt_evidence: dict[str, dict[str, object]] | None = None,
    adjudicator: ClaimVerdictBundle | None = None,
) -> tuple[dict[str, object], bool]:
    """Build an immutable ledger from frozen targets, receipts, and verdicts."""

    if not verdicts:
        raise ConfigurationError("claim ledger requires at least one verifier")
    if not required_targets:
        raise ConfigurationError("claim ledger requires at least one target")
    if len(set(required_targets)) != len(required_targets):
        raise ConfigurationError("claim ledger required_targets must be unique")

    proposal_aliases = set(proposals.by_alias)
    for verifier, bundle in verdicts.items():
        decision_aliases = set(bundle.by_claim)
        missing = proposal_aliases - decision_aliases
        unknown = decision_aliases - proposal_aliases
        if missing or unknown:
            raise ConfigurationError(
                f"verifier {verifier!r} decisions do not match proposals; "
                f"missing={sorted(missing)}, unknown={sorted(unknown)}"
            )
    if adjudicator is not None:
        decision_aliases = set(adjudicator.by_claim)
        if decision_aliases != proposal_aliases:
            raise ConfigurationError(
                "adjudicator decisions do not exactly match claim proposals"
            )

    claim_by_target = {
        claim.target: claim.alias
        for claim in proposals.claims
        if claim.target is not None
    }
    unknown_targets = set(required_targets) - claim_by_target.keys()
    if unknown_targets:
        raise ConfigurationError(
            f"required targets have no proposed claim: {sorted(unknown_targets)}"
        )
    declared_targets = declared_targets or {}
    for target, alias in claim_by_target.items():
        declared = declared_targets.get(target)
        if declared is None:
            continue
        claim = proposals.by_alias[alias]
        observed = {
            "kind": claim.kind,
            "statement": claim.statement,
            "scope": claim.scope,
        }
        if observed != declared:
            raise ConfigurationError(
                f"claim for target {target!r} does not exactly match its frozen "
                "kind, statement, and scope"
            )

    by_alias = proposals.by_alias
    content_ids: dict[str, str] = {}
    statuses: dict[str, ClaimStatus] = {}
    records: list[dict[str, object]] = []
    verdict_maps = {verifier: bundle.by_claim for verifier, bundle in verdicts.items()}
    adjudicator_map = adjudicator.by_claim if adjudicator is not None else {}
    disagreements: list[dict[str, object]] = []
    for alias in proposals.topological_order:
        claim = by_alias[alias]
        predecessor_ids = tuple(content_ids[item] for item in claim.depends_on)
        claim_id = _claim_digest(campaign_id, claim, predecessor_ids)
        content_ids[alias] = claim_id
        decisions = {
            verifier: verdict_map[alias]
            for verifier, verdict_map in verdict_maps.items()
        }
        votes = {decision.decision for decision in decisions.values()}
        adjudication = adjudicator_map.get(alias) if len(votes) > 1 else None
        if adjudication is not None:
            disagreements.append(
                {
                    "claim": alias,
                    "verifier_decisions": {
                        verifier: decision.decision
                        for verifier, decision in sorted(decisions.items())
                    },
                    "adjudicator_decision": adjudication.decision,
                    "reason": adjudication.reason,
                }
            )
            rejected = adjudication.decision == "reject"
        else:
            rejected = any(
                decision.decision == "reject" for decision in decisions.values()
            )
        if rejected:
            status: ClaimStatus = "rejected"
        elif any(statuses[dependency] != "verified" for dependency in claim.depends_on):
            status = "blocked"
        else:
            status = "verified"
        statuses[alias] = status
        records.append(
            {
                "alias": alias,
                "claim_id": claim_id,
                "kind": claim.kind,
                "statement": claim.statement,
                "scope": claim.scope,
                "proof": claim.proof,
                "predecessors": [content_ids[item] for item in claim.depends_on],
                "target": claim.target,
                "limitations": list(claim.limitations),
                "status": status,
                "verdicts": [
                    {
                        "verifier_stage": verifier,
                        "decision": decision.decision,
                        "reason": decision.reason,
                        "critical_errors": list(decision.critical_errors),
                        "gaps": list(decision.gaps),
                    }
                    for verifier, decision in sorted(decisions.items())
                ],
                "adjudication": (
                    {
                        "decision": adjudication.decision,
                        "reason": adjudication.reason,
                        "critical_errors": list(adjudication.critical_errors),
                        "gaps": list(adjudication.gaps),
                    }
                    if adjudication is not None
                    else None
                ),
                "evidence_refs": [
                    _evidence_reference(stage, reference)
                    for stage, reference in sorted(evidence.items())
                ]
                + [
                    _evidence_reference(stage, reference)
                    for stage, reference in sorted((receipt_evidence or {}).items())
                    if _receipt_covers(reference, claim.target)
                ],
            }
        )

    targets = [
        {
            "target_id": target,
            "claim_id": content_ids[claim_by_target[target]],
            "status": statuses[claim_by_target[target]],
        }
        for target in required_targets
    ]
    closed = all(target["status"] == "verified" for target in targets)
    ledger: dict[str, object] = {
        "schema_version": 2,
        "campaign_id": campaign_id,
        "status": "verified" if closed else "incomplete",
        "required_targets": targets,
        "claims": records,
        "evidence": evidence,
        "deterministic_receipts": receipt_evidence or {},
        "verifier_disagreements": disagreements,
    }
    return ledger, closed
