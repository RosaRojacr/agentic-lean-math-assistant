from __future__ import annotations

import json
from pathlib import Path

import pytest

from agentic_lean_math_assistant.claims import (
    ClaimProposalBundle,
    ClaimVerdictBundle,
    build_claim_ledger,
)
from agentic_lean_math_assistant.config import ConfigurationError


def _write(path: Path, value: object) -> Path:
    path.write_text(json.dumps(value), encoding="utf-8")
    return path


def _proposals(tmp_path: Path, *, proof: str = "By the preceding identity.") -> Path:
    return _write(
        tmp_path / "proposals.json",
        {
            "schema_version": 1,
            "claims": [
                {
                    "id": "base_identity",
                    "kind": "lemma",
                    "statement": "The base identity holds.",
                    "scope": "For every admissible fixture value.",
                    "proof": proof,
                    "depends_on": [],
                    "target": None,
                    "limitations": [],
                },
                {
                    "id": "main_theorem",
                    "kind": "theorem",
                    "statement": "The fixture theorem holds.",
                    "scope": "For every admissible fixture value.",
                    "proof": "Apply the base identity.",
                    "depends_on": ["base_identity"],
                    "target": "fixture_goal",
                    "limitations": [],
                },
            ],
        },
    )


def _verdicts(
    tmp_path: Path,
    *,
    name: str = "verdicts.json",
    reject: str | None = None,
) -> Path:
    decisions = []
    for claim in ("base_identity", "main_theorem"):
        rejected = claim == reject
        decisions.append(
            {
                "claim": claim,
                "decision": "reject" if rejected else "accept",
                "reason": "A dependency is unjustified." if rejected else "Checked.",
                "critical_errors": ["Invalid inference."] if rejected else [],
                "gaps": [],
            }
        )
    return _write(
        tmp_path / name,
        {"schema_version": 1, "decisions": decisions},
    )


def _ledger(
    tmp_path: Path,
    *,
    reject: str | None = None,
    proof: str = "By the preceding identity.",
) -> tuple[dict[str, object], bool]:
    proposals = ClaimProposalBundle.load(_proposals(tmp_path, proof=proof))
    verdicts = ClaimVerdictBundle.load(_verdicts(tmp_path, reject=reject))
    return build_claim_ledger(
        campaign_id="fixture",
        proposals=proposals,
        verdicts={"cold_verifier": verdicts},
        required_targets=("fixture_goal",),
        evidence={
            "proposer": {"path": "proposals.json", "sha256": "a" * 64},
            "cold_verifier": {"path": "verdicts.json", "sha256": "b" * 64},
        },
    )


def test_all_cold_verdicts_close_target_with_content_addressed_claims(
    tmp_path: Path,
) -> None:
    ledger, closed = _ledger(tmp_path)

    assert closed is True
    assert ledger["status"] == "verified"
    targets = ledger["required_targets"]
    assert isinstance(targets, list)
    assert targets == [
        {
            "target_id": "fixture_goal",
            "claim_id": targets[0]["claim_id"],
            "status": "verified",
        }
    ]
    claims = ledger["claims"]
    assert isinstance(claims, list)
    assert [claim["status"] for claim in claims] == ["verified", "verified"]
    assert claims[1]["predecessors"] == [claims[0]["claim_id"]]
    assert len(claims[0]["claim_id"]) == 64


def test_rejected_predecessor_blocks_dependent_target(tmp_path: Path) -> None:
    ledger, closed = _ledger(tmp_path, reject="base_identity")

    assert closed is False
    claims = ledger["claims"]
    assert isinstance(claims, list)
    assert [claim["status"] for claim in claims] == ["rejected", "blocked"]
    assert ledger["required_targets"] == [
        {
            "target_id": "fixture_goal",
            "claim_id": claims[1]["claim_id"],
            "status": "blocked",
        }
    ]


def test_one_rejecting_verifier_prevents_target_closure(tmp_path: Path) -> None:
    proposals = ClaimProposalBundle.load(_proposals(tmp_path))
    accepting = ClaimVerdictBundle.load(_verdicts(tmp_path, name="accepting.json"))
    rejecting = ClaimVerdictBundle.load(
        _verdicts(tmp_path, name="rejecting.json", reject="main_theorem")
    )

    ledger, closed = build_claim_ledger(
        campaign_id="fixture",
        proposals=proposals,
        verdicts={"accepting_verifier": accepting, "rejecting_verifier": rejecting},
        required_targets=("fixture_goal",),
        evidence={},
    )

    assert closed is False
    targets = ledger["required_targets"]
    assert isinstance(targets, list)
    assert targets[0]["status"] == "rejected"


def test_claim_content_address_changes_when_proof_changes(tmp_path: Path) -> None:
    first, _ = _ledger(tmp_path, proof="First proof.")
    second, _ = _ledger(tmp_path, proof="Materially different proof.")

    first_claims = first["claims"]
    second_claims = second["claims"]
    assert isinstance(first_claims, list) and isinstance(second_claims, list)
    assert first_claims[0]["claim_id"] != second_claims[0]["claim_id"]
    assert first_claims[1]["claim_id"] != second_claims[1]["claim_id"]


def test_verifier_must_decide_every_proposed_claim(tmp_path: Path) -> None:
    proposals = ClaimProposalBundle.load(_proposals(tmp_path))
    verdict_path = _verdicts(tmp_path)
    value = json.loads(verdict_path.read_text(encoding="utf-8"))
    value["decisions"].pop()
    _write(verdict_path, value)
    verdicts = ClaimVerdictBundle.load(verdict_path)

    with pytest.raises(ConfigurationError, match="decisions do not match proposals"):
        build_claim_ledger(
            campaign_id="fixture",
            proposals=proposals,
            verdicts={"cold_verifier": verdicts},
            required_targets=("fixture_goal",),
            evidence={},
        )


def test_claim_dependency_cycles_are_rejected(tmp_path: Path) -> None:
    path = _proposals(tmp_path)
    value = json.loads(path.read_text(encoding="utf-8"))
    value["claims"][0]["depends_on"] = ["main_theorem"]
    _write(path, value)

    with pytest.raises(ConfigurationError, match="contains a cycle"):
        ClaimProposalBundle.load(path)


@pytest.mark.parametrize(
    ("corruption", "message"),
    [
        ("boolean_schema", "schema_version must be 1"),
        ("unknown_field", "unknown keys"),
        ("invalid_id", "must match"),
        ("duplicate_id", "IDs must be unique"),
        ("duplicate_target", "only one claim"),
        ("unknown_dependency", "unknown dependencies"),
        ("duplicate_dependency", "must not contain duplicates"),
        ("blank_proof", "must be a nonempty string"),
    ],
)
def test_proposal_contract_rejects_malformed_boundaries(
    tmp_path: Path, corruption: str, message: str
) -> None:
    path = _proposals(tmp_path)
    value = json.loads(path.read_text(encoding="utf-8"))
    claims = value["claims"]
    if corruption == "boolean_schema":
        value["schema_version"] = True
    elif corruption == "unknown_field":
        value["unexpected"] = "not allowed"
    elif corruption == "invalid_id":
        claims[0]["id"] = "../escape"
    elif corruption == "duplicate_id":
        claims[1]["id"] = claims[0]["id"]
    elif corruption == "duplicate_target":
        claims[0]["target"] = claims[1]["target"]
    elif corruption == "unknown_dependency":
        claims[1]["depends_on"] = ["missing_lemma"]
    elif corruption == "duplicate_dependency":
        claims[1]["depends_on"] = ["base_identity", "base_identity"]
    elif corruption == "blank_proof":
        claims[0]["proof"] = " "
    else:
        raise AssertionError(f"unknown test corruption: {corruption}")
    _write(path, value)

    with pytest.raises(ConfigurationError, match=message):
        ClaimProposalBundle.load(path)


@pytest.mark.parametrize(
    ("corruption", "message"),
    [
        ("boolean_schema", "schema_version must be 1"),
        ("unknown_field", "unknown keys"),
        ("duplicate_decision", "name each claim once"),
        ("accept_with_gap", "cannot accept"),
        ("reject_without_finding", "must report at least one"),
        ("invalid_decision", "must be accept or reject"),
    ],
)
def test_verdict_contract_rejects_malformed_boundaries(
    tmp_path: Path, corruption: str, message: str
) -> None:
    path = _verdicts(tmp_path)
    value = json.loads(path.read_text(encoding="utf-8"))
    decisions = value["decisions"]
    if corruption == "boolean_schema":
        value["schema_version"] = True
    elif corruption == "unknown_field":
        decisions[0]["unexpected"] = "not allowed"
    elif corruption == "duplicate_decision":
        decisions[1]["claim"] = decisions[0]["claim"]
    elif corruption == "accept_with_gap":
        decisions[0]["gaps"] = ["Unchecked boundary."]
    elif corruption == "reject_without_finding":
        decisions[0]["decision"] = "reject"
    elif corruption == "invalid_decision":
        decisions[0]["decision"] = "maybe"
    else:
        raise AssertionError(f"unknown test corruption: {corruption}")
    _write(path, value)

    with pytest.raises(ConfigurationError, match=message):
        ClaimVerdictBundle.load(path)


def test_frozen_target_rejects_statement_or_scope_substitution(tmp_path: Path) -> None:
    proposals = ClaimProposalBundle.load(_proposals(tmp_path))
    verdicts = ClaimVerdictBundle.load(_verdicts(tmp_path))

    with pytest.raises(ConfigurationError, match="does not exactly match"):
        build_claim_ledger(
            campaign_id="fixture",
            proposals=proposals,
            verdicts={"cold_verifier": verdicts},
            required_targets=("fixture_goal",),
            evidence={},
            declared_targets={
                "fixture_goal": {
                    "kind": "theorem",
                    "statement": "A weaker substituted statement.",
                    "scope": "For every admissible fixture value.",
                }
            },
        )


def test_claim_records_retain_structured_gate_receipts(tmp_path: Path) -> None:
    proposals = ClaimProposalBundle.load(_proposals(tmp_path))
    verdicts = ClaimVerdictBundle.load(_verdicts(tmp_path))
    ledger, closed = build_claim_ledger(
        campaign_id="fixture",
        proposals=proposals,
        verdicts={"cold_verifier": verdicts},
        required_targets=("fixture_goal",),
        evidence={"cold_verifier": {"path": "verdicts.json", "sha256": "b" * 64}},
        receipt_evidence={
            "numerical_gate": {
                "path": "gate.json",
                "sha256": "c" * 64,
                "covers_targets": ["fixture_goal"],
            }
        },
    )

    assert closed is True
    claims = ledger["claims"]
    assert isinstance(claims, list)
    assert claims[1]["evidence_refs"] == [
        {
            "stage": "cold_verifier",
            "path": "verdicts.json",
            "sha256": "b" * 64,
        },
        {
            "stage": "numerical_gate",
            "path": "gate.json",
            "sha256": "c" * 64,
            "covers_targets": ["fixture_goal"],
        },
    ]


def test_adjudicator_resolves_explicit_verifier_disagreement(tmp_path: Path) -> None:
    proposals = ClaimProposalBundle.load(_proposals(tmp_path))
    accepting = ClaimVerdictBundle.load(_verdicts(tmp_path, name="accepting.json"))
    rejecting = ClaimVerdictBundle.load(
        _verdicts(tmp_path, name="rejecting.json", reject="main_theorem")
    )
    adjudicator = ClaimVerdictBundle.load(_verdicts(tmp_path, name="adjudication.json"))

    ledger, closed = build_claim_ledger(
        campaign_id="fixture",
        proposals=proposals,
        verdicts={"accepting": accepting, "rejecting": rejecting},
        required_targets=("fixture_goal",),
        evidence={},
        adjudicator=adjudicator,
    )

    assert closed is True
    disagreements = ledger["verifier_disagreements"]
    assert isinstance(disagreements, list)
    assert disagreements[0]["claim"] == "main_theorem"
    assert disagreements[0]["adjudicator_decision"] == "accept"
