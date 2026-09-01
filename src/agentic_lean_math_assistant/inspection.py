"""Read-only inspection of verifier-gated claims in retained campaign bundles."""

from __future__ import annotations

import json
from pathlib import Path, PurePosixPath
from typing import Any

from .artifacts import verify_evidence_index
from .config import ConfigurationError


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


def inspect_claim_ledgers(run_dir: Path, *, verify: bool = True) -> dict[str, object]:
    """Return claim ledgers and target closure from one retained run."""

    run = run_dir.expanduser().resolve()
    if verify:
        verify_evidence_index(run)
    state = _load_object(run / "state.json", "retained campaign state")
    features = _load_object(
        run / "configuration" / "features.json", "retained feature manifest"
    )
    if state.get("schema_version") != 1 or features.get("schema_version") != 1:
        raise ConfigurationError("retained claim inspection schema is unsupported")
    campaign_id = state.get("campaign_id")
    status = state.get("status")
    stages = state.get("stages")
    feature_stages = features.get("stages")
    if (
        not isinstance(campaign_id, str)
        or not campaign_id
        or not isinstance(status, str)
        or not isinstance(stages, dict)
        or not isinstance(feature_stages, dict)
    ):
        raise ConfigurationError("retained claim inspection state is malformed")

    ledgers: list[dict[str, Any]] = []
    for stage_id, feature_id in feature_stages.items():
        if feature_id != "claim_ledger":
            continue
        stage_state = stages.get(stage_id)
        if not isinstance(stage_id, str) or not isinstance(stage_state, dict):
            raise ConfigurationError("claim ledger stage state is malformed")
        artifacts = stage_state.get("artifacts")
        if not isinstance(artifacts, list) or not all(
            isinstance(path, str) for path in artifacts
        ):
            raise ConfigurationError(
                f"claim ledger stage {stage_id!r} artifacts are malformed"
            )
        if stage_state.get("status") not in {"succeeded", "failed"}:
            continue
        ledger_paths = [
            _safe_retained_path(run, path)
            for path in artifacts
            if path.endswith("-claim-ledger.json")
        ]
        if len(ledger_paths) != 1:
            raise ConfigurationError(
                f"claim ledger stage {stage_id!r} must retain exactly one ledger"
            )
        for path in ledger_paths:
            ledger = _load_object(path, f"claim ledger {stage_id!r}")
            _validate_ledger(ledger, campaign_id, stage_id)
            ledger["stage_id"] = stage_id
            ledgers.append(ledger)

    targets = [
        target
        for ledger in ledgers
        for target in ledger["required_targets"]
        if isinstance(target, dict)
    ]
    counts = {
        "required": len(targets),
        "verified": sum(target.get("status") == "verified" for target in targets),
        "rejected": sum(target.get("status") == "rejected" for target in targets),
        "blocked": sum(target.get("status") == "blocked" for target in targets),
    }
    return {
        "schema_version": 1,
        "run_dir": str(run),
        "campaign_id": campaign_id,
        "campaign_status": status,
        "target_summary": counts,
        "ledgers": ledgers,
    }


def inspect_assurance(run_dir: Path) -> dict[str, object]:
    """Report which deterministic trust boundaries a retained run actually passed."""

    run = run_dir.expanduser().resolve()
    artifacts = verify_evidence_index(run)
    state = _load_object(run / "state.json", "retained campaign state")
    features = _load_object(
        run / "configuration" / "features.json", "retained feature manifest"
    )
    stages = state.get("stages")
    feature_stages = features.get("stages")
    campaign_id = state.get("campaign_id")
    campaign_status = state.get("status")
    if (
        not isinstance(stages, dict)
        or not isinstance(feature_stages, dict)
        or not isinstance(campaign_id, str)
        or not isinstance(campaign_status, str)
    ):
        raise ConfigurationError("retained assurance state is malformed")

    claim_report = inspect_claim_ledgers(run, verify=False)
    target_summary = claim_report["target_summary"]
    assert isinstance(target_summary, dict)
    resolved = _load_object(
        run / "configuration" / "resolved.json", "resolved campaign"
    )
    ledgers_value = claim_report.get("ledgers")
    if not isinstance(ledgers_value, list):
        raise ConfigurationError("claim ledger inspection result is malformed")

    def stage_summary(feature_id: str) -> dict[str, int]:
        selected = [
            stage_id
            for stage_id, observed_feature in feature_stages.items()
            if isinstance(stage_id, str) and observed_feature == feature_id
        ]
        return {
            "configured": len(selected),
            "passed": sum(
                isinstance(stages.get(stage_id), dict)
                and stages[stage_id].get("status") == "succeeded"
                for stage_id in selected
            ),
            "failed": sum(
                isinstance(stages.get(stage_id), dict)
                and stages[stage_id].get("status") == "failed"
                for stage_id in selected
            ),
        }

    lean = stage_summary("lean_contract")
    semantic = stage_summary("semantic_contract")
    claims = stage_summary("claim_ledger")
    required = target_summary.get("required")
    verified = target_summary.get("verified")
    claim_closure = isinstance(required, int) and required > 0 and required == verified
    formalization_assured = (
        lean["configured"] > 0
        and lean["configured"] == lean["passed"]
        and semantic["configured"] > 0
        and semantic["configured"] == semantic["passed"]
    )
    assurance_gaps: list[str] = []
    if claims["configured"] == 0:
        assurance_gaps.append(
            "No verifier-gated mathematical claim ledger is configured."
        )
    elif not claim_closure:
        assurance_gaps.append("Not every required mathematical target is verified.")
    if lean["configured"] == 0:
        assurance_gaps.append("No deterministic Lean acceptance gate is configured.")
    elif semantic["configured"] == 0:
        assurance_gaps.append(
            "Lean acceptance is not paired with an informal-to-formal semantic gate."
        )
    if campaign_status != "complete":
        assurance_gaps.append(
            f"Campaign status is {campaign_status!r}, not 'complete'."
        )

    mathematical_limitations = sorted(
        {
            limitation
            for ledger in ledgers_value
            if isinstance(ledger, dict)
            for claim in ledger.get("claims", [])
            if isinstance(claim, dict)
            for limitation in claim.get("limitations", [])
            if isinstance(limitation, str)
        }
    )
    source_limitations = sorted(
        {
            limitation
            for ledger in ledgers_value
            if isinstance(ledger, dict)
            for claim in ledger.get("claims", [])
            if isinstance(claim, dict) and claim.get("kind") == "source"
            for limitation in claim.get("limitations", [])
            if isinstance(limitation, str)
        }
    )
    operational_limitations = (
        []
        if campaign_status == "complete"
        else [f"Campaign execution ended with status {campaign_status!r}."]
    )
    obligations_raw = resolved.get("obligations", [])
    if not isinstance(obligations_raw, list):
        raise ConfigurationError("resolved campaign obligations are malformed")
    obligations: list[dict[str, object]] = []
    for raw in obligations_raw:
        if (
            not isinstance(raw, dict)
            or not isinstance(raw.get("id"), str)
            or not isinstance(raw.get("description"), str)
            or not isinstance(raw.get("evidence_stages"), list)
            or not all(isinstance(item, str) for item in raw["evidence_stages"])
        ):
            raise ConfigurationError("resolved campaign obligation is malformed")
        statuses = [
            stages.get(stage_id, {}).get("status")
            if isinstance(stages.get(stage_id), dict)
            else None
            for stage_id in raw["evidence_stages"]
        ]
        if statuses and all(item == "succeeded" for item in statuses):
            disposition = "verified"
        elif any(item in {"failed", "skipped"} for item in statuses):
            disposition = "rejected"
        else:
            disposition = "blocked"
        obligations.append(
            {
                "id": raw["id"],
                "description": raw["description"],
                "evidence_stages": raw["evidence_stages"],
                "status": disposition,
            }
        )
    obligation_closure = bool(obligations) and all(
        item["status"] in {"verified", "rejected"} for item in obligations
    )
    if obligations and not obligation_closure:
        assurance_gaps.append("Not every verification obligation has a disposition.")

    profiles = ["evidence_bundle"]
    if claim_closure:
        profiles.append("verifier_gated_claims")
    if lean["configured"] > 0 and lean["configured"] == lean["passed"]:
        profiles.append("lean_checked")
    if formalization_assured:
        profiles.append("semantically_audited_formalization")
    return {
        "schema_version": 2,
        "run_dir": str(run),
        "campaign_id": campaign_id,
        "campaign_status": campaign_status,
        "profiles": profiles,
        "evidence_bundle": {
            "verified": True,
            "artifact_count": len(artifacts),
        },
        "claim_ledgers": {
            **claims,
            "target_summary": target_summary,
            "closure_passed": claim_closure,
        },
        "lean_contracts": lean,
        "semantic_contracts": {
            **semantic,
            "formalization_assured": formalization_assured,
        },
        "verification_obligations": {
            "configured": len(obligations),
            "closed": obligation_closure,
            "items": obligations,
        },
        "assurance_gaps": assurance_gaps,
        "mathematical_limitations": mathematical_limitations,
        "source_limitations": source_limitations,
        "operational_limitations": operational_limitations,
        "limitations": sorted(
            set(
                assurance_gaps
                + mathematical_limitations
                + source_limitations
                + operational_limitations
            )
        ),
        "final_report": {
            "execution": campaign_status,
            "evidence_integrity": "verified",
            "formal_verification": (
                "passed"
                if lean["configured"] > 0 and lean["configured"] == lean["passed"]
                else "not_assured"
            ),
            "semantic_assurance": (
                "passed" if formalization_assured else "not_assured"
            ),
            "claim_closure": "passed" if claim_closure else "not_assured",
            "obligation_coverage": ("closed" if obligation_closure else "not_assured"),
            "unresolved_mathematics": mathematical_limitations,
        },
    }


def _safe_retained_path(run: Path, value: str) -> Path:
    if value.startswith("workspace:"):
        raise ConfigurationError("claim ledgers must be retained outside the workspace")
    pure = PurePosixPath(value)
    if pure.is_absolute() or any(part in ("", ".", "..") for part in pure.parts):
        raise ConfigurationError(f"unsafe retained claim ledger path: {value!r}")
    path = run.joinpath(*pure.parts)
    if not path.is_file() or path.is_symlink():
        raise ConfigurationError(f"retained claim ledger is missing: {value}")
    return path


def _validate_ledger(ledger: dict[str, Any], campaign_id: str, stage_id: str) -> None:
    if (
        ledger.get("schema_version") not in {1, 2}
        or ledger.get("campaign_id") != campaign_id
    ):
        raise ConfigurationError(f"claim ledger {stage_id!r} identity is invalid")
    if ledger.get("status") not in {"verified", "incomplete"}:
        raise ConfigurationError(f"claim ledger {stage_id!r} status is invalid")
    targets = ledger.get("required_targets")
    claims = ledger.get("claims")
    if not isinstance(targets, list) or not isinstance(claims, list):
        raise ConfigurationError(f"claim ledger {stage_id!r} contents are malformed")
    for target in targets:
        if (
            not isinstance(target, dict)
            or not isinstance(target.get("target_id"), str)
            or not isinstance(target.get("claim_id"), str)
            or target.get("status") not in {"verified", "rejected", "blocked"}
        ):
            raise ConfigurationError(
                f"claim ledger {stage_id!r} has a malformed target"
            )
