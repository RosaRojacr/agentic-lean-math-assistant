from __future__ import annotations

import pytest

from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.models import (
    CampaignOutcome,
    OrchestrationPlan,
    ResearchDecision,
)


def task(task_id: str, depends_on: list[str]) -> dict[str, object]:
    return {
        "id": task_id,
        "title": task_id.title(),
        "category": "analytic",
        "instructions": "Establish the assigned claim and retain evidence.",
        "phase": "pilot",
        "strategy_id": None,
        "reasoning_class": "analysis",
        "novelty": "Independently establish this exact fixture obligation.",
        "expected_evidence": ["A retained mathematical report."],
        "continuation_gate": False,
        "depends_on": depends_on,
        "tools": ["read"],
        "model": None,
        "timeout": 60,
        "max_attempts": 1,
        "required": True,
        "failure_policy": "abort",
    }


def skipped_capabilities() -> list[dict[str, object]]:
    return [
        {
            "capability": "regression_assess",
            "decision": "skip",
            "task_id": None,
            "rationale": "This fixture has no numeric data.",
        },
        {
            "capability": "regression_fit",
            "decision": "skip",
            "task_id": None,
            "rationale": "This fixture requires an exact derivation.",
        },
    ]


def test_plan_rejects_cycles() -> None:
    value = {
        "schema_version": 3,
        "goal": "Resolve the example.",
        "rationale": "Independent checks converge.",
        "max_parallel": 2,
        "capability_decisions": skipped_capabilities(),
        "strategy_portfolio": [],
        "obligations": [
            {
                "id": "result",
                "statement": "The example result holds.",
                "evidence_tasks": ["first", "second"],
            }
        ],
        "tasks": [task("first", ["second"]), task("second", ["first"])],
    }

    with pytest.raises(ConfigurationError, match="contains a cycle"):
        OrchestrationPlan.parse(value)


def test_research_gate_requires_queries_when_research_is_needed() -> None:
    with pytest.raises(ConfigurationError, match="requires at least one query"):
        ResearchDecision.parse(
            {
                "schema_version": 1,
                "decision": "research",
                "reason": "A source is missing.",
                "existing_coverage": [],
                "required_queries": [],
                "reconsider_if": [],
            }
        )


def test_unsolved_outcome_requires_one_recommended_strategy() -> None:
    with pytest.raises(ConfigurationError, match="exactly one recommended"):
        CampaignOutcome.parse(
            {
                "schema_version": 2,
                "status": "unsolved",
                "summary": "One obligation remains.",
                "evidence": ["state.json"],
                "limitations": ["The final inequality is open."],
                "obligation_dispositions": [
                    {
                        "id": "final_inequality",
                        "status": "unresolved",
                        "reason": "No certified sign proof was produced.",
                        "evidence": [],
                    }
                ],
                "knowledge_promotions": [],
                "strategies": [
                    {
                        "id": "interval-proof",
                        "title": "Interval proof",
                        "rationale": "Certify the compact remainder.",
                        "next_prompt": "Prove the compact remainder by intervals.",
                        "recommended": False,
                    }
                ],
            }
        )


def test_plan_requires_a_pilot_continuation_gate_for_later_work() -> None:
    pilot = task("pilot", [])
    research = task("research", ["pilot"])
    research["phase"] = "research"
    value = {
        "schema_version": 3,
        "goal": "Resolve the example.",
        "rationale": "Pilot before research.",
        "max_parallel": 2,
        "capability_decisions": skipped_capabilities(),
        "strategy_portfolio": [],
        "obligations": [
            {
                "id": "result",
                "statement": "The example result holds.",
                "evidence_tasks": ["research"],
            }
        ],
        "tasks": [pilot, research],
    }

    with pytest.raises(ConfigurationError, match="continuation gate"):
        OrchestrationPlan.parse(value)


def test_outcome_rejects_promotion_without_downstream_audit() -> None:
    source = task("source", [])
    checker = task("checker", ["source"])
    plan = OrchestrationPlan.parse(
        {
            "schema_version": 3,
            "goal": "Resolve the example.",
            "rationale": "Derive and check.",
            "max_parallel": 2,
            "capability_decisions": skipped_capabilities(),
            "strategy_portfolio": [],
            "obligations": [
                {
                    "id": "result",
                    "statement": "The result holds.",
                    "evidence_tasks": ["source", "checker"],
                }
            ],
            "tasks": [source, checker],
        }
    )
    outcome = CampaignOutcome.parse(
        {
            "schema_version": 2,
            "status": "solved",
            "summary": "Solved.",
            "evidence": ["state.json"],
            "limitations": [],
            "obligation_dispositions": [
                {
                    "id": "result",
                    "status": "verified",
                    "reason": "Checked.",
                    "evidence": ["state.json"],
                }
            ],
            "knowledge_promotions": [
                {
                    "task_id": "source",
                    "summary": "Reusable result.",
                    "evidence": ["state.json"],
                    "limitations": [],
                    "verified_by": ["checker"],
                }
            ],
            "strategies": [],
        }
    )

    with pytest.raises(ConfigurationError, match="downstream-verified"):
        outcome.validate_against(plan)
