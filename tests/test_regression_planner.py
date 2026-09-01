from __future__ import annotations

import io
from pathlib import Path

import pytest

import agentic_lean_math_assistant.regime as regime_module
from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.models import OrchestrationPlan
from agentic_lean_math_assistant.project import ProjectSpec
from agentic_lean_math_assistant.regime import RegimeError, RegimeOptions, RegimeRunner


def runner_fixture(tmp_path: Path) -> RegimeRunner:
    (tmp_path / "problem.md").write_text("# Numeric fixture\n", encoding="utf-8")
    (tmp_path / "references").mkdir()
    (tmp_path / "knowledge").mkdir()
    manifest = tmp_path / "project.toml"
    manifest.write_text(
        """schema_version = 1
[project]
id = "regression-policy"
title = "Regression Policy"
problem = "problem.md"
references = "references"
knowledge = "knowledge"
runs = "runs"
[regime]
max_tasks = 6
max_parallel = 3
max_restarts = 1
default_agent_time = 30
pilot_agent_seconds = 1000
research_agent_seconds = 1000
formalization_agent_seconds = 1000
max_attempts_total = 20
allowed_tools = ["read", "bash", "eval"]
""",
        encoding="utf-8",
    )
    runner = RegimeRunner(
        ProjectSpec.load(manifest),
        RegimeOptions(missing_source_policy="checkpoint", output=io.StringIO()),
    )
    runner.pre_workspace = tmp_path / "pre-workspace"
    (runner.pre_workspace / "project-inputs").mkdir(parents=True)
    return runner


def task(
    task_id: str,
    instructions: str = "Read the retained problem.",
    tools: list[str] | None = None,
    depends_on: list[str] | None = None,
) -> dict[str, object]:
    return {
        "id": task_id,
        "title": task_id.title(),
        "category": "numeric",
        "instructions": instructions,
        "phase": "pilot",
        "strategy_id": None,
        "reasoning_class": "execution",
        "novelty": "Exercise one explicit retained capability decision.",
        "expected_evidence": ["A retained capability receipt."],
        "continuation_gate": False,
        "depends_on": depends_on or [],
        "tools": tools or ["read"],
        "model": None,
        "timeout": 30,
        "max_attempts": 1,
        "required": True,
        "failure_policy": "abort",
    }


def plan(
    decisions: list[dict[str, object]],
    tasks: list[dict[str, object]],
) -> OrchestrationPlan:
    return OrchestrationPlan.parse(
        {
            "schema_version": 3,
            "goal": "Resolve the numeric fixture.",
            "rationale": "The plan explicitly disposes every capability.",
            "max_parallel": min(3, len(tasks)),
            "capability_decisions": decisions,
            "strategy_portfolio": [],
            "obligations": [
                {
                    "id": "numeric_result",
                    "statement": "The numeric fixture is resolved.",
                    "evidence_tasks": [str(tasks[-1]["id"])],
                }
            ],
            "tasks": tasks,
        }
    )


def skipped_decisions() -> list[dict[str, object]]:
    return [
        {
            "capability": "regression_assess",
            "decision": "skip",
            "task_id": None,
            "rationale": "No independent numeric observations are available.",
        },
        {
            "capability": "regression_fit",
            "decision": "skip",
            "task_id": None,
            "rationale": "The exact result does not require a surrogate.",
        },
    ]


def use_decision(capability: str, task_id: str) -> dict[str, object]:
    return {
        "capability": capability,
        "decision": "use",
        "task_id": task_id,
        "rationale": "Retained independent numeric observations match this capability.",
    }


def test_plan_schema_requires_unique_explicit_capability_decisions() -> None:
    value = {
        "schema_version": 3,
        "goal": "Resolve the fixture.",
        "rationale": "One task suffices.",
        "max_parallel": 1,
        "strategy_portfolio": [],
        "obligations": [
            {"id": "result", "statement": "Result.", "evidence_tasks": ["work"]}
        ],
        "tasks": [task("work")],
    }
    with pytest.raises(ConfigurationError, match="capability_decisions"):
        OrchestrationPlan.parse(value)

    value["capability_decisions"] = [skipped_decisions()[0]] * 2
    with pytest.raises(ConfigurationError, match="must be unique"):
        OrchestrationPlan.parse(value)


def test_policy_accepts_explicit_skips(tmp_path: Path) -> None:
    runner_fixture(tmp_path)._validate_plan_policy(
        plan(skipped_decisions(), [task("work")])
    )


def test_policy_rejects_unknown_or_missing_catalog_decisions(tmp_path: Path) -> None:
    runner = runner_fixture(tmp_path)
    missing = skipped_decisions()[:1]
    with pytest.raises(RegimeError, match="missing=.*regression_fit"):
        runner._validate_plan_policy(plan(missing, [task("work")]))
    extra: list[dict[str, object]] = [
        *skipped_decisions(),
        {
            "capability": "unregistered_model",
            "decision": "skip",
            "task_id": None,
            "rationale": "The controller did not offer this capability.",
        },
    ]
    with pytest.raises(RegimeError, match="extra=.*unregistered_model"):
        runner._validate_plan_policy(plan(extra, [task("work")]))


def test_policy_rejects_unavailable_capability(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runner = runner_fixture(tmp_path)
    catalog = list(regime_module.regression_capability_catalog(None))
    catalog[0] = {**catalog[0], "available": False}
    monkeypatch.setattr(
        regime_module, "regression_capability_catalog", lambda _root: tuple(catalog)
    )
    decisions = [
        use_decision("regression_assess", "assessment"),
        skipped_decisions()[1],
    ]
    planned = plan(
        decisions,
        [
            task(
                "assessment",
                "Run agentic-lean-math-assistant regression-assess on the arrays.",
                ["bash"],
            )
        ],
    )

    with pytest.raises(RegimeError, match="unavailable capability"):
        runner._validate_plan_policy(planned)


@pytest.mark.parametrize(
    ("instructions", "tools"),
    [
        ("Assess the retained arrays.", ["bash"]),
        ("Run agentic-lean-math-assistant regression-assess on the arrays.", ["read"]),
        ("Call assess_regression on the arrays.", ["read"]),
    ],
)
def test_policy_requires_named_callable_and_execution_tool(
    instructions: str, tools: list[str], tmp_path: Path
) -> None:
    decisions = [
        use_decision("regression_assess", "assessment"),
        skipped_decisions()[1],
    ]
    planned = plan(decisions, [task("assessment", instructions, tools)])

    with pytest.raises(RegimeError, match="must name its CLI or Python API"):
        runner_fixture(tmp_path)._validate_plan_policy(planned)


def test_policy_accepts_python_api_invocation(tmp_path: Path) -> None:
    decisions = [
        use_decision("regression_assess", "assessment"),
        skipped_decisions()[1],
    ]
    planned = plan(
        decisions,
        [task("assessment", "Call assess_regression on the arrays.", ["eval"])],
    )

    runner_fixture(tmp_path)._validate_plan_policy(planned)


def test_fit_requires_used_assessment(tmp_path: Path) -> None:
    decisions = [
        skipped_decisions()[0],
        use_decision("regression_fit", "fit"),
    ]
    planned = plan(
        decisions,
        [
            task(
                "fit",
                "Run agentic-lean-math-assistant regression-fit on the arrays.",
                ["bash"],
            )
        ],
    )

    with pytest.raises(RegimeError, match="requires regression_assess"):
        runner_fixture(tmp_path)._validate_plan_policy(planned)


def test_fit_and_assessment_must_be_separate_tasks(tmp_path: Path) -> None:
    decisions = [
        use_decision("regression_assess", "numeric"),
        use_decision("regression_fit", "numeric"),
    ]
    planned = plan(
        decisions,
        [
            task(
                "numeric",
                "Run agentic-lean-math-assistant regression-assess then agentic-lean-math-assistant "
                "regression-fit on the arrays.",
                ["bash"],
            )
        ],
    )

    with pytest.raises(RegimeError, match="separate task IDs"):
        runner_fixture(tmp_path)._validate_plan_policy(planned)


def test_fit_accepts_transitive_assessment_dependency(tmp_path: Path) -> None:
    decisions = [
        use_decision("regression_assess", "assessment"),
        use_decision("regression_fit", "fit"),
    ]
    planned = plan(
        decisions,
        [
            task(
                "assessment",
                "Run agentic-lean-math-assistant regression-assess on the arrays.",
                ["bash"],
            ),
            task("audit", depends_on=["assessment"]),
            task(
                "fit",
                "Run agentic-lean-math-assistant regression-fit on the arrays.",
                ["bash"],
                ["audit"],
            ),
        ],
    )

    runner_fixture(tmp_path)._validate_plan_policy(planned)
