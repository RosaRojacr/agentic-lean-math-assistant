#!/usr/bin/env python3
"""Deterministic OMP process double for end-to-end campaign tests."""

from __future__ import annotations

import json
import os
import re
import sys
from pathlib import Path


def assignment(prompt: str) -> dict[str, object]:
    blocks = re.findall(r"```json\n(.*?)\n```", prompt, flags=re.DOTALL)
    return json.loads(blocks[-1]) if blocks else {}


def main() -> int:
    prompt_argument = next(
        (argument for argument in reversed(sys.argv[1:]) if argument.startswith("@")),
        None,
    )
    if prompt_argument is None:
        print("missing prompt", file=sys.stderr)
        return 2
    prompt = Path(prompt_argument[1:]).read_text(encoding="utf-8")
    if "Regime role: `research_gate`" in prompt:
        values = assignment(prompt)
        if (
            "Trigger research gate execution failure"
            in Path(str(values["problem"])).read_text(encoding="utf-8")
            and "Controller gate failure" not in prompt
        ):
            print("simulated research gate transport failure", file=sys.stderr)
            return 1
        references = Path(str(values["references"]))
        research = (
            os.environ.get("FAKE_REGIME_RESEARCH") == "1"
            or (references / ".request-missing-source").is_file()
            or (references / ".attempt-protected-mutation").is_file()
        )
        print(
            json.dumps(
                {
                    "schema_version": 1,
                    "decision": "research" if research else "skip",
                    "reason": (
                        "The fixture requests one unavailable publication."
                        if research
                        else "The fixture has complete retained source coverage."
                    ),
                    "existing_coverage": ["fixture reference"],
                    "required_queries": ["missing fixture paper"] if research else [],
                    "reconsider_if": ["the problem statement changes"],
                }
            )
        )
        return 0
    if "Regime role: `publication_research`" in prompt:
        values = assignment(prompt)
        existing_references = Path(str(values["existing_references"]))
        if (existing_references / ".attempt-protected-mutation").is_file():
            try:
                Path(str(values["problem"])).write_text(
                    "malicious replacement\n", encoding="utf-8"
                )
            except OSError:
                pass
            else:
                return 9
            added = Path(str(values["references"])) / "added.pdf"
            added.write_bytes(b"retained publication")
            print(
                json.dumps(
                    {
                        "schema_version": 1,
                        "status": "complete",
                        "summary": "Added one isolated fixture publication.",
                        "sources_added": ["added.pdf"],
                        "missing_sources": [],
                        "limitations": [],
                    }
                )
            )
            return 0
        if (existing_references / "missing.pdf").is_file():
            print(
                json.dumps(
                    {
                        "schema_version": 1,
                        "status": "complete",
                        "summary": "Observed the manually supplied fixture publication.",
                        "sources_added": [],
                        "missing_sources": [],
                        "limitations": [],
                    }
                )
            )
            return 0
        print(
            json.dumps(
                {
                    "schema_version": 1,
                    "status": "limited",
                    "summary": "A critical fixture paper requires manual acquisition.",
                    "sources_added": [],
                    "missing_sources": [
                        {
                            "title": "Missing fixture paper",
                            "reason": "No open copy was available.",
                            "importance": "critical",
                            "request": "Add missing.pdf to references.",
                        }
                    ],
                    "limitations": ["The primary statement could not be checked."],
                }
            )
        )
        return 0
    if "Regime role: `orchestration_planning`" in prompt:
        values = assignment(prompt)
        invalid_plan = (
            "Trigger invalid orchestration plan"
            in Path(str(values["problem"])).read_text(encoding="utf-8")
            and "Controller plan failure" not in prompt
        )
        strategy_id = None if invalid_plan else "direct"
        print(
            json.dumps(
                {
                    "schema_version": 3,
                    "goal": "Produce one independently inspectable analysis.",
                    "rationale": "One derivation and one downstream audit suffice.",
                    "max_parallel": 2,
                    "capability_decisions": [
                        {
                            "capability": "regression_assess",
                            "decision": "skip",
                            "task_id": None,
                            "rationale": "The fixture has no numeric observations.",
                        },
                        {
                            "capability": "regression_fit",
                            "decision": "skip",
                            "task_id": None,
                            "rationale": "The fixture requests a direct exact implication.",
                        },
                    ],
                    "strategy_portfolio": [
                        {
                            "id": "direct",
                            "title": "Direct implication",
                            "method": "Read and apply the retained premise directly.",
                            "falsification_test": "The source premise does not imply the result.",
                        }
                    ],
                    "obligations": [
                        {
                            "id": "fixture_result",
                            "statement": "The retained premise implies the fixture result.",
                            "evidence_tasks": ["analyst", "auditor"],
                        }
                    ],
                    "tasks": [
                        {
                            "id": "analyst",
                            "title": "Independent analysis",
                            "category": "analytic",
                            "instructions": "Read problem.md and report the fixture result.",
                            "phase": "pilot",
                            "strategy_id": strategy_id,
                            "reasoning_class": "analysis",
                            "novelty": "Establish the fixture result from the retained premise.",
                            "expected_evidence": ["A retained derivation report."],
                            "continuation_gate": False,
                            "depends_on": [],
                            "tools": ["read"],
                            "model": None,
                            "timeout": 30,
                            "max_attempts": 1,
                            "required": True,
                            "failure_policy": "abort",
                        },
                        {
                            "id": "auditor",
                            "title": "Independent audit",
                            "category": "review",
                            "instructions": "Independently audit the analyst report.",
                            "phase": "pilot",
                            "strategy_id": strategy_id,
                            "reasoning_class": "audit",
                            "novelty": "Falsify rather than repeat the direct derivation.",
                            "expected_evidence": ["An independent audit report."],
                            "continuation_gate": False,
                            "depends_on": ["analyst"],
                            "tools": ["read"],
                            "model": None,
                            "timeout": 30,
                            "max_attempts": 1,
                            "required": True,
                            "failure_policy": "abort",
                        },
                    ],
                }
            )
        )
        return 0
    if "Regime role: `main_assessment`" in prompt:
        values = assignment(prompt)
        report = Path(str(values["report_path"]))
        outcome = Path(str(values["outcome_path"]))
        fail_once = (
            "Trigger assessment execution failure"
            in Path(str(values["original_problem"])).read_text(encoding="utf-8")
            and "Controller assessment failure" not in prompt
        )
        if fail_once:
            print("simulated assessment transport failure", file=sys.stderr)
            return 1
        invalid_once = (
            "Trigger invalid assessment"
            in Path(str(values["original_problem"])).read_text(encoding="utf-8")
            and "Controller assessment failure" not in prompt
        )
        promotion_task = "historical_analyst" if invalid_once else "analyst"
        report.write_text(
            "# Final assessment\n\nThe fixture problem is solved by retained evidence.\n",
            encoding="utf-8",
        )
        outcome.write_text(
            json.dumps(
                {
                    "schema_version": 2,
                    "status": "solved",
                    "summary": "The fixture contract is satisfied.",
                    "evidence": ["agents/analytic/analyst/attempt-01.md"],
                    "limitations": [],
                    "obligation_dispositions": [
                        {
                            "id": "fixture_result",
                            "status": "verified",
                            "reason": "The audit independently confirms the direct implication.",
                            "evidence": ["agents/review/auditor/attempt-01.md"],
                        }
                    ],
                    "knowledge_promotions": [
                        {
                            "task_id": promotion_task,
                            "summary": "The retained premise implies the fixture result.",
                            "evidence": ["agents/analytic/analyst/attempt-01.md"],
                            "limitations": ["Applies only to the retained fixture."],
                            "verified_by": ["auditor"],
                        }
                    ],
                    "strategies": [],
                }
            ),
            encoding="utf-8",
        )
        print("assessment complete")
        return 0
    handoff_match = re.search(r"Write `([^`]+)` as strict JSON", prompt)
    if handoff_match and "`claim-proposals-v1` requires" in prompt:
        handoff = Path(handoff_match.group(1))
        handoff.parent.mkdir(parents=True, exist_ok=True)
        handoff.write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "claims": [
                        {
                            "id": "fixture_claim",
                            "kind": "theorem",
                            "statement": "The fixture theorem holds.",
                            "scope": "For the retained fixture.",
                            "proof": "The retained premise directly establishes it.",
                            "depends_on": [],
                            "target": "fixture_goal",
                            "limitations": [],
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        print("# Claim proposal\n\nSubmitted the exact fixture claim.")
        return 0
    if handoff_match and "`claim-verdicts-v1` requires" in prompt:
        handoff = Path(handoff_match.group(1))
        handoff.parent.mkdir(parents=True, exist_ok=True)
        handoff.write_text(
            json.dumps(
                {
                    "schema_version": 1,
                    "decisions": [
                        {
                            "claim": "fixture_claim",
                            "decision": "accept",
                            "reason": "The retained premise exactly matches the claim.",
                            "critical_errors": [],
                            "gaps": [],
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        print("# Cold verification\n\nAccepted after an independent check.")
        return 0
    print("# Independent analysis\n\nThe fixture result follows from its premise.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
