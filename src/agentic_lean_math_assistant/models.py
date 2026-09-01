"""Strict model-produced contracts for the deterministic campaign regime."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal, Self

from .config import ConfigurationError

_ID = re.compile(r"[a-z][a-z0-9_-]*")
FailurePolicy = Literal["continue", "abort", "replan", "restart"]
TaskPhase = Literal["pilot", "research", "formalization"]
ReasoningClass = Literal["execution", "analysis", "invention", "audit"]


def _object(
    value: object, label: str, required: set[str], optional: set[str] | None = None
) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise ConfigurationError(f"{label} must be an object")
    allowed = required | (optional or set())
    missing = required - value.keys()
    extra = value.keys() - allowed
    if missing or extra:
        raise ConfigurationError(
            f"{label} keys differ; missing={sorted(missing)}, extra={sorted(extra)}"
        )
    return value


def _text(value: object, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigurationError(f"{label} must be a nonempty string")
    return value.strip()


def _identifier(value: object, label: str) -> str:
    result = _text(value, label)
    if _ID.fullmatch(result) is None:
        raise ConfigurationError(f"{label} must match {_ID.pattern!r}")
    return result


def _texts(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list):
        raise ConfigurationError(f"{label} must be an array")
    return tuple(_text(item, f"{label}[{index}]") for index, item in enumerate(value))


def _integer(value: object, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ConfigurationError(f"{label} must be an integer")
    if not minimum <= value <= maximum:
        raise ConfigurationError(f"{label} must be between {minimum} and {maximum}")
    return value


def _boolean(value: object, label: str) -> bool:
    if not isinstance(value, bool):
        raise ConfigurationError(f"{label} must be a boolean")
    return value


def load_json_object(path: Path, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise ConfigurationError(f"cannot read {label}: {exc}") from exc
    except json.JSONDecodeError as exc:
        raise ConfigurationError(f"{label} is invalid JSON: {exc}") from exc
    return _object(value, label, set(value) if isinstance(value, dict) else set())


@dataclass(frozen=True, slots=True)
class ResearchDecision:
    decision: Literal["research", "skip"]
    reason: str
    existing_coverage: tuple[str, ...]
    required_queries: tuple[str, ...]
    reconsider_if: tuple[str, ...]

    @classmethod
    def parse(cls, value: object) -> Self:
        root = _object(
            value,
            "research decision",
            {
                "schema_version",
                "decision",
                "reason",
                "existing_coverage",
                "required_queries",
                "reconsider_if",
            },
        )
        if root["schema_version"] != 1:
            raise ConfigurationError("research decision schema_version must be 1")
        decision = root["decision"]
        if decision not in ("research", "skip"):
            raise ConfigurationError("research decision must be 'research' or 'skip'")
        queries = _texts(root["required_queries"], "required_queries")
        if decision == "research" and not queries:
            raise ConfigurationError("research decision requires at least one query")
        return cls(
            decision=decision,
            reason=_text(root["reason"], "reason"),
            existing_coverage=_texts(root["existing_coverage"], "existing_coverage"),
            required_queries=queries,
            reconsider_if=_texts(root["reconsider_if"], "reconsider_if"),
        )


@dataclass(frozen=True, slots=True)
class MissingSource:
    title: str
    reason: str
    importance: Literal["critical", "optional"]
    request: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        root = _object(
            value,
            f"missing_sources[{index}]",
            {"title", "reason", "importance", "request"},
        )
        importance = root["importance"]
        if importance not in ("critical", "optional"):
            raise ConfigurationError(
                f"missing_sources[{index}].importance must be critical or optional"
            )
        return cls(
            title=_text(root["title"], f"missing_sources[{index}].title"),
            reason=_text(root["reason"], f"missing_sources[{index}].reason"),
            importance=importance,
            request=_text(root["request"], f"missing_sources[{index}].request"),
        )


@dataclass(frozen=True, slots=True)
class ResearchResult:
    status: Literal["complete", "limited"]
    summary: str
    sources_added: tuple[str, ...]
    missing_sources: tuple[MissingSource, ...]
    limitations: tuple[str, ...]

    @classmethod
    def parse(cls, value: object) -> Self:
        root = _object(
            value,
            "research result",
            {
                "schema_version",
                "status",
                "summary",
                "sources_added",
                "missing_sources",
                "limitations",
            },
        )
        if root["schema_version"] != 1:
            raise ConfigurationError("research result schema_version must be 1")
        status = root["status"]
        if status not in ("complete", "limited"):
            raise ConfigurationError(
                "research result status must be complete or limited"
            )
        missing = root["missing_sources"]
        if not isinstance(missing, list):
            raise ConfigurationError("missing_sources must be an array")
        parsed_missing = tuple(
            MissingSource.parse(item, index) for index, item in enumerate(missing)
        )
        if status == "complete" and parsed_missing:
            raise ConfigurationError("complete research cannot contain missing sources")
        return cls(
            status=status,
            summary=_text(root["summary"], "summary"),
            sources_added=_texts(root["sources_added"], "sources_added"),
            missing_sources=parsed_missing,
            limitations=_texts(root["limitations"], "limitations"),
        )


@dataclass(frozen=True, slots=True)
class PlanStrategy:
    strategy_id: str
    title: str
    method: str
    falsification_test: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"strategy_portfolio[{index}]"
        root = _object(
            value,
            label,
            {"id", "title", "method", "falsification_test"},
        )
        return cls(
            strategy_id=_identifier(root["id"], f"{label}.id"),
            title=_text(root["title"], f"{label}.title"),
            method=_text(root["method"], f"{label}.method"),
            falsification_test=_text(
                root["falsification_test"], f"{label}.falsification_test"
            ),
        )


@dataclass(frozen=True, slots=True)
class PlanObligation:
    obligation_id: str
    statement: str
    evidence_tasks: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"obligations[{index}]"
        root = _object(value, label, {"id", "statement", "evidence_tasks"})
        evidence_tasks = _texts(root["evidence_tasks"], f"{label}.evidence_tasks")
        if not evidence_tasks:
            raise ConfigurationError(f"{label}.evidence_tasks must not be empty")
        return cls(
            obligation_id=_identifier(root["id"], f"{label}.id"),
            statement=_text(root["statement"], f"{label}.statement"),
            evidence_tasks=evidence_tasks,
        )


@dataclass(frozen=True, slots=True)
class PlanTask:
    task_id: str
    title: str
    category: str
    instructions: str
    phase: TaskPhase
    strategy_id: str | None
    reasoning_class: ReasoningClass
    novelty: str
    expected_evidence: tuple[str, ...]
    continuation_gate: bool
    depends_on: tuple[str, ...]
    tools: tuple[str, ...]
    model: str | None
    timeout: int
    max_attempts: int
    required: bool
    failure_policy: FailurePolicy

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"tasks[{index}]"
        root = _object(
            value,
            label,
            {
                "id",
                "title",
                "category",
                "instructions",
                "phase",
                "strategy_id",
                "reasoning_class",
                "novelty",
                "expected_evidence",
                "continuation_gate",
                "depends_on",
                "tools",
                "model",
                "timeout",
                "max_attempts",
                "required",
                "failure_policy",
            },
        )
        model = root["model"]
        if model is not None:
            model = _text(model, f"{label}.model")
        strategy_id = root["strategy_id"]
        if strategy_id is not None:
            strategy_id = _identifier(strategy_id, f"{label}.strategy_id")
        phase = root["phase"]
        if phase not in ("pilot", "research", "formalization"):
            raise ConfigurationError(f"{label}.phase is invalid")
        reasoning_class = root["reasoning_class"]
        if reasoning_class not in ("execution", "analysis", "invention", "audit"):
            raise ConfigurationError(f"{label}.reasoning_class is invalid")
        policy = root["failure_policy"]
        if policy not in ("continue", "abort", "replan", "restart"):
            raise ConfigurationError(f"{label}.failure_policy is invalid")
        required = _boolean(root["required"], f"{label}.required")
        if policy == "continue" and required:
            raise ConfigurationError(f"{label} continue policy requires required=false")
        if policy != "continue" and not required:
            raise ConfigurationError(f"{label} {policy} policy requires required=true")
        expected_evidence = _texts(
            root["expected_evidence"], f"{label}.expected_evidence"
        )
        if not expected_evidence:
            raise ConfigurationError(f"{label}.expected_evidence must not be empty")
        continuation_gate = _boolean(
            root["continuation_gate"], f"{label}.continuation_gate"
        )
        if continuation_gate and (
            reasoning_class != "audit"
            or phase != "pilot"
            or required
            or policy != "continue"
        ):
            raise ConfigurationError(
                f"{label} continuation gate must be an optional pilot audit "
                "with continue failure policy"
            )
        return cls(
            task_id=_identifier(root["id"], f"{label}.id"),
            title=_text(root["title"], f"{label}.title"),
            category=_identifier(root["category"], f"{label}.category"),
            instructions=_text(root["instructions"], f"{label}.instructions"),
            phase=phase,
            strategy_id=strategy_id,
            reasoning_class=reasoning_class,
            novelty=_text(root["novelty"], f"{label}.novelty"),
            expected_evidence=expected_evidence,
            continuation_gate=continuation_gate,
            depends_on=_texts(root["depends_on"], f"{label}.depends_on"),
            tools=_texts(root["tools"], f"{label}.tools"),
            model=model,
            timeout=_integer(root["timeout"], f"{label}.timeout", 30, 86400),
            max_attempts=_integer(root["max_attempts"], f"{label}.max_attempts", 1, 5),
            required=required,
            failure_policy=policy,
        )


@dataclass(frozen=True, slots=True)
class CapabilityDecision:
    capability_id: str
    decision: Literal["use", "skip"]
    task_id: str | None
    rationale: str

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"capability_decisions[{index}]"
        root = _object(
            value,
            label,
            {"capability", "decision", "task_id", "rationale"},
        )
        capability_id = _identifier(root["capability"], f"{label}.capability")
        decision = root["decision"]
        if decision not in ("use", "skip"):
            raise ConfigurationError(f"{label}.decision must be use or skip")
        task_id = root["task_id"]
        if task_id is not None:
            task_id = _identifier(task_id, f"{label}.task_id")
        if decision == "use" and task_id is None:
            raise ConfigurationError(
                f"{label}.task_id is required when decision is use"
            )
        if decision == "skip" and task_id is not None:
            raise ConfigurationError(
                f"{label}.task_id must be null when decision is skip"
            )
        return cls(
            capability_id=capability_id,
            decision=decision,
            task_id=task_id,
            rationale=_text(root["rationale"], f"{label}.rationale"),
        )


@dataclass(frozen=True, slots=True)
class OrchestrationPlan:
    goal: str
    rationale: str
    max_parallel: int
    capability_decisions: tuple[CapabilityDecision, ...]
    strategy_portfolio: tuple[PlanStrategy, ...]
    obligations: tuple[PlanObligation, ...]
    tasks: tuple[PlanTask, ...]

    @classmethod
    def parse(
        cls, value: object, *, max_tasks: int = 16, max_parallel: int = 8
    ) -> Self:
        root = _object(
            value,
            "orchestration plan",
            {
                "schema_version",
                "goal",
                "rationale",
                "max_parallel",
                "capability_decisions",
                "strategy_portfolio",
                "obligations",
                "tasks",
            },
        )
        if root["schema_version"] != 3:
            raise ConfigurationError("orchestration plan schema_version must be 3")
        strategy_values = root["strategy_portfolio"]
        if not isinstance(strategy_values, list):
            raise ConfigurationError("strategy_portfolio must be an array")
        strategies = tuple(
            PlanStrategy.parse(item, index)
            for index, item in enumerate(strategy_values)
        )
        strategy_ids = [strategy.strategy_id for strategy in strategies]
        if len(strategy_ids) != len(set(strategy_ids)):
            raise ConfigurationError("strategy portfolio IDs must be unique")
        raw_decisions = root["capability_decisions"]
        if not isinstance(raw_decisions, list) or not raw_decisions:
            raise ConfigurationError("capability_decisions must be a nonempty array")
        capability_decisions = tuple(
            CapabilityDecision.parse(item, index)
            for index, item in enumerate(raw_decisions)
        )
        capability_ids = [item.capability_id for item in capability_decisions]
        if len(capability_ids) != len(set(capability_ids)):
            raise ConfigurationError("capability decision IDs must be unique")
        obligation_values = root["obligations"]
        if not isinstance(obligation_values, list) or not obligation_values:
            raise ConfigurationError("orchestration plan obligations must be nonempty")
        obligations = tuple(
            PlanObligation.parse(item, index)
            for index, item in enumerate(obligation_values)
        )
        obligation_ids = [item.obligation_id for item in obligations]
        if len(obligation_ids) != len(set(obligation_ids)):
            raise ConfigurationError("orchestration plan obligation IDs must be unique")
        task_values = root["tasks"]
        if not isinstance(task_values, list) or not task_values:
            raise ConfigurationError(
                "orchestration plan tasks must be a nonempty array"
            )
        if len(task_values) > max_tasks:
            raise ConfigurationError(
                f"orchestration plan exceeds the project limit of {max_tasks} tasks"
            )
        tasks = tuple(
            PlanTask.parse(item, index) for index, item in enumerate(task_values)
        )
        _validate_task_dag(tasks)
        task_ids = {task.task_id for task in tasks}
        unknown_capability_tasks = {
            item.task_id
            for item in capability_decisions
            if item.task_id is not None and item.task_id not in task_ids
        }
        if unknown_capability_tasks:
            raise ConfigurationError(
                "capability decisions use unknown task IDs: "
                f"{sorted(unknown_capability_tasks)}"
            )
        _validate_plan_contract(strategies, obligations, tasks)
        return cls(
            goal=_text(root["goal"], "goal"),
            rationale=_text(root["rationale"], "rationale"),
            max_parallel=_integer(
                root["max_parallel"], "max_parallel", 1, min(max_parallel, len(tasks))
            ),
            strategy_portfolio=strategies,
            obligations=obligations,
            capability_decisions=capability_decisions,
            tasks=tasks,
        )

    @property
    def by_id(self) -> dict[str, PlanTask]:
        return {task.task_id: task for task in self.tasks}

    @property
    def capabilities_by_id(self) -> dict[str, CapabilityDecision]:
        return {item.capability_id: item for item in self.capability_decisions}


def _validate_task_dag(tasks: tuple[PlanTask, ...]) -> None:
    ids = [task.task_id for task in tasks]
    if len(set(ids)) != len(ids):
        raise ConfigurationError("orchestration plan task IDs must be unique")
    known = set(ids)
    for task in tasks:
        unknown = set(task.depends_on) - known
        if unknown:
            raise ConfigurationError(
                f"task {task.task_id!r} has unknown dependencies: {sorted(unknown)}"
            )
        if task.task_id in task.depends_on:
            raise ConfigurationError(f"task {task.task_id!r} depends on itself")
    resolved: set[str] = set()
    while len(resolved) < len(tasks):
        ready = {
            task.task_id
            for task in tasks
            if task.task_id not in resolved and set(task.depends_on) <= resolved
        }
        if not ready:
            raise ConfigurationError("orchestration plan task graph contains a cycle")
        resolved.update(ready)


def _validate_plan_contract(
    strategies: tuple[PlanStrategy, ...],
    obligations: tuple[PlanObligation, ...],
    tasks: tuple[PlanTask, ...],
) -> None:
    task_ids = {task.task_id for task in tasks}
    strategy_ids = {strategy.strategy_id for strategy in strategies}
    unknown_strategies = {
        task.strategy_id
        for task in tasks
        if task.strategy_id is not None and task.strategy_id not in strategy_ids
    }
    if unknown_strategies:
        raise ConfigurationError(
            f"tasks use unknown strategy IDs: {sorted(unknown_strategies)}"
        )
    unused_strategies = strategy_ids - {
        task.strategy_id for task in tasks if task.strategy_id is not None
    }
    if unused_strategies:
        raise ConfigurationError(
            f"strategy portfolio entries have no tasks: {sorted(unused_strategies)}"
        )
    for obligation in obligations:
        unknown = set(obligation.evidence_tasks) - task_ids
        if unknown:
            raise ConfigurationError(
                f"obligation {obligation.obligation_id!r} has unknown evidence tasks: "
                f"{sorted(unknown)}"
            )
    rank = {"pilot": 0, "research": 1, "formalization": 2}
    by_id = {task.task_id: task for task in tasks}
    for task in tasks:
        backward = {
            dependency
            for dependency in task.depends_on
            if rank[by_id[dependency].phase] > rank[task.phase]
        }
        if backward:
            raise ConfigurationError(
                f"task {task.task_id!r} depends on a later phase: {sorted(backward)}"
            )
    gates = {task.task_id for task in tasks if task.continuation_gate}
    if any(task.phase != "pilot" for task in tasks) and not gates:
        raise ConfigurationError(
            "research or formalization tasks require a pilot continuation gate"
        )
    ancestors: dict[str, set[str]] = {}
    for task in tasks:
        seen = set(task.depends_on)
        pending = list(task.depends_on)
        while pending:
            dependency = pending.pop()
            for ancestor in by_id[dependency].depends_on:
                if ancestor not in seen:
                    seen.add(ancestor)
                    pending.append(ancestor)
        ancestors[task.task_id] = seen
    unguarded = [
        task.task_id
        for task in tasks
        if task.phase != "pilot" and not (ancestors[task.task_id] & gates)
    ]
    if unguarded:
        raise ConfigurationError(
            f"later-phase tasks do not descend from a pilot continuation gate: "
            f"{sorted(unguarded)}"
        )


@dataclass(frozen=True, slots=True)
class ContinuationDecision:
    decision: Literal["continue", "stop"]
    reason: str
    evidence: tuple[str, ...]

    @classmethod
    def parse_text(cls, text: str) -> Self:
        try:
            value = json.loads(text)
        except json.JSONDecodeError as exc:
            raise ConfigurationError(
                f"continuation gate returned invalid JSON: {exc}"
            ) from exc
        root = _object(
            value,
            "continuation decision",
            {"schema_version", "decision", "reason", "evidence"},
        )
        if root["schema_version"] != 1:
            raise ConfigurationError("continuation decision schema_version must be 1")
        decision = root["decision"]
        if decision not in ("continue", "stop"):
            raise ConfigurationError("continuation decision is invalid")
        evidence = _texts(root["evidence"], "continuation decision evidence")
        if decision == "continue" and not evidence:
            raise ConfigurationError(
                "a continue decision requires at least one retained evidence path"
            )
        return cls(
            decision=decision,
            reason=_text(root["reason"], "continuation decision reason"),
            evidence=evidence,
        )


@dataclass(frozen=True, slots=True)
class Strategy:
    strategy_id: str
    title: str
    rationale: str
    next_prompt: str
    recommended: bool

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"strategies[{index}]"
        root = _object(
            value,
            label,
            {"id", "title", "rationale", "next_prompt", "recommended"},
        )
        return cls(
            strategy_id=_identifier(root["id"], f"{label}.id"),
            title=_text(root["title"], f"{label}.title"),
            rationale=_text(root["rationale"], f"{label}.rationale"),
            next_prompt=_text(root["next_prompt"], f"{label}.next_prompt"),
            recommended=_boolean(root["recommended"], f"{label}.recommended"),
        )


@dataclass(frozen=True, slots=True)
class ObligationDisposition:
    obligation_id: str
    status: Literal["verified", "rejected", "unresolved"]
    reason: str
    evidence: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"obligation_dispositions[{index}]"
        root = _object(value, label, {"id", "status", "reason", "evidence"})
        status = root["status"]
        if status not in ("verified", "rejected", "unresolved"):
            raise ConfigurationError(f"{label}.status is invalid")
        evidence = _texts(root["evidence"], f"{label}.evidence")
        if status != "unresolved" and not evidence:
            raise ConfigurationError(
                f"{label} requires evidence when status is {status}"
            )
        return cls(
            obligation_id=_identifier(root["id"], f"{label}.id"),
            status=status,
            reason=_text(root["reason"], f"{label}.reason"),
            evidence=evidence,
        )


@dataclass(frozen=True, slots=True)
class KnowledgePromotion:
    task_id: str
    summary: str
    evidence: tuple[str, ...]
    limitations: tuple[str, ...]
    verified_by: tuple[str, ...]

    @classmethod
    def parse(cls, value: object, index: int) -> Self:
        label = f"knowledge_promotions[{index}]"
        root = _object(
            value,
            label,
            {"task_id", "summary", "evidence", "limitations", "verified_by"},
        )
        evidence = _texts(root["evidence"], f"{label}.evidence")
        verified_by = _texts(root["verified_by"], f"{label}.verified_by")
        if not evidence:
            raise ConfigurationError(f"{label}.evidence must not be empty")
        if not verified_by:
            raise ConfigurationError(f"{label}.verified_by must not be empty")
        return cls(
            task_id=_identifier(root["task_id"], f"{label}.task_id"),
            summary=_text(root["summary"], f"{label}.summary"),
            evidence=evidence,
            limitations=_texts(root["limitations"], f"{label}.limitations"),
            verified_by=verified_by,
        )


@dataclass(frozen=True, slots=True)
class CampaignOutcome:
    status: Literal["solved", "unsolved", "blocked"]
    summary: str
    evidence: tuple[str, ...]
    limitations: tuple[str, ...]
    obligation_dispositions: tuple[ObligationDisposition, ...]
    knowledge_promotions: tuple[KnowledgePromotion, ...]
    strategies: tuple[Strategy, ...]

    @classmethod
    def parse(cls, value: object) -> Self:
        root = _object(
            value,
            "campaign outcome",
            {
                "schema_version",
                "status",
                "summary",
                "evidence",
                "limitations",
                "obligation_dispositions",
                "knowledge_promotions",
                "strategies",
            },
        )
        if root["schema_version"] != 2:
            raise ConfigurationError("campaign outcome schema_version must be 2")
        status = root["status"]
        if status not in ("solved", "unsolved", "blocked"):
            raise ConfigurationError("campaign outcome status is invalid")
        raw_dispositions = root["obligation_dispositions"]
        if not isinstance(raw_dispositions, list):
            raise ConfigurationError("obligation_dispositions must be an array")
        dispositions = tuple(
            ObligationDisposition.parse(item, index)
            for index, item in enumerate(raw_dispositions)
        )
        disposition_ids = [item.obligation_id for item in dispositions]
        if len(disposition_ids) != len(set(disposition_ids)):
            raise ConfigurationError("obligation disposition IDs must be unique")
        raw_promotions = root["knowledge_promotions"]
        if not isinstance(raw_promotions, list):
            raise ConfigurationError("knowledge_promotions must be an array")
        promotions = tuple(
            KnowledgePromotion.parse(item, index)
            for index, item in enumerate(raw_promotions)
        )
        promotion_ids = [item.task_id for item in promotions]
        if len(promotion_ids) != len(set(promotion_ids)):
            raise ConfigurationError("knowledge promotion task IDs must be unique")
        raw_strategies = root["strategies"]
        if not isinstance(raw_strategies, list):
            raise ConfigurationError("campaign outcome strategies must be an array")
        strategies = tuple(
            Strategy.parse(item, index) for index, item in enumerate(raw_strategies)
        )
        ids = [item.strategy_id for item in strategies]
        if len(ids) != len(set(ids)):
            raise ConfigurationError("campaign outcome strategy IDs must be unique")
        recommended = sum(item.recommended for item in strategies)
        if status == "solved" and strategies:
            raise ConfigurationError("a solved outcome cannot propose strategies")
        if status == "solved" and any(
            item.status == "unresolved" for item in dispositions
        ):
            raise ConfigurationError(
                "a solved outcome cannot retain unresolved obligations"
            )
        if status != "solved" and (not strategies or recommended != 1):
            raise ConfigurationError(
                "an unsolved or blocked outcome requires exactly one recommended strategy"
            )
        return cls(
            status=status,
            summary=_text(root["summary"], "summary"),
            evidence=_texts(root["evidence"], "evidence"),
            limitations=_texts(root["limitations"], "limitations"),
            obligation_dispositions=dispositions,
            knowledge_promotions=promotions,
            strategies=strategies,
        )

    def validate_against(self, plan: OrchestrationPlan) -> None:
        expected = {item.obligation_id for item in plan.obligations}
        observed = {item.obligation_id for item in self.obligation_dispositions}
        if observed != expected:
            raise ConfigurationError(
                "outcome obligation dispositions differ from the frozen plan; "
                f"missing={sorted(expected - observed)}, "
                f"extra={sorted(observed - expected)}"
            )
        task_by_id = plan.by_id
        ancestors: dict[str, set[str]] = {}
        for task in plan.tasks:
            seen = set(task.depends_on)
            pending = list(task.depends_on)
            while pending:
                dependency = pending.pop()
                for ancestor in task_by_id[dependency].depends_on:
                    if ancestor not in seen:
                        seen.add(ancestor)
                        pending.append(ancestor)
            ancestors[task.task_id] = seen
        for promotion in self.knowledge_promotions:
            if promotion.task_id not in task_by_id:
                raise ConfigurationError(
                    f"knowledge promotion uses unknown task {promotion.task_id!r}"
                )
            unknown = set(promotion.verified_by) - task_by_id.keys()
            if unknown:
                raise ConfigurationError(
                    f"knowledge promotion {promotion.task_id!r} has unknown verifiers: "
                    f"{sorted(unknown)}"
                )
            invalid = [
                verifier
                for verifier in promotion.verified_by
                if task_by_id[verifier].reasoning_class != "audit"
                or promotion.task_id not in ancestors[verifier]
            ]
            if invalid:
                raise ConfigurationError(
                    f"knowledge promotion {promotion.task_id!r} is not downstream-"
                    f"verified by audit tasks: {sorted(invalid)}"
                )
