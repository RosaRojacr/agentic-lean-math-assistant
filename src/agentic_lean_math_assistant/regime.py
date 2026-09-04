"""Fixed pre-campaign gates around a frozen, model-generated execution DAG."""

from __future__ import annotations

import json
import os
import secrets
import shutil
import sys
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path, PurePosixPath
from typing import Any, Literal, TextIO

from .agent_runner import execute as execute_agent_request
from .artifacts import (
    atomic_write_json,
    atomic_write_text,
    digest_file,
    digest_tree,
    utc_now,
    verify_evidence_for_repair,
    verify_evidence_index,
)
from .config import CampaignSpec
from .journal import JournalError, append_state_snapshot, load_state_snapshot
from .metrics import write_compute_ledger
from .models import (
    CampaignOutcome,
    OrchestrationPlan,
    ResearchDecision,
    ResearchResult,
)
from .project import ProjectSpec
from .regression import regression_capability_catalog
from .runtime import (
    CampaignBuilder,
    CampaignOptions,
    CampaignRunError,
    campaign_resolved_for_run,
    campaign_run_lock,
    campaign_state,
    campaign_status,
    path_is_excluded,
    refresh_campaign_evidence,
)

MissingSourcePolicy = Literal["checkpoint", "continue"]

_PRE_CAMPAIGN_LOCK_TIMEOUT_SECONDS = 30.0


class RegimeError(RuntimeError):
    """A fixed pre- or post-campaign regime stage failed."""


@dataclass(frozen=True, slots=True)
class RegimeOptions:
    missing_source_policy: MissingSourcePolicy
    omp: str | None = None
    herdr: str = "herdr"
    lake: str = "lake"
    focus: bool = True
    close_herdr: bool = True
    output: TextIO | None = None
    waive_missing_sources: bool = False
    campaign_directive: Path | None = None
    input_overrides: tuple[tuple[str, Path], ...] = ()


class RegimeRunner:
    """Ask, research, plan, execute, retain, assess, and offer next strategies."""

    def __init__(self, project: ProjectSpec, options: RegimeOptions) -> None:
        if options.missing_source_policy not in ("checkpoint", "continue"):
            raise ValueError("missing_source_policy must be checkpoint or continue")
        override_targets = [target for target, _ in options.input_overrides]
        known_targets = {item.target for item in project.inputs}
        if len(override_targets) != len(set(override_targets)):
            raise ValueError("input override targets must be unique")
        unknown_targets = set(override_targets) - known_targets
        if unknown_targets:
            raise ValueError(
                f"input overrides name unknown project targets: {sorted(unknown_targets)}"
            )
        if options.campaign_directive is not None:
            directive = options.campaign_directive.expanduser().resolve()
            if not directive.is_file() or directive.is_symlink():
                raise ValueError("campaign directive must be a regular file")
        self.project = project
        self.options = options
        self.output = options.output or sys.stdout
        self.run_dir: Path | None = None
        self.pre_dir: Path | None = None
        self.pre_workspace: Path | None = None

    def run(self) -> Path:
        self._initialize_run()
        with self._serialized_pre_campaign_lock():
            return self._prepare_and_execute()

    def resume(self, run_dir: Path) -> Path:
        self.run_dir = run_dir.expanduser().resolve()
        self.pre_dir = self.run_dir / "pre-campaign"
        self.pre_workspace = self.pre_dir / "workspace"
        state = self._pre_state()
        if state.get("project_manifest") != str(self.project.manifest_path):
            raise RegimeError("pre-campaign run belongs to a different project")
        if state.get("status") == "executing":
            return self._resume_execution()
        with self._serialized_pre_campaign_lock():
            state = self._pre_state()
            if state.get("project_manifest") != str(self.project.manifest_path):
                raise RegimeError("pre-campaign run belongs to a different project")
            status = state.get("status")
            if status == "awaiting_sources":
                self._refresh_pre_workspace_references()
            if status in {
                "research_gate",
                "research",
                "planning",
                "awaiting_sources",
            }:
                return self._prepare_and_execute()
            if status == "executing":
                return self._resume_execution()
            raise RegimeError(
                "regime resume requires a preparation or executing checkpoint"
            )

    def _initialize_run(self) -> None:
        self.project.references_dir.mkdir(parents=True, exist_ok=True)
        self.project.knowledge_dir.mkdir(parents=True, exist_ok=True)
        self.project.runs_dir.mkdir(parents=True, exist_ok=True)
        run_id = (
            datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ") + f"-{secrets.token_hex(3)}"
        )
        self.run_dir = self.project.runs_dir / run_id
        self.pre_dir = self.run_dir / "pre-campaign"
        self.pre_workspace = self.pre_dir / "workspace"
        self.pre_workspace.mkdir(parents=True)
        shutil.copy2(self.project.problem_path, self.pre_workspace / "problem.md")
        self._refresh_pre_workspace_references()
        self._copy_knowledge_snapshot()
        self._copy_project_input_snapshots()
        directive_name: str | None = None
        directive = self.options.campaign_directive
        if directive is not None:
            directive_name = "campaign-directive.md"
            shutil.copy2(
                directive.expanduser().resolve(), self.pre_workspace / directive_name
            )
        self._save_pre_state(
            {
                "schema_version": 1,
                "project_manifest": str(self.project.manifest_path),
                "run_id": run_id,
                "status": "research_gate",
                "missing_source_policy": self.options.missing_source_policy,
                "created_at": utc_now(),
                "updated_at": utc_now(),
                "research_decision": None,
                "research_result": None,
                "plan": None,
                "campaign_directive": directive_name,
                "input_lineage": [
                    {"target": target, "source": str(source.expanduser().resolve())}
                    for target, source in self.options.input_overrides
                ],
            }
        )

    @contextmanager
    def _serialized_pre_campaign_lock(self) -> Iterator[None]:
        assert self.pre_dir is not None
        deadline = time.monotonic() + _PRE_CAMPAIGN_LOCK_TIMEOUT_SECONDS
        while True:
            manager = campaign_run_lock(self.pre_dir)
            try:
                manager.__enter__()
            except CampaignRunError as exc:
                if "another controller holds the campaign run lock" not in str(exc):
                    raise RegimeError(
                        f"cannot acquire pre-campaign controller: {exc}"
                    ) from exc
                if time.monotonic() >= deadline:
                    raise RegimeError(
                        "timed out acquiring pre-campaign controller lock"
                    ) from exc
                time.sleep(0.02)
                continue
            try:
                yield
            finally:
                manager.__exit__(None, None, None)
            return

    def _prepare_and_execute(self) -> Path:
        assert self.run_dir is not None
        assert self.pre_dir is not None
        assert self.pre_workspace is not None
        status = self._pre_state().get("status")
        if status == "research_gate":
            decision = self._research_gate()
            status = "research" if decision.decision == "research" else "planning"
        elif status in {"research", "planning", "awaiting_sources"}:
            decision = self._load_research_decision()
        else:
            raise RegimeError(
                f"pre-campaign preparation cannot resume from status {status!r}"
            )
        research_result: ResearchResult | None = None
        if decision.decision == "research":
            research_result = (
                self._load_research_result()
                if status == "planning"
                else self._research(
                    decision,
                    resuming=status == "awaiting_sources",
                )
            )
            assert research_result is not None
            critical = tuple(
                item
                for item in research_result.missing_sources
                if item.importance == "critical"
            )
            if (
                critical
                and self.options.missing_source_policy == "checkpoint"
                and not self.options.waive_missing_sources
            ):
                self._checkpoint_sources(critical)
                return self.run_dir
            self._promote_research_sources(research_result)
        plan = self._plan(decision, research_result)
        manifest = self._render_generated_campaign(plan)
        campaign = CampaignSpec.load(manifest)
        return self._execute_campaign(campaign, plan, resume_existing=False)

    def _resume_execution(self) -> Path:
        assert self.run_dir is not None and self.pre_dir is not None
        state = self._pre_state()
        plan_name = state.get("plan")
        if not isinstance(plan_name, str):
            raise RegimeError("executing regime has no retained plan")
        frozen_plan = (
            self.pre_dir / "frozen-inputs" / "pre-campaign" / "orchestration-plan.json"
        )
        plan_path = frozen_plan if frozen_plan.is_file() else self.pre_dir / plan_name
        try:
            plan_value = json.loads(plan_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise RegimeError(f"cannot reload orchestration plan: {exc}") from exc
        plan = OrchestrationPlan.parse(
            plan_value,
            max_tasks=self.project.max_tasks,
            max_parallel=self.project.max_parallel,
        )
        configuration = self.run_dir / "configuration"
        if configuration.is_dir():
            campaign = CampaignSpec.load_resolved(
                campaign_resolved_for_run(self.run_dir)
            )
            state_value = campaign_state(self.run_dir)
            if state_value.get("outcome") is not None:
                with self._serialized_campaign_lock():
                    committed = campaign_state(self.run_dir)
                    atomic_write_json(self.run_dir / "state.json", committed)
                    refresh_campaign_evidence(self.run_dir)
                return self.run_dir
            if state_value.get("status") == "awaiting_strategy":
                return self.run_dir
            return self._execute_campaign(campaign, plan, resume_existing=True)
        manifest = self._render_generated_campaign(plan)
        return self._execute_campaign(
            CampaignSpec.load(manifest), plan, resume_existing=False
        )

    def _execute_campaign(
        self,
        campaign: CampaignSpec,
        plan: OrchestrationPlan,
        *,
        resume_existing: bool,
    ) -> Path:
        assert self.run_dir is not None
        builder = CampaignBuilder(
            campaign,
            options=CampaignOptions(
                herdr=self.options.herdr,
                omp=self.options.omp or self.project.omp,
                lake=self.options.lake,
                focus=self.options.focus,
                close_herdr=self.options.close_herdr,
                output=self.output,
                max_parallel=plan.max_parallel,
            ),
            run_dir=self.run_dir,
        )
        run = self._run_builder(builder, resume_existing=resume_existing)
        if campaign_status(run) == "restart_required":
            run = self._bounded_restart(campaign, plan)
        with self._serialized_campaign_lock():
            status = campaign_status(run)
            state = campaign_state(run)
            if state.get("outcome") is not None:
                atomic_write_json(run / "state.json", state)
                refresh_campaign_evidence(run)
                return run
            if status == "replan_required":
                self._write_replan(plan)
            if status not in {"complete", "incomplete", "replan_required"}:
                return run
            write_compute_ledger(run, plan, self.project)
            refresh_campaign_evidence(run)
            outcome = self._final_assessment(plan, status)
            write_compute_ledger(run, plan, self.project, outcome)
            refresh_campaign_evidence(run)
            self._publish_knowledge(plan, outcome)
            decision = self._load_research_decision()
            research_result = self._load_research_result()
            self._record_research_state(decision, research_result)
            self._apply_outcome(outcome)
        return run

    def _run_builder(self, builder: CampaignBuilder, *, resume_existing: bool) -> Path:
        while True:
            try:
                return builder.resume() if resume_existing else builder.run()
            except CampaignRunError as exc:
                if "another controller holds the campaign run lock" not in str(exc):
                    raise
                time.sleep(0.02)

    @contextmanager
    def _serialized_campaign_lock(self) -> Iterator[None]:
        assert self.run_dir is not None
        while True:
            manager = campaign_run_lock(self.run_dir)
            try:
                manager.__enter__()
            except CampaignRunError as exc:
                if "another controller holds the campaign run lock" not in str(exc):
                    raise
                time.sleep(0.02)
                continue
            try:
                yield
            finally:
                manager.__exit__(None, None, None)
            return

    def _research_gate(self) -> ResearchDecision:
        assert self.pre_dir is not None and self.pre_workspace is not None
        prior_state = self.pre_workspace / "knowledge" / "research" / "state.json"
        prompt = self._prompt_template("research_gate.md") + self._assignment_context(
            "research_gate",
            {
                "problem": self.pre_workspace / "problem.md",
                "references": self.pre_workspace / "references",
                "accepted_knowledge": self.pre_workspace / "knowledge",
                "prior_research_state": prior_state
                if prior_state.is_file()
                else "None",
                "campaign_directive": (
                    self.pre_workspace / "campaign-directive.md"
                    if (self.pre_workspace / "campaign-directive.md").is_file()
                    else "None"
                ),
            },
        )
        gate_error: str | None = None
        for attempt, role in enumerate(
            ("research_gate", "research_gate_retry"), start=1
        ):
            gate_prompt = prompt
            if gate_error is not None:
                gate_prompt += (
                    "\n## Controller gate failure\n\n"
                    "The previous gate attempt failed or returned an invalid decision:\n\n"
                    f"`{gate_error}`\n\n"
                    "Re-evaluate the retained assignment and return the complete required "
                    "JSON decision.\n"
                )
            try:
                value = self._run_meta_agent(
                    role,
                    gate_prompt,
                    tools=("read", "glob"),
                    max_time=min(600, self.project.default_agent_time),
                    workspace=self._meta_workspace("research_gate"),
                    read_paths=(self.pre_workspace,),
                )
                decision = ResearchDecision.parse(value)
            except (OSError, ValueError, RegimeError) as exc:
                gate_error = f"{type(exc).__name__}: {exc}"
                if attempt == 2:
                    raise RegimeError(
                        f"research gate failed again after one retry: {gate_error}"
                    ) from exc
                continue
            break
        else:
            raise AssertionError("unreachable research gate loop")
        path = self.pre_dir / "research-decision.json"
        atomic_write_json(path, value)
        state = self._pre_state()
        state["research_decision"] = path.name
        state["status"] = "research" if decision.decision == "research" else "planning"
        state["updated_at"] = utc_now()
        self._save_pre_state(state)
        self._emit(f"research gate: {decision.decision} — {decision.reason}")
        return decision

    def _research(
        self, decision: ResearchDecision, *, resuming: bool
    ) -> ResearchResult:
        assert self.pre_dir is not None and self.pre_workspace is not None
        workspace = self._meta_workspace("publication_research")
        source_output = workspace / "references"
        source_output.mkdir(parents=True, exist_ok=True)
        prompt = self._prompt_template("researcher.md") + self._assignment_context(
            "publication_research",
            {
                "problem": self.pre_workspace / "problem.md",
                "authorized_queries": list(decision.required_queries),
                "references": source_output,
                "existing_references": self.pre_workspace / "references",
                "missing_source_policy": self.options.missing_source_policy,
                "resuming_after_manual_source_request": resuming,
                "manual_source_waiver": self.options.waive_missing_sources,
            },
        )
        tools = tuple(
            tool
            for tool in ("read", "grep", "glob", "web_search", "write")
            if tool in self.project.allowed_tools
        )
        value = self._run_meta_agent(
            "publication_research",
            prompt,
            tools=tools,
            max_time=self.project.default_agent_time,
            workspace=workspace,
            read_paths=(
                self.pre_workspace / "problem.md",
                self.pre_workspace / "references",
            ),
            reuse_completed=not resuming,
        )
        result = ResearchResult.parse(value)
        self._retain_research_sources(source_output, result)
        path = self.pre_dir / "research-result.json"
        atomic_write_json(path, value)
        state = self._pre_state()
        state["research_result"] = path.name
        state["status"] = "planning"
        state["updated_at"] = utc_now()
        self._save_pre_state(state)
        self._emit(f"research: {result.status} — {result.summary}")
        return result

    def _checkpoint_sources(self, critical: tuple[Any, ...]) -> None:
        assert self.pre_dir is not None
        requests = {
            "schema_version": 1,
            "status": "awaiting_sources",
            "policy": self.options.missing_source_policy,
            "sources": [asdict(item) for item in critical],
            "resume": (
                "Add obtained files to the project references directory, then run "
                "agentic-lean-math-assistant regime-resume --run <run> --project <project.toml>. "
                "If acquisition is impossible, add --waive-missing-sources."
            ),
        }
        atomic_write_json(self.pre_dir / "source-request.json", requests)
        state = self._pre_state()
        state["status"] = "awaiting_sources"
        state["updated_at"] = utc_now()
        self._save_pre_state(state)
        self._emit("research checkpoint: critical publications require user input")
        for item in critical:
            self._emit(f"- {item.title}: {item.request}")

    def _plan(
        self,
        decision: ResearchDecision,
        research_result: ResearchResult | None,
    ) -> OrchestrationPlan:
        assert self.pre_dir is not None and self.pre_workspace is not None
        capabilities = regression_capability_catalog(
            self.pre_workspace / "project-inputs"
        )
        base_prompt = self._prompt_template("planner.md") + self._assignment_context(
            "orchestration_planning",
            {
                "problem": self.pre_workspace / "problem.md",
                "research_decision": asdict(decision),
                "research_result": asdict(research_result) if research_result else None,
                "accepted_knowledge": self.pre_workspace / "knowledge",
                "prior_failures": self.pre_workspace / "knowledge",
                "campaign_directive": (
                    self.pre_workspace / "campaign-directive.md"
                    if (self.pre_workspace / "campaign-directive.md").is_file()
                    else "None"
                ),
                "capability_catalog": capabilities,
                "allowed_tools": list(self.project.allowed_tools),
                "max_tasks": self.project.max_tasks,
                "max_parallel": self.project.max_parallel,
                "default_agent_time": self.project.default_agent_time,
                "max_restarts": self.project.max_restarts,
                "phase_budgets_seconds": {
                    "pilot": self.project.pilot_agent_seconds,
                    "research": self.project.research_agent_seconds,
                    "formalization": self.project.formalization_agent_seconds,
                },
                "max_attempts_total": self.project.max_attempts_total,
                "max_invention_tasks": self.project.max_invention_tasks,
                "reasoning_profiles": {
                    reasoning_class: self.project.thinking_for(reasoning_class)
                    for reasoning_class in (
                        "execution",
                        "analysis",
                        "invention",
                        "audit",
                    )
                },
                "model_policy": {
                    "primary": {
                        reasoning_class: self.project.model_for(reasoning_class)
                        for reasoning_class in (
                            "execution",
                            "analysis",
                            "invention",
                            "audit",
                        )
                    },
                    "targeted": self.project.targeted_task_model,
                    "max_targeted_tasks": self.project.max_targeted_tasks,
                },
            },
        )
        plan_error: str | None = None
        proposed_value: object | None = None
        normalization: dict[str, object] | None = None
        for attempt, role in enumerate(
            (
                "orchestration_planner",
                "orchestration_planner_repair",
                "orchestration_planner_repair_2",
            ),
            start=1,
        ):
            prompt = base_prompt
            if plan_error is not None:
                prompt += (
                    "\n## Controller plan failure\n\n"
                    "The previous plan attempt failed or was rejected:\n\n"
                    f"`{plan_error}`\n\n"
                    "Return a complete replacement plan that satisfies every controller "
                    "constraint. Do not omit a strategy lane, task, dependency, or budget.\n"
                )
            try:
                value = self._run_meta_agent(
                    role,
                    prompt,
                    tools=("read", "grep", "glob"),
                    max_time=self.project.default_agent_time,
                    workspace=self._meta_workspace("orchestration_planner"),
                    read_paths=(self.pre_workspace,),
                    reuse_completed=True,
                )
                plan = OrchestrationPlan.parse(
                    value,
                    max_tasks=self.project.max_tasks,
                    max_parallel=self.project.max_parallel,
                )
                proposed_value = value
                value, plan, normalization = self._normalize_plan_budgets(value, plan)
                self._validate_plan_policy(plan)
                disallowed = {
                    tool
                    for task in plan.tasks
                    for tool in task.tools
                    if tool not in self.project.allowed_tools
                }
                if disallowed:
                    raise RegimeError(
                        f"planner selected disallowed tools: {sorted(disallowed)}"
                    )
            except (OSError, ValueError, RegimeError) as exc:
                plan_error = f"{type(exc).__name__}: {exc}"
                if attempt == 3:
                    raise RegimeError(
                        "orchestration plan failed after two repair attempts: "
                        f"{plan_error}"
                    ) from exc
                continue
            break
        else:
            raise AssertionError("unreachable planning loop")
        if normalization is not None:
            assert proposed_value is not None
            atomic_write_json(
                self.pre_dir / "orchestration-plan-proposed.json",
                proposed_value,
            )
            atomic_write_json(
                self.pre_dir / "orchestration-plan-normalization.json",
                normalization,
            )
        path = self.pre_dir / "orchestration-plan.json"
        atomic_write_json(path, value)
        state = self._pre_state()
        state["plan"] = path.name
        state["status"] = "executing"
        state["updated_at"] = utc_now()
        self._save_pre_state(state)
        self._emit(
            f"orchestration plan: {len(plan.tasks)} agents, max {plan.max_parallel} parallel"
        )
        return plan

    def _normalize_plan_budgets(
        self, value: dict[str, Any], plan: OrchestrationPlan
    ) -> tuple[dict[str, Any], OrchestrationPlan, dict[str, object] | None]:
        normalized = json.loads(json.dumps(value))
        if not isinstance(normalized, dict):
            raise RegimeError("orchestration plan must be an object")
        raw_tasks = normalized.get("tasks")
        if not isinstance(raw_tasks, list):
            raise RegimeError("orchestration plan tasks must be an array")
        tasks: list[dict[str, Any]] = []
        for raw in raw_tasks:
            if not isinstance(raw, dict):
                raise RegimeError("orchestration plan task must be an object")
            tasks.append(raw)
        if len(tasks) != len(plan.tasks):
            raise RegimeError("orchestration plan task normalization lost a task")
        changes: list[dict[str, object]] = []

        def integer(task: dict[str, Any], key: str) -> int:
            result = task.get(key)
            if not isinstance(result, int) or isinstance(result, bool):
                raise RegimeError(f"orchestration task {key} is not an integer")
            return result

        def task_id(task: dict[str, Any]) -> str:
            result = task.get("id")
            if not isinstance(result, str):
                raise RegimeError("orchestration task id is invalid")
            return result

        attempt_cost = sum(integer(task, "max_attempts") * 2 for task in tasks)
        minimum_attempt_cost = len(tasks) * 2
        if minimum_attempt_cost > self.project.max_attempts_total:
            raise RegimeError(
                "orchestration plan cannot fit the invocation-attempt budget: "
                f"{minimum_attempt_cost} > {self.project.max_attempts_total}"
            )
        while attempt_cost > self.project.max_attempts_total:
            candidates = [task for task in tasks if integer(task, "max_attempts") > 1]
            if not candidates:
                raise RegimeError(
                    "orchestration plan cannot be normalized to the "
                    "invocation-attempt budget"
                )
            selected = min(
                candidates,
                key=lambda task: (
                    -integer(task, "max_attempts") * integer(task, "timeout"),
                    task_id(task),
                ),
            )
            before = integer(selected, "max_attempts")
            selected["max_attempts"] = before - 1
            attempt_cost -= 2
            changes.append(
                {
                    "task_id": task_id(selected),
                    "field": "max_attempts",
                    "before": before,
                    "after": before - 1,
                    "reason": "invocation-attempt budget",
                }
            )

        phase_limits = {
            "pilot": self.project.pilot_agent_seconds,
            "research": self.project.research_agent_seconds,
            "formalization": self.project.formalization_agent_seconds,
        }
        for phase, limit in phase_limits.items():
            phase_tasks = [task for task in tasks if task.get("phase") == phase]
            weights = {
                task_id(task): 2 * integer(task, "max_attempts") for task in phase_tasks
            }
            cost = sum(
                weights[task_id(task)] * integer(task, "timeout")
                for task in phase_tasks
            )
            if cost <= limit:
                continue
            minimum = sum(weights.values()) * 30
            if minimum > limit:
                raise RegimeError(
                    f"orchestration plan cannot fit the {phase} phase budget: "
                    f"minimum {minimum} > {limit}"
                )
            requested_extra = cost - minimum
            available_extra = limit - minimum
            for task in phase_tasks:
                before = integer(task, "timeout")
                after = 30 + (before - 30) * available_extra // requested_extra
                if after != before:
                    task["timeout"] = after
                    changes.append(
                        {
                            "task_id": task_id(task),
                            "field": "timeout",
                            "before": before,
                            "after": after,
                            "reason": f"{phase} phase agent-second budget",
                        }
                    )

        if not changes:
            return value, plan, None
        normalized_plan = OrchestrationPlan.parse(
            normalized,
            max_tasks=self.project.max_tasks,
            max_parallel=self.project.max_parallel,
        )
        return (
            normalized,
            normalized_plan,
            {
                "schema_version": 1,
                "formula": "sum(2 * timeout * max_attempts)",
                "changes": changes,
            },
        )

    def _validate_plan_policy(self, plan: OrchestrationPlan) -> None:
        phase_limits = {
            "pilot": self.project.pilot_agent_seconds,
            "research": self.project.research_agent_seconds,
            "formalization": self.project.formalization_agent_seconds,
        }
        phase_costs = {
            phase: sum(
                task.timeout * task.max_attempts * 2
                for task in plan.tasks
                if task.phase == phase
            )
            for phase in phase_limits
        }
        exceeded = {
            phase: (phase_costs[phase], limit)
            for phase, limit in phase_limits.items()
            if phase_costs[phase] > limit
        }
        if exceeded:
            raise RegimeError(
                f"orchestration plan exceeds phase agent-second budgets: {exceeded}"
            )
        attempts = sum(task.max_attempts * 2 for task in plan.tasks)
        if attempts > self.project.max_attempts_total:
            raise RegimeError(
                "orchestration plan exceeds the invocation-attempt budget: "
                f"{attempts} > {self.project.max_attempts_total}"
            )
        invention_count = sum(
            task.reasoning_class == "invention" for task in plan.tasks
        )
        if invention_count > self.project.max_invention_tasks:
            raise RegimeError(
                "orchestration plan exceeds the invention-task budget: "
                f"{invention_count} > {self.project.max_invention_tasks}"
            )
        targeted_tasks = [task for task in plan.tasks if task.model is not None]
        if len(targeted_tasks) > self.project.max_targeted_tasks:
            raise RegimeError(
                "orchestration plan exceeds the targeted-model task budget: "
                f"{len(targeted_tasks)} > {self.project.max_targeted_tasks}"
            )
        invalid_targeted_models = {
            task.model
            for task in targeted_tasks
            if task.model is not None and task.model != self.project.targeted_task_model
        }
        if invalid_targeted_models:
            raise RegimeError(
                "targeted tasks must use the configured targeted_task_model: "
                f"{sorted(invalid_targeted_models)}"
            )
        missing_pilots = [
            strategy.strategy_id
            for strategy in plan.strategy_portfolio
            if not any(
                task.strategy_id == strategy.strategy_id and task.phase == "pilot"
                for task in plan.tasks
            )
        ]
        if missing_pilots:
            raise RegimeError(
                f"strategy lanes lack pilot tasks: {sorted(missing_pilots)}"
            )
        catalog = {
            str(item["id"]): item
            for item in regression_capability_catalog(
                self.pre_workspace / "project-inputs"
                if self.pre_workspace is not None
                else None
            )
        }
        decisions = plan.capabilities_by_id
        missing_capabilities = catalog.keys() - decisions.keys()
        extra_capabilities = decisions.keys() - catalog.keys()
        if missing_capabilities or extra_capabilities:
            raise RegimeError(
                "capability decisions differ from the supplied catalog; "
                f"missing={sorted(missing_capabilities)}, "
                f"extra={sorted(extra_capabilities)}"
            )
        for capability_id, decision in decisions.items():
            if decision.decision == "skip":
                continue
            if not catalog[capability_id].get("available"):
                raise RegimeError(
                    f"planner selected unavailable capability {capability_id!r}"
                )
            assert decision.task_id is not None
            task = plan.by_id[decision.task_id]
            callable_from_task = (
                "bash" in task.tools
                and capability_id.replace("_", "-") in task.instructions
            ) or (
                "eval" in task.tools
                and (
                    "assess_regression" in task.instructions
                    if capability_id == "regression_assess"
                    else "fit_regression" in task.instructions
                )
            )
            if not callable_from_task:
                raise RegimeError(
                    f"capability {capability_id!r} task must name its CLI or Python API "
                    "and select the corresponding execution tool"
                )
        assess = decisions["regression_assess"]
        fit = decisions["regression_fit"]
        if fit.decision == "use":
            if assess.decision != "use":
                raise RegimeError("regression_fit requires regression_assess")
            assert assess.task_id is not None and fit.task_id is not None
            if assess.task_id == fit.task_id:
                raise RegimeError(
                    "regression assessment and fitting require separate task IDs"
                )
            ancestors = set(plan.by_id[fit.task_id].depends_on)
            pending = list(ancestors)
            while pending:
                dependency = pending.pop()
                for ancestor in plan.by_id[dependency].depends_on:
                    if ancestor not in ancestors:
                        ancestors.add(ancestor)
                        pending.append(ancestor)
            if assess.task_id not in ancestors:
                raise RegimeError(
                    "regression_fit task must descend from the regression_assess task"
                )

    def _render_generated_campaign(self, plan: OrchestrationPlan) -> Path:
        assert self.pre_dir is not None and self.run_dir is not None
        frozen = self._freeze_campaign_inputs()
        generated = self.pre_dir / "generated"
        generated.mkdir(parents=True, exist_ok=True)
        prompts = generated / "tasks"
        shutil.copy2(frozen / "problem.md", generated / "problem.md")
        prompts.mkdir(parents=True, exist_ok=True)
        lines = [
            "schema_version = 1",
            "",
            "[campaign]",
            f"id = {json.dumps(self.project.project_id)}",
            f"title = {json.dumps(self.project.title)}",
            'instructions = "problem.md"',
            f"runs_dir = {json.dumps(str(self.project.runs_dir))}",
            "max_revisions = 0",
            "",
        ]
        execution = self.project.execution
        lines.extend(
            [
                "[execution]",
                f"sandbox = {str(execution.sandbox).lower()}",
                f"network = {str(execution.network).lower()}",
                f"memory_max_mb = {execution.memory_max_mb}",
                f"cpu_quota_percent = {execution.cpu_quota_percent}",
                f"tasks_max = {execution.tasks_max}",
                f"file_size_max_mb = {execution.file_size_max_mb}",
                f"workspace_max_mb = {execution.workspace_max_mb}",
                "allowed_executable_paths = "
                + json.dumps(
                    [str(path) for path in execution.allowed_executable_paths]
                ),
                "environment_allow = " + json.dumps(list(execution.environment_allow)),
                "secret_environment = "
                + json.dumps(list(execution.secret_environment)),
                "",
            ]
        )
        input_records: list[tuple[Path, str, tuple[str, ...]]] = [
            (frozen / "problem.md", "problem.md", ()),
            (frozen / "references", "references", ()),
            (frozen / "knowledge", "knowledge", ()),
            (
                frozen / "pre-campaign" / "research-decision.json",
                "pre-campaign/research-decision.json",
                (),
            ),
            (
                frozen / "pre-campaign" / "orchestration-plan.json",
                "pre-campaign/orchestration-plan.json",
                (),
            ),
        ]
        research_result = frozen / "pre-campaign" / "research-result.json"
        if research_result.is_file():
            input_records.append(
                (research_result, "pre-campaign/research-result.json", ())
            )
        campaign_directive = frozen / "pre-campaign" / "campaign-directive.md"
        if campaign_directive.is_file():
            input_records.append(
                (
                    campaign_directive,
                    "pre-campaign/campaign-directive.md",
                    (),
                )
            )
        input_records.extend(
            (frozen / item.target, item.target, item.excludes)
            for item in self.project.inputs
        )
        seen_targets: set[str] = set()
        for source, target, excludes in input_records:
            if target in seen_targets:
                raise RegimeError(
                    f"generated campaign has duplicate input target {target!r}"
                )
            seen_targets.add(target)
            lines.extend(
                [
                    "[[inputs]]",
                    f"source = {json.dumps(str(source))}",
                    f"target = {json.dumps(target)}",
                    'strategy = "copy"',
                ]
            )
            if excludes:
                lines.append(f"excludes = {json.dumps(list(excludes))}")
            lines.append("")
        for task in plan.tasks:
            task_prompt = prompts / f"{task.task_id}.md"
            task_directive = "\n".join(
                [
                    task.instructions.rstrip(),
                    "",
                    "## Frozen planning contract",
                    f"- Phase: `{task.phase}`",
                    f"- Strategy lane: `{task.strategy_id or 'shared'}`",
                    f"- Reasoning class: `{task.reasoning_class}`",
                    f"- Initial novelty: {task.novelty}",
                    "- Expected retained evidence:",
                    *(f"  - {item}" for item in task.expected_evidence),
                    "",
                ]
            )
            atomic_write_text(task_prompt, task_directive)
            lines.extend(
                [
                    "[[stages]]",
                    f"id = {json.dumps(task.task_id)}",
                    f"title = {json.dumps(task.title)}",
                    'mode = "research"',
                    'feature = "agent"',
                    f"depends_on = {json.dumps(list(task.depends_on))}",
                    f"required = {'true' if task.required else 'false'}",
                    f"max_attempts = {task.max_attempts}",
                    f"failure_policy = {json.dumps(task.failure_policy)}",
                    "[stages.config]",
                    f"instructions = {json.dumps(f'tasks/{task.task_id}.md')}",
                    f"category = {json.dumps(task.category)}",
                    f"tools = {json.dumps(list(task.tools))}",
                    f"max_time = {task.timeout}",
                    "empty_output_retries = 1",
                    "novelty_gate = true",
                    f"continuation_gate = {str(task.continuation_gate).lower()}",
                ]
            )
            selected_model = task.model or self.project.model_for(task.reasoning_class)
            if selected_model is not None:
                lines.append(f"model = {json.dumps(selected_model)}")
            lines.append(
                f"thinking = {json.dumps(self.project.thinking_for(task.reasoning_class))}"
            )
            lines.append("")
        for obligation in plan.obligations:
            lines.extend(
                [
                    "[[obligations]]",
                    f"id = {json.dumps(obligation.obligation_id)}",
                    f"description = {json.dumps(obligation.statement)}",
                    f"evidence_stages = {json.dumps(list(obligation.evidence_tasks))}",
                    "",
                ]
            )
        manifest = generated / "campaign.toml"
        atomic_write_text(manifest, "\n".join(lines))
        return manifest

    def _bounded_restart(self, campaign: CampaignSpec, plan: OrchestrationPlan) -> Path:
        assert self.run_dir is not None
        run = self.run_dir
        for attempt in range(1, self.project.max_restarts + 1):
            if campaign_status(run) != "restart_required":
                break
            self._emit(
                f"failure policy: restarting frozen campaign "
                f"({attempt}/{self.project.max_restarts})"
            )
            options = CampaignOptions(
                herdr=self.options.herdr,
                omp=self.options.omp or self.project.omp,
                lake=self.options.lake,
                focus=self.options.focus,
                close_herdr=self.options.close_herdr,
                output=self.output,
                retry_stages=tuple(task.task_id for task in plan.tasks),
                max_parallel=plan.max_parallel,
            )
            builder = CampaignBuilder(campaign, options=options, run_dir=self.run_dir)
            run = self._run_builder(builder, resume_existing=True)
        return run

    def _write_replan(self, prior_plan: OrchestrationPlan) -> None:
        assert (
            self.pre_dir is not None
            and self.pre_workspace is not None
            and self.run_dir is not None
        )
        failures = [
            path.relative_to(self.run_dir).as_posix()
            for path in sorted(self.run_dir.glob("agents/*/*/*-failure.json"))
        ]
        prompt = self._prompt_template("planner.md") + self._assignment_context(
            "failure_replanning",
            {
                "prior_plan": asdict(prior_plan),
                "failure_records": failures,
                "instruction": (
                    "Produce a materially different successor plan. Every task must "
                    "identify the failed prior method, its new method, and expected "
                    "new evidence. Do not execute the plan."
                ),
                "max_tasks": self.project.max_tasks,
                "max_parallel": self.project.max_parallel,
                "capability_catalog": regression_capability_catalog(
                    self.pre_workspace / "project-inputs"
                ),
                "allowed_tools": list(self.project.allowed_tools),
                "phase_budgets_seconds": {
                    "pilot": self.project.pilot_agent_seconds,
                    "research": self.project.research_agent_seconds,
                    "formalization": self.project.formalization_agent_seconds,
                },
                "max_attempts_total": self.project.max_attempts_total,
                "max_invention_tasks": self.project.max_invention_tasks,
                "reasoning_profiles": {
                    reasoning_class: self.project.thinking_for(reasoning_class)
                    for reasoning_class in (
                        "execution",
                        "analysis",
                        "invention",
                        "audit",
                    )
                },
                "model_policy": {
                    "primary": {
                        reasoning_class: self.project.model_for(reasoning_class)
                        for reasoning_class in (
                            "execution",
                            "analysis",
                            "invention",
                            "audit",
                        )
                    },
                    "targeted": self.project.targeted_task_model,
                    "max_targeted_tasks": self.project.max_targeted_tasks,
                },
            },
        )
        workspace = self._meta_workspace("failure_replanner")
        value = self._run_meta_agent(
            "failure_replanner",
            prompt,
            tools=("read", "grep", "glob"),
            max_time=self.project.default_agent_time,
            workspace=workspace,
            read_paths=(self.run_dir,),
            reuse_completed=True,
        )
        successor = OrchestrationPlan.parse(
            value,
            max_tasks=self.project.max_tasks,
            max_parallel=self.project.max_parallel,
        )
        self._validate_plan_policy(successor)
        atomic_write_json(self.pre_dir / "successor-plan.json", value)

    def _validate_outcome_evidence(self, outcome: CampaignOutcome) -> None:
        assert self.run_dir is not None
        references = [
            *outcome.evidence,
            *(
                path
                for disposition in outcome.obligation_dispositions
                for path in disposition.evidence
            ),
            *(
                path
                for promotion in outcome.knowledge_promotions
                for path in promotion.evidence
            ),
        ]
        for relative in references:
            pure = PurePosixPath(relative)
            if (
                pure.is_absolute()
                or not pure.parts
                or any(part in ("", ".", "..") for part in pure.parts)
            ):
                raise RegimeError(f"outcome evidence path is unsafe: {relative!r}")
            path = self.run_dir.joinpath(*pure.parts)
            if not path.is_file() or path.is_symlink():
                raise RegimeError(
                    f"outcome evidence path is not a retained regular file: {relative!r}"
                )

    def _final_assessment(
        self, plan: OrchestrationPlan, execution_status: str
    ) -> CampaignOutcome:
        assert self.run_dir is not None
        workspace = self._meta_workspace("main_assessment")
        staged_report = workspace / "final-report.md"
        staged_outcome = workspace / "outcome.json"
        base_prompt = self._prompt_template(
            "final_reporter.md"
        ) + self._assignment_context(
            "main_assessment",
            {
                "original_problem": self.run_dir / "input-snapshot" / "problem.md",
                "frozen_plan": asdict(plan),
                "execution_status": execution_status,
                "agent_outputs": self.run_dir / "agents",
                "deterministic_stages": self.run_dir / "stages",
                "state": self.run_dir / "state.json",
                "report_path": staged_report,
                "outcome_path": staged_outcome,
            },
        )
        validation_error: str | None = None
        for attempt, role in enumerate(
            ("main_assessment", "main_assessment_repair"), start=1
        ):
            prompt = base_prompt
            if validation_error is not None:
                prompt += (
                    "\n## Controller assessment failure\n\n"
                    "The previous assessment attempt failed or was rejected and was not "
                    "published:\n\n"
                    f"`{validation_error}`\n\n"
                    "Write both required artifacts from retained evidence. Correct any "
                    "reported validation defect; do not weaken evidence or invent task IDs.\n"
                )
                staged_report.unlink(missing_ok=True)
                staged_outcome.unlink(missing_ok=True)
            try:
                self._run_meta_agent(
                    role,
                    prompt,
                    tools=("read", "grep", "glob", "write"),
                    max_time=self.project.default_agent_time,
                    workspace=workspace,
                    read_paths=(self.run_dir,),
                    expect_json=False,
                    reuse_completed=True,
                )
                if (
                    not staged_report.is_file()
                    or staged_report.is_symlink()
                    or not staged_outcome.is_file()
                    or staged_outcome.is_symlink()
                ):
                    raise RegimeError(
                        "main assessment did not write regular report and outcome files"
                    )
                try:
                    value = json.loads(staged_outcome.read_text(encoding="utf-8"))
                except json.JSONDecodeError as exc:
                    raise RegimeError(
                        f"main assessment outcome is invalid JSON: {exc}"
                    ) from exc
                outcome = CampaignOutcome.parse(value)
                outcome.validate_against(plan)
                self._validate_outcome_evidence(outcome)
            except (OSError, ValueError, RegimeError) as exc:
                validation_error = f"{type(exc).__name__}: {exc}"
                if attempt == 2:
                    raise RegimeError(
                        "main assessment failed again after one repair attempt: "
                        f"{validation_error}"
                    ) from exc
                continue
            report_text = staged_report.read_text(encoding="utf-8")
            atomic_write_text(self.run_dir / "final-report.md", report_text)
            atomic_write_json(self.run_dir / "outcome.json", value)
            self._emit("\n" + report_text.rstrip() + "\n")
            return outcome
        raise AssertionError("unreachable assessment loop")

    def _apply_outcome(self, outcome: CampaignOutcome) -> None:
        assert self.run_dir is not None
        state_path = self.run_dir / "state.json"
        value = campaign_state(self.run_dir)
        value["outcome"] = outcome.status
        value["status"] = (
            "complete" if outcome.status == "solved" else "awaiting_strategy"
        )
        value["error"] = None if outcome.status == "solved" else outcome.summary
        value["completed_at"] = utc_now()
        append_state_snapshot(
            self.run_dir, value, reason=f"regime:outcome:{outcome.status}"
        )
        atomic_write_json(state_path, value)
        refresh_campaign_evidence(self.run_dir)
        if outcome.status != "solved":
            self._emit("The problem remains unresolved. Choose one strategy:")
            for strategy in outcome.strategies:
                marker = " [Recommended]" if strategy.recommended else ""
                self._emit(f"- {strategy.strategy_id}: {strategy.title}{marker}")
            self._emit(
                "Record a decision with: agentic-lean-math-assistant choose-strategy "
                f"--run {self.run_dir} --strategy <id|stop>"
            )

    def _publish_knowledge(
        self, plan: OrchestrationPlan, outcome: CampaignOutcome
    ) -> None:
        assert self.run_dir is not None
        state = campaign_state(self.run_dir)
        task_by_id = plan.by_id
        assessment = digest_file(
            self.run_dir / "outcome.json", relative_to=self.run_dir
        )
        for promotion in outcome.knowledge_promotions:
            task = task_by_id[promotion.task_id]
            stage_state = state.get("stages", {}).get(promotion.task_id, {})
            if stage_state.get("status") != "succeeded":
                raise RegimeError(
                    f"cannot promote unsuccessful task {promotion.task_id!r}"
                )
            failed_verifiers = [
                verifier
                for verifier in promotion.verified_by
                if state.get("stages", {}).get(verifier, {}).get("status")
                != "succeeded"
            ]
            if failed_verifiers:
                raise RegimeError(
                    f"cannot promote {promotion.task_id!r}; verifier tasks did not "
                    f"succeed: {sorted(failed_verifiers)}"
                )
            source_dir = self.run_dir / "agents" / task.category / task.task_id
            reports = sorted(source_dir.glob("attempt-*.md"))
            if not reports:
                raise RegimeError(
                    f"cannot promote {promotion.task_id!r}; report is unavailable"
                )
            category = self.project.knowledge_dir / task.category
            category.mkdir(parents=True, exist_ok=True)
            destination = category / f"{self.run_dir.name}-{task.task_id}.md"
            shutil.copy2(reports[-1], destination)
            artifact = digest_file(destination, relative_to=self.project.knowledge_dir)
            atomic_write_json(
                category / f"{self.run_dir.name}-{task.task_id}.json",
                {
                    "schema_version": 2,
                    "run_id": self.run_dir.name,
                    "task_id": task.task_id,
                    "category": task.category,
                    "strategy_id": task.strategy_id,
                    "status": "accepted",
                    "summary": promotion.summary,
                    "evidence": list(promotion.evidence),
                    "limitations": list(promotion.limitations),
                    "verified_by": list(promotion.verified_by),
                    "assessment_sha256": assessment.sha256,
                    "report": artifact.to_dict(),
                },
            )
        for task in plan.tasks:
            source_dir = self.run_dir / "agents" / task.category / task.task_id
            failures = sorted(source_dir.glob("*-failure.json"))
            if failures:
                failure_dir = self.project.knowledge_dir / task.category / "failures"
                failure_dir.mkdir(parents=True, exist_ok=True)
                shutil.copy2(
                    failures[-1],
                    failure_dir / f"{self.run_dir.name}-{task.task_id}.json",
                )
        self._write_knowledge_index()

    def _write_knowledge_index(self) -> None:
        self.project.knowledge_dir.mkdir(parents=True, exist_ok=True)
        artifacts = digest_tree(self.project.knowledge_dir, exclude={"index.json"})
        atomic_write_json(
            self.project.knowledge_dir / "index.json",
            {
                "schema_version": 1,
                "generated_at": utc_now(),
                "artifacts": [artifact.to_dict() for artifact in artifacts],
            },
        )

    def _record_research_state(
        self,
        decision: ResearchDecision,
        result: ResearchResult | None,
    ) -> None:
        assert self.run_dir is not None
        research_dir = self.project.knowledge_dir / "research"
        research_dir.mkdir(parents=True, exist_ok=True)
        reference_artifacts = digest_tree(self.project.references_dir)
        atomic_write_json(
            research_dir / "state.json",
            {
                "schema_version": 1,
                "updated_at": utc_now(),
                "problem_sha256": digest_file(
                    self.run_dir / "input-snapshot" / "problem.md",
                    relative_to=self.run_dir / "input-snapshot",
                ).sha256,
                "decision": asdict(decision),
                "result": asdict(result) if result is not None else None,
                "references": [artifact.to_dict() for artifact in reference_artifacts],
            },
        )
        self._write_knowledge_index()

    def _retain_research_sources(
        self, source_root: Path, result: ResearchResult
    ) -> None:
        assert self.pre_workspace is not None
        self._reject_snapshot_symlinks(source_root)
        entries = tuple(source_root.rglob("*"))
        invalid = next(
            (path for path in entries if not path.is_dir() and not path.is_file()),
            None,
        )
        if invalid is not None:
            raise RegimeError(f"research output is not a regular file: {invalid}")
        observed = {
            path.relative_to(source_root).as_posix()
            for path in entries
            if path.is_file()
        }
        requested: set[str] = set()
        for relative in result.sources_added:
            pure = PurePosixPath(relative)
            if (
                pure.is_absolute()
                or not pure.parts
                or any(part in ("", ".", "..") for part in pure.parts)
            ):
                raise RegimeError(f"research source has an unsafe path: {relative}")
            normalized = pure.as_posix()
            if normalized in requested:
                raise RegimeError(f"research source is duplicated: {relative}")
            requested.add(normalized)
        if observed != requested:
            raise RegimeError(
                "research output files do not match sources_added: "
                f"missing={sorted(requested - observed)}, "
                f"unlisted={sorted(observed - requested)}"
            )
        destination_root = self.pre_workspace / "references"
        for relative in sorted(requested):
            source = source_root / relative
            destination = destination_root / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            for orphan in destination.parent.glob(f".{destination.name}.*.tmp"):
                if not orphan.is_file() or orphan.is_symlink():
                    raise RegimeError(
                        f"invalid orphaned research source temporary: {orphan}"
                    )
                orphan.unlink()
            if destination.exists() or destination.is_symlink():
                if (
                    destination.is_file()
                    and not destination.is_symlink()
                    and digest_file(source, relative_to=source_root).sha256
                    == digest_file(destination, relative_to=destination_root).sha256
                ):
                    continue
                raise RegimeError(
                    f"research source conflicts with a retained reference: {relative}"
                )
            temporary = destination.parent / (
                f".{destination.name}.{secrets.token_hex(6)}.tmp"
            )
            try:
                with (
                    source.open("rb") as input_stream,
                    temporary.open("xb") as output_stream,
                ):
                    shutil.copyfileobj(input_stream, output_stream)
                    output_stream.flush()
                    os.fsync(output_stream.fileno())
                os.replace(temporary, destination)
                descriptor = os.open(destination.parent, os.O_RDONLY | os.O_DIRECTORY)
                try:
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)
            finally:
                temporary.unlink(missing_ok=True)

    def _promote_research_sources(self, result: ResearchResult) -> None:
        assert self.pre_workspace is not None
        source_root = (self.pre_workspace / "references").resolve()
        destination_root = self.project.references_dir.resolve()
        for relative in result.sources_added:
            source = (source_root / relative).resolve()
            try:
                safe_relative = source.relative_to(source_root)
            except ValueError as exc:
                raise RegimeError(
                    f"research source escapes references: {relative}"
                ) from exc
            if not source.is_file() or source.is_symlink():
                raise RegimeError(f"research source is not a regular file: {relative}")
            destination = destination_root / safe_relative
            try:
                destination.resolve(strict=False).relative_to(destination_root)
            except ValueError as exc:
                raise RegimeError(
                    f"research destination escapes references: {relative}"
                ) from exc
            destination.parent.mkdir(parents=True, exist_ok=True)
            if destination.exists() or destination.is_symlink():
                if (
                    destination.is_file()
                    and not destination.is_symlink()
                    and digest_file(source, relative_to=source_root).sha256
                    == digest_file(destination, relative_to=destination_root).sha256
                ):
                    continue
                raise RegimeError(
                    f"research source conflicts with a retained reference: {relative}"
                )
            temporary = destination.parent / (
                f".{destination.name}.{secrets.token_hex(6)}.tmp"
            )
            try:
                with (
                    source.open("rb") as input_stream,
                    temporary.open("xb") as output_stream,
                ):
                    shutil.copyfileobj(input_stream, output_stream)
                    output_stream.flush()
                    os.fsync(output_stream.fileno())
                os.replace(temporary, destination)
                descriptor = os.open(destination.parent, os.O_RDONLY | os.O_DIRECTORY)
                try:
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)
            finally:
                temporary.unlink(missing_ok=True)

    def _run_meta_agent(
        self,
        role: str,
        prompt_text: str,
        *,
        tools: tuple[str, ...],
        max_time: int,
        workspace: Path | None = None,
        read_paths: tuple[Path, ...] = (),
        expect_json: bool = True,
        reuse_completed: bool = False,
    ) -> dict[str, Any]:
        assert (
            self.run_dir is not None
            and self.pre_dir is not None
            and self.pre_workspace is not None
        )
        role_root = self.pre_dir / "roles" / role
        role_root.mkdir(parents=True, exist_ok=True)
        retained_attempts = sorted(
            (
                path
                for path in role_root.iterdir()
                if path.is_dir()
                and not path.is_symlink()
                and path.name.startswith("attempt-")
                and path.name.removeprefix("attempt-").isdigit()
            ),
            key=lambda path: int(path.name.removeprefix("attempt-")),
        )
        if reuse_completed:
            for retained in reversed(retained_attempts):
                retained_output = retained / "output.json"
                if retained_output.is_file() and self._meta_receipt_succeeded(
                    retained / "receipt.json"
                ):
                    if not expect_json:
                        return {}
                    try:
                        value = json.loads(retained_output.read_text(encoding="utf-8"))
                    except json.JSONDecodeError as exc:
                        raise RegimeError(
                            f"meta-agent {role!r} returned invalid JSON: {exc}"
                        ) from exc
                    if not isinstance(value, dict):
                        raise RegimeError(
                            f"meta-agent {role!r} must return a JSON object"
                        )
                    return value
        attempt = (
            int(retained_attempts[-1].name.removeprefix("attempt-")) + 1
            if retained_attempts
            else 1
        )
        role_dir = role_root / f"attempt-{attempt:03d}"
        role_dir.mkdir()
        prompt = role_dir / "prompt.md"
        output = role_dir / "output.json"
        request = role_dir / "request.json"
        receipt = role_dir / "receipt.json"
        atomic_write_text(prompt, prompt_text.rstrip() + "\n")
        selected_workspace = (workspace or self.pre_workspace).resolve()
        atomic_write_json(
            request,
            {
                "role_id": role,
                "attempt": attempt,
                "omp": self.options.omp or self.project.omp,
                "workspace": str(selected_workspace),
                "run_dir": str(self.run_dir),
                "prompt": str(prompt),
                "output": str(output),
                "stdout_log": str(role_dir / "stdout.log"),
                "stderr_log": str(role_dir / "stderr.log"),
                "receipt": str(receipt),
                "tools": list(tools),
                "model": self.project.planner_model,
                "thinking": self.project.planner_thinking,
                "max_time": max_time,
                "empty_output_retries": 1,
                "execution": self.project.execution.to_dict(),
                "sandbox_read_paths": [
                    str(path.resolve()) for path in (prompt, *read_paths)
                ],
            },
        )
        exit_code = execute_agent_request(request)
        if exit_code != 0 or not output.is_file():
            raise RegimeError(f"meta-agent {role!r} failed; see {role_dir}")
        if not expect_json:
            return {}
        try:
            value = json.loads(output.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise RegimeError(
                f"meta-agent {role!r} returned invalid JSON: {exc}"
            ) from exc
        if not isinstance(value, dict):
            raise RegimeError(f"meta-agent {role!r} must return a JSON object")
        return value

    def _meta_workspace(self, role: str) -> Path:
        assert self.pre_dir is not None
        workspace = self.pre_dir / "meta-workspaces" / role
        workspace.mkdir(parents=True, exist_ok=True)
        return workspace

    @staticmethod
    def _meta_receipt_succeeded(receipt: Path) -> bool:
        try:
            value = json.loads(receipt.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return False
        return isinstance(value, dict) and value.get("status") == "succeeded"

    def _assignment_context(self, role: str, values: dict[str, object]) -> str:
        rendered = json.dumps(
            {
                key: str(value) if isinstance(value, Path) else value
                for key, value in values.items()
            },
            ensure_ascii=False,
            indent=2,
            default=str,
        )
        return f"\n\n## Retained assignment\n\n- Regime role: `{role}`\n\n```json\n{rendered}\n```\n"

    def _prompt_template(self, name: str) -> str:
        path = Path(__file__).with_name("prompts") / name
        return path.read_text(encoding="utf-8").rstrip()

    def _copy_project_input_snapshots(self) -> None:
        assert self.pre_workspace is not None
        root = self.pre_workspace / "project-inputs"
        root.mkdir()
        overrides = {
            target: source.expanduser().resolve()
            for target, source in self.options.input_overrides
        }
        for item in self.project.inputs:
            self._copy_regular_source(
                overrides.get(item.target, item.source),
                root / item.target,
                excludes=item.excludes,
            )

    def _freeze_campaign_inputs(self) -> Path:
        assert self.pre_dir is not None and self.pre_workspace is not None
        frozen = self.pre_dir / "frozen-inputs"
        if frozen.exists():
            self._verify_frozen_inputs(frozen)
            return frozen
        temporary = self.pre_dir / f".frozen-inputs-{secrets.token_hex(6)}"
        temporary.mkdir()
        try:
            shutil.copy2(self.pre_workspace / "problem.md", temporary / "problem.md")
            shutil.copytree(self.pre_workspace / "references", temporary / "references")
            shutil.copytree(self.pre_workspace / "knowledge", temporary / "knowledge")
            retained = temporary / "pre-campaign"
            retained.mkdir()
            for name in (
                "research-decision.json",
                "research-result.json",
                "orchestration-plan.json",
            ):
                source = self.pre_dir / name
                if source.is_file():
                    shutil.copy2(source, retained / name)
            directive = self.pre_workspace / "campaign-directive.md"
            if directive.is_file():
                shutil.copy2(directive, retained / "campaign-directive.md")
            project_inputs = self.pre_workspace / "project-inputs"
            for item in self.project.inputs:
                self._copy_regular_source(
                    project_inputs / item.target, temporary / item.target
                )
            self._reject_snapshot_symlinks(temporary)
            artifacts = digest_tree(temporary)
            atomic_write_json(
                temporary / "manifest.json",
                {
                    "schema_version": 1,
                    "artifacts": [artifact.to_dict() for artifact in artifacts],
                },
            )
            try:
                os.replace(temporary, frozen)
            except FileExistsError:
                self._verify_frozen_inputs(frozen)
            descriptor = os.open(self.pre_dir, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        finally:
            if temporary.exists():
                shutil.rmtree(temporary)
        return frozen

    def _verify_frozen_inputs(self, frozen: Path) -> None:
        self._reject_snapshot_symlinks(frozen)
        try:
            manifest = json.loads(
                (frozen / "manifest.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError) as exc:
            raise RegimeError(f"cannot verify frozen campaign inputs: {exc}") from exc
        observed = [
            artifact.to_dict()
            for artifact in digest_tree(frozen, exclude={"manifest.json"})
        ]
        if (
            not isinstance(manifest, dict)
            or manifest.get("schema_version") != 1
            or manifest.get("artifacts") != observed
        ):
            raise RegimeError("frozen campaign inputs changed after planning")

    @staticmethod
    def _copy_regular_source(
        source: Path, destination: Path, *, excludes: tuple[str, ...] = ()
    ) -> None:
        if source.is_symlink():
            raise RegimeError(f"campaign input cannot be a symlink: {source}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        if source.is_file():
            shutil.copy2(source, destination)
            return
        if not source.is_dir():
            raise RegimeError(
                f"campaign input is not a regular file or directory: {source}"
            )

        def ignored(directory: str, names: list[str]) -> set[str]:
            relative = Path(directory).relative_to(source)
            return {
                name
                for name in names
                if path_is_excluded((relative / name).as_posix(), excludes)
            }

        shutil.copytree(source, destination, symlinks=True, ignore=ignored)

    @staticmethod
    def _reject_snapshot_symlinks(root: Path) -> None:
        symlinks = [path for path in root.rglob("*") if path.is_symlink()]
        if symlinks:
            raise RegimeError(f"campaign input contains a symlink: {symlinks[0]}")

    def _refresh_pre_workspace_references(self) -> None:
        assert self.pre_workspace is not None
        destination = self.pre_workspace / "references"
        if destination.exists():
            shutil.rmtree(destination)
        shutil.copytree(self.project.references_dir, destination)

    def _copy_knowledge_snapshot(self) -> None:
        assert self.pre_workspace is not None
        destination = self.pre_workspace / "knowledge"
        if destination.exists():
            shutil.rmtree(destination)
        shutil.copytree(self.project.knowledge_dir, destination)

    def _pre_state(self) -> dict[str, Any]:
        assert self.pre_dir is not None
        try:
            snapshot = load_state_snapshot(self.pre_dir)
        except JournalError as exc:
            raise RegimeError(f"cannot read pre-campaign state journal: {exc}") from exc
        value = snapshot.state
        if not isinstance(value, dict) or value.get("schema_version") != 1:
            raise RegimeError("pre-campaign state is malformed")
        state_path = self.pre_dir / "state.json"
        try:
            projection = json.loads(state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            projection = None
        if projection != value:
            atomic_write_json(state_path, value)
        return value

    def _save_pre_state(self, value: dict[str, Any]) -> None:
        assert self.pre_dir is not None
        status = value.get("status")
        reason = (
            f"regime:pre:{status}" if isinstance(status, str) else "regime:pre:update"
        )
        append_state_snapshot(self.pre_dir, value, reason=reason)
        atomic_write_json(self.pre_dir / "state.json", value)

    def _load_research_decision(self) -> ResearchDecision:
        assert self.pre_dir is not None
        try:
            value = json.loads(
                (self.pre_dir / "research-decision.json").read_text(encoding="utf-8")
            )
        except (OSError, json.JSONDecodeError) as exc:
            raise RegimeError(f"cannot reload research decision: {exc}") from exc
        return ResearchDecision.parse(value)

    def _load_research_result(self) -> ResearchResult | None:
        assert self.pre_dir is not None
        path = self.pre_dir / "research-result.json"
        if not path.is_file():
            return None
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise RegimeError(f"cannot reload research result: {exc}") from exc
        return ResearchResult.parse(value)

    def _emit(self, text: str) -> None:
        print(text, file=self.output, flush=True)


def choose_strategy(run_dir: Path, strategy_id: str) -> str:
    """Record an explicit user choice for an unresolved campaign."""

    run = run_dir.expanduser().resolve()
    with campaign_run_lock(run):
        return _choose_strategy_locked(run, strategy_id)


def _choose_strategy_locked(run: Path, strategy_id: str) -> str:
    state_path = run / "state.json"
    outcome_path = run / "outcome.json"
    permitted = frozenset(
        {
            "events.jsonl",
            "state.json",
            "strategy-selection.json",
            "next-campaign.md",
        }
    )
    try:
        state = load_state_snapshot(run).state
    except JournalError as exc:
        raise RegimeError(f"cannot read unresolved campaign: {exc}") from exc

    receipt = state.get("strategy_selection_receipt")
    if state.get("status") == "complete" and isinstance(receipt, dict):
        try:
            verify_evidence_for_repair(run, permitted_paths=permitted)
            message = _write_strategy_artifacts(run, receipt)
            atomic_write_json(state_path, state)
            refresh_campaign_evidence(run)
        except (OSError, TypeError, ValueError) as exc:
            raise RegimeError(f"cannot recover strategy selection: {exc}") from exc
        return message

    intent = state.get("strategy_selection_intent")
    if isinstance(intent, dict):
        retained_id = intent.get("strategy_id")
        if retained_id != strategy_id:
            raise RegimeError(
                f"strategy selection {retained_id!r} is already being committed"
            )
        try:
            verify_evidence_for_repair(run, permitted_paths=permitted)
        except (OSError, TypeError, ValueError) as exc:
            raise RegimeError(f"cannot recover strategy selection: {exc}") from exc
    else:
        try:
            verify_evidence_index(run)
        except (OSError, TypeError, ValueError) as exc:
            raise RegimeError(f"cannot verify unresolved campaign: {exc}") from exc
        if state.get("status") != "awaiting_strategy":
            raise RegimeError(
                "strategy selection requires an awaiting_strategy campaign"
            )
        try:
            outcome_value = json.loads(outcome_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise RegimeError(f"cannot read unresolved campaign: {exc}") from exc
        outcome = CampaignOutcome.parse(outcome_value)
        intent = _strategy_intent(outcome, strategy_id)
        state["strategy_selection_intent"] = intent
        append_state_snapshot(run, state, reason=f"strategy:intent:{strategy_id}")
        atomic_write_json(state_path, state)
        refresh_campaign_evidence(run)

    message = _write_strategy_artifacts(run, intent)
    refresh_campaign_evidence(run)
    state["status"] = "complete"
    state["strategy_selection"] = strategy_id
    state["strategy_selection_receipt"] = intent
    state.pop("strategy_selection_intent", None)
    state["completed_at"] = utc_now()
    append_state_snapshot(run, state, reason=f"strategy:receipt:{strategy_id}")
    atomic_write_json(state_path, state)
    refresh_campaign_evidence(run)
    return message


def _strategy_intent(outcome: CampaignOutcome, strategy_id: str) -> dict[str, object]:
    if strategy_id == "stop":
        return {
            "schema_version": 1,
            "strategy_id": strategy_id,
            "selection": {
                "schema_version": 1,
                "selected": None,
                "stopped": True,
                "selected_at": utc_now(),
            },
            "next_campaign": None,
            "message": "No successor strategy selected.",
        }
    selected = next(
        (item for item in outcome.strategies if item.strategy_id == strategy_id),
        None,
    )
    if selected is None:
        raise RegimeError(f"unknown strategy {strategy_id!r}")
    return {
        "schema_version": 1,
        "strategy_id": strategy_id,
        "selection": {
            "schema_version": 1,
            "selected": {
                "id": selected.strategy_id,
                "title": selected.title,
                "rationale": selected.rationale,
                "next_prompt": selected.next_prompt,
                "recommended": selected.recommended,
            },
            "stopped": False,
            "selected_at": utc_now(),
        },
        "next_campaign": selected.next_prompt.rstrip() + "\n",
        "message": f"Selected strategy: {selected.title}",
    }


def _write_strategy_artifacts(run: Path, intent: dict[str, object]) -> str:
    selection = intent.get("selection")
    next_campaign = intent.get("next_campaign")
    message = intent.get("message")
    if (
        not isinstance(selection, dict)
        or (next_campaign is not None and not isinstance(next_campaign, str))
        or not isinstance(message, str)
    ):
        raise RegimeError("retained strategy selection intent is malformed")
    if next_campaign is None:
        (run / "next-campaign.md").unlink(missing_ok=True)
    else:
        atomic_write_text(run / "next-campaign.md", next_campaign)
    atomic_write_json(run / "strategy-selection.json", selection)
    return message
