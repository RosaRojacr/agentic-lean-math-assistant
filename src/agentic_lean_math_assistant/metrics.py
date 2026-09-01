"""Deterministic compute-consumption and evidence-yield accounting."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .artifacts import atomic_write_json, utc_now
from .models import CampaignOutcome, OrchestrationPlan
from .project import ProjectSpec


@dataclass(frozen=True, slots=True)
class InvocationMetric:
    role_id: str
    attempt: int
    phase: str
    reasoning_class: str
    model: str | None
    thinking: str | None
    status: str
    duration_seconds: float
    invocation_count: int
    output_bytes: int
    request: str
    receipt: str | None

    def to_dict(self) -> dict[str, object]:
        return {
            "role_id": self.role_id,
            "attempt": self.attempt,
            "phase": self.phase,
            "reasoning_class": self.reasoning_class,
            "model": self.model,
            "thinking": self.thinking,
            "status": self.status,
            "duration_seconds": self.duration_seconds,
            "invocation_count": self.invocation_count,
            "output_bytes": self.output_bytes,
            "request": self.request,
            "receipt": self.receipt,
        }


def _object(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def _retained_path(path: Path, run_dir: Path) -> str:
    try:
        return path.resolve().relative_to(run_dir.resolve()).as_posix()
    except ValueError:
        return str(path.resolve())


def _request_paths(run_dir: Path) -> tuple[Path, ...]:
    paths = {
        *run_dir.glob("agents/*/*/attempt-*-request.json"),
        *run_dir.glob("pre-campaign/roles/*/*/request.json"),
    }
    return tuple(sorted(path for path in paths if path.is_file()))


def collect_compute_metrics(
    run_dir: Path, plan: OrchestrationPlan
) -> tuple[InvocationMetric, ...]:
    run = run_dir.expanduser().resolve()
    tasks = plan.by_id
    metrics: list[InvocationMetric] = []
    for request_path in _request_paths(run):
        request = _object(request_path)
        if request is None:
            continue
        role_id = request.get("role_id")
        attempt = request.get("attempt")
        if (
            not isinstance(role_id, str)
            or isinstance(attempt, bool)
            or not isinstance(attempt, int)
        ):
            continue
        receipt_value = request.get("receipt")
        receipt_path = (
            Path(receipt_value).expanduser().resolve()
            if isinstance(receipt_value, str)
            else None
        )
        receipt = _object(receipt_path) if receipt_path is not None else None
        invocations = receipt.get("invocations", []) if receipt is not None else []
        if not isinstance(invocations, list):
            invocations = []
        duration = sum(
            float(item.get("duration_seconds", 0.0))
            for item in invocations
            if isinstance(item, dict)
            and isinstance(item.get("duration_seconds"), int | float)
            and not isinstance(item.get("duration_seconds"), bool)
        )
        output_value = request.get("output")
        output_path = (
            Path(output_value).expanduser().resolve()
            if isinstance(output_value, str)
            else None
        )
        output_bytes = (
            output_path.stat().st_size
            if output_path is not None and output_path.is_file()
            else 0
        )
        task = tasks.get(role_id)
        metrics.append(
            InvocationMetric(
                role_id=role_id,
                attempt=attempt,
                phase=task.phase if task is not None else "meta",
                reasoning_class=(
                    task.reasoning_class if task is not None else "controller"
                ),
                model=request.get("model")
                if isinstance(request.get("model"), str)
                else None,
                thinking=request.get("thinking")
                if isinstance(request.get("thinking"), str)
                else None,
                status=(
                    str(receipt.get("status", "missing"))
                    if receipt is not None
                    else "missing"
                ),
                duration_seconds=round(duration, 3),
                invocation_count=len(invocations),
                output_bytes=output_bytes,
                request=_retained_path(request_path, run),
                receipt=(
                    _retained_path(receipt_path, run)
                    if receipt_path is not None
                    else None
                ),
            )
        )
    return tuple(metrics)


def write_compute_ledger(
    run_dir: Path,
    plan: OrchestrationPlan,
    project: ProjectSpec,
    outcome: CampaignOutcome | None = None,
) -> Path:
    """Write one reproducible aggregate without trusting model self-reporting."""
    run = run_dir.expanduser().resolve()
    metrics = collect_compute_metrics(run, plan)
    phase_seconds = {
        phase: round(
            sum(item.duration_seconds for item in metrics if item.phase == phase), 3
        )
        for phase in ("pilot", "research", "formalization", "meta")
    }
    phase_limits = {
        "pilot": project.pilot_agent_seconds,
        "research": project.research_agent_seconds,
        "formalization": project.formalization_agent_seconds,
    }
    dispositions = outcome.obligation_dispositions if outcome is not None else ()
    disposed = sum(item.status in {"verified", "rejected"} for item in dispositions)
    agent_seconds = round(sum(item.duration_seconds for item in metrics), 3)
    agent_hours = agent_seconds / 3600
    yield_per_hour = round(disposed / agent_hours, 6) if agent_hours else None
    novelty_records = len(tuple(run.glob("agents/*/*/attempt-*-novelty.json")))
    destination = run / "compute-ledger.json"
    atomic_write_json(
        destination,
        {
            "schema_version": 1,
            "generated_at": utc_now(),
            "campaign_id": project.project_id,
            "budget": {
                "phase_agent_seconds": phase_limits,
                "max_invocation_attempts": project.max_attempts_total,
                "max_invention_tasks": project.max_invention_tasks,
            },
            "consumption": {
                "agent_seconds": agent_seconds,
                "phase_agent_seconds": phase_seconds,
                "runner_attempts": len(metrics),
                "omp_invocations": sum(item.invocation_count for item in metrics),
                "output_bytes": sum(item.output_bytes for item in metrics),
                "novelty_declarations": novelty_records,
            },
            "yield": {
                "obligations_configured": len(plan.obligations),
                "obligations_disposed": disposed,
                "knowledge_promotions": (
                    len(outcome.knowledge_promotions) if outcome is not None else 0
                ),
                "disposed_obligations_per_agent_hour": yield_per_hour,
            },
            "attempts": [item.to_dict() for item in metrics],
        },
    )
    return destination
