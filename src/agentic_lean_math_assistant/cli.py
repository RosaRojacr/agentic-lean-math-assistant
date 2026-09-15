"""One public CLI for Research, Build, review, gates, resume, and promotion."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Any, NoReturn, cast

from . import __version__
from .artifacts import atomic_write_json
from .autonomy import (
    AutonomyError,
    AutonomyRunner,
    AutonomyRuntimeOptions,
    autonomy_status,
    record_autonomy_decision,
)
from .autorun import (
    AutoRunError,
    AutoRunRunner,
    conductor_claim_marker,
    discover_project,
    follow_autorun_events,
    follow_autorun_output,
    follow_autorun_status,
    request_autorun_stop,
    restore_autorun_workspace,
)
from .autorun import (
    add_arguments as add_autorun_arguments,
)
from .autorun import (
    autorun_status as read_autorun_status,
)
from .autorun import (
    options_from_args as autorun_options_from_args,
)
from .benchmark import (
    BenchmarkRuntime,
    BenchmarkSuite,
    resume_benchmark_suite,
    run_benchmark_suite,
)
from .config import CampaignSpec, ConfigurationError
from .features import FeatureRegistry
from .herdr import HerdrError
from .inspection import inspect_assurance, inspect_claim_ledgers
from .processes import stop_all_campaigns
from .project import ProjectSpec
from .proof_attempt import run_candidate_proof_gate
from .proof_builder import (
    ProofBuilderError,
    VerificationMode,
    build_proof_package,
    compare_proof_packages,
    discover_lean_declarations,
    format_proof_failure,
    initialize_proof_manifest,
    plan_proof_package,
    preflight_proof_package,
    preview_proof_package,
    proof_package_status,
    record_review_dispositions,
    resume_proof_package,
    verify_proof_package,
)
from .publication import plan_publication, publish_campaign
from .regime import (
    RegimeError,
    RegimeOptions,
    RegimeRunner,
    choose_strategy,
)
from .regression import (
    RegressionConfig,
    assess_regression,
    fit_regression,
    load_array,
)
from .runtime import (
    CampaignBuilder,
    CampaignOptions,
    CampaignRunError,
    approve_handoff,
    campaign_resolved_for_run,
    campaign_status,
    campaign_status_exit_code,
    replay_verifier_command,
    verify_campaign_bundle,
)
from .solve import SolveError, SolveSpec
from .solve_runner import SolveRunner, request_solve_stop, solve_status


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="agentic-lean-math-assistant",
        description="Run declarative Research and Build stage DAGs.",
    )
    parser.add_argument(
        "--version", action="version", version=f"%(prog)s {__version__}"
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    run = subparsers.add_parser("run", help="start a new campaign")
    run.add_argument("--campaign", type=Path, required=True)
    _runtime_arguments(run)

    regime_run = subparsers.add_parser(
        "regime-run", help="run the fixed research-plan-execute-assess regime"
    )
    regime_run.add_argument("--project", type=Path, required=True)
    regime_run.add_argument(
        "--missing-source-policy",
        choices=("checkpoint", "continue"),
        help="required operator choice before publication research",
    )
    _runtime_arguments(regime_run, include_runs=False)

    regime_resume = subparsers.add_parser(
        "regime-resume", help="resume a missing-source checkpoint"
    )
    regime_resume.add_argument("--project", type=Path, required=True)
    regime_resume.add_argument("--run", type=Path, required=True)
    regime_resume.add_argument("--waive-missing-sources", action="store_true")
    _runtime_arguments(regime_resume, include_runs=False)

    choose = subparsers.add_parser(
        "choose-strategy", help="record the user's post-campaign strategy choice"
    )
    choose.add_argument("--run", type=Path, required=True)
    choose.add_argument("--strategy", required=True, metavar="ID|stop")
    autorun = subparsers.add_parser(
        "autorun", help="run a persistent self-prompting project conductor"
    )
    add_autorun_arguments(autorun)
    autorun_report = subparsers.add_parser(
        "autorun-report",
        help="emit a claim bound to the active frozen conductor invocation",
    )
    autorun_report.add_argument("--request", type=Path, required=True)
    checkpoint = autorun_report.add_mutually_exclusive_group(required=True)
    checkpoint.add_argument("--checkpoint-id")
    checkpoint.add_argument("--no-checkpoint", action="store_true")
    autorun_report.add_argument(
        "--progress-class",
        choices=sorted({"incremental", "meaningful", "blocked", "complete"}),
        required=True,
    )
    autorun_report.add_argument("--summary", required=True)
    autorun_report.add_argument("--evidence", required=True)
    autorun_show = subparsers.add_parser(
        "autorun-status", help="show retained autorun controller state"
    )
    autorun_show.add_argument("--session", type=Path, required=True)
    autorun_show.add_argument("--follow", action="store_true")
    autorun_show.add_argument("--interval", type=float, default=1.0)
    autorun_show.add_argument("--recap-minutes", type=float, default=10.0)
    autorun_output = subparsers.add_parser(
        "autorun-output", help="follow output from the active autorun round"
    )
    autorun_output.add_argument("--session", type=Path, required=True)
    autorun_output.add_argument("--interval", type=float, default=1.0)
    autorun_events = subparsers.add_parser(
        "autorun-events", help="follow raw autorun events for the active round"
    )
    autorun_events.add_argument("--session", type=Path, required=True)
    autorun_events.add_argument("--interval", type=float, default=1.0)
    autorun_workspace = subparsers.add_parser(
        "autorun-workspace",
        help="create or refresh a live Herdr workspace for an autorun session",
    )
    autorun_workspace.add_argument("--project", type=Path)
    autorun_workspace.add_argument("--session", type=Path)
    autorun_workspace.add_argument("--label", required=True)
    autorun_workspace.add_argument("--herdr", default="herdr")
    autorun_workspace.add_argument("--no-focus", action="store_true")
    autorun_stop = subparsers.add_parser(
        "autorun-stop",
        help="request a durable stop and return its one-use resume token",
    )
    autorun_stop.add_argument("--session", type=Path, required=True)
    autonomy_run = subparsers.add_parser(
        "autonomy-run",
        help="run bounded evidence-driven campaigns until the success contract passes",
    )
    autonomy_run.add_argument("--project", type=Path, required=True)
    _autonomy_arguments(autonomy_run)
    autonomy_resume = subparsers.add_parser(
        "autonomy-resume", help="resume a retained autonomous campaign session"
    )
    autonomy_resume.add_argument("--project", type=Path, required=True)
    autonomy_resume.add_argument("--session", type=Path, required=True)
    autonomy_resume.add_argument("--waive-missing-sources", action="store_true")
    _autonomy_arguments(autonomy_resume)
    autonomy_decide = subparsers.add_parser(
        "autonomy-decide", help="submit a decision to a waiting autonomous session"
    )
    autonomy_decide.add_argument("--session", type=Path, required=True)
    autonomy_decide.add_argument(
        "--strategy", required=True, metavar="ID|recommended|stop"
    )
    autonomy_show = subparsers.add_parser(
        "autonomy-status", help="show verified autonomous session state"
    )
    autonomy_show.add_argument("--session", type=Path, required=True)
    solve = subparsers.add_parser(
        "solve", help="solve and publish a mathematical problem folder"
    )
    _solve_arguments(solve, include_restart=True)
    solve_resume = subparsers.add_parser(
        "solve-resume", help="resume a retained folder solve"
    )
    _solve_arguments(solve_resume, include_restart=False)
    solve_show = subparsers.add_parser(
        "solve-status", help="show retained folder solve state"
    )
    solve_show.add_argument("folder", type=Path)
    solve_stop = subparsers.add_parser(
        "solve-stop", help="request a durable stop at the next safe boundary"
    )
    solve_stop.add_argument("folder", type=Path)
    resume = subparsers.add_parser("resume", help="resume a retained campaign")
    resume.add_argument("--run", type=Path, required=True)
    resume.add_argument(
        "--retry-failed",
        action="store_true",
        help="retry failed stages and invalidate their descendants",
    )
    resume.add_argument(
        "--retry-stage",
        action="append",
        default=[],
        metavar="STAGE",
        help="retry one stage and invalidate its descendants; repeatable",
    )
    resume.add_argument(
        "--feedback",
        action="append",
        default=[],
        metavar="TEXT",
        help="feedback supplied to each explicitly retried stage; repeatable",
    )
    _runtime_arguments(resume, include_runs=False)

    validate = subparsers.add_parser(
        "validate", help="validate a campaign and features"
    )
    validate.add_argument("--campaign", type=Path, required=True)

    approve = subparsers.add_parser("approve", help="approve a retained typed handoff")
    approve.add_argument("--run", type=Path, required=True)

    verify = subparsers.add_parser("verify", help="verify a retained evidence bundle")
    verify.add_argument("--run", type=Path, required=True)

    status = subparsers.add_parser("status", help="show authoritative run status")
    status.add_argument("--run", type=Path, required=True)
    dashboard = subparsers.add_parser(
        "dashboard", help="show live stage, target, and limitation status"
    )
    dashboard.add_argument("--run", type=Path, required=True)
    dashboard.add_argument("--watch", action="store_true")
    dashboard.add_argument("--interval", type=float, default=1.0)
    replay = subparsers.add_parser(
        "replay", help="rerun one frozen allowlisted verifier command"
    )
    replay.add_argument("--run", type=Path, required=True)
    replay.add_argument("--stage", required=True)
    claims = subparsers.add_parser(
        "claims", help="inspect verifier-gated claims and target closure"
    )
    claims.add_argument("--run", type=Path, required=True)
    audit = subparsers.add_parser(
        "audit", help="report passed trust boundaries and remaining assurance gaps"
    )
    audit.add_argument("--run", type=Path, required=True)

    publish_plan = subparsers.add_parser(
        "publish-plan", help="print the complete immutable publication plan"
    )
    publish_plan.add_argument("--run", type=Path, required=True)

    publish = subparsers.add_parser(
        "publish", help="publish an approved artifact from a verified complete run"
    )
    publish.add_argument("--run", type=Path, required=True)
    publish.add_argument("--approve-digest", required=True, metavar="SHA256")

    regression_assess = subparsers.add_parser(
        "regression-assess",
        help="assess retained numeric arrays before fitting",
    )
    _regression_array_arguments(regression_assess)
    regression_assess.add_argument("--output", type=Path, required=True)
    regression_fit = subparsers.add_parser(
        "regression-fit",
        help="fit a bounded held-out regression with a linear baseline",
    )
    _regression_array_arguments(regression_fit)
    regression_fit.add_argument("--config", type=Path, required=True)
    regression_fit.add_argument("--output", type=Path, required=True)
    subparsers.add_parser("features", help="list registered feature IDs")
    benchmark = subparsers.add_parser(
        "benchmark", help="run a blind autonomous-outcome benchmark suite"
    )
    benchmark_source = benchmark.add_mutually_exclusive_group(required=True)
    benchmark_source.add_argument("--suite", type=Path)
    benchmark_source.add_argument(
        "--resume",
        type=Path,
        metavar="REPORT",
        help="resume a running schema-v2 report",
    )
    _runtime_arguments(benchmark, include_runs=False)
    proof_builder = subparsers.add_parser(
        "proof-builder",
        help="build, inspect, resume, and verify professor-facing Lean proof packages",
    )
    proof_commands = proof_builder.add_subparsers(
        dest="proof_builder_command", required=True
    )
    proof_init = proof_commands.add_parser(
        "init", help="create a reusable proof-package manifest template"
    )
    proof_init.add_argument("--manifest", type=Path, required=True)

    def add_model_options(command: argparse.ArgumentParser) -> None:
        command.add_argument("--author-model")
        command.add_argument("--semantic-review-model")
        command.add_argument(
            "--review-profile",
            choices=("strict", "standard", "economical"),
        )
        command.add_argument("--max-model-calls", type=int)

    proof_preflight = proof_commands.add_parser(
        "preflight", help="validate inputs, tools, models, and the Lean contract"
    )
    proof_preflight.add_argument("--manifest", type=Path, required=True)
    proof_preflight.add_argument("--omp")
    proof_preflight.add_argument("--lake", default="lake")
    proof_preflight.add_argument(
        "--no-lean", action="store_true", help="skip the temporary Lean contract gate"
    )
    proof_preflight.add_argument("--format", choices=("text", "json"), default="text")
    add_model_options(proof_preflight)

    proof_build = proof_commands.add_parser(
        "build", help="build a new immutable proof package"
    )
    proof_build.add_argument("--manifest", type=Path, required=True)
    proof_build.add_argument("--omp")
    proof_build.add_argument("--lake", default="lake")
    proof_build.add_argument(
        "--dry-run", action="store_true", help="print the execution plan without work"
    )
    proof_build.add_argument("--format", choices=("text", "json"), default="text")
    add_model_options(proof_build)

    proof_resume = proof_commands.add_parser(
        "resume", help="repair a failed retained proof package from a selected stage"
    )
    proof_resume.add_argument("--package", type=Path, required=True)
    proof_resume.add_argument("--feedback", action="append", default=[])
    proof_resume.add_argument(
        "--from",
        dest="from_stage",
        choices=(
            "lean-export",
            "explanation",
            "semantic-review",
            "pdf-render",
            "checksum-ledger",
        ),
        default="semantic-review",
    )
    proof_resume.add_argument("--omp")
    proof_resume.add_argument("--lake", default="lake")
    add_model_options(proof_resume)

    proof_review = proof_commands.add_parser(
        "review", help="disposition retained semantic-review findings"
    )
    proof_review.add_argument("--package", type=Path, required=True)
    proof_review.add_argument("--decision", action="append", default=[])

    proof_diff = proof_commands.add_parser(
        "diff", help="compare two proof packages semantically"
    )
    proof_diff.add_argument("left", type=Path)
    proof_diff.add_argument("right", type=Path)
    proof_diff.add_argument("--format", choices=("text", "json"), default="text")

    proof_declarations = proof_commands.add_parser(
        "declarations", help="list Lean declarations with types and collected axioms"
    )
    proof_declarations.add_argument("--manifest", type=Path, required=True)
    proof_declarations.add_argument("--lake", default="lake")
    proof_declarations.add_argument("--contains")
    proof_declarations.add_argument(
        "--format", choices=("text", "json"), default="text"
    )

    proof_preview = proof_commands.add_parser(
        "preview", help="render an explicitly unverified publication preview"
    )
    proof_preview.add_argument("--manifest", type=Path, required=True)
    proof_preview.add_argument("--output", type=Path)

    proof_verify = proof_commands.add_parser(
        "verify", help="verify package checksums and/or rerun its pinned Lean build"
    )
    proof_verify.add_argument("--package", type=Path, required=True)
    proof_verify.add_argument("--lake", default="lake")
    verification_mode = proof_verify.add_mutually_exclusive_group()
    verification_mode.add_argument("--checksums-only", action="store_true")
    verification_mode.add_argument("--lean-only", action="store_true")
    proof_verify.add_argument("--no-network", action="store_true")
    proof_verify.add_argument("--format", choices=("text", "json"), default="text")
    proof_verify.add_argument("--quiet", action="store_true")

    proof_status = proof_commands.add_parser(
        "status", help="show proof-package health and provenance"
    )
    proof_status.add_argument("--package", type=Path, required=True)
    proof_status.add_argument("--format", choices=("text", "json"), default="text")

    proof_attempt = subparsers.add_parser(
        "proof-attempt",
        help="verify one retained Lean candidate against a trusted typed contract",
    )
    proof_attempt.add_argument("--project", type=Path, required=True)
    proof_attempt.add_argument("--candidate", type=Path, required=True)
    proof_attempt.add_argument("--contract", type=Path, required=True)
    proof_attempt.add_argument("--trusted-declaration", required=True)
    proof_attempt.add_argument("--allowed-axiom", action="append", default=[])
    proof_attempt.add_argument("--lake", default="lake")
    proof_attempt.add_argument("--timeout", type=float, default=180.0)
    proof_attempt.add_argument("--receipt", type=Path, required=True)
    subparsers.add_parser("stop-all", help="stop every active campaign")
    return parser


def _regression_array_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--features", type=Path, required=True)
    parser.add_argument("--targets", type=Path, required=True)
    parser.add_argument("--feature-key")
    parser.add_argument("--target-key")
    parser.add_argument("--feature-skip-rows", type=int, default=0)
    parser.add_argument("--target-skip-rows", type=int, default=0)


def _runtime_arguments(
    parser: argparse.ArgumentParser,
    *,
    include_runs: bool = True,
    omp_default: str | None = "omp",
) -> None:
    if include_runs:
        parser.add_argument("--runs-dir", type=Path)
    parser.add_argument("--herdr", default="herdr")
    parser.add_argument("--omp", default=omp_default)
    parser.add_argument("--lake", default="lake")
    visibility = parser.add_mutually_exclusive_group()
    visibility.add_argument("--visible", action="store_true", help="focus Herdr panes")
    visibility.add_argument(
        "--headless", "--no-focus", dest="headless", action="store_true"
    )
    parser.add_argument(
        "--keep-workspace",
        "--keep-herdr",
        dest="keep_workspace",
        action="store_true",
        help="leave the visible Herdr workspace open after completion",
    )


def _autonomy_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--profile")
    parser.add_argument("--approval-timeout-minutes", type=int)
    afk = parser.add_mutually_exclusive_group()
    afk.add_argument("--afk-autonomy", dest="afk_autonomy", action="store_true")
    afk.add_argument("--no-afk-autonomy", dest="afk_autonomy", action="store_false")
    parser.set_defaults(afk_autonomy=None)
    parser.add_argument("--max-campaigns", type=int)
    _runtime_arguments(parser, include_runs=False, omp_default=None)


def _solve_arguments(parser: argparse.ArgumentParser, *, include_restart: bool) -> None:
    parser.add_argument("folder", type=Path)
    parser.add_argument("--problem", type=Path)
    parser.add_argument("--runtime-limit")
    parser.add_argument("--predicted-runtime-limit")
    parser.add_argument("--forecast-interval")
    parser.add_argument("--forecast-percentile", type=int, choices=(50, 80, 95))
    parser.add_argument("--max-model-calls", type=int)
    parser.add_argument("--profile", choices=("economical", "balanced", "max"))
    parser.add_argument("--proof-author-model")
    parser.add_argument("--proof-reviewer-model")
    parser.add_argument("--feedback", action="append", default=[])
    parser.add_argument("--headless", action="store_true")
    web = parser.add_mutually_exclusive_group()
    web.add_argument("--allow-web", dest="allow_web", action="store_true")
    web.add_argument("--no-web", dest="allow_web", action="store_false")
    parser.set_defaults(allow_web=None)
    sandbox = parser.add_mutually_exclusive_group()
    sandbox.add_argument("--sandbox", dest="sandbox", action="store_true")
    sandbox.add_argument("--no-sandbox", dest="sandbox", action="store_false")
    parser.set_defaults(sandbox=None)
    publication = parser.add_mutually_exclusive_group()
    publication.add_argument(
        "--publish-inconclusive", dest="publish_inconclusive", action="store_true"
    )
    publication.add_argument(
        "--skip-inconclusive", dest="publish_inconclusive", action="store_false"
    )
    parser.set_defaults(publish_inconclusive=None)
    if include_restart:
        parser.add_argument("--restart", action="store_true")
    parser.add_argument("--omp", default="omp")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--pandoc", default="pandoc")
    parser.add_argument("--chromium")


def _options(args: argparse.Namespace) -> CampaignOptions:
    return CampaignOptions(
        herdr=args.herdr,
        omp=args.omp,
        lake=args.lake,
        runs_dir=getattr(args, "runs_dir", None),
        focus=not args.headless,
        close_herdr=not args.keep_workspace,
        retry_failed=getattr(args, "retry_failed", False),
        retry_stages=tuple(getattr(args, "retry_stage", ())),
        retry_feedback=tuple(getattr(args, "feedback", ())),
    )


def _fail(parser: argparse.ArgumentParser, message: str) -> NoReturn:
    parser.error(message)


def _source_policy(value: str | None) -> str:
    if value is not None:
        return value
    if not sys.stdin.isatty():
        raise ConfigurationError(
            "choose --missing-source-policy checkpoint or continue before research"
        )
    print("If an important publication is inaccessible, what should the campaign do?")
    print("  1. Checkpoint and ask you to provide it [Recommended]")
    print("  2. Continue automatically and retain the limitation")
    while True:
        choice = input("Choose 1 or 2: ").strip()
        if choice in ("1", ""):
            return "checkpoint"
        if choice == "2":
            return "continue"
        print("Enter 1 or 2.")


def _regime_options(args: argparse.Namespace, policy: str) -> RegimeOptions:
    return RegimeOptions(
        missing_source_policy=policy,  # type: ignore[arg-type]
        omp=args.omp,
        herdr=args.herdr,
        lake=args.lake,
        focus=not args.headless,
        close_herdr=not args.keep_workspace,
        waive_missing_sources=getattr(args, "waive_missing_sources", False),
    )


def _autonomy_options(args: argparse.Namespace) -> AutonomyRuntimeOptions:
    return AutonomyRuntimeOptions(
        profile=args.profile,
        approval_timeout_minutes=args.approval_timeout_minutes,
        afk_autonomy=args.afk_autonomy,
        max_campaigns=args.max_campaigns,
        omp=args.omp,
        herdr=args.herdr,
        lake=args.lake,
        focus=not args.headless,
        close_herdr=not args.keep_workspace,
        waive_missing_sources=getattr(args, "waive_missing_sources", False),
    )


def _autonomy_exit_code(status: object) -> int:
    if status == "solved":
        return 0
    if status in {"awaiting_approval", "checkpoint"}:
        return 3
    return 1


def _reported_status(run_dir: Path) -> str:
    run = run_dir.expanduser().resolve()
    if (run / "state.json").is_file():
        return campaign_status(run)
    pre_state_path = run / "pre-campaign" / "state.json"
    try:
        value = json.loads(pre_state_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RegimeError(f"cannot read campaign status: {exc}") from exc
    status = value.get("status")
    if not isinstance(status, str):
        raise RegimeError("pre-campaign status is malformed")
    return status


def _reported_status_exit_code(status: str) -> int:
    if status == "awaiting_sources":
        return 3
    return campaign_status_exit_code(status)


def _interactive_strategy_choice(run_dir: Path) -> None:
    if campaign_status(run_dir) != "awaiting_strategy" or not sys.stdin.isatty():
        return
    outcome = json.loads((run_dir / "outcome.json").read_text(encoding="utf-8"))
    strategies = outcome.get("strategies", [])
    recommended = next(
        (
            item.get("id")
            for item in strategies
            if isinstance(item, dict) and item.get("recommended") is True
        ),
        None,
    )
    choice = input(
        "Select a strategy ID, press Enter for the recommended strategy, "
        "or enter 'stop': "
    ).strip()
    selected = choice or recommended
    if not isinstance(selected, str):
        raise RegimeError("the outcome has no recommended strategy")
    print(choose_strategy(run_dir, selected))


def _dashboard_snapshot(run_dir: Path) -> tuple[str, str]:
    run = run_dir.expanduser().resolve()
    state = json.loads((run / "state.json").read_text(encoding="utf-8"))
    stages = state.get("stages")
    if not isinstance(stages, dict):
        raise ConfigurationError("retained dashboard stage state is malformed")
    rows = [
        f"{stage_id}: {item.get('status')} | {item.get('summary') or '-'}"
        for stage_id, item in stages.items()
        if isinstance(stage_id, str) and isinstance(item, dict)
    ]
    status = str(state.get("status"))
    lines = [
        f"campaign: {state.get('campaign_id')} [{status}]",
        f"run: {run}",
        *rows,
    ]
    if (run / "evidence.json").is_file() and status != "running":
        assurance = inspect_assurance(run)
        obligations = assurance.get("verification_obligations", {})
        limitations = assurance.get("limitations", [])
        if isinstance(obligations, dict):
            lines.append(
                "obligations: "
                f"{sum(item.get('status') in {'verified', 'rejected'} for item in obligations.get('items', []) if isinstance(item, dict))}/"
                f"{obligations.get('configured', 0)} disposed"
            )
        if isinstance(limitations, list):
            lines.append(f"limitations: {len(limitations)}")
            lines.extend(f"- {item}" for item in limitations if isinstance(item, str))
    return status, "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        if args.command == "solve-status":
            print(json.dumps(solve_status(args.folder), indent=2, sort_keys=True))
            return 0
        if args.command == "solve-stop":
            print(f"solve stop requested: {request_solve_stop(args.folder)}")
            return 0
        if args.command in {"solve", "solve-resume"}:
            solve_spec = SolveSpec.load(
                args.folder,
                problem=args.problem,
                runtime_limit=args.runtime_limit,
                predicted_runtime_limit=args.predicted_runtime_limit,
                forecast_interval=args.forecast_interval,
                forecast_percentile=args.forecast_percentile,
                max_model_calls=args.max_model_calls,
                profile=args.profile,
                proof_author_model=args.proof_author_model,
                proof_reviewer_model=args.proof_reviewer_model,
                restart=getattr(args, "restart", False),
                publish_inconclusive=args.publish_inconclusive,
                headless=args.headless,
                allow_web=args.allow_web,
                sandbox=args.sandbox,
                feedback=tuple(args.feedback),
            )
            solve_result = SolveRunner(
                solve_spec,
                omp=args.omp,
                lake=args.lake,
                pandoc=args.pandoc,
                chromium=args.chromium,
            ).run()
            print(f"solve status: {solve_result.status}")
            print(f"mathematical status: {solve_result.mathematical_status}")
            print(f"publication status: {solve_result.publication_status}")
            print(f"state directory: {solve_result.state_root}")
            if solve_result.proof_package is not None:
                print(f"proof package: {solve_result.proof_package}")
            if solve_result.error:
                print(f"detail: {solve_result.error}")
            if solve_result.status == "complete":
                return 0
            if solve_result.status == "needs_input":
                return 3
            return 1
        if args.command == "proof-builder":
            command = args.proof_builder_command
            if command == "init":
                manifest = initialize_proof_manifest(args.manifest)
                print(f"proof-builder manifest: {manifest}")
                return 0
            if command in {"preflight", "build"}:
                model_options = {
                    "author_model": args.author_model,
                    "reviewer_model": args.semantic_review_model,
                    "review_profile": args.review_profile,
                    "max_model_calls": args.max_model_calls,
                }
                if command == "preflight":
                    preflight_report = cast(
                        dict[str, Any],
                        preflight_proof_package(
                            args.manifest,
                            omp=args.omp,
                            lake=args.lake,
                            run_lean=not args.no_lean,
                            **model_options,
                        ),
                    )
                    if args.format == "json":
                        print(json.dumps(preflight_report, indent=2, sort_keys=True))
                    else:
                        print("proof-builder preflight: passed")
                        for check in cast(
                            list[dict[str, Any]], preflight_report["checks"]
                        ):
                            print(
                                f"  {check['name']}: "
                                f"{'passed' if check['passed'] else 'failed'} "
                                f"({check['detail']})"
                            )
                    return 0
                if args.dry_run:
                    proof_plan = cast(
                        dict[str, Any],
                        plan_proof_package(args.manifest, **model_options),
                    )
                    if args.format == "json":
                        print(json.dumps(proof_plan, indent=2, sort_keys=True))
                    else:
                        print(f"proof-builder plan: {proof_plan['output']}")
                        print(
                            f"  modules={len(proof_plan['module_closure'])} "
                            f"declarations={proof_plan['declaration_count']} "
                            f"model_calls<={proof_plan['limits']['planned_model_calls']}"
                        )
                        print("  stages: " + " -> ".join(proof_plan["stages"]))
                    return 0
                package_result = build_proof_package(
                    args.manifest,
                    omp=args.omp,
                    lake=args.lake,
                    **model_options,
                )
                print(f"proof package status: {package_result.status}")
                print(f"proof package: {package_result.package_dir}")
                failure = format_proof_failure(package_result)
                if failure:
                    print(failure)
                return 0 if package_result.accepted else 1
            if command == "resume":
                package_result = resume_proof_package(
                    args.package,
                    omp=args.omp,
                    lake=args.lake,
                    feedback=tuple(args.feedback),
                    from_stage=args.from_stage,
                    author_model=args.author_model,
                    reviewer_model=args.semantic_review_model,
                    review_profile=args.review_profile,
                    max_model_calls=args.max_model_calls,
                )
                print(f"proof package status: {package_result.status}")
                print(f"proof package: {package_result.package_dir}")
                failure = format_proof_failure(package_result)
                if failure:
                    print(failure)
                return 0 if package_result.accepted else 1
            if command == "review":
                sidecar = record_review_dispositions(
                    args.package, decisions=tuple(args.decision)
                )
                print(f"review dispositions: {sidecar}")
                return 0
            if command == "diff":
                comparison = cast(
                    dict[str, Any], compare_proof_packages(args.left, args.right)
                )
                if args.format == "json":
                    print(json.dumps(comparison, indent=2, sort_keys=True))
                else:
                    label = "different" if comparison["different"] else "equivalent"
                    declarations = comparison["declarations"]
                    print(f"proof packages: {label}")
                    print(
                        f"  declarations: +{len(declarations['added'])} "
                        f"-{len(declarations['removed'])} "
                        f"changed={len(declarations['changed'])}"
                    )
                    print(
                        f"  roots={comparison['root_contract_changed']} "
                        f"axioms={comparison['allowed_axioms_changed']} "
                        f"models={comparison['models_changed']}"
                    )
                return 1 if comparison["different"] else 0
            if command == "declarations":
                declarations = cast(
                    list[dict[str, Any]],
                    discover_lean_declarations(
                        args.manifest, lake=args.lake, contains=args.contains
                    ),
                )
                if args.format == "json":
                    print(json.dumps(declarations, indent=2, sort_keys=True))
                else:
                    for declaration in declarations:
                        print(
                            f"{declaration['declaration']} : {declaration['type']} "
                            f"[axioms: {', '.join(declaration['axioms'])}]"
                        )
                return 0
            if command == "preview":
                preview = preview_proof_package(
                    args.manifest,
                    output=args.output,
                )
                print(f"unverified proof-package preview: {preview}")
                return 0
            if command == "verify":
                mode: VerificationMode = (
                    "checksums"
                    if args.checksums_only
                    else "lean"
                    if args.lean_only
                    else "full"
                )
                count = verify_proof_package(
                    args.package,
                    lake=args.lake,
                    mode=mode,
                    no_network=args.no_network,
                )
                verification_result = {
                    "status": "verified",
                    "mode": mode,
                    "retained_files": count,
                    "no_network": args.no_network,
                }
                if not args.quiet:
                    if args.format == "json":
                        print(json.dumps(verification_result, indent=2, sort_keys=True))
                    elif mode == "lean":
                        print("proof package Lean rebuild verified")
                    else:
                        print(f"proof package verified: {count} retained files")
                return 0
            if command == "status":
                package_health = cast(
                    dict[str, Any], proof_package_status(args.package)
                )
                if args.format == "json":
                    print(json.dumps(package_health, indent=2, sort_keys=True))
                else:
                    print(f"Package status: {package_health['status']}")
                    print(f"Ledger: {package_health['ledger']}")
                    print(f"Retained files: {package_health['retained_files']}")
                    print(f"Revision attempts: {package_health['revision_attempts']}")
                    reviewer = package_health["models"].get(
                        "semantic_reviewer", "unknown"
                    )
                    reviewer_route = (
                        reviewer.get("route", "unknown")
                        if isinstance(reviewer, dict)
                        else reviewer
                    )
                    print(f"Semantic reviewer: {reviewer_route}")
                return (
                    0
                    if package_health["status"] == "verified"
                    and package_health["ledger"] == "valid"
                    else 1
                )
            raise AssertionError(f"unhandled proof-builder command: {command}")
        if args.command in {"regression-assess", "regression-fit"}:
            features = load_array(
                args.features,
                key=args.feature_key,
                skip_rows=args.feature_skip_rows,
            )
            targets = load_array(
                args.targets,
                key=args.target_key,
                skip_rows=args.target_skip_rows,
            )
            if args.command == "regression-assess":
                assessment = assess_regression(features, targets)
                atomic_write_json(
                    args.output.expanduser().resolve(), assessment.to_dict()
                )
                print(f"regression recommended: {str(assessment.recommended).lower()}")
                print(f"assessment: {args.output.expanduser().resolve()}")
                return 0 if assessment.recommended else 3
            receipt = fit_regression(
                features,
                targets,
                RegressionConfig.load(args.config),
                args.output,
            )
            print(f"regression receipt: {receipt}")
            return 0
        if args.command == "proof-attempt":
            receipt = args.receipt.expanduser().resolve()
            proof_result = run_candidate_proof_gate(
                args.project,
                candidate_path=args.candidate,
                contract_path=args.contract,
                trusted_declaration=args.trusted_declaration,
                allowed_axioms=tuple(args.allowed_axiom),
                lake=args.lake,
                timeout=args.timeout,
                run_dir=receipt.parent,
            )
            atomic_write_json(receipt, proof_result.to_dict())
            print(f"proof attempt: {proof_result.status}")
            print(f"receipt: {receipt}")
            return 0 if proof_result.passed else 1
        if args.command == "features":
            for feature_id in FeatureRegistry().feature_ids:
                print(feature_id)
            return 0
        if args.command == "stop-all":
            report = stop_all_campaigns()
            print(json.dumps(report.to_dict(), sort_keys=True))
            return 0 if report.ok else 1
        if args.command == "benchmark":
            benchmark_runtime = BenchmarkRuntime(
                omp=args.omp,
                herdr=args.herdr,
                lake=args.lake,
                focus=not args.headless,
                close_herdr=not args.keep_workspace,
            )
            report_path = (
                resume_benchmark_suite(args.resume, benchmark_runtime)
                if args.resume is not None
                else run_benchmark_suite(
                    BenchmarkSuite.load(args.suite), benchmark_runtime
                )
            )
            report = json.loads(report_path.read_text(encoding="utf-8"))
            summary = report["summary"]
            print(
                "benchmark: "
                f"{summary['passed']}/{summary['cases']} passed; "
                f"{summary['errors']} case errors; "
                f"{summary['false_closures']} false closures"
            )
            print(f"report: {report_path}")
            return 0 if summary["accepted"] else 1
        if args.command == "autorun-report":
            marker = conductor_claim_marker(
                args.request,
                checkpoint_id=None if args.no_checkpoint else args.checkpoint_id,
                progress_class=args.progress_class,
                summary=args.summary,
                evidence=args.evidence,
            )
            print(marker)
            return 0
        if args.command == "autorun-workspace":
            project = ProjectSpec.load(args.project or discover_project())
            workspace = restore_autorun_workspace(
                project,
                label=args.label,
                session_dir=args.session,
                herdr_executable=args.herdr,
                focus=not args.no_focus,
            )
            print(f"autorun workspace: {workspace.workspace_id}")
            return 0
        if args.command == "autorun-output":
            follow_autorun_output(args.session, interval_seconds=args.interval)
            return 0
        if args.command == "autorun-events":
            follow_autorun_events(args.session, interval_seconds=args.interval)
            return 0
        if args.command == "autorun-stop":
            print(request_autorun_stop(args.session))
            return 0
        if args.command == "autorun-status":
            if args.follow:
                follow_autorun_status(
                    args.session,
                    interval_seconds=args.interval,
                    recap_interval_seconds=args.recap_minutes * 60,
                    persistent=True,
                )
                return 0
            state = read_autorun_status(args.session)
            print(json.dumps(state, indent=2, sort_keys=True))
            return 0 if state.get("status") in {"running", "recovering"} else 1
        if args.command == "autorun":
            project = ProjectSpec.load(args.project or discover_project())
            session = AutoRunRunner(project, autorun_options_from_args(args)).run()
            state = read_autorun_status(session)
            print(f"autorun status: {state.get('status')}")
            print(f"session directory: {session}")
            return 0 if state.get("status") in {"stopped", "paused"} else 1
        if args.command == "autonomy-decide":
            print(record_autonomy_decision(args.session, args.strategy))
            return 0
        if args.command == "autonomy-status":
            state = autonomy_status(args.session)
            print(json.dumps(state, indent=2, sort_keys=True))
            return _autonomy_exit_code(state.get("status"))
        if args.command == "autonomy-run":
            project = ProjectSpec.load(args.project)
            session = AutonomyRunner(project, _autonomy_options(args)).run()
            state = autonomy_status(session)
            print(f"autonomy status: {state.get('status')}")
            print(f"session directory: {session}")
            return _autonomy_exit_code(state.get("status"))
        if args.command == "autonomy-resume":
            project = ProjectSpec.load(args.project)
            session = AutonomyRunner(project, _autonomy_options(args)).resume(
                args.session
            )
            state = autonomy_status(session)
            print(f"autonomy status: {state.get('status')}")
            print(f"session directory: {session}")
            return _autonomy_exit_code(state.get("status"))
        if args.command == "choose-strategy":
            print(choose_strategy(args.run, args.strategy))
            return 0
        if args.command == "regime-run":
            project = ProjectSpec.load(args.project)
            policy = _source_policy(args.missing_source_policy)
            run_dir = RegimeRunner(project, _regime_options(args, policy)).run()
            if (run_dir / "state.json").is_file():
                _interactive_strategy_choice(run_dir)
                status = campaign_status(run_dir)
                print(f"campaign status: {status}")
                print(f"run directory: {run_dir}")
                return campaign_status_exit_code(status)
            print("campaign status: awaiting_sources")
            print(f"run directory: {run_dir}")
            return 3
        if args.command == "regime-resume":
            project = ProjectSpec.load(args.project)
            pre_state = json.loads(
                (args.run / "pre-campaign" / "state.json").read_text(encoding="utf-8")
            )
            policy = pre_state.get("missing_source_policy")
            if policy not in ("checkpoint", "continue"):
                raise RegimeError("retained missing-source policy is invalid")
            run_dir = RegimeRunner(project, _regime_options(args, policy)).resume(
                args.run
            )
            if not (run_dir / "state.json").is_file():
                print("campaign status: awaiting_sources")
                print(f"run directory: {run_dir}")
                return 3
            _interactive_strategy_choice(run_dir)
            status = campaign_status(run_dir)
            print(f"campaign status: {status}")
            print(f"run directory: {run_dir}")
            return campaign_status_exit_code(status)
        if args.command == "claims":
            claim_report = inspect_claim_ledgers(args.run)
            print(json.dumps(claim_report, indent=2, sort_keys=True))
            summary = claim_report["target_summary"]
            assert isinstance(summary, dict)
            required = summary.get("required")
            verified = summary.get("verified")
            return 0 if required == verified else 1
        if args.command == "audit":
            assurance = inspect_assurance(args.run)
            print(json.dumps(assurance, indent=2, sort_keys=True))
            return 0
        if args.command == "dashboard":
            if args.interval <= 0:
                raise ConfigurationError("dashboard interval must be positive")
            while True:
                status, rendered = _dashboard_snapshot(args.run)
                print(rendered)
                if not args.watch or status not in {"running"}:
                    return _reported_status_exit_code(status)
                print("---")
                time.sleep(args.interval)
        if args.command == "replay":
            receipt = replay_verifier_command(args.run, args.stage)
            print(f"verifier replay passed: {receipt}")
            return 0
        if args.command == "status":
            status = _reported_status(args.run)
            print(f"campaign status: {status}")
            print(f"run directory: {args.run.expanduser().resolve()}")
            if (args.run / "state.json").is_file() and (
                args.run / "configuration" / "features.json"
            ).is_file():
                claim_report = inspect_claim_ledgers(args.run)
                summary = claim_report["target_summary"]
                assert isinstance(summary, dict)
                if summary.get("required"):
                    print(
                        "claim targets: "
                        f"{summary.get('verified')}/{summary.get('required')} verified; "
                        f"{summary.get('rejected')} rejected; "
                        f"{summary.get('blocked')} blocked"
                    )
                    assurance = inspect_assurance(args.run)
                    limitations = assurance.get("limitations", [])
                    obligations = assurance.get("verification_obligations", {})
                    if isinstance(obligations, dict) and obligations.get("configured"):
                        print(
                            "verification obligations: "
                            f"{sum(item.get('status') in {'verified', 'rejected'} for item in obligations.get('items', []) if isinstance(item, dict))}/"
                            f"{obligations.get('configured')} disposed"
                        )
                    if isinstance(limitations, list) and limitations:
                        print(f"limitations: {len(limitations)}")
                        for limitation in limitations:
                            print(f"- {limitation}")
            return _reported_status_exit_code(status)
        if args.command == "publish-plan":
            plan = plan_publication(args.run)
            print(json.dumps(plan.to_dict(), indent=2, sort_keys=True))
            return 0
        if args.command == "publish":
            plan = publish_campaign(args.run, args.approve_digest)
            print(f"published sha256: {plan.digest}")
            print(f"publication destination: {plan.destination}")
            return 0
        if args.command == "verify":
            count = verify_campaign_bundle(args.run)
            print(f"verified: {count} artifacts")
            return 0
        if args.command == "approve":
            digest = approve_handoff(args.run)
            print(f"approved handoff sha256: {digest}")
            return 0
        if args.command == "validate":
            campaign = CampaignSpec.load(args.campaign)
            FeatureRegistry().validate(campaign)
            print(
                f"valid: {campaign.campaign_id}; {len(campaign.stages)} stages; "
                f"features={','.join(sorted({stage.feature for stage in campaign.stages}))}"
            )
            return 0
        if args.command == "run":
            campaign = CampaignSpec.load(args.campaign)
            run_dir = CampaignBuilder(campaign, options=_options(args)).run()
        elif args.command == "resume":
            resolved = campaign_resolved_for_run(args.run)
            campaign = CampaignSpec.load_resolved(resolved)
            run_dir = CampaignBuilder(
                campaign,
                options=_options(args),
                run_dir=args.run,
            ).resume()
        else:
            raise AssertionError(f"unhandled command: {args.command}")
        status = campaign_status(run_dir)
        print(f"campaign status: {status}")
        print(f"run directory: {run_dir}")
        return campaign_status_exit_code(status)
    except (
        AutoRunError,
        AutonomyError,
        ConfigurationError,
        CampaignRunError,
        RegimeError,
        HerdrError,
        ProofBuilderError,
        SolveError,
        OSError,
        ValueError,
    ) as exc:
        _fail(parser, str(exc))


if __name__ == "__main__":
    raise SystemExit(main())
