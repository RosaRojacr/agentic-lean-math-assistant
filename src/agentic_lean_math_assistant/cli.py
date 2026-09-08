"""One public CLI for Research, Build, review, gates, resume, and promotion."""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import NoReturn

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
    discover_project,
    follow_autorun_events,
    follow_autorun_output,
    follow_autorun_status,
    request_autorun_stop,
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
from .inspection import inspect_assurance, inspect_claim_ledgers
from .processes import stop_all_campaigns
from .project import ProjectSpec
from .proof_attempt import run_candidate_proof_gate
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
    autorun_stop = subparsers.add_parser(
        "autorun-stop", help="request a running autorun controller to stop"
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
            result = run_candidate_proof_gate(
                args.project,
                candidate_path=args.candidate,
                contract_path=args.contract,
                trusted_declaration=args.trusted_declaration,
                allowed_axioms=tuple(args.allowed_axiom),
                lake=args.lake,
                timeout=args.timeout,
                run_dir=receipt.parent,
            )
            atomic_write_json(receipt, result.to_dict())
            print(f"proof attempt: {result.status}")
            print(f"receipt: {receipt}")
            return 0 if result.passed else 1
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
        OSError,
        ValueError,
    ) as exc:
        _fail(parser, str(exc))


if __name__ == "__main__":
    raise SystemExit(main())
