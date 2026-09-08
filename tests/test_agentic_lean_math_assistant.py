from __future__ import annotations

import errno
import hashlib
import io
import json
import os
import signal
import subprocess
import sys
import time
from dataclasses import replace
from pathlib import Path
from tempfile import NamedTemporaryFile
from types import SimpleNamespace

import pytest

import agentic_lean_math_assistant.config as campaign_config
import agentic_lean_math_assistant.features as campaign_features
import agentic_lean_math_assistant.processes as campaign_processes
import agentic_lean_math_assistant.publication as campaign_publish_module
import agentic_lean_math_assistant.runtime as campaign_runtime
from agentic_lean_math_assistant import process_registry
from agentic_lean_math_assistant.agent_runner import _invoke, _StreamingRedactor
from agentic_lean_math_assistant.artifacts import (
    digest_file,
    digest_tree,
    verify_evidence_index,
)
from agentic_lean_math_assistant.cli import main as campaign_main
from agentic_lean_math_assistant.command import run_captured_command
from agentic_lean_math_assistant.config import (
    CampaignSpec,
    ConfigurationError,
    ExecutionSpec,
)
from agentic_lean_math_assistant.features import (
    FeatureRegistry,
    LeanContractConfig,
    LeanSubstitutionConfig,
    _matching_lean_axiom_report,
    _resolve_substitutions,
)
from agentic_lean_math_assistant.herdr import HerdrClient, HerdrError
from agentic_lean_math_assistant.inspection import (
    inspect_assurance,
    inspect_claim_ledgers,
)
from agentic_lean_math_assistant.journal import (
    JournalError,
    append_state_snapshot,
    load_state_snapshot,
)
from agentic_lean_math_assistant.lean import run_proof_gate
from agentic_lean_math_assistant.process_registry import (
    RegisteredRunProcess,
    register_run_process,
    registered_run_processes,
    registered_run_units,
    unregister_run_unit,
)
from agentic_lean_math_assistant.processes import (
    register_campaign,
    register_workspace,
    stop_all_campaigns,
    terminate_run_processes,
)
from agentic_lean_math_assistant.publication import plan_publication, publish_campaign
from agentic_lean_math_assistant.runtime import (
    CampaignBuilder,
    CampaignOptions,
    CampaignRunError,
    approve_handoff,
    campaign_resolved_for_run,
    campaign_run_lock,
    refresh_campaign_evidence,
    replay_verifier_command,
    verify_campaign_bundle,
)
from agentic_lean_math_assistant.sandbox import (
    SandboxError,
    prepare_sandbox,
    workspace_size_exceeds,
)
from agentic_lean_math_assistant.terminal_status import PaneHeartbeat

ROOT = Path(__file__).parents[1]
FAKE_HERDR = ROOT / "tests" / "fake_herdr.py"


@pytest.fixture(autouse=True)
def _allow_fake_campaign_environment(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    fake_names = (
        "FAKE_CAMPAIGN_BLANK_INVOCATIONS",
        "FAKE_CAMPAIGN_BLANK_EXIT_CODE",
        "FAKE_CAMPAIGN_PARTIAL_OUTPUT",
        "FAKE_CAMPAIGN_ESCAPE_VERIFIER",
        "FAKE_CAMPAIGN_INVALID_HANDOFF_ONCE",
        "FAKE_CAMPAIGN_MUTATE_DEPENDENCY",
        "FAKE_LAKE_REQUIRE_READY",
        "FAKE_CAMPAIGN_MUTATE_VERIFIER",
        "FAKE_CAMPAIGN_OMP_COUNTER",
        "FAKE_CAMPAIGN_REJECT_CLAIM",
        "FAKE_CAMPAIGN_REVISE",
        "FAKE_CAMPAIGN_SEMANTIC_MISMATCH",
        "FAKE_CAMPAIGN_STALE_HANDOFF_RETRY",
    )
    monkeypatch.setattr(
        campaign_config,
        "_DEFAULT_ENVIRONMENT_ALLOW",
        (*campaign_config._DEFAULT_ENVIRONMENT_ALLOW, *fake_names),
    )


def _executable(path: Path, source: str) -> Path:
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)
    return path


def _fake_omp(path: Path) -> Path:
    return _executable(
        path,
        r"""#!/usr/bin/env python3
import json
import os
import pathlib
import re
import sys

prompt_path = next(value[1:] for value in sys.argv if value.startswith("@"))
prompt = pathlib.Path(prompt_path).read_text(encoding="utf-8")
stage = re.search(r"- Stage: `([^`]+)`", prompt).group(1)
attempt = int(re.search(r"- Attempt: `(\d+)`", prompt).group(1))
counter_value = os.environ.get("FAKE_CAMPAIGN_OMP_COUNTER")
if counter_value:
    counter = pathlib.Path(counter_value)
    invocation = int(counter.read_text(encoding="utf-8")) + 1 if counter.exists() else 1
    counter.write_text(str(invocation), encoding="utf-8")
    blank_invocations = int(os.environ.get("FAKE_CAMPAIGN_BLANK_INVOCATIONS", "0"))
    if invocation <= blank_invocations:
        partial_value = os.environ.get("FAKE_CAMPAIGN_PARTIAL_OUTPUT")
        if partial_value:
            partial = pathlib.Path(partial_value)
            partial.parent.mkdir(parents=True, exist_ok=True)
            partial.write_text("useful partial output\n", encoding="utf-8")
        print("   ")
        raise SystemExit(int(os.environ.get("FAKE_CAMPAIGN_BLANK_EXIT_CODE", "0")))
handoff_match = re.search(r"Write `([^`]+)` as strict JSON", prompt)
if handoff_match and "`claim-proposals-v1` requires" in prompt:
    handoff = pathlib.Path(handoff_match.group(1))
    handoff.parent.mkdir(parents=True, exist_ok=True)
    handoff.write_text(json.dumps({
        "schema_version": 1,
        "claims": [{
            "id": "fixture_claim",
            "kind": "theorem",
            "statement": "The fixture theorem holds.",
            "scope": "For the retained fixture.",
            "proof": "The fixture premise directly establishes the conclusion.",
            "depends_on": [],
            "target": "fixture_goal",
            "limitations": ["The global theorem is outside the retained fixture scope."],
        }],
    }), encoding="utf-8")
if handoff_match and "`claim-verdicts-v1` requires" in prompt:
    if os.environ.get("FAKE_CAMPAIGN_MUTATE_DEPENDENCY") == "1":
        dependency = re.search(r"- `(/[^`\n]*proposals\.json)`", prompt)
        if dependency is None:
            raise RuntimeError("proposal dependency path not found")
        pathlib.Path(dependency.group(1)).write_text(
            json.dumps({"tampered_attempt": attempt}), encoding="utf-8"
        )
    if os.environ.get("FAKE_CAMPAIGN_ESCAPE_VERIFIER") == "1":
        dependency = re.search(r"- `(/[^`\n]*proposals\.json)`", prompt)
        if dependency is None:
            raise RuntimeError("proposal dependency path not found")
        canonical = pathlib.Path(dependency.group(1)).parents[3] / "workspace/input.txt"
        canonical.write_text(
            f"escaped verifier attempt {attempt}\n", encoding="utf-8"
        )
    if os.environ.get("FAKE_CAMPAIGN_MUTATE_VERIFIER") == "1":
        pathlib.Path("input.txt").write_text("tampered by verifier\n", encoding="utf-8")
    handoff = pathlib.Path(handoff_match.group(1))
    handoff.parent.mkdir(parents=True, exist_ok=True)
    reject = os.environ.get("FAKE_CAMPAIGN_REJECT_CLAIM") == "1"
    handoff.write_text(json.dumps({
        "schema_version": 1,
        "decisions": [{
            "claim": "fixture_claim",
            "decision": "reject" if reject else "accept",
            "reason": "A deliberate fixture rejection." if reject else "Checked independently.",
            "critical_errors": ["Fixture error."] if reject else [],
            "gaps": [],
        }],
    }), encoding="utf-8")
if handoff_match and "`semantic-review-v1` requires" in prompt:
    handoff = pathlib.Path(handoff_match.group(1))
    handoff.parent.mkdir(parents=True, exist_ok=True)
    mismatch = os.environ.get("FAKE_CAMPAIGN_SEMANTIC_MISMATCH") == "1"
    handoff.write_text(json.dumps({
        "schema_version": 1,
        "declaration": "Fixture.main_theorem",
        "informal_statement": "Every retained fixture satisfies the theorem.",
        "relation": "conditional_fragment" if mismatch else "equivalent",
        "added_hypotheses": ["Adds an unstated regularity hypothesis."] if mismatch else [],
        "omitted_hypotheses": [],
        "quantifier_issues": [],
        "domain_issues": [],
        "boundary_issues": [],
        "symbol_mismatches": [],
        "critical_errors": [],
        "reason": "The formal theorem is conditional." if mismatch else "The statements match.",
    }), encoding="utf-8")
if stage in {"synthesizer", "formalization_synthesizer"}:
    match = re.search(r"Write `([^`]+)` as strict JSON", prompt)
    inventory_match = re.search(
        r"Read `([^`]+)` before writing the handoff", prompt
    )
    if (
        os.environ.get("FAKE_CAMPAIGN_STALE_HANDOFF_RETRY") == "1"
        and attempt == 2
    ):
        match = None
    if match and inventory_match:
        inventory = json.loads(
            pathlib.Path(inventory_match.group(1)).read_text(encoding="utf-8")
        )
        source = inventory["workspace_sources"][0]
        digest = source["sha256"]
        if (
            os.environ.get("FAKE_CAMPAIGN_INVALID_HANDOFF_ONCE") == "1"
            and attempt == 1
        ):
            digest = "not-recorded"
        handoff = pathlib.Path(match.group(1))
        handoff.parent.mkdir(parents=True, exist_ok=True)
        handoff.write_text(json.dumps({
            "schema_version": 1,
            "goal": "Prove the configured external contract.",
            "scope": "The explicit test model only.",
            "sources": [{
                "id": "paper",
                "locator": source["path"],
                "sha256": digest,
                "usage": "Defines the test claim.",
                "confidence": "exact test fixture",
            }],
            "claims": [{
                "id": "claim",
                "statement": "The fixture claim holds.",
                "status": "verified",
                "sources": ["paper"],
                "build_obligation": "Encode the claim.",
            }],
            "definitions": [{
                "name": "Fixture",
                "description": "The fixture object.",
                "domain": "Unit test domain.",
                "source_claims": ["claim"],
            }],
            "obligations": [{
                "id": "build",
                "statement": "Build the fixture contract.",
                "dependencies": ["claim"],
                "acceptance": "The deterministic gate passes.",
            }],
            "limitations": [],
            "recommended_stages": ["build"],
        }), encoding="utf-8")
    if (
        os.environ.get("FAKE_CAMPAIGN_STALE_HANDOFF_RETRY") == "1"
        and attempt == 1
    ):
        print(f"# {stage}\n\nFailed after writing attempt {attempt} handoff.")
        raise SystemExit(1)
if stage == "final_reviewer":
    revise = os.environ.get("FAKE_CAMPAIGN_REVISE") == "1" and attempt == 1
    print(json.dumps({
        "decision": "revise" if revise else "accept",
        "reason": "one correction" if revise else "accepted",
        "target_stages": ["source_analyst"] if revise else [],
        "required_changes": ["add locator"] if revise else [],
    }))
    raise SystemExit(0)
if "## Required continuation decision" in prompt:
    print(json.dumps({
        "schema_version": 1,
        "decision": "stop",
        "reason": "The pilot produced no qualifying new evidence.",
        "evidence": [],
    }))
    raise SystemExit(0)
if stage == "baseline_prover" and attempt >= 2:
    (pathlib.Path.cwd() / "proof" / "ready").write_text("ready\n", encoding="utf-8")
print(f"# {stage}\n\nCompleted attempt {attempt}.")
""",
    )


def _fake_lake(path: Path) -> Path:
    return _executable(
        path,
        r"""#!/usr/bin/env python3
import json
import os
import pathlib
import sys

if sys.argv[1:] == ["build"]:
    if os.environ.get("FAKE_LAKE_REQUIRE_READY") == "1" and not pathlib.Path("ready").is_file():
        print("proof is not ready", file=sys.stderr)
        raise SystemExit(7)
    print("Build completed successfully.")
elif sys.argv[1:] == ["env", "which", "lean"]:
    print(pathlib.Path(sys.argv[0]).resolve())
elif "--run" in sys.argv:
    separator = sys.argv.index("--")
    for declaration in sys.argv[separator + 1:]:
        print(json.dumps({
            "declaration": declaration,
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        }))
else:
    pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"fake olean")
""",
    )


def _base_files(tmp_path: Path) -> None:
    (tmp_path / "input.txt").write_text("fixture\n", encoding="utf-8")
    (tmp_path / "campaign.md").write_text(
        "Execute the fixture campaign.\n", encoding="utf-8"
    )
    (tmp_path / "role.md").write_text("Perform the assigned stage.\n", encoding="utf-8")


def _command_manifest(
    tmp_path: Path,
    script: str,
    *,
    arguments: tuple[str, ...] = (),
    execution: str = "",
    stage_config: str = "",
) -> Path:
    _base_files(tmp_path)
    manifest = tmp_path / "command-campaign.toml"
    argv = json.dumps([sys.executable, "-c", script, *arguments])
    manifest.write_text(
        f"""schema_version = 1
[campaign]
id = "sandbox-check"
title = "Sandbox Check"
instructions = "campaign.md"
runs_dir = "runs"
{execution}
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "check"
title = "Check"
mode = "build"
feature = "command"
depends_on = []
required = true
failure_policy = "abort"
[stages.config]
argv = {argv}
cwd = "."
timeout = 15
{stage_config}
""",
        encoding="utf-8",
    )
    return manifest


def _options(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    *,
    omp: Path | None = None,
    lake: Path | None = None,
    retry_failed: bool = False,
    retry_stages: tuple[str, ...] = (),
    retry_feedback: tuple[str, ...] = (),
) -> CampaignOptions:
    monkeypatch.setenv("FAKE_HERDR_STATE", str(tmp_path / "herdr.json"))
    return CampaignOptions(
        herdr=str(FAKE_HERDR),
        omp=str(omp or _fake_omp(tmp_path / "fake-omp")),
        lake=str(lake or _fake_lake(tmp_path / "fake-lake")),
        runs_dir=tmp_path / "runs",
        focus=False,
        close_herdr=True,
        output=io.StringIO(),
        retry_failed=retry_failed,
        retry_stages=retry_stages,
        retry_feedback=retry_feedback,
    )


def test_execution_policy_rejects_unallowlisted_secret(
    tmp_path: Path,
) -> None:
    manifest = _command_manifest(
        tmp_path,
        "print('unused')",
        execution=(
            "[execution]\n"
            'environment_allow = ["PATH"]\n'
            'secret_environment = ["SECRET_SETTING"]'
        ),
    )

    with pytest.raises(
        ConfigurationError,
        match="secret_environment must also be allowed",
    ):
        CampaignSpec.load(manifest)


def test_execution_policy_rejects_secrets_for_untrusted_sandbox(
    tmp_path: Path,
) -> None:
    manifest = _command_manifest(
        tmp_path,
        "print('unused')",
        execution=(
            "[execution]\n"
            'environment_allow = ["PATH", "SECRET_SETTING"]\n'
            'secret_environment = ["SECRET_SETTING"]'
        ),
    )

    with pytest.raises(
        ConfigurationError,
        match="secret_environment requires sandbox=false",
    ):
        CampaignSpec.load(manifest)


@pytest.mark.parametrize(
    ("script", "stage_config"),
    [
        ("print('retained-literal')", ""),
        ("print('unused')", 'environment = { PUBLIC_VALUE = "retained-literal" }'),
        ("print('unused')", 'environment = { SECRET_SETTING = "retained-literal" }'),
    ],
)
def test_command_config_rejects_embedded_declared_secret_value(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    script: str,
    stage_config: str,
) -> None:
    monkeypatch.setenv("SECRET_SETTING", "retained-literal")
    manifest = _command_manifest(
        tmp_path,
        script,
        execution=(
            "[execution]\n"
            "sandbox = false\n"
            'environment_allow = ["PATH", "SECRET_SETTING"]\n'
            'secret_environment = ["SECRET_SETTING"]'
        ),
        stage_config=stage_config,
    )

    with pytest.raises(ConfigurationError, match="embeds a declared secret value"):
        CampaignSpec.load(manifest)


def test_schema_rejects_research_dependency_on_build(tmp_path: Path) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "bad-order"
title = "Bad Order"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "build"
title = "Build"
mode = "build"
feature = "command"
depends_on = []
[stages.config]
argv = ["true"]
cwd = ".work"
[[stages]]
id = "research"
title = "Research"
mode = "research"
feature = "command"
depends_on = ["build"]
[stages.config]
argv = ["true"]
cwd = ".work"
""",
        encoding="utf-8",
    )
    with pytest.raises(ConfigurationError, match="cannot depend on a build stage"):
        CampaignSpec.load(manifest)


def test_registry_rejects_unknown_feature(tmp_path: Path) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "unknown-feature"
title = "Unknown Feature"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "stage"
title = "Stage"
mode = "research"
feature = "missing"
depends_on = []
[stages.config]
""",
        encoding="utf-8",
    )
    with pytest.raises(ConfigurationError, match="unknown campaign feature"):
        FeatureRegistry().validate(CampaignSpec.load(manifest))


@pytest.mark.parametrize(
    (
        "empty_output_retries",
        "blank_invocations",
        "blank_exit_code",
        "run_status",
        "statuses",
        "exit_codes",
    ),
    (
        (None, 1, 0, "incomplete", ("failed",), (0,)),
        (2, 1, 0, "complete", ("failed", "succeeded"), (0, 0)),
        (2, 99, 0, "incomplete", ("failed", "failed", "failed"), (0, 0, 0)),
        (2, 1, 1, "complete", ("failed", "succeeded"), (1, 0)),
    ),
)
def test_agent_empty_output_retries_are_bounded_and_durable(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    empty_output_retries: int | None,
    blank_invocations: int,
    blank_exit_code: int,
    run_status: str,
    statuses: tuple[str, ...],
    exit_codes: tuple[int, ...],
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    retry_config = (
        ""
        if empty_output_retries is None
        else f"empty_output_retries = {empty_output_retries}"
    )
    manifest.write_text(
        f"""schema_version = 1
[campaign]
id = "empty-output"
title = "Empty Output"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "analyst"
title = "Analyst"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read"]
max_time = 60
{retry_config}
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CAMPAIGN_OMP_COUNTER", ".omp-invocations")
    monkeypatch.setenv("FAKE_CAMPAIGN_BLANK_INVOCATIONS", str(blank_invocations))
    monkeypatch.setenv("FAKE_CAMPAIGN_BLANK_EXIT_CODE", str(blank_exit_code))
    if run_status != "complete":
        monkeypatch.setenv(
            "FAKE_CAMPAIGN_PARTIAL_OUTPUT",
            "agents/research/analyst/checkpoint.txt",
        )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    receipt = json.loads(
        (run_dir / "agents/research/analyst/attempt-01.json").read_text(
            encoding="utf-8"
        )
    )
    request = json.loads(
        (run_dir / "agents/research/analyst/attempt-01-request.json").read_text(
            encoding="utf-8"
        )
    )
    assert request["workspace_executables"] is True
    configured_retries = empty_output_retries or 0
    assert state["status"] == run_status
    counter = run_dir / "workspace/.omp-invocations"
    if run_status == "complete":
        assert counter.read_text(encoding="utf-8") == str(len(statuses))
    else:
        assert not counter.exists()
    assert request["empty_output_retries"] == configured_retries
    assert receipt["empty_output_retries"] == configured_retries
    assert tuple(item["ordinal"] for item in receipt["invocations"]) == tuple(
        range(1, len(statuses) + 1)
    )
    assert tuple(item["status"] for item in receipt["invocations"]) == statuses
    assert tuple(item["exit_code"] for item in receipt["invocations"]) == exit_codes
    assert all(
        isinstance(item["duration_seconds"], (int, float))
        and item["duration_seconds"] >= 0
        and item["stdout_truncated"] is False
        and item["stderr_truncated"] is False
        for item in receipt["invocations"]
    )
    if run_status == "complete":
        assert receipt["status"] == "succeeded"
        assert receipt["error"] is None
        assert (
            (run_dir / "agents/research/analyst/attempt-01.md")
            .read_text(encoding="utf-8")
            .startswith("# analyst")
        )
    else:
        assert receipt["status"] == "failed"
        assert receipt["error"] == "OMP exited with 0 and produced no output"
        partial = run_dir / "agents/research/analyst/attempt-01-partial/checkpoint.txt"
        assert partial.read_text(encoding="utf-8") == "useful partial output\n"
        partial_receipt = json.loads(
            (run_dir / "agents/research/analyst/attempt-01-partial.json").read_text(
                encoding="utf-8"
            )
        )
        assert partial_receipt["status"] == "partial"
        assert "checkpoint.txt" in partial_receipt["retained"]
        assert "failure.json" in partial_receipt["retained"]
        assert not (
            run_dir / "workspace/agents/research/analyst/checkpoint.txt"
        ).exists()
        assert (
            partial.relative_to(run_dir).as_posix()
            in state["stages"]["analyst"]["artifacts"]
        )


def test_agent_stage_retry_continues_from_partial_workspace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "partial-retry"
title = "Partial Retry"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "formalizer"
title = "Formalizer"
mode = "research"
feature = "agent"
depends_on = []
max_attempts = 2
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
empty_output_retries = 0
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CAMPAIGN_OMP_COUNTER", ".stage-invocations")
    monkeypatch.setenv("FAKE_CAMPAIGN_BLANK_INVOCATIONS", "1")
    monkeypatch.setenv(
        "FAKE_CAMPAIGN_PARTIAL_OUTPUT",
        "proof/PartialCheckpoint.lean",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    stage = state["stages"]["formalizer"]
    assert state["status"] == "complete"
    assert stage["status"] == "succeeded"
    assert stage["attempts"] == 2
    assert (run_dir / "workspace/proof/PartialCheckpoint.lean").read_text(
        encoding="utf-8"
    ) == "useful partial output\n"
    assert (run_dir / "workspace/.stage-invocations").read_text(encoding="utf-8") == "2"
    assert any(
        event["stage"] == "formalizer"
        and event["status"] == "retrying"
        and "continuing from partial workspace" in event["summary"]
        for event in state["events"]
    )
    assert not any((run_dir / "recovery").iterdir())


def test_failed_agent_retains_changed_workspace_before_rollback(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "partial-failure"
title = "Partial Failure"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "formalizer"
title = "Formalizer"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
empty_output_retries = 0
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CAMPAIGN_OMP_COUNTER", ".stage-invocations")
    monkeypatch.setenv("FAKE_CAMPAIGN_BLANK_INVOCATIONS", "1")
    monkeypatch.setenv(
        "FAKE_CAMPAIGN_PARTIAL_OUTPUT",
        "proof/PartialFailure.lean",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert not (run_dir / "workspace/proof/PartialFailure.lean").exists()
    retained = (
        run_dir
        / "agents/research/formalizer/attempt-01-workspace-partial/proof"
        / "PartialFailure.lean"
    )
    assert retained.read_text(encoding="utf-8") == "useful partial output\n"
    receipt = json.loads(
        (
            run_dir / "agents/research/formalizer/attempt-01-workspace-partial.json"
        ).read_text(encoding="utf-8")
    )
    assert receipt["status"] == "partial-workspace"
    assert "proof/PartialFailure.lean" in receipt["changed"]
    assert (
        retained.relative_to(run_dir).as_posix()
        in state["stages"]["formalizer"]["artifacts"]
    )


def test_workspace_checkpoint_excludes_regenerable_caches(tmp_path: Path) -> None:
    manifest = _command_manifest(tmp_path, "print('ok')")
    run_dir = tmp_path / "run"
    workspace = run_dir / "workspace"
    workspace.mkdir(parents=True)
    (workspace / "keep.txt").write_text("retained\n", encoding="utf-8")
    for relative in (
        ".cache/mathlib/cache",
        ".elan/toolchains/cache",
        ".lake/build/cache",
        "nested/.mypy_cache/cache",
        "nested/.pytest_cache/cache",
        "nested/.ruff_cache/cache",
        "nested/__pycache__/cache",
    ):
        path = workspace / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("regenerable\n", encoding="utf-8")

    builder = CampaignBuilder(CampaignSpec.load(manifest), run_dir=run_dir)
    builder.workspace = workspace
    builder._checkpoint_workspace("check", 1)

    checkpoint = builder._checkpoint_path("check", 1)
    assert (checkpoint / "keep.txt").read_text(encoding="utf-8") == "retained\n"
    assert {path.name for path in checkpoint.rglob("*")} == {"keep.txt", "nested"}

    (workspace / "keep.txt").write_text("mutated\n", encoding="utf-8")
    assert builder._restore_checkpoint("check", 1) is True
    assert (workspace / "keep.txt").read_text(encoding="utf-8") == "retained\n"
    assert {path.name for path in workspace.rglob("*")} == {"keep.txt", "nested"}


def test_continuation_gate_stops_unsupported_later_work(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "continuation-gate"
title = "Continuation Gate"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "pilot"
title = "Pilot"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read"]
[[stages]]
id = "pilot_gate"
title = "Pilot Gate"
mode = "research"
feature = "agent"
depends_on = ["pilot"]
required = false
failure_policy = "continue"
[stages.config]
instructions = "role.md"
tools = ["read"]
continuation_gate = true
[[stages]]
id = "expensive_research"
title = "Expensive Research"
mode = "research"
feature = "agent"
depends_on = ["pilot_gate"]
[stages.config]
instructions = "role.md"
tools = ["read"]
""",
        encoding="utf-8",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert state["stages"]["pilot"]["status"] == "succeeded"
    assert state["stages"]["pilot_gate"]["status"] == "failed"
    assert state["stages"]["expensive_research"]["status"] == "skipped"
    decision = json.loads(
        (run_dir / "agents/research/pilot_gate/attempt-01-continuation.json").read_text(
            encoding="utf-8"
        )
    )
    assert decision["decision"] == "stop"


@pytest.mark.parametrize("value", ("-1", "4", "true"))
def test_agent_config_rejects_invalid_empty_output_retries(
    tmp_path: Path, value: str
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        f"""schema_version = 1
[campaign]
id = "bad-empty-output-retries"
title = "Bad Empty Output Retries"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "analyst"
title = "Analyst"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read"]
empty_output_retries = {value}
""",
        encoding="utf-8",
    )
    with pytest.raises(ConfigurationError, match="empty_output_retries"):
        FeatureRegistry().validate(CampaignSpec.load(manifest))


def test_agent_timeout_terminates_descendant_processes(tmp_path: Path) -> None:
    marker = tmp_path / "orphan-finished"
    child = (
        "import pathlib,signal,sys,time; "
        "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(2); "
        "pathlib.Path(sys.argv[1]).write_text('orphan', encoding='utf-8')"
    )
    parent = (
        "import subprocess,sys,time; "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]]); "
        "time.sleep(60)"
    )

    result = _invoke(
        [sys.executable, "-c", parent, child, str(marker)],
        tmp_path,
        PaneHeartbeat("timeout-test", stream=io.StringIO()),
        -59,
    )

    assert result[0] == 124
    time.sleep(2.2)
    assert not marker.exists()


@pytest.mark.parametrize(
    "termination_signal",
    (signal.SIGHUP, signal.SIGQUIT, signal.SIGTERM),
)
def test_external_runner_termination_reaps_active_process_group(
    tmp_path: Path, termination_signal: signal.Signals
) -> None:
    marker = tmp_path / "escaped-child"
    ready = tmp_path / "inner-ready"
    secret_file = tmp_path / "interrupted-secret"
    secret = "interrupt-cleanup-secret"
    child = (
        "import pathlib,signal,sys,time; "
        "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(2); "
        "pathlib.Path(sys.argv[1]).write_text('escaped', encoding='utf-8')"
    )
    parent = (
        "import os,pathlib,subprocess,sys,time; "
        f"pathlib.Path({str(secret_file)!r}).write_text("
        "os.environ['RUNNER_SECRET'], encoding='utf-8'); "
        "pathlib.Path(sys.argv[3]).write_text('ready', encoding='utf-8'); "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]]); "
        "time.sleep(3)"
    )
    wrapper = tmp_path / "runner-wrapper.py"
    wrapper.write_text(
        "import io,sys\n"
        "from pathlib import Path\n"
        "from agentic_lean_math_assistant.agent_runner import _invoke\n"
        "from agentic_lean_math_assistant.config import ExecutionSpec\n"
        "from agentic_lean_math_assistant.terminal_status import PaneHeartbeat\n"
        f"_invoke([sys.executable, '-c', {parent!r}, {child!r}, "
        f"{str(marker)!r}, {str(ready)!r}], Path({str(tmp_path)!r}), "
        "PaneHeartbeat('signal-test', stream=io.StringIO()), 60, "
        "ExecutionSpec.from_table({'sandbox': False, "
        "'environment_allow': ['PATH', 'RUNNER_SECRET'], "
        "'secret_environment': ['RUNNER_SECRET']}, "
        f"Path({str(tmp_path)!r})))\n",
        encoding="utf-8",
    )
    runner = subprocess.Popen(
        [sys.executable, str(wrapper)],
        cwd=ROOT,
        env={**os.environ, "RUNNER_SECRET": secret},
    )
    deadline = time.monotonic() + 5
    while not ready.exists() and time.monotonic() < deadline:
        time.sleep(0.05)
    assert ready.exists()

    os.kill(runner.pid, termination_signal)
    runner.wait(timeout=5)
    time.sleep(3.2)

    assert not marker.exists()
    assert not secret_file.exists()


@pytest.mark.parametrize(
    "termination_signal",
    (signal.SIGHUP, signal.SIGQUIT, signal.SIGTERM),
)
def test_external_controller_termination_reaps_command_process_group(
    tmp_path: Path, termination_signal: signal.Signals
) -> None:
    _base_files(tmp_path)
    marker_name = "escaped-command-child"
    ready_name = "command-ready"
    child = (
        "import pathlib,signal,sys,time; "
        "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(2); "
        "pathlib.Path(sys.argv[1]).write_text('escaped', encoding='utf-8')"
    )
    parent = (
        "import pathlib,subprocess,sys,time; "
        "pathlib.Path(sys.argv[3]).write_text('ready', encoding='utf-8'); "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]]); "
        "time.sleep(3)"
    )
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "signal-containment"
title = "Signal Containment"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "command"
title = "Command"
mode = "build"
feature = "command"
depends_on = []
required = true
[stages.config]
argv = """
        + json.dumps([sys.executable, "-c", parent, child, marker_name, ready_name])
        + '\ncwd = "."\ntimeout = 60\n',
        encoding="utf-8",
    )
    wrapper = tmp_path / "controller-wrapper.py"
    wrapper.write_text(
        "import sys\n"
        "from pathlib import Path\n"
        "from agentic_lean_math_assistant.config import CampaignSpec\n"
        "from agentic_lean_math_assistant.runtime import CampaignBuilder, CampaignOptions\n"
        f"campaign = CampaignSpec.load(Path({str(manifest)!r}))\n"
        "CampaignBuilder(campaign, options=CampaignOptions("
        f"runs_dir=Path({str(tmp_path / 'runs')!r}), output=sys.stdout, "
        "focus=False, close_herdr=True)).run()\n",
        encoding="utf-8",
    )
    controller = subprocess.Popen([sys.executable, str(wrapper)], cwd=ROOT)
    deadline = time.monotonic() + 5
    ready: Path | None = None
    while ready is None and time.monotonic() < deadline:
        ready = next((tmp_path / "runs").glob(f"*/workspace/{ready_name}"), None)
        time.sleep(0.05)
    assert ready is not None

    os.kill(controller.pid, termination_signal)
    controller.wait(timeout=5)
    time.sleep(3.2)

    assert not ready.with_name(marker_name).exists()
    state_path = next((tmp_path / "runs").glob("*/state.json"))
    state = json.loads(state_path.read_text(encoding="utf-8"))
    assert state["status"] == "stopped"


@pytest.mark.parametrize("tamper_dependency", [False, True])
def test_resume_recovers_journal_workspace_and_rejects_dependency_corruption(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    tamper_dependency: bool,
) -> None:
    _base_files(tmp_path)
    ready = tmp_path / "crash-ready"
    child_pid = tmp_path / "child.pid"
    manifest = tmp_path / "crash-campaign.toml"
    script = (
        "import os,sys,time; from pathlib import Path; "
        "ready=Path(sys.argv[1]); pid=Path(sys.argv[2]); "
        "\nif not ready.exists():"
        "\n Path('partial.txt').write_text('partial', encoding='utf-8')"
        "\n pid.write_text(str(os.getpid()), encoding='utf-8')"
        "\n ready.write_text('ready', encoding='utf-8')"
        "\n time.sleep(60)"
        "\nelse:"
        "\n assert not Path('partial.txt').exists()"
        "\n Path('completed.txt').write_text('complete', encoding='utf-8')"
    )
    manifest.write_text(
        f"""schema_version = 1
[campaign]
id = "crash-recovery"
title = "Crash Recovery"
instructions = "campaign.md"
runs_dir = "runs"
[execution]
sandbox = false
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "upstream"
title = "Upstream"
mode = "build"
feature = "command"
depends_on = []
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; Path('upstream.txt').write_text('trusted', encoding='utf-8')"]
cwd = "."
[[stages]]
id = "mutator"
title = "Mutator"
mode = "build"
feature = "command"
depends_on = ["upstream"]
[stages.config]
argv = {json.dumps([sys.executable, "-c", script, str(ready), str(child_pid)])}
cwd = "."
timeout = 120
""",
        encoding="utf-8",
    )
    wrapper = tmp_path / "crash-controller.py"
    wrapper.write_text(
        "from pathlib import Path\n"
        "from agentic_lean_math_assistant.config import CampaignSpec\n"
        "from agentic_lean_math_assistant.runtime import CampaignBuilder, CampaignOptions\n"
        f"manifest=Path({str(manifest)!r})\n"
        "CampaignBuilder(CampaignSpec.load(manifest), "
        f"options=CampaignOptions(runs_dir=Path({str(tmp_path / 'runs')!r}), "
        "focus=False, close_herdr=True)).run()\n",
        encoding="utf-8",
    )
    controller = subprocess.Popen([sys.executable, str(wrapper)], cwd=ROOT)
    deadline = time.monotonic() + 10
    while not ready.exists() and time.monotonic() < deadline:
        time.sleep(0.05)
    assert ready.exists()
    run_dir = next((tmp_path / "runs").iterdir())
    assert (run_dir / "workspace/partial.txt").is_file()

    os.kill(controller.pid, signal.SIGKILL)
    controller.wait(timeout=5)
    stale_pid = int(child_pid.read_text(encoding="utf-8"))
    (run_dir / "state.json").write_text("{corrupt", encoding="utf-8")
    with (run_dir / "events.jsonl").open("ab") as stream:
        stream.write(b'{"truncated":')
    if tamper_dependency:
        dependency = run_dir / "stages/upstream/attempt-01.json"
        assert dependency.is_file()
        dependency.write_text("tampered dependency\n", encoding="utf-8")
        evidence_before = (run_dir / "evidence.json").read_bytes()
        state_before = (run_dir / "state.json").read_bytes()
        journal_before = (run_dir / "events.jsonl").read_bytes()
        try:
            with pytest.raises(
                CampaignRunError, match="cannot verify retained evidence before resume"
            ):
                CampaignBuilder(
                    CampaignSpec.load(manifest),
                    options=_options(tmp_path, monkeypatch),
                    run_dir=run_dir,
                ).resume()
        finally:
            try:
                os.kill(stale_pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        assert (run_dir / "evidence.json").read_bytes() == evidence_before
        assert (run_dir / "state.json").read_bytes() == state_before
        assert (run_dir / "events.jsonl").read_bytes() == journal_before
        return

    resumed = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
        run_dir=run_dir,
    ).resume()
    state = json.loads((resumed / "state.json").read_text(encoding="utf-8"))

    assert state["status"] == "complete"
    assert state["stages"]["mutator"]["attempts"] == 2
    assert state["stages"]["mutator"]["interruptions"] == 1
    assert not (resumed / "workspace/partial.txt").exists()
    assert (resumed / "workspace/completed.txt").read_text(encoding="utf-8") == (
        "complete"
    )
    assert any(event["status"] == "interrupted" for event in state["events"])
    assert any(event["status"] == "recovered" for event in state["events"])
    assert not (Path("/proc") / str(stale_pid)).exists()
    assert load_state_snapshot(resumed).state == state
    assert verify_campaign_bundle(resumed) > 0


def test_sigkill_recovery_stops_registered_sandbox_unit_identity_safely(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime_dir = tmp_path / "runtime"
    run_dir = tmp_path / "retained-run"
    wrong_run = tmp_path / "different-run"
    run_dir.mkdir()
    wrong_run.mkdir()
    state_path = tmp_path / "unit-state.json"
    ready = tmp_path / "unit-ready"
    marker = tmp_path / "unit-survived"
    unit = f"campaign-{os.getpid()}-0123456789ab.service"
    systemctl = _executable(
        tmp_path / "systemctl",
        "#!/usr/bin/env python3\n"
        "import json,os,signal,sys\n"
        f"path={str(state_path)!r}\n"
        "state=json.loads(open(path, encoding='utf-8').read())\n"
        "command=next(value for value in sys.argv if value in "
        "('kill','stop','is-active'))\n"
        "if command == 'kill' and state['active']:\n"
        " os.killpg(state['pid'], signal.SIGKILL)\n"
        " state['active']=False\n"
        " open(path, 'w', encoding='utf-8').write(json.dumps(state))\n"
        "raise SystemExit(0 if command != 'is-active' or state['active'] else 3)\n",
    )
    wrapper = tmp_path / "sandbox-controller.py"
    wrapper.write_text(
        "import json,subprocess,sys,time\n"
        "from pathlib import Path\n"
        "from agentic_lean_math_assistant.process_registry import register_run_unit\n"
        f"run=Path({str(run_dir)!r}); unit={unit!r}; "
        f"systemctl={str(systemctl)!r}\n"
        "register_run_unit(run, unit, systemctl)\n"
        f"child=subprocess.Popen([sys.executable, '-c', "
        f'"import time; from pathlib import Path; time.sleep(1.5); '
        f"Path({str(marker)!r}).write_text('survived', encoding='utf-8'); "
        'time.sleep(60)"], start_new_session=True)\n'
        f"Path({str(state_path)!r}).write_text("
        "json.dumps({'pid': child.pid, 'active': True}), encoding='utf-8')\n"
        f"Path({str(ready)!r}).write_text('ready', encoding='utf-8')\n"
        "time.sleep(60)\n",
        encoding="utf-8",
    )
    monkeypatch.setenv("AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(runtime_dir))
    controller = subprocess.Popen(
        [sys.executable, str(wrapper)],
        cwd=ROOT,
        env={**os.environ, "AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR": str(runtime_dir)},
    )
    deadline = time.monotonic() + 5
    while not ready.exists() and time.monotonic() < deadline:
        time.sleep(0.05)
    assert ready.exists()
    os.kill(controller.pid, signal.SIGKILL)
    controller.wait(timeout=5)

    assert not unregister_run_unit(wrong_run, unit, str(systemctl))
    assert len(registered_run_units(run_dir)) == 1
    report = terminate_run_processes(run_dir)
    time.sleep(1.7)

    assert report.ok
    assert not marker.exists()
    assert registered_run_units(run_dir) == ()


def test_event_journal_rejects_mid_chain_corruption(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _command_manifest(tmp_path, "print('ok')")
    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    path = run_dir / "events.jsonl"
    records = path.read_bytes().splitlines(keepends=True)
    first = bytearray(records[0])
    first[first.index(b"campaign initialized")] = ord("C")
    path.write_bytes(bytes(first) + b"".join(records[1:]))

    with pytest.raises(JournalError, match="invalid digest"):
        load_state_snapshot(run_dir)


def test_lean_gate_capture_is_bounded_and_hashes_full_output(
    tmp_path: Path,
) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    (project / "Main.lean").write_text(
        "theorem Fixture.main : True := by trivial\n", encoding="utf-8"
    )
    contract = project / "contract.lean"
    contract.write_text("import Main\n#print axioms Fixture.main\n", encoding="utf-8")
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import json
import pathlib
import sys
if sys.argv[1:] == ["build"]:
    sys.stdout.write("x" * (2 * 1024 * 1024))
elif sys.argv[1:] == ["env", "which", "lean"]:
    print(pathlib.Path(sys.argv[0]).resolve())
elif "--run" in sys.argv:
    separator = sys.argv.index("--")
    for declaration in sys.argv[separator + 1:]:
        print(json.dumps({"declaration": declaration, "axioms": []}))
else:
    pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"fake olean")
""",
    )

    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=(),
        lake=str(lake),
        timeout=10,
        execution=ExecutionSpec.from_table(None, tmp_path),
    )

    assert result.status == "passed"
    build_receipt = result.command_receipts[0]
    assert len(build_receipt.stdout) == 1024 * 1024
    assert (
        build_receipt.stdout_sha256
        == hashlib.sha256(b"x" * (2 * 1024 * 1024)).hexdigest()
    )
    assert build_receipt.sandbox["enabled"] is True
    assert len(build_receipt.sandbox["environment"]["sha256"]) == 64
    assert len(build_receipt.sandbox["toolchain"]["executable"]["sha256"]) == 64


def test_lean_gate_audits_unicode_declaration_names(tmp_path: Path) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    (project / "Main.lean").write_text(
        "theorem θstar_spec : True := by trivial\n", encoding="utf-8"
    )
    contract = project / "contract.lean"
    contract.write_text("import Main\n#print axioms θstar_spec\n", encoding="utf-8")
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import json
import pathlib
import sys
if sys.argv[1:] == ["build"]:
    pass
elif sys.argv[1:] == ["env", "which", "lean"]:
    print(pathlib.Path(sys.argv[0]).resolve())
elif "--run" in sys.argv:
    separator = sys.argv.index("--")
    for declaration in sys.argv[separator + 1:]:
        print(json.dumps({"declaration": declaration, "axioms": []}))
else:
    pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"fake olean")
""",
    )

    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=(),
        lake=str(lake),
        timeout=10,
        execution=ExecutionSpec.from_table(None, tmp_path),
    )

    assert result.status == "passed"
    assert [report.declaration for report in result.axiom_reports] == ["θstar_spec"]


def test_lean_metadata_substitution_rejects_command_and_forged_report(
    tmp_path: Path,
) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    contract = project / "contract.lean"
    contract.write_text(
        "import Main\n#check {{candidate}}\n#print axioms Fixture.main\n",
        encoding="utf-8",
    )
    payload = (
        "Fixture.main\n"
        "#print axioms Fixture.other\n"
        "#eval IO.println \"'Fixture.main' does not depend on any axioms\""
    )
    (tmp_path / "metadata.json").write_text(
        json.dumps({"candidate": payload}), encoding="utf-8"
    )
    config = LeanContractConfig(
        project="proof",
        contract="proof/contract.lean",
        substitutions=(
            LeanSubstitutionConfig(
                name="candidate",
                source="$metadata.candidate",
                kind="identifier",
            ),
        ),
        metadata="metadata.json",
        allowed_axioms=(),
        lake=None,
        timeout=10,
        bound=None,
        repair_target=None,
    )

    with pytest.raises(ConfigurationError, match="one valid identifier token"):
        _resolve_substitutions(tmp_path, config)

    execution_marker = tmp_path / "lake-executed"
    lake = _executable(
        tmp_path / "lake",
        f"""#!/usr/bin/env python3
import pathlib
pathlib.Path({str(execution_marker)!r}).write_text("executed", encoding="utf-8")
""",
    )
    with pytest.raises(ValueError, match="one valid token"):
        run_proof_gate(
            project,
            contract_path=contract,
            substitutions={"candidate": payload},
            allowed_axioms=(),
            lake=str(lake),
            timeout=10,
        )
    assert not execution_marker.exists()


def test_typed_lean_metadata_substitution_accepts_valid_identifier(
    tmp_path: Path,
) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    (project / "Main.lean").write_text(
        "theorem Fixture.main : True := by trivial\n", encoding="utf-8"
    )
    contract = project / "contract.lean"
    contract.write_text(
        "import Main\n#check {{candidate}}\n#print axioms Fixture.main\n",
        encoding="utf-8",
    )
    (tmp_path / "metadata.json").write_text(
        json.dumps({"candidate": "Fixture.main"}), encoding="utf-8"
    )
    config = LeanContractConfig(
        project="proof",
        contract="proof/contract.lean",
        substitutions=(
            LeanSubstitutionConfig(
                name="candidate",
                source="$metadata.candidate",
                kind="identifier",
            ),
        ),
        metadata="metadata.json",
        allowed_axioms=("propext", "Classical.choice", "Quot.sound"),
        lake=None,
        timeout=10,
        bound=None,
        repair_target=None,
    )

    substitutions = _resolve_substitutions(tmp_path, config)
    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=substitutions,
        allowed_axioms=config.allowed_axioms,
        lake=str(_fake_lake(tmp_path / "lake")),
        timeout=10,
        execution=ExecutionSpec.from_table(None, tmp_path),
    )

    assert result.status == "passed"
    assert result.substitutions == {"candidate": "Fixture.main"}
    assert [report.to_dict() for report in result.axiom_reports] == [
        {
            "declaration": "Fixture.main",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        }
    ]


def test_lean_gate_rejects_forged_compile_output_and_mismatched_audit(
    tmp_path: Path,
) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    (project / "Main.lean").write_text(
        "theorem Fixture.main : True := by trivial\n", encoding="utf-8"
    )
    contract = project / "contract.lean"
    contract.write_text("import Main\n#print axioms Fixture.main\n", encoding="utf-8")
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import json
import pathlib
import sys
if sys.argv[1:] == ["build"]:
    pass
elif sys.argv[1:] == ["env", "which", "lean"]:
    print(pathlib.Path(sys.argv[0]).resolve())
elif "--run" in sys.argv:
    print(json.dumps({"declaration": "Fixture.other", "axioms": []}))
else:
    print("'Fixture.main' does not depend on any axioms")
    pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"fake olean")
""",
    )

    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=(),
        lake=str(lake),
        timeout=10,
        execution=ExecutionSpec.from_table(None, tmp_path),
    )

    assert result.status == "failed"
    assert result.axiom_reports == ()
    assert any("unrequested declarations" in error for error in result.errors)


def test_lean_contract_feature_uses_frozen_contract_snapshot(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = tmp_path / "workspace"
    project = workspace / "proof"
    project.mkdir(parents=True)
    mutable_contract = project / "contract.lean"
    mutable_contract.write_text("malicious replacement\n", encoding="utf-8")
    run_dir = tmp_path / "run"
    frozen_contract = run_dir / "input-snapshot" / "proof" / "contract.lean"
    frozen_contract.parent.mkdir(parents=True)
    frozen_contract.write_text(
        "import Main\n#print axioms Fixture.main\n", encoding="utf-8"
    )
    stage_dir = run_dir / "stages" / "lean"
    stage_dir.mkdir(parents=True)
    observed: list[Path] = []

    def fake_gate(project_path: Path, **values: object) -> SimpleNamespace:
        assert project_path == project
        contract_path = values["contract_path"]
        assert isinstance(contract_path, Path)
        observed.append(contract_path)
        return SimpleNamespace(
            passed=True,
            errors=(),
            to_dict=lambda: {"status": "passed"},
        )

    monkeypatch.setattr(campaign_features, "run_proof_gate", fake_gate)
    config = LeanContractConfig(
        project="proof",
        contract="proof/contract.lean",
        substitutions=(),
        metadata=None,
        allowed_axioms=(),
        lake=None,
        timeout=10,
        bound=None,
        repair_target=None,
    )
    context = SimpleNamespace(
        config=config,
        workspace=workspace,
        run_dir=run_dir,
        stage_dir=stage_dir,
        attempt=1,
        lake="lake",
        campaign=SimpleNamespace(execution=None),
    )

    result = campaign_features.LeanContractFeature().execute(context)

    assert result.status == "succeeded"
    assert observed == [frozen_contract.resolve()]


def test_lean_gate_mounts_generated_sources_read_only_outside_workspace(
    tmp_path: Path,
) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    (project / "Main.lean").write_text(
        "theorem Fixture.main : True := by trivial\n", encoding="utf-8"
    )
    contract = project / "contract.lean"
    contract.write_text("import Main\n#print axioms Fixture.main\n", encoding="utf-8")
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import json
import pathlib
import sys

if sys.argv[1:] == ["build"]:
    raise SystemExit(0)
if sys.argv[1:] == ["env", "which", "lean"]:
    print(pathlib.Path(sys.argv[0]).resolve())
    raise SystemExit(0)
running_reader = "--run" in sys.argv
subject = pathlib.Path(
    sys.argv[sys.argv.index("--run") + 1] if running_reader else sys.argv[-1]
)
outside = not subject.resolve().is_relative_to(pathlib.Path.cwd().resolve())
try:
    subject.write_text("forged\\n", encoding="utf-8")
except OSError:
    protected = True
else:
    protected = False
with pathlib.Path("audit-observed.jsonl").open("a", encoding="utf-8") as stream:
    stream.write(json.dumps({"outside": outside, "protected": protected}) + "\\n")
if not outside or not protected:
    raise SystemExit(9)
if running_reader:
    separator = sys.argv.index("--")
    for declaration in sys.argv[separator + 1:]:
        print(json.dumps({"declaration": declaration, "axioms": []}))
else:
    pathlib.Path(sys.argv[sys.argv.index("-o") + 1]).write_bytes(b"fake olean")
""",
    )

    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=(),
        lake=str(lake),
        timeout=10,
        execution=ExecutionSpec.from_table(None, tmp_path),
        run_dir=tmp_path / "run",
    )

    observations = [
        json.loads(line)
        for line in (project / "audit-observed.jsonl")
        .read_text(encoding="utf-8")
        .splitlines()
    ]
    assert result.status == "passed"
    assert observations == [
        {"outside": True, "protected": True},
        {"outside": True, "protected": True},
    ]


def test_lean_gate_timeout_reaps_signal_resistant_descendants(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    project = tmp_path / "proof"
    project.mkdir()
    contract = project / "contract.lean"
    contract.write_text("#print axioms Fixture.main\n", encoding="utf-8")
    marker = tmp_path / "lean-orphan"
    monkeypatch.setenv("LEAN_ORPHAN_MARKER", str(marker))
    lake = _executable(
        tmp_path / "lake",
        """#!/usr/bin/env python3
import os
import subprocess
import sys
import time
child = (
    "import pathlib,signal,sys,time; "
    "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(2); "
    "pathlib.Path(sys.argv[1]).write_text('orphan', encoding='utf-8')"
)
subprocess.Popen(
    [sys.executable, "-c", child, os.environ["LEAN_ORPHAN_MARKER"]]
)
time.sleep(60)
""",
    )

    result = run_proof_gate(
        project,
        contract_path=contract,
        substitutions=None,
        allowed_axioms=(),
        lake=str(lake),
        timeout=1,
    )
    time.sleep(2.2)

    assert result.status == "failed"
    assert any("timed out" in error for error in result.errors)
    assert not marker.exists()


def test_deterministic_command_capture_is_bounded(tmp_path: Path) -> None:
    result = run_captured_command(
        (
            sys.executable,
            "-c",
            (
                "import sys; "
                "sys.stdout.write('o' * (2 * 1024 * 1024)); "
                "sys.stderr.write('e' * (2 * 1024 * 1024))"
            ),
        ),
        cwd=tmp_path,
        env=os.environ,
        timeout=10,
    )

    assert result.exit_code == 0
    assert len(result.stdout) == 1024 * 1024
    assert len(result.stderr) == 1024 * 1024
    assert result.stdout_truncated is True
    assert result.stderr_truncated is True


@pytest.mark.parametrize("parent_exits", (False, True))
def test_deterministic_command_reaps_descendants(
    tmp_path: Path, parent_exits: bool
) -> None:
    marker = tmp_path / f"orphan-{parent_exits}"
    child = (
        "import pathlib,signal,sys,time; "
        "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(2); "
        "pathlib.Path(sys.argv[1]).write_text('orphan', encoding='utf-8')"
    )
    parent = (
        "import subprocess,sys,time; "
        "subprocess.Popen([sys.executable, '-c', sys.argv[1], sys.argv[2]]); "
        f"time.sleep({0 if parent_exits else 60})"
    )

    result = run_captured_command(
        (sys.executable, "-c", parent, child, str(marker)),
        cwd=tmp_path,
        env=os.environ,
        timeout=1,
    )

    assert result.exit_code == (0 if parent_exits else 124)
    time.sleep(2.2)
    assert not marker.exists()


def test_workspace_fsync_tolerates_vanished_build_temporary(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    retained = tmp_path / "retained.txt"
    transient = tmp_path / "build-output.tmp"
    retained.write_text("retained\n", encoding="utf-8")
    transient.write_text("transient\n", encoding="utf-8")
    original_open = campaign_runtime.os.open

    def open_without_transient(path: object, flags: int, *args: object) -> int:
        if Path(path) == transient:
            transient.unlink()
            raise FileNotFoundError(transient)
        return original_open(path, flags, *args)

    monkeypatch.setattr(campaign_runtime.os, "open", open_without_transient)

    campaign_runtime._fsync_tree(tmp_path)

    assert retained.read_text(encoding="utf-8") == "retained\n"


def test_run_cleanup_discovers_orphaned_workspace_processes(tmp_path: Path) -> None:
    run_dir = tmp_path / "run"
    workspace = run_dir / "workspace"
    workspace.mkdir(parents=True)
    child_code = "import time; time.sleep(60)"
    parent_code = (
        "import subprocess,sys; "
        "child=subprocess.Popen("
        "[sys.executable,'-c',sys.argv[1]],"
        "cwd=sys.argv[2],start_new_session=True,"
        "stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,"
        "stderr=subprocess.DEVNULL); "
        "print(child.pid,flush=True)"
    )
    parent = subprocess.run(
        (sys.executable, "-c", parent_code, child_code, str(workspace)),
        check=True,
        capture_output=True,
        text=True,
    )
    child_pid = int(parent.stdout.strip())
    deadline = time.monotonic() + 2
    while time.monotonic() < deadline:
        try:
            fields = (
                Path(f"/proc/{child_pid}/stat")
                .read_text(encoding="utf-8")
                .rsplit(") ", maxsplit=1)[1]
                .split()
            )
        except OSError:
            break
        if fields[1] == "1":
            break
        time.sleep(0.01)

    report = terminate_run_processes(run_dir, terminate_timeout=0.2)

    assert report.ok
    assert child_pid in set(report.terminated_pids) | set(report.killed_pids)
    assert campaign_processes._is_alive(child_pid) is False


def test_repeated_captured_commands_leave_no_process_registrations(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    runtime_dir = tmp_path / "runtime"
    monkeypatch.setenv("AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(runtime_dir))

    results = tuple(
        run_captured_command(
            (sys.executable, "-c", "print('ok')"),
            cwd=tmp_path,
            env=os.environ,
            timeout=5,
            run_dir=run_dir,
        )
        for _ in range(25)
    )

    assert all(result.exit_code == 0 and result.stdout == "ok\n" for result in results)
    assert registered_run_processes(run_dir) == ()
    assert registered_run_units(run_dir) == ()
    assert process_registry.registered_run_directories() == ()


def test_command_campaign_retains_verifiable_evidence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        f'''schema_version = 1
[campaign]
id = "command-smoke"
title = "Command Smoke"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "work/input.txt"
[[stages]]
id = "check"
title = "Check Input"
mode = "research"
feature = "command"
depends_on = []
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; assert Path('input.txt').read_text().strip() == 'fixture'"]
cwd = "work"
''',
        encoding="utf-8",
    )
    campaign = CampaignSpec.load(manifest)
    options = _options(tmp_path, monkeypatch)
    run_dir = CampaignBuilder(campaign, options=options).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert state["stages"]["check"]["status"] == "succeeded"
    assert verify_campaign_bundle(run_dir) > 0
    assert isinstance(options.output, io.StringIO)
    lines = options.output.getvalue().splitlines()
    assert len(lines) == 4
    assert all("\r" not in line and len(line) < 120 for line in lines)


def test_sandbox_denies_host_writes_and_uses_private_network_namespace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    outside = tmp_path / "outside-sandbox"
    script = (
        "import os,socket,sys; from pathlib import Path; "
        "outside=Path(sys.argv[1]); host_secret=Path(sys.argv[2]); "
        "\ntry: outside.write_text('escaped', encoding='utf-8')"
        "\nexcept OSError: pass"
        "\nprint(os.readlink('/proc/self/ns/net'))"
        "\nprint(socket.socket().connect_ex(('1.1.1.1', 53)))"
        "\nprint(Path(f'/run/user/{os.getuid()}/bus').exists())"
        "\nprint(host_secret.exists())"
    )
    with NamedTemporaryFile(
        prefix=".agentic-lean-math-assistant-sandbox-", dir=Path.home()
    ) as host_secret:
        manifest = _command_manifest(
            tmp_path, script, arguments=(str(outside), host_secret.name)
        )
        run_dir = CampaignBuilder(
            CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
        ).run()

    assert not outside.exists()
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["sandbox"]["enabled"] is True
    assert receipt["sandbox"]["network"] is False
    assert receipt["sandbox"]["writable_paths"] == [str(run_dir / "workspace")]
    sandbox_net, connection_result, user_bus_visible, host_secret_visible = receipt[
        "stdout"
    ].splitlines()
    assert sandbox_net != os.readlink("/proc/self/ns/net")
    assert int(connection_result) != 0
    assert user_bus_visible == "False"
    assert host_secret_visible == "False"


def test_sandbox_uses_cgroup_memory_without_virtual_address_limit(
    tmp_path: Path,
) -> None:
    invocation = prepare_sandbox(
        ("true",),
        cwd=tmp_path,
        workspace=tmp_path,
        environment={"HOME": str(tmp_path), "PATH": "/usr/bin"},
        policy=ExecutionSpec.from_table(None, tmp_path),
        runtime_max_seconds=30,
    )

    assert any("MemoryMax=" in argument for argument in invocation.argv)
    assert not any("LimitAS=" in argument for argument in invocation.argv)


def test_resource_controls_apply_when_namespace_sandbox_is_disabled(
    tmp_path: Path,
) -> None:
    policy = ExecutionSpec.from_table(
        {"sandbox": False, "memory_max_mb": 64},
        tmp_path,
    )
    invocation = prepare_sandbox(
        (sys.executable, "-c", "bytearray(256 * 1024 * 1024)"),
        cwd=tmp_path,
        workspace=tmp_path,
        environment={"HOME": str(tmp_path), "PATH": "/usr/bin"},
        policy=policy,
        runtime_max_seconds=30,
    )

    result = subprocess.run(
        invocation.argv,
        cwd=tmp_path,
        env=invocation.environment,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )

    assert result.returncode != 0
    assert invocation.metadata["enabled"] is False
    assert invocation.metadata["backend"] == "systemd-cgroup"


@pytest.mark.parametrize("allow_workspace_executables", (False, True))
def test_sandbox_enforces_workspace_executable_policy(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    allow_workspace_executables: bool,
) -> None:
    script = (
        "import pathlib,subprocess,sys; "
        "tool=pathlib.Path('generated-tool'); "
        "tool.write_text('#!/bin/sh\\necho executed\\n', encoding='utf-8'); "
        "tool.chmod(0o755); "
        "\ntry: result=subprocess.run([str(tool.resolve())], check=False)"
        "\nexcept OSError:"
        "\n print('denied')"
        "\n raise SystemExit(0 if not " + repr(allow_workspace_executables) + " else 3)"
        "\nraise SystemExit(0 if ("
        + repr(allow_workspace_executables)
        + " and result.returncode == 0) else 4)"
    )
    manifest = _command_manifest(
        tmp_path,
        script,
        stage_config=(
            f"workspace_executables = {str(allow_workspace_executables).lower()}"
        ),
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))

    assert state["status"] == "complete"
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["sandbox"]["workspace_executables"] is allow_workspace_executables


def test_sandbox_rejects_workspace_symlink_executable_by_default(
    tmp_path: Path,
) -> None:
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    executable = workspace / "linked-tool"
    executable.symlink_to(sys.executable)

    with pytest.raises(
        SandboxError, match="workspace executable requires workspace_executables=true"
    ):
        prepare_sandbox(
            (str(executable),),
            cwd=workspace,
            workspace=workspace,
            environment=os.environ,
            policy=ExecutionSpec.from_table(None, tmp_path),
        )


def test_sandbox_exposes_virtual_environment_and_external_runtime_prefix(
    tmp_path: Path,
) -> None:
    external_prefix = tmp_path / "runtime"
    external_executable = external_prefix / "bin/python3.13"
    external_executable.parent.mkdir(parents=True)
    external_executable.write_bytes(b"external-python-fixture")
    external_executable.chmod(0o755)
    (external_prefix / "lib/python3.13").mkdir(parents=True)

    venv_root = tmp_path / "venv"
    (venv_root / "bin").mkdir(parents=True)
    (venv_root / "pyvenv.cfg").write_text(
        f"home = {external_prefix / 'bin'}\n", encoding="utf-8"
    )
    executable = venv_root / "bin/python"
    executable.symlink_to(external_executable)
    workspace = tmp_path / "workspace"
    workspace.mkdir()

    invocation = prepare_sandbox(
        (str(executable), "-c", "pass"),
        cwd=workspace,
        workspace=workspace,
        environment={"HOME": str(workspace), "PATH": str(venv_root / "bin")},
        policy=ExecutionSpec.from_table(None, tmp_path),
        runtime_max_seconds=30,
    )

    arguments = invocation.argv
    assert any(
        arguments[index : index + 3] == ("--ro-bind", str(venv_root), str(venv_root))
        for index in range(len(arguments) - 2)
    )
    assert any(
        arguments[index : index + 3]
        == ("--ro-bind", str(external_prefix), str(external_prefix))
        for index in range(len(arguments) - 2)
    )
    allowed = invocation.metadata["allowed_executable_paths"]
    assert str(venv_root) in allowed
    assert str(external_prefix) in allowed


def test_workspace_quota_ignores_regenerable_caches(tmp_path: Path) -> None:
    workspace = tmp_path / "workspace"
    cache = workspace / ".lake" / "build"
    cache.mkdir(parents=True)
    (cache / "dependency.olean").write_bytes(b"x" * (2 * 1024 * 1024))
    exceeded, observed = workspace_size_exceeds(workspace, 1024 * 1024)
    assert not exceeded
    assert observed < 1024 * 1024
    (workspace / "durable.bin").write_bytes(b"x" * (2 * 1024 * 1024))
    exceeded, observed = workspace_size_exceeds(workspace, 1024 * 1024)
    assert exceeded
    assert observed > 1024 * 1024


def test_sandbox_enforces_workspace_quota(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _command_manifest(
        tmp_path,
        "import pathlib; "
        "pathlib.Path('large.bin').write_bytes(b'x' * (2 * 1024 * 1024))",
        execution="[execution]\nworkspace_max_mb = 1",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    assert state["stages"]["check"]["status"] == "failed"
    assert receipt["exit_code"] == 125
    assert "workspace exceeded sandbox limit" in receipt["error"]


def test_sandbox_enforces_memory_limit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _command_manifest(
        tmp_path,
        "import time; value=bytearray(256 * 1024 * 1024); time.sleep(1)",
        execution="[execution]\nmemory_max_mb = 64",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    assert state["stages"]["check"]["status"] == "failed"
    assert receipt["exit_code"] != 0
    assert receipt["sandbox"]["memory_max_mb"] == 64
    assert receipt["sandbox"]["memory_swap_max_mb"] == 0


def test_sandbox_enforces_process_limit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    script = (
        "import subprocess,time; processes=[]"
        "\nfor ordinal in range(20):"
        "\n try: processes.append(subprocess.Popen(['/usr/bin/sleep', '2']))"
        "\n except OSError:"
        "\n  print(ordinal)"
        "\n  break"
        "\nelse: raise SystemExit('process limit was not enforced')"
        "\nfor process in processes: process.terminate()"
    )
    manifest = _command_manifest(
        tmp_path,
        script,
        execution="[execution]\ntasks_max = 4",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    assert receipt["exit_code"] == 0
    assert int(receipt["stdout"]) < 20
    assert receipt["sandbox"]["tasks_max"] == 4


def test_sandbox_enforces_per_file_size_limit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    script = (
        "import pathlib"
        "\ntry: pathlib.Path('oversized.bin').write_bytes(b'x' * (2 * 1024 * 1024))"
        "\nexcept OSError: print('limited')"
        "\nelse: raise SystemExit('file size limit was not enforced')"
    )
    manifest = _command_manifest(
        tmp_path,
        script,
        execution="[execution]\nfile_size_max_mb = 1",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    assert receipt["exit_code"] == 0
    assert receipt["stdout"].strip() == "limited"
    assert (run_dir / "workspace/oversized.bin").stat().st_size <= 1024 * 1024


def test_sandbox_allowlists_environment_and_redacts_secrets(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    secret = "retained-secret-must-not-leak"
    monkeypatch.setenv("VISIBLE_SETTING", "visible")
    monkeypatch.setenv("SECRET_SETTING", secret)
    monkeypatch.setenv("UNDECLARED_SETTING", "hidden")
    host_home = os.environ["HOME"]
    script = (
        "import json,os; from pathlib import Path; "
        "secret_path=Path('private/secret-output.txt'); "
        "secret_path.parent.mkdir(); "
        "secret_path.write_text(os.environ['SECRET_SETTING'], encoding='utf-8'); "
        "secret_path.chmod(0); secret_path.parent.chmod(0); "
        "Path('leak-link').symlink_to(os.environ['SECRET_SETTING']); "
        "Path(os.environ['SECRET_SETTING']).mkdir(); "
        "print(json.dumps({"
        "'home': os.environ.get('HOME'), "
        "'visible': os.environ.get('VISIBLE_SETTING'), "
        "'secret': os.environ.get('SECRET_SETTING'), "
        "'undeclared': os.environ.get('UNDECLARED_SETTING')"
        "}, sort_keys=True))"
    )
    manifest = _command_manifest(
        tmp_path,
        script,
        execution=(
            "[execution]\n"
            "sandbox = false\n"
            'environment_allow = ["HOME", "PATH", "VISIBLE_SETTING", '
            '"SECRET_SETTING"]\n'
            'secret_environment = ["SECRET_SETTING"]'
        ),
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    output = json.loads(receipt["stdout"])

    assert output == {
        "home": host_home,
        "secret": "[REDACTED]",
        "undeclared": None,
        "visible": "visible",
    }
    assert receipt["exit_code"] == 126
    assert not (run_dir / "workspace/private/secret-output.txt").exists()
    assert not (run_dir / "workspace/leak-link").is_symlink()
    assert not (run_dir / "workspace" / secret).exists()
    assert receipt["sandbox"]["enabled"] is False
    assert all(
        secret not in path.read_text(encoding="utf-8", errors="replace")
        for path in run_dir.rglob("*")
        if path.is_file()
    )


def test_streaming_redactor_catches_secrets_across_chunks() -> None:
    redactor = _StreamingRedactor(("cross-boundary-secret",))

    output = (
        redactor.feed("prefix-cross-boundary-")
        + redactor.feed("secret-suffix")
        + redactor.feed("", final=True)
    )

    assert output == "prefix-[REDACTED]-suffix"


def test_sandbox_normalizes_environment_and_fingerprints_toolchain(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv("LANG", "host-locale")
    monkeypatch.setenv("LC_ALL", "host-locale")
    monkeypatch.setenv("TZ", "host-zone")
    monkeypatch.setenv("TERM", "host-terminal")
    monkeypatch.setenv("USER", "host-user")
    (tmp_path / "dependency.lock").write_text("locked\n", encoding="utf-8")
    script = (
        "import json,os; print(json.dumps({name: os.environ.get(name) for name in "
        "('LANG','LC_ALL','TZ','TERM','USER')}, sort_keys=True))"
    )
    manifest = _command_manifest(
        tmp_path,
        script,
        execution=(
            "[execution]\n"
            'environment_allow = ["HOME", "PATH", "LANG", "LC_ALL", "TZ", '
            '"TERM", "USER"]'
        ),
    )
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            "[[stages]]",
            '[[inputs]]\nsource = "dependency.lock"\ntarget = "uv.lock"\n[[stages]]',
            1,
        ),
        encoding="utf-8",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest), options=_options(tmp_path, monkeypatch)
    ).run()
    receipt_path = next((run_dir / "stages" / "check").glob("attempt-*.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))

    assert json.loads(receipt["stdout"]) == {
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TERM": "dumb",
        "TZ": "UTC",
        "USER": "campaign",
    }
    environment = receipt["sandbox"]["environment"]
    assert len(environment["sha256"]) == 64
    assert environment["secret"] == []
    executable = receipt["sandbox"]["toolchain"]["executable"]
    assert executable["resolved_path"] == str(Path(sys.executable).resolve())
    assert len(executable["sha256"]) == 64
    assert receipt["sandbox"]["toolchain"]["dependency_manifests"] == [
        {
            "path": "uv.lock",
            "sha256": hashlib.sha256(b"locked\n").hexdigest(),
            "size": 7,
        }
    ]


def test_research_revision_reruns_target_and_downstream(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "research-migration"
title = "Research Migration"
instructions = "campaign.md"
runs_dir = "runs"
max_revisions = 1
[[inputs]]
source = "input.txt"
target = "input.txt"
[handoff]
producer = "synthesizer"
artifact = "handoffs/research.json"
schema = "research-v1"
approval = "automatic"
[[stages]]
id = "source_analyst"
title = "Source Analyst"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read"]
max_time = 60
[[stages]]
id = "synthesizer"
title = "Synthesizer"
mode = "research"
feature = "agent"
depends_on = ["source_analyst"]
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
handoff = "handoffs/research.json"
handoff_schema = "research-v1"
[[stages]]
id = "final_reviewer"
title = "Final Reviewer"
mode = "research"
feature = "agent"
depends_on = ["synthesizer"]
max_attempts = 2
[stages.config]
instructions = "role.md"
tools = ["read"]
max_time = 60
review = true
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CAMPAIGN_REVISE", "1")
    campaign = CampaignSpec.load(manifest)
    run_dir = CampaignBuilder(campaign, options=_options(tmp_path, monkeypatch)).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert state["revisions"] == 1
    assert state["stages"]["source_analyst"]["attempts"] == 2
    assert state["stages"]["synthesizer"]["attempts"] == 2
    assert state["stages"]["final_reviewer"]["attempts"] == 2
    assert (run_dir / "agents/research/synthesizer/research.json").is_file()
    assert verify_campaign_bundle(run_dir) > 15


def test_required_approval_resumes_exact_handoff(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        f'''schema_version = 1
[campaign]
id = "approval-resume"
title = "Approval Resume"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[handoff]
producer = "formalization_synthesizer"
artifact = "handoffs/research.json"
schema = "research-v1"
approval = "required"
[[stages]]
id = "formalization_synthesizer"
title = "Formalization Synthesizer"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
handoff = "handoffs/research.json"
handoff_schema = "research-v1"
[[stages]]
id = "build"
title = "Build"
mode = "build"
feature = "command"
depends_on = ["formalization_synthesizer"]
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; Path('built').write_text('done')"]
cwd = "."
''',
        encoding="utf-8",
    )
    campaign = CampaignSpec.load(manifest)
    options = _options(tmp_path, monkeypatch)
    run_dir = CampaignBuilder(campaign, options=options).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "awaiting_approval"
    inventory = json.loads(
        (
            run_dir
            / "agents/research/formalization_synthesizer/attempt-01-sources.json"
        ).read_text(encoding="utf-8")
    )
    handoff = json.loads(
        (run_dir / "workspace" / "handoffs" / "research.json").read_text(
            encoding="utf-8"
        )
    )
    assert handoff["sources"][0]["sha256"] in {
        item["sha256"] for item in inventory["workspace_sources"]
    }
    prompt = (
        run_dir / "prompts" / "formalization_synthesizer-attempt-01.md"
    ).read_text(encoding="utf-8")
    assert "`goal` and `scope`: nonempty strings, not arrays" in prompt
    assert "Never use placeholders or fabricate a digest" in prompt
    digest = approve_handoff(run_dir)
    assert len(digest) == 64
    assert verify_campaign_bundle(run_dir) > 10
    manifest.unlink()
    (tmp_path / "campaign.md").unlink()
    (tmp_path / "role.md").unlink()
    resolved_path = campaign_resolved_for_run(run_dir)
    retained_campaign = CampaignSpec.load_resolved(resolved_path)
    retained_source = resolved_path.read_text(encoding="utf-8")
    resolved_path.write_text(retained_source + "\n", encoding="utf-8")
    with pytest.raises(CampaignRunError, match="configuration changed"):
        CampaignBuilder(retained_campaign, options=options, run_dir=run_dir).resume()
    resolved_path.write_text(retained_source, encoding="utf-8")
    CampaignBuilder(retained_campaign, options=options, run_dir=run_dir).resume()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert (run_dir / "workspace" / "built").read_text(encoding="utf-8") == "done"
    assert verify_campaign_bundle(run_dir) > 10


def test_explicit_resume_retries_invalid_handoff(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        f'''schema_version = 1
[campaign]
id = "handoff-retry"
title = "Handoff Retry"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[handoff]
producer = "formalization_synthesizer"
artifact = "handoffs/research.json"
schema = "research-v1"
approval = "automatic"
[[stages]]
id = "formalization_synthesizer"
title = "Formalization Synthesizer"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
handoff = "handoffs/research.json"
handoff_schema = "research-v1"
[[stages]]
id = "build"
title = "Build"
mode = "build"
feature = "command"
depends_on = ["formalization_synthesizer"]
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; Path('built').write_text('done')"]
cwd = "."
''',
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CAMPAIGN_INVALID_HANDOFF_ONCE", "1")
    campaign = CampaignSpec.load(manifest)
    run_dir = CampaignBuilder(campaign, options=_options(tmp_path, monkeypatch)).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert state["stages"]["formalization_synthesizer"]["status"] == "failed"
    assert (
        run_dir / "agents/research/formalization_synthesizer/attempt-01-research.json"
    ).is_file()

    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    CampaignBuilder(
        retained,
        options=_options(tmp_path, monkeypatch, retry_failed=True),
        run_dir=run_dir,
    ).resume()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert state["stages"]["formalization_synthesizer"]["attempts"] == 2
    assert state["stages"]["build"]["status"] == "succeeded"
    assert (run_dir / "workspace" / "built").read_text(encoding="utf-8") == "done"
    assert any(
        event["status"] == "retrying"
        and "formalization_synthesizer" in event["summary"]
        for event in state["events"]
    )


def test_retry_requires_handoff_created_by_current_attempt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "fresh-handoff-retry"
title = "Fresh Handoff Retry"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[handoff]
producer = "formalization_synthesizer"
artifact = "handoffs/research.json"
schema = "research-v1"
approval = "automatic"
[[stages]]
id = "formalization_synthesizer"
title = "Formalization Synthesizer"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
handoff = "handoffs/research.json"
handoff_schema = "research-v1"
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_CAMPAIGN_STALE_HANDOFF_RETRY", "1")
    campaign = CampaignSpec.load(manifest)
    options = _options(tmp_path, monkeypatch)
    run_dir = CampaignBuilder(campaign, options=options).run()
    handoff = run_dir / "workspace" / "handoffs" / "research.json"
    assert not handoff.exists()

    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    CampaignBuilder(
        retained,
        options=_options(tmp_path, monkeypatch, retry_failed=True),
        run_dir=run_dir,
    ).resume()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    stage = state["stages"]["formalization_synthesizer"]
    assert state["status"] == "incomplete"
    assert stage["status"] == "failed"
    assert stage["attempts"] == 2
    assert stage["summary"] == (
        "agent did not produce required handoff: handoffs/research.json"
    )
    stage_dir = run_dir / "agents/research/formalization_synthesizer"
    receipt = json.loads((stage_dir / "attempt-02.json").read_text(encoding="utf-8"))
    assert receipt["status"] == "succeeded"
    assert "Completed attempt 2" in (stage_dir / "attempt-02.md").read_text(
        encoding="utf-8"
    )
    inventory = json.loads(
        (stage_dir / "attempt-02-sources.json").read_text(encoding="utf-8")
    )
    assert "handoffs/research.json" not in {
        item["path"] for item in inventory["workspace_sources"]
    }
    assert not handoff.exists()


def test_failed_lean_gate_routes_targeted_repair_and_promotes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    project = tmp_path / "seed"
    project.mkdir()
    (project / "lakefile.toml").write_text('name = "fixture"\n', encoding="utf-8")
    (project / "Certificate.lean").write_text(
        "theorem proof_result : True := True.intro\n", encoding="utf-8"
    )
    cache = tmp_path / "cache"
    cache.mkdir()
    (cache / "cache-file").write_text("linked\n", encoding="utf-8")
    contract = tmp_path / "contract.lean"
    contract.write_text(
        "import Certificate\nexample : True := proof_result\n#print axioms proof_result\n",
        encoding="utf-8",
    )
    manifest = tmp_path / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "repair-routing"
title = "Repair Routing"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "seed"
target = "proof"
[[inputs]]
source = "cache"
target = "proof/.lake"
strategy = "symlink"
[[inputs]]
source = "contract.lean"
target = "contracts/final.lean"
[[stages]]
id = "baseline_prover"
title = "Baseline Prover"
mode = "build"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
[[stages]]
id = "gate"
title = "Gate"
mode = "build"
feature = "lean_contract"
depends_on = ["baseline_prover"]
max_attempts = 2
[stages.config]
project = "proof"
contract = "contracts/final.lean"
allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]
repair_target = "baseline_prover"
timeout = 30
[[stages]]
id = "promote"
title = "Promote"
mode = "build"
feature = "artifact_promote"
depends_on = ["gate"]
[stages.config]
source = "proof"
destination = "accepted"
excludes = [".lake/**"]
""",
        encoding="utf-8",
    )
    monkeypatch.setenv("FAKE_LAKE_REQUIRE_READY", "1")
    omp = _fake_omp(tmp_path / "fake-omp")
    lake = _fake_lake(tmp_path / "fake-lake")
    campaign = CampaignSpec.load(manifest)
    run_dir = CampaignBuilder(
        campaign,
        options=_options(tmp_path, monkeypatch, omp=omp, lake=lake),
    ).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert state["stages"]["baseline_prover"]["attempts"] == 2
    assert state["stages"]["gate"]["attempts"] == 2
    assert (run_dir / "accepted" / "ready").read_text(encoding="utf-8") == "ready\n"
    assert not (run_dir / "accepted" / ".lake").exists()
    assert verify_campaign_bundle(run_dir) > 15

    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    CampaignBuilder(
        retained,
        options=_options(
            tmp_path,
            monkeypatch,
            omp=omp,
            lake=lake,
            retry_stages=("baseline_prover",),
            retry_feedback=("Recheck the completed proof.",),
        ),
        run_dir=run_dir,
    ).resume()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert state["stages"]["baseline_prover"]["attempts"] == 3
    retry_prompt = (run_dir / "prompts" / "baseline_prover-attempt-03.md").read_text(
        encoding="utf-8"
    )
    assert "Recheck the completed proof." in retry_prompt
    assert (run_dir / "accepted" / "ready").read_text(encoding="utf-8") == "ready\n"


def test_stop_all_is_idempotent_without_registrations(tmp_path: Path) -> None:
    first = stop_all_campaigns(runtime_dir=tmp_path / "runtime")
    second = stop_all_campaigns(runtime_dir=tmp_path / "runtime")
    assert first.ok and second.ok
    assert first.registrations == second.registrations == 0


def test_herdr_error_retains_machine_readable_code(tmp_path: Path) -> None:
    herdr = _executable(
        tmp_path / "missing-herdr",
        """#!/usr/bin/env python3
import sys
print('{"error":{"code":"workspace_not_found","message":"missing"}}', file=sys.stderr)
raise SystemExit(1)
""",
    )

    with pytest.raises(HerdrError) as failure:
        HerdrClient(str(herdr)).close_workspace("w-missing")

    assert failure.value.code == "workspace_not_found"


def test_herdr_pane_run_preserves_absolute_program(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    client = HerdrClient("herdr")
    observed: list[tuple[str, ...]] = []

    def run(*arguments: str) -> SimpleNamespace:
        observed.append(arguments)
        return SimpleNamespace(error=None, exit_code=0, stderr="", stdout="")

    monkeypatch.setattr(client, "_run", run)

    client.run_in_pane("w1:p1", ("/opt/campaign/bin/python", "-m", "runner"))

    assert observed == [
        (
            "pane",
            "run",
            "w1:p1",
            " env",
            "/opt/campaign/bin/python",
            "-m",
            "runner",
        )
    ]


def test_herdr_timeout_reaps_signal_resistant_descendants(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    marker = tmp_path / "herdr-orphan"
    monkeypatch.setenv("HERDR_ORPHAN_MARKER", str(marker))
    herdr = _executable(
        tmp_path / "hung-herdr",
        """#!/usr/bin/env python3
import os
import subprocess
import sys
import time
child = (
    "import pathlib,signal,sys,time; "
    "signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(2); "
    "pathlib.Path(sys.argv[1]).write_text('orphan', encoding='utf-8')"
)
subprocess.Popen(
    [sys.executable, "-c", child, os.environ["HERDR_ORPHAN_MARKER"]]
)
time.sleep(60)
""",
    )

    with pytest.raises(HerdrError, match="timed out"):
        HerdrClient(str(herdr), timeout=0.2).close_workspace("w-hung")
    time.sleep(2.2)

    assert not marker.exists()


def test_controller_registrations_preserve_reused_pid_identities(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime_dir = tmp_path / "runtime"
    old_run = tmp_path / "old-run"
    new_run = tmp_path / "new-run"
    old_run.mkdir()
    new_run.mkdir()
    current_start = ["old-start"]
    monkeypatch.setattr(
        campaign_processes,
        "_process_start_time",
        lambda _pid: current_start[0],
    )

    register_campaign(old_run, "herdr", pid=4242, runtime_dir=runtime_dir)
    register_workspace("old-workspace", pid=4242, runtime_dir=runtime_dir)
    current_start[0] = "new-start"
    register_campaign(new_run, "herdr", pid=4242, runtime_dir=runtime_dir)
    register_workspace("new-workspace", pid=4242, runtime_dir=runtime_dir)

    registrations = [
        campaign_processes._read_registration(path)
        for path in sorted(runtime_dir.glob("*.json"))
    ]
    assert {
        (value["process_start_time"], value["run_dir"], value["herdr_workspace_id"])
        for value in registrations
    } == {
        ("old-start", str(old_run.resolve()), "old-workspace"),
        ("new-start", str(new_run.resolve()), "new-workspace"),
    }

    campaign_processes.unregister_campaign(pid=4242, runtime_dir=runtime_dir)
    remaining = [
        campaign_processes._read_registration(path)
        for path in runtime_dir.glob("*.json")
    ]
    assert len(remaining) == 1
    assert remaining[0]["process_start_time"] == "old-start"


def test_stop_all_treats_missing_registered_workspace_as_closed(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime_dir = tmp_path / "runtime"
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    (run_dir / "state.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "campaign_id": "fixture",
                "status": "running",
                "herdr_closed": False,
            }
        ),
        encoding="utf-8",
    )
    dead_pid = 999_999_999
    register_campaign(run_dir, "missing-herdr", pid=dead_pid, runtime_dir=runtime_dir)
    register_workspace("w-missing", pid=dead_pid, runtime_dir=runtime_dir)

    class MissingWorkspaceHerdr:
        def __init__(self, executable: str) -> None:
            assert executable == "missing-herdr"

        def close_workspace(self, workspace_id: str) -> None:
            assert workspace_id == "w-missing"
            raise HerdrError("workspace does not exist", code="workspace_not_found")

    monkeypatch.setattr(
        "agentic_lean_math_assistant.processes.HerdrClient", MissingWorkspaceHerdr
    )
    report = stop_all_campaigns(runtime_dir=runtime_dir)

    assert report.ok
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "stopped"
    assert state["herdr_closed"] is True
    assert stop_all_campaigns(runtime_dir=runtime_dir).registrations == 0


def test_kept_workspace_remains_registered_until_stop_all(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime_dir = tmp_path / "runtime"
    monkeypatch.setenv("AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(runtime_dir))
    manifest = _copy_claim_ledger_example(tmp_path)
    options = replace(_options(tmp_path, monkeypatch), close_herdr=False)

    run_dir = CampaignBuilder(CampaignSpec.load(manifest), options=options).run()

    registrations = list(runtime_dir.glob("*.json"))
    assert len(registrations) == 1
    registration = json.loads(registrations[0].read_text(encoding="utf-8"))
    registration["pid"] = 999_999_999
    registration["process_start_time"] = None
    registrations[0].write_text(json.dumps(registration), encoding="utf-8")
    report = stop_all_campaigns(runtime_dir=runtime_dir)

    assert report.ok
    assert report.workspaces_closed == ("w1",)
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    assert state["herdr_closed"] is True
    assert stop_all_campaigns(runtime_dir=runtime_dir).registrations == 0
    assert verify_campaign_bundle(run_dir) > 0


def _publication_run(tmp_path: Path, *, status: str = "complete") -> tuple[Path, Path]:
    manifest_dir = tmp_path / "manifest"
    manifest_dir.mkdir(parents=True)
    (manifest_dir / "input.txt").write_text("input\n", encoding="utf-8")
    instructions = manifest_dir / "campaign.md"
    instructions.write_text("Publish the retained proof.\n", encoding="utf-8")
    manifest = manifest_dir / "campaign.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "publication-fixture"
title = "Publication Fixture"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "build"
title = "Build"
mode = "build"
feature = "command"
depends_on = []
[stages.config]
argv = ["true"]
[publish]
source = "final-proof"
root = ".."
destination = "../canonical"
preserve = [".lake"]
""",
        encoding="utf-8",
    )
    campaign = CampaignSpec.load(manifest)
    run_dir = tmp_path / "run"
    configuration = run_dir / "configuration"
    configuration.mkdir(parents=True)
    retained_manifest = configuration / "campaign.toml"
    retained_manifest.write_text(manifest.read_text(encoding="utf-8"), encoding="utf-8")
    retained_instructions = configuration / "campaign.md"
    retained_instructions.write_text(
        instructions.read_text(encoding="utf-8"), encoding="utf-8"
    )
    (configuration / "resolved.json").write_text(
        json.dumps(
            campaign.to_resolved_dict(
                manifest_path=retained_manifest,
                instructions_path=retained_instructions,
                stage_instructions={},
            ),
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    source = run_dir / "final-proof"
    source.mkdir()
    (source / "new.txt").write_text("replacement\n", encoding="utf-8")
    (run_dir / "state.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "campaign_id": campaign.campaign_id,
                "run_id": "publication-run",
                "status": status,
            }
        )
        + "\n",
        encoding="utf-8",
    )
    refresh_campaign_evidence(run_dir)
    assert campaign.publish is not None
    return run_dir, campaign.publish.destination


def test_publication_rejects_unapproved_plan_without_touching_destination(
    tmp_path: Path,
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    plan = plan_publication(run_dir)

    with pytest.raises(CampaignRunError, match="publication digest mismatch"):
        publish_campaign(run_dir, "0" * 64)

    assert plan.digest != "0" * 64
    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert not (run_dir / "publication.json").exists()


def test_publication_requires_complete_untampered_evidence(tmp_path: Path) -> None:
    incomplete, _ = _publication_run(tmp_path / "incomplete", status="incomplete")
    with pytest.raises(CampaignRunError, match="complete campaign"):
        plan_publication(incomplete)

    tampered, _ = _publication_run(tmp_path / "tampered")
    (tampered / "final-proof" / "new.txt").write_text("tampered\n", encoding="utf-8")
    with pytest.raises(CampaignRunError, match="evidence verification failed"):
        plan_publication(tampered)


def test_publication_replaces_content_and_preserves_allowlisted_cache(
    tmp_path: Path,
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "stale.txt").write_text("stale\n", encoding="utf-8")
    cache = destination / ".lake"
    cache.mkdir()
    (cache / "cache.bin").write_text("retained\n", encoding="utf-8")
    plan = plan_publication(run_dir)

    published = publish_campaign(run_dir, plan.digest)

    assert published.digest == plan.digest
    assert (destination / "new.txt").read_text(encoding="utf-8") == "replacement\n"
    assert not (destination / "stale.txt").exists()
    assert not (destination / ".lake" / "new-cache").exists()
    assert (destination / ".lake" / "cache.bin").read_text(
        encoding="utf-8"
    ) == "retained\n"
    receipt = json.loads((run_dir / "publication.json").read_text(encoding="utf-8"))
    assert receipt["sha256"] == plan.digest
    assert (
        CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir)).publish
        is not None
    )
    assert verify_campaign_bundle(run_dir) > 0


def _rewrite_resolved_publish(
    run_dir: Path,
    *,
    root: Path | None = None,
    destination: Path | None = None,
    preserve: list[str] | None = None,
) -> None:
    resolved = campaign_resolved_for_run(run_dir)
    data = json.loads(resolved.read_text(encoding="utf-8"))
    publish = data["publish"]
    if root is not None:
        publish["root"] = str(root)
    if destination is not None:
        publish["destination"] = str(destination)
    if preserve is not None:
        publish["preserve"] = preserve
    resolved.write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    refresh_campaign_evidence(run_dir)


def test_publication_serializes_canonical_destination_across_processes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    first_run, _ = _publication_run(tmp_path / "first")
    second_run, _ = _publication_run(tmp_path / "second")
    (second_run / "final-proof" / "new.txt").write_text(
        "second replacement\n", encoding="utf-8"
    )
    publish_root = tmp_path / "publish-root"
    alias_component = publish_root / "alias"
    alias_component.mkdir(parents=True)
    destination = publish_root / "canonical"
    aliased_destination = alias_component / ".." / destination.name
    _rewrite_resolved_publish(first_run, root=publish_root, destination=destination)
    _rewrite_resolved_publish(
        second_run, root=publish_root, destination=aliased_destination
    )
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    first_plan = plan_publication(first_run)
    second_plan = plan_publication(second_run)
    assert first_plan.destination.resolve() == second_plan.destination.resolve()

    first_entered = tmp_path / "first-entered"
    second_entered = tmp_path / "second-entered"
    release_first = tmp_path / "release-first"
    second_started = tmp_path / "second-started"
    first_result = tmp_path / "first-result.json"
    second_result = tmp_path / "second-result.json"
    original_publish = campaign_publish_module._publish_locked

    def pause_first_transaction(
        plan: campaign_publish_module.PublicationPlan,
    ) -> None:
        entered = first_entered if plan.run_dir == first_run else second_entered
        entered.write_text("entered\n", encoding="utf-8")
        if plan.run_dir == first_run:
            deadline = time.monotonic() + 5
            while not release_first.exists() and time.monotonic() < deadline:
                time.sleep(0.01)
            if not release_first.exists():
                raise AssertionError("timed out waiting to release first publication")
        original_publish(plan)

    monkeypatch.setattr(
        campaign_publish_module, "_publish_locked", pause_first_transaction
    )

    def publish_in_child(
        run_dir: Path, digest: str, result_path: Path, started: Path | None = None
    ) -> None:
        if started is not None:
            started.write_text("started\n", encoding="utf-8")
        try:
            published = publish_campaign(run_dir, digest)
            result = {"status": "committed", "digest": published.digest}
        except BaseException as exc:  # noqa: BLE001
            result = {
                "status": "error",
                "type": type(exc).__name__,
                "message": str(exc),
            }
        result_path.write_text(json.dumps(result), encoding="utf-8")
        os._exit(0)

    child_pids: list[int] = []
    try:
        first_pid = os.fork()
        if first_pid == 0:
            publish_in_child(first_run, first_plan.digest, first_result)
        child_pids.append(first_pid)
        deadline = time.monotonic() + 5
        while not first_entered.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert first_entered.exists()

        second_pid = os.fork()
        if second_pid == 0:
            publish_in_child(
                second_run,
                second_plan.digest,
                second_result,
                started=second_started,
            )
        child_pids.append(second_pid)
        deadline = time.monotonic() + 5
        while not second_started.exists() and time.monotonic() < deadline:
            time.sleep(0.01)
        assert second_started.exists()
        time.sleep(0.1)
        assert not second_entered.exists()
        assert not second_result.exists()
    finally:
        release_first.touch()
        for child_pid in child_pids:
            waited_pid, status = os.waitpid(child_pid, 0)
            assert waited_pid == child_pid
            assert os.waitstatus_to_exitcode(status) == 0

    first_outcome = json.loads(first_result.read_text(encoding="utf-8"))
    second_outcome = json.loads(second_result.read_text(encoding="utf-8"))
    assert first_outcome == {"status": "committed", "digest": first_plan.digest}
    assert second_outcome["status"] == "error"
    assert second_outcome["type"] == "CampaignRunError"
    assert "publication digest mismatch" in second_outcome["message"]
    assert not second_entered.exists()
    assert (destination / "new.txt").read_text(encoding="utf-8") == "replacement\n"
    first_receipt = json.loads(
        (first_run / "publication.json").read_text(encoding="utf-8")
    )
    assert first_receipt["phase"] == "committed"
    assert first_receipt["sha256"] == first_plan.digest
    assert not (second_run / "publication.json").exists()


def test_publication_digest_commits_to_destination_and_ordered_preserve(
    tmp_path: Path,
) -> None:
    run_dir, _ = _publication_run(tmp_path)
    first = plan_publication(run_dir)
    _rewrite_resolved_publish(
        run_dir,
        destination=tmp_path / "other-canonical",
        preserve=["cache", ".lake"],
    )

    second = plan_publication(run_dir)

    assert first.artifacts == second.artifacts
    assert first.destination != second.destination
    assert first.preserve != second.preserve
    assert first.digest != second.digest


def test_publication_rehashes_exact_staged_bytes_after_planning(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    original_copy = campaign_publish_module._copy_exact_plan

    def mutate_then_copy(
        approved: campaign_publish_module.PublicationPlan, staging: Path
    ) -> None:
        (approved.source / "new.txt").write_text("unapproved\n", encoding="utf-8")
        original_copy(approved, staging)

    monkeypatch.setattr(campaign_publish_module, "_copy_exact_plan", mutate_then_copy)

    with pytest.raises(CampaignRunError, match="staged publication bytes"):
        publish_campaign(run_dir, plan.digest)

    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert not (run_dir / "publication.json").exists()


def test_publication_rejects_root_destination_overlap_and_symlink_boundaries(
    tmp_path: Path,
) -> None:
    outside_run, _ = _publication_run(tmp_path / "outside")
    outside_root = tmp_path / "outside"
    _rewrite_resolved_publish(
        outside_run,
        root=outside_root,
        destination=tmp_path / "escaped",
    )
    with pytest.raises(ConfigurationError, match="strictly below"):
        plan_publication(outside_run)

    overlap_run, _ = _publication_run(tmp_path / "overlap")
    _rewrite_resolved_publish(
        overlap_run,
        root=tmp_path,
        destination=overlap_run / "canonical",
    )
    with pytest.raises(CampaignRunError, match="overlaps"):
        plan_publication(overlap_run)

    symlink_run, _ = _publication_run(tmp_path / "symlink")
    real_parent = tmp_path / "symlink" / "real-destination-parent"
    real_parent.mkdir()
    linked_parent = tmp_path / "symlink" / "linked-destination-parent"
    linked_parent.symlink_to(real_parent, target_is_directory=True)
    _rewrite_resolved_publish(
        symlink_run,
        root=tmp_path / "symlink",
        destination=linked_parent / "canonical",
    )
    with pytest.raises(CampaignRunError, match="symlink ancestry"):
        plan_publication(symlink_run)


def test_publish_plan_cli_prints_complete_json_without_publication(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    state_before = (run_dir / "state.json").read_bytes()
    evidence_before = (run_dir / "evidence.json").read_bytes()

    assert campaign_main(["publish-plan", "--run", str(run_dir)]) == 0

    displayed = json.loads(capsys.readouterr().out)
    assert displayed["approved_digest"] == plan_publication(run_dir).digest
    assert displayed["campaign_id"] == "publication-fixture"
    assert displayed["run_id"] == "publication-run"
    assert displayed["source"] == {"kind": "directory", "path": "final-proof"}
    assert displayed["root"] == str(tmp_path)
    assert displayed["destination"] == str(destination)
    assert displayed["preserve"] == [".lake"]
    assert displayed["artifacts"] == [
        {
            "path": "new.txt",
            "sha256": digest_file(
                run_dir / "final-proof" / "new.txt",
                relative_to=run_dir / "final-proof",
            ).sha256,
            "size": 12,
        }
    ]
    assert displayed["changes"] == [
        {"path": "new.txt", "status": "added"},
        {"path": "old.txt", "status": "deleted"},
    ]
    assert (run_dir / "state.json").read_bytes() == state_before
    assert (run_dir / "evidence.json").read_bytes() == evidence_before
    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert not (run_dir / "publication.json").exists()
    assert not (run_dir / "publication.pending.json").exists()


def test_publication_post_swap_failure_restores_destination_and_records_recovery(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    cache = destination / ".lake"
    cache.mkdir()
    (cache / "cache.bin").write_text("retained\n", encoding="utf-8")
    plan = plan_publication(run_dir)

    original_atomic_write_json = campaign_publish_module.atomic_write_json

    def fail_commit_receipt(path: Path, value: object) -> None:
        if (
            path == run_dir / "publication.json"
            and isinstance(value, dict)
            and value.get("phase") == "committed"
        ):
            raise OSError("injected commit receipt durability failure")
        original_atomic_write_json(path, value)

    monkeypatch.setattr(
        campaign_publish_module, "atomic_write_json", fail_commit_receipt
    )
    with pytest.raises(OSError, match="injected commit receipt durability failure"):
        publish_campaign(run_dir, plan.digest)

    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert (destination / ".lake" / "cache.bin").read_text(
        encoding="utf-8"
    ) == "retained\n"
    recovery = json.loads(
        (run_dir / "publication.pending.json").read_text(encoding="utf-8")
    )
    receipt = json.loads((run_dir / "publication.json").read_text(encoding="utf-8"))
    assert recovery["phase"] == "rolled_back"
    assert receipt["phase"] == "rolled_back"
    failed = Path(recovery["failed_destination"])
    assert (failed / "new.txt").read_text(encoding="utf-8") == "replacement\n"
    assert not (failed / ".lake").exists()


def test_publication_recovers_a_crash_between_swap_and_phase_receipt(
    tmp_path: Path,
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    cache = destination / ".lake"
    cache.mkdir()
    (cache / "cache.bin").write_text("retained\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    token = "abc123def456"
    staging = destination.parent / f".{destination.name}.publish-{token}"
    backup = destination.parent / f".{destination.name}.previous-{token}"
    failed = destination.parent / f".{destination.name}.failed-{token}"
    campaign_publish_module._copy_exact_plan(plan, staging)
    os.replace(destination, backup)
    campaign_publish_module._move_preserved(backup, staging, plan.preserve)
    os.replace(staging, destination)
    recovery = campaign_publish_module._receipt(plan, phase="prepared")
    recovery.update(
        {
            "staging": str(staging),
            "backup": str(backup),
            "failed_destination": str(failed),
            "had_destination": True,
        }
    )
    (run_dir / "publication.pending.json").write_text(
        json.dumps(recovery), encoding="utf-8"
    )

    recovered_plan = plan_publication(run_dir)

    assert recovered_plan.artifacts == plan.artifacts
    assert recovered_plan.destination == plan.destination
    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert (destination / ".lake/cache.bin").read_text(encoding="utf-8") == (
        "retained\n"
    )
    assert not staging.exists()
    assert not backup.exists()
    assert not failed.exists()
    receipt = json.loads(
        (run_dir / "publication.pending.json").read_text(encoding="utf-8")
    )
    assert receipt["phase"] == "rolled_back"
    assert verify_evidence_index(run_dir)


@pytest.mark.parametrize(
    ("tamper", "error"),
    [
        ("missing_field", "invalid structure"),
        ("digest_mismatch", "digest is invalid"),
        ("had_destination", "recovery identity"),
    ],
)
def test_pending_publication_preflight_rejects_tampering_without_mutation(
    tmp_path: Path,
    tamper: str,
    error: str,
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    old = destination / "old.txt"
    old.write_text("old\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    token = "fedcba654321"
    staging = destination.parent / f".{destination.name}.publish-{token}"
    backup = destination.parent / f".{destination.name}.previous-{token}"
    failed = destination.parent / f".{destination.name}.failed-{token}"
    campaign_publish_module._copy_exact_plan(plan, staging)
    recovery = campaign_publish_module._receipt(plan, phase="prepared")
    recovery.update(
        {
            "staging": str(staging),
            "backup": str(backup),
            "failed_destination": str(failed),
            "had_destination": True,
        }
    )
    if tamper == "missing_field":
        del recovery["source"]
    elif tamper == "digest_mismatch":
        recovery["campaign_id"] = "tampered-campaign"
    else:
        recovery["had_destination"] = False
    pending = run_dir / "publication.pending.json"
    pending.write_text(json.dumps(recovery), encoding="utf-8")
    destination_before = old.read_bytes()
    staging_before = (staging / "new.txt").read_bytes()
    evidence_before = (run_dir / "evidence.json").read_bytes()
    pending_before = pending.read_bytes()

    with pytest.raises(CampaignRunError, match=error):
        plan_publication(run_dir)

    assert old.read_bytes() == destination_before
    assert (staging / "new.txt").read_bytes() == staging_before
    assert not backup.exists()
    assert not failed.exists()
    assert (run_dir / "evidence.json").read_bytes() == evidence_before
    assert pending.read_bytes() == pending_before
    assert not (run_dir / "publication.json").exists()


def _write_terminal_publication_recovery(
    run_dir: Path,
    plan: campaign_publish_module.PublicationPlan,
    *,
    phase: str,
) -> tuple[Path, Path, Path]:
    token = "123456abcdef"
    destination = plan.destination
    staging = destination.parent / f".{destination.name}.publish-{token}"
    backup = destination.parent / f".{destination.name}.previous-{token}"
    failed = destination.parent / f".{destination.name}.failed-{token}"
    for remnant in (staging, backup, failed):
        remnant.mkdir()
        (remnant / "remnant.txt").write_text("safe to clean\n", encoding="utf-8")
    receipt = campaign_publish_module._receipt(plan, phase=phase)
    recovery = {
        **receipt,
        "staging": str(staging),
        "backup": str(backup),
        "failed_destination": str(failed),
        "had_destination": True,
    }
    (run_dir / "publication.json").write_text(json.dumps(receipt), encoding="utf-8")
    (run_dir / "publication.pending.json").write_text(
        json.dumps(recovery), encoding="utf-8"
    )
    return staging, backup, failed


@pytest.mark.parametrize("phase", ["committed", "rolled_back"])
def test_terminal_publication_recovery_repairs_only_receipts_and_is_idempotent(
    tmp_path: Path, phase: str
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    remnants = _write_terminal_publication_recovery(run_dir, plan, phase=phase)

    recovered = plan_publication(run_dir)
    repaired_evidence = (run_dir / "evidence.json").read_bytes()

    assert verify_evidence_index(run_dir)
    assert all(not path.exists() for path in remnants)
    assert plan_publication(run_dir).digest == recovered.digest
    assert (run_dir / "evidence.json").read_bytes() == repaired_evidence


@pytest.mark.parametrize("phase", ["committed", "rolled_back"])
def test_terminal_publication_recovery_refuses_unrelated_evidence_drift(
    tmp_path: Path, phase: str
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    remnants = _write_terminal_publication_recovery(run_dir, plan, phase=phase)
    evidence_before = (run_dir / "evidence.json").read_bytes()
    (run_dir / "unrelated.txt").write_text("unapproved drift\n", encoding="utf-8")

    with pytest.raises(CampaignRunError, match="cannot repair publication evidence"):
        plan_publication(run_dir)

    assert (run_dir / "evidence.json").read_bytes() == evidence_before
    assert all(path.exists() for path in remnants)


@pytest.mark.parametrize("entry_kind", ["symlink", "fifo", "nested_symlink"])
def test_publication_rejects_irregular_preserved_entries_before_mutation(
    tmp_path: Path, entry_kind: str
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    preserved = destination / ".lake"
    if entry_kind == "symlink":
        target = tmp_path / "outside-cache"
        target.mkdir()
        preserved.symlink_to(target, target_is_directory=True)
    elif entry_kind == "fifo":
        os.mkfifo(preserved)
    else:
        preserved.mkdir()
        target = tmp_path / "outside-cache"
        target.mkdir()
        (preserved / "linked").symlink_to(target, target_is_directory=True)

    with pytest.raises(CampaignRunError, match="symlink|special entry"):
        plan_publication(run_dir)

    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert not (run_dir / "publication.pending.json").exists()


def test_publication_rechecks_preserved_entry_type_immediately_before_swap(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    preserved = destination / ".lake"
    preserved.mkdir()
    plan = plan_publication(run_dir)
    assert plan.preserved_entries == ((".lake", "directory"),)
    original_copy = campaign_publish_module._copy_exact_plan

    def copy_then_change_preserved_type(
        approved: campaign_publish_module.PublicationPlan, staging: Path
    ) -> None:
        original_copy(approved, staging)
        preserved.rmdir()
        preserved.write_text("changed type\n", encoding="utf-8")

    monkeypatch.setattr(
        campaign_publish_module, "_copy_exact_plan", copy_then_change_preserved_type
    )

    with pytest.raises(CampaignRunError, match="entry type changed"):
        publish_campaign(run_dir, plan.digest)

    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"


def test_publication_fsyncs_complete_staging_before_prepared_receipt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    nested = run_dir / "final-proof" / "nested"
    nested.mkdir()
    (nested / "proof.txt").write_text("nested proof\n", encoding="utf-8")
    refresh_campaign_evidence(run_dir)
    plan = plan_publication(run_dir)
    durability_calls: list[tuple[str, Path]] = []
    original_atomic_write_json = campaign_publish_module.atomic_write_json

    def record_file_fsync(path: Path) -> None:
        durability_calls.append(("file", path))

    def record_directory_fsync(path: Path) -> None:
        durability_calls.append(("directory", path))

    def crash_at_prepared_receipt(path: Path, value: object) -> None:
        if (
            path == run_dir / "publication.pending.json"
            and isinstance(value, dict)
            and value.get("phase") == "prepared"
        ):
            staging = Path(value["staging"])
            assert {
                staging / "new.txt",
                staging / "nested" / "proof.txt",
            } == {
                called_path for kind, called_path in durability_calls if kind == "file"
            }
            assert {
                staging / "nested",
                staging,
                destination.parent,
            }.issubset(
                {
                    called_path
                    for kind, called_path in durability_calls
                    if kind == "directory"
                }
            )
            raise KeyboardInterrupt("injected crash before prepared receipt")
        original_atomic_write_json(path, value)

    monkeypatch.setattr(
        campaign_publish_module, "_fsync_regular_file", record_file_fsync
    )
    monkeypatch.setattr(
        campaign_publish_module, "_fsync_directory", record_directory_fsync
    )
    monkeypatch.setattr(
        campaign_publish_module, "atomic_write_json", crash_at_prepared_receipt
    )

    with pytest.raises(KeyboardInterrupt, match="injected crash"):
        publish_campaign(run_dir, plan.digest)

    assert not destination.exists()
    assert not (run_dir / "publication.pending.json").exists()


def test_publication_cleanup_interrupt_after_commit_never_rolls_back(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    original_remove_path = campaign_publish_module._remove_path

    def interrupt_backup_cleanup(path: Path) -> None:
        if path.name.startswith(f".{destination.name}.previous-"):
            raise KeyboardInterrupt("injected committed cleanup interruption")
        original_remove_path(path)

    monkeypatch.setattr(
        campaign_publish_module, "_remove_path", interrupt_backup_cleanup
    )

    with pytest.raises(KeyboardInterrupt, match="committed cleanup"):
        publish_campaign(run_dir, plan.digest)

    receipt = json.loads((run_dir / "publication.json").read_text(encoding="utf-8"))
    recovery = json.loads(
        (run_dir / "publication.pending.json").read_text(encoding="utf-8")
    )
    backup = Path(recovery["backup"])
    assert receipt["phase"] == "committed"
    assert recovery["phase"] == "committed"
    assert (destination / "new.txt").read_text(encoding="utf-8") == "replacement\n"
    assert not (destination / "old.txt").exists()
    assert backup.exists()

    monkeypatch.setattr(campaign_publish_module, "_remove_path", original_remove_path)
    recovered = plan_publication(run_dir)

    assert recovered.destination == destination
    assert not backup.exists()
    assert (destination / "new.txt").read_text(encoding="utf-8") == "replacement\n"
    assert plan_publication(run_dir).digest == recovered.digest


def test_rollback_recovery_fsyncs_preserved_moves_before_terminal_receipt(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    run_dir, destination = _publication_run(tmp_path)
    destination.mkdir()
    (destination / "old.txt").write_text("old\n", encoding="utf-8")
    cache = destination / ".lake"
    cache.mkdir()
    (cache / "cache.bin").write_text("retained\n", encoding="utf-8")
    plan = plan_publication(run_dir)
    token = "fedcba654321"
    staging = destination.parent / f".{destination.name}.publish-{token}"
    backup = destination.parent / f".{destination.name}.previous-{token}"
    failed = destination.parent / f".{destination.name}.failed-{token}"
    campaign_publish_module._copy_exact_plan(plan, staging)
    os.replace(destination, backup)
    campaign_publish_module._move_preserved(backup, staging, plan.preserve)
    os.replace(staging, destination)
    recovery = {
        **campaign_publish_module._receipt(plan, phase="prepared"),
        "staging": str(staging),
        "backup": str(backup),
        "failed_destination": str(failed),
        "had_destination": True,
    }
    (run_dir / "publication.pending.json").write_text(
        json.dumps(recovery), encoding="utf-8"
    )
    durable_directories: list[Path] = []
    original_atomic_write_json = campaign_publish_module.atomic_write_json

    def record_directory_fsync(path: Path) -> None:
        durable_directories.append(path)

    def require_durable_moves(path: Path, value: object) -> None:
        if isinstance(value, dict) and value.get("phase") == "rolled_back":
            assert destination in durable_directories
            assert backup in durable_directories
        original_atomic_write_json(path, value)

    monkeypatch.setattr(
        campaign_publish_module, "_fsync_directory", record_directory_fsync
    )
    monkeypatch.setattr(
        campaign_publish_module, "atomic_write_json", require_durable_moves
    )

    plan_publication(run_dir)

    assert (destination / "old.txt").read_text(encoding="utf-8") == "old\n"
    assert (destination / ".lake" / "cache.bin").read_text(
        encoding="utf-8"
    ) == "retained\n"


@pytest.mark.parametrize(
    ("status", "expected"),
    [
        ("complete", 0),
        ("awaiting_approval", 3),
        ("incomplete", 1),
        ("failed", 1),
        ("stopped", 1),
        ("running", 1),
    ],
)
def test_status_command_exit_codes(
    tmp_path: Path,
    capsys: pytest.CaptureFixture[str],
    status: str,
    expected: int,
) -> None:
    run_dir = tmp_path / status
    run_dir.mkdir()
    (run_dir / "state.json").write_text(
        json.dumps({"schema_version": 1, "campaign_id": "fixture", "status": status}),
        encoding="utf-8",
    )
    assert campaign_main(["status", "--run", str(run_dir)]) == expected
    assert f"campaign status: {status}" in capsys.readouterr().out


def _verified_source_run(
    path: Path,
    *,
    status: str = "complete",
    campaign_id: str = "source-campaign",
    run_id: str | None = None,
    evidence_status: str | None = None,
) -> Path:
    run_id = run_id or path.name
    path.mkdir()
    artifact = path / "final-proof"
    artifact.mkdir()
    verified = artifact / "verified.txt"
    verified.write_text("verified proof\n", encoding="utf-8")
    # Files omitted from evidence are rejected; the selected tree is exact.
    (path / "state.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "campaign_id": campaign_id,
                "run_id": run_id,
                "status": status,
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    artifacts = (
        digest_file(path / "state.json", relative_to=path),
        digest_file(verified, relative_to=path),
    )
    (path / "evidence.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "campaign_id": campaign_id,
                "status": evidence_status or status,
                "generated_at": "2026-08-01T00:00:00Z",
                "artifacts": [item.to_dict() for item in artifacts],
            },
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return path


def test_digest_tree_excludes_complete_subtrees(tmp_path: Path) -> None:
    (tmp_path / "retained").mkdir()
    (tmp_path / "retained/result.txt").write_text("result\n", encoding="utf-8")
    (tmp_path / "workspace/cache").mkdir(parents=True)
    (tmp_path / "workspace/proof.lean").write_text("proof\n", encoding="utf-8")
    (tmp_path / "workspace/cache/dependency.olean").write_bytes(b"cache")

    artifacts = digest_tree(tmp_path, exclude={"workspace"})

    assert [artifact.path for artifact in artifacts] == ["retained/result.txt"]


def test_evidence_verification_rejects_unindexed_retained_files(
    tmp_path: Path,
) -> None:
    source = _verified_source_run(tmp_path / "source-run")
    (source / "omitted.txt").write_text("not indexed\n", encoding="utf-8")

    with pytest.raises(ValueError, match="artifact set mismatch"):
        verify_evidence_index(source)


def _verified_import_manifest(tmp_path: Path, script: str) -> Path:
    _base_files(tmp_path)
    evidence_sha256 = digest_file(
        tmp_path / "source-run/evidence.json", relative_to=tmp_path / "source-run"
    ).sha256
    manifest = tmp_path / "verified-import.toml"
    manifest.write_text(
        f"""schema_version = 1
[campaign]
id = "verified-import"
title = "Verified import"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "source-run"
artifact = "final-proof"
target = "proof"
strategy = "verified_artifact"
expected_campaign_id = "source-campaign"
expected_run_id = "source-run"
evidence_sha256 = "{evidence_sha256}"
[[stages]]
id = "check"
title = "Check imported proof"
mode = "build"
feature = "command"
depends_on = []
[stages.config]
argv = {json.dumps([sys.executable, "-c", script])}
cwd = "."
""",
        encoding="utf-8",
    )
    return manifest


def test_verified_artifact_import_copies_only_evidence_indexed_files(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _verified_source_run(tmp_path / "source-run")
    manifest = _verified_import_manifest(
        tmp_path,
        "from pathlib import Path; "
        "assert Path('proof/verified.txt').read_text() == 'verified proof\\n'; "
        "assert not Path('proof/unindexed.txt').exists()",
    )
    campaign = CampaignSpec.load(manifest)

    run_dir = CampaignBuilder(campaign, options=_options(tmp_path, monkeypatch)).run()

    assert campaign.inputs[0].artifact == "final-proof"
    assert campaign.inputs[0].expected_campaign_id == "source-campaign"
    assert campaign.inputs[0].expected_run_id == "source-run"
    assert campaign.inputs[0].evidence_sha256 is not None
    assert (run_dir / "workspace/proof/verified.txt").read_text(
        encoding="utf-8"
    ) == "verified proof\n"
    assert not (run_dir / "workspace/proof/unindexed.txt").exists()
    assert not (run_dir / "input-snapshot/proof/unindexed.txt").exists()
    input_manifest = json.loads(
        (run_dir / "input-manifest.json").read_text(encoding="utf-8")
    )
    assert input_manifest["inputs"][0]["strategy"] == "verified_artifact"
    assert input_manifest["inputs"][0]["expected_campaign_id"] == "source-campaign"
    assert input_manifest["inputs"][0]["expected_run_id"] == "source-run"
    assert (
        input_manifest["inputs"][0]["evidence_sha256"]
        == campaign.inputs[0].evidence_sha256
    )
    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    assert retained.inputs[0].strategy == "verified_artifact"
    assert retained.inputs[0].artifact == "final-proof"
    assert retained.inputs[0].expected_campaign_id == "source-campaign"
    assert retained.inputs[0].expected_run_id == "source-run"
    assert retained.inputs[0].evidence_sha256 == campaign.inputs[0].evidence_sha256


def test_verified_artifact_rejects_incomplete_source_before_stages(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _verified_source_run(
        tmp_path / "source-run",
        status="incomplete",
        evidence_status="complete",
    )
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )

    with pytest.raises(CampaignRunError, match="source state is not complete"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_rejects_tampered_source_before_stages(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = _verified_source_run(tmp_path / "source-run")
    (source / "final-proof/verified.txt").write_text(
        "tampered proof\n", encoding="utf-8"
    )
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )

    with pytest.raises(CampaignRunError, match="evidence artifact digest mismatch"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_rejects_indexed_symlink_ancestry(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = _verified_source_run(tmp_path / "source-run")
    linked = source / "final-proof/verified.txt"
    linked.unlink()
    (source / "linked-target.txt").write_text("linked\n", encoding="utf-8")
    linked.symlink_to(source / "linked-target.txt")
    artifacts = (
        digest_file(source / "state.json", relative_to=source),
        digest_file(linked, relative_to=source),
    )
    evidence = json.loads((source / "evidence.json").read_text(encoding="utf-8"))
    evidence["artifacts"] = [item.to_dict() for item in artifacts]
    (source / "evidence.json").write_text(
        json.dumps(evidence, sort_keys=True) + "\n", encoding="utf-8"
    )
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )

    with pytest.raises(CampaignRunError, match="symlink ancestry"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_rejects_empty_indexed_selection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _verified_source_run(tmp_path / "source-run")
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            'artifact = "final-proof"', 'artifact = "missing-proof"'
        ),
        encoding="utf-8",
    )

    with pytest.raises(CampaignRunError, match="no indexed files"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_rejects_mismatched_campaign_pin_before_stages(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _verified_source_run(tmp_path / "source-run")
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            'expected_campaign_id = "source-campaign"',
            'expected_campaign_id = "other-campaign"',
        ),
        encoding="utf-8",
    )

    with pytest.raises(CampaignRunError, match="evidence campaign ID"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_rejects_mismatched_run_pin_before_stages(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _verified_source_run(tmp_path / "source-run")
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(
            'expected_run_id = "source-run"',
            'expected_run_id = "other-run"',
        ),
        encoding="utf-8",
    )

    with pytest.raises(CampaignRunError, match="source directory"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_rejects_mismatched_evidence_digest_before_stages(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = _verified_source_run(tmp_path / "source-run")
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )
    observed = digest_file(source / "evidence.json", relative_to=source).sha256
    manifest.write_text(
        manifest.read_text(encoding="utf-8").replace(observed, "0" * 64),
        encoding="utf-8",
    )

    with pytest.raises(CampaignRunError, match="evidence SHA-256"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


@pytest.mark.parametrize(
    ("field", "replacement", "message"),
    [
        ("campaign_id", "rewritten-campaign", "state campaign ID"),
        ("run_id", "rewritten-run", "state run ID"),
    ],
)
def test_verified_artifact_rejects_mismatched_indexed_state_identity(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    replacement: str,
    message: str,
) -> None:
    source = _verified_source_run(tmp_path / "source-run")
    state_path = source / "state.json"
    state = json.loads(state_path.read_text(encoding="utf-8"))
    state[field] = replacement
    state_path.write_text(json.dumps(state, sort_keys=True) + "\n", encoding="utf-8")
    evidence_path = source / "evidence.json"
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    evidence["artifacts"] = [
        digest_file(state_path, relative_to=source).to_dict(),
        digest_file(source / "final-proof/verified.txt", relative_to=source).to_dict(),
    ]
    evidence_path.write_text(
        json.dumps(evidence, sort_keys=True) + "\n", encoding="utf-8"
    )
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )

    with pytest.raises(CampaignRunError, match=message):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def test_verified_artifact_pin_rejects_rewritten_source_and_local_hashes(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = _verified_source_run(tmp_path / "source-run")
    marker = tmp_path / "stage-ran"
    manifest = _verified_import_manifest(
        tmp_path,
        f"from pathlib import Path; Path({str(marker)!r}).write_text('ran')",
    )
    verified = source / "final-proof/verified.txt"
    verified.write_text("rewritten proof\n", encoding="utf-8")
    evidence_path = source / "evidence.json"
    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
    evidence["artifacts"] = [
        digest_file(source / "state.json", relative_to=source).to_dict(),
        digest_file(verified, relative_to=source).to_dict(),
    ]
    evidence_path.write_text(
        json.dumps(evidence, sort_keys=True) + "\n", encoding="utf-8"
    )

    with pytest.raises(CampaignRunError, match="evidence SHA-256"):
        CampaignBuilder(
            CampaignSpec.load(manifest),
            options=_options(tmp_path, monkeypatch),
        ).run()
    assert not marker.exists()


def _retained_state_validation_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[CampaignSpec, CampaignOptions, Path]:
    _base_files(tmp_path)
    manifest = tmp_path / "retained-state-campaign.toml"
    manifest.write_text(
        f'''schema_version = 1
[campaign]
id = "retained-state-validation"
title = "Retained State Validation"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "check"
title = "Check"
mode = "build"
feature = "command"
depends_on = []
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; Path('checked').write_text('yes')"]
cwd = "."
''',
        encoding="utf-8",
    )
    campaign = CampaignSpec.load(manifest)
    options = _options(tmp_path, monkeypatch)
    return campaign, options, CampaignBuilder(campaign, options=options).run()


@pytest.mark.parametrize(
    "corruption",
    [
        "stage_ids",
        "stage_status",
        "attempts",
        "artifacts",
        "summary",
        "completion",
        "feedback",
        "run_status",
        "events",
        "revisions",
    ],
)
def test_state_projection_corruption_recovers_from_authoritative_journal(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    corruption: str,
) -> None:
    _campaign, options, run_dir = _retained_state_validation_run(tmp_path, monkeypatch)
    state_path = run_dir / "state.json"
    state = json.loads(state_path.read_text(encoding="utf-8"))
    stage = state["stages"]["check"]
    if corruption == "stage_ids":
        state["stages"]["unexpected"] = state["stages"].pop("check")
    elif corruption == "stage_status":
        stage["status"] = "unknown"
    elif corruption == "attempts":
        stage["attempts"] = True
    elif corruption == "artifacts":
        stage["artifacts"] = ["../../outside.json"]
    elif corruption == "summary":
        stage["summary"] = []
    elif corruption == "completion":
        stage["completed_at"] = 123
    elif corruption == "feedback":
        stage["feedback"] = "not-a-list"
    elif corruption == "run_status":
        state["status"] = "unknown"
    elif corruption == "events":
        state["events"] = {}
    else:
        state["revisions"] = -1
    state_path.write_text(json.dumps(state), encoding="utf-8")
    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    resumed_options = replace(options, retry_stages=("check",))
    CampaignBuilder(retained, options=resumed_options, run_dir=run_dir).resume()
    recovered = json.loads(state_path.read_text(encoding="utf-8"))

    assert recovered["status"] == "complete"
    assert recovered["stages"]["check"]["status"] == "succeeded"
    assert recovered["stages"]["check"]["attempts"] == 2
    assert load_state_snapshot(run_dir).state == recovered


def test_second_resume_cannot_mutate_a_locked_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _campaign, options, run_dir = _retained_state_validation_run(tmp_path, monkeypatch)
    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    state_path = run_dir / "state.json"
    before = state_path.read_bytes()

    with (
        campaign_run_lock(run_dir),
        pytest.raises(CampaignRunError, match="another controller"),
    ):
        CampaignBuilder(retained, options=options, run_dir=run_dir).resume()

    with campaign_run_lock(run_dir):
        pass

    assert state_path.read_bytes() == before


def test_nonancestral_build_waits_for_handoff_approval(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _base_files(tmp_path)
    marker_name = "build-ran"
    manifest = tmp_path / "nonancestral-handoff.toml"
    manifest.write_text(
        f'''schema_version = 1
[campaign]
id = "nonancestral-handoff"
title = "Nonancestral Handoff"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[handoff]
producer = "formalization_synthesizer"
artifact = "handoffs/research.json"
schema = "research-v1"
approval = "required"
[[stages]]
id = "build"
title = "Build"
mode = "build"
feature = "command"
depends_on = []
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; Path('{marker_name}').write_text('ran')"]
cwd = "."
[[stages]]
id = "research_setup"
title = "Research Setup"
mode = "research"
feature = "command"
depends_on = []
[stages.config]
argv = ["{sys.executable}", "-c", "from pathlib import Path; Path('research-ready').write_text('ready')"]
cwd = "."
[[stages]]
id = "formalization_synthesizer"
title = "Formalization Synthesizer"
mode = "research"
feature = "agent"
depends_on = ["research_setup"]
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
handoff = "handoffs/research.json"
handoff_schema = "research-v1"
''',
        encoding="utf-8",
    )
    campaign = CampaignSpec.load(manifest)
    options = _options(tmp_path, monkeypatch)
    run_dir = CampaignBuilder(campaign, options=options).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))

    assert state["status"] == "awaiting_approval"
    assert state["stages"]["build"]["status"] == "pending"
    assert state["stages"]["formalization_synthesizer"]["status"] == "succeeded"
    marker = run_dir / "workspace" / marker_name
    assert not marker.exists()

    approve_handoff(run_dir)
    assert not marker.exists()
    retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
    CampaignBuilder(retained, options=options, run_dir=run_dir).resume()

    assert marker.read_text(encoding="utf-8") == "ran"


def _copy_claim_ledger_example(tmp_path: Path) -> Path:
    source = ROOT / "examples" / "claim-ledger"
    for name in (
        "campaign.toml",
        "campaign.md",
        "proposer.md",
        "verifier.md",
        "input.txt",
    ):
        (tmp_path / name).write_bytes((source / name).read_bytes())
    return tmp_path / "campaign.toml"


def test_claim_receipt_rejects_changed_evidence_input(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _copy_claim_ledger_example(tmp_path)
    content = manifest.read_text(encoding="utf-8").replace(
        """argv = ["python", "-c", "from pathlib import Path; assert Path('input.txt').read_text(encoding='utf-8').strip()"]""",
        """argv = ["python", "-c", "from pathlib import Path; Path('input.txt').write_text('tampered by command\\\\n', encoding='utf-8')"]""",
    )
    manifest.write_text(content, encoding="utf-8")

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert state["stages"]["claim_gate"]["status"] == "failed"
    assert "evidence input changed" in state["stages"]["claim_gate"]["summary"]


def test_claim_verifier_cannot_mutate_workspace_sources(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _copy_claim_ledger_example(tmp_path)
    monkeypatch.setenv("FAKE_CAMPAIGN_MUTATE_VERIFIER", "1")

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert state["stages"]["cold_verifier"]["status"] == "failed"
    assert (
        "modified protected workspace sources"
        in state["stages"]["cold_verifier"]["summary"]
    )


def test_claim_verifier_cannot_mutate_retained_dependencies(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _copy_claim_ledger_example(tmp_path)
    monkeypatch.setenv("FAKE_CAMPAIGN_MUTATE_DEPENDENCY", "1")

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()
    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert state["stages"]["cold_verifier"]["status"] == "failed"
    stderr = (run_dir / "logs/cold_verifier-attempt-01.stderr.log").read_text(
        encoding="utf-8"
    )
    assert "Read-only file system" in stderr


def test_claim_verifier_cannot_escape_isolated_workspace(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _copy_claim_ledger_example(tmp_path)
    monkeypatch.setenv("FAKE_CAMPAIGN_ESCAPE_VERIFIER", "1")

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    assert state["stages"]["cold_verifier"]["status"] == "failed"
    stderr = (run_dir / "logs/cold_verifier-attempt-01.stderr.log").read_text(
        encoding="utf-8"
    )
    assert "FileNotFoundError" in stderr


def test_claim_ledger_closes_campaign_only_after_independent_verdict(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _base_files(tmp_path)
    manifest = tmp_path / "claim-ledger.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "claim-ledger"
title = "Claim Ledger"
instructions = "campaign.md"
runs_dir = "runs"
[[targets]]
id = "fixture_goal"
kind = "theorem"
statement = "The fixture theorem holds."
scope = "For the retained fixture."
[[obligations]]
id = "claim_closure"
description = "Freeze, check, and independently verify the fixture claim."
evidence_stages = ["claim_gate"]
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "claim_proposer"
title = "Claim Proposer"
mode = "research"
feature = "agent"
depends_on = []
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
max_time = 60
handoff = "claims/proposals.json"
handoff_schema = "claim-proposals-v1"
[[stages]]
id = "numerical_gate"
title = "Numerical Gate"
mode = "research"
feature = "command"
depends_on = ["claim_proposer"]
[stages.config]
argv = ["true"]
replayable = true
workspace_executables = true
covers_targets = ["fixture_goal"]
evidence_inputs = ["input.txt"]
[[stages]]
id = "cold_verifier"
title = "Cold Verifier"
mode = "research"
feature = "agent"
depends_on = ["claim_proposer", "numerical_gate"]
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
category = "verification"
verifier_type = "numerical"
max_time = 60
handoff = "claims/verdicts.json"
handoff_schema = "claim-verdicts-v1"
[[stages]]
id = "claim_gate"
title = "Claim Gate"
mode = "research"
feature = "claim_ledger"
depends_on = ["claim_proposer", "numerical_gate", "cold_verifier"]
required = true
failure_policy = "abort"
[stages.config]
proposals_stage = "claim_proposer"
verifier_stages = ["cold_verifier"]
receipt_stages = ["numerical_gate"]
required_targets = ["fixture_goal"]
""",
        encoding="utf-8",
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    ledger_path = next((run_dir / "stages" / "claim_gate").glob("*-claim-ledger.json"))
    ledger = json.loads(ledger_path.read_text(encoding="utf-8"))
    assert ledger["status"] == "verified"
    assert ledger["required_targets"][0]["status"] == "verified"
    assert ledger["claims"][0]["verdicts"][0]["verifier_stage"] == "cold_verifier"
    assert ledger["schema_version"] == 2
    assert ledger["claims"][0]["evidence_refs"][-1]["stage"] == "numerical_gate"
    assert verify_campaign_bundle(run_dir) > 0
    inspection = inspect_claim_ledgers(run_dir)
    assert inspection["target_summary"] == {
        "required": 1,
        "verified": 1,
        "rejected": 0,
        "blocked": 0,
    }
    assert campaign_main(["claims", "--run", str(run_dir)]) == 0
    assert '"fixture_goal"' in capsys.readouterr().out
    assert campaign_main(["status", "--run", str(run_dir)]) == 0
    assert "claim targets: 1/1 verified" in capsys.readouterr().out
    assurance = inspect_assurance(run_dir)
    assert assurance["profiles"] == ["evidence_bundle", "verifier_gated_claims"]
    claim_assurance = assurance["claim_ledgers"]
    assert isinstance(claim_assurance, dict)
    assert claim_assurance["closure_passed"] is True
    obligation_assurance = assurance["verification_obligations"]
    assert isinstance(obligation_assurance, dict)
    assert obligation_assurance["closed"] is True
    assert obligation_assurance["items"][0]["status"] == "verified"
    final_report = assurance["final_report"]
    assert isinstance(final_report, dict)
    assert final_report["obligation_coverage"] == "closed"
    assert assurance["mathematical_limitations"] == [
        "The global theorem is outside the retained fixture scope."
    ]
    assert assurance["assurance_gaps"] == [
        "No deterministic Lean acceptance gate is configured."
    ]
    assert campaign_main(["audit", "--run", str(run_dir)]) == 0
    assert '"verifier_gated_claims"' in capsys.readouterr().out
    assert campaign_main(["dashboard", "--run", str(run_dir)]) == 0
    dashboard = capsys.readouterr().out
    assert "claim_gate: succeeded" in dashboard
    assert "obligations: 1/1 disposed" in dashboard
    assert "limitations: 2" in dashboard
    assert (
        campaign_main(["replay", "--run", str(run_dir), "--stage", "numerical_gate"])
        == 0
    )
    replay_output = capsys.readouterr().out
    assert "verifier replay passed:" in replay_output
    replay_receipts = list((run_dir / "replays").glob("*-numerical_gate.json"))
    assert len(replay_receipts) == 1
    replay_receipt = json.loads(replay_receipts[0].read_text(encoding="utf-8"))
    assert replay_receipt["argv"] == ["true"]
    assert replay_receipt["exit_code"] == 0
    assert replay_receipt["sandbox"]["workspace_executables"] is True
    assert verify_campaign_bundle(run_dir) > 0
    (run_dir / "workspace" / "input.txt").write_text(
        "changed after receipt\n", encoding="utf-8"
    )
    with pytest.raises(CampaignRunError, match="evidence inputs changed"):
        replay_verifier_command(run_dir, "numerical_gate")


def test_claim_verifier_role_rejects_mutating_or_nonverification_agent() -> None:
    campaign = CampaignSpec.load(ROOT / "examples" / "claim-ledger" / "campaign.toml")
    verifier = campaign.by_id["cold_verifier"]
    cases = (
        ({"category": "proof"}, "explicit verification category"),
        ({"tools": ["read", "write", "bash"]}, "mutating or execution tools"),
        ({"verifier_type": "generalist"}, "verifier_type is invalid"),
    )
    for changes, message in cases:
        invalid_verifier = replace(
            verifier,
            config={**verifier.config, **changes},
        )
        invalid = replace(
            campaign,
            stages=tuple(
                invalid_verifier if stage.stage_id == verifier.stage_id else stage
                for stage in campaign.stages
            ),
        )
        with pytest.raises(ConfigurationError, match=message):
            FeatureRegistry().validate(invalid)


def test_claim_receipt_must_follow_proposal_stage() -> None:
    campaign = CampaignSpec.load(ROOT / "examples" / "claim-ledger" / "campaign.toml")
    receipt = campaign.by_id["fixture_gate"]
    invalid_receipt = replace(receipt, depends_on=())
    invalid = replace(
        campaign,
        stages=tuple(
            invalid_receipt if stage.stage_id == receipt.stage_id else stage
            for stage in campaign.stages
        ),
    )

    with pytest.raises(ConfigurationError, match="must directly depend on proposal"):
        FeatureRegistry().validate(invalid)


def test_target_covering_receipt_requires_evidence_inputs() -> None:
    campaign = CampaignSpec.load(ROOT / "examples" / "claim-ledger" / "campaign.toml")
    receipt = campaign.by_id["fixture_gate"]
    invalid_receipt = replace(
        receipt,
        config={
            key: value
            for key, value in receipt.config.items()
            if key != "evidence_inputs"
        },
    )
    invalid = replace(
        campaign,
        stages=tuple(
            invalid_receipt if stage.stage_id == receipt.stage_id else stage
            for stage in campaign.stages
        ),
    )

    with pytest.raises(ConfigurationError, match="evidence_inputs is required"):
        FeatureRegistry().validate(invalid)


def test_model_diversity_requires_distinct_verifier_lanes() -> None:
    campaign = CampaignSpec.load(ROOT / "examples" / "claim-ledger" / "campaign.toml")
    gate = campaign.by_id["claim_gate"]
    invalid_gate = replace(
        gate,
        config={**gate.config, "require_model_diversity": True},
    )
    invalid = replace(
        campaign,
        stages=tuple(
            invalid_gate if stage.stage_id == gate.stage_id else stage
            for stage in campaign.stages
        ),
    )

    with pytest.raises(ConfigurationError, match="distinct verifier model lanes"):
        FeatureRegistry().validate(invalid)


def _semantic_contract_manifest(tmp_path: Path, *, lean_declaration: str) -> Path:
    _base_files(tmp_path)
    proof = tmp_path / "proof"
    proof.mkdir()
    (proof / "lakefile.toml").write_text(
        'name = "Fixture"\nversion = "0.1.0"\n', encoding="utf-8"
    )
    (proof / "Main.lean").write_text(
        "namespace Fixture\n"
        "theorem main_theorem : True := by trivial\n"
        "theorem other_theorem : True := by trivial\n"
        "end Fixture\n",
        encoding="utf-8",
    )
    (proof / "contract.lean").write_text(
        f"import Main\n#print axioms {lean_declaration}\n", encoding="utf-8"
    )
    manifest = tmp_path / "semantic-contract.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "semantic-contract"
title = "Semantic Contract"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "proof"
target = "proof"
[[stages]]
id = "lean_gate"
title = "Lean Gate"
mode = "build"
feature = "lean_contract"
depends_on = []
[stages.config]
project = "proof"
contract = "proof/contract.lean"
allowed_axioms = ["propext", "Classical.choice", "Quot.sound"]
timeout = 30
[[stages]]
id = "semantic_reviewer"
title = "Semantic Reviewer"
mode = "build"
feature = "agent"
depends_on = ["lean_gate"]
[stages.config]
instructions = "role.md"
tools = ["read", "write"]
category = "verification"
max_time = 60
handoff = "reviews/semantic.json"
handoff_schema = "semantic-review-v1"
[[stages]]
id = "semantic_gate"
title = "Semantic Gate"
mode = "build"
feature = "semantic_contract"
depends_on = ["lean_gate", "semantic_reviewer"]
required = true
failure_policy = "abort"
[stages.config]
lean_stage = "lean_gate"
reviewer_stage = "semantic_reviewer"
declaration = "Fixture.main_theorem"
informal_statement = "Every retained fixture satisfies the theorem."
""",
        encoding="utf-8",
    )
    return manifest


def test_semantic_contract_requires_lean_and_independent_equivalence(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _semantic_contract_manifest(
        tmp_path, lean_declaration="Fixture.main_theorem"
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "complete"
    receipt_path = next((run_dir / "stages" / "semantic_gate").glob("*-semantic.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["status"] == "accepted"
    assert receipt["lean_gate"]["passed"] is True
    assert receipt["lean_gate"]["axiom_report"] == {
        "declaration": "Fixture.main_theorem",
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
    }
    assert receipt["lean_gate"]["identity_error"] is None
    assert receipt["semantic_review"]["relation"] == "equivalent"
    assurance = inspect_assurance(run_dir)
    assert assurance["profiles"] == [
        "evidence_bundle",
        "lean_checked",
        "semantically_audited_formalization",
    ]
    semantic_assurance = assurance["semantic_contracts"]
    assert isinstance(semantic_assurance, dict)
    assert semantic_assurance["formalization_assured"] is True


def test_semantic_contract_rejects_cross_declaration_substitution(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    manifest = _semantic_contract_manifest(
        tmp_path, lean_declaration="Fixture.other_theorem"
    )

    run_dir = CampaignBuilder(
        CampaignSpec.load(manifest),
        options=_options(tmp_path, monkeypatch),
    ).run()

    state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
    assert state["status"] == "incomplete"
    lean_path = next((run_dir / "stages" / "lean_gate").glob("attempt-*.json"))
    lean_receipt = json.loads(lean_path.read_text(encoding="utf-8"))
    assert lean_receipt["status"] == "passed"
    assert lean_receipt["axiom_reports"] == [
        {
            "declaration": "Fixture.other_theorem",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        }
    ]
    receipt_path = next((run_dir / "stages" / "semantic_gate").glob("*-semantic.json"))
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["status"] == "rejected"
    assert receipt["lean_gate"]["passed"] is False
    assert receipt["lean_gate"]["axiom_report"] is None
    assert "found 0" in receipt["lean_gate"]["identity_error"]
    assert receipt["semantic_review"]["declaration"] == "Fixture.main_theorem"


def test_semantic_contract_rejects_duplicate_matching_axiom_reports() -> None:
    report, issue = _matching_lean_axiom_report(
        {
            "axiom_reports": [
                {"declaration": "Fixture.main_theorem", "axioms": []},
                {"declaration": "Fixture.main_theorem", "axioms": []},
            ]
        },
        "Fixture.main_theorem",
    )

    assert report is None
    assert issue is not None
    assert "exactly one axiom report" in issue


def _promotion_retry_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[CampaignSpec, CampaignOptions, Path]:
    _base_files(tmp_path)
    manifest = tmp_path / "promotion-retry.toml"
    manifest.write_text(
        """schema_version = 1
[campaign]
id = "promotion-retry-ordering"
title = "Promotion Retry Ordering"
instructions = "campaign.md"
runs_dir = "runs"
[[inputs]]
source = "input.txt"
target = "input.txt"
[[stages]]
id = "promote"
title = "Promote"
mode = "build"
feature = "artifact_promote"
depends_on = []
[stages.config]
source = "input.txt"
destination = "accepted"
""",
        encoding="utf-8",
    )
    campaign = CampaignSpec.load(manifest)
    options = _options(tmp_path, monkeypatch)
    return campaign, options, CampaignBuilder(campaign, options=options).run()


@pytest.mark.parametrize("retry_kind", ["operator", "routed"])
def test_retry_cleanup_intent_recovers_after_pre_delete_crash(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    retry_kind: str,
) -> None:
    campaign, options, run_dir = _promotion_retry_run(tmp_path, monkeypatch)
    destination = run_dir / "accepted"
    assert destination.is_file()
    original_cleanup = CampaignBuilder._complete_pending_output_cleanup

    def crash_before_cleanup(builder: CampaignBuilder) -> None:
        if builder.state.get("pending_output_cleanup"):
            raise RuntimeError("crash before promotion cleanup")
        original_cleanup(builder)

    monkeypatch.setattr(
        CampaignBuilder, "_complete_pending_output_cleanup", crash_before_cleanup
    )
    if retry_kind == "operator":
        retained = CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir))
        with pytest.raises(RuntimeError, match="crash before promotion cleanup"):
            CampaignBuilder(
                retained,
                options=replace(options, retry_stages=("promote",)),
                run_dir=run_dir,
            ).resume()
    else:
        builder = CampaignBuilder(campaign, options=options, run_dir=run_dir)
        builder.workspace = run_dir / "workspace"
        builder.state = json.loads((run_dir / "state.json").read_text(encoding="utf-8"))
        builder.state["status"] = "running"
        builder.state["completed_at"] = None
        with pytest.raises(RuntimeError, match="crash before promotion cleanup"):
            builder._route_retry(("promote",), ("retry",), campaign.by_id["promote"])

    retained = load_state_snapshot(run_dir).state
    assert retained["status"] == "running"
    assert retained["stages"]["promote"]["status"] == "pending"
    assert retained["pending_output_cleanup"] == ["promote"]
    assert destination.is_file()

    monkeypatch.setattr(
        CampaignBuilder, "_complete_pending_output_cleanup", original_cleanup
    )
    CampaignBuilder(
        CampaignSpec.load_resolved(campaign_resolved_for_run(run_dir)),
        options=options,
        run_dir=run_dir,
    ).resume()
    recovered = load_state_snapshot(run_dir).state
    assert recovered["status"] == "complete"
    assert recovered["pending_output_cleanup"] == []
    assert destination.is_file()


def test_terminate_rechecks_start_time_after_pidfd_open_and_before_signal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    descriptor = os.open("/dev/null", os.O_RDONLY)
    observed_starts = iter(("exact-start", "reused-start"))
    opened: list[int] = []
    signaled: list[tuple[int, int]] = []

    class NeverReadyPoll:
        def register(self, _descriptor: int, _events: int) -> None:
            pass

        def poll(self, _timeout: int) -> list[tuple[int, int]]:
            return []

    def pidfd_open(pid: int) -> int:
        opened.append(pid)
        return descriptor

    monkeypatch.setattr(campaign_processes.os, "pidfd_open", pidfd_open)
    monkeypatch.setattr(
        campaign_processes, "_process_start_time", lambda _pid: next(observed_starts)
    )
    monkeypatch.setattr(campaign_processes.select, "poll", NeverReadyPoll)
    monkeypatch.setattr(
        campaign_processes.signal,
        "pidfd_send_signal",
        lambda handle, number: signaled.append((handle, number)),
    )

    campaign_processes._terminate(
        (campaign_processes._ProcessTarget(4242, "exact-start"),), 0.01
    )

    assert opened == [4242]
    assert signaled == []


def test_unregister_run_process_discards_reused_leader_identity(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "registration.json"
    path.write_text("{}\n", encoding="utf-8")
    record = RegisteredRunProcess(tmp_path, 4242, "old-start", 4242, 4242)
    monkeypatch.setattr(process_registry, "_process_path", lambda _record: path)
    monkeypatch.setattr(process_registry, "_read_process", lambda _path: record)
    monkeypatch.setattr(
        process_registry, "_process_start_time", lambda _pid: "reused-start"
    )
    monkeypatch.setattr(
        process_registry,
        "_owned_group_is_alive",
        lambda _record: pytest.fail("numeric reused group must not be consulted"),
    )

    assert process_registry.unregister_run_process(record) is True
    assert not path.exists()


def test_process_registration_prunes_dead_owner_records(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setenv(
        "AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(tmp_path / "runtime")
    )
    group_alive = [True]
    monkeypatch.setattr(
        process_registry, "_owned_group_is_alive", lambda _record: group_alive[0]
    )
    monkeypatch.setattr(
        process_registry, "_process_start_time", lambda _pid: "original-start"
    )
    monkeypatch.setattr(process_registry.os, "getpgid", lambda _pid: 4242)
    monkeypatch.setattr(process_registry.os, "getsid", lambda _pid: 4242)
    stale = register_run_process(tmp_path / "stale-run", 4242)
    assert registered_run_processes(stale.run_dir) == (stale,)

    monkeypatch.setattr(process_registry, "_process_start_time", lambda _pid: None)
    group_alive[0] = False
    process_registry._prune_dead_process_registrations()

    assert registered_run_processes(stale.run_dir) == ()


def test_unregister_waits_for_descendants_after_leader_exit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "registration.json"
    path.write_text("{}\n", encoding="utf-8")
    record = RegisteredRunProcess(tmp_path, 4242, "old-start", 4242, 4242)
    group_liveness = iter((True, True, False))
    monkeypatch.setattr(process_registry, "_process_path", lambda _record: path)
    monkeypatch.setattr(process_registry, "_read_process", lambda _path: record)
    monkeypatch.setattr(
        process_registry, "_process_start_time", lambda _pid: "old-start"
    )
    monkeypatch.setattr(
        process_registry,
        "_owned_group_is_alive",
        lambda _record: next(group_liveness),
    )
    monkeypatch.setattr(process_registry.time, "sleep", lambda _seconds: None)

    assert process_registry.unregister_run_process(record, wait_timeout=1.0) is True
    assert not path.exists()


def test_terminate_preserves_distinct_group_identities_with_same_pid(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    base_descriptor = os.open("/dev/null", os.O_RDONLY)
    live_groups = {7001, 7002}
    signaled: list[tuple[int, int]] = []

    class NeverReadyPoll:
        def register(self, _descriptor: int, _events: int) -> None:
            pass

        def poll(self, _timeout: int) -> list[tuple[int, int]]:
            return []

    monkeypatch.setattr(
        campaign_processes.os,
        "pidfd_open",
        lambda _pid: os.dup(base_descriptor),
    )
    monkeypatch.setattr(
        campaign_processes, "_process_start_time", lambda _pid: "exact-start"
    )
    monkeypatch.setattr(
        campaign_processes,
        "_group_members",
        lambda target: (
            {target.pid} if target.process_group_id in live_groups else set()
        ),
    )
    monkeypatch.setattr(campaign_processes.select, "poll", NeverReadyPoll)

    def signal_member(_descriptor: int, number: int) -> None:
        group = min(live_groups)
        signaled.append((group, number))
        live_groups.discard(group)

    monkeypatch.setattr(campaign_processes.signal, "pidfd_send_signal", signal_member)
    try:
        terminated, killed, survivors = campaign_processes._terminate(
            (
                campaign_processes._ProcessTarget(4242, "exact-start", 7001, 8001),
                campaign_processes._ProcessTarget(4242, "exact-start", 7002, 8002),
            ),
            0.01,
        )
    finally:
        os.close(base_descriptor)

    assert signaled == [(7001, signal.SIGTERM), (7002, signal.SIGTERM)]
    assert terminated == {4242}
    assert killed == set()
    assert survivors == set()


def test_terminate_never_signals_reused_group_after_start_time_mismatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    descriptor = os.open("/dev/null", os.O_RDONLY)
    group_scans: list[int] = []
    group_signals: list[tuple[int, int]] = []
    monkeypatch.setattr(campaign_processes.os, "pidfd_open", lambda _pid: descriptor)
    monkeypatch.setattr(
        campaign_processes, "_process_start_time", lambda _pid: "reused-start"
    )
    monkeypatch.setattr(
        campaign_processes,
        "_group_members",
        lambda target: group_scans.append(target.process_group_id) or {target.pid},
    )
    monkeypatch.setattr(
        campaign_processes.os,
        "killpg",
        lambda group, number: group_signals.append((group, number)),
    )

    terminated, killed, survivors = campaign_processes._terminate(
        (campaign_processes._ProcessTarget(4242, "old-start", 4242, 4242),),
        0.01,
    )

    assert group_scans == []
    assert group_signals == []
    assert terminated == {4242}
    assert killed == set()
    assert survivors == set()


def test_crash_recovery_reports_unverifiable_orphaned_group_without_signaling(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    runtime_dir = tmp_path / "runtime"
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    worker_pid_path = tmp_path / "worker-pid"
    marker = tmp_path / "worker-survived"
    monkeypatch.setenv("AGENTIC_LEAN_MATH_ASSISTANT_RUNTIME_DIR", str(runtime_dir))
    leader = subprocess.Popen(
        [
            sys.executable,
            "-c",
            (
                "import os,time\nfrom pathlib import Path\nworker=os.fork()\n"
                "if worker == 0:\n time.sleep(0.8)\n"
                f" Path({str(marker)!r}).write_text('survived', encoding='utf-8')\n"
                " time.sleep(60)\n raise SystemExit\n"
                f"Path({str(worker_pid_path)!r}).write_text(str(worker), encoding='utf-8')\n"
                "time.sleep(60)\n"
            ),
        ],
        start_new_session=True,
    )
    record = register_run_process(run_dir, leader.pid)
    deadline = time.monotonic() + 5
    while not worker_pid_path.exists() and time.monotonic() < deadline:
        time.sleep(0.02)
    assert worker_pid_path.exists()
    worker_pid = int(worker_pid_path.read_text(encoding="utf-8"))
    try:
        os.kill(leader.pid, signal.SIGKILL)
        leader.wait(timeout=5)
        report = terminate_run_processes(run_dir, terminate_timeout=0.2)
        time.sleep(0.9)
        assert not report.ok
        assert report.surviving_pids == (record.pid,)
        assert marker.is_file()
        assert campaign_processes._is_alive(worker_pid)
        assert registered_run_processes(run_dir) == (record,)
    finally:
        try:
            os.killpg(record.process_group_id, signal.SIGKILL)
        except ProcessLookupError:
            pass


def test_group_signal_permission_denied_remains_survivor(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    descriptor = os.open("/dev/null", os.O_RDONLY)
    record = RegisteredRunProcess(tmp_path, 4242, "exact-start", 4242, 4242)

    class NeverReadyPoll:
        def register(self, _descriptor: int, _events: int) -> None:
            pass

        def poll(self, _timeout: int) -> list[tuple[int, int]]:
            return []

    monkeypatch.setattr(
        campaign_processes.os, "pidfd_open", lambda _pid: os.dup(descriptor)
    )
    monkeypatch.setattr(
        campaign_processes, "_process_start_time", lambda _pid: "exact-start"
    )
    monkeypatch.setattr(campaign_processes, "_group_members", lambda _target: {4242})
    monkeypatch.setattr(campaign_processes.select, "poll", NeverReadyPoll)
    monkeypatch.setattr(
        campaign_processes.signal,
        "pidfd_send_signal",
        lambda _descriptor, _signal: (_ for _ in ()).throw(PermissionError()),
    )
    try:
        terminated, _killed, survivors = campaign_processes._terminate((record,), 0.01)
    finally:
        os.close(descriptor)
    assert terminated == set()
    assert survivors == {4242}


def test_pidfd_resource_exhaustion_blocks_process_recovery(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    record = RegisteredRunProcess(tmp_path, 4242, "exact-start", 4242, 4242)
    monkeypatch.setattr(
        campaign_processes.os,
        "pidfd_open",
        lambda _pid: (_ for _ in ()).throw(OSError(errno.EMFILE, "too many files")),
    )
    terminated, killed, survivors = campaign_processes._terminate((record,), 0.01)
    assert terminated == set()
    assert killed == set()
    assert survivors == {4242}


def test_resume_closes_workspace_matching_durable_creation_intent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    campaign, options, run_dir = _retained_state_validation_run(tmp_path, monkeypatch)
    label = "campaign:retained-state-validation:crash-intent"
    leaked = HerdrClient(options.herdr).create_workspace(
        cwd=run_dir / "workspace",
        label=label,
        focus=False,
    )
    state = load_state_snapshot(run_dir).state
    state["herdr_creation_label"] = label
    append_state_snapshot(run_dir, state, reason="test:workspace-creation-intent")
    (run_dir / "state.json").write_text(json.dumps(state), encoding="utf-8")

    CampaignBuilder(campaign, options=options, run_dir=run_dir).resume()

    fake_state = json.loads(
        Path(os.environ["FAKE_HERDR_STATE"]).read_text(encoding="utf-8")
    )
    assert leaked.workspace_id not in fake_state["workspaces"]
    recovered = load_state_snapshot(run_dir).state
    assert recovered["herdr_creation_label"] is None
    assert recovered["herdr_closed"] is True
