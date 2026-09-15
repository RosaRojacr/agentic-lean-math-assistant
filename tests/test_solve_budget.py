from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

from agentic_lean_math_assistant.agent_runner import execute
from agentic_lean_math_assistant.solve_budget import (
    SolveBudgetExceeded,
    admit_nested_model_call,
    initialize_solve_budget,
    solve_budget_environment,
    solve_budget_model_calls,
)


def test_nested_admission_clamps_time_and_enforces_model_call_limit(
    tmp_path: Path,
) -> None:
    budget = tmp_path / "budget.json"
    initialize_solve_budget(
        budget,
        remaining_seconds=200,
        max_model_calls=2,
        model_calls=0,
        now=1_000,
    )
    environment = {"ALMA_SOLVE_BUDGET": str(budget)}

    first = admit_nested_model_call(300, now=1_010, environment=environment)
    second = admit_nested_model_call(60, now=1_020, environment=environment)

    assert first.max_time == 130
    assert first.model_call == 1
    assert first.remaining_seconds == 190
    assert second.max_time == 60
    assert second.model_call == 2
    assert solve_budget_model_calls(budget) == 2
    with pytest.raises(SolveBudgetExceeded, match="model-call limit reached"):
        admit_nested_model_call(60, now=1_030, environment=environment)


def test_nested_admission_rejects_call_that_cannot_fit_runner_grace(
    tmp_path: Path,
) -> None:
    budget = tmp_path / "budget.json"
    initialize_solve_budget(
        budget,
        remaining_seconds=89,
        max_model_calls=None,
        model_calls=0,
        now=1_000,
    )

    with pytest.raises(SolveBudgetExceeded, match="insufficient time"):
        admit_nested_model_call(
            30,
            now=1_000,
            environment={"ALMA_SOLVE_BUDGET": str(budget)},
        )
    assert solve_budget_model_calls(budget) == 0


def test_agent_runner_counts_each_retry_against_global_budget(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    workspace = tmp_path / "workspace"
    run_dir = tmp_path / "run"
    workspace.mkdir()
    run_dir.mkdir()
    omp = tmp_path / "blank-omp"
    omp.write_text(
        f"#!{sys.executable}\n"
        "import json\n"
        "import sys\n"
        "from pathlib import Path\n"
        "counter = Path('calls')\n"
        "counter.write_text(str(int(counter.read_text()) + 1) if counter.exists() else '1')\n"
        "Path('argv.json').write_text(json.dumps(sys.argv))\n"
        "print('   ')\n",
        encoding="utf-8",
    )
    omp.chmod(0o755)
    prompt = tmp_path / "prompt.md"
    prompt.write_text("Return useful output.\n", encoding="utf-8")
    receipt = run_dir / "receipt.json"
    request = tmp_path / "request.json"
    request.write_text(
        json.dumps(
            {
                "role_id": "budgeted_retry",
                "attempt": 1,
                "omp": str(omp),
                "workspace": str(workspace),
                "run_dir": str(run_dir),
                "prompt": str(prompt),
                "output": str(run_dir / "output.md"),
                "stdout_log": str(run_dir / "stdout.log"),
                "stderr_log": str(run_dir / "stderr.log"),
                "receipt": str(receipt),
                "tools": [],
                "model": None,
                "thinking": None,
                "max_time": 300,
                "empty_output_retries": 3,
                "execution": {"sandbox": False},
            }
        ),
        encoding="utf-8",
    )
    budget = tmp_path / "budget.json"
    initialize_solve_budget(
        budget,
        remaining_seconds=150,
        max_model_calls=1,
        model_calls=0,
        now=1_000,
    )
    monkeypatch.setattr(
        "agentic_lean_math_assistant.solve_budget.time.time", lambda: 1_000
    )
    monkeypatch.setenv("ALMA_SOLVE_BUDGET", str(budget))

    assert execute(request) == 1

    retained = json.loads(receipt.read_text(encoding="utf-8"))
    assert retained["status"] == "budget_exhausted"
    assert retained["failure_class"] == "budget_exhausted"
    assert [item["status"] for item in retained["invocations"]] == [
        "failed",
        "budget_exhausted",
    ]
    assert retained["invocations"][0]["global_model_call"] == 1
    assert retained["invocations"][1]["global_model_call"] is None
    assert (workspace / "calls").read_text(encoding="utf-8") == "1"
    assert "--max-time=90" in json.loads(
        (workspace / "argv.json").read_text(encoding="utf-8")
    )
    assert solve_budget_model_calls(budget) == 1


def test_budget_environment_restores_prior_value(tmp_path: Path) -> None:
    previous = os.environ.get("ALMA_SOLVE_BUDGET")
    os.environ["ALMA_SOLVE_BUDGET"] = "prior"
    try:
        with solve_budget_environment(tmp_path / "budget.json"):
            assert os.environ["ALMA_SOLVE_BUDGET"] == str(
                (tmp_path / "budget.json").resolve()
            )
        assert os.environ["ALMA_SOLVE_BUDGET"] == "prior"
    finally:
        if previous is None:
            os.environ.pop("ALMA_SOLVE_BUDGET", None)
        else:
            os.environ["ALMA_SOLVE_BUDGET"] = previous
