from __future__ import annotations

from pathlib import Path

import pytest

from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.project import ProjectSpec


def write_project(
    tmp_path: Path, *, input_target: str = "proof", execution: str = ""
) -> Path:
    (tmp_path / "problem.md").write_text("# Problem\n\nProve it.\n", encoding="utf-8")
    (tmp_path / "references").mkdir()
    (tmp_path / "knowledge").mkdir()
    (tmp_path / "proof").mkdir()
    manifest = tmp_path / "project.toml"
    manifest.write_text(
        f'''schema_version = 1
{execution}
[project]
id = "example-problem"
title = "Example Problem"
problem = "problem.md"
references = "references"
knowledge = "knowledge"
runs = "runs"
[regime]
max_tasks = 4
max_parallel = 2
allowed_tools = ["read", "write"]
[[inputs]]
path = "proof"
target = "{input_target}"
''',
        encoding="utf-8",
    )
    return manifest


def test_project_spec_resolves_owned_paths_and_defaults(tmp_path: Path) -> None:
    project = ProjectSpec.load(write_project(tmp_path))

    assert project.root == tmp_path.resolve()
    assert project.problem_path == (tmp_path / "problem.md").resolve()
    assert project.runs_dir == (tmp_path / "runs").resolve()
    assert project.max_tasks == 4
    assert project.max_parallel == 2
    assert project.max_restarts == 1
    assert project.inputs[0].target == "proof"
    assert project.execution.sandbox is True
    assert project.execution.network is False


def test_project_spec_loads_explicit_execution_policy(tmp_path: Path) -> None:
    project = ProjectSpec.load(
        write_project(
            tmp_path,
            execution="""[execution]
sandbox = false
network = true
memory_max_mb = 8192
""",
        )
    )

    assert project.execution.sandbox is False
    assert project.execution.network is True
    assert project.execution.memory_max_mb == 8192


def test_project_spec_loads_autorun_policy_and_trusted_metrics(
    tmp_path: Path,
) -> None:
    project = ProjectSpec.load(
        write_project(
            tmp_path,
            execution="""[autorun]
worthwhile_likelihood_threshold = 42
strategy_horizon_rounds = 9
adjudication_minutes = 7

[[autorun.progress_metrics]]
id = "coverage"
command = ["python3", "metric.py"]
timeout = 45
""",
        )
    )

    assert project.autorun.worthwhile_likelihood_threshold == 42
    assert project.autorun.strategy_horizon_rounds == 9
    assert project.autorun.adjudication_minutes == 7
    assert project.autorun.progress_metrics[0].metric_id == "coverage"
    assert project.autorun.progress_metrics[0].command == ("python3", "metric.py")
    assert project.autorun.progress_metrics[0].timeout == 45


def test_project_spec_rejects_reserved_input_target(tmp_path: Path) -> None:
    with pytest.raises(ConfigurationError, match="reserved target"):
        ProjectSpec.load(write_project(tmp_path, input_target="knowledge"))
