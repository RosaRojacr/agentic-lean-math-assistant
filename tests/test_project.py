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


def test_project_spec_rejects_reserved_input_target(tmp_path: Path) -> None:
    with pytest.raises(ConfigurationError, match="reserved target"):
        ProjectSpec.load(write_project(tmp_path, input_target="knowledge"))


def test_autorun_policy_defaults(tmp_path: Path) -> None:
    project = ProjectSpec.load(write_project(tmp_path))
    assert project.autorun.max_strategy_executions == 100
    assert project.autorun.adjudication_minutes == 5
    assert project.autorun.progress_metrics == ()


@pytest.mark.parametrize("value", [1, 100])
def test_autorun_max_strategy_executions_boundaries(
    tmp_path: Path, value: int
) -> None:
    project = ProjectSpec.load(
        write_project(
            tmp_path,
            execution=f"""[autorun]
max_strategy_executions = {value}
""",
        )
    )
    assert project.autorun.max_strategy_executions == value


@pytest.mark.parametrize("value", [0, 101])
def test_autorun_max_strategy_executions_rejects_out_of_bounds(
    tmp_path: Path, value: int
) -> None:
    with pytest.raises(ConfigurationError, match="max_strategy_executions"):
        ProjectSpec.load(
            write_project(
                tmp_path,
                execution=f"""[autorun]
max_strategy_executions = {value}
""",
            )
        )


def test_autorun_legacy_strategy_horizon_rounds_alias(tmp_path: Path) -> None:
    project = ProjectSpec.load(
        write_project(
            tmp_path,
            execution="""[autorun]
strategy_horizon_rounds = 9
""",
        )
    )
    assert project.autorun.max_strategy_executions == 9


def test_autorun_rejects_new_and_legacy_ceiling_keys_together(
    tmp_path: Path,
) -> None:
    with pytest.raises(ConfigurationError, match="cannot both be specified"):
        ProjectSpec.load(
            write_project(
                tmp_path,
                execution="""[autorun]
max_strategy_executions = 10
strategy_horizon_rounds = 9
""",
            )
        )


def test_autorun_rejects_worthwhile_likelihood_threshold(
    tmp_path: Path,
) -> None:
    with pytest.raises(
        ConfigurationError,
        match="delete it because strategy selection belongs to the strategy governor",
    ):
        ProjectSpec.load(
            write_project(
                tmp_path,
                execution="""[autorun]
worthwhile_likelihood_threshold = 30
""",
            )
        )


def test_autorun_progress_metric_parsing_and_duplicate_ids(
    tmp_path: Path,
) -> None:
    project = ProjectSpec.load(
        write_project(
            tmp_path,
            execution="""[autorun]
adjudication_minutes = 7
progress_metrics = [
  { id = "scope-delta", command = ["python", "metric.py"], timeout = 12 },
]
""",
        )
    )
    metric = project.autorun.progress_metrics[0]
    assert metric.metric_id == "scope-delta"
    assert metric.command == ("python", "metric.py")
    assert metric.timeout == 12
    duplicate_root = tmp_path / "duplicate"
    duplicate_root.mkdir()
    with pytest.raises(ConfigurationError, match="metric IDs must be unique"):
        ProjectSpec.load(
            write_project(
                duplicate_root,
                execution="""[autorun]
progress_metrics = [
  { id = "scope", command = ["one"] },
  { id = "scope", command = ["two"] },
]
""",
            )
        )


def test_autorun_rejects_unknown_keys(tmp_path: Path) -> None:
    with pytest.raises(ConfigurationError, match="extra"):
        ProjectSpec.load(
            write_project(
                tmp_path,
                execution="""[autorun]
unexpected_gate = 4
""",
            )
        )
