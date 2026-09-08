from __future__ import annotations

from importlib.metadata import version

import pytest

from agentic_lean_math_assistant import __version__
from agentic_lean_math_assistant.cli import main


def test_public_version_matches_distribution_metadata() -> None:
    assert __version__ == version("agentic-lean-math-assistant")


def test_cli_reports_release_version(capsys: pytest.CaptureFixture[str]) -> None:
    with pytest.raises(SystemExit) as raised:
        main(["--version"])

    assert raised.value.code == 0
    assert capsys.readouterr().out == f"agentic-lean-math-assistant {__version__}\n"
