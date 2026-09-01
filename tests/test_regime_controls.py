from __future__ import annotations

from pathlib import Path

import pytest

from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.features import _validate_retry_novelty


def test_retry_novelty_gate_retains_specific_declaration(tmp_path: Path) -> None:
    (tmp_path / "attempt-01.md").write_text(
        "# Attempt\n\nThe direct sign expansion did not close.\n", encoding="utf-8"
    )
    current = """# Attempt

## Retry novelty
- Prior limitation: The direct sign expansion left an uncontrolled remainder.
- New method: Eliminate the constraint and certify the remaining interval boxes.
- Expected new evidence: A retained interval certificate covering every box.

## Result
The certificate was produced.
"""
    (tmp_path / "attempt-02.md").write_text(current, encoding="utf-8")

    receipt = _validate_retry_novelty(current, tmp_path, 2)

    assert receipt["attempt"] == 2
    assert receipt["new_method"].startswith("Eliminate the constraint")
    assert len(str(receipt["report_sha256"])) == 64


def test_retry_novelty_gate_rejects_duplicate_report(tmp_path: Path) -> None:
    duplicate = "# Attempt\n\nNo new method.\n"
    (tmp_path / "attempt-01.md").write_text(duplicate, encoding="utf-8")
    (tmp_path / "attempt-02.md").write_text(duplicate, encoding="utf-8")

    with pytest.raises(ConfigurationError, match="identical"):
        _validate_retry_novelty(duplicate, tmp_path, 2)
