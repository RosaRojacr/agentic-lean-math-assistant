from __future__ import annotations

import pytest

from agentic_lean_math_assistant.config import ConfigurationError
from agentic_lean_math_assistant.forecast import (
    CompletionForecast,
    RuntimeQuantiles,
    predicted_limit_breached,
)


def _forecast(**overrides: object) -> CompletionForecast:
    value: dict[str, object] = {
        "schema_version": 1,
        "assessment": "progressing",
        "completion_probability": 0.6,
        "current_result_publishable": False,
        "strongest_verified_result_summary": None,
        "strongest_verified_roots": [],
        "next_publishable_runtime_seconds": {"p50": 100, "p80": 200, "p95": 300},
        "complete_solution_runtime_seconds": {"p50": 400, "p80": 500, "p95": 600},
        "confidence": "medium",
        "evidence_quality": "sufficient",
        "verified_progress": [],
        "critical_path": ["close the remaining theorem"],
        "blocking_risks": [],
        "reason": "The retained proof closes half of the obligations.",
        "recommended_review_after_seconds": 3600,
    }
    value.update(overrides)
    return CompletionForecast.parse(value)


def test_runtime_quantiles_are_ordered_and_selectable() -> None:
    quantiles = RuntimeQuantiles.parse({"p50": 10, "p80": 20, "p95": 30}, "runtime")

    assert quantiles.at(80) == 20
    with pytest.raises(ConfigurationError, match="nondecreasing"):
        RuntimeQuantiles.parse({"p50": 20, "p80": 10, "p95": 30}, "runtime")


def test_predicted_limit_requires_both_targets_to_exceed_limit() -> None:
    forecast = _forecast()

    assert not predicted_limit_breached(
        forecast, active_seconds=100, runtime_limit_seconds=350, percentile=80
    )
    assert predicted_limit_breached(
        forecast, active_seconds=200, runtime_limit_seconds=350, percentile=80
    )


def test_low_confidence_and_insufficient_evidence_do_not_stop() -> None:
    low = _forecast(confidence="low")
    insufficient = _forecast(
        assessment="insufficient_evidence",
        evidence_quality="insufficient",
        next_publishable_runtime_seconds=None,
        complete_solution_runtime_seconds=None,
    )

    assert not predicted_limit_breached(
        low, active_seconds=1000, runtime_limit_seconds=10, percentile=80
    )
    assert not predicted_limit_breached(
        insufficient, active_seconds=1000, runtime_limit_seconds=10, percentile=80
    )


def test_publishable_forecast_requires_verified_roots() -> None:
    with pytest.raises(ConfigurationError, match="strongest verified result"):
        _forecast(current_result_publishable=True)

    accepted = _forecast(
        current_result_publishable=True,
        strongest_verified_result_summary="A strict range reduction.",
        strongest_verified_roots=["Result.range_reduction"],
    )
    assert accepted.current_result_publishable
