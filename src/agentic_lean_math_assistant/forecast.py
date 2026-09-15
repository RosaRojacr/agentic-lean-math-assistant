"""Independent completion forecasts and controller-owned runtime policy."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Self

from .config import ConfigurationError

ForecastAssessment = Literal[
    "progressing",
    "stalled",
    "blocked",
    "complete",
    "insufficient_evidence",
]
ForecastConfidence = Literal["low", "medium", "high"]
ForecastEvidenceQuality = Literal["insufficient", "limited", "sufficient"]


@dataclass(frozen=True, slots=True)
class RuntimeQuantiles:
    p50: int
    p80: int
    p95: int

    @classmethod
    def parse(cls, value: object, label: str) -> Self:
        if not isinstance(value, dict) or set(value) != {"p50", "p80", "p95"}:
            raise ConfigurationError(f"{label} must contain exactly p50, p80, and p95")
        parsed: list[int] = []
        for name in ("p50", "p80", "p95"):
            item = value[name]
            if isinstance(item, bool) or not isinstance(item, int) or item < 0:
                raise ConfigurationError(
                    f"{label}.{name} must be a nonnegative integer"
                )
            parsed.append(item)
        if parsed != sorted(parsed):
            raise ConfigurationError(f"{label} quantiles must be nondecreasing")
        return cls(*parsed)

    def at(self, percentile: int) -> int:
        if percentile == 50:
            return self.p50
        if percentile == 80:
            return self.p80
        if percentile == 95:
            return self.p95
        raise ValueError(f"unsupported forecast percentile: {percentile}")

    def to_dict(self) -> dict[str, int]:
        return {"p50": self.p50, "p80": self.p80, "p95": self.p95}


@dataclass(frozen=True, slots=True)
class CompletionForecast:
    assessment: ForecastAssessment
    completion_probability: float | None
    current_result_publishable: bool
    strongest_verified_result_summary: str | None
    strongest_verified_roots: tuple[str, ...]
    next_publishable_runtime: RuntimeQuantiles | None
    complete_solution_runtime: RuntimeQuantiles | None
    confidence: ForecastConfidence
    evidence_quality: ForecastEvidenceQuality
    verified_progress: tuple[str, ...]
    critical_path: tuple[str, ...]
    blocking_risks: tuple[str, ...]
    reason: str
    recommended_review_after_seconds: int

    @classmethod
    def parse(cls, value: object) -> Self:
        if not isinstance(value, dict):
            raise ConfigurationError("completion forecast must be an object")
        required = {
            "schema_version",
            "assessment",
            "completion_probability",
            "current_result_publishable",
            "strongest_verified_result_summary",
            "strongest_verified_roots",
            "next_publishable_runtime_seconds",
            "complete_solution_runtime_seconds",
            "confidence",
            "evidence_quality",
            "verified_progress",
            "critical_path",
            "blocking_risks",
            "reason",
            "recommended_review_after_seconds",
        }
        if set(value) != required:
            raise ConfigurationError(
                "completion forecast keys differ; "
                f"missing={sorted(required - value.keys())}, "
                f"extra={sorted(value.keys() - required)}"
            )
        if value["schema_version"] != 1:
            raise ConfigurationError("completion forecast schema_version must be 1")
        assessment = value["assessment"]
        if assessment not in {
            "progressing",
            "stalled",
            "blocked",
            "complete",
            "insufficient_evidence",
        }:
            raise ConfigurationError("completion forecast assessment is invalid")
        probability = value["completion_probability"]
        if probability is not None and (
            isinstance(probability, bool)
            or not isinstance(probability, (int, float))
            or not 0 <= float(probability) <= 1
        ):
            raise ConfigurationError(
                "completion forecast completion_probability must be null or in [0, 1]"
            )
        publishable = value["current_result_publishable"]
        if not isinstance(publishable, bool):
            raise ConfigurationError(
                "completion forecast current_result_publishable must be boolean"
            )
        summary = value["strongest_verified_result_summary"]
        if summary is not None and (
            not isinstance(summary, str) or not summary.strip()
        ):
            raise ConfigurationError(
                "completion forecast strongest_verified_result_summary must be null or text"
            )
        roots = _text_array(value["strongest_verified_roots"], "strongest roots")
        if (summary is None) != (not roots):
            raise ConfigurationError(
                "a strongest verified result requires both a summary and roots"
            )
        if publishable and (summary is None or not roots):
            raise ConfigurationError(
                "a publishable forecast requires a strongest verified result"
            )
        confidence = value["confidence"]
        if confidence not in {"low", "medium", "high"}:
            raise ConfigurationError("completion forecast confidence is invalid")
        evidence_quality = value["evidence_quality"]
        if evidence_quality not in {"insufficient", "limited", "sufficient"}:
            raise ConfigurationError("completion forecast evidence_quality is invalid")
        reason = value["reason"]
        if not isinstance(reason, str) or not reason.strip():
            raise ConfigurationError("completion forecast reason must be nonempty text")
        review_after = value["recommended_review_after_seconds"]
        if (
            isinstance(review_after, bool)
            or not isinstance(review_after, int)
            or not 60 <= review_after <= 604_800
        ):
            raise ConfigurationError(
                "completion forecast recommended_review_after_seconds must be between 60 and 604800"
            )
        next_runtime = _optional_quantiles(
            value["next_publishable_runtime_seconds"], "next publishable runtime"
        )
        complete_runtime = _optional_quantiles(
            value["complete_solution_runtime_seconds"], "complete solution runtime"
        )
        if assessment == "insufficient_evidence" and (
            next_runtime is not None or complete_runtime is not None
        ):
            raise ConfigurationError(
                "an insufficient-evidence forecast cannot supply runtime estimates"
            )
        return cls(
            assessment=assessment,
            completion_probability=(
                None if probability is None else float(probability)
            ),
            current_result_publishable=publishable,
            strongest_verified_result_summary=(
                None if summary is None else summary.strip()
            ),
            strongest_verified_roots=roots,
            next_publishable_runtime=next_runtime,
            complete_solution_runtime=complete_runtime,
            confidence=confidence,
            evidence_quality=evidence_quality,
            verified_progress=_text_array(
                value["verified_progress"], "verified progress"
            ),
            critical_path=_text_array(value["critical_path"], "critical path"),
            blocking_risks=_text_array(value["blocking_risks"], "blocking risks"),
            reason=reason.strip(),
            recommended_review_after_seconds=review_after,
        )

    def projected_total_seconds(
        self, active_seconds: int, percentile: int
    ) -> dict[str, int | None]:
        return {
            "next_publishable": (
                None
                if self.next_publishable_runtime is None
                else active_seconds + self.next_publishable_runtime.at(percentile)
            ),
            "complete_solution": (
                None
                if self.complete_solution_runtime is None
                else active_seconds + self.complete_solution_runtime.at(percentile)
            ),
        }

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": 1,
            "assessment": self.assessment,
            "completion_probability": self.completion_probability,
            "current_result_publishable": self.current_result_publishable,
            "strongest_verified_result_summary": self.strongest_verified_result_summary,
            "strongest_verified_roots": list(self.strongest_verified_roots),
            "next_publishable_runtime_seconds": (
                None
                if self.next_publishable_runtime is None
                else self.next_publishable_runtime.to_dict()
            ),
            "complete_solution_runtime_seconds": (
                None
                if self.complete_solution_runtime is None
                else self.complete_solution_runtime.to_dict()
            ),
            "confidence": self.confidence,
            "evidence_quality": self.evidence_quality,
            "verified_progress": list(self.verified_progress),
            "critical_path": list(self.critical_path),
            "blocking_risks": list(self.blocking_risks),
            "reason": self.reason,
            "recommended_review_after_seconds": self.recommended_review_after_seconds,
        }


def predicted_limit_breached(
    forecast: CompletionForecast,
    *,
    active_seconds: int,
    runtime_limit_seconds: int,
    percentile: int,
) -> bool:
    """Return true only when neither useful forecast target fits the total limit."""

    if forecast.evidence_quality == "insufficient" or forecast.confidence == "low":
        return False
    totals = forecast.projected_total_seconds(active_seconds, percentile)
    candidates = [value for value in totals.values() if value is not None]
    return bool(candidates) and all(
        value > runtime_limit_seconds for value in candidates
    )


def _optional_quantiles(value: object, label: str) -> RuntimeQuantiles | None:
    if value is None:
        return None
    return RuntimeQuantiles.parse(value, label)


def _text_array(value: object, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item.strip() for item in value
    ):
        raise ConfigurationError(f"completion forecast {label} must be a text array")
    return tuple(item.strip() for item in value)
