from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

import agentic_lean_math_assistant.regression as regression_module
from agentic_lean_math_assistant.cli import main
from agentic_lean_math_assistant.regression import (
    RegressionConfig,
    RegressionError,
    assess_regression,
    fit_regression,
    load_array,
    regression_capability_catalog,
)


def sample_arrays(samples: int = 60) -> tuple[np.ndarray, np.ndarray]:
    first = np.linspace(-2.0, 3.0, samples)
    second = np.sin(first) + np.linspace(0.0, 1.0, samples)
    features = np.column_stack((first, second))
    targets = np.column_stack(
        (
            2.0 * first - 3.0 * second + 1.0,
            -0.5 * first + 4.0 * second - 2.0,
        )
    )
    return features, targets


def test_assessment_is_shape_agnostic_and_deterministic() -> None:
    features, targets = sample_arrays()

    first = assess_regression(features.tolist(), targets.tolist())
    second = assess_regression(features, targets)

    assert first.samples == 60
    assert first.features == 2
    assert first.targets == 2
    assert first.recommended is True
    assert first.feature_sha256 == second.feature_sha256
    assert first.target_sha256 == second.target_sha256
    assert first.evidence_class == "exploratory_numeric_not_proof"


def test_assessment_reports_invalid_numeric_content_without_fitting() -> None:
    features, targets = sample_arrays(25)
    features[3, 0] = np.nan
    targets[:, 1] = 4.0

    assessment = assess_regression(features, targets)

    assert assessment.recommended is False
    assert assessment.nonfinite_features == 1
    assert assessment.constant_targets == (1,)
    assert any("cannot be fitted" in item for item in assessment.warnings)


def test_config_rejects_unbounded_or_unknown_settings() -> None:
    with pytest.raises(RegressionError, match="must not exceed epochs"):
        RegressionConfig.parse({"epochs": 3, "early_stopping_patience": 4})
    with pytest.raises(RegressionError, match="keys differ"):
        RegressionConfig.parse({"epochs": 3, "arbitrary_code": "yes"})
    with pytest.raises(RegressionError, match="between 1 and 6"):
        RegressionConfig.parse({"hidden_layers": []})


def test_linear_fit_retains_baseline_split_metrics_and_artifact_hashes(
    tmp_path: Path,
) -> None:
    features, targets = sample_arrays()
    config = RegressionConfig.parse(
        {
            "model_kind": "linear",
            "validation_fraction": 0.25,
            "split_method": "ordered",
            "seed": 42,
        }
    )

    first_receipt = fit_regression(features, targets, config, tmp_path / "first")
    second_receipt = fit_regression(features, targets, config, tmp_path / "second")
    first = json.loads(first_receipt.read_text(encoding="utf-8"))
    second = json.loads(second_receipt.read_text(encoding="utf-8"))

    assert first["status"] == "succeeded"
    assert first["proof_status"] == "not_proof"
    assert first["backend"]["name"] == "numpy_linear"
    assert first["split"]["validation_samples"] == 15
    assert first["split"]["method"] == "ordered"
    with np.load(tmp_path / "first" / "validation-results.npz") as retained:
        assert retained["validation_indices"].tolist() == list(range(45, 60))
    assert first["model_metrics"] == first["baseline_metrics"]
    assert first["comparison"] == {
        "criterion": "strictly lower mean held-out RMSE",
        "model_beats_linear_baseline": False,
        "selected_model": "linear_baseline",
    }
    assert first["model_metrics"]["mean_rmse"] == pytest.approx(0.0, abs=1e-12)
    assert first["model_metrics"] == second["model_metrics"]
    assert first["split"] == second["split"]
    assert {item["path"] for item in first["artifacts"]} == {
        "history.json",
        "validation-results.npz",
    }


def test_tensorflow_backend_fails_cleanly_when_optional_extra_is_absent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    features, targets = sample_arrays(25)
    original = regression_module.importlib.util.find_spec
    monkeypatch.setattr(
        regression_module.importlib.util,
        "find_spec",
        lambda name: None if name == "tensorflow" else original(name),
    )

    with pytest.raises(RegressionError, match="install the 'ml' extra"):
        fit_regression(
            features,
            targets,
            RegressionConfig.parse(
                {
                    "model_kind": "tensorflow_dense",
                    "epochs": 2,
                    "early_stopping_patience": 1,
                }
            ),
            tmp_path / "tensorflow",
        )


def test_cli_assesses_npz_arrays_and_catalog_discovers_candidates(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    features, targets = sample_arrays()
    arrays = tmp_path / "arrays.npz"
    np.savez(arrays, features=features, targets=targets)
    assessment = tmp_path / "assessment.json"

    exit_code = main(
        [
            "regression-assess",
            "--features",
            str(arrays),
            "--feature-key",
            "features",
            "--targets",
            str(arrays),
            "--target-key",
            "targets",
            "--output",
            str(assessment),
        ]
    )

    assert exit_code == 0
    assert json.loads(assessment.read_text(encoding="utf-8"))["recommended"] is True
    assert "regression recommended: true" in capsys.readouterr().out
    assert load_array(arrays, key="features").shape == (60, 2)
    catalog = regression_capability_catalog(tmp_path)
    assert catalog[0]["candidate_files"] == ["arrays.npz"]
    assert {item["id"] for item in catalog} == {
        "regression_assess",
        "regression_fit",
    }
