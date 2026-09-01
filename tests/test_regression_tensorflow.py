from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest

tf = pytest.importorskip(
    "tensorflow", reason="TensorFlow optional extra is not installed"
)

from agentic_lean_math_assistant.regression import RegressionConfig, fit_regression


def nonlinear_arrays(samples: int = 48) -> tuple[np.ndarray, np.ndarray]:
    first = np.linspace(-2.0, 2.0, samples)
    second = np.cos(first * 1.7)
    third = np.sin(first * 0.4) + first**2
    features = np.column_stack((first, second, third))
    targets = np.column_stack(
        (
            first**3 - 0.5 * second + third,
            np.sin(first * 2.0) + second * third,
        )
    )
    return features, targets


@pytest.mark.parametrize(
    ("activation", "loss", "optimizer"),
    [
        ("relu", "mse", "adam"),
        ("tanh", "mae", "rmsprop"),
        ("elu", "huber", "sgd"),
        ("gelu", "mse", "adam"),
        ("sigmoid", "mae", "rmsprop"),
    ],
)
def test_tensorflow_option_matrix_trains_and_retains_replayable_model(
    activation: str,
    loss: str,
    optimizer: str,
    tmp_path: Path,
) -> None:
    features, targets = nonlinear_arrays()
    output = tmp_path / f"{activation}-{loss}-{optimizer}"
    receipt_path = fit_regression(
        features,
        targets,
        RegressionConfig.parse(
            {
                "model_kind": "tensorflow_dense",
                "hidden_layers": [6],
                "activation": activation,
                "loss": loss,
                "optimizer": optimizer,
                "epochs": 1,
                "batch_size": 12,
                "learning_rate": 0.005,
                "validation_fraction": 0.25,
                "early_stopping_patience": 1,
                "seed": 101,
                "device": "cpu",
            }
        ),
        output,
    )

    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    assert receipt["backend"]["name"] == "tensorflow"
    assert receipt["backend"]["version"] == tf.__version__
    assert receipt["config"]["activation"] == activation
    assert receipt["config"]["loss"] == loss
    assert receipt["config"]["optimizer"] == optimizer
    assert {item["path"] for item in receipt["artifacts"]} == {
        "history.json",
        "model.keras",
        "validation-results.npz",
    }
    history = json.loads((output / "history.json").read_text(encoding="utf-8"))
    assert len(history["loss"]) == 1
    assert len(history["val_loss"]) == 1
    assert np.isfinite(history["loss"]).all()
    assert np.isfinite(history["val_loss"]).all()

    model = tf.keras.models.load_model(output / "model.keras")
    with np.load(output / "validation-results.npz") as retained:
        validation = retained["validation_indices"]
        scaled_features = (features[validation] - retained["feature_mean"]) / retained[
            "feature_scale"
        ]
        replayed = (
            model.predict(scaled_features, verbose=0) * retained["target_scale"]
            + retained["target_mean"]
        )
        assert replayed.shape == (12, 2)
        assert np.allclose(replayed, retained["model_prediction"], rtol=1e-6, atol=1e-6)
        assert np.isfinite(retained["model_prediction"]).all()
    model_rmse = receipt["model_metrics"]["mean_rmse"]
    baseline_rmse = receipt["baseline_metrics"]["mean_rmse"]
    assert receipt["comparison"]["model_beats_linear_baseline"] == (
        model_rmse < baseline_rmse
    )


def test_tensorflow_seed_reproduces_history_metrics_and_predictions(
    tmp_path: Path,
) -> None:
    features, targets = nonlinear_arrays()
    config = RegressionConfig.parse(
        {
            "model_kind": "tensorflow_dense",
            "hidden_layers": [8, 4],
            "activation": "tanh",
            "loss": "mse",
            "optimizer": "adam",
            "epochs": 2,
            "batch_size": 12,
            "learning_rate": 0.01,
            "validation_fraction": 0.25,
            "early_stopping_patience": 1,
            "seed": 77,
            "device": "cpu",
        }
    )
    receipts = [
        json.loads(
            fit_regression(features, targets, config, tmp_path / name).read_text(
                encoding="utf-8"
            )
        )
        for name in ("first", "second")
    ]

    assert receipts[0]["model_metrics"] == receipts[1]["model_metrics"]
    assert receipts[0]["split"] == receipts[1]["split"]
    assert (tmp_path / "first" / "history.json").read_bytes() == (
        tmp_path / "second" / "history.json"
    ).read_bytes()
    with (
        np.load(tmp_path / "first" / "validation-results.npz") as first,
        np.load(tmp_path / "second" / "validation-results.npz") as second,
    ):
        assert np.array_equal(first["model_prediction"], second["model_prediction"])
