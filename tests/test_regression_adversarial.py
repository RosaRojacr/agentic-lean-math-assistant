from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

import numpy as np
import pytest
from hypothesis import given, settings
from hypothesis import strategies as st

import agentic_lean_math_assistant.regression as regression_module
from agentic_lean_math_assistant.cli import main
from agentic_lean_math_assistant.regression import (
    RegressionConfig,
    RegressionError,
    assess_regression,
    discover_regression_candidates,
    fit_regression,
    load_array,
)


@settings(max_examples=40, deadline=None)
@given(
    samples=st.integers(min_value=3, max_value=100),
    feature_count=st.integers(min_value=1, max_value=8),
    target_count=st.integers(min_value=1, max_value=4),
    seed=st.integers(min_value=0, max_value=2**16),
)
def test_assessment_preserves_arbitrary_valid_shapes_and_is_deterministic(
    samples: int, feature_count: int, target_count: int, seed: int
) -> None:
    generator = np.random.default_rng(seed)
    features = generator.normal(size=(samples, feature_count))
    targets = generator.normal(size=(samples, target_count))

    first = assess_regression(features, targets)
    second = assess_regression(features.tolist(), targets.tolist())

    assert (first.samples, first.features, first.targets) == (
        samples,
        feature_count,
        target_count,
    )
    assert first.feature_sha256 == second.feature_sha256
    assert first.target_sha256 == second.target_sha256
    assert first.recommended == (
        samples >= max(20, 5 * (feature_count + target_count))
        and feature_count < samples
    )


@pytest.mark.parametrize(
    ("features", "targets", "message"),
    [
        ([[1.0], [2.0]], [1.0, 2.0], "at least 3 samples"),
        ([[1.0], [2.0], [3.0]], [1.0, 2.0], "same sample count"),
        (np.zeros((3, 1, 1)), np.zeros(3), "one- or two-dimensional"),
        (["a", "b", "c"], [1.0, 2.0, 3.0], "numeric arrays"),
        (np.empty((3, 0)), np.zeros(3), "1 feature"),
        (np.zeros((3, 1)), np.empty((3, 0)), "1 target"),
    ],
)
def test_array_contract_rejects_invalid_shapes_and_types(
    features: object, targets: object, message: str
) -> None:
    with pytest.raises(RegressionError, match=message):
        assess_regression(features, targets)


@pytest.mark.parametrize(
    ("value", "message"),
    [
        ({"model_kind": "forest"}, "model_kind"),
        ({"hidden_layers": [0]}, "between 1 and 4096"),
        ({"hidden_layers": [1] * 7}, "between 1 and 6"),
        ({"epochs": True}, "must be an integer"),
        ({"epochs": 10001}, "between 1 and 10000"),
        ({"batch_size": 0}, "between 1 and 65536"),
        ({"learning_rate": float("nan")}, "between"),
        ({"validation_fraction": 0.01}, "between 0.05 and 0.5"),
        ({"split_method": "grouped"}, "split_method"),
        ({"l1": -1.0}, "between 0.0 and 10.0"),
        ({"seed": -1}, "between 0"),
        ({"device": "gpu"}, "device"),
    ],
)
def test_config_rejects_every_unbounded_or_unknown_dimension(
    value: dict[str, object], message: str
) -> None:
    with pytest.raises(RegressionError, match=message):
        RegressionConfig.parse(value)


def test_fit_revalidates_direct_dataclass_construction(tmp_path: Path) -> None:
    features = np.arange(60.0).reshape(30, 2)
    targets = np.arange(30.0)
    invalid = RegressionConfig(model_kind="linear", epochs=0)

    with pytest.raises(RegressionError, match="epochs"):
        fit_regression(features, targets, invalid, tmp_path / "fit")


def test_fit_rejects_a_negative_assessment(tmp_path: Path) -> None:
    features = np.arange(18.0).reshape(9, 2)
    targets = np.arange(9.0)
    assert assess_regression(features, targets).recommended is False

    with pytest.raises(RegressionError, match="assessment does not recommend"):
        fit_regression(
            features,
            targets,
            RegressionConfig.parse({"model_kind": "linear"}),
            tmp_path / "fit",
        )


def test_load_array_rejects_final_symlink(tmp_path: Path) -> None:
    source = tmp_path / "source.npy"
    np.save(source, np.arange(10.0))
    link = tmp_path / "link.npy"
    link.symlink_to(source)

    with pytest.raises(RegressionError, match="regular file"):
        load_array(link)


def test_output_rejects_final_symlink_without_touching_target(tmp_path: Path) -> None:
    features = np.arange(80.0).reshape(40, 2)
    targets = features[:, 0] + features[:, 1]
    target = tmp_path / "target"
    target.mkdir()
    link = tmp_path / "output"
    link.symlink_to(target, target_is_directory=True)

    with pytest.raises(RegressionError, match="regular directory"):
        fit_regression(
            features,
            targets,
            RegressionConfig.parse({"model_kind": "linear"}),
            link,
        )
    assert list(target.iterdir()) == []


def test_candidate_discovery_does_not_follow_symlink_root(tmp_path: Path) -> None:
    outside = tmp_path / "outside"
    outside.mkdir()
    np.save(outside / "secret.npy", np.arange(10.0))
    root = tmp_path / "root"
    root.symlink_to(outside, target_is_directory=True)

    assert discover_regression_candidates(root) == ()


def test_config_loader_rejects_undocumented_suffix(tmp_path: Path) -> None:
    path = tmp_path / "config.txt"
    path.write_text('{"model_kind": "linear"}', encoding="utf-8")

    with pytest.raises(RegressionError, match="must use .json or .toml"):
        RegressionConfig.load(path)


def test_loader_rejects_oversized_input_before_parsing(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "large.npy"
    path.write_bytes(b"0123456789")
    monkeypatch.setattr(regression_module, "_MAX_INPUT_BYTES", 5)

    with pytest.raises(RegressionError, match="exceeds"):
        load_array(path)


@pytest.mark.parametrize("suffix", [".npy", ".npz", ".csv", ".tsv", ".json"])
def test_loader_round_trips_every_documented_format(
    suffix: str, tmp_path: Path
) -> None:
    expected = np.arange(12.0).reshape(6, 2)
    path = tmp_path / f"array{suffix}"
    key: str | None = None
    if suffix == ".npy":
        np.save(path, expected)
    elif suffix == ".npz":
        np.savez(path, values=expected)
        key = "values"
    elif suffix == ".csv":
        np.savetxt(path, expected, delimiter=",")
    elif suffix == ".tsv":
        np.savetxt(path, expected, delimiter="\t")
    else:
        path.write_text(json.dumps(expected.tolist()), encoding="utf-8")

    assert np.array_equal(load_array(path, key=key), expected)


def test_csv_header_skip_and_npz_key_failures(tmp_path: Path) -> None:
    csv_path = tmp_path / "values.csv"
    csv_path.write_text("first,second\n1,2\n3,4\n", encoding="utf-8")
    assert load_array(csv_path, skip_rows=1).tolist() == [[1.0, 2.0], [3.0, 4.0]]
    archive = tmp_path / "arrays.npz"
    np.savez(archive, first=np.arange(3), second=np.arange(3))
    with pytest.raises(RegressionError, match="multiple arrays"):
        load_array(archive)
    with pytest.raises(RegressionError, match="is absent"):
        load_array(archive, key="missing")


def test_linear_receipt_is_self_consistent_and_uses_train_only_scaling(
    tmp_path: Path,
) -> None:
    features = np.column_stack((np.arange(40.0), np.arange(40.0) ** 2))
    targets = 2.0 * features[:, 0] - features[:, 1]
    receipt_path = fit_regression(
        features,
        targets,
        RegressionConfig.parse(
            {
                "model_kind": "linear",
                "split_method": "ordered",
                "validation_fraction": 0.25,
            }
        ),
        tmp_path / "fit",
    )
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    with np.load(tmp_path / "fit" / "validation-results.npz") as retained:
        training = retained["training_indices"]
        validation = retained["validation_indices"]
        assert set(training).isdisjoint(set(validation))
        assert sorted(np.concatenate((training, validation)).tolist()) == list(
            range(40)
        )
        assert np.array_equal(validation, np.arange(30, 40))
        assert np.allclose(retained["feature_mean"], features[:30].mean(axis=0))
        assert np.allclose(retained["actual"], targets[validation, None])
    for artifact in receipt["artifacts"]:
        artifact_path = tmp_path / "fit" / artifact["path"]
        assert artifact_path.stat().st_size == artifact["size"]
        assert (
            hashlib.sha256(artifact_path.read_bytes()).hexdigest() == artifact["sha256"]
        )


def test_random_split_seed_controls_only_the_partition(tmp_path: Path) -> None:
    features = np.column_stack((np.arange(60.0), np.sin(np.arange(60.0))))
    targets = features[:, 0] + features[:, 1]
    splits: list[list[int]] = []
    for seed in (7, 7, 8):
        output = tmp_path / f"fit-{len(splits)}"
        fit_regression(
            features,
            targets,
            RegressionConfig.parse({"model_kind": "linear", "seed": seed}),
            output,
        )
        with np.load(output / "validation-results.npz") as retained:
            splits.append(retained["validation_indices"].tolist())
    assert splits[0] == splits[1]
    assert splits[0] != splits[2]


def test_failed_backend_leaves_no_partial_output(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    features = np.arange(80.0).reshape(40, 2)
    targets = features[:, 0] + features[:, 1]
    original = regression_module.importlib.util.find_spec
    monkeypatch.setattr(
        regression_module.importlib.util,
        "find_spec",
        lambda name: None if name == "tensorflow" else original(name),
    )
    output = tmp_path / "failed"

    with pytest.raises(RegressionError, match="install the 'ml' extra"):
        fit_regression(
            features,
            targets,
            RegressionConfig.parse(
                {
                    "model_kind": "tensorflow_dense",
                    "epochs": 1,
                    "early_stopping_patience": 1,
                }
            ),
            output,
        )
    assert not output.exists()


def test_cli_negative_assessment_retains_report_and_returns_three(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    np.save(tmp_path / "features.npy", np.arange(18.0).reshape(9, 2))
    np.save(tmp_path / "targets.npy", np.arange(9.0))
    output = tmp_path / "assessment.json"

    exit_code = main(
        [
            "regression-assess",
            "--features",
            str(tmp_path / "features.npy"),
            "--targets",
            str(tmp_path / "targets.npy"),
            "--output",
            str(output),
        ]
    )

    assert exit_code == 3
    assert json.loads(output.read_text(encoding="utf-8"))["recommended"] is False
    assert "regression recommended: false" in capsys.readouterr().out


def test_receipt_tampering_is_detectable_from_retained_hashes(tmp_path: Path) -> None:
    features = np.arange(80.0).reshape(40, 2)
    targets = features[:, 0] + features[:, 1]
    receipt_path = fit_regression(
        features,
        targets,
        RegressionConfig.parse({"model_kind": "linear"}),
        tmp_path / "fit",
    )
    receipt: dict[str, Any] = json.loads(receipt_path.read_text(encoding="utf-8"))
    result = tmp_path / "fit" / "validation-results.npz"
    result.write_bytes(result.read_bytes() + b"tampered")
    retained = next(
        item for item in receipt["artifacts"] if item["path"] == result.name
    )

    assert hashlib.sha256(result.read_bytes()).hexdigest() != retained["sha256"]
