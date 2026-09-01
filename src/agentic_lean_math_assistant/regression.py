"""Bounded, array-oriented regression for exploratory campaign evidence."""

from __future__ import annotations

import hashlib
import importlib
import importlib.util
import json
import math
import os
import shutil
import tempfile
import tomllib
import zipfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Literal, Self, cast

from .artifacts import atomic_write_json, utc_now

_EVIDENCE_CLASS = "exploratory_numeric_not_proof"
_ARRAY_SUFFIXES = frozenset({".npy", ".npz", ".csv", ".tsv"})
_CAPABILITIES = ("regression_assess", "regression_fit")
_MAX_INPUT_BYTES = 512 * 1024 * 1024
_MAX_ARRAY_BYTES = 512 * 1024 * 1024


class RegressionError(ValueError):
    """Regression inputs, configuration, or optional backend are invalid."""


def _numpy() -> Any:
    try:
        return importlib.import_module("numpy")
    except ImportError as exc:
        raise RegressionError(
            "regression requires NumPy; install the 'ml' or 'research' extra"
        ) from exc


def _keys(
    value: object,
    label: str,
    required: set[str],
    optional: set[str] | None = None,
) -> dict[str, Any]:
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        raise RegressionError(f"{label} must be an object")
    allowed = required | (optional or set())
    missing = required - value.keys()
    extra = value.keys() - allowed
    if missing or extra:
        raise RegressionError(
            f"{label} keys differ; missing={sorted(missing)}, extra={sorted(extra)}"
        )
    return value


def _integer(value: object, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise RegressionError(f"{label} must be an integer")
    if not minimum <= value <= maximum:
        raise RegressionError(f"{label} must be between {minimum} and {maximum}")
    return value


def _number(value: object, label: str, minimum: float, maximum: float) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise RegressionError(f"{label} must be numeric")
    result = float(value)
    if not math.isfinite(result) or not minimum <= result <= maximum:
        raise RegressionError(f"{label} must be between {minimum} and {maximum}")
    return result


def _choice(value: object, label: str, allowed: set[str]) -> str:
    if not isinstance(value, str) or value not in allowed:
        raise RegressionError(f"{label} must be one of {sorted(allowed)}")
    return value


@dataclass(frozen=True, slots=True)
class RegressionConfig:
    """Validated, bounded training configuration supplied by a planner or agent."""

    model_kind: Literal["linear", "tensorflow_dense"] = "tensorflow_dense"
    hidden_layers: tuple[int, ...] = (128, 64)
    activation: Literal["relu", "tanh", "elu", "gelu", "sigmoid"] = "relu"
    loss: Literal["mse", "mae", "huber"] = "mse"
    optimizer: Literal["adam", "rmsprop", "sgd"] = "adam"
    epochs: int = 500
    batch_size: int = 64
    learning_rate: float = 1e-3
    validation_fraction: float = 0.2
    split_method: Literal["random", "ordered"] = "random"
    early_stopping_patience: int = 30
    l1: float = 0.0
    l2: float = 0.0
    seed: int = 1729
    device: Literal["cpu", "auto"] = "cpu"

    @classmethod
    def parse(cls, value: object) -> Self:
        table = _keys(
            value,
            "regression config",
            set(),
            {
                "model_kind",
                "hidden_layers",
                "activation",
                "loss",
                "optimizer",
                "epochs",
                "batch_size",
                "learning_rate",
                "validation_fraction",
                "split_method",
                "early_stopping_patience",
                "l1",
                "l2",
                "seed",
                "device",
            },
        )
        raw_layers = table.get("hidden_layers", [128, 64])
        if not isinstance(raw_layers, list) or not 1 <= len(raw_layers) <= 6:
            raise RegressionError("hidden_layers must contain between 1 and 6 widths")
        layers = tuple(
            _integer(width, f"hidden_layers[{index}]", 1, 4096)
            for index, width in enumerate(raw_layers)
        )
        epochs = _integer(table.get("epochs", 500), "epochs", 1, 10000)
        patience = _integer(
            table.get("early_stopping_patience", 30),
            "early_stopping_patience",
            1,
            2000,
        )
        if patience > epochs:
            raise RegressionError("early_stopping_patience must not exceed epochs")
        return cls(
            model_kind=cast(
                Literal["linear", "tensorflow_dense"],
                _choice(
                    table.get("model_kind", "tensorflow_dense"),
                    "model_kind",
                    {"linear", "tensorflow_dense"},
                ),
            ),
            hidden_layers=layers,
            activation=cast(
                Literal["relu", "tanh", "elu", "gelu", "sigmoid"],
                _choice(
                    table.get("activation", "relu"),
                    "activation",
                    {"relu", "tanh", "elu", "gelu", "sigmoid"},
                ),
            ),
            loss=cast(
                Literal["mse", "mae", "huber"],
                _choice(table.get("loss", "mse"), "loss", {"mse", "mae", "huber"}),
            ),
            optimizer=cast(
                Literal["adam", "rmsprop", "sgd"],
                _choice(
                    table.get("optimizer", "adam"),
                    "optimizer",
                    {"adam", "rmsprop", "sgd"},
                ),
            ),
            epochs=epochs,
            batch_size=_integer(table.get("batch_size", 64), "batch_size", 1, 65536),
            learning_rate=_number(
                table.get("learning_rate", 1e-3),
                "learning_rate",
                1e-8,
                1.0,
            ),
            validation_fraction=_number(
                table.get("validation_fraction", 0.2),
                "validation_fraction",
                0.05,
                0.5,
            ),
            split_method=cast(
                Literal["random", "ordered"],
                _choice(
                    table.get("split_method", "random"),
                    "split_method",
                    {"random", "ordered"},
                ),
            ),
            early_stopping_patience=patience,
            l1=_number(table.get("l1", 0.0), "l1", 0.0, 10.0),
            l2=_number(table.get("l2", 0.0), "l2", 0.0, 10.0),
            seed=_integer(table.get("seed", 1729), "seed", 0, 2**31 - 1),
            device=cast(
                Literal["cpu", "auto"],
                _choice(table.get("device", "cpu"), "device", {"cpu", "auto"}),
            ),
        )

    @classmethod
    def load(cls, path: Path) -> Self:
        requested = path.expanduser()
        suffix = requested.suffix.lower()
        if suffix not in {".json", ".toml"}:
            raise RegressionError("regression config must use .json or .toml")
        if requested.is_symlink():
            raise RegressionError("regression config must be a regular file")
        source = requested.resolve()
        if not source.is_file():
            raise RegressionError("regression config must be a regular file")
        if source.stat().st_size > _MAX_INPUT_BYTES:
            raise RegressionError("regression config exceeds the input size limit")
        try:
            raw = source.read_bytes()
            value = (
                tomllib.loads(raw.decode("utf-8"))
                if suffix == ".toml"
                else json.loads(raw)
            )
        except (
            OSError,
            UnicodeDecodeError,
            json.JSONDecodeError,
            tomllib.TOMLDecodeError,
        ) as exc:
            raise RegressionError(f"cannot read regression config: {exc}") from exc
        return cls.parse(value)


@dataclass(frozen=True, slots=True)
class RegressionAssessment:
    schema_version: int
    evidence_class: str
    samples: int
    features: int
    targets: int
    feature_dtype: str
    target_dtype: str
    feature_sha256: str
    target_sha256: str
    nonfinite_features: int
    nonfinite_targets: int
    constant_features: tuple[int, ...]
    constant_targets: tuple[int, ...]
    tensorflow_available: bool
    recommended: bool
    reasons: tuple[str, ...]
    warnings: tuple[str, ...]

    def to_dict(self) -> dict[str, object]:
        return asdict(self)


def _arrays(
    features: object, targets: object, *, require_finite: bool
) -> tuple[Any, Any]:
    np = _numpy()
    try:
        x = np.asarray(features, dtype=np.float64)
        y = np.asarray(targets, dtype=np.float64)
    except (TypeError, ValueError) as exc:
        raise RegressionError("features and targets must be numeric arrays") from exc
    if x.ndim == 1:
        x = x.reshape((-1, 1))
    if y.ndim == 1:
        y = y.reshape((-1, 1))
    if x.ndim != 2 or y.ndim != 2:
        raise RegressionError("features and targets must be one- or two-dimensional")
    if x.shape[0] != y.shape[0]:
        raise RegressionError("features and targets must have the same sample count")
    if x.shape[0] < 3 or x.shape[1] < 1 or y.shape[1] < 1:
        raise RegressionError(
            "regression requires at least 3 samples, 1 feature, and 1 target"
        )
    if x.nbytes > _MAX_ARRAY_BYTES or y.nbytes > _MAX_ARRAY_BYTES:
        raise RegressionError("numeric array exceeds the in-memory size limit")
    if require_finite and (not np.isfinite(x).all() or not np.isfinite(y).all()):
        raise RegressionError("training arrays must not contain NaN or infinity")
    return np.ascontiguousarray(x), np.ascontiguousarray(y)


def _array_digest(array: Any) -> str:
    digest = hashlib.sha256()
    digest.update(str(tuple(int(item) for item in array.shape)).encode("ascii"))
    digest.update(str(array.dtype).encode("ascii"))
    digest.update(array.tobytes(order="C"))
    return digest.hexdigest()


def assess_regression(features: object, targets: object) -> RegressionAssessment:
    """Assess array suitability without fitting or claiming mathematical truth."""

    np = _numpy()
    x, y = _arrays(features, targets, require_finite=False)
    finite_x = np.isfinite(x)
    finite_y = np.isfinite(y)
    nonfinite_x = int(x.size - int(finite_x.sum()))
    nonfinite_y = int(y.size - int(finite_y.sum()))
    constant_features = tuple(
        int(index)
        for index in range(x.shape[1])
        if finite_x[:, index].all() and np.ptp(x[:, index]) == 0
    )
    constant_targets = tuple(
        int(index)
        for index in range(y.shape[1])
        if finite_y[:, index].all() and np.ptp(y[:, index]) == 0
    )
    reasons: list[str] = []
    warnings: list[str] = []
    warnings.append(
        "sample independence cannot be inferred from arrays; use an ordered split "
        "for temporal data and skip fitting when grouped leakage cannot be excluded"
    )
    minimum_samples = max(20, 5 * (x.shape[1] + y.shape[1]))
    if x.shape[0] >= minimum_samples:
        reasons.append(
            f"sample count {x.shape[0]} meets the screening floor {minimum_samples}"
        )
    else:
        warnings.append(
            f"sample count {x.shape[0]} is below the screening floor {minimum_samples}"
        )
    if nonfinite_x or nonfinite_y:
        warnings.append(
            "arrays contain NaN or infinity and cannot be fitted as supplied"
        )
    if constant_features:
        warnings.append(f"constant feature columns: {list(constant_features)}")
    if constant_targets:
        warnings.append(f"constant target columns: {list(constant_targets)}")
    if x.shape[1] >= x.shape[0]:
        warnings.append("feature count is not smaller than sample count")
    recommended = (
        x.shape[0] >= minimum_samples
        and nonfinite_x == 0
        and nonfinite_y == 0
        and not constant_targets
        and x.shape[1] < x.shape[0]
    )
    if recommended:
        reasons.append(
            "held-out regression is numerically feasible; run a linear baseline first"
        )
    return RegressionAssessment(
        schema_version=1,
        evidence_class=_EVIDENCE_CLASS,
        samples=int(x.shape[0]),
        features=int(x.shape[1]),
        targets=int(y.shape[1]),
        feature_dtype=str(x.dtype),
        target_dtype=str(y.dtype),
        feature_sha256=_array_digest(x),
        target_sha256=_array_digest(y),
        nonfinite_features=nonfinite_x,
        nonfinite_targets=nonfinite_y,
        constant_features=constant_features,
        constant_targets=constant_targets,
        tensorflow_available=importlib.util.find_spec("tensorflow") is not None,
        recommended=recommended,
        reasons=tuple(reasons),
        warnings=tuple(warnings),
    )


def _bounded_loaded_array(value: Any) -> Any:
    if not hasattr(value, "nbytes") or value.nbytes > _MAX_ARRAY_BYTES:
        raise RegressionError("numeric array exceeds the in-memory size limit")
    return value


def load_array(path: Path, *, key: str | None = None, skip_rows: int = 0) -> Any:
    """Load a numeric array from NPY, NPZ, CSV, TSV, or nested JSON."""

    if skip_rows < 0:
        raise RegressionError("skip_rows must be nonnegative")
    np = _numpy()
    requested = path.expanduser()
    if requested.is_symlink():
        raise RegressionError(f"array input must be a regular file: {requested}")
    source = requested.resolve()
    if not source.is_file():
        raise RegressionError(f"array input must be a regular file: {source}")
    if source.stat().st_size > _MAX_INPUT_BYTES:
        raise RegressionError(f"array input exceeds the size limit: {source}")
    suffix = source.suffix.lower()
    try:
        if suffix == ".npy":
            if key is not None:
                raise RegressionError("an NPY input does not accept an array key")
            return _bounded_loaded_array(np.load(source, allow_pickle=False))
        if suffix == ".npz":
            with zipfile.ZipFile(source) as compressed:
                if any(
                    item.file_size > _MAX_ARRAY_BYTES for item in compressed.infolist()
                ):
                    raise RegressionError(
                        f"NPZ array exceeds the in-memory size limit: {source}"
                    )
            with np.load(source, allow_pickle=False) as archive:
                names = tuple(archive.files)
                selected = key or (names[0] if len(names) == 1 else None)
                if selected is None:
                    raise RegressionError(
                        f"NPZ input has multiple arrays; choose one of {list(names)}"
                    )
                if selected not in names:
                    raise RegressionError(
                        f"NPZ array {selected!r} is absent; choose one of {list(names)}"
                    )
                return _bounded_loaded_array(np.array(archive[selected], copy=True))
        if suffix in {".csv", ".tsv"}:
            if key is not None:
                raise RegressionError("CSV and TSV inputs do not accept an array key")
            delimiter = "," if suffix == ".csv" else "\t"
            return _bounded_loaded_array(
                np.loadtxt(source, delimiter=delimiter, skiprows=skip_rows, ndmin=2)
            )
        if suffix == ".json":
            if key is not None:
                raise RegressionError("JSON inputs do not accept an array key")
            return _bounded_loaded_array(
                np.asarray(json.loads(source.read_text(encoding="utf-8")))
            )
    except (
        OSError,
        ValueError,
        json.JSONDecodeError,
        zipfile.BadZipFile,
    ) as exc:
        raise RegressionError(f"cannot load numeric array {source}: {exc}") from exc
    raise RegressionError("array input must use .npy, .npz, .csv, .tsv, or .json")


def _metrics(actual: Any, predicted: Any) -> dict[str, object]:
    np = _numpy()
    residual = predicted - actual
    mse = np.mean(np.square(residual), axis=0)
    mae = np.mean(np.abs(residual), axis=0)
    centered = actual - np.mean(actual, axis=0)
    denominator = np.sum(np.square(centered), axis=0)
    numerator = np.sum(np.square(residual), axis=0)
    ratio = np.full_like(numerator, np.nan, dtype=np.float64)
    np.divide(numerator, denominator, out=ratio, where=denominator > 0)
    r2 = np.where(denominator > 0, 1.0 - ratio, np.nan)

    def values(array: Any) -> list[float | None]:
        return [float(item) if np.isfinite(item) else None for item in array]

    return {
        "rmse_by_target": values(np.sqrt(mse)),
        "mae_by_target": values(mae),
        "r2_by_target": values(r2),
        "mean_rmse": float(np.mean(np.sqrt(mse))),
        "mean_mae": float(np.mean(mae)),
    }


def _tensorflow_prediction(
    x_train: Any,
    y_train: Any,
    x_validation: Any,
    y_validation: Any,
    config: RegressionConfig,
    output_dir: Path,
) -> tuple[Any, dict[str, list[float]], dict[str, object]]:
    if importlib.util.find_spec("tensorflow") is None:
        raise RegressionError(
            "tensorflow_dense requires TensorFlow; install the 'ml' extra"
        )
    os.environ.setdefault("TF_CPP_MIN_LOG_LEVEL", "2")
    os.environ.setdefault("TF_ENABLE_ONEDNN_OPTS", "0")
    if config.device == "cpu":
        os.environ.setdefault("CUDA_VISIBLE_DEVICES", "-1")
    try:
        tf = importlib.import_module("tensorflow")
    except ImportError as exc:
        raise RegressionError("TensorFlow could not be imported") from exc
    tf.keras.utils.set_random_seed(config.seed)
    try:
        if config.device == "cpu":
            tf.config.set_visible_devices([], "GPU")
        tf.config.experimental.enable_op_determinism()
    except (AttributeError, RuntimeError, ValueError) as exc:
        raise RegressionError(
            f"TensorFlow deterministic device setup is unavailable: {exc}"
        ) from exc
    regularizer = tf.keras.regularizers.L1L2(l1=config.l1, l2=config.l2)
    layers: list[Any] = [tf.keras.layers.Input(shape=(x_train.shape[1],))]
    layers.extend(
        tf.keras.layers.Dense(
            width,
            activation=config.activation,
            kernel_regularizer=regularizer,
        )
        for width in config.hidden_layers
    )
    layers.append(tf.keras.layers.Dense(y_train.shape[1]))
    model = tf.keras.Sequential(layers)
    optimizers = {
        "adam": tf.keras.optimizers.Adam,
        "rmsprop": tf.keras.optimizers.RMSprop,
        "sgd": tf.keras.optimizers.SGD,
    }
    losses: dict[str, object] = {
        "mse": "mse",
        "mae": "mae",
        "huber": tf.keras.losses.Huber(),
    }
    model.compile(
        optimizer=optimizers[config.optimizer](learning_rate=config.learning_rate),
        loss=losses[config.loss],
        metrics=["mae"],
    )
    callbacks = [
        tf.keras.callbacks.EarlyStopping(
            monitor="val_loss",
            patience=config.early_stopping_patience,
            restore_best_weights=True,
        ),
        tf.keras.callbacks.TerminateOnNaN(),
    ]
    device = "/CPU:0" if config.device == "cpu" else None
    context = tf.device(device) if device is not None else _NullContext()
    with context:
        fitted = model.fit(
            x_train,
            y_train,
            validation_data=(x_validation, y_validation),
            epochs=config.epochs,
            batch_size=min(config.batch_size, x_train.shape[0]),
            shuffle=True,
            verbose=0,
            callbacks=callbacks,
        )
        prediction = model.predict(x_validation, verbose=0)
    model.save(output_dir / "model.keras")
    history = {
        name: [float(item) for item in values]
        for name, values in fitted.history.items()
    }
    backend = {
        "name": "tensorflow",
        "version": tf.__version__,
        "devices": [device.name for device in tf.config.list_physical_devices()],
        "selected_device": config.device,
    }
    return prediction, history, backend


class _NullContext:
    def __enter__(self) -> None:
        return None

    def __exit__(self, *_args: object) -> None:
        return None


def fit_regression(
    features: object,
    targets: object,
    config: RegressionConfig,
    output_dir: Path,
) -> Path:
    """Fit a held-out regression and atomically retain an exploratory receipt."""
    config = RegressionConfig.parse(
        {
            **asdict(config),
            "hidden_layers": list(config.hidden_layers),
        }
    )
    requested = output_dir.expanduser()
    if requested.is_symlink():
        raise RegressionError("regression output must be a regular directory")
    destination = requested.resolve()
    if destination.exists() and not destination.is_dir():
        raise RegressionError("regression output must be a regular directory")
    if destination.exists() and any(destination.iterdir()):
        raise RegressionError("regression output directory must be empty")

    x, y = _arrays(features, targets, require_finite=True)
    assessment = assess_regression(x, y)
    if not assessment.recommended:
        raise RegressionError(
            "regression assessment does not recommend fitting: "
            + "; ".join(assessment.warnings)
        )

    destination.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(
        tempfile.mkdtemp(
            prefix=f".{destination.name}.regression-",
            dir=destination.parent,
        )
    )
    try:
        _fit_regression_into(x, y, config, staging, assessment)
        if destination.exists():
            destination.rmdir()
        os.replace(staging, destination)
    except BaseException:
        shutil.rmtree(staging, ignore_errors=True)
        raise
    return destination / "receipt.json"


def _fit_regression_into(
    x: Any,
    y: Any,
    config: RegressionConfig,
    destination: Path,
    assessment: RegressionAssessment,
) -> None:
    np = _numpy()
    validation_count = max(1, math.ceil(x.shape[0] * config.validation_fraction))
    if x.shape[0] - validation_count < 2:
        raise RegressionError("validation split leaves fewer than two training samples")
    if config.split_method == "random":
        generator = np.random.default_rng(config.seed)
        order = generator.permutation(x.shape[0])
        validation_indices = order[:validation_count]
        training_indices = order[validation_count:]
    else:
        boundary = x.shape[0] - validation_count
        training_indices = np.arange(boundary)
        validation_indices = np.arange(boundary, x.shape[0])
    x_train = x[training_indices]
    y_train = y[training_indices]
    x_validation = x[validation_indices]
    y_validation = y[validation_indices]
    x_mean = np.mean(x_train, axis=0)
    x_scale = np.std(x_train, axis=0)
    x_scale = np.where(x_scale > 0, x_scale, 1.0)
    x_train_scaled = (x_train - x_mean) / x_scale
    x_validation_scaled = (x_validation - x_mean) / x_scale
    design_train = np.column_stack((np.ones(x_train.shape[0]), x_train_scaled))
    design_validation = np.column_stack(
        (np.ones(x_validation.shape[0]), x_validation_scaled)
    )
    coefficients, *_ = np.linalg.lstsq(design_train, y_train, rcond=None)
    baseline_prediction = design_validation @ coefficients
    baseline_metrics = _metrics(y_validation, baseline_prediction)
    target_scaling: dict[str, Any] = {}
    history: dict[str, list[float]] = {}
    if config.model_kind == "linear":
        model_prediction = baseline_prediction
        model_metrics = baseline_metrics
        backend: dict[str, object] = {
            "name": "numpy_linear",
            "version": np.__version__,
            "selected_device": "cpu",
        }
    else:
        y_mean = np.mean(y_train, axis=0)
        y_scale = np.std(y_train, axis=0)
        y_scale = np.where(y_scale > 0, y_scale, 1.0)
        target_scaling = {"target_mean": y_mean, "target_scale": y_scale}
        scaled_prediction, history, backend = _tensorflow_prediction(
            x_train_scaled,
            (y_train - y_mean) / y_scale,
            x_validation_scaled,
            (y_validation - y_mean) / y_scale,
            config,
            destination,
        )
        model_prediction = scaled_prediction * y_scale + y_mean
        model_metrics = _metrics(y_validation, model_prediction)
    arrays_path = destination / "validation-results.npz"
    np.savez_compressed(
        arrays_path,
        training_indices=training_indices,
        validation_indices=validation_indices,
        actual=y_validation,
        baseline_prediction=baseline_prediction,
        model_prediction=model_prediction,
        feature_mean=x_mean,
        feature_scale=x_scale,
        linear_coefficients=coefficients,
        **target_scaling,
    )
    history_path = destination / "history.json"
    atomic_write_json(history_path, history)
    artifacts = []
    for path in sorted(destination.iterdir()):
        if path.is_file() and path.name != "receipt.json":
            artifacts.append(
                {
                    "path": path.name,
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    "size": path.stat().st_size,
                }
            )
    baseline_score = baseline_metrics["mean_rmse"]
    model_score = model_metrics["mean_rmse"]
    assert isinstance(baseline_score, float) and isinstance(model_score, float)
    model_beats_baseline = (
        config.model_kind == "tensorflow_dense" and model_score < baseline_score
    )
    atomic_write_json(
        destination / "receipt.json",
        {
            "schema_version": 1,
            "status": "succeeded",
            "evidence_class": _EVIDENCE_CLASS,
            "proof_status": "not_proof",
            "warning": (
                "Regression output is exploratory numeric evidence and must not be "
                "reported as a proof or certified bound."
            ),
            "completed_at": utc_now(),
            "config": asdict(config),
            "assessment": assessment.to_dict(),
            "split": {
                "method": config.split_method,
                "training_samples": int(training_indices.size),
                "validation_samples": int(validation_indices.size),
                "training_indices_sha256": _array_digest(training_indices),
                "validation_indices_sha256": _array_digest(validation_indices),
            },
            "baseline_metrics": baseline_metrics,
            "model_metrics": model_metrics,
            "comparison": {
                "criterion": "strictly lower mean held-out RMSE",
                "model_beats_linear_baseline": model_beats_baseline,
                "selected_model": (
                    "tensorflow_dense" if model_beats_baseline else "linear_baseline"
                ),
            },
            "backend": backend,
            "artifacts": artifacts,
        },
    )


def discover_regression_candidates(root: Path, *, limit: int = 50) -> tuple[str, ...]:
    """Return bounded numeric-array candidates without parsing untrusted contents."""

    if root.is_symlink() or not root.is_dir():
        return ()
    candidates: list[str] = []
    for current, directories, files in os.walk(root, followlinks=False):
        directories[:] = sorted(
            name for name in directories if not (Path(current) / name).is_symlink()
        )
        for name in sorted(files):
            path = Path(current) / name
            if path.is_symlink() or path.suffix.lower() not in _ARRAY_SUFFIXES:
                continue
            candidates.append(path.relative_to(root).as_posix())
            if len(candidates) >= limit:
                return tuple(candidates)
    return tuple(candidates)


def regression_capability_catalog(root: Path | None) -> tuple[dict[str, object], ...]:
    """Describe planner-facing eligibility, availability, and invocation contracts."""

    candidates = discover_regression_candidates(root) if root is not None else ()
    numpy_available = importlib.util.find_spec("numpy") is not None
    tensorflow_available = importlib.util.find_spec("tensorflow") is not None
    return (
        {
            "id": _CAPABILITIES[0],
            "available": numpy_available,
            "candidate_files": list(candidates),
            "invocation": (
                "agentic-lean-math-assistant regression-assess --features <array> "
                "--targets <array> --output <assessment.json>"
            ),
            "use_when": [
                "numeric samples may support prediction, interpolation, sensitivity, or a surrogate",
                "parameter sweeps or tabular observations need leakage checks",
            ],
            "avoid_when": [
                "the target is an exact proof directly accessible to symbolic or interval methods",
                "there are too few independent observations",
            ],
            "evidence_class": _EVIDENCE_CLASS,
        },
        {
            "id": _CAPABILITIES[1],
            "available": numpy_available,
            "tensorflow_available": tensorflow_available,
            "requires": _CAPABILITIES[0],
            "invocation": (
                "agentic-lean-math-assistant regression-fit --features <array> --targets <array> "
                "--config <config.json|toml> --output <directory>"
            ),
            "use_when": [
                "regression_assess recommends held-out fitting",
                "a linear baseline and independently evaluated surrogate answer a campaign question",
            ],
            "avoid_when": [
                "the assessment rejects the supplied arrays",
                "grouped dependence cannot be separated by the supported random or ordered split",
                "a fitted relationship would be misrepresented as proof",
            ],
            "evidence_class": _EVIDENCE_CLASS,
        },
    )
