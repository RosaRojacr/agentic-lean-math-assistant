"""Cross-controller deadline and model-call admission for folder solves."""

from __future__ import annotations

import fcntl
import json
import math
import os
import time
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .artifacts import atomic_write_json, utc_now

_BUDGET_ENV = "ALMA_SOLVE_BUDGET"
_RUNNER_GRACE_SECONDS = 60
_MINIMUM_AGENT_SECONDS = 30


class SolveBudgetExceeded(RuntimeError):
    """A nested model invocation cannot fit the retained solve budget."""


@dataclass(frozen=True, slots=True)
class SolveBudgetAdmission:
    max_time: int
    model_call: int | None
    remaining_seconds: int | None
    deadline_epoch: float | None


@dataclass(frozen=True, slots=True)
class SolveBudgetState:
    deadline_epoch: float
    max_model_calls: int | None
    model_calls: int

    @classmethod
    def parse(cls, value: object) -> SolveBudgetState:
        if not isinstance(value, dict) or set(value) != {
            "schema_version",
            "deadline_epoch",
            "max_model_calls",
            "model_calls",
            "updated_at",
        }:
            raise SolveBudgetExceeded("retained solve budget is malformed")
        if value["schema_version"] != 1:
            raise SolveBudgetExceeded("retained solve budget schema is unsupported")
        deadline = value["deadline_epoch"]
        maximum = value["max_model_calls"]
        calls = value["model_calls"]
        if (
            isinstance(deadline, bool)
            or not isinstance(deadline, (int, float))
            or not math.isfinite(float(deadline))
            or float(deadline) <= 0
        ):
            raise SolveBudgetExceeded("retained solve deadline is malformed")
        if maximum is not None and (
            isinstance(maximum, bool) or not isinstance(maximum, int) or maximum < 1
        ):
            raise SolveBudgetExceeded("retained solve model-call limit is malformed")
        if isinstance(calls, bool) or not isinstance(calls, int) or calls < 0:
            raise SolveBudgetExceeded("retained solve model-call count is malformed")
        return cls(float(deadline), maximum, calls)

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": 1,
            "deadline_epoch": self.deadline_epoch,
            "max_model_calls": self.max_model_calls,
            "model_calls": self.model_calls,
            "updated_at": utc_now(),
        }


def initialize_solve_budget(
    path: Path,
    *,
    remaining_seconds: int,
    max_model_calls: int | None,
    model_calls: int,
    now: float | None = None,
) -> SolveBudgetState:
    if remaining_seconds < 0:
        raise ValueError("remaining solve runtime cannot be negative")
    if max_model_calls is not None and max_model_calls < 1:
        raise ValueError("solve model-call limit must be positive")
    if model_calls < 0:
        raise ValueError("solve model-call count cannot be negative")
    current_time = time.time() if now is None else now
    state = SolveBudgetState(
        deadline_epoch=current_time + remaining_seconds,
        max_model_calls=max_model_calls,
        model_calls=model_calls,
    )
    with _budget_lock(path):
        atomic_write_json(path, state.to_dict())
    return state


def admit_nested_model_call(
    requested_seconds: int,
    *,
    now: float | None = None,
    environment: dict[str, str] | os._Environ[str] | None = None,
) -> SolveBudgetAdmission:
    env = os.environ if environment is None else environment
    budget_value = env.get(_BUDGET_ENV)
    if budget_value is None:
        return SolveBudgetAdmission(requested_seconds, None, None, None)
    path = Path(budget_value).expanduser().resolve()
    current_time = time.time() if now is None else now
    with _budget_lock(path):
        state = _load_budget(path)
        remaining = math.floor(state.deadline_epoch - current_time)
        if remaining < _MINIMUM_AGENT_SECONDS + _RUNNER_GRACE_SECONDS:
            raise SolveBudgetExceeded(
                "global solve deadline leaves insufficient time for another model call"
            )
        if (
            state.max_model_calls is not None
            and state.model_calls >= state.max_model_calls
        ):
            raise SolveBudgetExceeded(
                f"global solve model-call limit reached ({state.model_calls}/{state.max_model_calls})"
            )
        effective = min(
            requested_seconds,
            max(_MINIMUM_AGENT_SECONDS, remaining - _RUNNER_GRACE_SECONDS),
        )
        admitted = SolveBudgetState(
            deadline_epoch=state.deadline_epoch,
            max_model_calls=state.max_model_calls,
            model_calls=state.model_calls + 1,
        )
        atomic_write_json(path, admitted.to_dict())
    return SolveBudgetAdmission(
        effective, admitted.model_calls, remaining, admitted.deadline_epoch
    )


def solve_budget_model_calls(path: Path) -> int:
    with _budget_lock(path):
        return _load_budget(path).model_calls


@contextmanager
def solve_budget_environment(path: Path) -> Iterator[None]:
    prior = os.environ.get(_BUDGET_ENV)
    os.environ[_BUDGET_ENV] = str(path.expanduser().resolve())
    try:
        yield
    finally:
        if prior is None:
            os.environ.pop(_BUDGET_ENV, None)
        else:
            os.environ[_BUDGET_ENV] = prior


@contextmanager
def _budget_lock(path: Path) -> Iterator[None]:
    path.parent.mkdir(parents=True, exist_ok=True)
    lock = path.with_suffix(path.suffix + ".lock")
    flags = os.O_CREAT | os.O_RDWR
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(lock, flags, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _load_budget(path: Path) -> SolveBudgetState:
    try:
        value: Any = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SolveBudgetExceeded(f"cannot load retained solve budget: {exc}") from exc
    return SolveBudgetState.parse(value)
