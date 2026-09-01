"""Small deterministic numerical routines for research agents."""

from __future__ import annotations

import math
from collections.abc import Callable, Iterable
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class RootBracket:
    left: float
    right: float
    f_left: float
    f_right: float

    def __post_init__(self) -> None:
        if not self.left < self.right:
            raise ValueError("root bracket requires left < right")
        if not all(
            math.isfinite(value)
            for value in (self.left, self.right, self.f_left, self.f_right)
        ):
            raise ValueError("root bracket values must be finite")
        if (
            self.f_left != 0.0
            and self.f_right != 0.0
            and self.f_left * self.f_right > 0
        ):
            raise ValueError("root bracket endpoints must have opposite signs")


def bracket_sign_changes(
    function: Callable[[float], float], points: Iterable[float]
) -> tuple[RootBracket, ...]:
    """Return adjacent finite samples that contain a zero or sign change."""

    iterator = iter(points)
    try:
        left = float(next(iterator))
    except StopIteration:
        return ()
    f_left = float(function(left))
    result: list[RootBracket] = []
    for raw_right in iterator:
        right = float(raw_right)
        if not left < right:
            raise ValueError("sample points must be strictly increasing")
        f_right = float(function(right))
        if not math.isfinite(f_left) or not math.isfinite(f_right):
            raise ValueError("function samples must be finite")
        if f_left == 0.0 or f_right == 0.0 or f_left * f_right < 0.0:
            result.append(RootBracket(left, right, f_left, f_right))
        left, f_left = right, f_right
    return tuple(result)


def bisect_root(
    function: Callable[[float], float],
    bracket: RootBracket,
    *,
    absolute_tolerance: float = 1e-12,
    max_iterations: int = 200,
) -> RootBracket:
    """Narrow a sign-changing bracket without assuming derivatives."""

    if not math.isfinite(absolute_tolerance) or absolute_tolerance <= 0:
        raise ValueError("absolute_tolerance must be positive and finite")
    if max_iterations < 1:
        raise ValueError("max_iterations must be positive")
    left, right = bracket.left, bracket.right
    f_left, f_right = bracket.f_left, bracket.f_right
    for _ in range(max_iterations):
        if right - left <= absolute_tolerance or f_left == 0.0 or f_right == 0.0:
            return RootBracket(left, right, f_left, f_right)
        midpoint = left + (right - left) / 2.0
        f_midpoint = float(function(midpoint))
        if not math.isfinite(f_midpoint):
            raise ValueError("function returned a non-finite midpoint value")
        if f_midpoint == 0.0:
            neighbor = math.nextafter(midpoint, left)
            return RootBracket(
                neighbor, midpoint, float(function(neighbor)), f_midpoint
            )
        if f_left == 0.0 or f_left * f_midpoint < 0.0:
            right, f_right = midpoint, f_midpoint
        else:
            left, f_left = midpoint, f_midpoint
    raise RuntimeError("bisection did not reach the requested tolerance")
