"""Transparent SymPy helpers that retain residuals instead of hiding failures."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

import sympy as sp  # type: ignore[import-untyped]


@dataclass(frozen=True, slots=True)
class IdentityCheck:
    proved: bool
    residual: sp.Expr


def check_identity(left: sp.Expr, right: sp.Expr) -> IdentityCheck:
    """Simplify `left - right`; `proved` means SymPy reduced it exactly to zero."""

    residual = sp.trigsimp(sp.cancel(sp.together(left - right)))
    return IdentityCheck(proved=residual == 0, residual=residual)


def derivative_residual(
    expression: sp.Expr,
    variable: sp.Symbol,
    claimed_derivative: sp.Expr,
) -> IdentityCheck:
    """Check a claimed symbolic derivative and expose the exact residual."""

    return check_identity(sp.diff(expression, variable), claimed_derivative)


def substitute_exact(
    expression: sp.Expr, substitutions: dict[sp.Symbol, Any]
) -> sp.Expr:
    """Substitute values and simplify without converting exact inputs to floats."""

    return sp.simplify(expression.subs(substitutions))
