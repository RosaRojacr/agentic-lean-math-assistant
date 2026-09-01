"""Reusable exact, numerical, symbolic, and reference-acquisition helpers."""

from .exact import decimal_fraction, interval_horner, outward_decimal_interval
from .numeric import RootBracket, bisect_root, bracket_sign_changes
from .references import DownloadedReference, download_reference, sha256_file
from .symbolic import (
    IdentityCheck,
    check_identity,
    derivative_residual,
    substitute_exact,
)

__all__ = [
    "DownloadedReference",
    "IdentityCheck",
    "RootBracket",
    "bisect_root",
    "bracket_sign_changes",
    "check_identity",
    "decimal_fraction",
    "derivative_residual",
    "download_reference",
    "interval_horner",
    "outward_decimal_interval",
    "sha256_file",
    "substitute_exact",
]
