#!/usr/bin/env python3
"""Independent high-precision semantic audit of the exact germ identities.

This audit is observational only.  It evaluates both the retained h-coordinate
formulas and the angle-coordinate formulas without importing checker code.
"""

from __future__ import annotations

import hashlib
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[2]
CALCULUS = ROOT / "proof" / "verify_calculus.py"
EXPECTED_CALCULUS_SHA256 = "61f8ca964996b090b62b61cebd070339448103860d1637962ce3940aa954d150"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def retained(lam: mp.mpf, h: mp.mpf, kind: int) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    if kind == 4:
        u = mp.sqrt(1 - h * h)
        dcap = mp.sqrt(lam * lam - h * h)
        alpha = mp.acos(h / lam)
        length = lam * alpha + mp.asin(h)
        d = dcap / lam - u
        area = 2 * (length + h * d) / (h * h)
        perimeter = 4 * length / h
        fold = 4 * (h * (1 / u - lam / dcap) - length)
        return area, perimeter, fold

    q = 2 * h - 1
    u = mp.sqrt(1 - q * q)
    dcap = mp.sqrt(lam * lam - q * q)
    alpha = mp.acos(q / lam)
    length = lam * alpha + mp.asin(q)
    d = dcap / lam - u
    area = (length + mp.pi / 2 + (q + 2) * d) / (h * h)
    perimeter = 2 * (length + mp.pi / 2 + d) / h
    fold = 4 * h * ((1 + q) / u - (lam * lam + q) / (lam * dcap)) - 2 * (
        length + mp.pi / 2 + d
    )
    return area, perimeter, fold


def angle_values(x: mp.mpf, z: mp.mpf, r: mp.mpf, e: mp.mpf) -> dict[str, mp.mpf]:
    y = x + x * x * z
    w = x * r
    v = w + x * x * e
    lam = mp.cos(x) / mp.cos(y)
    h4 = mp.cos(x)
    h3 = (1 + mp.cos(w)) / 2

    l4 = lam * y + mp.pi / 2 - x
    d4 = mp.sin(y) - mp.sin(x)
    a4 = 2 * (l4 + h4 * d4) / (h4 * h4)
    p4 = 4 * l4 / h4
    f4 = 4 * (mp.cos(x) * (1 / mp.sin(x) - 1 / mp.sin(y)) - l4)

    q3 = mp.cos(w)
    l3h = lam * v + mp.pi - w
    d3 = mp.sin(v) - mp.sin(w)
    a3 = (l3h + (q3 + 2) * d3) / (h3 * h3)
    p3 = 2 * (l3h + d3) / h3
    cosine = mp.cos(v) * mp.cos(x) - mp.cos(w) * mp.cos(y)
    return {
        "lambda": lam,
        "h3": h3,
        "h4": h4,
        "a3": a3,
        "a4": a4,
        "p3": p3,
        "p4": p4,
        "f4": f4,
        "cosine": cosine,
    }


def main() -> None:
    mp.mp.dps = 100
    actual_hash = sha256(CALCULUS)
    if actual_hash != EXPECTED_CALCULUS_SHA256:
        raise RuntimeError(f"retained calculus hash changed: {actual_hash}")

    maximum_formula_residual = mp.mpf("0")
    maximum_equation_residual = mp.mpf("0")
    rows: list[str] = []
    for text in ("0.03", "0.01", "0.003", "0.001"):
        x = mp.mpf(text)

        def fold_eq(z: mp.mpf) -> mp.mpf:
            values = angle_values(x, z, mp.mpf(2), mp.pi / 4)
            return values["f4"] / 4

        z = mp.findroot(fold_eq, mp.pi / 2)

        def equal_eq(r: mp.mpf, e: mp.mpf) -> tuple[mp.mpf, mp.mpf]:
            values = angle_values(x, z, r, e)
            return values["cosine"] / x**3, (values["a3"] - values["a4"]) / x**2

        r, e = mp.findroot(equal_eq, (mp.mpf(2), mp.pi / 4))
        values = angle_values(x, z, r, e)
        original3 = retained(values["lambda"], values["h3"], 3)
        original4 = retained(values["lambda"], values["h4"], 4)
        formula_residuals = (
            original3[0] - values["a3"],
            original3[1] - values["p3"],
            original4[0] - values["a4"],
            original4[1] - values["p4"],
            original4[2] - values["f4"],
        )
        equation_residuals = (
            values["f4"],
            values["cosine"],
            values["a3"] - values["a4"],
        )
        maximum_formula_residual = max(maximum_formula_residual, *(abs(v) for v in formula_residuals))
        maximum_equation_residual = max(maximum_equation_residual, *(abs(v) for v in equation_residuals))
        if not original3[2] < 0:
            raise RuntimeError("selected type-(iii) branch is not descending")
        ratio = (values["p3"] - values["p4"]) / x**4
        rows.append(
            "x={} lambda-1={} r={} K3={} gap/x^4={}".format(
                text,
                mp.nstr(values["lambda"] - 1, 16),
                mp.nstr(r, 16),
                mp.nstr(original3[2], 16),
                mp.nstr(ratio, 20),
            )
        )

    print(f"CALCULUS_SHA256={actual_hash}")
    print(f"MPMATH_VERSION={mp.__version__}")
    for row in rows:
        print(row)
    print(f"TARGET_GAP_OVER_X4={mp.nstr(-3 * mp.pi / 4, 20)}")
    print(f"MAX_FORMULA_RESIDUAL={mp.nstr(maximum_formula_residual, 8)}")
    print(f"MAX_EQUATION_RESIDUAL={mp.nstr(maximum_equation_residual, 8)}")
    print("SEMANTIC_AUDIT=PASS")


if __name__ == "__main__":
    main()
