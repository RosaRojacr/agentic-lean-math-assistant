from __future__ import annotations

import json
import math
import subprocess
import tomllib
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "cases"
EXPECTED = json.loads(
    (ROOT / "validation" / "expected-outcomes.json").read_text(encoding="utf-8")
)
SUITE = tomllib.loads((ROOT / "benchmark.toml").read_text(encoding="utf-8"))

expected = {item["id"]: item["expected_outcome"] for item in EXPECTED["cases"]}
configured = {item["id"]: item["expected_outcome"] for item in SUITE["cases"]}
assert EXPECTED["schema_version"] == 1
assert len(expected) == len(EXPECTED["cases"]) == 12
assert configured == expected
assert list(expected.values()).count("solved") == 7
assert list(expected.values()).count("blocked") == 2
assert list(expected.values()).count("unsolved") == 3

# Exact derivation certificates.
assert sum(3 * 2**k for k in range(8)) == 765 == 3 * (2**8 - 1)
assert math.gcd(84, 30) == 6
assert -84 + 3 * 30 == 6
assert (1, -6, 13) == (1, -2 * 3, 3**2 + 4)
assert all((n**3 - n) % 6 == 0 for n in range(6))

# Exact non-uniqueness certificates for unavailable and underdetermined cases.
mean_with_zero = Fraction(4 + 8 + 0 + 10, 4)
mean_with_ten = Fraction(4 + 8 + 10 + 10, 4)
assert mean_with_zero == Fraction(11, 2)
assert mean_with_ten == 8
assert mean_with_zero != mean_with_ten
assert (0 + 4, 2 * 0 + 2 * 4, 0 - 4) == (4, 8, -4)
assert (1 + 3, 2 * 1 + 2 * 3, 1 - 3) == (4, 8, -2)
assert "[ROW ILLEGIBLE" in (
    CASES / "missing-table-entry" / "references" / "source.md"
).read_text(encoding="utf-8")

# Exact counterexamples for false-closure traps.
odd_composite = 9
assert odd_composite > 1 and odd_composite % 2 == 1 and odd_composite % 3 == 0
(a, b, c, d) = (-2, -1, 1, 1)
assert b != 0 and d != 0 and Fraction(a, b) > Fraction(c, d)
assert not (a * d > b * c)

# Independent kernel certificates for the three repairable Lean cases.
lean_cases = {
    "lean-succ-add": "SuccAdd.lean",
    "lean-and-swap": "AndSwap.lean",
    "lean-append-nil": "AppendNil.lean",
}
for case_id, solution in lean_cases.items():
    challenge = (CASES / case_id / "proof" / "Calibration.lean").read_text(
        encoding="utf-8"
    )
    assert "?_" in challenge
    assert "sorry" not in challenge and "admit" not in challenge
    completed = subprocess.run(
        ["lake", "env", "lean", str(ROOT / "validation" / "lean-solutions" / solution)],
        cwd=CASES / case_id / "proof",
        check=False,
        capture_output=True,
        text=True,
        timeout=60,
    )
    if completed.returncode != 0:
        raise AssertionError(
            f"{case_id} validation failed:\n{completed.stdout}\n{completed.stderr}"
        )
    assert "does not depend on any axioms" in completed.stdout

print("validated 12 blind cases: 7 solved, 2 blocked, 3 unsolved")
