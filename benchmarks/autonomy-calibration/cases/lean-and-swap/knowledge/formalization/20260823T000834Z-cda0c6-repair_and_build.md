Implemented the conjunction-symmetry proof in `proof/Calibration.lean`:

```lean
theorem and_swap_calibration (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hP hQ =>
      exact And.intro hQ hP
```

- The theorem name and statement are unchanged.
- Only `exact ?_` was replaced.
- Scan for `sorry`, `admit`, `axiom`, and `?_`: no matches.
- No imports, hypotheses, declarations, automation, or aliases added.

Pinned build, run from `proof/`:

```text
lake build
```

Exit status: `0`

```text
ℹ [2/3] Replayed Calibration
info: Calibration.lean:7:0: 'and_swap_calibration' does not depend on any axioms
Build completed successfully (3 jobs).
```

Axiom check:

```text
lake env lean Calibration.lean
```

Exit status: `0`

```text
'and_swap_calibration' does not depend on any axioms
```

Exact retained evidence: `agents/formalization/repair_and_build/build-evidence.md`.
