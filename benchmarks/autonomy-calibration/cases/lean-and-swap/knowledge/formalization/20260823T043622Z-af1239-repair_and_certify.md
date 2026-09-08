Implemented and certified the conjunction-symmetry proof.

### Source

`proof/Calibration.lean` now contains:

```lean
theorem and_swap_calibration (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hP hQ =>
      exact And.intro hQ hP

#print axioms and_swap_calibration
```

The theorem name and statement remain unchanged. Only `exact ?_` was replaced.

### Verification

Prohibited-construct scan across `proof/*.lean` found no:

- `sorry`
- `admit`
- axiom declarations
- unresolved `?_` metavariables

Pinned build, from `proof/`:

```text
/home/rosa/.elan/bin/lake build
```

Exit status: `0`

```text
ℹ [2/3] Built Calibration (185ms)
info: Calibration.lean:7:0: 'and_swap_calibration' does not depend on any axioms
Build completed successfully (3 jobs).
```

Direct axiom check:

```text
/home/rosa/.elan/bin/lake env lean Calibration.lean
```

Exit status: `0`

```text
'and_swap_calibration' does not depend on any axioms
```

Exact retained evidence, including the initial `lake`-not-on-`PATH` failure:

`agents/formalization/repair_and_certify/build-evidence.md`
