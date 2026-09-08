## Located declaration

Relevant files under `proof/`:

- `proof/Calibration.lean` — theorem source
- `proof/lakefile.toml` — declares module/default target `Calibration`
- `proof/lean-toolchain` — pins `leanprover/lean4:v4.33.1`
- `proof/lake-manifest.json` — pinned Lake manifest

**Source:** `proof/Calibration.lean:1`  
**Module:** `Calibration`  
**Theorem:** `and_swap_calibration`

Verbatim statement:

```lean
theorem and_swap_calibration (P Q : Prop) : P ∧ Q → Q ∧ P := by
```

The unresolved body is `exact ?_` at `proof/Calibration.lean:2`.

The declaration matches conjunction symmetry; replanning is unnecessary.

## Derived proof

```lean
by
  intro h
  cases h with
  | intro hP hQ =>
      exact And.intro hQ hP
```

This eliminates `h : P ∧ Q` into `hP : P` and `hQ : Q`, then constructs `Q ∧ P` with `And.intro hQ hP`.

## Pinned-environment probe

Probe artifact:

`agents/analytic/inspect_and_derive/Probe.lean`

```lean
theorem and_swap_calibration_probe (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hP hQ =>
      exact And.intro hQ hP

#print axioms and_swap_calibration_probe
```

Exact successful command, run from `proof/`:

```text
/home/rosa/.elan/bin/lake env lean ../agents/analytic/inspect_and_derive/Probe.lean
```

Output:

```text
'and_swap_calibration_probe' does not depend on any axioms
```

Exit status: `0`; elapsed time: `0.22 seconds`.

The initial command using bare `lake` failed because `/home/rosa/.elan/bin` was absent from `PATH`:

```text
error: command not found: lake
```

No retained source was edited. Repair and full `lake build` remain obligations for the repair stage.
