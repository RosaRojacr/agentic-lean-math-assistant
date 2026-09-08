## Current source identity

`proof/Calibration.lean:1`

```lean
theorem and_swap_calibration (P Q : Prop) : P ∧ Q → Q ∧ P := by
```

Current unresolved body at `proof/Calibration.lean:2`:

```lean
  exact ?_
```

The theorem name, parameters, hypotheses, and conclusion exactly match the retained conjunction-symmetry contract:

```text
and_swap_calibration (P Q : Prop) : P ∧ Q → Q ∧ P
```

No material contradiction found.

## Pinned environment

`proof/lean-toolchain`:

```text
leanprover/lean4:v4.33.1
```

`proof/lakefile.toml` identifies:

```toml
name = "lean_and_swap_calibration"
defaultTargets = ["Calibration"]

[[lean_lib]]
name = "Calibration"
```

Relevant `proof/lake-manifest.json` entries:

```json
{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [],
  "name": "lean_and_swap_calibration",
  "lakeDir": ".lake",
  "fixedToolchain": false
}
```

## Isolated constructor probe

Created outside retained source at:

```text
agents/analytic/inspect_and_probe/Probe.lean
```

Exact probe source:

```lean
theorem and_swap_calibration_probe (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hP hQ =>
      exact And.intro hQ hP

#print axioms and_swap_calibration_probe
```

Exact command, run with working directory `proof/`:

```text
/home/rosa/.elan/bin/lake env lean ../agents/analytic/inspect_and_probe/Probe.lean
```

Exact process output:

```text
'and_swap_calibration_probe' does not depend on any axioms
```

Exit status: `0`

The pinned Lean environment accepts the `intro` / `cases` / `And.intro hQ hP` proof, and the probe axiom report confirms that it depends on no axioms. No files under `proof/` were modified.
