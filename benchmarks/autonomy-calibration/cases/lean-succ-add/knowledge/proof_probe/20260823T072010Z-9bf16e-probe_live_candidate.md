Probe accepted against the live declaration. `proof/Calibration.lean` was not modified.

**Live target — `proof/Calibration.lean:1-2`**

- Imports: none
- Theorem: `succ_add_calibration`
- Binders: `(m n : Nat)`
- Proposition: `Nat.succ m + n = Nat.succ (m + n)`
- Unresolved site: line 2, `exact ?_`

**Temporary candidate — `agents/proof_probe/probe_live_candidate/CalibrationProbe.lean`**

```lean
theorem succ_add_calibration (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  exact Nat.succ_add m n

#print axioms succ_add_calibration
```

**Pinned toolchain**

```text
leanprover/lean4:v4.33.1
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

**Exact command**, run from `proof/`:

```sh
/home/rosa/.elan/bin/lake env lean ../agents/proof_probe/probe_live_candidate/CalibrationProbe.lean
```

**Complete output**

```text
'succ_add_calibration' does not depend on any axioms
```

**Exit status:** `0`

Retained evidence:

- `agents/proof_probe/probe_live_candidate/CalibrationProbe.lean`
- `agents/proof_probe/probe_live_candidate/compile-command.txt`
- `agents/proof_probe/probe_live_candidate/compile-output.txt`
- `agents/proof_probe/probe_live_candidate/compile-exit-status.txt`
- `agents/proof_probe/probe_live_candidate/live-target.txt`
- `agents/proof_probe/probe_live_candidate/toolchain.txt`

Result: `Nat.succ_add m n` elaborates as the complete proof of the exact live theorem, and the probed theorem depends on no axioms.
