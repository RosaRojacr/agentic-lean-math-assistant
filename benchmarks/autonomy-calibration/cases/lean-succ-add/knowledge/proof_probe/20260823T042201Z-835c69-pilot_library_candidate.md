Pilot proof probe succeeded. `proof/Calibration.lean` was not modified.

**Live target — `proof/Calibration.lean:1`**
```lean
theorem succ_add_calibration (m n : Nat) : Nat.succ m + n = Nat.succ (m + n)
```

**Retained scratch source — `agents/proof_probe/pilot_library_candidate/CalibrationScratch.lean`**
```lean
theorem succ_add_calibration (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  exact Nat.succ_add m n

#print axioms succ_add_calibration
```

**Pinned toolchain**
```text
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

**Compile command**, from `proof/`:
```sh
/home/rosa/.elan/bin/lake env lean ../agents/proof_probe/pilot_library_candidate/CalibrationScratch.lean
```

**Complete output**
```text
'succ_add_calibration' does not depend on any axioms
```

**Exit status:** `0`

Retained evidence:

- `compile-command.txt`
- `compile-output.txt`
- `compile-exit-status.txt`
- `target-statement.txt`
- `toolchain-check.txt`
- `failed-attempt.txt`

The initial bare `lake` invocation failed with status `127` because `~/.elan/bin` was absent from `PATH`; rerunning through `/home/rosa/.elan/bin/lake` succeeded under the project’s pinned toolchain.
