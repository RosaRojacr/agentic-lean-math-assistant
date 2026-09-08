Implemented the structural-induction proof in `proof/Calibration.lean` while preserving the exact theorem declaration and `#print axioms` command.

```lean
theorem append_nil_calibration {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    change head :: (tail ++ []) = head :: tail
    rw [ih]
```

Verification from `proof/`:

```text
$ /home/rosa/.elan/bin/lean --version
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)

$ /home/rosa/.elan/bin/lake build
ℹ [2/3] Built Calibration (179ms)
info: Calibration.lean:8:0: 'append_nil_calibration' does not depend on any axioms
Build completed successfully (3 jobs).
```

Both commands exited with status `0`. No `sorry`, `admit`, placeholder, or axiom declaration remains.

Evidence retained at:

`agents/lean_formalization/formalize_proof/build-evidence.txt`
