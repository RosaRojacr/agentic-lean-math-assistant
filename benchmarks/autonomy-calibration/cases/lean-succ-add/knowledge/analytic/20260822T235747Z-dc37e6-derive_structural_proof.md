## Structural derivation

Induct on `n`, following `Nat.add`’s recursion on its second argument.

- **Base `n = 0`:**
  - `Nat.succ m + 0` reduces to `Nat.succ m`.
  - `Nat.succ (m + 0)` reduces to `Nat.succ m`.
  - Closed by `rfl`.

- **Step `n = Nat.succ k`:**
  - `Nat.succ m + Nat.succ k` reduces to `Nat.succ (Nat.succ m + k)`.
  - `Nat.succ (m + Nat.succ k)` reduces to `Nat.succ (Nat.succ (m + k))`.
  - The induction hypothesis is:
    ```lean
    Nat.succ m + k = Nat.succ (m + k)
    ```
  - Applying `congrArg Nat.succ` closes the reduced goal.

No successor-addition theorem is invoked.

## Exact Lean candidate

```lean
theorem succ_add_calibration (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      exact congrArg Nat.succ ih

#print axioms succ_add_calibration
```

Scratch source retained at:

```text
agents/analytic/derive_structural_proof/Structural.lean
```

## Successful pinned-toolchain check

Working directory:

```text
proof
```

Exact command:

```text
/home/rosa/.elan/bin/lake env lean ../agents/analytic/derive_structural_proof/Structural.lean
```

Exit status:

```text
0
```

Complete output:

```text
'succ_add_calibration' does not depend on any axioms


Wall time: 0.23 seconds
```

This uses `proof/lean-toolchain`, pinned to `leanprover/lean4:v4.33.1`.

## Initial environment failure

The unqualified command was unavailable because `lake` was not on `PATH`.

Command:

```text
lake env lean ../agents/analytic/derive_structural_proof/Structural.lean
```

Exit status:

```text
127
```

Complete output:

```text
error: command not found: lake


Wall time: 0.06 seconds

Command exited with code 127
```

Full evidence retained at:

```text
agents/analytic/derive_structural_proof/verification.txt
```

`proof/Calibration.lean` was not edited, as required by the read-only stage directive.
