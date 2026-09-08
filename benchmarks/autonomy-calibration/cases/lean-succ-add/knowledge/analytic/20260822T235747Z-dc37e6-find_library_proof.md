## Candidate

Replace only the metavariable `?_` with:

```lean
Nat.succ_add m n
```

Resulting proof body:

```lean
by
  exact Nat.succ_add m n
```

The theorem statement remains unchanged.

## Declaration evidence

Scratch source: `agents/analytic/find_library_proof/LibraryProof.lean`

```lean
#check Nat.succ_add

theorem succ_add_calibration (m n : Nat) :
    Nat.succ m + n = Nat.succ (m + n) := by
  exact Nat.succ_add m n

#print axioms succ_add_calibration
```

Pinned toolchain: `proof/lean-toolchain`

```text
leanprover/lean4:v4.33.1
```

## Successful verification

Working directory: `proof`

Exact command:

```console
PATH=/home/rosa/.elan/bin:/home/rosa/.local/bin:/home/rosa/bin:/usr/bin:/usr:/var/lib/snapd/snap/bin lake env lean ../agents/analytic/find_library_proof/LibraryProof.lean
```

Complete compiler output:

```text
Nat.succ_add (n m : Nat) : n.succ + m = (n + m).succ
'succ_add_calibration' does not depend on any axioms
```

Exit status: `0`.

## Environment failure encountered

The first invocation lacked the elan binary directory in `PATH`:

```console
lake env lean ../agents/analytic/find_library_proof/LibraryProof.lean
```

Output:

```text
error: command not found: lake
```

Exit status: `127`.

Evidence retained in:

- `agents/analytic/find_library_proof/LibraryProof.lean`
- `agents/analytic/find_library_proof/verification.txt`

`proof/Calibration.lean` was not modified, as required by this read-only stage.
