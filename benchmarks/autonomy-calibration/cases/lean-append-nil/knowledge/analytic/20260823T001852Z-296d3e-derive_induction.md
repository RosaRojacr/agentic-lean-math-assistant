## Unchanged theorem type

```lean
theorem append_nil_calibration {α : Type} (xs : List α) : xs ++ [] = xs := by
```

No premise or import is needed.

## Structural-induction derivation

After `induction xs with`:

1. **Nil branch**

   Residual goal:

   ```lean
   [] ++ [] = []
   ```

   By the defining equation of `List.append`, `[] ++ []` reduces to `[]`. The goal is reflexive, so `rfl` closes it.

2. **Cons branch**

   For `x : α`, `xs : List α`, and induction hypothesis

   ```lean
   ih : xs ++ [] = xs
   ```

   the residual goal is:

   ```lean
   (x :: xs) ++ [] = x :: xs
   ```

   Unfolding the defining cons equation for append gives:

   ```lean
   x :: (xs ++ []) = x :: xs
   ```

   Rewriting the tail with `ih` yields `x :: xs = x :: xs`, closing the branch.

## Exact replacement for `exact ?_`

```lean
induction xs with
| nil =>
    rfl
| cons x xs ih =>
    change x :: (xs ++ []) = x :: xs
    rw [ih]
```

Resulting complete declaration:

```lean
theorem append_nil_calibration {α : Type} (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      change x :: (xs ++ []) = x :: xs
      rw [ih]

#print axioms append_nil_calibration
```

## Evidence and limitations

Consulted retained locators:

- `problem.md:1-5`
- `references/source.md:1-3`
- `proof/Calibration.lean:1-4`
- `proof/lean-toolchain:1` — `leanprover/lean4:v4.33.1`
- `knowledge/index.json:1-4` — no retained artifacts
- `knowledge/analytic/` — absent

The directive’s `project-inputs/proof/...` paths are absent in this workspace; the corresponding retained files are under `proof/`. Per the stage restriction, no project files were edited and no compilation claim is made.
