# Repair a Lean successor-addition proof

The retained project under `proof/` contains one theorem with an unresolved metavariable. Replace the metavariable with a complete kernel-checked proof.

Acceptance requires:

- the theorem statement remains unchanged;
- no `sorry`, `admit`, new axiom, or weakened statement;
- `lake build` succeeds in `proof/`; and
- `#print axioms succ_add_calibration` reports no axioms.

Retain the corrected Lean source and the exact build command and output.
