Pilot replay completed without editing `proof/Calibration.lean`.

- Confirmed declaration at `proof/Calibration.lean:1`:
  ```lean
  theorem append_nil_calibration {α : Type} (xs : List α) : xs ++ [] = xs := by
  ```
- Created disposable structural-induction candidate:
  `agents/formal_probe/pilot_replay/append_nil_candidate.lean`
- Bare `lake --version` reproduced the retained PATH failure: exit `127`.
- Pinned environment:
  ```text
  Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
  ```
- Replay command from `proof/`:
  ```text
  /home/rosa/.elan/bin/lake env lean ../agents/formal_probe/pilot_replay/append_nil_candidate.lean
  ```
  Exit status: `0`.

Verbatim axiom report:

```text
'append_nil_calibration' does not depend on any axioms
```

Full commands, outputs, source, statuses, scope, and limitations retained in:

`agents/formal_probe/pilot_replay/replay-evidence.md`
