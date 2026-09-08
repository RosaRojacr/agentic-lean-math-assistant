# Admissible Table 2 evidence record

## Literal source content

- **Retained coefficient cell:** `references/source.md:7`, Table 2 row `j = 7`, coefficient `cⱼ`:
  > `[ROW ILLEGIBLE IN RETAINED SCAN]`

  This is an illegibility marker, **not a numerical value for \(c_7\)**.

- **Neighboring-row restriction:** `problem.md:3`:
  > “Values in neighboring rows are not evidence of an interpolation rule.”

- **Pattern-inference restriction:** `problem.md:5`:
  > “Do not infer a pattern unless the source explicitly states one.”

- **All supplied statements about governing formulas:** `references/source.md:10`:
  > “The table caption gives no recurrence, interpolation rule, or closed formula.”

- **Original-page availability:** `references/source.md:10`:
  > “The original page containing a legible row 7 is unavailable.”

## Retained analytic conclusion—not literal table evidence

The artifact is marked accepted in `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.json:25`. Its report concludes:

- `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.md:5-9`: the retained row is illegible, no recurrence/interpolation/closed formula is supplied, neighboring rows are inadmissible as interpolation evidence, and no additional constraint is retained.
- `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.md:27`: the transcription does not uniquely determine \(c_7\).
- `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.md:31` identifies the required fragment:
  > “The legible coefficient cell in Table 2 row \(j=7\) on the unavailable original page.”

Its illustrative assignments \(0\) and \(1\) are explicitly logical witnesses rather than candidate readings (`knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.json:10-13`).

## Result

The exact coefficient \(c_7\) **cannot be uniquely recovered** from the supplied transcription. The unavailable fragment required is precisely:

> **Table 2, row \(j=7\), coefficient cell \(c_7\), in legible form on the unavailable original page.**

No numerical value was inferred from rows 5, 6, or 8.

## Inspection boundary

Files inspected:

1. `problem.md`
2. `references/source.md`
3. `knowledge/index.json`
4. `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.md`
5. `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.json`

Method: workspace `read` operations only. No external source was consulted; no tool failures occurred.
