# Source-bounded coefficient report

## Result

The exact numerical value of \(c_7\) **is not uniquely recoverable** from the supplied transcription.

### Retained Table 2 row

`references/source.md:7`, Table 2 row \(j=7\), column `coefficient cⱼ`:

> `[ROW ILLEGIBLE IN RETAINED SCAN]`

This is an illegibility marker, not a literal value for \(c_7\). Moreover, `references/source.md:10` states:

> “The table caption gives no recurrence, interpolation rule, or closed formula. The original page containing a legible row 7 is unavailable.”

## Verified non-uniqueness certificate

Two distinct completions compatible with every supplied statement are:

1. \(c_7=0\)
2. \(c_7=1\)

Both preserve the transcribed rows \(c_5=11/8\), \(c_6=-3/2\), and \(c_8=5/3\); neither contradicts the illegible row-7 cell or any stated governing rule, because no such rule is supplied. Since \(0\neq1\), the transcription does not uniquely determine \(c_7\).

This certificate is retained at:

- `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.md`, section **“Two compatible completions”**
- `knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.json`, where `status` is `"accepted"` and `verified_by` contains `"audit_source_gap"`

The values \(0\) and \(1\) are logical witnesses only, **not candidate readings** of the missing cell.

## Exact required source fragment

Unique direct recovery requires:

> **The legible coefficient cell \(c_7\) in Table 2, row \(j=7\), on the unavailable original page.**

## Source-boundary compliance

- Rows \(j=5,6,8\) were not used to infer or interpolate \(c_7\).
- No external source or publication was consulted.
- No unstated recurrence, formula, interpolation rule, or numerical pattern was assumed.
- No coefficient was guessed.
- The conclusion uses only `problem.md`, `references/source.md`, and the retained accepted source-extraction and analytic certificates.

## Inspection record

Read operations performed:

- `read problem.md`
- `read references/source.md`
- `read knowledge/source_extraction/20260823T014302Z-6eea4b-extract_allowed_evidence.md`
- `read knowledge/source_extraction/20260823T022122Z-0c0ccb-revalidate_source.md`
- `glob knowledge/analytic/**`
- `read knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.md`
- `read knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.json`
- `read knowledge/analytic/20260823T003634Z-5c59c6-derive_source_gap.json:20-26`

Failures: none. Limitation: the actual coefficient remains unavailable without the identified legible row-7 cell.
