# Revalidation evidence ledger

| Item | Literal evidence | Locator |
|---|---|---|
| Table 2 row \(j=7\), coefficient cell | `[ROW ILLEGIBLE IN RETAINED SCAN]` | `references/source.md:7`, Table 2 row `j = 7`, column `coefficient cⱼ` |
| Neighboring-row restriction | “Values in neighboring rows are not evidence of an interpolation rule.” | `problem.md:3` |
| Pattern-inference restriction | “Do not infer a pattern unless the source explicitly states one.” | `problem.md:5` |
| Supplied statement about recurrence, interpolation, and closed formula | “The table caption gives no recurrence, interpolation rule, or closed formula.” | `references/source.md:10` |
| Availability of the original legible row | “The original page containing a legible row 7 is unavailable.” | `references/source.md:10` |
| Required fragment if recovery fails | “If the coefficient cannot be recovered uniquely, identify the exact unavailable source fragment required.” | `problem.md:5` |

## Result

The retained row contains an illegibility marker, not a numerical coefficient. Therefore the exact value of \(c_7\) **cannot be recovered uniquely from the permitted transcription**.

The exact unavailable fragment required is:

> **The legible coefficient cell \(c_7\) in Table 2, row \(j=7\), on the unavailable original page.**

Rows \(j=5\), \(j=6\), and \(j=8\) were not used as constraints or evidence for interpolation or any unstated pattern. No numerical coefficient was derived or guessed.

## Comparison with retained extraction

The current files agree with `knowledge/source_extraction/20260823T014302Z-6eea4b-extract_allowed_evidence.md`:

- Same row-\(7\) cell text.
- Same neighboring-row and pattern-inference restrictions.
- Same absence of a recurrence, interpolation rule, or closed formula.
- Same statement that the original legible row is unavailable.
- Same required missing fragment.

**Substantive discrepancy: none. The retained extraction remains current.**

`knowledge/index.json` lists the retained report, and its recorded report SHA-256 agrees with the SHA-256 repeated in `knowledge/source_extraction/20260823T014302Z-6eea4b-extract_allowed_evidence.json`.

## Inspection record and limitation

Read operations:

- `problem.md:raw`
- `problem.md:1-5`
- `references/source.md:raw`
- `references/source.md:1-10`
- `knowledge/index.json:raw`
- `knowledge/source_extraction/20260823T014302Z-6eea4b-extract_allowed_evidence.md:raw`
- `knowledge/source_extraction/20260823T014302Z-6eea4b-extract_allowed_evidence.json:raw`

A lookup for the provenance paths named by the retained metadata—`input-snapshot/**` and `agents/source_extraction/extract_allowed_evidence/**`—returned “Path not found.” Thus those historical snapshots could not be independently compared byte-for-byte. This does not create a content discrepancy: every literal claim preserved in the retained report matches the current permitted files. No external source was consulted.
