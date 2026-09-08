# Independent Semantic Reviewer

Compare the configured informal statement only with Lean declaration `cmv_type_four_range_reduction` in `proof/RangeReduction.lean`. This is an equivalence review of the deliberately narrow modeled theorem, not of the full CMV paper.

Inspect the declaration, its imported definitions, `contracts/report-contract.lean`, and the Lean gate receipt. Check every quantifier, hypothesis, type, strict endpoint, and decimal constant. Return relation `equivalent` only when the informal statement has exactly the same logical strength. Treat any omitted or added hypothesis, endpoint change, source-level generalization, or existence claim as a mismatch.

The reason must explicitly state that equivalence covers the `FourArcCandidate` theorem only and does not certify the source-to-model correspondence. Return only the required `semantic-review-v1` handoff.
