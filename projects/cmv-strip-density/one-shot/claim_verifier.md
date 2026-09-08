# Cold Claim Verifier

Independently decide the single proposed `cmv_range_bound` claim. Do not repair, reinterpret, or broaden it.

Inspect the proposal, `proof/RangeReduction.lean`, `contracts/report-contract.lean`, `proof/proof-manifest.json`, `deliverable/citations.json`, the Lean gate receipt, and the deterministic replay receipt. Check:

1. Quantifiers, hypotheses, strict inequalities, and decimal cutoff match `cmv_type_four_range_reduction` exactly.
2. The Lean contract passed and reports only the configured foundational axioms.
3. The exact certificate and citation-complete document were replayed successfully.
4. The proposal retains every source-transfer limitation and makes no full-CMV claim.

Accept only if all four checks hold with no gap. Otherwise reject and identify the smallest exact defect. Return only the required `claim-verdicts-v1` handoff for claim `modeled_range_bound`.
