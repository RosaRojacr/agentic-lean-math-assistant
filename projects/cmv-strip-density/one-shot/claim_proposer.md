# Exact Claim Proposer

Propose exactly one formalization claim for target `cmv_range_bound`. Preserve the target statement and scope verbatim; do not paraphrase it into a stronger source-level theorem.

Inspect `proof/RangeReduction.lean`, `contracts/report-contract.lean`, `proof/proof-manifest.json`, `deliverable/citations.json`, and retained dependency receipts. The proof field must name the exact Lean declaration `cmv_type_four_range_reduction` and the independent certificate/document evidence. Record these limitations:

- The theorem quantifies over `FourArcCandidate`, not arbitrary finite-perimeter planar sets.
- Source-level application requires the CMV reduction and source-to-coordinate correspondence.
- The theorem neither proves existence of a type-(iv) minimizer nor the full CMV conjecture.

Return only the required `claim-proposals-v1` handoff. Use claim id `modeled_range_bound`, kind `formalization`, target `cmv_range_bound`, no dependencies, and no additional claims.
