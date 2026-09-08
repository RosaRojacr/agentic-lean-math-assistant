Completed source reconstruction.

Artifacts:

- `agents/source_analysis/source_reconstruction/reconstruction.md`
- `agents/source_analysis/source_reconstruction/verify_coordinate_formulas.py`

The report contains:

- SHA-256 identity and exact PDF/printed-page locators for every requested CMV statement.
- Audited density, reduced-boundary perimeter, Snell-law, symmetry, classification, admissibility, equality, and degeneration conventions.
- Independent coordinate derivations of all four type-(iii)/(iv) area and perimeter formulas.
- Explicit principal inverse-trigonometric branches, circle centers, endpoints, segment constraints, major/minor transitions, and `h→0+`/`h=1` behavior.
- Source-to-Lean reconciliation with file-line locators.
- Nine-item discrepancy ledger.
- Precise remaining source-to-model bridge hypotheses and reproducible next campaign.

Verification:

- Coordinate verifier: exit 0 at 80-digit precision; largest sampled formula residual `8.6361686e-78`.
- Lean: `/home/rosa/.elan/bin/lake build` from `proof/` succeeded, all 8,707 jobs.
- Source identity: `references/Canete2010.pdf`, 40 pages, SHA-256  
  `0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230`.

Strongest justified conclusion: CMV’s four displayed type-(iii)/(iv) formulas are independently recovered with branch and endpoint control. The retained Lean model verifies type-(iv) cap-replacement exclusion for `λ ≥ 1.2581840884`. Global exclusion for `1 < λ < 1.2581840884`, exhaustive equal-area comparison, and Conjecture 3.12 remain unresolved.
