# One-shot CMV range-reduction deliverable

Produce a recruiter-facing summary and a citation-complete technical report in one fail-closed campaign.

1. Assemble and kernel-check `proof/RangeReduction.lean` against the immutable external Lean contract. The exact certificate checker must also pass.
2. Render one-page `deliverable/Portfolio.html` and `deliverable/Portfolio.pdf` entry points plus the full `deliverable/Proof.html` and `deliverable/Proof.pdf`. Every substantive mathematical claim must resolve to the retained CMV PDF or a compiled Lean declaration.
3. Bind the frozen proof and contract hashes, then replay the certificate and document checks. A cold claim verifier must close the native claim ledger against that evidence and the retained Lean gate.
4. Independently compare the narrow informal statement with `cmv_type_four_range_reduction`. Do not treat equivalence of that modeled theorem as verification of the source-to-model correspondence.

A failed Lean, certificate, citation, render, claim, or semantic stage is retained as its own failure class. Artifact promotion requires every class to pass.

After a complete run, `publish_release.py` can verify, atomically publish, and deterministically archive the promoted bundle:

```bash
uv run python projects/cmv-strip-density/one-shot/publish_release.py \
  --run <run-directory> \
  --destination ~/Downloads/CMV-One-Shot-Proof \
  --archive ~/Downloads/CMV-One-Shot-Proof.tar.gz \
  --replace
```
