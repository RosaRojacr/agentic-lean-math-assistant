# CMV strip-density cutoff

This directory contains the Lean source and publication artifacts for the
machine-checked cutoff in the Cañete–Miranda–Vittone strip-density problem.

## Verified result

Under the modeled four-arc hypotheses encoded by
[`FourArcCandidate.SatisfiesCMVTypeIVHypotheses`](proof/FourArcCandidate.lean),
Lean proves that no type-(iv) candidate minimizes weighted perimeter when

\[
\lambda \ge \frac{51}{50}.
\]

The exported theorem is
[`CMVModeledCutoff.candidate_not_isWeightedPerimeterMinimizer_from_51_50`](proof/CMVModeledCutoff.lean).
It combines:

- the exact-rational equal-area type-(iii) comparison on
  \([51/50,9/7]\); and
- the geometric two-cap-to-one-cap replacement above \(9/7\).

The result is universal in the modeled candidate curvature and quantifies
minimality against genuine measurable competitors. It does not prove the
remaining interval \(1<\lambda<51/50\), universal source classification,
source-to-model correspondence, or the full CMV conjecture.

## Read the paper

- [Lean-verified paper (PDF)](reports/lean-verified-cmv-cutoff.pdf)
- [Standalone HTML edition](reports/lean-verified-cmv-cutoff.html)
- [Markdown source](reports/lean-verified-cmv-cutoff.md)
- [Primary CMV source](references/Canete2010.pdf)

The paper links named declarations to exact GitHub source lines, states the
formal assumptions, records the axiom audit, and separates kernel-checked
claims from source interpretation and open mathematics.

## Reproduce the theorem

Install Lean through `elan`, then run from the repository root:

```bash
cd projects/cmv-strip-density/proof
lake build CMVModeledCutoff
lake env lean CMVCutoffAssumptions.lean
```

The first command builds the theorem and its complete local import closure.
The second prints the axioms of the three exported cutoff declarations. The
expected noncomputable Mathlib axiom set is:

```text
propext
Classical.choice
Quot.sound
```

No theorem in the cutoff source uses `sorry`, `admit`, a project-defined
`axiom`, or `native_decide`.

## Rebuild the publication

The renderer requires Pandoc and a Chromium-family browser:

```bash
cd projects/cmv-strip-density/reports
./build-lean-verified-cmv-cutoff.sh
```

It regenerates the standalone HTML and PDF from the Markdown manuscript,
stylesheet, and bibliography.

## Proof map

- [`CMVSuffixModel.lean`](proof/CMVSuffixModel.lean): scalar comparison and
  exact interval data.
- [`ScalarSuffixCertificate.lean`](proof/ScalarSuffixCertificate.lean): exact
  rational cell certificates.
- [`MiddleFaceCells.lean`](proof/MiddleFaceCells.lean) and
  `MiddleFaceCell*.lean`: middle-strip tiling certificate.
- [`CompactCellAssembly.lean`](proof/CompactCellAssembly.lean) and
  `CompactCells*.lean`: compact near-one suffix certificate.
- [`SameCurvatureArea.lean`](proof/SameCurvatureArea.lean): equal-area
  competitor and strict weighted-perimeter comparison.
- [`CMVSourceBridge.lean`](proof/CMVSourceBridge.lean): source-coordinate
  carrier statements.
- [`CMVModeledCutoff.lean`](proof/CMVModeledCutoff.lean): final interval splice.
- [`CMVCutoffAssumptions.lean`](proof/CMVCutoffAssumptions.lean): focused axiom
  audit.

Generated rational leaves are committed because they are proof terms checked
by Lean's kernel. Python generators and exploratory notebooks are not part of
the trusted theorem path.
