# CMV Strip-Density Isoperimetry

## Problem

For the planar density

\[
f(x,y)=\begin{cases}
1,& |y|\le 1,\\
\lambda,& |y|>1,
\end{cases}
\qquad \lambda>1,
\]

complete and verify the unresolved comparison in Cañete–Miranda–Vittone's classification of isoperimetric regions. In particular, determine whether a regular type-(iv) region bounded by four circular arcs can ever minimize weighted perimeter at fixed weighted area, and settle CMV Conjecture 3.12 over the entire admissible range.

## Current verified baseline

The retained Lean development proves analytic lower bounds for Morgan's comparison function, a certified strict threshold at \(1.2581840884\), and the formal cap-replacement perimeter inequality for the encoded four-arc geometry. A canonical verifier now checks the exact dyadic coverage, signs, rational tail margins, and hashes of the retained full-domain directed-MPFR ledgers. Their claimed scalar inequality \(\Gamma(\lambda)<0\) for every \(\lambda>1\) remains conditional on the interval generators and equal-area reduction: the verifier does not independently recompute transcendental enclosures. CMV's published classification and geometric reductions remain source prerequisites. The present formal development does **not** formalize that full-domain scalar reduction or prove the globally quantified source-to-model exclusion theorem for every admissible type-(iv) region.

## Required next work

1. Audit the exact CMV definitions, formulas, parameter domains, equality cases, and classification results against `references/Canete2010.pdf`.
2. Reconstruct the type-(iii) and type-(iv) weighted areas and perimeters independently, with explicit branch, angle, orientation, and sign conventions.
3. Compare candidates only at equal weighted area. Define and evaluate the full equal-area solution set, not one optimizer trajectory.
4. Search the complete admissible domain for counterexamples, near-equality configurations, interior stationary points, and minima approaching a boundary.
5. Treat separately the singular limit \(\lambda\to1^+\), candidate degenerations, branch transitions, and the large-\(\lambda\) regime.
6. Convert every decisive numerical claim into an exact enclosure, analytic estimate, or machine-checked theorem.
7. Close the geometric bridge between the abstract Lean coordinate model and CMV's admissible regions, or state the remaining hypotheses precisely.
8. End with the strongest justified theorem, exact unresolved obligations, and a reproducible next campaign plan.

## Current campaign directive

The immediate milestone is a kernel-checked modeled range reduction to
\(51/50=1.02\). Prove declarations with the following observable consequence:

\[
\text{a modeled regular type-(iv) minimizer implies }
1<\lambda<51/50.
\]

Do not spend this milestone trying to close the remaining near-one interval
\(1<\lambda<51/50\). The retained exact-rational suffix already supplies the
computational material needed for the new cutoff:

- `proof/face_bridge_pilot/` and `proof/middle_face_tiling/` certify
  \([51/50,9/7]\), including exact branch, seam, denominator, uniqueness, and
  strict-gap checks;
- `proof/compact_fold_gap/` supplies overlapping compact coverage;
- the existing Lean theorem in `CandidateExclusion.lean` excludes modeled
  type-(iv) minimizers for \(\lambda\ge1.2581840884\);
- \(1.2581840884<9/7\), so a sound formalization of the exact-rational suffix
  composes with the existing Lean theorem to cover every
  \(\lambda\ge51/50\).

The latest semantic audit invalidated an older planning premise:
`proof/verify_calculus.py` does not contain a branch-complete equal-area
envelope theorem. It contains formulas and local identities only. Reconstruct
every reduction actually needed by the suffix theorem. Do not cite the Python
checker, its JSON output, a successful process exit, or generated booleans as
a Lean proof.

Formalize a sound certificate contract in Lean. The kernel must check why the
rational cells imply the required real inequalities and why those inequalities
produce a genuine equal-area type-(iii) competitor with strictly smaller
weighted perimeter. Extend `TypeThreeAssembly.lean` with the exact weighted
area, perimeter, and admissible-competitor facts needed by that argument.
Connect the scalar theorem to `FourArcCandidate` rather than stopping at a
detached numerical lemma.

The milestone is complete only when all of the following hold:

1. `lake build` succeeds from the retained `proof/` project.
2. No changed declaration contains `sorry`, `admit`, a project axiom, an
   unchecked numerical oracle, or `native_decide`.
3. A named theorem proves that every modeled type-(iv) weighted-perimeter
   minimizer has \(\lambda<51/50\), and a companion theorem records the open
   range \(1<\lambda<51/50\).
4. `#print axioms` for both declarations contains only `propext`,
   `Quot.sound`, and `Classical.choice`, or a strict subset.
5. An independent audit checks the exact theorem types, the interval splice,
   certificate coverage, branch hypotheses, and source/model limitations.

Work in bounded modules and retain compilable checkpoints early. Agents must
write partial Lean and machine-readable progress before extended proof search,
then run targeted builds after each declaration. If an agent deadline is
approaching, preserve the smallest compiling prefix and a precise failure
record rather than returning only prose.

Fresh isolated workspaces must run `lake exe cache get` before their first
`lake build`. Do not spend an agent deadline recompiling Mathlib dependencies
from source unless cache retrieval fails; retain the cache failure if it does.

After this milestone, resume the exact-germ and normalized-flow work needed for
the remaining near-one interval, then the source-profile bridge and the full
CMV conjecture. Failed centered-box, barrier-tube, ordered-seed, and matrix
interval-Newton attempts remain rejection evidence and must not be silently
reused.

## Evidence rules

- Primary-source claims require a precise page, theorem, proposition, equation, or line locator.
- Computed claims require retained code, parameters, precision, command, and output.
- Formal claims require the exact Lean declaration and a successful clean build or check.
- Distinguish published, derived, numerically observed, interval-certified, formally verified, inferred, conjectured, and unresolved statements.
- Never claim that agent agreement, a plot, a floating-point sample, or a passing theorem with unmatched hypotheses settles the mathematical problem.
