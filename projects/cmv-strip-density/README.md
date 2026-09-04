# CMV Strip-Density Project

This folder is the canonical record for the Cañete–Miranda–Vittone strip-density isoperimetry problem. `problem.md` defines the research contract; `project.toml` defines the automated regime.

## Current result

The canonical project verifies:

- the analytic definition and derivative identities for Morgan's arc function;
- monotonicity and lower bounds for the comparison function;
- exact rational/numerical certificate inequalities around the critical point;
- the coordinate realization of the doubled-area cap replacement;
- a canonical hash-bound replay of the retained directed-MPFR full-domain sign
  ledgers;
- strict perimeter improvement for the encoded positive geometric branch;
- a closed, branch-complete type-(iii) coordinate carrier, including the major,
  semicircular, and minor upper-arc regimes;
- an abstract type-(iv) exclusion theorem under the formal hypotheses;
- an exact `lambda = 5/4`, type-(iii) semicircular transition certificate,
  including a dyadically isolated equal-area type-(iv) height, a proof that its
  slab exhausts the regular area fiber, strict perimeter improvement, and a
  branch-complete candidate-facing exclusion with no stationarity premise;
- an exact `lambda = 5/4`, type-(iii) endpoint closure certificate: the unique
  regular type-(iii) equal-area root and both matching regular type-(iv) roots
  are dyadically isolated and proved exhaustive, their strict perimeter chain
  is checked from degree-27 Taylor bounds, and every genuine type-(iv)
  candidate with the endpoint area is excluded without stationarity; the
  separate `h4 = 1` branch is ruled out by a strict area inequality;
- an independent, mutation-sensitive calculus checker for the exact type-(iii)
  and type-(iv) Green-integral normal forms, fold derivatives, and
  \(P_i'(h)=hA_i'(h)\) identities;
- a kernel-checked all-root theorem for the type-(iii) area profile at every
  \(\lambda>1\): each horizontal level has at most two roots in \(0<h\le1\);
  any certified negative-fold root is the global least (descending) root, and
  at most one upper root remains;
- an independent exact-rational compact fold-gap certificate on
  \([33/32,9/7]\), with 1,024 adjacent boxes, no unresolved boxes, recomputed
  elementary-function bounds, and four rejected mutations.
- an unconditional modeled type-(iv) range reduction: every weighted-perimeter
  minimizer satisfies \(1<\lambda<51/50\).

The Lean cap-replacement theorem gives the unconditional modeled cutoff

\[
\lambda_* = 1.2581840884.
\]

Separately, the canonical ledger verifier checks exact dyadic endpoints,
adjacency, sign fields, rational tail margins, and artifact hashes for the
retained claim \(\Gamma(\lambda)<0\) for every \(\lambda>1\). That claim
remains conditional on the correctness of the directed-MPFR generators and the
retained equal-area reduction: the verifier does not independently recompute
the transcendental enclosures. This still does **not** settle CMV Conjecture
3.12. The canonical type-(iii) carrier now has kernel-checked weighted-area,
complete-frontier weighted-perimeter, and admissible-competitor realizations
through its major, semicircular, and minor branches. At \(\lambda=5/4\), the
semicircular transition-area fiber has exactly one regular type-(iv) root, in
\([34912/65536,34913/65536]\); Rolle's theorem, the exact area derivative,
strict fold monotonicity, and the lower endpoint area exclude every other
height, including \(h_4=1\). Exact
degree-27 Taylor certificates isolate the unique regular type-(iii) root and
two distinct regular type-(iv) roots matching the type-(iii) endpoint area,
including the near-one type-(iv) root in
\([1046830/1048576,1046831/1048576]\). Rolle's theorem, the exact area
derivatives, and strict fold monotonicity prove that these slabs exhaust all
regular equal-area roots; every corresponding genuine regular candidate is
defeated by the certified regular type-(iii) replacement. A separate exact
endpoint calculation proves the \(h_4=1\) type-(iv) area is strictly larger,
so the candidate-facing exclusion is branch-complete for the endpoint-area
fiber. All 113 actual middle-inventory face bricks, `B0000` through `B0112`,
are kernel-checked end to end on the contiguous interval
\([102001/100000,25781/25000]\). The reusable stationary-pair assembly and
global descending-envelope theorem remove both stationarity and curvature-cell
projection premises: every modeled type-(iv) candidate throughout all bricks,
including \(h_4=1\), has a genuine equal-area type-(iii) competitor with
strictly smaller weighted perimeter. Manifest-generated balanced seam trees
compose the checked cells into one candidate theorem over the full closed
interval.
The lower and upper prototype certificates supply the same branch-complete
stationary-pair promotion on \([51/50,102001/100000]\) and
\([25781/25000,33/32]\), respectively. Exact seam splits compose both
prototypes with `B0000`--`B0112`, excluding every modeled type-(iv) candidate
on the closed interval \([51/50,33/32]\), including both endpoints and
\(h_4=1\), without a stationarity or curvature-cell projection premise. The
same closed range is exposed by the raw-profile source bridge under its
explicit normalization and perimeter-semantics contracts.
The reusable proof-valued `MiddleFaceAssembly.CellCertificate` contract names
the lambda guard, branch bounds, eight strict residual-specific face decisions,
uniform \(K_3<0\), and uniform \(G<0\); its kernel-checked soundness theorem
assembles `MiddleFaceAssembly.Conditions`. These conditions construct a
stationary equal-area pair on the descending type-(iii) branch and promote it
to the branch-complete candidate exclusion. Both retained prototypes and
`B0000` through `B0112` are complete instances, built from exact interval
lemmas rather than serialized Booleans or diagnostic margins.
The shared `MiddleFaceAssembly.EResidual`,
`MiddleFaceAssembly.C4Residual`, `MiddleFaceAssembly.FResidual`, and
`MiddleFaceAssembly.C3Residual` lanes centralize the exact derivative calculus,
mean-value estimates, monotonicity, and strict rho/eta/xi/sigma face margins;
each brick supplies only its exact-rational trigonometric derivative enclosures
and endpoint/origin bounds.
`middle_face_tiling/generate_lean_cell.py` validates each shard's schema and
semantic hash, recomputes outward affine and exact Taylor bounds, and emits the
kernel-replayed cell proof. `middle_face_tiling/generate_lean_batch.py`
additionally verifies the complete manifest's hashes, order, exact seams, and
coverage before emitting a selected cell batch and its balanced aggregate.
Regenerating the final `B0092`--`B0112` batches remains byte-identical. The
widened coarse \(K_3\) enclosure is kernel-checked through `B0111`, the farthest
full-width face brick. The narrower terminal brick `B0112` is kernel-checked
on its actual lambda radius \(3/200000\) and participates in the contiguous
`MiddleFaceCells` aggregate.
The first source/model vertical slice now starts from an independent raw
coordinate definition of regular \(E_4\), with the strict source domain
\(0<h<1\), and proves that its five carrier components are exactly the
normalized `FourArcCandidate.assembly.carrier`. Weighted area and canonical
complete-frontier perimeter equality follow from that set equality rather than
from detached scalar formulas. Every `AdmissibleCompetitor` constructor now
embeds value-preservingly into `FinitePerimeterRegion`, closing the modeled
competitor-quantifier gap. Horizontal placement is now handled by a
kernel-checked density-preserving homeomorphism: planar volume, weighted area,
the complete-frontier measure pushforward, and weighted perimeter are invariant
under every horizontal translation. `MiddleFaceSourceBridge` composes these
facts with both prototypes and `B0000`--`B0112` on
\([51/50,33/32]\); `CompactFirstCellSourceBridge` composes them with
compact box 0 on \([33/32,236601/229376]\), `TransitionSourceBridge`
composes them with the branch-complete transition exclusion at
\(\lambda=5/4\) and weighted area \(9\pi/2\), and
`EndpointClosureSourceBridge` composes them with the branch-complete
type-(iii) endpoint-area exclusion at \(\lambda=5/4\). Every horizontal
translate of the normalized regular raw carrier is unconditionally excluded
under canonical-frontier semantics on the respective cells, transition-area
fiber, or endpoint-area fiber.
The regular source/model parameter bridge is exact in both directions: every
modeled `FourArcCandidate` satisfying the CMV source laws with \(h<1\) recovers
a `CanonicalTypeIVProfile`, normalization returns the original candidate, and
the recovered carrier has exactly its assembly, weighted area, and complete-
frontier weighted perimeter. The \(h=1\) closure remains an explicit separate
endpoint rather than being mislabeled as a regular source profile.
Under abstract CMV source semantics, the corresponding arbitrary
representative is excluded from horizontal congruence, source/model
compatibility, and only the local reduced-boundary/complete-frontier equality
for that representative. The universal CMV classification and that local
boundary-semantics theorem remain open; neither is silently identified with
the model.

The retained calculus pilot additionally reduces the complete scalar
comparison to the sign of the attained type-(iv) fold gap
\(G_\lambda(f_4)\). Its checker reproduces 35 exact rational identities,
168 high-precision branch checks, and rejects all 11 formula mutations. This
is a verified reduction and falsification check, not a proof that the fold gap
is negative on \(1<\lambda<4/\pi\).

The compact certificate proves the retained scalar fold-gap model is strictly
negative throughout \([33/32,9/7]\), which contains \(4/\pi\). The exact germ
checker proves the first nonzero near-one term is
\(-3\pi x^4/4\), but does not yet supply a positive certified neighborhood.
`NearOneNormalizedFlow` kernel-checks exact divisibility and cancellation for
the retained **algebraic row parts**:
\[
s^2\widehat H_3=H_3-2H_2+4H_1+\frac{2\pi}{3}s(H_2-H_1).
\]
`NearOneAnalyticSystem` now gives the missing semantic audit in Lean. It defines
the removable `arctan(x)/x` half-angle system, proves its principal-angle and
sine identities under explicit branch/denominator guards, and proves the exact
source-residual clearings. That audit found that polynomial `H2` is the complete
cleared cosine row, while polynomial `H1`, `areaNumerator`, `H3`, and the
displayed quotient omit explicit angle terms. The module therefore defines and
kernel-checks corrected complete fold, area, and row-operated `H3` numerators
instead of treating the algebraic pieces as complete equations.
`NearOneRegularizedThirdRow` removes that remaining normalization defect. It
represents the second remainder of `arctan(x)/x` by an exact compact-interval
integral, factors both complete angle corrections by \(s^2\), and defines the
complete regularized third row without division by \(s\). Lean proves
\[
s^2\widehat H_{3,\mathrm{complete}}=
H_{3,\mathrm{complete}}-2H_2+4H_{1,\mathrm{complete}}
+\frac{2\pi}{3}s(H_2-H_{1,\mathrm{complete}})
\]
under only the three chart-denominator guards. The numerator vanishes at
\(s=0\), the quotient is continuous there, and its endpoint differs from the
old algebraic quotient by \(80z-192a\). On the source fold and cosine equations,
the regularized row has exactly the source equal-area zero set for \(s\ne0\).
The exact cusp coordinates
\((z,a,b)=(\pi,5\pi/12,-44+19\pi^2/24)\) solve all three complete normalized
rows at \(s=0\).
The module packages these rows as a three-coordinate root map and proves that
its exact \((z,a,b)\)-Jacobian at the cusp is
\[
\begin{pmatrix}
2&0&0\\
-40&96&0\\
\frac{8(3\pi^2-412)}3&-\frac{2(7\pi^2-2880)}3&-4\pi
\end{pmatrix}.
\]
Its determinant is \(-768\pi<0\), so the complete normalized endpoint system is
nondegenerate.
The exact parameter derivative at the cusp is
\[
\partial_sF=
\left(-2\pi^2,\ \frac{2(17\pi^2-1056)}3,\
-\frac{247\pi^4-63840\pi^2+3041280}{216}\right).
\]
`NearOneCuspTangent` kernel-checks these analytic derivatives, including the
integral remainder contribution, and proves that the unique solution of
\(Jv+\partial_sF=0\) is
\[
v=\left(\pi^2,\ \frac{43\pi^2+1056}{144},\
\frac{\pi(295\pi^2-14256)}{216}\right).
\]
This is the forced first-order tangent if a branch exists; it is not a
branch-existence theorem.
`NearOneShearCoordinates` turns this tangent data into the local chart needed
for interval cells. It uses the determinant-one lower-triangular shear
\[
S=\begin{pmatrix}
1&0&0\\
5/12&1&0\\
(109\pi^2-5376)/(72\pi)&(2880-7\pi^2)/(6\pi)&1
\end{pmatrix},
\]
centers physical coordinates at \(x_0+s v\), and negates only the third
residual. Lean proves both the exact matrix identity and the actual
coordinate-Jacobian statement for the transformed root map:
\[
J S=\operatorname{diag}(2,96,-4\pi),\qquad
D_u\widetilde F(0,0)=\operatorname{diag}(2,96,4\pi).
\]
The row orientation preserves the root set and the shear has determinant one.
This positive diagonal linearization does not itself prove branch existence.
Global rational lower and upper enclosures for the integral
remainder now make the complete row accessible to exact interval arithmetic:
\[
-\frac13+\frac{x^2}{5}-\frac{x^4}{7}
+\frac{x^6}{9(1+x^2)}
\le J(x)\le
-\frac13+\frac{x^2}{5}-\frac{x^4}{7(1+x^2)}.
\]
`NearOneRescaledOrientedMap` now divides the tangent-centered transformed map
by \(s^2\) away from the cusp and supplies exact pole-free formulas at the
endpoint. Retained two-jet calculations prove continuity there for all three
coordinates. `NearOneRescaledSecondRowContinuity` additionally proves joint
continuity of the second row by coefficientwise polynomial continuity and a
uniform degree bound. `NearOneRescaledFirstCell` fixes the exact rational
endpoint box \([52,54]\times[27,28]\times[-3822,-3821]\), proves all six strict
endpoint face signs, and proves that some exact positive reciprocal-natural
slice below \(1/100\) simultaneously retains all six complete face signs. The
complete rescaled map is continuous on that fixed-scale box.
`BoxPoincareMiranda` derives a finite-dimensional opposite-face zero theorem
from the kernel-checked Brouwer fixed-point theorem for products of simplices in
the pinned `math-xmum/Brouwer` dependency; the theorem is dimension-generic and
is used below at both `Fin 3` and `Fin 4`.
Applying it at `Fin 3` gives a simultaneous zero of all three rescaled
equations at the same positive scale and, by exact rescaling, a genuine zero of
the corrected near-one analytic system. `NearOneFirstCellSource` proves uniformly
on every positive box slice below \(1/100\) that the cancellation-free cubic
density quotient lies strictly between \(12\) and \(14\), the physical
half-angle coordinates satisfy \(0<s<Y<1\) and \(0<W<V<1\), and their exact
incidence density satisfies \(1<\lambda<51/50\). These bounds imply all principal-chart
denominator and arctangent-addition guards, so the same existential root is now
kernel-checked to satisfy those strict coordinate and density bounds together
with the original source fold, incidence, and equal-area residuals. With
\(h_4=\operatorname{halfCos}(s)\) and
\(h_3=(1+\operatorname{halfCos}(W))/2\), those same residuals are now
kernel-checked to produce an actual `LeanSuffixAnalytic.StationaryEqualAreaPair`.
`NearOneFirstCellGap` clears the reduced radical gap by an explicitly positive
source denominator, removes its exact \(s^4\) cusp zero by two polynomial
divisions, and proves the endpoint coefficient is uniformly negative on the
complete box. Compactness makes the face and gap signs persist uniformly at
every sufficiently small positive scale. Poincare--Miranda therefore gives a
source root at each such scale; its stationary equal-area pair is
kernel-checked to lie on the negative type-(iii) fold branch and give a strict
type-(iii) perimeter improvement. The branch sign follows without a
second cusp rescaling: exact endpoint-box arithmetic gives \(h_3<h_4\), the
same-curvature area comparison puts the type-(iii) area at \(h_4\) below the
equal-area value at \(h_3\), and the mean-value theorem plus strict fold
monotonicity forces the type-(iii) fold at \(h_3\) to be negative.
`NearOnePrescribedDensity` adds the scale coordinate and the cancellation-free
density residual to form the exact four-dimensional prism
\([52,54]\times[27,28]\times[-3822,-3821]\times[0,r/2]\). It proves joint
continuity of the complete map on this prism, including its cusp face, and all
eight strict opposite-face signs for every sufficiently small \(r>0\).
Poincare--Miranda therefore supplies a positive-scale simultaneous root with
exact density \(1+r^3\). An intermediate-value argument for \(r\mapsto r^3\)
upgrades this to a kernel-checked \(\delta>0\) such that every
\(1<\lambda<1+\delta\) has a source stationary equal-area pair on the negative
type-(iii) fold branch with strict type-(iii) perimeter improvement.
The explicit-certificate interface now isolates the remaining quantitative
obligation: any proved uniform six-face radius \(R\le1/100\) yields roots for
every \(0<r<2R\), and hence an exact density seam
\(1<\lambda<1+(2R)^3\), with no further compactness extraction.
`NearOneFirstFaceBounds` already certifies the first pair of faces throughout
the literal interval \(0\le s\le10^{-6}\).
The third-row cusp faces have exact margins below \(-7\) and above \(4\), so it is enough to
bound their positive-scale perturbation by \(4\).  The global arctangent
remainder bounds have also been recentered to the cancellation-preserving form
\(0\le J(x)+1/3\le x^2/5\) for \(x^2\le1\).  A literal certified value for the
complete six-face radius \(R\) is still unresolved.
The type-(iii) area is now kernel-checked to diverge to \(+\infty\) as
\(h\to0^+\), while every regular type-(iv) fold root is a global area minimum
on \(0<h\le1\). At the same positive curvature, the exact type-(iii) area is
strictly smaller than the type-(iv) area for every \(\lambda>1\), including the
\(h=1\) formula closure. Consequently, any certified stationary equal-area pair
with negative type-(iii) fold constructs the unique regular descending
equal-area root for every regular or endpoint type-(iv) curvature, and that
root satisfies \(h_3<h_4\). Compact branch trapping now proves this canonical
root is continuous on \(0<h_4\le1\), including one-sided continuity of the
perimeter gap at \(h_4=1\); neither continuity statement remains an envelope
perimeter gap at `h_4=1`; neither continuity statement remains an envelope
hypothesis. All 1,024 concrete compact cells promote their stationary strict
gaps to every modeled type-(iv) candidate and compose across every exact seam
on \([33/32,9/7]\), including \(h_4=1\).
For the first compact
cell, the source bridge transfers this conclusion to every horizontally
congruent regular raw carrier under canonical-frontier semantics; abstract
source semantics still requires explicit model compatibility and the
carrier-local reduced-boundary/complete-frontier equality.
The all-root theorem still classifies any remaining equal-area root as the
unique upper root.
The concrete `B0000` face cell now has the same branch-complete conclusion:
its certified stationary pair excludes every modeled type-(iv) candidate at
each lambda in \([102001/100000,102011/100000]\), including \(h_4=1\), without
a stationarity or cell-projection premise.
The exact-rational checkers independently certify the complete scalar suffix
\([51/50,9/7]\): the middle checker proves exact adjacency, both prototype
contacts, every face and uniqueness decision, strict gap negativity, and 30
mutation rejections on \([102001/100000,25781/25000]\); the compact checker
proves all 1,024 boxes, 1,023 exact adjacencies, and four mutation rejections on
\([33/32,9/7]\). Lean replays both prototypes, all 113 middle cells, and all
1,024 compact cells. `CMVModeledCutoff` composes their unconditional
candidate-facing exclusions with the cap-replacement theorem above
\(1.2581840884\). Its named kernel-checked conclusions state that every modeled
type-(iv) weighted-perimeter minimizer has
\(1<\lambda<51/50\), with no stationarity or cell-projection premise and with
the \(h_4=1\) endpoint included.
The same module now composes the full cutoff with `CMVSourceBridge`:
`sourceCarrier_minimizer_open_range_51_50` transfers the conclusion to an
arbitrary regular source representative under the explicit normalization and
source/model boundary-compatibility contracts, while
`canonicalCarrier_minimizer_open_range_51_50` proves the range directly for the
raw \(E_4\) carrier under canonical complete-frontier semantics.
The earlier near-one barrier failed its first inward-face check, excluded the
exact germ initial value, and missed the prototype branch at its terminal seam;
the scale-density prism now replaces it on a proved, existential neighborhood
\((1,1+\delta)\). Extending these certificates through the remaining interval
\([1+\delta,51/50)\), universal source classification, and reduced-boundary
compatibility remain open. The modeled cutoff does not identify
the complete-frontier model with arbitrary CMV source representatives.

The publication-ready theorem statement, proof architecture, direct links to
the cited Lean declarations, exact trust boundary, and reproduction record are
in [`reports/lean-verified-cmv-cutoff.pdf`](reports/lean-verified-cmv-cutoff.pdf),
with [Markdown](reports/lean-verified-cmv-cutoff.md) and
[standalone HTML](reports/lean-verified-cmv-cutoff.html) sources.

## Folder contract

- `references/` — frozen publications and bibliography.
- `knowledge/` — promoted campaign work organized by source analysis, analytic work, computation, formalization, review, and research state.
- `proof/` — canonical Lean sources, Lake configuration, exact certificates, and certificate checkers.
- `reports/lean-verified-cmv-cutoff.{md,html,pdf}` — canonical Lean-verified
  \(51/50\) cutoff paper.
- `reports/build-lean-verified-cmv-cutoff.sh` — reproducible HTML/PDF renderer.
- `reports/formal-proof.ipynb` — source notebook for the earlier mathematical presentation.
- `reports/formal-proof.html` — rendered professor-facing report.
- `reports/technical-note.md` — compact technical narrative.
- `runs/` — local campaign workspaces. Reviewed artifacts are promoted into
  `proof/` or `knowledge/`; newly generated runs are ignored by Git.

## Reproduce the proof

Compile the paper's exported theorem and print its axiom dependencies:

```bash
cd proof
lake build CMVModeledCutoff
lake env lean CMVCutoffAssumptions.lean
```

For full certificate regeneration, independent checkers, and the complete
Lean build:
```bash
cd proof
python middle_face_tiling/generate_lean_batch.py --first 92 --last 103
python middle_face_tiling/generate_lean_batch.py --first 104 --last 112
python compact_fold_gap/generate_compact_lean.py
first=11
prefix=CompactCells2To10
while [ "$first" -le 1023 ]; do
  last=$((first + 31))
  if [ "$last" -gt 1023 ]; then last=1023; fi
  python compact_fold_gap/generate_compact_lean.py \
    --first "$first" --last "$last" --prefix-module "$prefix"
  prefix="CompactCells${first}To${last}"
  first=$((last + 1))
done
lake build
lake env lean _Assumptions.lean
uv run python verify_certificate.py
uv run python verify_full_domain.py
uv run python verify_calculus.py
python compact_fold_gap/check_compact_certificate.py compact_fold_gap/compact_certificate.json
python compact_fold_gap/run_mutations.py
python exact_germ/exact_germ_checker.py --output exact_germ/independent-check.json
python exact_germ/semantic_audit.py
python face_bridge_pilot/check_bridge.py --output face_bridge_pilot/independent-check.json
python face_bridge_pilot/run_mutations.py
python middle_face_tiling/check_tiling.py middle_face_tiling/manifest.json --output middle_face_tiling/independent-check.json
python middle_face_tiling/run_mutations.py
```

Rebuild the canonical paper from its cited Markdown and bibliography:

```bash
cd ../reports
./build-lean-verified-cmv-cutoff.sh
```

## Start a new campaign

From the repository root:

```bash
uv run agentic-lean-math-assistant regime-run \
  --project projects/cmv-strip-density/project.toml
```

Every new campaign begins with an agent-run publication-research gate. Prior research state and reference digests are retained under `knowledge/research/`; unchanged source coverage can therefore be skipped explicitly rather than rediscovered on every run.

The CMV manifest explicitly runs its OMP agents without the OS sandbox so they
can use the operator's existing OMP login. This is a trusted-project decision:
agents can execute repository-approved tools with the operator's host access.
Do not use this manifest for untrusted problem statements or input snapshots.

For bounded back-to-back campaigns using the retained success contract:

```bash
uv run agentic-lean-math-assistant autonomy-run \
  --project projects/cmv-strip-density/project.toml \
  --headless
```
