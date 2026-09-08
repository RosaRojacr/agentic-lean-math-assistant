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
- a universal modeled type-(iv) exclusion at every admissible density
  \(\lambda>1\): a denominator-free fold IVT produces an interior stationary
  type-(iv) height, a finite endpoint area bracket produces a strictly ordered
  equal-area type-(iii) height, and the variational transfer proves strictly
  smaller weighted perimeter;
- exact extended relaxed-perimeter equality for every regular canonical
  type-(iv) carrier, and source admissibility with a sharp recovery upper bound
  for every actual `TypeThreeAssembly`;
- a direct source-level exclusion for every literal `FourArcCandidate` at
  every \(\lambda>1\), including \(h=1\), with no contact-law premise: zero
  signed defect uses the recovered type-(iii) equal-area comparison, while
  either nonzero defect sign uses exact-area constrained chord variation and
  sharp recovery of an actual unequal-radius competitor;
- exact and almost-everywhere horizontal transport of that exclusion, together
  with a shared raw-coordinate `sourceRadius ≥ 1` interface whose candidate and
  carrier identification use only radius, minor-angle, and placement geometry;
- a symmetry-free bilateral Figure-4 source interface: four signed Snell laws
  derive the vertical reflection axis and feed the existing scalar reduction
  without assumed symmetry data. Literal \(\lambda=2\) specimens at \(R=2\)
  and \(R=1\) use bounded open interiors with exact four-arc frontiers, full
  regular-point local one-sidedness, almost-everywhere agreement, and arbitrary
  horizontal placement;
- a source-independent Figure-3 incidence signature covering both vertical
  orientations, degenerate interface segments, and the unresolved radius-one
  boundary, plus a literal model-side obstruction proving that an equal-radius
  contact-law exterior chord cannot fit in any horizontal translate of an
  actual type-(iii) lower-interface section; the radius-two singleton section
  is included explicitly.

`UniversalStationaryPair` kernel-checks the all-density scalar witness.
`CMVCanonicalLowerBound`, `CMVTypeThreeSharpRecovery`, and
`CMVTypeThreeSourceExclusion` connect it to the literal relaxed source
semantics. The earlier explicit \(51/50\) cell cutoff and cap-replacement
inventory remain independently checked, but are no longer the sharp modeled or
classified-source range restriction.

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
The source-facing path starts from an independent raw coordinate definition of
the five-piece type-(iv) carrier.
`RawFourArcCoordinates.SatisfiesClosedGeometry` records only the common-radius
bound \(R\ge1\) and the principal minor-angle domain; horizontal placement is
part of the raw coordinates. It constructs the literal `FourArcCandidate` and
identifies its carrier without density or contact data.
`RawFourArcCoordinates.SatisfiesClosedSnell` separately adds \(\lambda>1\) and
the transverse-contact equation when the scalar CMV normalization is needed.
For \(R>1\), that normalized candidate is exactly the existing
`CanonicalTypeIVProfile`; for \(R=1\), it is exactly
`FourArcCandidate.endpoint`. Horizontal translation and almost-everywhere
replacement preserve weighted area and extended relaxed perimeter.

The relaxation is source-located: source admissibility requires null
measurability, finite relaxed perimeter, and integrable weighted area.
Profilewise squared-width recovery proves exact extended relaxed-perimeter
equality for every regular canonical carrier. A separate branch-complete smooth
recovery handles every actual type-(iii) assembly, including the lower-contact,
upper-contact, and radius-two-disk branches, and bounds its source perimeter by
its literal complete-frontier value.

Candidate-level tangent-patch exhaustion proves the lower bound needed for
source comparison. Four pairwise-disjoint upper, lower, right, and left arc
families approximate the complete frontier and charge one global `smoothCost`;
the characteristic-distance error vanishes along every convergent
`SmoothSequence`. This works for every \(0<h\le1\), so the original endpoint
needs no recovery or finiteness assumption. For a literal candidate, the exact
signed defect is \(\lambda\cos\alpha-h\). If it vanishes, the unchanged
stationary type-(iii) construction supplies the recovered equal-area
competitor. If it has either nonzero sign, constrained chord variation supplies
a strict complete-frontier descent; at \(h=1\), one-sided curvature
perturbation keeps the strict gap, moves the competitor below curvature one,
and corrects its two cap areas exactly. Sharp four-arc recovery then gives an
actual source-admissible unequal-radius competitor. Thus literal, endpoint,
exact-horizontal, almost-everywhere-horizontal, and raw-coordinate
non-minimality hold for all \(\lambda>1\) without `model_covered`,
`CompatibleWithModel`, or a caller-supplied Snell/contact law.

The Figure-4 scalar core of Lemma 3.8 Step 2 is also formalized. A
symmetry-free `BilateralSourceIncidence` starts from the actual bounded open
representative, complete four-circle frontier, local one-sidedness, endpoint
incidence, and three independent signed Snell laws. The upper pair forces equal
strip-center heights; the fourth signed law follows from the lower-left law before
the unchanged `SourceGeometry` scalar reduction proves both strip components
equal \(1/R\). Literal \(\lambda=2\), \(R=2\) and \(R=1\) four-arc sources
exercise this producer and its closed-Snell consumer under arbitrary horizontal
translation.
`CMVSourceSectionClassification` isolates the upstream measure-theoretic step.
The raw carrier is closed and Borel measurable; almost-everywhere agreement of
almost every horizontal slice implies planar almost-everywhere equality by a
checked Fubini argument.

Source locators and separation of arguments:

- Proposition 2.13, equation (13), printed page 9 (with the discussion
  continuing on page 10), derives Snell refraction only for an isoperimetric
  boundary crossing a density interface transversally with regular traces and
  the stated tangent spaces.
- Lemma 3.8, printed pages 15--18, classifies vertically symmetric strip
  candidates after invoking Snell's law and common-curvature continuation.
  Its Step 2 and equations (24)--(25), printed pages 16--17, contain the
  Figure-4 strip-height calculation; Proposition 3.9, printed page 18, supplies
  vertical reflection for an isoperimetric region.
- `CMVFourArcChordVariation` is a different statement: it varies the attachment
  chord inside the explicit four-arc assembly while preserving weighted area.
  Its derivative is \(2(\lambda\cos\alpha-h)\). It neither derives nor assumes
  Proposition 2.13's transverse-contact law.

The Lean bilateral producer still imports none of Proposition 3.9's conclusion:
its reflection proof uses only the endpoint/circle incidences, endpoint order,
branch signs, common radius, and three independent signed local Snell equations
stored in `BilateralSourceIncidence`; the lower-right equation is a theorem.

Universal geometric/GMT classification remains unresolved. In particular, no
theorem yet derives bilateral local Snell laws, common-circle geometry,
configuration enumeration, or exact/almost-everywhere representative
identification from every source-admissible regular type-(iv) minimizer.
Bilateral symmetry inputs and minimizer-to-common-circle extraction remain open.
The frozen Figure-5 geometry forces both strip-circle centers onto \(y=0\) and
then forces \(R=1\) from its four literal strip
tangencies, but its one- and two-cap segmented carriers still lack the
source-connected area/perimeter comparison needed for exclusion.
Arbitrary-competitor `model_covered` and general reduced-boundary/model compatibility remain
auxiliary open routes, but neither is a premise of the direct source
comparison. The project therefore does not claim an unconditional proof of
CMV Conjecture 3.12.

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
density quotient lies strictly between \(251/20\) and \(14\), the physical
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
The explicit-certificate interface isolates the quantitative obligation: a
uniform six-face radius \(R\le1/126334\) yields roots for every \(0<r<2R\),
and hence an exact density seam \(1<\lambda<1+(2R)^3\), with no further
compactness extraction.
`NearOneFirstFaceBounds` and `NearOneSecondFaceBounds` certify the first two
pairs of faces throughout \(0\le s\le1/126334\). The second-row proof
regroups its cubic coefficient before taking absolute values, bounding it by
\(166112\) and reducing the complete base-tail bound from \(837000\) to \(166200\).
`NearOneThirdFaceBounds` gives uniform rational bounds for every physical
coordinate and angle-addition denominator on that interval. It bounds the
four centered arctangent square remainders by \(1/8000000000\), freezes them
at their common cusp value \(-1/3\), proves the resulting nonlinear replacement
changes the honest regularized third row by at most \(s^2/1000\), and reduces
both third-coordinate face signs to
\[
\left|F_{\mathrm{frozen}}(s,q)-s^2F_3(0,q)\right|
  < \frac{3999}{1000}s^2.
\]
`NearOneThirdFrozenMajorantTenthBounds` bounds the retained \(K\) DAG by
\(161/10\) at radius \(1/10\), and consequently sharpens the scalar bounds for
the fold, cosine, area, and \(q'\) DAGs to \(29/2\), \(9553/5\),
\(160443/50\), and \(83/4\). Their exact component sum bounds the frozen
third-row numerator by \(6750317/600\). The rho numerator majorant is exactly
bounded by \(1313/1250\), and the common-denominator majorant is bounded by
\(43923/5120\), sharpening the former \(429/50\) bound. Propagating those
factors without integer widening gives exact four-bar and three-bar bounds
\(26379901/50000\) and \(2661239/200\).
Using \(64883/25\) for the \(\pi\)-coefficient majorant, the common-numerator
bound is \(3935312342799/400000\). After the endpoint term, the radius-\(1/10\)
cleared-error majorant is at most \(7870625783673/800000\), and its fourth-order
tail is at most \(7870625783673/80\). On the physical radius \(1/126334\),
the latter rounds upward to \(778752\). The signed component bounds
\(c_{\rm base}\le56887671/50\), \(c_0\le201407/10\),
\(c_1\le-938811/5\), and \(-936971/1000\le c_2\) give the cubic bound
\(736875\) and cleared cubic quotient \(1515627\). The resulting frozen-row
comparison has exact positive slack \(366813/23198080750\), so
`explicit_all_face_cell_of_frozen_estimate` unconditionally composes all six
face signs on the closed interval through \(1/126334\).
`NearOneGapBounds` bounds the degree-three coefficient by \(3408\), the
degree-four contribution linearly in \(s\), and every higher contribution
quadratically in \(s\). It certifies on the same box and scale interval
\[
|G(s,q)-G(0,q)|\le59916s,\qquad G(0,q)<-10,\qquad
G(s,q)<-\frac{19}{2}.
\]
Here \(G\) is `poleFreeReducedGap`; its negative sign transfers to the actual
source reduced gap at every positive scale.
`prescribedDensity_lambda_explicit_first_cell` gives every strict-improvement
conclusion for
\(1<\lambda<1+(2/200000)^3\).
The first fixed prism, with scale coordinate in
\([1/400000,1/200000]\), covers that seam and continues through
\[
1+\frac{251}{20}\left(\frac1{200000}\right)^3.
\]
The next fixed prism uses \([1/360000,1/180000]\), starts at exactly that
closed endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{180000}\right)^3.
\]
The third fixed prism uses \([1/359336,1/179668]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{179668}\right)^3.
\]
The fourth fixed prism uses \([1/340000,1/170000]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{170000}\right)^3.
\]
The fifth fixed prism uses \([1/336000,1/168000]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{168000}\right)^3.
\]
The sixth fixed prism uses \([1/335000,1/167500]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{167500}\right)^3.
\]
The seventh fixed prism uses \([1/334802,1/167401]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{167401}\right)^3.
\]
The eighth fixed prism uses \([1/328000,1/164000]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{164000}\right)^3.
\]
The ninth fixed prism uses \([1/327870,1/163935]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{163935}\right)^3.
\]
The tenth fixed prism uses \([1/322000,1/161000]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{161000}\right)^3.
\]
The eleventh fixed prism uses \([1/321800,1/160900]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160900}\right)^3.
\]
The twelfth fixed prism uses \([1/321658,1/160829]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160829}\right)^3.
\]
The thirteenth fixed prism uses \([1/321634,1/160817]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160817}\right)^3.
\]
The fourteenth fixed prism uses \([1/321556,1/160778]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160778}\right)^3.
\]
The fifteenth fixed prism uses \([1/321554,1/160777]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160777}\right)^3.
\]
The sixteenth fixed prism uses \([1/321544,1/160772]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160772}\right)^3.
\]
The seventeenth fixed prism uses \([1/321542,1/160771]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160771}\right)^3.
\]
The eighteenth fixed prism uses \([1/321540,1/160770]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160770}\right)^3.
\]
The nineteenth fixed prism uses \([1/321538,1/160769]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160769}\right)^3.
\]
The twentieth fixed prism uses \([1/321090,1/160545]\), starts at that closed
endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{160545}\right)^3.
\]
The twenty-first fixed prism uses \([1/276340,1/138170]\), starts at that
closed endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{138170}\right)^3.
\]
The twenty-second fixed prism uses \([1/261460,1/130730]\), starts at that
closed endpoint, and continues through
\[
1+\frac{251}{20}\left(\frac1{130730}\right)^3.
\]
The twenty-third fixed prism uses \([1/257594,1/128797]\), starts at that
closed endpoint, and reaches the prior certified radius:
\[
1+\frac{251}{20}\left(\frac1{128797}\right)^3.
\]
The twenty-fourth fixed prism uses \([1/257576,1/128788]\), starts at that
closed endpoint, and reaches the next exact seam:
\[
1+\frac{251}{20}\left(\frac1{128788}\right)^3.
\]
The twenty-fifth fixed prism uses \([1/256978,1/128489]\), starts at that
closed endpoint, and reaches the next exact seam:
\[
1+\frac{251}{20}\left(\frac1{128489}\right)^3.
\]
The twenty-sixth fixed prism uses \([1/256798,1/128399]\), starts at that
closed endpoint, and reaches the next exact seam:
\[
1+\frac{251}{20}\left(\frac1{128399}\right)^3.
\]
The twenty-seventh fixed prism uses \([1/256788,1/128394]\), starts at that
closed endpoint, and reaches the sharpened common face radius:
\[
1+\frac{251}{20}\left(\frac1{128394}\right)^3.
\]
The twenty-eighth fixed prism uses \([1/256778,1/128389]\), starts at that
closed endpoint, and reaches the next exact seam:
\[
1+\frac{251}{20}\left(\frac1{128389}\right)^3.
\]
The twenty-ninth fixed prism uses \([1/256770,1/128385]\), starts at that
closed endpoint, and reaches the rho-sharpened common face radius:
\[
1+\frac{251}{20}\left(\frac1{128385}\right)^3.
\]
The thirtieth fixed prism uses \([1/256768,1/128384]\), starts at that
closed endpoint, and reaches the next exact seam:
\[
1+\frac{251}{20}\left(\frac1{128384}\right)^3.
\]
The thirty-first fixed prism uses \([1/254560,1/127280]\), starts at that
closed endpoint, and reaches the previous common face radius:
\[
1+\frac{251}{20}\left(\frac1{127280}\right)^3.
\]
The thirty-second fixed prism uses \([1/252682,1/126341]\), starts at that
closed endpoint, and reaches the widened common face radius:
\[
1+\frac{251}{20}\left(\frac1{126341}\right)^3.
\]
The thirty-third fixed prism uses \([1/252668,1/126334]\), starts at that
closed endpoint, and reaches the sharpened common face radius:
\[
1+\frac{251}{20}\left(\frac1{126334}\right)^3.
\]
`prescribedDensity_lambda_explicit_combined` composes all thirty-four cells,
including all thirty-three shared seams and the new closed upper endpoint. The
private fixed-prism construction remains radius-parametric for subsequent
certified scale intervals.

The scale-local replacement campaign has a retained two-band numerical pilot
with partial kernel replay in
[`proof/scale_local_atlas/REPORT.md`](proof/scale_local_atlas/REPORT.md).
It covers the closed density-increment bands
\([\delta_0,8\delta_0]\) and \([1/1000,1/500]\), with
\(\delta_0=(251/20)(1/126334)^3\), using 64 rational subslabs each.
Independent replay of the saved inputs passed all eight uniform face signs,
source guards, height-order inequalities, and normalized negative-gap
enclosures with 160-bit outward dyadic arithmetic. Lean now kernel-replays the
shared interval primitives, the exact 160-bit dyadic `pi` interval, and 17 of
the seam-adjoining cell's 18 guards, through `A_pos`; `gap_den`, generated
identities, face/gap mean-value enclosures, and the Poincare-Miranda step remain
pending. The public kernel-checked coverage endpoint above is unchanged.
`NearOneLocalSource.stationaryEqualAreaPair_strictImprovement` is independently
kernel-checked and audited: explicit local source equations and inequalities
give the existing scalar consumer's conclusion without cusp-box assumptions.
It is a transport theorem, not a completed slab. Reproduce the targeted build
with `lake build NearOneLocalAtlas` from `proof/`.

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
hypothesis. All 1,024 concrete compact cells promote their stationary strict
gaps to every modeled type-(iv) candidate and compose across every exact seam
on \([33/32,9/7]\), including \(h_4=1\).
The branch-complete source route no longer depends on the compact-cell range or
on abstract source/model compatibility. `CandidateFourArc` projection
exhaustion gives the literal complete-frontier lower bound for every geometric
candidate with \(0<h\le1\). `CMVTypeThreeSourceExclusion` splits on
\(\lambda\cos\alpha-h\): the zero branch uses the unchanged recovered
type-(iii) theorem, and both nonzero branches use the recovered constrained-
chord competitor. Source minimality supplies the original candidate's
finiteness only inside the contradiction.

The resulting contact-law-free non-minimality covers arbitrary literal
candidates, the closed \(h=1\) endpoint, exact horizontal representatives,
almost-everywhere horizontal representatives, and raw coordinates with
\(R\ge1\) under only their closed geometric domain. The stronger canonical and
zero-defect type-(iii) witness declarations remain available. The older
near-one, middle-cell, compact-cell, and \(51/50\) cutoff certificates remain
independent reproducible evidence, but they are no longer needed for this
classified-source exclusion.

Universal source classification remains open. The current Lean development
does not derive bilateral symmetry, the minimizer's common-circle geometry,
configuration enumeration, or representative identification from every
source-admissible regular type-(iv) minimizer, and it does not eliminate every
distinct Figure-5 configuration in CMV Lemma 3.8. The project therefore does
not identify arbitrary source minimizers with the checked carrier interface or
claim CMV Conjecture 3.12.

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

Compile the current all-density direct source-exclusion path and audit every
permanent declaration ledger in that path:

```bash
lake build CMVContactLawFreeSourceExclusionSupport
lake env lean CMVFourArcChordVariationAssumptions.lean
lake env lean CMVFourArcRecoveryAssumptions.lean
lake env lean CMVFourArcSourceCompetitorAssumptions.lean
lake env lean CMVTypeThreeSourceExclusionAssumptions.lean
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
