---
title: "A Lean-Verified 51/50 Cutoff for Four-Arc Minimizers"
subtitle: "The Cañete–Miranda–Vittone strip-density problem"
author: "Rosa Pavlak"
date: "4 September 2026"
abstract: |
  For the planar strip density equal to $1$ on $\{|y|\le 1\}$ and to
  $\lambda>1$ outside, Cañete, Miranda Jr., and Vittone reduced the unresolved
  part of their classification to the possible optimality of a symmetric
  four-arc candidate. We give a machine-checked exclusion of every such
  candidate for $\lambda\ge 51/50$. The formal theorem is universal in the
  candidate curvature, includes the limiting curvature $h=1$, and quantifies
  minimality against genuine measurable coordinate regions with weighted area
  and complete-frontier weighted perimeter. On the exact interval
  $[51/50,9/7]$, Lean constructs an equal-area regular type-(iii) competitor
  with strictly smaller perimeter. Above $9/7$, the proof splices to the CMV
  two-cap-to-one-cap replacement, realized as an admissible three-arc carrier
  with the same area and smaller perimeter. The local transcendental work is
  discharged by 1,139 exact-rational cells whose seams and union are checked by
  Lean. The final theorem and its source-coordinate corollaries compile in
  Lean 4 using only the standard logical axioms reported by `#print axioms`.
keywords:
  - weighted isoperimetry
  - strip density
  - formal verification
  - Lean 4
  - interval certificates
bibliography: ../references/references.bib
link-citations: true
lang: en-US
---

::: {.result-card}
**Main result.** Let $\lambda\ge 51/50$. Every modeled CMV type-(iv)
four-arc candidate satisfying the density jump and Snell incidence law has an
admissible equal-area competitor of smaller weighted perimeter. Consequently,
it is not a weighted-perimeter minimizer. For a canonical regular source
profile, the only remaining possible density range is

$$
1<\lambda<\frac{51}{50}.
$$

**Lean declaration:**
[`CMVModeledCutoff.candidate_not_isWeightedPerimeterMinimizer_from_51_50`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean#L21-L38).
:::

# 1. Statement, scope, and novelty

Consider the lower-semicontinuous planar density

$$
f_\lambda(x,y)=
\begin{cases}
1,& |y|\le 1,\\
\lambda,& |y|>1,
\end{cases}
\qquad \lambda>1.
$$

For a sufficiently regular carrier $E\subset\mathbb R^2$, the associated
weighted area and perimeter are

$$
A_\lambda(E)=\int_E f_\lambda\,d\mathcal L^2,
\qquad
P_\lambda(E)=\int_{\partial E} f_\lambda\,d\mathcal H^1.
$$

The source problem is formulated for finite-perimeter sets and reduced
boundaries. Cañete, Miranda Jr., and Vittone (CMV) prove existence,
connectedness, symmetrization, and a geometric classification of candidates
[@CaneteMirandaVittone2010, Proposition 3.6, Lemma 3.8, Proposition 3.9]. Their
Conjecture 3.12 predicts that type-(iv) candidates are never minimizing. Their
Theorem 3.16 proves this for $\lambda\ge 4/\pi$ by replacing two exterior caps
with one; Remark 3.17 explicitly says that $4/\pi$ is not optimal.

This paper proves the following formal cutoff.

::: {.theorem}
**Theorem 1 (Lean-verified modeled cutoff).** If
$\lambda\ge 51/50$, `candidate : FourArcCandidate λ`, and
`candidate.SatisfiesCMVTypeIVHypotheses`, then

$$
\neg\,\texttt{candidate.IsWeightedPerimeterMinimizer}.
$$
:::

The exact Lean statement is:

```lean
theorem candidate_not_isWeightedPerimeterMinimizer_from_51_50
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer
```

It appears verbatim in
[`CMVModeledCutoff.lean`, lines 21–38](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean#L21-L38).
The proof is not a numerical sample and not a theorem about one selected
curvature: the conclusion holds for every candidate in the formal family.

A logically equivalent corollary is:

```lean
theorem type_four_minimizer_implies_lambda_lt_51_50 ... :
    lam < (51 / 50 : ℝ)
```

and, after using the recorded density jump $1<\lambda$:

```lean
theorem type_four_minimizer_open_range_51_50 ... :
    1 < lam ∧ lam < (51 / 50 : ℝ)
```

Both are in
[`CMVModeledCutoff.lean`, lines 40–61](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean#L40-L61).

## 1.1 What “type-(iii) is better” means here

The comparison has two rigorous branches.

1. **Exact source-family type-(iii) comparison.** For every
   $\lambda\in[51/50,9/7]$ and every admissible type-(iv) curvature, Lean
   produces a regular type-(iii) assembly with exactly equal weighted area and
   strictly smaller weighted perimeter.
2. **Three-arc cap replacement.** For $\lambda>9/7$, Lean uses the CMV
   two-cap-to-one-cap construction. Its carrier has the type-(iii) topology:
   two strip-side circular arcs, one exterior circular arc, and the exposed
   density-one interface segment. It is a genuine equal-area admissible
   competitor and has smaller perimeter. It is not asserted to satisfy the
   stationary equal-curvature equation of the canonical type-(iii) candidate
   family.

This distinction matters. The full formal claim is the exclusion of type (iv)
for every $\lambda\ge51/50$. The stronger literal statement that a *stationary,
equal-curvature* type-(iii) candidate beats every type-(iv) candidate is
machine-checked on $[51/50,9/7]$; above that interval the checked competitor is
the cap replacement. Calling the latter stationary would add a premise not
present in the Lean theorem.

# 2. From the CMV paper to formal parameters

CMV identify four candidate families. Their type (iii) has one exterior cap and
two arcs through the strip; type (iv) has reflected exterior caps above and
below the strip together with two strip-side arcs. Equations (26) and (27) give
area and perimeter in terms of generalized curvature $h$ and principal angles
[@CaneteMirandaVittone2010, pp. 18–19]. CMV record $0<h\le1$ for type (iv), and
their numerical plots suggest that type (iii) always beats type (iv)
[@CaneteMirandaVittone2010, Figure 6 and the paragraph following equation (27)].

The formalization begins from coordinate geometry rather than postulating the
scalar formulas.

## 2.1 Four-arc candidates

[`FourArcCandidate.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FourArcCandidate.lean)
defines the geometric data

$$
0<h\le1,
\qquad
0<\alpha<\frac\pi2,
$$

then derives the common radius, strip core, two reflected caps, carrier,
weighted area, and weighted perimeter. The source-specific predicate is only

```lean
structure SatisfiesCMVTypeIVHypotheses : Prop where
  density_jump : 1 < lam
  snell_incidence : lam * cos candidate.alpha = candidate.h
```

See
[`FourArcCandidate.lean`, lines 75–93](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FourArcCandidate.lean#L75-L93).
In particular, this predicate does **not** assume an area formula, a perimeter
formula, a competitor, an inequality, or nonminimality. The principal-branch
identity
$\alpha=\arccos(h/\lambda)$ is proved from the incidence law and angle bounds
([`alpha_eq_arccos`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FourArcCandidate.lean#L198-L213)).
The CMV type-(iv) formulas are then derived from the constructed boundary pieces
([`candidate_perimeter_formula`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FourArcCandidate.lean#L276-L292)
and
[`candidate_area_formula`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FourArcCandidate.lean#L294-L314)).

Minimality is not restricted to another scalar record. It quantifies over every
formal `AdmissibleCompetitor` of the same weighted area:

```lean
def IsWeightedPerimeterMinimizer : Prop :=
  ∀ competitor : AdmissibleCompetitor lam,
    competitor.WeightedArea = candidate.WeightedArea →
      candidate.WeightedPerimeter ≤ competitor.WeightedPerimeter
```

Thus one concrete equal-area region with smaller perimeter refutes minimality.

## 2.2 Genuine type-(iii) carriers

[`TypeThreeAssembly.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/TypeThreeAssembly.lean)
implements the regular CMV type-(iii) family on $0<h_3<1$. It defines the
closed coordinate carrier, its major/semicircular/minor exterior-cap branches,
the two strip-side arc traces, and the possibly degenerate lower interface
segment. The common radius is $R=1/h_3$; branch selection is explicit rather
than hidden in a numerical inverse function. The module proves measurability,
finite-perimeter realization, weighted-area identities, and complete-frontier
weighted-perimeter identities.

The analytic-to-geometric bridge is
[`FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVSuffixModel.lean#L197-L221):
if the scalar type-(iii) area equals the type-(iv) area and its perimeter is
strictly smaller, Lean constructs the `TypeThreeAssembly`, obtains its
finite-perimeter realization, and contradicts candidate minimality.

## 2.3 Complete-frontier perimeter

The earlier scalar argument could not by itself certify that a formula was the
perimeter of the displayed region. The current development closes that gap in
[`FrontierPerimeter.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FrontierPerimeter.lean).
It proves exact frontier decompositions, zero $\mathcal H^1$ mass of finite
join sets, pairwise almost-disjointness of arc measures, and equality between
explicit boundary sums and the weighted integral over the complete topological
frontier. The same module treats four-arc, type-(iii), and replacement
assemblies.

These theorems use Hausdorff measure on the Euclidean realization, not a
Manhattan proxy and not a sum of disconnected lengths. Endpoints are included
set-theoretically and shown to have zero one-dimensional Hausdorff measure.

# 3. The scalar comparison on $[51/50,9/7]$

The coordinate geometry reduces the stationary comparison to exact scalar
identities. The notation below is the one used by the retained certificate:

$$
h_4=\cos x,
\qquad
q_3=\cos w,
\qquad
h_3=\frac{1+\cos w}{2}.
$$

For type (iv), set

$$
B_4=\lambda y+\frac\pi2-x,
\qquad
d_4=\sin y-\sin x,
\qquad
N_4=B_4+\cos x\,d_4.
$$

For type (iii), set

$$
B_3=\lambda v+\pi-w,
\qquad
d_3=\sin v-\sin w,
\qquad
N_3=B_3+(\cos w+2)d_3.
$$

Four equations determine the stationary type-(iv) fold and its selected
equal-area type-(iii) comparison:

$$
\begin{aligned}
C_4&=\cos x-\lambda\cos y,\\
F&=\cos x(\sin y-\sin x)
   -\sin x\sin y\left(\lambda y+\frac\pi2-x\right),\\
C_3&=\cos w-\lambda\cos v,\\
E&=2\cos^2x\,N_3-(1+\cos w)^2N_4.
\end{aligned}
$$

Here $C_4=F=0$ is the incidence/stationarity system for type (iv), while
$C_3=E=0$ is the incidence/equal-area system for type (iii). The sign-transfer
quantity is

$$
G=\cos x(B_3+d_3)-(1+\cos w)B_4.
$$

Under the proved domain and denominator guards, $G$ has the sign of
$P_3-P_4$. Each retained cell proves $G<0$.

The formulas and their derivatives are formalized in
[`LeanSuffixAnalytic.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/LeanSuffixAnalytic.lean).
[`SameCurvatureArea.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/SameCurvatureArea.lean)
and
[`EqualAreaEnvelope.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/EqualAreaEnvelope.lean)
turn one certified stationary comparison into an all-curvature statement.
The decisive theorem
[`allCurvature_typeThreeImprovement`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/EqualAreaEnvelope.lean)
returns, for every $0<h_4\le1$, a regular $h_3$ with equal area and smaller
perimeter.

At the candidate layer,
[`CompactCellAssembly.Conditions.candidate_not_isWeightedPerimeterMinimizer`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CompactCellAssembly.lean#L309-L335)
packages the certified stationary pair, proves the descending type-(iii) branch
condition, invokes the all-curvature envelope, and realizes the resulting
competitor geometrically. This is why the final theorem covers arbitrary
candidate curvature and the endpoint $h_4=1$ rather than only a stationary
sample.

# 4. Exact-rational coverage

The compact numerical work is proof-producing. Floating-point root solvers are
used to propose boxes, but Lean accepts only rational endpoints and exact
inequalities. Transcendental values are enclosed using rational Taylor bounds;
interval ordering, face signs, derivative signs, denominator positivity, and
all seams are replayed by the kernel.

| Component | Closed density interval | Cells | Formal role |
|---|---:|---:|---|
| Left prototype | $[51/50,102001/100000]$ | 1 | Starts the new cutoff and proves the first seam. |
| Middle-face tiling | $[102001/100000,25781/25000]$ | 113 | Covers the narrow source-to-compact transition. |
| Right prototype | $[25781/25000,33/32]$ | 1 | Reaches the compact certificate exactly. |
| Compact certificate | $[33/32,9/7]$ | 1,024 | Covers the remaining scalar suffix. |
| **Total** | **$[51/50,9/7]$** | **1,139** | **No rational seam gap.** |

The first three rows compose in
[`MiddleFaceCells.candidate_not_isWeightedPerimeterMinimizer_from_51_50`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/MiddleFaceCells.lean#L72-L100).
The compact cells compose in
[`CompactCells1003To1023.boxes0To1023_candidate_not_isWeightedPerimeterMinimizer`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CompactCells1003To1023.lean#L14117-L14129).
The final cell ends at the exact rational $9/7$, not a rounded decimal.

## 4.1 What a cell proves

A compact cell contains a rational interval in $\lambda$, a slab for the
stationary type-(iv) root, and a slab for the equal-area type-(iii) root. Its
`Conditions` proof establishes:

- strict physical domains for both curvatures;
- existence and uniqueness of the type-(iv) fold root;
- existence and selected-branch uniqueness of the type-(iii) equal-area root;
- strict negativity of the type-(iii) fold on the selected slab;
- strict negativity of $P_3-P_4$;
- exact compatibility of adjacent density intervals.

For a representative generated leaf, see
[`CompactCells1003To1023.Box1003`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CompactCells1003To1023.lean#L18-L153).
The leaf contains only rational literals and proofs built from the shared
checker. The reusable checker lives in
[`CompactCellCertificate.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CompactCellCertificate.lean),
and the candidate-facing composition is in
[`CompactCellAssembly.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CompactCellAssembly.lean).

The middle-face path uses the same principle with slanted four-dimensional
bricks. Its reusable contract is
[`MiddleFaceAssembly.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/MiddleFaceAssembly.lean),
and its generated leaves are grouped by
[`MiddleFaceCells.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/MiddleFaceCells.lean).

# 5. The high-density cap replacement

CMV's proof at $\lambda\ge4/\pi$ replaces the two equal exterior caps of a
type-(iv) candidate by one cap of twice the Euclidean area and exposes the
opposite interface chord [@CaneteMirandaVittone2010, Theorem 3.16]. If $L$ is
the old chord length, $A$ one old cap area, and `arc` is the length of a
circular arc with unit chord and prescribed enclosed area, strict improvement
is equivalent to

$$
\lambda L\,\operatorname{arc}(2A/L^2)+L
<2\lambda L\,\operatorname{arc}(A/L^2).
$$

The formal development improves the numerical density threshold for this
argument to the exact decimal rational

$$
1.2581840884=\frac{3145460221}{2500000000}.
$$

[`CapReplacement.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CapReplacement.lean)
constructs the replacement carrier and proves that its upper cap has exactly
twice the old Euclidean cap area. It covers minor, semicircular, and major
branches. The exposed lower segment is proved to lie on the density-one
interface and on the actual frontier
([`exposed_lower_chord_on_frontier`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CapReplacement.lean#L94-L118)).

[`GeometricBridge.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/GeometricBridge.lean)
proves exact area preservation and transfers the certified arc inequality to
strict weighted-perimeter improvement. Finally,
[`CandidateExclusion.cmv_type_four_not_minimizing`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CandidateExclusion.lean#L16-L34)
instantiates minimality with that concrete region.

Since

$$
1.2581840884 < \frac97,
$$

the high-density result covers every $\lambda>9/7$. The final composition is a
three-way exact case split:

```lean
by_cases hface : lam ≤ (33 / 32 : ℝ)
-- 1, 113, and 1 face/prototype cells
...
by_cases hcompact : lam ≤ (9 / 7 : ℝ)
-- 1,024 compact cells
...
-- cap replacement, using 1.2581840884 < 9/7
```

This proof is visible at
[`CMVModeledCutoff.lean`, lines 29–38](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean#L29-L38).
There is no uncovered seam at $33/32$ or $9/7$.

# 6. Source-coordinate transfer

The modeled theorem is already a theorem about actual coordinate carriers and
weighted integrals, but connecting an arbitrary source presentation to the
canonical coordinates is a separate logical step.

[`CMVSourceBridge.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVSourceBridge.lean)
defines `CanonicalTypeIVProfile`, its independent source-coordinate carrier,
and the conversion `toCandidate`. It proves that the converted candidate
satisfies the CMV incidence law and that every regular modeled candidate comes
from such a profile. Horizontal translations preserve both weighted area and
complete-frontier weighted perimeter
([`HorizontallyCongruent` and invariance theorems](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVSourceBridge.lean#L131-L166)).

For a generic external source semantics, the exact transfer theorem names its
two assumptions rather than hiding them:

```lean
theorem sourceCarrier_not_isMinimizer_from_51_50
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (source : SourcePerimeterSemantics lam)
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (normalization : source.NormalizationWitness sourceCarrier profile)
    (compatibility : source.CompatibleWithModel profile) :
    ¬ source.IsMinimizer sourceCarrier
```

See
[`CMVModeledCutoff.lean`, lines 63–83](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean#L63-L83).

For the canonical complete-frontier source semantics implemented in the
repository, those compatibility obligations are discharged internally. The
result is:

```lean
theorem canonicalCarrier_minimizer_open_range_51_50
    (profile : CanonicalTypeIVProfile lam)
    (hmin : (canonicalFrontierSemantics lam).IsMinimizer profile.carrier) :
    1 < lam ∧ lam < (51 / 50 : ℝ)
```

See
[`CMVModeledCutoff.lean`, lines 103–118](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean#L103-L118).

::: {.scope-note}
**Scope boundary.** CMV's geometric classification and regularity arguments are
cited, not re-formalized. The Lean theorem excludes every regular canonical
source type-(iv) profile and every external source carrier satisfying the
explicit normalization and reduced-boundary compatibility contract. It does
not claim a new formalization of CMV's existence or symmetrization theorems.
The global conjecture remains open only on $1<\lambda<51/50$.
:::

# 7. Trust and audit

The proof uses Lean 4 [@deMouraUllrich2021] and mathlib
[@mathlib2020]. The repository pins the compiler in
[`lean-toolchain`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/lean-toolchain)
and pins dependencies in
[`lake-manifest.json`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/lake-manifest.json).

## 7.1 Trusted and untrusted components

| Component | Role | Trusted for the theorem? |
|---|---|---:|
| Lean kernel | Checks elaborated proof terms | Yes |
| mathlib definitions and theorems | Analysis, topology, measure theory, algebra | Yes, as imported theory |
| Rational certificate generators | Propose boxes and bounds | No |
| Floating-point root finding | Finds candidate witnesses | No |
| Generated `.lean` files | Supply rational propositions and proof terms | Only after kernel checking |
| Python mutation/replay scripts | Independent diagnostics | No |
| PDF/HTML rendering | Presentation only | No |

The essential point is proof-producing computation: a bad floating-point guess
can make generation fail, but it cannot make Lean accept a false rational
inequality. Coverage is also a theorem-level composition, so omission of a
cell creates a missing interval rather than silently passing a loop.

The focused publication audit lists the exported cutoff declarations in
[`CMVCutoffAssumptions.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVCutoffAssumptions.lean).
`#print axioms` reports only the standard logical axioms used throughout
mathlib:

```text
propext
Classical.choice
Quot.sound
```

No theorem in the cutoff chain depends on a project-local `axiom`, `sorry`,
`admit`, or `native_decide` shortcut.

# 8. Reproduction

A clean checkout contains all Lean sources, generated exact certificates,
build configuration, bibliography, manuscript source, stylesheet, and the
paper build script.

## 8.1 Check the theorem

From the repository root:

```bash
cd projects/cmv-strip-density/proof
lake build CMVModeledCutoff
lake env lean CMVCutoffAssumptions.lean
```

The first command compiles the theorem and its complete dependency closure. The
second prints the axiom dependencies of the public declarations. To build the
entire formal development, including every generated cell:

```bash
cd projects/cmv-strip-density/proof
lake build
```

The relevant roots and pinned dependency are declared in
[`lakefile.toml`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/lakefile.toml).

## 8.2 Rebuild the paper

The paper is generated from this Markdown source and the adjacent stylesheet:

```bash
cd projects/cmv-strip-density/reports
./build-lean-verified-cmv-cutoff.sh
```

The script invokes Pandoc with citation processing and then Chromium's print
engine. Its outputs are
`lean-verified-cmv-cutoff.html` and `lean-verified-cmv-cutoff.pdf`.
The manuscript's direct source links target the same repository paths used by
the Lean commands above.

# 9. Conclusion

The 2010 CMV analysis isolated type (iv) as the remaining obstruction and
proved its exclusion for $\lambda\ge4/\pi$. The present formal development
lowers the verified cutoff to

$$
\boxed{\lambda\ge\frac{51}{50}}.
$$

The result is stronger than the earlier scalar certificate in three ways.
First, it is a Lean theorem about every modeled type-(iv) candidate, not a
standalone table of numerical signs. Second, the equal-area type-(iii)
comparison on $[51/50,9/7]$ is realized as a genuine finite-perimeter coordinate
competitor whose weighted area and complete-frontier weighted perimeter agree
with the scalar formulas. Third, the theorem transfers to independent source
coordinates through explicit normalization and boundary-semantics contracts,
with the canonical source carrier requiring no external bridge assumption.

The mathematical work left by this theorem is sharply delimited: decide the
punctured near-one interval $1<\lambda<51/50$ and, separately, formalize as much
of the global CMV existence/classification argument as desired. Neither task is
silently included in the cutoff proved here.

# References
