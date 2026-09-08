---
title: "A Lean-Verified 51/50 Cutoff and the Remaining-Range Frontier"
subtitle: "From exact rational cells to an all-density classified-carrier exclusion"
author: "Rosa Pavlak"
date: "7 September 2026"
abstract: |
  For the planar strip density equal to $1$ on $\{|y|\le 1\}$ and to
  $\lambda>1$ outside, Cañete, Miranda Jr., and Vittone reduced the unresolved
  part of their classification to the possible optimality of a symmetric
  four-arc candidate. This paper gives a reproducible Lean 4 proof of the
  exact cutoff $\lambda\ge 51/50$. On $[51/50,9/7]$, 1,139 exact-rational
  cells are composed without a seam gap; above $9/7$, the proof uses a
  formally realized cap replacement. We then report the stronger development
  obtained on the old remaining range $1<\lambda<51/50$: every modeled
  type-(iv) candidate, every literal source-incidence four-arc carrier, and
  every exact or almost-everywhere horizontal representative of the checked
  closed-Snell coordinate family is now excluded for every $\lambda>1$.
  A separate near-one construction kernel-checks an explicit density prefix,
  while an independently replayed interval atlas supplies nonformal
  exploration farther into the interval. The scalar and classified-carrier
  problems are therefore closed throughout the admissible density range. The
  full CMV conjecture is not claimed: the remaining obligation is universal
  geometric and GMT classification of arbitrary source minimizers into the
  checked carrier interfaces, including the residual configurations in CMV
  Lemma 3.8. Every theorem level, computational certificate, and unresolved
  interface is distinguished explicitly.
keywords:
  - weighted isoperimetry
  - strip density
  - formal verification
  - Lean 4
  - interval certificates
  - geometric measure theory
bibliography: ../references/references.bib
link-citations: true
lang: en-US
---

::: {.result-card}
**Certified conclusions.**

1. If $\lambda\ge 51/50$, every modeled CMV type-(iv) candidate satisfying the
   density jump and Snell incidence law has a genuine equal-area competitor of
   smaller weighted perimeter.
2. In fact, the modeled exclusion now holds for every $\lambda>1$.
3. The all-density comparison has been lifted to literal coordinate carriers
   for the relaxed source perimeter, including $h=1$, horizontal translation,
   almost-everywhere replacement, and independent closed-Snell coordinates
   with source radius $R\ge1$.
4. The unconditional CMV conjecture remains open because universal source
   classification into those carriers has not been formalized.

**Exact cutoff declaration:**
[`CMVModeledCutoff.candidate_not_isWeightedPerimeterMinimizer_from_51_50`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean).

**Stronger all-density declaration:**
[`CMVModeledCutoff.candidate_not_isWeightedPerimeterMinimizer`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVModeledCutoff.lean).
:::

# 1. Statement and logical scope

Consider the lower-semicontinuous density

$$
f_\lambda(x,y)=
\begin{cases}
1,& |y|\le1,\\
\lambda,& |y|>1,
\end{cases}
\qquad \lambda>1.
$$

For a sufficiently regular set $E\subset\mathbb R^2$, write

$$
A_\lambda(E)=\int_E f_\lambda\,d\mathcal L^2,
\qquad
P_\lambda(E)=\int_{\partial E}f_\lambda\,d\mathcal H^1.
$$

The source variational problem is posed for finite-perimeter sets and reduced
boundaries. CMV prove existence, symmetrization, and a geometric classification
of candidate shapes [@CaneteMirandaVittone2010, Proposition 3.6, Lemma 3.8,
Proposition 3.9]. Their Conjecture 3.12 says that type (iv), the symmetric
four-arc family, is never minimizing. Their Theorem 3.16 establishes this for
$\lambda\ge4/\pi$ by a cap replacement and Remark 3.17 notes that this threshold
is not optimal.

The formal development separates three statements that must not be conflated.

| Level | Quantified object | Current status |
|---|---|---|
| Modeled candidate | `FourArcCandidate λ` satisfying the exact CMV incidence hypotheses | **Proved for every $\lambda>1$** |
| Classified source carrier | Literal, canonical, translated, a.e.-translated, or raw closed-Snell coordinate carrier | **Proved for every $\lambda>1$** |
| Arbitrary source minimizer | Any source-admissible minimizer covered by the full CMV/GMT classification | **Open: universal classification is not formalized** |

Thus “all-density” below always means the first or second row unless the source
classification hypothesis is stated. No result in this paper silently assumes
that every arbitrary minimizer is already a `FourArcCandidate`.

## 1.1 The exact $51/50$ theorem

The original cutoff remains as an independent theorem with an independent
certificate path.

::: {.theorem}
**Theorem 1 (exact Lean-verified cutoff).** Let $\lambda\ge51/50$ and let
`candidate : FourArcCandidate λ` satisfy
`candidate.SatisfiesCMVTypeIVHypotheses`. Then

$$
\neg\,\texttt{candidate.IsWeightedPerimeterMinimizer}.
$$
:::

The exported Lean statement is:

```lean
theorem candidate_not_isWeightedPerimeterMinimizer_from_51_50
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer
```

The conclusion is universal in candidate curvature. It includes the limiting
curvature $h=1$ and refutes minimality by constructing an admissible competitor
at exactly equal weighted area. The proof is neither a plot nor a finite sample
of candidates.

The logically equivalent retained corollaries are:

```lean
theorem type_four_minimizer_implies_lambda_lt_51_50 ... :
    lam < (51 / 50 : ℝ)

theorem type_four_minimizer_open_range_51_50 ... :
    1 < lam ∧ lam < (51 / 50 : ℝ)
```

These corollaries describe the frontier established by the *cutoff proof
alone*. Section 4 explains why the stronger subsequent theorem closes that
modeled near-one interval.

## 1.2 The stronger theorem

::: {.theorem}
**Theorem 2 (all-density modeled exclusion).** Let $\lambda>1$ and let
`candidate : FourArcCandidate λ` satisfy the CMV type-(iv) hypotheses. Then the
candidate is not a weighted-perimeter minimizer.
:::

Its exact Lean declaration is:

```lean
theorem candidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ}
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer
```

The hypothesis `hcandidate.density_jump` supplies $1<\lambda$. Source
classification and reduced-boundary compatibility are deliberately absent from
this theorem because its quantified object is already the formal coordinate
candidate.

# 2. The geometric meaning of the model

[`FourArcCandidate.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FourArcCandidate.lean)
defines a common curvature parameter $0<h\le1$, a principal exterior angle,
two strip-side circular arcs, two exterior caps, interface segments, the
coordinate carrier, weighted area, and complete-frontier weighted perimeter.
The source-facing hypothesis is small:

```lean
structure SatisfiesCMVTypeIVHypotheses : Prop where
  density_jump : 1 < lam
  snell_incidence : lam * cos candidate.alpha = candidate.h
```

Area and perimeter formulas are derived from the coordinate pieces rather than
inserted into this predicate. Minimality quantifies over every formal
`AdmissibleCompetitor` of equal weighted area:

```lean
def IsWeightedPerimeterMinimizer : Prop :=
  ∀ competitor : AdmissibleCompetitor lam,
    competitor.WeightedArea = candidate.WeightedArea →
      candidate.WeightedPerimeter ≤ competitor.WeightedPerimeter
```

Consequently, one constructed equal-area region with smaller perimeter is a
complete refutation of modeled minimality.

The competitor is a genuine [`TypeThreeAssembly`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/TypeThreeAssembly.lean),
not merely a scalar tuple. It includes the major, semicircular, and minor
exterior-cap branches, the two strip-side arcs, and the possibly degenerate
interface segment. Its weighted area and perimeter are connected to literal
coordinate geometry. [`FrontierPerimeter.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/FrontierPerimeter.lean)
proves that the displayed sums equal weighted Hausdorff integrals over the
complete topological frontier; finite join sets have zero $\mathcal H^1$ mass.

# 3. Independent hard proof of the $51/50$ cutoff

The exact cutoff uses a proof-producing interval decomposition on
$[51/50,9/7]$ and a geometric cap replacement above it. Keeping this route is
valuable even after Theorem 2: it is an independently structured certificate
with explicit rational coverage and a different high-density splice.

## 3.1 Scalar reduction

Use

$$
h_4=\cos x,\qquad q_3=\cos w,\qquad h_3=\frac{1+\cos w}{2}.
$$

For type (iv), define

$$
B_4=\lambda y+\frac\pi2-x,
\qquad d_4=\sin y-\sin x,
\qquad N_4=B_4+\cos x\,d_4.
$$

For type (iii), define

$$
B_3=\lambda v+\pi-w,
\qquad d_3=\sin v-\sin w,
\qquad N_3=B_3+(\cos w+2)d_3.
$$

The four equations checked in the retained cells are

$$
\begin{aligned}
C_4&=\cos x-\lambda\cos y,\\
F&=\cos x(\sin y-\sin x)
  -\sin x\sin y\left(\lambda y+\frac\pi2-x\right),\\
C_3&=\cos w-\lambda\cos v,\\
E&=2\cos^2x\,N_3-(1+\cos w)^2N_4.
\end{aligned}
$$

Here $C_4=F=0$ is the type-(iv) incidence/stationarity system and
$C_3=E=0$ is the type-(iii) incidence/equal-area system. The sign-transfer
quantity is

$$
G=\cos x(B_3+d_3)-(1+\cos w)B_4.
$$

Under the proved domain and denominator guards, $G<0$ implies
$P_3<P_4$. The analytic formulas and their derivatives are formalized in
[`LeanSuffixAnalytic.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/LeanSuffixAnalytic.lean).
The envelope argument in
[`SameCurvatureArea.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/SameCurvatureArea.lean)
and
[`EqualAreaEnvelope.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/EqualAreaEnvelope.lean)
promotes one certified stationary pair to every admissible type-(iv) curvature.

## 3.2 Exact coverage with no seam gap

Floating-point computations proposed the cells, but Lean accepts only exact
rational endpoints and proof terms. Rational Taylor bounds enclose the
transcendental functions. The kernel checks interval inclusion, face signs,
derivative signs, denominator positivity, branch selection, and every seam.

| Component | Closed density interval | Cells | Role |
|---|---:|---:|---|
| Left prototype | $[51/50,102001/100000]$ | 1 | Establishes the cutoff endpoint and first seam |
| Middle-face tiling | $[102001/100000,25781/25000]$ | 113 | Covers the source-to-compact transition |
| Right prototype | $[25781/25000,33/32]$ | 1 | Reaches the compact certificate |
| Compact certificate | $[33/32,9/7]$ | 1,024 | Covers the remaining scalar suffix |
| **Total** | **$[51/50,9/7]$** | **1,139** | **Exact contiguous union** |

Each cell proves physical domains, existence and selected uniqueness of the
stationary type-(iv) root, existence and selected-branch uniqueness of the
equal-area type-(iii) root, negativity of the type-(iii) fold, negativity of
the perimeter gap, and compatibility with adjacent density intervals.

The first 115 cells compose in
[`MiddleFaceCells.candidate_not_isWeightedPerimeterMinimizer_from_51_50`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/MiddleFaceCells.lean).
The 1,024 compact cells compose in
[`CompactCells1003To1023.boxes0To1023_candidate_not_isWeightedPerimeterMinimizer`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CompactCells1003To1023.lean).
The terminal endpoint is the exact rational $9/7$, not a rounded decimal.

## 3.3 High-density splice

Above the interval certificate, Lean uses the CMV two-cap-to-one-cap
replacement. [`CapReplacement.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CapReplacement.lean)
constructs the replacement carrier and proves exact area preservation for all
minor, semicircular, and major branches.
[`GeometricBridge.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/GeometricBridge.lean)
transfers the certified arc inequality to strict weighted-perimeter
improvement. The formal threshold for this branch is

$$
1.2581840884=\frac{3145460221}{2500000000}<\frac97.
$$

Therefore every $\lambda>9/7$ lies in the cap-replacement range. The public
cutoff theorem performs an exact three-way split at $33/32$ and $9/7$; neither
seam is omitted.

# 4. How the old remaining range was closed in the model

The interval $1<\lambda<51/50$ was difficult numerically because the stationary
system becomes singular at the cusp $\lambda=1$. The decisive later proof does
not continue shrinking interval cells toward that cusp. It replaces the
quantitative continuation problem with a qualitative existence argument valid
for every $\lambda>1$.

## 4.1 A stationary type-(iv) root at every density

[`TypeFourStationaryRoot.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/TypeFourStationaryRoot.lean)
defines a denominator-free continuous extension of the type-(iv) fold on
$[9/10,1]$. It proves opposite endpoint signs without evaluating a totalized
singular quotient at $h=1$. The intermediate value theorem gives

$$
\forall\lambda>1\;\exists h_4\in(9/10,1),
\qquad F_4(\lambda,h_4)=0.
$$

This is a theorem over real parameters, not a numerical root finder.

## 4.2 The ordered equal-area type-(iii) root

At a stationary $h_4$, the type-(iv) area is bounded above by its finite
endpoint value. The exact endpoint comparison is

$$
A_4(\lambda,1)<A_3\!\left(\lambda,\frac12\right)
\qquad(\lambda>1).
$$

At the same curvature,

$$
A_3(\lambda,h_4)<A_4(\lambda,h_4).
$$

Continuity of $A_3$ on $[1/2,h_4]$ therefore yields
$h_3\in(1/2,h_4)$ with

$$
A_3(\lambda,h_3)=A_4(\lambda,h_4).
$$

The exact Lean witness is exported by
[`LeanSuffixAnalytic.stationaryEqualAreaPair_exists`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/UniversalStationaryPair.lean).
The same-curvature variational identities then prove

$$
F_3(\lambda,h_3)<0,
\qquad P_3(\lambda,h_3)<P_4(\lambda,h_4),
\qquad G_\lambda(h_3,h_4)<0.
$$

The combined declaration is:

```lean
theorem stationaryEqualAreaPair_strictImprovement_exists
    {lam : ℝ} (hlam : 1 < lam) :
    ∃ pair : StationaryEqualAreaPair lam,
      typeThreeFold lam pair.h₃ < 0 ∧
      typeThreePerimeter lam pair.h₃ <
        typeFourPerimeter lam pair.h₄ ∧
      reducedFoldGap lam pair.h₃ pair.h₄ < 0
```

Finally, the all-curvature envelope transports this stationary strict
comparison to an arbitrary modeled candidate curvature, producing Theorem 2.
Thus the old “remaining range” is now empty at the modeled level:

$$
\boxed{\text{No modeled type-(iv) minimizer exists for any }\lambda>1.}
$$

# 5. Direct source realization of the all-density comparison

A scalar inequality is not yet a source variational theorem. The later
formalization establishes both sides of the relaxed-perimeter comparison for
literal coordinate carriers.

## 5.1 The relaxed functional

[`CMVRelaxation.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVRelaxation.lean)
defines an extended-valued lower-semicontinuous relaxation through smooth open
approximants. It proves:

- equivalence between symmetric-difference volume and extended $L^1$ distance
  of characteristic functions;
- exact horizontal-translation invariance of area and relaxed perimeter;
- almost-everywhere invariance, including at value $+\infty$;
- a real-valued source semantics only after finiteness is established; and
- weighted-area integrability as part of source admissibility.

This prevents the real integral's non-integrable fallback from entering an
equal-area argument.

## 5.2 Lower bound for every literal four-arc carrier

The lower bound cannot be obtained by naming a formal frontier sum. It must be
charged to every approximating smooth domain.
[`CMVRigidProjection.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVRigidProjection.lean)
constructs localized projection patches and transports them under Euclidean
isometries. Four pairwise-disjoint patch families cover the upper cap, lower
cap, right side, and left side. One finite-summation theorem charges all four
families to one global smooth cost plus a characteristic-distance error.

[`CMVFourArcExhaustion.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVFourArcExhaustion.lean)
identifies the four target contributions with the actual complete-frontier
weighted perimeter. Letting the patch deficit and characteristic-distance
error vanish gives

$$
P_{\lambda,\mathrm{frontier}}(C_4)
\le \overline P_\lambda(C_4)
$$

for every literal `FourArcCandidate`, including $h=1$.

## 5.3 Upper recovery for the type-(iii) competitor

[`CMVTypeThreeLowerRecovery.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVTypeThreeLowerRecovery.lean),
[`CMVTypeThreeUpperRecovery.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVTypeThreeUpperRecovery.lean), and
[`CMVTypeThreeSharpRecovery.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVTypeThreeSharpRecovery.lean)
construct branch-complete smooth recovery sequences for every actual
`TypeThreeAssembly`. The lower-contact, upper-contact, and radius-two disk
branches are treated separately. The resulting source carrier is admissible and
satisfies

$$
\overline P_\lambda(C_3)\le P_{3,\mathrm{frontier}}.
$$

Combined with equal weighted area and the strict scalar inequality, this gives
an actual source-admissible competitor of smaller extended relaxed perimeter.

The central source theorem is:

```lean
theorem candidateCarrier_not_isMinimizer
    {lam : ℝ} (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer
      candidate.assembly.carrier
```

It is in
[`CMVTypeThreeSourceExclusion.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVTypeThreeSourceExclusion.lean).
No `model_covered`, `CompatibleWithModel`, caller-supplied recovery theorem, or
caller-supplied finiteness assumption occurs in this declaration.

## 5.4 Closed-Snell coordinates and the endpoint

[`CMVSourceClassification.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVSourceClassification.lean)
introduces independent raw data: a source radius $R\ge1$, principal exterior
angle, horizontal placement, density jump, and closed Snell law. Lean identifies
its literal carrier with a `FourArcCandidate`. If $R>1$, it agrees with the
canonical regular profile; if $R=1$, it agrees exactly with the explicit
endpoint carrier.

The source-facing result is:

```lean
theorem rawFourArcCarrier_not_isMinimizer_of_closedSnell
    {lam : ℝ} (raw : RawFourArcCoordinates)
    (hclosed : raw.SatisfiesClosedSnell lam) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer raw.carrier
```

Exact horizontal translations and almost-everywhere horizontal representatives
inherit the same exclusion. The radius-one endpoint is not treated by an
informal limiting argument.

# 6. The explicit near-one certificate program

The qualitative proof in Section 4 supersedes interval continuation for the
modeled theorem. The earlier near-one program remains important independent
evidence: it regularizes the singular endpoint, produces actual roots at
prescribed densities, and records exactly where numerical evidence stops being
a Lean proof.

## 6.1 Regularization at the cusp

With $s$ the near-one scale, the corrected normalized system removes explicit
angle singularities using an integral representation of the second remainder
of $\arctan(x)/x$. At $s=0$, the exact cusp is

$$
(z,a,b)=\left(\pi,\frac{5\pi}{12},-44+\frac{19\pi^2}{24}\right).
$$

The Jacobian in the physical coordinates is

$$
J=
\begin{pmatrix}
2&0&0\\
-40&96&0\\
\frac{8(3\pi^2-412)}3&-\frac{2(7\pi^2-2880)}3&-4\pi
\end{pmatrix},
\qquad \det J=-768\pi<0.
$$

Lean computes the unique tangent forced by $Jv+\partial_sF=0$ and then applies a
determinant-one shear $S$ satisfying

$$
JS=\operatorname{diag}(2,96,-4\pi).
$$

After reversing the third residual, the transformed coordinate Jacobian is
positive diagonal. The complete oriented map is divided by $s^2$ away from the
cusp and extended continuously to $s=0$ by exact two-jet identities.

## 6.2 Poincaré--Miranda and prescribed density

[`BoxPoincareMiranda.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/BoxPoincareMiranda.lean)
derives the finite-dimensional opposite-face zero theorem from the pinned
Brouwer fixed-point dependency. A three-dimensional endpoint box provides a
simultaneous zero of the rescaled fold, incidence, and equal-area equations.
Adding a fourth scale coordinate and the cancellation-free density equation
produces a prescribed-density prism.

Thirty-four exact adjacent prisms compose in
[`prescribedDensity_lambda_explicit_combined`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/NearOnePrescribedDensity.lean):

```lean
theorem prescribedDensity_lambda_explicit_combined :
  ∀ (lam : ℝ), 1 < lam →
    lam ≤ 1 + (251 / 20 : ℝ) * (1 / 126334 : ℝ) ^ 3 →
    ∃ s q, ... ∧
      typeThreeFold lam pair.h₃ < 0 ∧
      reducedFoldGap lam pair.h₃ pair.h₄ < 0 ∧
      typeThreePerimeter lam pair.h₃ <
        typeFourPerimeter lam pair.h₄
```

The exact density increment is

$$
\delta_0=\frac{251}{20}\left(\frac1{126334}\right)^3
       =\frac{251}{40326519148554080}
       \approx 6.22419205276237\times10^{-15}.
$$

This small numerical width should not obscure the theorem's role: it is a
direct, kernel-checked construction through the singular endpoint, with exact
prescribed density and strict perimeter improvement.

## 6.3 The scale-local atlas: retained numerical evidence

A separate 160-bit directed-dyadic preflight checks 13 bands with 64 rational
subslabs each, for 832 cells from $\delta_0$ to $10^{-3}$, plus a remote stress
slab. Each saved cell satisfies the proposed face signs, source and denominator
guards, height order, and negative normalized gap. Independent replay validates
the stored arithmetic and mutation tests.

::: {.scope-note}
**Status of the atlas.** The 832-cell preflight is numerical certificate
evidence, not kernel-checked density coverage. Shared interval primitives,
Machin's $\pi$ enclosure, analytic arctangent remainder bounds, and part of a
seam cell are formalized. Generated whole-cell replay exceeded or violated the
accepted resource gates, so those generated stress modules are not counted as
Lean proofs. The public kernel-checked density endpoint remains $1+\delta_0$.
:::

This distinction is intentional. The later universal theorem closes the modeled
range without promoting unverified atlas cells.

# 7. Progress on universal source classification

The remaining theorem is no longer a scalar sign problem. It is the source
classification statement that every relevant source minimizer supplies an exact
or almost-everywhere horizontal representative in one of the checked carrier
families.

## 7.1 Measure-theoretic reconstruction already checked

[`CMVSourceSectionClassification.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVSourceSectionClassification.lean)
proves that the raw five-piece carrier is closed and Borel measurable. Its
non-interface horizontal slices are explicitly empty or centered intervals.
If a source representative has centered interval slices of the same
one-dimensional measure almost everywhere, interval-volume uniqueness and a
Fubini argument yield planar almost-everywhere equality. Thus the final passage
from verified slices to the raw carrier is formalized.

What is not yet formalized is the source theorem producing those slice
hypotheses for every minimizer from Schwarz symmetrization, its equality case,
regularity, circular continuation, and Snell incidence.

## 7.2 Figure 3: strict-radius branch excluded under explicit source data

The Figure-3 development deliberately starts from an independent source
signature rather than a preselected canonical profile.
[`CMVFigureThreeSourceExtraction.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVFigureThreeSourceExtraction.lean)
records one actual closed boundary curve, a branch selection into six ordered
pieces, regular Snell data, reflection symmetry, circular continuation, and
endpoint incidence. From those inputs Lean derives the literal six-piece
frontier and the existing `ActualBoundaryRealization`.

The geometry then constructs the branch-complete type-(iii) assembly and
identifies its actual lower-interface section. The added exterior chord cannot
fit inside that section when $R>1$. Hence:

```lean
theorem strictRadius_false (hR : 1 < c.sourceRadius) : False

theorem sourceRadius_eq_one : c.sourceRadius = 1
```

Both vertical orientations, degenerate interface segments, arbitrary horizontal
placement, and the radius-two semicircular transition are represented. The
result retains—not discards—the separate $R=1$ configuration.

The open input is extraction of the pre-selection boundary curve, branch cuts,
regular Snell law, symmetry, and continuation from every relevant arbitrary
source minimizer.

## 7.3 Figure 4: source-native scalar reduction retained

[`CMVFigureFourSourceGeometry.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVFigureFourSourceGeometry.lean)
freezes an actual source set, a bounded open almost-everywhere representative,
generic interval sections, four common-radius circle traces with actual
junctions, signed Snell laws, reflection, complete frontier, and local
one-sided circle equations. It does not assume normalized widths, target
sections, carrier equality, area formulas, or comparison data.

From those primitives,
[`CMVFigureFourScalarReduction.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVFigureFourScalarReduction.lean)
derives the scalar reduction, horizontal center symmetry, $R\ge1$, the
principal closed-Snell angle, and generic-section endpoints by transverse
intersection arguments. Explicit $\lambda=2$ examples exercise both $R=2$ and
$R=1$ parameter branches.

::: {.scope-note}
**Current Figure-4 boundary.** Full source-geometry instances for the strict and
endpoint branches, actual-to-raw almost-everywhere reconstruction, and
extraction of the frozen primitives from arbitrary minimizers are not proved.
The latest completed Figure-4 strategy retained compiling mathematics but was
terminated after exceeding its precommitted wall-time limit. It adds no
unconditional source classification.
:::

## 7.4 Figure 5: the endpoint-support competitor is proved

The radius-one Figure-3 residual is a segmented Figure-5 configuration; it is
not the literal four-arc endpoint and is not eliminated by renaming it. Its
source boundary may contain one or two exterior caps, unit-radius strip
semicircles, and possibly degenerate interface segments.

One substantial comparison component is now kernel-checked.
[`CMVFigureFiveAngular.lean`](https://github.com/RosaRojacr/agentic-lean-math-assistant/blob/main/projects/cmv-strip-density/proof/CMVFigureFiveAngular.lean)
uses the regular one-sided chart

$$
h(u)=\frac{1+\cos u}{2},\qquad 0\le u<\pi,
$$

and proves that its pole-free area extension has derivative $-4$ at $u=0$.
No source identity is asserted on the invalid negative-angle branch. With

$$
\theta_\lambda=\arccos(1/\lambda),\qquad
\Gamma_\lambda=\lambda\theta_\lambda-\sin\theta_\lambda>0,
$$

the endpoint support intercept is

$$
P_3(\lambda,1)-A_3(\lambda,1)=\pi+\Gamma_\lambda.
$$

Endpoint continuity, area coercivity toward $h=0$, an endpoint-maximum theorem,
and one positive support slope then give, for every
$V\ge A_3(\lambda,1)$, a regular $0<h<1$ with

$$
A_3(\lambda,h)=V,\qquad
P_3(\lambda,h)<V+\pi+\Gamma_\lambda.
$$

The existing branch-complete recovery realizes this as an actual
source-admissible `TypeThreeAssembly`:

```lean
theorem exists_admissible_typeThree_below_endpoint_support
    {lam V : ℝ} (hlam : 1 < lam)
    (hV : LeanSuffixAnalytic.typeThreeArea lam 1 ≤ V) :
    ∃ a : TypeThreeAssembly lam,
      a.h ∈ Set.Ioo (0 : ℝ) 1 ∧
      (relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      WeightedArea lam a.carrier = V ∧
      a.WeightedPerimeter < V + π + endpointGap lam
```

::: {.scope-note}
**Current Figure-5 boundary.** This theorem supplies the regular equal-area
competitor required at and above the singular endpoint area. It does not yet
exclude a Figure-5 source carrier. Full threshold-width and off-center source
instances, literal area identities, and the complete one-charge relaxed
lower-perimeter barrier over every permitted cap and degenerate segment remain
unproved. Subsequent resource-admission rounds added no mathematical coverage.
:::

The exact remaining source obligations are:

1. derive the source regularity, Snell, symmetry, continuation, and
   pre-selection boundary data from every relevant minimizer;
2. construct the complete Figure-5 source instances and lower barrier, then
   combine them with the proved endpoint-support competitor;
3. close the incomplete Figure-4 reconstruction or show that the source
   classification bypasses it;
4. compose all Lemma 3.8 branches with the existing all-density direct source
   exclusion; and
5. audit the resulting theorem against CMV's existence, symmetrization, and
   reduced-boundary hypotheses.

Only after these steps may one claim an unconditional proof of CMV Conjecture
3.12.

# 8. Trust boundary and audit

The development uses Lean 4 [@deMouraUllrich2021] and mathlib [@mathlib2020].
The compiler is pinned by `proof/lean-toolchain`; dependencies are pinned by
`proof/lake-manifest.json`.

| Component | Function | Trusted for Lean theorems? |
|---|---|---:|
| Lean kernel | Checks elaborated proof terms | Yes |
| Pinned mathlib and Brouwer dependency | Imported definitions and theorems | Yes, as imported theory |
| Rational certificate generators | Propose exact cells and source text | No |
| Floating-point or MPFR searches | Locate boxes and diagnostic roots | No |
| Generated `.lean` files | Exact propositions and proof terms | Only after kernel checking |
| Python replay and mutation scripts | Independent diagnostics | No |
| Markdown, Pandoc, HTML, and PDF | Presentation | No |

The cutoff proof is proof-producing: an incorrect numerical proposal can fail
to elaborate, but it cannot make the kernel accept a false real inequality.
Coverage is theorem-level composition, so a missing cell creates a missing
interval rather than an unnoticed loop omission.

The permanent assumption ledgers invoke `#print axioms` on the public cutoff,
universal stationary-pair, source-relaxation, direct source-exclusion,
Figure-5 endpoint-support, and source-classification declarations. The expected
output is a subset of:

```text
propext
Classical.choice
Quot.sound
```

No theorem claimed here may depend on `sorry`, `admit`, a project-local `axiom`,
`native_decide`, or an unchecked numerical oracle. Resource receipts and agent
adjudications are evidence about the construction process; they are not proof
objects and are never substituted for a successful Lean check.

## 8.1 Evidence snapshot

This manuscript describes completed, adjudicated results through autorun round
269 of session `20260902T064759Z-62a799`, plus direct verification commands run
for publication. Round 267 supplied the Figure-5 endpoint-support theorem;
rounds 268 and 269 added no mathematical coverage. Work left active after that
boundary is not silently counted.

# 9. Reproduction

From the repository root, check the exact $51/50$ theorem and its public axiom
ledger:

```bash
cd projects/cmv-strip-density/proof
lake build CMVModeledCutoff
lake env lean CMVCutoffAssumptions.lean
```

Check the stronger all-density scalar and direct source path:

```bash
lake build TypeFourStationaryRootSupport \
  CMVFourArcExhaustionSupport CMVTypeThreeLowerRecoverySupport \
  CMVSourceClassificationSupport
lake env lean CMVTypeThreeSourceExclusionAssumptions.lean
```

Check the explicit near-one prefix and current source-classification modules:

```bash
lake build NearOneFirstCell CMVFigureThreeNonfitSupport \
  CMVFigureFourSourceSupport CMVFigureFiveSourceSupport
lake env lean NearOnePrescribedDensity.lean
lake env lean CMVFigureThreeSourceExtractionAssumptions.lean
lake env lean CMVFigureFourSourceAssumptions.lean
lake env lean CMVFigureFiveSourceAssumptions.lean
```

The full retained development can be checked with:

```bash
lake build
lake env lean _Assumptions.lean
```

Independent certificate checkers are retained beside their inputs:

```bash
uv run python verify_certificate.py
uv run python verify_full_domain.py
uv run python verify_calculus.py
python compact_fold_gap/check_compact_certificate.py \
  compact_fold_gap/compact_certificate.json
python compact_fold_gap/run_mutations.py
python middle_face_tiling/check_tiling.py \
  middle_face_tiling/manifest.json \
  --output middle_face_tiling/independent-check.json
python middle_face_tiling/run_mutations.py
```

Rebuild this paper with:

```bash
cd ../reports
./build-lean-verified-cmv-frontier.sh
```

The renderer produces `lean-verified-cmv-frontier.html` and
`lean-verified-cmv-frontier.pdf`. Neither rendered file participates in the
mathematical trust boundary.

# 10. Conclusion

The exact-rational certificate gives a hard, independently reproducible cutoff:

$$
\boxed{\lambda\ge\frac{51}{50}\Longrightarrow
\text{modeled type (iv) is not minimizing}.}
$$

The later analytic argument is stronger. It proves existence of an ordered
stationary equal-area type-(iii) comparison and strict perimeter improvement at
every $\lambda>1$, then transfers that comparison to arbitrary modeled
curvature. The relaxed-perimeter development realizes the comparison by actual
source-admissible carriers and excludes literal, translated,
almost-everywhere-translated, and raw closed-Snell four-arc carriers, including
the radius-one endpoint.

The old remaining density interval has therefore been closed at the scalar,
modeled-candidate, and classified-carrier levels. The surviving frontier is not
a thin numerical interval. It is a precise geometric/GMT interface: derive the
checked carrier classifications from every arbitrary source minimizer and
eliminate the remaining Lemma 3.8 configurations. The explicit near-one cells,
scale-local atlas, relaxation theory, recovery constructions, and Figure-3/4
source extraction modules document substantial progress toward that interface
without representing it as a completed proof.

# References
