# Narrowing the Range

## A machine-checked refinement of the Cañete–Miranda–Vittone four-arc bound

**Working technical note — August 2026**

This is a collaborative working draft, not a journal submission. Final authorship, attribution, and exposition should be agreed by the research collaborators before external circulation.

## Abstract

Cañete, Miranda Jr., and Vittone studied the planar isoperimetric problem with density

\[
f(x,y)=
\begin{cases}
1,& |y|\le 1,\\
\lambda,& |y|>1,
\end{cases}
\qquad \lambda>1.
\]

Their classification leaves one difficult comparison: whether a four-arc candidate of type (iv) can minimize weighted perimeter. In Theorem 3.16 they exclude type (iv) for \(\lambda\ge 4/\pi\), and in Remark 3.17 they observe that their cap-replacement argument has a better threshold \(1/k\), where \(k\) is the minimum of an arc-length comparison function, without computing that minimum.

We formalize this comparison in Lean 4. The formal development constructs the unit-chord circular-arc function, proves that the comparison function

\[
g(x)=2\,\operatorname{arc}(x)-\operatorname{arc}(2x)
\]

has the global minimum

\[
\min_{x>0}g(x)=3\cos\theta_*,
\]

where \(\theta_*\) is the unique solution of

\[
3\theta-3\sin\theta\cos\theta=\pi.
\]

Numerically,

\[
\frac{1}{3\cos\theta_*}=1.25818408832253\ldots.
\]

An exact rational certificate checked by Lean yields the inclusive cutoff

\[
\lambda\ge 1.2581840884.
\]

The development also constructs the regular four-arc candidate and its equal-area cap replacement as planar carriers, proves their complete frontier decompositions, evaluates their Euclidean one-dimensional Hausdorff measures, and derives strict weighted-perimeter improvement. Consequently, Lean proves that any modeled type-(iv) minimizer lies in

\[
1<\lambda<1.2581840884.
\]

Combined with the classification in the original paper, this reduces the unresolved interval from \((1,4/\pi)\) to \((1,1.2581840884)\). The original classification of arbitrary finite-perimeter minimizers and its exhaustiveness relative to the Lean coordinate model remain cited external inputs rather than formalized Lean theorems.

## 1. The strip-density problem

Weighted area and perimeter are determined by the density \(f\). For a sufficiently regular region \(E\subset\mathbb R^2\),

\[
A_f(E)=\int_E f\,d\mathcal L^2,
\qquad
P_f(E)=\int_{\partial E} f\,d\mathcal H^1.
\]

For general finite-perimeter sets, Cañete–Miranda–Vittone (CMV) use the relaxed perimeter and its representation on the reduced boundary. Their Section 3.2 establishes existence and symmetry properties and classifies the possible planar profiles. The relevant source chain is:

1. Propositions 3.5 and 3.6: existence, connectedness, and horizontal-slice structure;
2. Lemma 3.8: classification into candidates (i)–(iv);
3. Proposition 3.9: vertical reflective symmetry;
4. Theorem 3.16: all remaining cases except the possible type-(iv) minimizer, together with the cap-replacement exclusion for \(\lambda\ge 4/\pi\);
5. Remark 3.17: the observation that the constant \(4/\pi\) is not optimal.

A type-(iv) profile is bounded by four circular arcs of a common radius: two arcs inside the strip and two horizontally symmetric exterior arcs. CMV parameterize the profile by curvature \(h\), with \(0<h\le1\), and an exterior half-angle \(\alpha\). Equation (27) gives, equivalently,

\[
\lambda\cos\alpha=h,
\qquad
0<\alpha<\frac\pi2.
\]

The Lean structure `FourArcCandidate` records precisely the nondegenerate geometric parameter domain, while `SatisfiesCMVTypeIVHypotheses` records \(1<\lambda\) and the incidence equation \(\lambda\cos\alpha=h\).

## 2. CMV's cap-replacement inequality

Let an exterior cap have chord length \(L\) and Euclidean area \(A\). CMV remove the two congruent exterior caps, expose the lower chord as a density-one boundary segment, and place a single cap of Euclidean area \(2A\) above the upper chord. The strip portion of the candidate is retained.

Define \(\operatorname{arc}(x)\) to be the length of the circular arc with unit chord enclosing area \(x\). Scaling by \(L\), a cap with area \(A\) has arc length

\[
L\,\operatorname{arc}\!\left(\frac{A}{L^2}\right).
\]

Writing

\[
x=\frac{A}{L^2},
\]

the old exterior contribution is

\[
2\lambda L\,\operatorname{arc}(x),
\]

while the replacement contribution is

\[
\lambda L\,\operatorname{arc}(2x)+L.
\]

The replacement is strictly cheaper precisely when

\[
2\lambda L\,\operatorname{arc}(x)
>
\lambda L\,\operatorname{arc}(2x)+L,
\]

or, equivalently,

\[
g(x):=2\operatorname{arc}(x)-\operatorname{arc}(2x)>\frac1\lambda.
\]

CMV prove \(g(x)>\pi/4\), producing the sufficient condition

\[
\lambda\ge\frac4\pi=1.2732395447\ldots.
\]

The mathematical problem addressed here is therefore exact and narrow: compute the global minimum of \(g\), and certify a usable rational lower bound for it.

## 3. Constructing the arc function

For a unit chord and half-central-angle \(\theta\in(0,\pi)\), define

\[
\ell(\theta)=\frac{\theta}{\sin\theta},
\qquad
\operatorname{area}(\theta)
=
\frac{\theta-\sin\theta\cos\theta}{4\sin^2\theta}.
\]

The Lean file `MorgansArcFunction.lean` proves that `area` is a strictly increasing bijection from \((0,\pi)\) to \((0,\infty)\). Its inverse is denoted by \(\theta(x)\), or `θOf x` in Lean, and

\[
\operatorname{arc}(x)=\ell(\theta(x)).
\]

Differentiating through the inverse parameterization gives the key identity

\[
\operatorname{arc}'(x)=2\sin\theta(x).
\]

This also recovers the semicircle values

\[
\operatorname{arc}\!\left(\frac\pi8\right)=\frac\pi2,
\qquad
\operatorname{arc}'\!\left(\frac\pi8\right)=2.
\]

These are derived from the construction rather than inserted as axioms.

## 4. The exact global minimum

From the derivative of `arc`,

\[
g'(x)=4\bigl(\sin\theta(x)-\sin\theta(2x)\bigr).
\]

The files `GFunction.lean`, `Minimiser.lean`, and `MinimumValue.lean` establish the following chain.

First, \(g'\) is negative to the left of \(\pi/16\) and positive to the right of \(\pi/8\). Hence every global minimizer lies in

\[
\left(\frac\pi{16},\frac\pi8\right).
\]

At an interior critical point, the two distinct angles have the same sine and are therefore supplementary. Combining this relation with the area parameterization reduces the critical-point condition to

\[
F(\theta)=3\theta-3\sin\theta\cos\theta-\pi=0.
\]

Since

\[
F'(\theta)=6\sin^2\theta>0
\]

on the relevant interval, \(F\) has a unique root \(\theta_*\). Setting

\[
x_* = \operatorname{area}(\theta_*),
\]

Lean proves

\[
g(x_*)=3\cos\theta_*.
\]

It then proves that \(g\) is strictly decreasing before \(x_*\) and strictly increasing after \(x_*\). Thus

\[
3\cos\theta_*\le g(x)
\qquad (x>0),
\]

with equality at \(x=x_*\). Numerically,

\[
\theta_*=1.30266283730045\ldots,
\]

\[
3\cos\theta_*=0.794796253808331\ldots,
\]

and therefore the sharp threshold for this cap-replacement strategy is

\[
\lambda_*=\frac1{3\cos\theta_*}
=1.25818408832253\ldots.
\]

Strict improvement at the exact sharp threshold would fail because the minimum is attained: the strategy requires \(1/\lambda<\min g\), hence \(\lambda>\lambda_*\). A rational cutoff slightly above \(\lambda_*\) gives a convenient inclusive theorem.

## 5. The rational certificate

`Certificate.lean` replaces floating-point evidence with exact rational inequalities. The optimized certificate proves

\[
\theta_*<1.30266283731
\]

and establishes a rational lower bound for \(\cos(1.30266283731)\) by reducing the angle through repeated halving and rebuilding certified sine and cosine intervals with double-angle identities. It then proves

\[
\frac1{1.2581840884}
<3\cos(1.30266283731)
<3\cos\theta_*
\le g(x)
\]

for every \(x>0\). The exported theorem is:

```lean
theorem cmv_comparison_bound_optimized {lam x : ℝ}
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (hx : 0 < x) :
    1 / lam < g x
```

The decimal in this statement is an exact rational value in Lean, not a floating-point approximation. The certified cutoff exceeds the sharp value by approximately

\[
7.75\times10^{-11}.
\]

It improves the published cutoff by approximately

\[
\frac4\pi-1.2581840884
=0.0150554563,
\]

which is about \(5.51\%\) of the original interval \((1,4/\pi)\).

## 6. Formalizing the regular geometry

The analytic inequality alone does not establish that the proposed geometric replacement is a legitimate equal-area, lower-perimeter competitor. The files

- `CMVGeometry.lean`,
- `FrontierPerimeter.lean`,
- `FourArcCandidate.lean`,
- `CapReplacement.lean`, and
- `GeometricBridge.lean`

formalize this step.

### 6.1 Coordinate carriers

The four-arc candidate is assembled from a central strip carrier and two reflected exterior circular caps. The construction derives:

- a common radius for all four arcs;
- the original cap chord and cap area;
- horizontal and vertical reflection identities;
- exact weighted-area and explicit component-perimeter formulas;
- the complete topological frontier of the carrier.

The replacement retains the central carrier, removes both exterior caps, exposes the complete lower chord, and inserts one upper cap with twice the old Euclidean cap area. Its inverse-area construction covers minor, semicircular, and major replacement caps; no hidden minor-arc assumption is used.

### 6.2 Euclidean frontier measure

An important formalization issue is that the product type \(\mathbb R\times\mathbb R\) inherits Mathlib's product max metric, whereas CMV use Euclidean arclength. A first attempted frontier theorem was therefore false. The retained research campaign found a concrete counterexample and stopped before accepting it.

The corrected definition maps each coordinate carrier through the coordinate-preserving homeomorphism

\[
\mathbb R\times\mathbb R\longrightarrow
\operatorname{WithLp}_2(\mathbb R\times\mathbb R)
\]

and takes \(\mathcal H^1\) there. In Lean, `FrontierMeasure` is the pullback of Euclidean one-dimensional Hausdorff measure restricted to the realized complete frontier.

`FrontierPerimeter.lean` proves exact Euclidean \(\mathcal H^1\) formulas for circular arcs, the two strip arcs, and horizontal segments. It also proves that distinct boundary components overlap only in finite join sets of \(\mathcal H^1\)-measure zero. These results yield

```lean
theorem fourArc_frontier_weightedPerimeter_eq ...
theorem replacement_frontier_weightedPerimeter_eq ...
```

identifying the component formulas with canonical weighted integrals over the complete Euclidean frontier for both regular families.

### 6.3 Equal area and strict improvement

The bridge proves exact area preservation:

```lean
theorem cap_replacement_preserves_area :
    candidate.capReplacementRegion.WeightedArea =
      candidate.WeightedArea
```

and the signed perimeter identity

\[
P_{\mathrm{new}}-P_{\mathrm{old}}
=L\bigl(1-\lambda g(x)\bigr).
\]

The optimized analytic theorem makes this quantity strictly negative whenever \(\lambda\ge1.2581840884\).

## 7. The formal exclusion theorem

`CandidateExclusion.lean` defines minimality by comparison with every admitted equal-area competitor. The actual contradiction uses the constructed cap replacement. Lean proves:

```lean
theorem cmv_type_four_not_minimizing {lam : ℝ}
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    False
```

For a source-facing statement, the development also exports:

```lean
theorem type_four_minimizer_open_range {lam : ℝ}
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    1 < lam ∧ lam < (1.2581840884 : ℝ)
```

The theorem does not assume area preservation, a perimeter formula, compatibility of boundary measures, or existence of a better competitor. Those facts are derived from the coordinate constructors. Its source-specific assumptions are the nondegenerate parameter domain, \(1<\lambda\), and CMV's incidence equation \(\lambda\cos\alpha=h\).

## 8. What is proved, and what remains external

The result has two distinct trust levels.

### 8.1 Fully machine-checked

Lean verifies that:

1. the arc function has the stated derivative;
2. \(g\) has the unique global minimum \(3\cos\theta_*\);
3. \(\lambda\ge1.2581840884\) implies \(1/\lambda<g(x)\) for all \(x>0\);
4. every constructed four-arc candidate has the claimed carrier, symmetry, and common-radius geometry;
5. the replacement covers all positive-area circular-cap branches;
6. candidate and replacement have equal weighted area;
7. their component costs equal canonical Euclidean \(\mathcal H^1\)-frontier integrals;
8. the replacement has strictly smaller weighted perimeter;
9. a modeled type-(iv) minimizer must lie in \(1<\lambda<1.2581840884\).

The exported theorem and frontier identities use only the standard axioms reported by Mathlib:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, new `axiom`, unsafe declaration, or theorem-shaped compatibility field is used.

### 8.2 Cited from CMV rather than formalized

The Lean project does not reconstruct CMV's complete relaxed finite-perimeter theory. In particular, it does not prove from first principles that:

1. every arbitrary finite-perimeter minimizer has one of the profiles in Lemma 3.8;
2. the symmetrization, regularity, trace, and blow-down arguments apply with all source hypotheses;
3. every source-level type-(iv) profile is exhausted by `FourArcCandidate`;
4. complete topological frontier measure agrees with reduced-boundary perimeter for every arbitrary representative.

For the two explicit regular families used in the cap comparison, the Euclidean frontier calculation is formalized. The remaining gap is the global source-to-model classification, not the analytic inequality or the regular cap substitution.

Accordingly, the strongest precise headline is:

> Combining the machine-checked optimized comparison and regular type-(iv) exclusion with CMV's published classification reduces the unresolved interval from \((1,4/\pi)\) to \((1,1.2581840884)\).

A domain expert should independently review the source-to-model correspondence before this sentence is used in a journal submission.

## 9. Reproducibility

The canonical Lean project pins Lean and Mathlib in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. From the project directory:

```bash
lake exe cache get
lake build
lake env lean _Assumptions.lean
```

The complete build has 8,707 jobs in the retained environment. The two immutable campaign contracts separately check the frontier identities and final exclusion theorem. The retained campaign is

```text
campaign-runs/cmv-frontier-perimeter/20260815T202603Z-dc18b6
```

and its evidence bundle verifies 167 retained artifacts. The canonical publication-plan digest is

```text
38deda72980aa080dd85176d4fe6811183e2ff19d846acc5f87bcd38c408a907
```

The optimized cutoff is checked inside Lean. The auxiliary `verify_certificate.py` script independently checks the earlier, coarser rational witness and should not be confused with the optimized 20-decimal Lean certificate.

## 10. Lessons from the agentic formalization process

The formalization was not simply a translation of a finished hand proof. It separated three kinds of evidence that are easy to conflate:

- numerical exploration, useful for locating the minimizer and designing interval bounds;
- source interpretation, needed to identify the correct CMV parameterization and cap replacement;
- kernel-checked proof, needed to certify the analytic and geometric claims.

The Euclidean-metric correction is the most important methodological example. Several independent components initially appeared consistent, but the inherited max metric made the proposed Hausdorff-measure theorem false. An adversarial research stage produced a counterexample, the build stopped, and the model was revised rather than weakening the theorem or adding a compatibility assumption. The final development uses a genuine Euclidean realization and proves the necessary measure identities.

This illustrates both the value and the limitation of an agentic Lean workflow. Automated agents can search APIs, derive auxiliary lemmas, test constructions, and assemble long formal proofs. Lean can then check the resulting declarations. Neither mechanism alone validates the interpretation of a published source or decides whether the formal model captures every intended object. Those remain collaborative mathematical responsibilities.

## 11. Collaboration and next research steps

Before turning this note into a paper, the collaboration should settle four items.

1. **Source audit.** A geometric-measure-theory expert should check the correspondence table against CMV's Propositions 3.5, 3.6, and 3.9, Lemma 3.8, equation (27), Theorem 3.16, and Remark 3.17.
2. **Authorship and credit.** Separate mathematical contributions, formalization, software infrastructure, source interpretation, auditing, and exposition should be recorded explicitly.
3. **Independent reproduction.** A collaborator should build the canonical project from a clean checkout and compare the theorem statements and axiom output with this note.
4. **Choice of next theorem.** The remaining interval near \(\lambda=1\) probably requires a new geometric comparison rather than a sharper evaluation of the same constant. Alternatively, a larger formalization project could target CMV's source-to-model classification and reduced-boundary framework.

The present result is therefore a natural technical note: it isolates one published nonoptimal constant, computes its sharp analytic value, certifies an essentially sharp rational cutoff, formalizes the regular geometric replacement, and states exactly which part of the broader theorem still comes from the literature.

## 12. Conclusion

CMV's bound \(4/\pi\) is not the limiting value of their cap-substitution argument. The sharp constant is determined by the unique root \(\theta_*\) of

\[
3\theta-3\sin\theta\cos\theta=\pi,
\]

and is

\[
\lambda_*=\frac1{3\cos\theta_*}
=1.25818408832253\ldots.
\]

Lean certifies the inclusive rational cutoff

\[
\boxed{\lambda\ge1.2581840884}
\]

and proves that the corresponding regular four-arc candidate is beaten by an equal-area competitor with strictly smaller Euclidean frontier-weighted perimeter. Hence any modeled type-(iv) minimizer lies in

\[
\boxed{1<\lambda<1.2581840884}.
\]

With CMV's published classification as an external input, this is the promised reduction of the unresolved range.

## Reference

A. Cañete, M. Miranda Jr., and D. Vittone, “Some Isoperimetric Problems in Planes with Density,” *The Journal of Geometric Analysis* **20** (2010), 243–290. arXiv:0906.1256 [math.DG].
