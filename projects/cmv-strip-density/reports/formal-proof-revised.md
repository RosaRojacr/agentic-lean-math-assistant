# Narrowing the Range

## A machine-checked refinement of the Cañete–Miranda–Vittone four-arc bound

**Revised technical note — 21 August 2026**

> **What changed in this revision.** This version incorporates the completed
> frontier/perimeter campaign. It replaces the earlier component-level
> perimeter model with canonical weighted integrals over the complete
> Euclidean frontier, records the correction from Mathlib's product max metric
> to the Euclidean metric, covers minor, semicircular, and major replacement
> caps, and states the final Lean exclusion theorem. It also sharpens the trust
> boundary: the regular cap comparison is machine-checked, while CMV's
> symmetrization and candidate-reduction theorems are cited, and the
> reduced-boundary source-to-model correspondence is stated separately as an
> external input. The numerical threshold is unchanged.

This is a collaborative technical note, not a journal submission. Final
attribution and exposition should be agreed by the research collaborators
before external circulation.

## Abstract

Cañete, Miranda Jr., and Vittone study the planar isoperimetric problem with
strip density

\[
f_\lambda(x,y)=
\begin{cases}
1,& |y|\le 1,\\
\lambda,& |y|>1,
\end{cases}
\qquad \lambda>1.
\]

Their Theorem 3.16 excludes type (iv) when \(\lambda\ge 4/\pi\).
In the last part of its proof, CMV compare two exterior caps with one
equal-area cap and an exposed chord. Remark 3.17 then says that this same
comparison has a better threshold \(1/k\), where
\(k=\min_{x>0}(2\operatorname{arc}(x)-\operatorname{arc}(2x))\), but CMV do
not evaluate \(k\) [CMV, Theorem 3.16, pp. 22–24; Remark 3.17, p. 24].

We formalize the comparison in Lean 4. For the length
\(\operatorname{arc}(x)\) of the circular arc with unit chord enclosing area
\(x\), define

\[
g(x)=2\operatorname{arc}(x)-\operatorname{arc}(2x).
\]

Lean proves

\[
\min_{x>0}g(x)=3\cos\theta_*,
\]

where \(\theta_*\) is the unique solution of

\[
3\theta-3\sin\theta\cos\theta=\pi.
\]

Consequently, the sharp threshold for this particular cap substitution is

\[
\lambda_* = \frac{1}{3\cos\theta_*}
 = 1.25818408832253\ldots.
\]

An exact rational certificate gives the convenient inclusive cutoff

\[
\lambda\ge 1.2581840884.
\]

Inside an explicit coordinate model, the geometric development takes an
arbitrary `FourArcCandidate` satisfying the recorded type-(iv) incidence
equation and constructs an equal-area cap replacement. It proves complete
topological-frontier decompositions for both carriers, evaluates their
components using Euclidean one-dimensional Hausdorff measure, identifies
those component costs with canonical weighted-frontier integrals, and proves
strict perimeter improvement. Thus every minimizer **in that model** satisfies

\[
1<\lambda<1.2581840884.
\]

To transfer this statement to an arbitrary CMV finite-perimeter minimizer one
must additionally use CMV's reduction to the four candidate families
[CMV, Proposition 3.6, Lemma 3.8, and Proposition 3.9] and identify a
source-level type-(iv) representative with the Lean coordinates while
preserving reduced-boundary perimeter. That last source-to-model
identification is not proved in Lean. Subject to it, the parameter range in
which type (iv) is not excluded narrows from \((1,4/\pi)\) to
\((1,1.2581840884)\). This note does not prove CMV Conjecture 3.12.

## 1. Statement and scope

For a sufficiently regular region \(E\subset\mathbb R^2\), write

\[
A_\lambda(E)=\int_E f_\lambda\,d\mathcal L^2,
\qquad
P_\lambda(E)=\int_{\partial E}f_\lambda\,d\mathcal H^1.
\]

The formal theorem concerns the explicit regular coordinate model represented
by `FourArcCandidate`. At the level of that model, Lean proves:

```lean
theorem type_four_minimizer_open_range
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    1 < lam ∧ lam < (1.2581840884 : ℝ)
```

Equivalently, at or above the certified cutoff:

```lean
theorem cmv_type_four_not_minimizing
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    False
```

The result does not claim that a type-(iv) minimizer exists below the cutoff,
nor does it settle CMV Conjecture 3.12. Unconditionally, it is a range
reduction for the explicit Lean coordinate model; its source-facing use is
conditional on §1.1(3).

### 1.1 Logical dependency of the conclusion

It is useful to separate three statements that are easy to conflate.

1. **CMV source reduction.** CMV prove existence and structural properties
   for planar minimizers, classify the vertically symmetric candidates, and
   then prove that every planar minimizer has the required vertical symmetry
   [CMV, Propositions 3.5–3.6, Lemma 3.8, Proposition 3.9].
2. **Machine-checked modeled comparison.** Given a `FourArcCandidate` and the
   hypotheses displayed above, Lean constructs a competitor of the same
   modeled weighted area and proves that its modeled weighted perimeter is
   smaller when \(\lambda\ge1.2581840884\).
3. **Source-to-model correspondence.** To apply item 2 to item 1, one must
   show that a source type-(iv) finite-perimeter representative can be put in
   the Lean coordinates and that CMV's reduced-boundary perimeter agrees with
   the modeled complete-frontier integral. This note treats that
   correspondence as an external geometric-measure-theory input.

Accordingly, the Lean theorem itself uses only item 2. The source-facing range
reduction uses items 1–3. No later argument in this note silently promotes
item 3 to a machine-checked theorem.

## 2. Exact CMV inputs and how they are used

The primary source is [CMV]. The page numbers below refer to the 40-page
arXiv:0906.1256v1 PDF retained with the project.

| Source locator | What CMV state | Use in this note |
|---|---|---|
| §2 opening, pp. 2–3 | Weighted volume is \(\int_E f\,dx\). The relaxed weighted perimeter is represented by integration over the reduced boundary of a finite-perimeter set. | Fixes the source notion that must eventually be compared with the Lean complete-frontier integral. |
| Proposition 3.5, p. 13 | For the planar strip density, an isoperimetric set exists for every prescribed volume and is connected. | Part of the source reduction; not needed for the conditional Lean theorem. |
| Proposition 3.6, pp. 13–14 | A symmetric minimizer exists; almost every horizontal slice is an interval in dimension two; traces at \(y=\pm1\) are regular; a non-strip minimizer touches both sides of the strip. | Supplies the slice and trace structure used before CMV's candidate classification. |
| Lemma 3.8, statement p. 15, proof pp. 15–18 | Up to density-preserving isometries, the vertically symmetric candidates are types (i)–(iv). Type (iv) has four equal-radius arcs, with two strip arcs and reflected exterior arcs. Step 2 proves horizontal symmetry of type (iv). | Identifies the source family that the modeled four-arc coordinates are intended to represent. Lemma 3.8 alone does **not** say that every minimizer is vertically symmetric. |
| Proposition 3.9, p. 18 | Every planar strip isoperimetric region has reflection symmetry about a vertical line. | Combined with Lemma 3.8, passes from actual minimizers to the candidate list. A horizontal translation is still allowed. |
| Equation (27) and following displays, p. 19 | For type (iv), \(\widehat\beta=\pi/2-\arcsin h\), \(\widehat\alpha=\arccos(\cos\widehat\beta/\lambda)\), and \(0<h\le1\), followed by the area and perimeter formulas. | On the principal branches, \(\cos\widehat\beta=h\), so \(\lambda\cos\widehat\alpha=h\). This is the incidence equation stored by `SatisfiesCMVTypeIVHypotheses`. |
| Lemma 3.8, Step 3, pp. 17–18; Remark 3.14, p. 21 | The radius-one threshold-contact configuration is excluded from minimizer eligibility, and the area/perimeter curves fold near \(h=1\). | The displayed formulas have a finite \(h=1\) closure, but an actual regular source minimizer has \(0<h<1\). The Lean coordinate type conservatively includes the closure \(h=1\). |
| Theorem 3.16, statement pp. 22–23, cap argument pp. 23–24 | CMV partially classify minimizers and prove that type (iv) never occurs for \(\lambda\ge4/\pi\), including equality. | Supplies the cap-replacement construction and the original bound being sharpened. |
| Remark 3.17, p. 24 | If \(k\) is the true minimum of the cap comparison, the same argument works for \(\lambda>1/k\); \(k>\pi/4\), but \(k<1\), so this substitution cannot settle all small \(\lambda\). | Motivates the exact minimization performed here. It is not evidence that type (iv) minimizes when the substitution fails. |

The density in §3.2 is \(1\) on \(|y|\le1\) and \(\lambda\) on
\(|y|>1\); in particular, the interface itself has cost \(1\). The source
uses reduced-boundary perimeter for general finite-perimeter sets. Those two
conventions matter in the geometric bridge and are not inferred merely from
the displayed candidate formulas.

## 3. The cap-replacement inequality

Let either exterior cap have chord length \(L>0\) and Euclidean area \(A>0\).
In the final part of the proof of Theorem 3.16, CMV remove the two congruent
exterior caps, expose a chord on \(y=-1\), and insert above the strip one cap
with the same chord and Euclidean area \(2A\) [CMV, pp. 23–24]. The unchanged
central part cancels from both area and perimeter comparisons.

Put

\[
x=\frac{A}{L^2}.
\]

The definition of \(\operatorname{arc}(x)\) uses a unit chord. Scaling a
unit-chord segment by \(L\) multiplies its area by \(L^2\) and its arclength by
\(L\). Therefore a cap with chord \(L\) and area \(A\) has arc length
\(L\operatorname{arc}(x)\), while the doubled-area cap has arc length
\(L\operatorname{arc}(2x)\). Both circular arcs lie in density \(\lambda\);
the newly exposed interface chord has density \(1\). Hence the removed and
inserted perimeter contributions are, respectively,

\[
2\lambda L\operatorname{arc}(x)
\quad\text{and}\quad
\lambda L\operatorname{arc}(2x)+L.
\]

Because \(L>0\), the replacement is strictly cheaper if and only if

\[
\begin{aligned}
2\lambda L\operatorname{arc}(x)
&>\lambda L\operatorname{arc}(2x)+L,\\
g(x):=2\operatorname{arc}(x)-\operatorname{arc}(2x)
&>\frac1\lambda.
\end{aligned}
\]

CMV call this comparison function \(h\), not \(g\). Their tangent-line
argument at its minimizer proves \(g(x)>\pi/4\) for every \(x>0\); since the
inequality is strict, it also covers the endpoint
\(\lambda=4/\pi\) [CMV, proof of Theorem 3.16, p. 24]. Remark 3.17 explicitly
identifies the sharper constant as the true minimum of this function. The
remaining analytic task is therefore exactly—not heuristically—to compute
\(\min_{x>0}g(x)\).

## 4. Circular segments and the arc derivative

For a unit chord and half-central-angle \(0<\theta<\pi\), the radius, arc
length, and enclosed area are

\[
r(\theta)=\frac1{2\sin\theta},
\qquad
\ell(\theta)=\frac{\theta}{\sin\theta},
\]

\[
a(\theta)=
\frac{\theta-\sin\theta\cos\theta}{4\sin^2\theta}.
\]

The interval \((0,\pi)\) contains minor, semicircular, and major arcs. Direct
differentiation gives

\[
\ell'(\theta)=
\frac{\sin\theta-\theta\cos\theta}{\sin^2\theta},
\]

\[
a'(\theta)=
\frac{\sin\theta-\theta\cos\theta}{2\sin^3\theta}.
\]

Let

\[
q(\theta)=\sin\theta-\theta\cos\theta.
\]

Then \(q(0)=0\) and

\[
q'(\theta)=\theta\sin\theta>0
\qquad(0<\theta<\pi).
\]

Thus \(q(\theta)>0\) on \((0,\pi)\), and the displayed formula for \(a'\)
shows that \(a\) is strictly increasing. The endpoint limits are
\(a(\theta)\to0\) as \(\theta\to0^+\) and
\(a(\theta)\to\infty\) as \(\theta\to\pi^-\). Continuity and strict
monotonicity therefore make

\[
a:(0,\pi)\longrightarrow(0,\infty)
\]

a bijection. Define

\[
\theta(x)=a^{-1}(x),
\qquad
\operatorname{arc}(x)=\ell(\theta(x)).
\]

Since \(a'(\theta)>0\), the inverse-function theorem applies. The chain rule
and the common factor \(q(\theta)\) in \(\ell'\) and \(a'\) give

\[
\operatorname{arc}'(x)
=\frac{\ell'(\theta(x))}{a'(\theta(x))}
=2\sin\theta(x).
\]

This is proved in `MorgansArcFunction.lean`, together with the bijectivity and
inverse identities used here.

## 5. The exact global minimum

Differentiating

\[
g(x)=2\operatorname{arc}(x)-\operatorname{arc}(2x)
\]

yields

\[
\boxed{g'(x)=4\bigl(\sin\theta(x)-\sin\theta(2x)\bigr)}.
\]

A unit-chord semicircle has area \(\pi/8\), so
\(\theta(\pi/8)=\pi/2\). The derivative signs away from the transition
interval are explicit:

- If \(0<x\le\pi/16\), then
  \(0<\theta(x)<\theta(2x)\le\pi/2\). Sine is strictly increasing there, so
  \(g'(x)<0\).
- If \(x\ge\pi/8\), then
  \(\pi/2\le\theta(x)<\theta(2x)<\pi\). Sine is strictly decreasing there, so
  \(g'(x)>0\).

Any critical point must consequently have

\[
\frac\pi{16}<x<\frac\pi8.
\]

In this interval \(\theta(x)<\pi/2<\theta(2x)\). At a critical point the two
angles are distinct and have equal sine; on these specified branches the only
possibility is

\[
\theta(2x)=\pi-\theta(x).
\]

Write \(\theta=\theta(x)\). Since \(x=a(\theta)\), the last identity is
equivalent to

\[
a(\pi-\theta)=2a(\theta).
\]

Substituting the displayed formula for \(a\) and multiplying by
\(4\sin^2\theta>0\) gives

\[
3\theta-3\sin\theta\cos\theta=\pi.
\]

Set

\[
F(\theta)=3\theta-3\sin\theta\cos\theta-\pi.
\]

Now

\[
F'(\theta)=6\sin^2\theta>0
\qquad(0<\theta<\pi),
\]

while \(F(0)=-\pi<0\) and \(F(\pi/2)=\pi/2>0\). Hence there is exactly one
root \(\theta_*\in(0,\pi/2)\). Conversely, the equation
\(F(\theta_*)=0\) gives
\(a(\pi-\theta_*)=2a(\theta_*)\), so
\(x_*=a(\theta_*)\) is a critical point. It is therefore the unique critical
point of \(g\).

The derivative is continuous. It is negative before the unique zero and
positive after it (otherwise another zero would occur between a sign change).
Thus \(g\) is strictly decreasing on \((0,x_*)\) and strictly increasing on
\((x_*,\infty)\). This sign argument, formalized in `GFunction.lean` and
`Minimiser.lean`, proves that \(x_*\) is the global minimizer.

Finally,

\[
\begin{aligned}
g(x_*)
&=2\ell(\theta_*)-\ell(\pi-\theta_*)\\
&=\frac{3\theta_*-\pi}{\sin\theta_*}\\
&=3\cos\theta_*,
\end{aligned}
\]

where the last equality is exactly \(F(\theta_*)=0\). Therefore
`MinimumValue.lean` proves

\[
\boxed{\min_{x>0}g(x)=3\cos\theta_*}.
\]

Numerically,

\[
\theta_*=1.30266283730045\ldots,
\]

\[
3\cos\theta_*=0.794796253808331\ldots,
\]

and

\[
\boxed{
\lambda_*=\frac1{3\cos\theta_*}
=1.25818408832253\ldots
}.
\]

At \(\lambda=\lambda_*\), equality occurs for \(x=x_*\), so this particular
substitution is not uniformly strict at the exact sharp threshold. An
inclusive theorem requires a rational number slightly larger than
\(\lambda_*\).

## 6. Exact rational certification

`Certificate.lean` proves exact rational inequalities, not conclusions from
the decimal approximations above. It uses the rational number

\[
t_0=1.30266283731.
\]

First, exact bounds show \(0<t_0<\pi/2\) and \(F(t_0)>0\). Since \(F\) is
strictly increasing and \(F(\theta_*)=0\), this proves
\(\theta_*<t_0\). Cosine is strictly decreasing on \((0,\pi)\), so

\[
\cos t_0<\cos\theta_*.
\]

The same Lean file derives a rational lower bound for \(\cos t_0\) from
rational small-angle bounds and exact repeated double-angle identities. The
final certified chain is

\[
\frac1{1.2581840884}
<3\cos t_0
<3\cos\theta_*
\le g(x)
\qquad (x>0).
\]

If \(\lambda\ge1.2581840884>0\), reciprocal monotonicity gives
\(1/\lambda\le1/1.2581840884\). Combining this non-strict inequality with the
strict first inequality above yields

\[
\boxed{
\lambda\ge1.2581840884
\Longrightarrow
\frac1\lambda<g(x)
\quad\text{for every }x>0.
}
\]

In Lean:

```lean
theorem cmv_comparison_bound_optimized {lam x : ℝ}
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (hx : 0 < x) :
    1 / lam < g x
```

The decimal is elaborated as an exact rational. The certified cutoff is only
about \(7.75\times10^{-11}\) above the sharp threshold.

## 7. The revised geometric bridge

The analytic inequality alone supplies neither a planar competitor nor a
perimeter comparison. The files `CMVGeometry.lean`,
`FrontierPerimeter.lean`, `FourArcCandidate.lean`, `CapReplacement.lean`, and
`GeometricBridge.lean` close that gap **for the explicit coordinate model**.
They do not prove the universal source-to-model correspondence isolated in
§1.1.

### 7.1 Candidate and replacement carriers

The Lean structure assumes an exterior half-angle
\(\alpha\in(0,\pi/2)\), curvature \(0<h\le1\), and the source incidence
equation

\[
\lambda\cos\alpha=h.
\]

This is exactly equation (27) on its principal branches: CMV define
\(\widehat\beta=\pi/2-\arcsin h\) and
\(\widehat\alpha=\arccos(\cos\widehat\beta/\lambda)\), and
\(\cos\widehat\beta=h\) for \(0<h\le1\) [CMV, p. 19]. The model includes the
finite closure \(h=1\); as noted in §2, actual regular source-minimizer
profiles require \(0<h<1\).

The common radius is \(R=1/h\). Either original exterior cap has chord length
and area

\[
L=\frac{2\sin\alpha}{h}>0,
\qquad
A=\frac{\alpha-\sin\alpha\cos\alpha}{h^2}>0.
\]

Consequently,

\[
\frac{A}{L^2}
=\frac{\alpha-\sin\alpha\cos\alpha}{4\sin^2\alpha}
=a(\alpha).
\]

The replacement angle is \(\theta(2A/L^2)\). By the defining inverse identity
\(a(\theta(z))=z\), its cap area is exactly \(2A\), not merely numerically
close to \(2A\). Because \(\theta\) ranges over all of \((0,\pi)\), this
construction covers minor, semicircular, and major replacement arcs.

The original coordinate carrier consists of a central strip core and two
reflected exterior caps. The replacement retains that core, removes both
caps, inserts one doubled-area upper cap, and exposes the full lower chord.

### 7.2 Euclidean frontier measure

A load-bearing correction concerns the ambient metric. Mathlib's ordinary
product type \(\mathbb R\times\mathbb R\) carries the product max metric, not
the Euclidean metric used for planar arclength. An earlier proposed
Hausdorff-measure theorem was therefore false; an adversarial campaign stage
found a counterexample and the theorem was rejected.

The corrected construction maps the coordinate carrier through the
coordinate-preserving homeomorphism

\[
\mathbb R\times\mathbb R
\longrightarrow
\operatorname{WithLp}_2(\mathbb R\times\mathbb R)
\]

and measures the realized frontier there. `FrontierMeasure` is the pullback of
Euclidean one-dimensional Hausdorff measure restricted to the complete
realized topological frontier.

`FrontierPerimeter.lean` proves, for these explicit assemblies:

- exact Euclidean \(\mathcal H^1\) formulas for every circular arc, strip arc,
  and exposed segment;
- measurability of the realized components;
- that pairwise overlaps lie in finite join sets and are therefore
  \(\mathcal H^1\)-null;
- complete frontier decompositions for candidate and replacement;
- equality between explicit component costs and weighted integrals over those
  modeled complete Euclidean frontiers.

The principal identities are:

```lean
theorem fourArc_frontier_weightedPerimeter_eq ...
theorem replacement_frontier_weightedPerimeter_eq ...
```

Thus no equality between a component sum and the modeled frontier integral is
assumed as a theorem-shaped hypothesis. What is **not** proved here is that
this complete-topological-frontier integral agrees, for every arbitrary CMV
finite-perimeter representative, with CMV's reduced-boundary perimeter.

### 7.3 Equal area and strict improvement

The geometric bridge proves

```lean
theorem cap_replacement_preserves_area :
    candidate.capReplacementRegion.WeightedArea =
      candidate.WeightedArea
```

and the exact perimeter-difference formula

\[
P_\lambda(E_{\mathrm{new}})-P_\lambda(E_{\mathrm{iv}})
=
L\bigl(1-\lambda g(x)\bigr).
\]

If \(\lambda\ge1.2581840884\), then \(\lambda>0\), and the certificate gives
\(1/\lambda<g(x)\). Multiplication by the positive number \(\lambda\) yields
\(1<\lambda g(x)\), hence \(1-\lambda g(x)<0\). Since \(L>0\),

\[
\boxed{
P_\lambda(E_{\mathrm{new}})
<
P_\lambda(E_{\mathrm{iv}}).
}
\]

The proved area identity makes the modeled replacement an equal-area
competitor. By the definition of `IsWeightedPerimeterMinimizer`, which
quantifies over every modeled `AdmissibleCompetitor`, this strict inequality
contradicts modeled minimality.

## 8. What Lean checks

The following table gives the concrete proof object behind each manuscript
claim. A file name is evidence only because the named declaration is checked
by the pinned Lean build.

| Manuscript claim | Checked declaration(s) |
|---|---|
| \(a:(0,\pi)\to(0,\infty)\) is bijective and \(\theta=a^{-1}\). | `area_strictMonoOn`, `area_surjOn`, `area_θOf`, and `θOf_area` in `MorgansArcFunction.lean`. |
| \(\operatorname{arc}'(x)=2\sin\theta(x)\). | `hasDerivAt_arc` in `MorgansArcFunction.lean`. |
| \(x_*\) is the global minimizer and \(\min g=3\cos\theta_*\). | `g_xstar_le`, `min_g_eq_three_mul_cos_θstar`, and `min_g_attained` in `MinimumValue.lean`. |
| The exact rational cutoff works for every \(x>0\). | `cmv_comparison_bound_optimized` in `Certificate.lean`. |
| Explicit candidate/replacement component costs equal their modeled Euclidean-frontier integrals. | `fourArc_frontier_weightedPerimeter_eq` and `replacement_frontier_weightedPerimeter_eq` in `FrontierPerimeter.lean`. |
| The modeled replacement preserves area and has the stated perimeter difference. | `cap_replacement_preserves_area` and `cap_replacement_perimeter_difference` in `GeometricBridge.lean`. |
| The modeled perimeter improvement is strict, including at the rational cutoff. | `cap_replacement_strictly_improves` and `cap_replacement_strict_at_campaign_threshold` in `GeometricBridge.lean`. |
| A modeled type-(iv) minimizer lies in the stated open interval. | `cmv_type_four_not_minimizing` and `type_four_minimizer_open_range` in `CandidateExclusion.lean`. |

The exported exclusion theorem and frontier identities report only the
standard axioms

```text
[propext, Classical.choice, Quot.sound]
```

and use no `sorry`, `admit`, new `axiom`, unsafe declaration, or
proof-substituting compatibility field.

## 9. What remains external

The formal project does not reconstruct CMV's general
geometric-measure-theory argument. In particular, Lean does not reprove:

1. Proposition 3.6's symmetrization, slice, and regular-trace conclusions;
2. Proposition 3.9's vertical symmetry for every planar minimizer;
3. the passage from those facts and Lemma 3.8 to a normalized
   `FourArcCandidate`, modulo density-preserving isometries and null-set
   representatives;
4. equality between CMV's reduced-boundary perimeter and the modeled complete
   topological-frontier integral for every such representative;
5. transfer of source-level minimality through that normalization.

Items 1 and 2 are published CMV theorems. Items 3–5 are the precise
source-to-model correspondence being used externally; calling them
"classification" without this decomposition would obscure the logical gap.
For the two explicit regular coordinate carriers, the Euclidean frontier and
perimeter calculations themselves are machine-checked.

The strongest source-facing conclusion is therefore conditional:

> Assume the CMV reduction in Propositions 3.6 and 3.9 and Lemma 3.8, together
> with the source-to-model correspondence in items 3–5 above. Then the
> machine-checked modeled exclusion reduces the \(\lambda\)-interval in which
> a type-(iv) minimizer has not been excluded from
> \((1,4/\pi)\) to \((1,1.2581840884)\).

A domain expert should independently audit the source-to-model correspondence
before this statement is promoted as a journal-level result.

## 10. Reproducibility and retained evidence

The canonical Lean project pins Lean and Mathlib in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`. From
`projects/cmv-strip-density/proof`:

```bash
lake build
uv run python verify_certificate.py
```

The build contains 8,707 jobs in the retained environment. The canonical
completed campaign is

```text
projects/cmv-strip-density/runs/20260815T202603Z-dc18b6
```

Its state records that all required stages succeeded, both Lean contracts
passed, the independent frontier audit accepted the result, and 30 proof
artifacts were promoted. Its evidence index contains 167 retained artifacts.

The optimized cutoff is checked inside Lean. The auxiliary Python verifier
independently checks the retained rational-certificate calculations; it is a
reproducibility aid, not part of Lean's trusted proof kernel.

## 11. Conclusion

The CMV constant \(4/\pi\) is not the limiting value of the cap-substitution
argument. Its sharp analytic threshold is

\[
\lambda_*
=
\frac1{3\cos\theta_*}
=
1.25818408832253\ldots,
\]

where \(\theta_*\) is the unique root of

\[
3\theta-3\sin\theta\cos\theta=\pi.
\]

Lean certifies the inclusive rational cutoff

\[
\boxed{\lambda\ge1.2581840884}
\]

and proves that every explicit four-arc candidate satisfying the modeled CMV
incidence hypotheses is beaten by an equal-area modeled competitor with
strictly smaller Euclidean frontier-weighted perimeter. Hence every minimizer
in that coordinate model lies in

\[
\boxed{1<\lambda<1.2581840884}.
\]

For a source-level finite-perimeter conclusion, one must additionally invoke
CMV Propositions 3.6 and 3.9 and Lemma 3.8, plus the reduced-boundary
source-to-model correspondence stated in §9. Under those explicit external
inputs, the argument narrows—but does not eliminate—the range in which type
(iv) remains unexcluded. It does not settle CMV Conjecture 3.12.

## Reference

**[CMV]** A. Cañete, M. Miranda Jr., and D. Vittone, “Some Isoperimetric
Problems in Planes with Density,” *The Journal of Geometric Analysis* **20**
(2010), 243–290; arXiv:0906.1256. Retained arXiv-PDF locators: weighted
perimeter, pp. 2–3; strip density and Propositions 3.5–3.6, pp. 13–14;
Lemma 3.8, pp. 15–18; Proposition 3.9, p. 18; equation (27), p. 19;
Remark 3.14, p. 21; Theorem 3.16, pp. 22–24; Remark 3.17, p. 24.
