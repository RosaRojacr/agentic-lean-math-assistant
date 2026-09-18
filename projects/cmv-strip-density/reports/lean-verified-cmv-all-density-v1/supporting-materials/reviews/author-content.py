MAIN = r'''## Statement and geometric setting

Cañete, Miranda Jr., and Vittone study the isoperimetric problem for the planar strip density and identify a symmetric four-arc family among the possible minimizers. Their Conjecture 3.12 predicts its exclusion; the relevant geometric descriptions and formulas are in CMV, §3.2, Lemma 3.8 and equations (26)–(27). Here the conclusion concerns the explicit coordinate model of that family, not an unrestricted translation of the source conjecture.

Fix a real number \(\lambda>1\). Write
\[
f_\lambda(x,y)=
\begin{cases}
1,& |y|\leq 1,\\
\lambda,& |y|>1,
\end{cases}
\qquad
A_\lambda(E)=\int_E f_\lambda\,d\mathcal L^2,
\qquad
P_\lambda(E)=\int_{\partial E}f_\lambda\,d\mathcal H^1.
\]
The boundary in the last expression is the complete topological frontier, and Hausdorff measure uses the Euclidean metric. The general competitors in the model are measurable coordinate sets for which the density is integrable over the set and against this frontier measure. The formal competitor class also has explicit empty, four-arc, and replacement constructors; its area and perimeter are determined by their carriers. In particular, minimality is not merely comparison within the four-arc family. [@lean:StripDensity] [@lean:WeightedArea] [@lean:FrontierMeasure] [@lean:WeightedPerimeter] [@lean:FinitePerimeterRegion] [@lean:AdmissibleCompetitor] [@lean:AdmissibleCompetitor.weightedArea_eq_carrier] [@lean:AdmissibleCompetitor.WeightedPerimeter]

A modeled four-arc candidate has parameters satisfying
\[
0<h\leq1,
\qquad
0<\alpha<\frac\pi2,
\qquad
\lambda\cos\alpha=h.
\]
Its common radius is \(R=1/h\), and the two exterior caps have chord length \(2R\sin\alpha\) on the interfaces. The retained strip core joins them with two circular side arcs. The upper and lower caps are reflected copies. These coordinate constructions, together with the displayed parameter bounds, define the modeled candidate; the additional CMV predicate consists precisely of the density jump and incidence equation, not an assumed comparison inequality. The incidence equation gives \(\alpha=\arccos(h/\lambda)\). The strict-curvature range \(0<h<1\) is the regular analytic range; the constructor also retains \(h=1\) as a finite closure endpoint. [@lean:FourArcCandidate] [@lean:FourArcCandidate.capChord] [@lean:FourArcCandidate.stripCore] [@lean:FourArcCandidate.assembly] [@lean:FourArcCandidate.SatisfiesCMVTypeIVHypotheses] [@lean:FourArcCandidate.alpha_eq_arccos]

**Theorem.** For every \(\lambda>1\), every modeled regular type-\(\mathrm{iv}\) four-arc candidate satisfying the formal CMV type-\(\mathrm{iv}\) hypotheses fails to minimize weighted perimeter. More precisely, for every candidate with the parameters just specified, the modeled minimality condition
\[
A_\lambda(F)=A_\lambda(E)
\quad\Longrightarrow\quad
P_\lambda(E)\leq P_\lambda(F)
\qquad\text{for every admissible competitor }F
\]
is false. The formal statement includes the retained closure endpoint; it does not identify that endpoint with an additional regular source profile. [@lean:FourArcCandidate.IsWeightedPerimeterMinimizer] [@lean:CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one]

## Scalar formulas and geometric realization

Suppress the fixed density from the notation. For \(-1\leq x\leq1\), put
\[
B(x)=\lambda\arccos(x/\lambda)+\arcsin x,
\qquad
D(x)=\frac{\sqrt{\lambda^2-x^2}}{\lambda}-\sqrt{1-x^2},
\qquad q(h)=2h-1.
\]
The principal inverse-trigonometric branches are used throughout. The two families have scalar areas and perimeters
\[
\begin{aligned}
A_4(h)&=\frac{2\bigl(B(h)+hD(h)\bigr)}{h^2},
& P_4(h)&=\frac{4B(h)}h,\\
A_3(h)&=\frac{B(q(h))+\pi/2+(q(h)+2)D(q(h))}{h^2},
& P_3(h)&=\frac{2\bigl(B(q(h))+\pi/2+D(q(h))\bigr)}h.
\end{aligned}
\]
The geometric type-\(\mathrm{iii}\) range is \(0<h<1\); the type-\(\mathrm{iv}\) range is \(0<h\leq1\). We will occasionally use the continuous formula value \(A_3(1)\), without treating it as a regular type-\(\mathrm{iii}\) assembly. [@lean:LeanSuffixAnalytic.typeThreeShape] [@lean:LeanSuffixAnalytic.typeThreeAngle] [@lean:LeanSuffixAnalytic.typeThreeDelta] [@lean:LeanSuffixAnalytic.typeThreeArea] [@lean:LeanSuffixAnalytic.typeThreePerimeter] [@lean:LeanSuffixAnalytic.typeFourAngle] [@lean:LeanSuffixAnalytic.typeFourDelta] [@lean:LeanSuffixAnalytic.typeFourArea] [@lean:LeanSuffixAnalytic.typeFourPerimeter]

These are formulas for actual coordinate regions. To describe the type-\(\mathrm{iii}\) competitor at curvature \(h\), let
\[
R=\frac1h,
\qquad \beta=\arccos q(h),
\qquad \alpha=\arccos(q(h)/\lambda),
\qquad w=R(\sin\alpha-\sin\beta).
\]
Its strip core is the rectangle \([-w,w]\times[-1,1]\), together with the portions of the disks centered at \((-w,R-1)\) and \((w,R-1)\) lying respectively to the left and right of this rectangle and within the strip. Add the upper circular cap of radius \(R\), center \((0,1-R\cos\alpha)\), and base on \(y=1\). The complete frontier consists of the two side arcs, the upper cap arc, and the bottom segment. Here \(w\geq0\), with \(w=0\) exactly when \(h=1/2\). The construction includes major, semicircular, and minor upper caps; the vanishing bottom segment is not discarded from the set-theoretic boundary description. [@lean:TypeThreeAssembly] [@lean:TypeThreeAssembly.coreCarrier] [@lean:TypeThreeAssembly.outerCap] [@lean:TypeThreeAssembly.carrier] [@lean:TypeThreeAssembly.sideHalfWidth_eq_zero_iff] [@lean:TypeThreeAssembly.frontier_carrier]

For a circular cap of radius \(R\) and half-central angle \(\theta\in(0,\pi)\), its area and arc length are
\[
R^2(\theta-\sin\theta\cos\theta)
\qquad\text{and}\qquad 2R\theta.
\]
Integrating the circular slices gives the area formula; arclength parametrization gives the Euclidean Hausdorff length. The frontier pieces intersect only in finitely many junctions, which have zero one-dimensional Hausdorff measure. Thus summing the weighted arc lengths counts the complete frontier exactly, including the density-one bottom segment. Applied to the two constructions, these computations give \(A_\lambda(E)=A_4(h)\), \(P_\lambda(E)=P_4(h)\), and the corresponding identities \(A_3(h)\), \(P_3(h)\) for the type-\(\mathrm{iii}\) carrier. Its integrability and measurability supply an admissible competitor, not just a pair of assigned scalar values. [@lean:OneSidedCircularCap.volume_carrier] [@lean:cap_arcLength_eq_two_radius_theta] [@lean:exact_euclidean_capTrace_hausdorffMeasure] [@lean:fourArc_pairwiseOverlap_h1_null] [@lean:fourArc_frontier_weightedPerimeter_eq] [@lean:TypeThreeAssembly.pairwiseOverlap_h1_null] [@lean:TypeThreeAssembly.weightedArea_formula] [@lean:TypeThreeAssembly.weightedPerimeter_formula] [@lean:TypeThreeAssembly.hasModeledCompetitor] [@lean:CMVSuffixModel.TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea] [@lean:CMVSuffixModel.TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter] [@lean:CMVSuffixModel.FourArcCandidate.weightedArea_eq_typeFourArea] [@lean:CMVSuffixModel.FourArcCandidate.weightedPerimeter_eq_typeFourPerimeter]

## Fold monotonicity and a stationary curvature

All differentiations below take place in \(0<h<1\). Define the fold numerators by
\[
\begin{aligned}
F_4(h)&=4\left[h\left(\frac1{\sqrt{1-h^2}}-
\frac\lambda{\sqrt{\lambda^2-h^2}}\right)-B(h)\right],\\
F_3(h)&=4h\left[\frac{1+q(h)}{\sqrt{1-q(h)^2}}-
\frac{\lambda^2+q(h)}{\lambda\sqrt{\lambda^2-q(h)^2}}\right]
-2\left[B(q(h))+\frac\pi2+D(q(h))\right].
\end{aligned}
\]
Direct differentiation yields
\[
A_i'(h)=\frac{F_i(h)}{h^3},
\qquad P_i'(h)=hA_i'(h),
\qquad i\in\{3,4\}.
\]
Thus a zero of the fold is a stationary point of the area profile. It is not a hypothesis imposed on the candidate we ultimately exclude. [@lean:LeanSuffixAnalytic.typeThreeFold] [@lean:LeanSuffixAnalytic.typeFourFold] [@lean:LeanSuffixAnalytic.hasDerivAt_typeThreeArea] [@lean:LeanSuffixAnalytic.hasDerivAt_typeFourArea] [@lean:LeanSuffixAnalytic.typeThree_variational_hasDerivAt] [@lean:LeanSuffixAnalytic.typeFour_variational_hasDerivAt]

For \(-1<x<1\), set
\[
K(x)=\frac1{(1-x^2)^{3/2}}-
\frac\lambda{(\lambda^2-x^2)^{3/2}}.
\]
This is positive: for \(x\ne0\), squaring gives \(\sqrt{\lambda^2-x^2}>\lambda\sqrt{1-x^2}\), and the case \(x=0\) reduces to \(1-\lambda^{-2}>0\). Consequently
\[
F_4'(h)=4h^2K(h)>0,
\qquad F_3'(h)=16h^2K(q(h))>0.
\]
Both folds are strictly increasing. In particular, the type-\(\mathrm{iii}\) area cannot exceed the larger of its endpoint areas on any interval \([a,b]\subset(0,1]\): its derivative can change sign only from negative to positive. Continuity handles \(b=1\). [@lean:LeanSuffixAnalytic.radicalCubeGap_pos] [@lean:LeanSuffixAnalytic.hasDerivAt_typeThreeFold] [@lean:LeanSuffixAnalytic.hasDerivAt_typeFourFold] [@lean:LeanSuffixAnalytic.typeThreeFold_strictMonoOn] [@lean:LeanSuffixAnalytic.typeFourFold_strictMonoOn] [@lean:LeanSuffixAnalytic.typeThreeArea_le_max_endpoints]

To find a stationary type-\(\mathrm{iv}\) curvature without evaluating a singular fold at the endpoint, write \(u(h)=\sqrt{1-h^2}\), \(v(h)=\sqrt{\lambda^2-h^2}\), and use the continuous expression
\[
C(h)=h\bigl(v(h)-\lambda u(h)\bigr)-B(h)u(h)v(h).
\]
On the open interval it satisfies
\[
C(h)=\frac{u(h)v(h)}4F_4(h),
\qquad \frac{u(h)v(h)}4>0.
\]
At \(h=9/10\), we have \(u(h)>2/5\), \(\lambda/v(h)\geq1\), and \(B(h)\geq\pi/2\). Therefore
\[
h\left(\frac1{u(h)}-\frac\lambda{v(h)}\right)
<\frac{27}{20}<\frac\pi2\leq B(h),
\]
so \(C(9/10)<0\). At the other endpoint,
\[
C(1)=\sqrt{\lambda^2-1}>0.
\]
The intermediate value theorem gives a curvature \(s\in(9/10,1)\) with \(F_4(s)=0\). Strict fold monotonicity shows that \(A_4\) decreases before \(s\) and increases after it. Hence
\[
A_4(s)\leq A_4(h)\qquad(0<h\leq1).
\]
Only continuity of the area formula, not an endpoint derivative, is used here. [@lean:LeanSuffixAnalytic.typeFourClearedFold] [@lean:LeanSuffixAnalytic.typeFourClearedFold_continuous] [@lean:LeanSuffixAnalytic.typeFourClearedFold_eq_fold] [@lean:LeanSuffixAnalytic.typeFourClearedFold_multiplier_pos] [@lean:LeanSuffixAnalytic.typeFourClearedFold_nine_tenths_neg] [@lean:LeanSuffixAnalytic.typeFourClearedFold_one_pos] [@lean:LeanSuffixAnalytic.typeFourFold_zero_exists] [@lean:LeanSuffixAnalytic.typeFourArea_fold_le]

## Comparing the two families

We first prove the same-curvature area inequality
\[
A_3(h)<A_4(h)\qquad(0<h\leq1).
\]
Put \(T(x)=B(x)-\pi/2\) and \(M(x)=T(x)-(2-x)D(x)\) for \(0\leq x\leq1\). On the interior, \(T'(x)>0\), \(D'(x)>0\), and
\[
M'(x)=2(x-1)D'(x)\leq0.
\]
Also \(D(0)=0\). With \(\theta=\arccos(1/\lambda)>0\), the endpoint value is
\[
M(1)=\lambda\theta-\sin\theta>0.
\]
It follows that \(T(x)>(2-x)D(x)\) throughout the closed interval. To compare areas, multiply by \(h^2\) and use
\[
\begin{aligned}
h^2A_3(h)&=\pi+T(q(h))+(2h+1)D(q(h)),\\
h^2A_4(h)&=\pi+2T(h)+2hD(h).
\end{aligned}
\]
If \(q(h)\geq0\), monotonicity and \(q(h)\leq h\) bound the first numerator by \(\pi+T(h)+(2h+1)D(h)\), strictly less than the second because \(T(h)>D(h)\). If \(q(h)<0\), use the identities
\[
T(-x)=\pi(\lambda-1)-T(x),\qquad D(-x)=D(x),
\qquad 2T(0)=\pi(\lambda-1).
\]
For \(x=-q(h)\), positivity of \(M(x)\) gives
\[
T(q(h))+(q(h)+2)D(q(h))<2T(0)<2T(h)+2hD(h).
\]
This proves the claimed inequality in both cases, including the finite endpoint. [@lean:LeanSuffixAnalytic.typeThreeArea_lt_typeFourArea]

A second comparison concerns the quantity \(P-hA\). Define
\[
S(x)=B(x)-xD(x)\qquad(0\leq x\leq1).
\]
Since \(S'(x)=-2D(x)\), this function is concave, and the endpoint inequality above gives \(S(1)>\pi/2\). For \(1/2<h<1\), the point \(h\) is the midpoint of \(q(h)\) and \(1\), so
\[
S(q(h))+\frac\pi2<S(q(h))+S(1)\leq2S(h).
\]
The exact identity
\[
h\bigl[(P_3(h)-hA_3(h))-(P_4(h)-hA_4(h))\bigr]
=S(q(h))+\frac\pi2-2S(h)
\]
therefore proves
\[
P_3(h)-hA_3(h)<P_4(h)-hA_4(h).
\]
[@lean:LeanSuffixAnalytic.typeFourSupport] [@lean:LeanSuffixAnalytic.typeFourSupport_hasDerivAt] [@lean:LeanSuffixAnalytic.typeFourSupport_concaveOn] [@lean:LeanSuffixAnalytic.typeFourSupport_one_gt_halfPi] [@lean:LeanSuffixAnalytic.typeFourSupport_midpoint] [@lean:LeanSuffixAnalytic.sameHeight_support_identity] [@lean:LeanSuffixAnalytic.typeThree_support_lt_typeFour_support]

Suppose now that \(1/2<r<h<1\) and \(A_3(r)=A_4(h)=V\). The same-curvature area inequality gives \(A_3(h)<V\). The endpoint-maximum property gives \(A_3(x)\leq V\) for \(r\leq x\leq h\). Introduce
\[
H_V(x)=P_3(x)+x\bigl(V-A_3(x)\bigr),
\qquad H_V'(x)=V-A_3(x)\geq0.
\]
The variational identity justifies the derivative cancellation. Combining monotonicity with the strict comparison of \(P-hA\), we obtain
\[
P_3(r)=H_V(r)\leq H_V(h)<P_4(h).
\]
Moreover, the mean value theorem applied to \(A_3(h)<A_3(r)\) finds a point between them where \(F_3\) is negative. Since \(F_3\) is increasing, \(F_3(r)<0\). [@lean:LeanSuffixAnalytic.typeThreeAreaSupport] [@lean:LeanSuffixAnalytic.typeThreeAreaSupport_hasDerivAt] [@lean:LeanSuffixAnalytic.typeThreePerimeter_lt_typeFourPerimeter_of_equalArea] [@lean:LeanSuffixAnalytic.typeThreeFold_neg_of_equalArea_of_lt]

Apply this to the stationary curvature \(s\). Direct evaluation and elementary endpoint bounds give
\[
A_3(1/2)=2\pi(\lambda+1),
\qquad A_4(1)\leq2\lambda\pi+\pi+2<2\pi(\lambda+1).
\]
Thus
\[
A_3(s)<A_4(s)\leq A_4(1)<A_3(1/2).
\]
By continuity there is \(r\in(1/2,s)\) such that
\[
A_3(r)=A_4(s),\qquad F_3(r)<0,\qquad P_3(r)<P_4(s).
\]
This constructs the required stationary equal-area pair for every \(\lambda>1\), without a density cutoff or a numerical cell decomposition. [@lean:LeanSuffixAnalytic.typeThreeArea_half] [@lean:LeanSuffixAnalytic.typeFourArea_one_lt_typeThreeArea_half] [@lean:LeanSuffixAnalytic.stationaryEqualAreaPair_of_typeFourFold_zero] [@lean:LeanSuffixAnalytic.stationaryEqualAreaPair_exists] [@lean:LeanSuffixAnalytic.stationaryEqualAreaPair_strictImprovement_exists]

## Extending the comparison to every modeled curvature

Fix the pair \((r,s)\) just constructed. On \((0,r]\), the function \(A_3\) is strictly decreasing, since \(F_3\) is increasing and \(F_3(r)<0\). Also
\[
\lim_{h\downarrow0}A_3(h)=+\infty.
\]
Indeed, its numerator tends to the strictly positive number
\[
\lambda\arccos(-1/\lambda)+\frac{\sqrt{\lambda^2-1}}\lambda.
\]
For every \(h\in(0,1]\), the inequality \(A_4(h)\geq A_4(s)=A_3(r)\) therefore supplies a unique descending root \(\rho(h)\in(0,r]\) satisfying
\[
A_3(\rho(h))=A_4(h),\qquad F_3(\rho(h))<0.
\]
Uniqueness here is on the negative-fold branch; no uniqueness of every equal-area root is being assumed. In particular, \(\rho(s)=r\). [@lean:LeanSuffixAnalytic.typeThreeArea_tendsto_atRight_zero] [@lean:LeanSuffixAnalytic.typeThreeArea_strictAntiOn_Icc_of_fold_neg_right] [@lean:LeanSuffixAnalytic.typeThreeArea_descending_root_existsUnique] [@lean:LeanSuffixAnalytic.typeThreeArea_descending_root_existsUnique_of_stationary_pair]

The same-curvature area comparison implies the strict order \(\rho(h)<h\). Otherwise, strict decrease on the negative-fold branch would contradict \(A_3(h)<A_4(h)=A_3(\rho(h))\). The root is continuous on \((0,1]\): near any \(h_0\), choose \(a\in(0,\rho(h_0))\); continuity of \(A_4\) and strict decrease of \(A_3\) trap the nearby roots in the compact regular interval \([a,r]\). On that interval, uniqueness and the closed equal-area equation give continuity. This includes one-sided continuity at \(h=1\). In the interior, \(A_3'(\rho(h))<0\), and the inverse-function theorem gives
\[
\rho'(h)=\frac{A_4'(h)}{A_3'(\rho(h))}.
\]
[@lean:LeanSuffixAnalytic.typeThreeArea_descending_root_lt] [@lean:LeanSuffixAnalytic.equalAreaRoot_continuousOn_of_compact_unique] [@lean:LeanSuffixAnalytic.equalAreaRoot_hasDerivAt]

Consider the genuine equal-area perimeter gap
\[
\Delta(h)=P_3(\rho(h))-P_4(h).
\]
Differentiating the equal-area constraint and using the two variational identities yields
\[
\Delta'(h)=(\rho(h)-h)A_4'(h).
\]
The first factor is negative; the second is negative before \(s\) and positive after it. Consequently \(\Delta\) increases up to \(s\) and decreases thereafter. Continuity extends the comparison to the closure endpoint, giving
\[
\Delta(h)\leq\Delta(s)=P_3(r)-P_4(s)<0
\qquad(0<h\leq1).
\]
This is the all-curvature step: stationarity is used to locate the maximum of the gap, not to restrict the candidate being compared. [@lean:LeanSuffixAnalytic.equalAreaPerimeterGap] [@lean:LeanSuffixAnalytic.equalAreaPerimeterGap_hasDerivAt] [@lean:LeanSuffixAnalytic.equalAreaPerimeterGap_lt_fold] [@lean:LeanSuffixAnalytic.equalAreaPerimeterGap_le_fold] [@lean:LeanSuffixAnalytic.allCurvature_typeThreeImprovement_of_envelope]

For the original modeled candidate at curvature \(h\), construct the regular type-\(\mathrm{iii}\) carrier at \(\rho(h)\). The geometric identities above give it exactly the candidate's weighted area and strictly smaller complete-frontier weighted perimeter. It is admissible, so substituting it into the modeled minimality condition is a contradiction. This proves the theorem. [@lean:FourArcCandidate.not_isWeightedPerimeterMinimizer_of_typeThree] [@lean:CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree] [@lean:CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair]

## Closing scope

The all-density theorem subsumes the earlier modeled cutoff \(\lambda\geq51/50\) and closes the entire modeled interval \(1<\lambda<51/50\). Its subject is precisely modeled regular type-\(\mathrm{iv}\) candidates satisfying the formal hypotheses, with the formal constructor's closure endpoint handled separately by continuity. It neither changes the perimeter convention nor turns a model parameterization into a source-normalization theorem.

Two obligations remain separate before one can claim the unqualified source-level CMV Conjecture 3.12: normalization of every source-defined type-\(\mathrm{iv}\) region into the formal candidate, and compatibility of CMV's reduced-boundary perimeter with the model's complete-frontier perimeter for the candidate and its constructed competitor. The source uses reduced boundaries in §2, whereas the present theorem uses the frontier integral defined above. A full universal classification of every arbitrary minimizer is stronger than the bridge needed here: transferring this exclusion requires identifying the source type-\(\mathrm{iv}\) candidate and validating the admissibility, area, and perimeter of this comparison, not formally classifying all possible minimizers.

## Bibliography

A. Cañete, M. Miranda Jr., and D. Vittone, “Some isoperimetric problems in planes with density,” *The Journal of Geometric Analysis* **20** (2010), 243–290. Preprint arXiv:0906.1256; cited here at §2 and §3.2, especially Lemma 3.8, Conjecture 3.12, and equations (26)–(27).
'''

INTRO = r'''The supplement records the mathematical meanings of the declarations in the publication closure. The main text follows the stationary-pair and equal-area-envelope argument; the supporting entries retain the coordinate geometry, Euclidean Hausdorff-measure calculations, branch bounds, integrability results, and algebraic identities that make the scalar comparison an admissible geometric comparison. Each entry's statement and explanation describe mathematics; the separately displayed declaration identifier, source location, and Lean code are source metadata rather than additional hypotheses.

The notation \(f_\lambda,A_\lambda,P_\lambda,B,D,q,A_3,P_3,A_4,P_4,F_3,F_4\) agrees with the main proof. Unless a statement specifies a larger domain, the analytic comparisons assume \(\lambda>1\) and regular curvatures in \((0,1)\); individual entries explicitly indicate endpoint extensions. Generic geometric integration lemmas often permit arbitrary real \(\lambda\), since integrability does not require positivity. A cap has chord length \(L>0\), half-central angle \(0<\theta<\pi\), chord midpoint \((m,b)\), and radius \(R=L/(2\sin\theta)\). Write \(a(\theta)=(\theta-\sin\theta\cos\theta)/(4\sin^2\theta)\) and \(\ell(\theta)=\theta/\sin\theta\). A strip core has chord \(L>0\), curvature \(0<\kappa\leq1\), radius \(R=1/\kappa\), and side angle \(\phi=\arcsin\kappa\). For a type-\(\mathrm{iii}\) assembly, use \(R=1/h\), \(q=2h-1\), \(\beta=\arccos q\), \(\alpha=\arccos(q/\lambda)\), \(\gamma=\pi-\beta\), and \(w=R(\sin\alpha-\sin\beta)\). Symbols for carriers and arc traces denote the coordinate sets defined in their entries, and all Hausdorff measures are Euclidean. The coordinate identification \(J\) sends an ordered pair of real numbers to the same point equipped with the Euclidean norm.

No generated declaration families are configured in this frozen package, and no inventoried declaration is marked generated. Accordingly there are no generated-family representatives or numerical coverage ledgers to supply. Elementary rational estimates and repetitive algebra remain in the Lean proofs; the all-density argument does not depend on a density-cell certificate. The supplement does not extend the root to an unqualified source conjecture or supply the separate normalization and boundary-perimeter compatibility obligations.'''
