Completed the geometric-variation pilot.

**Result:** rigorous obstruction for the full fixed-core, fixed-junction redistribution class. For every \(\lambda>1\) and regular \(0<h<1\), redistributing weighted area between two nondegenerate exterior circular caps strictly increases perimeter unless the caps remain equal. This includes semicircular and major-cap branches.

Exact constrained variations at the symmetric type-(iv) profile are

\[
P_f'(0)=0,\qquad
P_f''(0)=
\frac{4(\sin\alpha-\alpha\cos\alpha)}{\sin^2\alpha}>0,
\quad \alpha=\arccos(h/\lambda).
\]

Using transferred Euclidean cap area \(\delta\),

\[
\frac{d^2P_f}{d\delta^2}(0)
=
\frac{h^4}{\sin\alpha-\alpha\cos\alpha}>0.
\]

The global proof establishes that every feasible pair satisfies
\(\theta_++\theta_-<\pi\), which controls the nonconvex major-cap branch and makes the equal pair the unique global minimum.

The singular cap-extinction endpoint is excluded: there the reduced boundary changes and an interface chord of density \(1\) appears, producing a \(2a(\lambda-1)\) perimeter jump. Analyzing that endpoint would reproduce the frozen cap-replacement method. Thus this variation class cannot settle the unresolved range \(1<\lambda<1.2581840884\).

Artifacts:

- `agents/geometric/geometric_variation_pilot/report.md`
- `agents/geometric/geometric_variation_pilot/verify_variation.py`

Verification:

```text
python3 agents/geometric/geometric_variation_pilot/verify_variation.py
```

Result:

```text
precision_digits=100
redistribution_checks=28
major_branch_checks=10
max_normalized_area_residual=3.7682039569356e-97
max_hessian_relative_residual=4.8447310442487e-31
RESULT fixed-junction redistribution checks passed
```

The report also treats \(\lambda\to1^+\), \(h\to0^+\), \(h\to1^-\), the joint \((\lambda,h)\to(1,1)\) degeneration, large \(\lambda\), Snell failure of unequal competitors, reduced-boundary admissibility, and the vanishing moving-junction terms.
