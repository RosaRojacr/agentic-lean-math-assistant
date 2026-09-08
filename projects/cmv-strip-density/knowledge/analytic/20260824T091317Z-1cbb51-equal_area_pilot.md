Completed the equal-area pilot.

### Main result

Using the audited CMV formulas, the analysis proves exactly:

- Each of \(A_{\mathrm{iii}}\) and \(A_{\mathrm{iv}}\) has one nondegenerate fold and at most two curvature roots at fixed area.
- For every \(\lambda>1\) and \(0<h\le1\),
  \[
  A_{\mathrm{iii}}(h)<A_{\mathrm{iv}}(h),\qquad
  P_{\mathrm{iii}}(h)<P_{\mathrm{iv}}(h).
  \]
- Every type-(iv) target has exactly one descending-branch type-(iii) equal-area root. A second root exists precisely when \(A_{\mathrm{iv}}(h_4)<A_{\mathrm{iii}}(1)\); endpoint and branch-transition cases are fully classified.
- The descending root always has the smaller type-(iii) perimeter.
- Along an equal-area branch,
  \[
  \frac{dP_i}{dA_i}=h_i,\qquad
  \frac{d}{dV}(P_3-P_4)=h_3-h_4.
  \]
  Same-curvature equal area is impossible, so there are no regular common-area stationary gaps.
- The minimum type-(iii) gap has one global maximum, attained at the unique type-(iv) area fold.

Thus the complete comparison reduces to one exact scalar sign:

\[
\Gamma(\lambda)
=P_3(\ell(\lambda))-P_4(f_4(\lambda))<0,
\]

where \(K_4(f_4)=0\) and \(\ell\) is the descending root of
\(A_3(\ell)=A_4(f_4)\). The exact gap identity used for certification is

\[
P_3-P_4
=2V(h_3-h_4)-4\bigl(d_\lambda(2h_3-1)-d_\lambda(h_4)\bigr).
\]

### Singular regimes

Derived analytic asymptotics establish:

\[
\Gamma(1+\delta)
=-3\pi(2\pi^2)^{-2/3}\delta^{4/3}
+o(\delta^{4/3})<0
\]

near \(\lambda=1^+\), and

\[
\Gamma(\lambda)
=-(2-\sqrt2)\pi\lambda+O(1)<0
\]

for sufficiently large \(\lambda\). Equal-area gaps also tend to \(-\infty\) through the \(h_3,h_4\to0\) degeneration. The \(h=1\) closures, \(h_3=1/2\) transition, folds, and all endpoint roots are treated separately.

### All-root probe

Command:

```text
python3 agents/analytic/equal_area_pilot/verify_equal_area.py
```

Observed at 90 decimal digits:

```text
lambda_count=62 pair_count=3224 root_count=3551
root_multiplicity zero=0 one=2897 two=327
nonnegative_individual_root_gaps=81
pairs_with_all_root_gaps_nonnegative=0
max_relative_area_residual=1.91568814167320e-66
lower_gap_max=-1.290381026554386328233262e-32
```

A retained interior two-root witness has an upper-root gap \(+0.0125417\), but its companion lower-root gap is \(-0.0178103\). This confirms that following one area inverse can give the wrong conclusion.

Artifacts:

- `agents/analytic/equal_area_pilot/report.md`
- `agents/analytic/equal_area_pilot/verify_equal_area.py`
- `agents/analytic/equal_area_pilot/probe_results.json` — every probed root and gap

### Remaining obligation

The pilot does not settle CMV Conjecture 3.12. The remaining analytic task is an exact or outward-rounded proof of \(\Gamma(\lambda)<0\) on the compact intermediate density range left between the two analytic tails. The universal CMV source-profile/reduced-boundary bridge and formal Lean type-(iii) carrier also remain open.
