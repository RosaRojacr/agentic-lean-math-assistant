Implemented the branch-aware interval pilot.

### Retained artifacts

- `agents/computation/interval_pilot/interval_probe.py`
- `agents/computation/interval_pilot/interval_results.json`
- `agents/computation/interval_pilot/report.md`

The probe uses `ctypes` with `libmpfr.so.6` at 224-bit precision. Every elementary operation uses directed MPFR rounding. Box endpoints are retained as exact dyadic rationals plus readable decimals.

### Strongest certified result

Using the audited CMV formulas and the retained analytic branch reduction to the fold gap

\[
\Gamma(\lambda)=P_3(\ell(\lambda))-P_4(f_4(\lambda)),
\]

the adaptive interval run certifies

\[
\Gamma(\lambda)<0
\qquad\text{for every }\lambda\in[17/16,3/2].
\]

Coverage comprises 127 terminal boxes, with no unresolved boxes. The tightest upper gap enclosure is

\[
-\frac{
5175068402864548756660590098155753917983288386550287269814703657
}{2^{222}}
\approx -7.6781582200533258\times10^{-4},
\]

on

\[
\lambda\in[2337/2^{11},293/2^8].
\]

Conditional on the exact equal-area reduction, every regular type-(iv) formula profile in this density interval therefore has a descending-branch type-(iii) competitor with the same weighted area and strictly smaller perimeter.

Combined with the retained Lean theorem
`cmv_type_four_not_minimizing` in `proof/CandidateExclusion.lean`, which covers

\[
\lambda\ge1.2581840884,
\]

the remaining density range for the modeled type-(iv) decision is reduced to

\[
1<\lambda<17/16.
\]

This does not close the universal source-profile bridge and therefore does not settle CMV Conjecture 3.12.

### Branch and candidate evidence

The retained fixed rational probes certify:

- one two-root equal-area case, with both type-(iii) roots isolated separately;
- three one-root cases, including the type-(iv) \(h=1\) formula closure;
- unique \(K_3=0\) and \(K_4=0\) fold boxes;
- the \(h_3=1/2\) segment-transition event;
- the \(h_3=1\) second-root entry event;
- type-(ii) comparisons on every probed volume where \(V>\pi\);
- type-(i) marked inapplicable rather than evaluated outside \(V\le\pi\).

The ledger treats \(\rho=0,\rho=1,h=0,h=1\) as distinct boundary obligations. No random sampling, regression, or continued single-root trajectory is used.

### Verification

Command:

```text
python3 agents/computation/interval_pilot/interval_probe.py
```

Observed output:

```text
libmpfr=libmpfr.so.6 precision_bits=224
self_tests_passed=True fixed_cases=4 roots=5
fixed_root_counts=two-root-near-closure:2,h3-transition-probe:1,regular-one-root:1,h4-equals-one-formula-closure:1
coverage_range=[17/16,3/2] attempts=253 terminal=127 certified=127 unresolved=0
global_proof_claimed=False
results=/mnt/games/Math_Project/LeanExperiment/projects/cmv-strip-density/runs/20260824T091317Z-1cbb51/workspace/agents/computation/interval_pilot/interval_results.json
```

Artifact hashes:

```text
526d42b10c965c4de30fe39ca006aefa44c70e9b69d8f513a5bfe2a27a5c8a7a  interval_probe.py
f35daee5bee3b7d51a49d77860e7fbf0ce749f8d2ad8f4a4b91ed6f3824664c7  interval_results.json
42e1bf71fc339e4b5d7d45f839effaf5ae3ef4ba92fd815681ac5ef57d4f94be  report.md
```

### Exact remaining obligations

1. Certify \(\Gamma(\lambda)<0\) on \(1<\lambda<17/16\), including the singular \(\lambda\to1^+\) face.
2. Convert the existing asymptotic
   \[
   \Gamma(1+\delta)
   =-3\pi(2\pi^2)^{-2/3}\delta^{4/3}+o(\delta^{4/3})
   \]
   into an explicit remainder enclosure.
3. Certify the \(h\to0\) boundary tail uniformly rather than relying on the derived asymptotic statement.
4. Formalize the type-(iii) carrier, equal-area branch topology, and reduction from all \(h_4\) to \(\Gamma\).
5. Prove the universal source-level CMV type-(iv) normalization and reduced-boundary/minimality transfer.

### Reproducible next campaign

Use

\[
\lambda=1+t^3,\qquad
h_4=1-t^2u_4,\qquad
h_3=1-t^2u_3,
\]

and enclose the scaled gap \(\Gamma(1+t^3)/t^4\). Derive explicit Taylor remainders for the endpoint-cancelling `sqrt`, `asin`, and `acos` combinations, then apply interval Newton to the scaled fold and equal-area equations. Cover

\[
0<t\le(1/16)^{1/3}
\]

with overlap at \(\lambda=17/16\), retaining the same exact-dyadic coverage ledger. This directly targets the only remaining density interval without widening the already certified compact boxes.
