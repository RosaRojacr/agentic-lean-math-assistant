## Decision

No regular type-(iv) region minimizes for any \(\lambda>1\).

For every admissible \(0<h_4<1\), the descending type-(iii) equal-area root \(h_3\) satisfies

\[
A_3(h_3,\lambda)=A_4(h_4,\lambda),
\qquad
P_3(h_3,\lambda)<P_4(h_4,\lambda).
\]

Thus, using CMV Lemma 3.8, Proposition 3.9, and Theorem 3.16, Conjecture 3.12 holds over the full domain:

- type (i) for \(0<v<\pi\);
- at \(v=\pi\), the unit disk, also the zero-segment type-(ii) degeneration;
- type (ii) for \(\pi<v<v_*(\lambda)\);
- at \(v=v_*(\lambda)\), at least one type-(ii) and one distinct type-(iii) minimizer;
- type (iii) for \(v>v_*(\lambda)\);
- no type-(iv) minimizer.

Here \(v_*(\lambda)\) is CMV Theorem 3.16’s \(v_0\).

## Proof coverage

The complete equal-area analysis proves:

- each area family has one nondegenerate fold;
- every type-(iv) target has exactly one descending type-(iii) root;
- the second type-(iii) root exists exactly when \(A_4(h_4)<A_3(1)\);
- the descending root always has smaller type-(iii) perimeter;
- \(h_3=1/2\), \(h_3=1\), both folds, branch transitions, and endpoint roots are covered;
- the minimum equal-area gap has one global maximum
  \[
  \Gamma(\lambda)
  =P_3(\ell(A_4(f_4)))-P_4(f_4).
  \]

The full-domain sign is established in three pieces:

1. \(1<\lambda\le17/16\): cancellation-free scaling
   \[
   \lambda=1+t^3,\qquad h_4=1-t^2a,\qquad h_3=1-t^2b,
   \]
   with one Taylor box and 107 directed-MPFR compact boxes.

2. \(17/16\le\lambda\le3/2\): retained 127-box directed-MPFR certificate.

3. \(\lambda\ge3/2\): exact analytic proof that \(\Gamma'(\lambda)<0\), starting from the certified \(\Gamma(3/2)<0\).

Hence

\[
\boxed{\Gamma(\lambda)<0\quad\text{for every }\lambda>1.}
\]

There is no admissible equality case. As \(\lambda\to1^+\),

\[
\frac{\Gamma(\lambda)}{(\lambda-1)^{4/3}}
\longrightarrow
-3\pi(2\pi^2)^{-2/3}<0.
\]

## Artifacts

- `agents/analytic/full_domain_proof/report.md`
- `agents/analytic/full_domain_proof/scaled_interval_certificate.py`
- `agents/analytic/full_domain_proof/scaled_interval_certificate.json`
- `agents/analytic/full_domain_proof/verify_full_domain.py`

The report contains the source audit, formula reconstruction, all-root theorem, exact large-\(\lambda\) argument, geometric normalization, boundary ledger, classification deduction, commands, outputs, and limitations.

## Verification

`scaled_interval_certificate.py`:

```text
tail=[0,1/2^8]
compact=[1/2^8,13/2^5] attempts=213 terminal=107 certified=107 unresolved=0
adjacencies=106/106 exact=True
K3_transition_signs_negative=108/108
global_Gamma_over_t4_upper=-19147056112786742784287931064497997453614283575313799525799125428299/2^230
global_statement=Gamma(lambda)<0 for every 1<lambda<=17/16
```

`verify_full_domain.py`:

```text
EXACT low_t=[0,13/32] entries=108 adjacencies=107/107 K3_negative=108/108 Gamma_scaled_upper_negative=108/108
EXACT compact_lambda=[17/16,3/2] boxes=127 adjacencies=126/126 Gamma_upper_negative=127/127
EXACT large_lambda_tail=analytic Gamma_strictly_decreasing_on_[3/2,infinity) area_margin>13/96 j_margin>4/315 K3_upper<-132/25
HASH source=0ee9b4787aa3c09f9a4ed05fb66563a820cd13596af401b76e7900e597711230
FULL_DOMAIN_LEDGER_RESULT=PASS
```

Source/formula audit: `AUDIT_RESULT=PASS`; all four symbolic formula differences reduced to zero.

Lean baseline:

```text
Build completed successfully (8707 jobs).
```

The retained formal theorem remains `cmv_type_four_not_minimizing` in `proof/CandidateExclusion.lean:18-34`. The new full-domain proof and source bridge are derived and replayably certified but not yet encoded in Lean. Trusted external inputs are CMV’s published existence, regularity, symmetry, and classification results at the locators documented in the report, plus MPFR correctness for the certificate checker.
