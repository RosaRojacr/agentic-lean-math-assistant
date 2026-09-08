# Signed refutation

## Ordered-field derivation

Let \(a,b,c,d\in\mathbb R\), with \(b\neq 0\) and \(d\neq 0\). Then \(bd\neq 0\), and

\[
\frac ab-\frac cd
=\frac{ad}{bd}-\frac{bc}{bd}
=\frac{ad-bc}{bd}.
\]

Assume the strict antecedent

\[
\frac ab>\frac cd.
\]

Subtracting \(c/d\) gives

\[
\frac ab-\frac cd>0,
\]

hence

\[
\frac{ad-bc}{bd}>0.
\]

The consequence depends on the sign of \(bd\):

1. **If \(bd>0\):** multiplying by \(bd\) preserves the inequality:
   \[
   ad-bc>0,
   \]
   so
   \[
   ad>bc.
   \]

2. **If \(bd<0\):** multiplying by \(bd\) reverses the inequality:
   \[
   ad-bc<0,
   \]
   so
   \[
   ad<bc.
   \]

Because \(b,d\neq 0\), these are the only cases. Thus denominators with the same sign give \(bd>0\) and support the requested conclusion; mixed-sign denominators give \(bd<0\) and force the opposite strict inequality.

## Exact counterexample certificate

Take

\[
(a,b,c,d)=(0,1,1,-1).
\]

Exact checks:

1. Nonzero denominators:
   \[
   b=1\neq 0,\qquad d=-1\neq 0.
   \]

2. Mixed signs:
   \[
   b=1>0,\qquad d=-1<0,\qquad bd=1(-1)=-1<0.
   \]

3. Strict antecedent:
   \[
   \frac ab=\frac01=0,
   \qquad
   \frac cd=\frac1{-1}=-1,
   \]
   and therefore
   \[
   \frac01>\frac1{-1}
   \quad\Longleftrightarrow\quad
   0>-1,
   \]
   which is true.

4. Requested conclusion:
   \[
   ad=0(-1)=0,\qquad bc=1(1)=1.
   \]
   Hence the asserted conclusion would be
   \[
   0(-1)>1(1)
   \quad\Longleftrightarrow\quad
   0>1,
   \]
   which is false. In fact, \(ad<bc\), exactly as the \(bd<0\) classification predicts.

All calculations are exact; no floating-point evidence was used.

## Resolution

The universal implication is **false as written**. Consequently, the requested universal proof cannot validly be produced without adding a denominator-sign hypothesis, which the assignment forbids.

## Retained evidence and status

Workspace-relative locators:

- Problem: `problem.md`
- Ordered-field source: `references/source.md`
- Accepted counterexample report:  
  `knowledge/computational/20260823T005350Z-d78df8-construct_counterexample.md`
- Accepted JSON record:  
  `knowledge/computational/20260823T005350Z-d78df8-construct_counterexample.json`

The JSON record has `"status": "accepted"` and records independent analytic verification under `"verified_by": ["audit_sign_and_counterexample"]`.

The accepted report refers to `agents/computational/construct_counterexample/certificate.json`; that auxiliary path is not present in the current workspace. This does not affect the retained accepted Markdown report or JSON record. No shell commands or proof-assistant formalization were used. No unresolved mathematical obligations remain.
