# Signed resolution

Let \(a,b,c,d\in\mathbb R\), with \(b\neq 0\) and \(d\neq 0\). Begin with

\[
\frac ab-\frac cd
=\frac{ad}{bd}-\frac{bc}{bd}
=\frac{ad-bc}{bd}.
\]

The common denominator is valid because \(b\neq0\) and \(d\neq0\). Moreover, \(bd\neq0\): if \(bd=0\), the zero-product property for real numbers would imply \(b=0\) or \(d=0\), contradicting the hypotheses.

Assume

\[
\frac ab>\frac cd.
\]

Subtracting \(c/d\) from both sides gives

\[
\frac ab-\frac cd>0,
\]

so the identity yields

\[
\frac{ad-bc}{bd}>0.
\]

Since \(bd\neq0\), ordered-field trichotomy makes the following two cases exhaustive.

1. **Case \(bd>0\).** Multiplication by the positive number \(bd\) preserves the inequality:

   \[
   ad-bc>0.
   \]

   Therefore

   \[
   ad>bc.
   \]

2. **Case \(bd<0\).** Multiplication by the negative number \(bd\) reverses the inequality:

   \[
   ad-bc<0.
   \]

   Therefore

   \[
   ad<bc.
   \]

Thus the requested conclusion follows when \(bd>0\), but the opposite strict comparison follows when \(bd<0\). In particular, same-sign denominators have \(bd>0\), while mixed-sign denominators have \(bd<0\).

## Exact mixed-sign counterexample

Take exactly

\[
(a,b,c,d)=(0,1,1,-1).
\]

Every condition and comparison evaluates as follows:

- First nonzero-denominator hypothesis:

  \[
  b=1\neq0.
  \]

- Second nonzero-denominator hypothesis:

  \[
  d=-1\neq0.
  \]

- The denominators have mixed signs, and

  \[
  bd=1(-1)=-1<0.
  \]

- Strict antecedent:

  \[
  \frac ab=\frac01=0,
  \qquad
  \frac cd=\frac1{-1}=-1.
  \]

  Hence

  \[
  \frac ab>\frac cd
  \iff
  0>-1,
  \]

  which is true.

- Requested conclusion:

  \[
  ad=0(-1)=0,
  \qquad
  bc=1(1)=1.
  \]

  Thus

  \[
  ad>bc
  \iff
  0>1,
  \]

  which is false. Indeed, \(ad<bc\), as the \(bd<0\) case predicts.

Therefore the universal implication in `problem.md` is **false as written**. No valid universal proof can be reported without adding a denominator-sign hypothesis, which the assignment prohibits.

## Retained evidence

Workspace-relative locators:

- Problem statement: `problem.md`
- Ordered-field rules: `references/source.md`
- Accepted analytic derivation:  
  `knowledge/analytic/20260823T020407Z-7b964d-derive_signed_refutation.md`
- Accepted analytic metadata (`"status": "accepted"`):  
  `knowledge/analytic/20260823T020407Z-7b964d-derive_signed_refutation.json`
- Accepted exact computational record:  
  `knowledge/computational/20260823T005350Z-d78df8-construct_counterexample.md`
- Accepted computational metadata (`"status": "accepted"`):  
  `knowledge/computational/20260823T005350Z-d78df8-construct_counterexample.json`

The absent `agents/computational/construct_counterexample/certificate.json` was not used. No floating-point calculations, shell commands, or proof-assistant commands were used. No mathematical obligations remain unresolved.
