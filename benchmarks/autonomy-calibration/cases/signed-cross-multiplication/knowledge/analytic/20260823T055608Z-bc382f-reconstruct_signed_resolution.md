# Signed resolution

Let \(a,b,c,d\in\mathbb R\), with \(b\neq 0\) and \(d\neq 0\), and suppose

\[
\frac ab>\frac cd.
\]

## 1. Establish \(bd\neq 0\)

If \(bd=0\), the zero-product property for real numbers would imply \(b=0\) or \(d=0\), contradicting the hypotheses. Therefore

\[
bd\neq 0.
\]

## 2. Rewrite the difference

Because \(bd\neq0\),

\[
\frac ab-\frac cd
=\frac{ad}{bd}-\frac{bc}{bd}
=\frac{ad-bc}{bd}.
\]

The assumed inequality gives

\[
\frac ab-\frac cd>0,
\]

and hence

\[
\frac{ad-bc}{bd}>0.
\]

Since \(bd\neq0\), exactly one of \(bd>0\) and \(bd<0\) holds.

## 3. Exhaustive sign split

### Case \(bd>0\)

Multiplication by the positive number \(bd\) preserves the inequality:

\[
ad-bc>0.
\]

Therefore

\[
ad>bc.
\]

This is the regime in which the requested cross-multiplication conclusion is valid.

### Case \(bd<0\)

Multiplication by the negative number \(bd\) reverses the inequality:

\[
ad-bc<0.
\]

Therefore

\[
ad<bc.
\]

Thus mixed-sign denominators produce the opposite strict comparison. Equivalently,

\[
\frac ab>\frac cd
\quad\Longrightarrow\quad
\begin{cases}
ad>bc,& bd>0,\\
ad<bc,& bd<0.
\end{cases}
\]

## 4. Exact mixed-sign counterexample

Substitute exactly

\[
(a,b,c,d)=(0,1,1,-1).
\]

The denominator hypotheses hold:

\[
b=1\neq0,\qquad d=-1\neq0.
\]

Their signs are mixed, and

\[
bd=1(-1)=-1<0.
\]

The antecedent evaluates exactly to

\[
\frac ab=\frac01=0,
\qquad
\frac cd=\frac1{-1}=-1,
\]

so

\[
\frac ab>\frac cd
\iff 0>-1,
\]

which is true.

The proposed conclusion evaluates to

\[
ad=0(-1)=0,
\qquad
bc=1(1)=1,
\]

so

\[
ad>bc
\iff 0>1,
\]

which is false. Indeed,

\[
ad=0<1=bc,
\]

as the \(bd<0\) case predicts.

## Verdict

The universal implication in `problem.md` is **false as written**. A valid universal proof cannot be reported: when \(bd<0\), the premise implies \(ad<bc\), not \(ad>bc\). No positivity hypothesis has been added.

## Retained evidence

Workspace-relative locators:

- Statement under review: `problem.md`
- Ordered-field sign rules: `references/source.md`
- Retained signed derivation: `knowledge/analytic/20260823T024453Z-130e0f-reconstruct_signed_resolution.md`
- Retained exact witness: `knowledge/computational/20260823T005350Z-d78df8-construct_counterexample.md`

The absent `agents/computational/construct_counterexample/certificate.json` was not used. No shell, floating-point, or proof-assistant commands were run. Exact symbolic arithmetic resolves all coverage obligations; no mathematical obligations remain unresolved.
