# Signed classification

Let \(a,b,c,d\in\mathbb R\), with \(b\neq0\), \(d\neq0\), and suppose

\[
\frac ab>\frac cd.
\]

## 1. The denominator product is nonzero

If \(bd=0\), the zero-product property gives \(b=0\) or \(d=0\), contradicting the hypotheses. Hence

\[
bd\neq0.
\]

Therefore exactly one of \(bd>0\) and \(bd<0\) holds.

## 2. Rewrite the difference

Since \(bd\neq0\),

\[
\frac ab-\frac cd
=\frac{ad}{bd}-\frac{bc}{bd}
=\frac{ad-bc}{bd}.
\]

The premise implies

\[
\frac ab-\frac cd>0,
\]

so

\[
\frac{ad-bc}{bd}>0.
\]

## 3. Exhaustive sign split

### Case \(bd>0\)

Multiplication by the positive number \(bd\) preserves the inequality direction:

\[
\frac{ad-bc}{bd}>0
\quad\Longrightarrow\quad
ad-bc>0.
\]

Thus

\[
ad>bc.
\]

### Case \(bd<0\)

Multiplication by the negative number \(bd\) reverses the inequality direction:

\[
\frac{ad-bc}{bd}>0
\quad\Longrightarrow\quad
ad-bc<0.
\]

Thus

\[
ad<bc.
\]

Consequently, the exact signed classification is

\[
\frac ab>\frac cd
\quad\Longrightarrow\quad
\begin{cases}
ad>bc,&bd>0,\\[2mm]
ad<bc,&bd<0.
\end{cases}
\]

## Exact mixed-sign counterexample

Take

\[
(a,b,c,d)=(0,1,1,-1).
\]

Then

\[
b=1\neq0,\qquad d=-1\neq0,\qquad bd=-1<0.
\]

The premise holds exactly:

\[
\frac ab=\frac01=0>-1=\frac1{-1}=\frac cd.
\]

But

\[
ad=0(-1)=0,\qquad bc=1(1)=1,
\]

and hence

\[
ad>bc\iff 0>1,
\]

which is false; in fact \(ad<bc\).

## Status

The requested universal implication is **false as written**. It cannot be reported as successfully proved. No positivity or same-sign hypothesis was added. The valid conclusion depends on the sign of \(bd\), and mixed-sign denominators force the opposite comparison.

## Evidence and locators

- Requested statement and reporting condition: `problem.md:3-7`
- Ordered-field inequality-direction rules: `references/source.md:1-3`
- Reused proof that \(bd\neq0\), difference rewrite, and exhaustive sign split: `knowledge/analytic/20260823T055608Z-bc382f-reconstruct_signed_resolution.md:9-82`
- Reused exact witness and verdict: `knowledge/analytic/20260823T055608Z-bc382f-reconstruct_signed_resolution.md:84-146`

Commands executed: none. Verification used exact ordered-field algebra and exact integer arithmetic; no unresolved mathematical obligations remain.
