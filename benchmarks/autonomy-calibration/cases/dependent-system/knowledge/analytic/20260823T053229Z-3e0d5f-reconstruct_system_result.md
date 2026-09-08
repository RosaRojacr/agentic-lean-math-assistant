# Campaign-local derivation

## Permitted source scope

- `problem.md:3-9`: \(x,y\in\mathbb R\) satisfy
  \[
  x+y=4,\qquad 2x+2y=8,
  \]
  and \(x-y\) must be determined from these equations alone.
- `references/source.md:3`: these equations are the complete constraints. No sign, integrality, ordering, optimization, normalization, or other auxiliary condition is permitted.

## Independence and rank

The augmented rows are

\[
R_1=(1,1\mid 4),\qquad R_2=(2,2\mid 8).
\]

Exactly,

\[
R_2=2R_1,
\qquad
R_2-2R_1=(0,0\mid 0).
\]

Therefore the equations are **not independent**. Both the coefficient matrix and augmented matrix have rank \(1\):

\[
\operatorname{rank}
\begin{pmatrix}
1&1\\
2&2
\end{pmatrix}
=
\operatorname{rank}
\begin{pmatrix}
1&1&4\\
2&2&8
\end{pmatrix}
=1.
\]

## Complete real solution set

Only \(x+y=4\) remains as an independent constraint. Taking \(x=t\), where \(t\in\mathbb R\), gives

\[
(x,y)=(t,4-t),\qquad t\in\mathbb R.
\]

Thus

\[
x-y=t-(4-t)=2t-4.
\]

This expression is not constant as \(t\) varies. Exact witnesses are:

\[
(x,y)=(0,4):
\quad 0+4=4,\quad 2(0)+2(4)=8,\quad x-y=-4,
\]

and

\[
(x,y)=(1,3):
\quad 1+3=4,\quad 2(1)+2(3)=8,\quad x-y=-2.
\]

Since both pairs satisfy both equations while \(-4\ne-2\), there is no real constant \(c\) such that every solution satisfies \(x-y=c\).

## Requested numerical value

**No exact numerical value for \(x-y\) is entailed by the equations alone.** Selecting one would require an unstated auxiliary condition.

## Retained evidence

- `knowledge/analytic/20260823T004123Z-703163-derive_system_result.md:1-45`
- `knowledge/analytic/20260823T011347Z-32bf4e-produce_exact_answer.md:1-43`
- `knowledge/analytic/20260823T015022Z-31c929-convert_retained_certificate.md:1-46`

Verification used exact augmented-row comparison and exact substitution of both witnesses. Commands run: none. Failures, limitations, and unresolved obligations: none.
