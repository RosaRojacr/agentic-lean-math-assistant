The augmented rows are

\[
(1,1\mid 4),\qquad (2,2\mid 8)=2(1,1\mid 4).
\]

Thus the second equation is exactly twice the first, so the equations are **not independent**.

Let \(x=t\). Then every real solution is

\[
(x,y)=(t,4-t),\qquad t\in\mathbb R.
\]

Hence

\[
x-y=t-(4-t)=2t-4,
\]

which varies with \(t\). Therefore, **no unique exact value of \(x-y\) exists**.

Two witnesses:

\[
(x,y)=(0,4):
\quad 0+4=4,\quad 2(0)+2(4)=8,\quad x-y=-4;
\]

\[
(x,y)=(1,3):
\quad 1+3=4,\quad 2(1)+2(3)=8,\quad x-y=-2.
\]

Since \(-4\ne-2\), \(x-y\) is not uniquely determined.

One additional scalar restriction that removes the free parameter \(t\) is minimally required. If it is a linear equation

\[
ax+by=c,
\]

it must be independent of \(x+y=4\), so

\[
\det\begin{pmatrix}1&1\\a&b\end{pmatrix}=b-a\ne 0.
\]

**Retained inputs:** `references/source.md:3` confirms the real domain and absence of hidden constraints; `knowledge/analytic/20260823T004123Z-703163-derive_system_result.md:1-45` contains the accepted derivation. No shell commands were required; verification above uses exact substitution into both equations.
