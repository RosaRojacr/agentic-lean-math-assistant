# GCD and Bézout certificate for \(84\) and \(30\)

The general Euclidean-algorithm and back-substitution principles used below are retained in [`references/source.md`](references/source.md), under **“Permitted source record.”** All concrete arithmetic is derived here.

## 1. Euclidean-algorithm proof

The complete Euclidean remainder chain is

\[
84=2\cdot 30+24,
\qquad 0\le 24<30,
\]

\[
30=1\cdot 24+6,
\qquad 0\le 6<24,
\]

\[
24=4\cdot 6+0,
\qquad 0\le 0<6.
\]

Thus the remainders strictly decrease:

\[
30>24>6>0,
\]

and the first zero remainder follows \(6\). Therefore the last nonzero remainder is \(6\).

### \(6\) divides both inputs

Explicit integer quotients witness both divisibilities:

\[
84=6\cdot 14,
\qquad
30=6\cdot 5.
\]

Hence \(6\mid 84\) and \(6\mid 30\).

### Every common divisor divides \(6\)

Let \(d\in\mathbb Z\) satisfy

\[
d\mid 84
\quad\text{and}\quad
d\mid 30.
\]

A divisor of two integers divides every integer linear combination of them. From the first remainder equality,

\[
24=84-2\cdot 30,
\]

so \(d\mid 24\). From the second remainder equality,

\[
6=30-24,
\]

so \(d\mid 6\).

Thus \(6\) divides both original inputs, while every common divisor of \(84\) and \(30\) divides \(6\). Therefore

\[
\boxed{\gcd(84,30)=6}.
\]

## 2. Bézout back-substitution proof

Start with the remainder equality that produced \(6\):

\[
6=30-1\cdot 24.
\]

The preceding equality gives

\[
24=84-2\cdot 30.
\]

Substitute this expression for \(24\), showing each algebraic step:

\[
\begin{aligned}
6
  &=30-1\cdot 24\\
  &=30-1\cdot(84-2\cdot 30)\\
  &=30-84+2\cdot 30\\
  &=-84+3\cdot 30\\
  &=84(-1)+30(3).
\end{aligned}
\]

Hence explicit Bézout coefficients are

\[
\boxed{u=-1,\qquad v=3},
\]

and indeed

\[
84u+30v=84(-1)+30(3)=-84+90=6.
\]

### Separate universal-divisor proof from the Bézout identity

Again, let \(d\in\mathbb Z\) be any common divisor of \(84\) and \(30\). Then there are integers \(a,b\) such that

\[
84=da,\qquad 30=db.
\]

Using the Bézout identity,

\[
\begin{aligned}
6
  &=84(-1)+30(3)\\
  &=(da)(-1)+(db)(3)\\
  &=d(-a+3b).
\end{aligned}
\]

Because \(-a+3b\in\mathbb Z\), this proves \(d\mid 6\). Together with

\[
84=6\cdot14,\qquad 30=6\cdot5,
\]

it independently establishes both gcd divisibility directions and therefore confirms

\[
\boxed{\gcd(84,30)=6}.
\]

**Evidence inspected:** `problem.md`, `references/source.md`, and `knowledge/index.json` (which contains no retained artifacts). No failures, limitations, or unresolved obligations.
