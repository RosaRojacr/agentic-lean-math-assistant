# GCD and Bézout certificate

\[
\boxed{\gcd(84,30)=6}
\]

## 1. Euclidean-algorithm proof

The complete Euclidean remainder chain is

\[
84=2\cdot30+24,
\qquad 0\le 24<30,
\]

\[
30=1\cdot24+6,
\qquad 0\le 6<24,
\]

\[
24=4\cdot6+0,
\qquad 0\le 0<6.
\]

Each equality is arithmetically valid:

\[
2\cdot30+24=84,\qquad
1\cdot24+6=30,\qquad
4\cdot6+0=24.
\]

The first zero remainder occurs after \(6\), so \(6\) is the last nonzero remainder. Therefore, by the Euclidean algorithm,

\[
\boxed{\gcd(84,30)=6}.
\]

The required divisibility characterization is also explicit. First,

\[
84=6\cdot14,\qquad 30=6\cdot5,
\]

so \(6\mid84\) and \(6\mid30\).

Now let \(d\in\mathbb Z\) be arbitrary and suppose

\[
d\mid84\qquad\text{and}\qquad d\mid30.
\]

Because a common divisor divides every integer linear combination,

\[
24=84-2\cdot30
\]

implies \(d\mid24\). Then

\[
6=30-24
\]

implies \(d\mid6\). Thus \(6\) divides both inputs, and every common divisor of the inputs divides \(6\). Since \(6>0\), it is the positive greatest common divisor.

## 2. Bézout back-substitution proof

Begin with

\[
6=30-24
\]

and use

\[
24=84-2\cdot30.
\]

Back-substitution gives

\[
\begin{aligned}
6
 &=30-24\\
 &=30-(84-2\cdot30)\\
 &=30-84+2\cdot30\\
 &=-84+3\cdot30\\
 &=84(-1)+30(3).
\end{aligned}
\]

Hence the explicit Bézout coefficients are

\[
\boxed{u=-1,\qquad v=3}.
\]

Direct evaluation verifies the identity:

\[
84u+30v
=84(-1)+30(3)
=-84+90
=6.
\]

This identity also proves the common-divisor condition independently. If \(d\in\mathbb Z\), \(d\mid84\), and \(d\mid30\), then there exist \(a,b\in\mathbb Z\) such that

\[
84=da,\qquad 30=db.
\]

Therefore,

\[
6=84(-1)+30(3)
  =(da)(-1)+(db)(3)
  =d(-a+3b).
\]

Since \(-a+3b\in\mathbb Z\), \(d\mid6\). Together with

\[
84=6\cdot14,\qquad 30=6\cdot5,
\]

this confirms again that

\[
\boxed{\gcd(84,30)=6}.
\]

**Evidence inspected:** `problem.md`, `references/source.md`, `knowledge/analytic/20260823T030622Z-f26548-compose_certificate.md`, and `knowledge/analytic/20260822T233912Z-7e3d4c-derive_certificate.md`.

**Commands executed:** none; only workspace file reads were required.  
**Failures, limitations, and unresolved obligations:** none.
