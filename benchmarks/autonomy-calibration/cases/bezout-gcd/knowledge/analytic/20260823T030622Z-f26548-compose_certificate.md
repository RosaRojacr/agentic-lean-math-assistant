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

because \(2\cdot30+24=60+24=84\);

\[
30=1\cdot24+6,
\qquad 0\le 6<24,
\]

because \(1\cdot24+6=24+6=30\); and

\[
24=4\cdot6+0,
\qquad 0\le 0<6,
\]

because \(4\cdot6+0=24\).

Thus \(6\) is the last nonzero remainder. By the Euclidean algorithm,

\[
\gcd(84,30)=6.
\]

The required divisibility properties can also be checked directly. First,

\[
84=6\cdot14,\qquad 30=6\cdot5,
\]

so \(6\mid84\) and \(6\mid30\).

Now let \(d\in\mathbb Z\) be arbitrary and suppose \(d\mid84\) and \(d\mid30\). Since a common divisor divides every integer linear combination,

\[
24=84-2\cdot30
\]

implies \(d\mid24\). Then

\[
6=30-24
\]

implies \(d\mid6\). Therefore \(6\) divides both inputs and every common divisor of the inputs divides \(6\), confirming that \(6\) is their positive greatest common divisor.

## 2. Bézout back-substitution proof

Start with the equation producing the last nonzero remainder:

\[
6=30-24.
\]

From the preceding Euclidean division,

\[
24=84-2\cdot30.
\]

Substitution gives

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

Hence the Bézout coefficients are

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

This identity also proves the universal common-divisor property directly. If \(d\mid84\) and \(d\mid30\), then for some integers \(a,b\),

\[
84=da,\qquad 30=db.
\]

Consequently,

\[
\begin{aligned}
6
 &=84(-1)+30(3)\\
 &=(da)(-1)+(db)(3)\\
 &=d(-a+3b).
\end{aligned}
\]

Because \(-a+3b\in\mathbb Z\), it follows that \(d\mid6\). Together with

\[
84=6\cdot14,\qquad 30=6\cdot5,
\]

this independently certifies

\[
\boxed{\gcd(84,30)=6}.
\]

**Evidence inspected:** `problem.md`, `references/source.md`, and `knowledge/analytic/20260822T233912Z-7e3d4c-derive_certificate.md`. All displayed arithmetic was independently evaluated. No commands were executed; no failures, limitations, or unresolved obligations remain.
