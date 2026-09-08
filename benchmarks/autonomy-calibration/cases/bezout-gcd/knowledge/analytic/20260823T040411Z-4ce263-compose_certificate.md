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

All three equations are valid:

\[
2\cdot30+24=84,\qquad
1\cdot24+6=30,\qquad
4\cdot6+0=24.
\]

The first zero remainder occurs after \(6\), so \(6\) is the last nonzero remainder. Therefore, by the Euclidean algorithm,

\[
\boxed{\gcd(84,30)=6}.
\]

The candidate \(6\) divides both inputs, with explicit integer quotients:

\[
84=6\cdot14,\qquad 30=6\cdot5.
\]

Thus \(6\mid84\) and \(6\mid30\).

Now let \(d\in\mathbb Z\) be any common divisor of \(84\) and \(30\). Then \(d\mid84\) and \(d\mid30\). From the remainder equations,

\[
24=84-2\cdot30,
\]

so \(d\mid24\). Then

\[
6=30-24,
\]

so \(d\mid6\). Hence every integer common divisor of \(84\) and \(30\) divides \(6\). Since \(6>0\), this confirms that the positive greatest common divisor is \(6\).

## 2. Bézout back-substitution proof

Begin with

\[
6=30-24
\]

and use the preceding remainder equation

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

Therefore the explicit Bézout coefficients are

\[
\boxed{u=-1,\qquad v=3}.
\]

The numerical check is

\[
84(-1)+30(3)=-84+90=6.
\]

This identity also directly proves the universal common-divisor condition. If \(d\mid84\) and \(d\mid30\), then there are integers \(a,b\) such that

\[
84=da,\qquad 30=db.
\]

Consequently,

\[
6=84(-1)+30(3)
  =(da)(-1)+(db)(3)
  =d(-a+3b).
\]

Because \(-a+3b\in\mathbb Z\), it follows that \(d\mid6\). Together with

\[
84=6\cdot14,\qquad 30=6\cdot5,
\]

this proves again that

\[
\boxed{\gcd(84,30)=6}.
\]

**Retained source artifacts consulted:**

- `problem.md`
- `knowledge/analytic/20260823T032529Z-fa6c18-compose_certificate.md`
- `knowledge/analytic/20260823T030622Z-f26548-compose_certificate.md`
- `knowledge/analytic/20260822T233912Z-7e3d4c-derive_certificate.md`

**Commands executed:** none; the listed workspace artifacts were inspected using harness file reads.

**Failures, limitations, and unresolved obligations:** none.
