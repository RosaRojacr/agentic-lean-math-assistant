# GCD and Bézout certificate

\[
\boxed{\gcd(84,30)=6}
\]

## 1. Euclidean-algorithm proof

The complete remainder chain is

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

Indeed,

\[
2\cdot30+24=84,\qquad
1\cdot24+6=30,\qquad
4\cdot6+0=24.
\]

The algorithm terminates with remainder \(0\), and the last nonzero remainder is \(6\). Therefore,

\[
\boxed{\gcd(84,30)=6}.
\]

The claimed gcd divides both inputs, since

\[
84=6\cdot14,\qquad 30=6\cdot5.
\]

Thus \(6\mid84\) and \(6\mid30\).

To verify the universal common-divisor condition, let \(d\in\mathbb Z\) satisfy

\[
d\mid84\qquad\text{and}\qquad d\mid30.
\]

A divisor of two integers divides every integer linear combination of them. Hence, from

\[
24=84-2\cdot30,
\]

we obtain \(d\mid24\). Then, from

\[
6=30-24,
\]

we obtain \(d\mid6\). Thus every common divisor of \(84\) and \(30\) divides \(6\). Since \(6>0\) and divides both inputs, it is their positive greatest common divisor.

## 2. Bézout back-substitution proof

Starting with the second remainder equation,

\[
6=30-24,
\]

and using

\[
24=84-2\cdot30,
\]

back-substitution gives

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

Therefore the Bézout coefficients are

\[
\boxed{u=-1,\qquad v=3}.
\]

The numerical verification is

\[
84(-1)+30(3)=-84+90=6.
\]

This identity also verifies the common-divisor condition directly. If \(d\mid84\) and \(d\mid30\), write \(84=da\) and \(30=db\) for integers \(a,b\). Then

\[
6=84(-1)+30(3)
  =(da)(-1)+(db)(3)
  =d(-a+3b),
\]

where \(-a+3b\in\mathbb Z\). Therefore \(d\mid6\).

Consequently,

\[
\boxed{\gcd(84,30)=6,\qquad u=-1,\qquad v=3}.
\]

**Evidence consulted:** `problem.md`, `knowledge/analytic/20260823T040411Z-4ce263-compose_certificate.md`, and its accepted JSON metadata.

**Commands executed:** none; files were inspected through workspace reads.

**Failures, limitations, and unresolved obligations:** none.
