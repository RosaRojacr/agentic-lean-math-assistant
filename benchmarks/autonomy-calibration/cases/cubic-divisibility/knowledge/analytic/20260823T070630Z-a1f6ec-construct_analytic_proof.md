# Consecutive-factor proof

Let \(n\in\mathbb Z\) be arbitrary and set
\[
x=n^3-n.
\]

## 1. Factorization

Expanding explicitly,
\[
\begin{aligned}
n(n-1)(n+1)
&=n\bigl((n-1)(n+1)\bigr)\\
&=n(n^2+n-n-1)\\
&=n(n^2-1)\\
&=n^3-n.
\end{aligned}
\]
Therefore
\[
x=n^3-n=n(n-1)(n+1).
\]

## 2. Divisibility by \(2\)

Euclidean division of \(n\) by \(2\) gives an integer \(k\) and a remainder \(s\in\{0,1\}\) such that \(n=2k+s\).

- If \(s=0\), then \(n=2k\), so
  \[
  x=(n-1)(2k)(n+1)
   =2\bigl(k(n-1)(n+1)\bigr).
  \]
  The quantity \(k(n-1)(n+1)\) is an integer quotient witness.

- If \(s=1\), then \(n=2k+1\), hence \(n-1=2k\), so
  \[
  x=(2k)n(n+1)
   =2\bigl(kn(n+1)\bigr).
  \]
  The quantity \(kn(n+1)\) is an integer quotient witness.

Thus in every case there is an \(a\in\mathbb Z\) such that
\[
x=2a.
\]
Hence \(2\mid x\).

## 3. Divisibility by \(3\)

Euclidean division of \(n\) by \(3\) gives an integer \(k\) and a remainder \(s\in\{0,1,2\}\) such that \(n=3k+s\).

- If \(s=0\), then \(n=3k\), and
  \[
  x=(n-1)(3k)(n+1)
   =3\bigl(k(n-1)(n+1)\bigr).
  \]

- If \(s=1\), then \(n-1=3k\), and
  \[
  x=(3k)n(n+1)
   =3\bigl(kn(n+1)\bigr).
  \]

- If \(s=2\), then \(n+1=3(k+1)\), and
  \[
  x=(n-1)n\,3(k+1)
   =3\bigl((k+1)(n-1)n\bigr).
  \]

Every expression in parentheses is an integer. Therefore there is a \(b\in\mathbb Z\) such that
\[
x=3b.
\]
Hence \(3\mid x\).

## 4. Recombination into divisibility by \(6\)

We have integers \(a,b\) satisfying
\[
x=2a=3b.
\]
The coprimality of \(2\) and \(3\) is explicitly witnessed by the Bézout identity
\[
1=3-2.
\]
Multiplying by \(a\) and substituting \(2a=x=3b\) gives
\[
\begin{aligned}
a
&=3a-2a\\
&=3a-x\\
&=3a-3b\\
&=3(a-b).
\end{aligned}
\]
Thus \(a\) is divisible by \(3\), with explicit integer quotient
\[
c=a-b\in\mathbb Z.
\]
Consequently,
\[
x=2a=2\bigl(3(a-b)\bigr)=6(a-b)=6c.
\]
Therefore
\[
\boxed{6\mid n^3-n}.
\]

This calculation explicitly explains the recombination: simultaneous divisibility by \(2\) and \(3\), together with the Bézout identity \(1=3-2\), produces the integer quotient \(a-b\) for division by \(6\).

## 5. Zero and negative integers

The argument applies to an arbitrary \(n\in\mathbb Z\). Euclidean division by each positive divisor \(2\), \(3\), and \(6\) is valid for negative integers as well as nonnegative integers: the quotient may be negative, while the remainder remains in the prescribed set.

All quotient witnesses above are sums, differences, or products of integers, so they remain integers when \(n<0\). No step assumes positivity.

Zero is also included:
\[
0^3-0=0=6\cdot0.
\]
Hence the result holds for every integer, including zero and all negative integers.

---

# Independent residue-class check modulo \(6\)

This check does not use the consecutive-factor proof.

For arbitrary \(n\in\mathbb Z\), Euclidean division by \(6\) supplies \(q\in\mathbb Z\) and
\[
r\in\{0,1,2,3,4,5\}
\]
such that
\[
n=6q+r.
\]
In particular, \(n-r=6q\). Using the difference-of-cubes identity,
\[
n^3-r^3=(n-r)(n^2+nr+r^2)
       =6q(n^2+nr+r^2).
\]
Therefore
\[
\begin{aligned}
(n^3-n)-(r^3-r)
&=(n^3-r^3)-(n-r)\\
&=6q(n^2+nr+r^2)-6q\\
&=6q(n^2+nr+r^2-1).
\end{aligned}
\]
The final expression is explicitly divisible by \(6\), so
\[
n^3-n\equiv r^3-r\pmod 6.
\]

Checking all six representatives gives:

| \(r\) | \(r^3-r\) | Explicit multiple of \(6\) |
|---:|---:|---:|
| \(0\) | \(0\) | \(6\cdot0\) |
| \(1\) | \(0\) | \(6\cdot0\) |
| \(2\) | \(6\) | \(6\cdot1\) |
| \(3\) | \(24\) | \(6\cdot4\) |
| \(4\) | \(60\) | \(6\cdot10\) |
| \(5\) | \(120\) | \(6\cdot20\) |

Thus for each possible \(r\), there is an integer \(t_r\) with
\[
r^3-r=6t_r.
\]
Combining this with the transfer calculation yields the explicit equation
\[
n^3-n
=6\left(q(n^2+nr+r^2-1)+t_r\right).
\]
The expression in parentheses is an integer, including when \(n\) and \(q\) are negative. Hence this independent check also proves
\[
\boxed{6\mid n^3-n\quad\text{for every }n\in\mathbb Z}.
\]

## Retained artifact locators

Retained accepted analytic artifacts used:

1. `knowledge/analytic/20260823T041540Z-425127-synthesize_proof.md`  
   Sections **Factorization**, **Divisibility by \(2\)**, **Divisibility by \(3\)**, **Recombination into divisibility by \(6\)**, **Zero and negative integers**, and **Independent residue-class certificate modulo \(6\)**.

2. `knowledge/analytic/20260822T234941Z-5c8f19-derive_consecutive_proof.md`  
   Sections **Factorization**, **Divisibility by \(2\)**, **Divisibility by \(3\)**, **Explicit recombination into divisibility by \(6\)**, **Coverage of zero and negative integers**, and **Independent residue-class check modulo \(6\)**.

Evidence inspected through workspace reads. Commands executed: none. Failures: none. Limitation: elementary analytic proof rather than a proof-assistant kernel certificate. Unresolved obligations: none.
