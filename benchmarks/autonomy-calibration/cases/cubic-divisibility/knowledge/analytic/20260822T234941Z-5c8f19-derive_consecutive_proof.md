# Consecutive-factor proof

Let \(n\in\mathbb Z\) be arbitrary, and set
\[
x=n^3-n.
\]

## 1. Factorization

Expanding gives
\[
\begin{aligned}
n(n-1)(n+1)
&=n\bigl((n-1)(n+1)\bigr)\\
&=n(n^2+n-n-1)\\
&=n(n^2-1)\\
&=n^3-n.
\end{aligned}
\]
Thus
\[
x=(n-1)n(n+1).
\]

## 2. Divisibility by \(2\)

The integers \(n-1\) and \(n\) are consecutive. Hence one is even.

- If \(n=2k\) for some \(k\in\mathbb Z\), then
  \[
  x=(n-1)(2k)(n+1)
   =2\bigl(k(n-1)(n+1)\bigr),
  \]
  so \(2\mid x\).

- If \(n-1=2k\) for some \(k\in\mathbb Z\), then
  \[
  x=(2k)n(n+1)
   =2\bigl(kn(n+1)\bigr),
  \]
  so again \(2\mid x\).

Therefore \(2\mid n^3-n\).

## 3. Divisibility by \(3\)

The factors \(n-1,n,n+1\) are three consecutive integers. Hence one is divisible by \(3\).

- If \(n-1=3k\), then
  \[
  x=3\bigl(kn(n+1)\bigr).
  \]
- If \(n=3k\), then
  \[
  x=3\bigl(k(n-1)(n+1)\bigr).
  \]
- If \(n+1=3k\), then
  \[
  x=3\bigl(k(n-1)n\bigr).
  \]

In every case the expression in parentheses is an integer. Therefore
\[
3\mid n^3-n.
\]

## 4. Explicit recombination into divisibility by \(6\)

Since \(2\mid x\) and \(3\mid x\), there are integers \(a,c\) such that
\[
x=2a
\qquad\text{and}\qquad
x=3c.
\]

The coprimality of \(2\) and \(3\) is witnessed explicitly by
\[
1=3-2.
\]
Multiplying by \(a\) and using \(2a=x=3c\),
\[
a=3a-2a=3a-x=3a-3c=3(a-c).
\]
Thus \(3\mid a\). Setting \(b=a-c\in\mathbb Z\), we have \(a=3b\), and consequently
\[
x=2a=2(3b)=6b.
\]
Hence
\[
\boxed{6\mid n^3-n}.
\]

Because \(n\) was an arbitrary integer, this holds for every \(n\in\mathbb Z\).

## 5. Coverage of zero and negative integers

No step assumes \(n>0\). The source facts are stated for **integers**, and consecutive integers remain consecutive regardless of their signs. Divisibility means the existence of an integer quotient; the witnesses above remain integers when \(n\) or a factor is negative.

For \(n=0\), the argument also applies directly:
\[
0^3-0=0=6\cdot0.
\]
Thus zero and all negative integers are included.

## 6. Independent residue-class check modulo \(6\)

By the integer division algorithm, for every \(n\in\mathbb Z\)—including negative \(n\)—there exist \(q\in\mathbb Z\) and a unique
\[
r\in\{0,1,2,3,4,5\}
\]
such that \(n=6q+r\). Therefore \(n\equiv r\pmod 6\). Congruence is preserved under multiplication and subtraction, so
\[
n^3-n\equiv r^3-r\pmod 6.
\]

The six possibilities are
\[
\begin{array}{c|c}
r & r^3-r\\ \hline
0 & 0\\
1 & 0\\
2 & 6\\
3 & 24\\
4 & 60\\
5 & 120
\end{array}
\]
and every value in the right column is divisible by \(6\). Hence independently,
\[
n^3-n\equiv0\pmod6.
\]

## Retained-source evidence

Source: [`references/source.md`](references/source.md)

Exact permitted facts used:

> “Among any two consecutive integers, one is even.”

> “Among any three consecutive integers, one is divisible by `3`.”

> “The integers `2` and `3` are coprime.”

> “Standard integer factorization and divisibility rules may be used.”

Evidence inspected: `problem.md` and `references/source.md`. No shell commands were run; no failures or unresolved obligations.
