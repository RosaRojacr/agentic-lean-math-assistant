## Independent exact-arithmetic check

Evaluate each summand directly:

| \(k\) | \(3\cdot 2^k\) |
|---:|---:|
| \(0\) | \(3\cdot 1=3\) |
| \(1\) | \(3\cdot 2=6\) |
| \(2\) | \(3\cdot 4=12\) |
| \(3\) | \(3\cdot 8=24\) |
| \(4\) | \(3\cdot 16=48\) |
| \(5\) | \(3\cdot 32=96\) |
| \(6\) | \(3\cdot 64=192\) |
| \(7\) | \(3\cdot 128=384\) |

Exact cumulative sums:

\[
\begin{aligned}
3+6&=9,\\
9+12&=21,\\
21+24&=45,\\
45+48&=93,\\
93+96&=189,\\
189+192&=381,\\
381+384&=765.
\end{aligned}
\]

Hence

\[
\sum_{k=0}^{7}3\cdot 2^k
=3+6+12+24+48+96+192+384
=765.
\]

No geometric-series closed form was used. A deterministic integer computation independently returned `765`.

Evidence saved to `agents/computational/enumerate_exact_terms/exact-check.md`.
