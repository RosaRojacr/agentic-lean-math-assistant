# Residue-class certificate modulo \(6\)

Deterministic command:

```sh
seq 0 5 | awk '{v=$1*$1*$1-$1; printf "r=%d, r^3-r=%d, residue=%d\n", $1, v, ((v%6)+6)%6}'
```

Output:

```text
r=0, r^3-r=0, residue=0
r=1, r^3-r=0, residue=0
r=2, r^3-r=6, residue=0
r=3, r^3-r=24, residue=0
r=4, r^3-r=60, residue=0
r=5, r^3-r=120, residue=0
```

| \(r\) | \(r^3-r\) | \((r^3-r)\bmod 6\) |
|---:|---:|---:|
| 0 | 0 | 0 |
| 1 | 0 | 0 |
| 2 | 6 | 0 |
| 3 | 24 | 0 |
| 4 | 60 | 0 |
| 5 | 120 | 0 |

All six residues are zero. No counterexample occurs.

For any integer \(n\), including \(0\) and negative integers, Euclidean division by the positive integer \(6\) gives integers \(q,r\) with

\[
n=6q+r,\qquad 0\le r<6.
\]

Thus \(r\in\{0,1,2,3,4,5\}\) and \(n\equiv r\pmod 6\). This residue is unique: if also \(n=6q'+r'\) with \(0\le r'<6\), then

\[
r-r'=6(q'-q).
\]

Since \(-5\le r-r'\le5\), the only possible multiple of \(6\) is \(0\); hence \(r=r'\).

Now \(n-r=6k\) for some integer \(k\). Therefore

\[
n^3-r^3=(n-r)(n^2+nr+r^2)
       =6k(n^2+nr+r^2),
\]

so \(n^3\equiv r^3\pmod 6\). Together with \(n\equiv r\pmod 6\), subtraction gives

\[
n^3-n\equiv r^3-r\pmod 6.
\]

The table proves \(r^3-r\equiv0\pmod6\) for every possible canonical residue \(r\). Consequently,

\[
\boxed{6\mid n^3-n}
\]

for every integer \(n\), including zero and all negative integers.

Certificate saved to:

```text
agents/computational/check_residue_classes/certificate.md
```

This check is independent of the consecutive-factor proof. No failures or unresolved stage obligations remain.
