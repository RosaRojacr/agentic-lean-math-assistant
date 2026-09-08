Completed the independently recomputed modulo-6 certificate:

`agents/computational/check_residue_certificate/attempt-01.md`

Evidence:

- Checked all six residues:
  \[
  (r,r^3-r,(r^3-r)/6)=(0,0,0),(1,0,0),(2,6,1),(3,24,4),(4,60,10),(5,120,20).
  \]
- Computation exited `0` with empty standard error.
- Proved Euclidean division for every \(n\in\mathbb Z\), including negative integers, using \(q=\lfloor n/6\rfloor\) and \(r=n-6q\).
- Established algebraically:
  \[
  (n^3-n)-(r^3-r)
  =6q(36q^2+18qr+3r^2-1).
  \]
- Supplied an explicit quotient witness for \(n^3-n\).
- Reconciled exactly with retained artifact:
  `knowledge/computational/20260822T234941Z-5c8f19-check_residue_classes.md`
- No failures or unresolved stage obligations.
