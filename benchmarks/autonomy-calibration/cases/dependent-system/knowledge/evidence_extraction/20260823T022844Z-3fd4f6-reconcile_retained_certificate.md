# Retained-certificate reconciliation

**Source scope.** `problem.md:3-9` states that \(x,y\in\mathbb R\) satisfy only

\[
x+y=4,\qquad 2x+2y=8,
\]

and prohibits auxiliary sign, integrality, ordering, optimization, or normalization conditions. `references/source.md:3` confirms the real domain, completeness of these constraints, and absence of those assumptions. This matches the retained analyses at:

- `knowledge/analytic/20260823T004123Z-703163-derive_system_result.md:3-9,25-37,51`
- `knowledge/analytic/20260823T011347Z-32bf4e-produce_exact_answer.md:1-35,46`
- `knowledge/analytic/20260823T015022Z-31c929-convert_retained_certificate.md:3-55`

**Independence check.**

\[
(2,2\mid 8)=2(1,1\mid 4).
\]

Thus the second augmented row is exactly twice the first; the equations are not independent.

**Exact witnesses.**

For \((x,y)=(0,4)\):

\[
0+4=4,\qquad 2(0)+2(4)=8,\qquad x-y=0-4=-4.
\]

For \((x,y)=(1,3)\):

\[
1+3=4,\qquad 2(1)+2(3)=8,\qquad x-y=1-3=-2.
\]

Both pairs satisfy both original equations, while \(-4\ne-2\). Therefore the equations alone do **not** entail one exact numerical value for \(x-y\); supplying one would invent an auxiliary condition.

**Execution record.** No shell commands, publication research, or auxiliary assumptions used. Exact row comparison and substitution completed; no failures, limitations, or unresolved obligations.
