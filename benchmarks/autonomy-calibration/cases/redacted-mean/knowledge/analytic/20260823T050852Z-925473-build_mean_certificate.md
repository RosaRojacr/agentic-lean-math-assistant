# Mean certificate: record R-17

The retained evidence does **not** uniquely determine a numerical arithmetic mean.

## Four-slot constraint ledger

| Ordered slot | Retained constraint | Primary locator |
|---:|---|---|
| 1 | Exactly \(4\) | `references/source.md:5` |
| 2 | Exactly \(8\) | `references/source.md:6` |
| 3 | Original value unavailable; denote it by \(x\) | `references/source.md:7` |
| 4 | Exactly \(10\) | `references/source.md:8` |

`references/source.md:3` establishes acquisition order. `references/source.md:10` states that no range, checksum, aggregate, or relationship constraining the redacted value was retained. `problem.md:3` requires all four measurements and prohibits guessing or omission.

## Exact supported mean

Using all four slots,

\[
\bar m(x)
=\frac{4+8+x+10}{4}
=\frac{22+x}{4}.
\]

Thus the retained evidence determines the conditional family

\[
\boxed{\bar m(x)=\frac{22+x}{4}},
\]

not a unique numerical mean.

## Compatible completions

For \(x=0\), the completed record is \((4,8,0,10)\):

\[
\bar m(0)
=\frac{4+8+0+10}{4}
=\frac{22}{4}
=\frac{11}{2}.
\]

For \(x=4\), the completed record is \((4,8,4,10)\):

\[
\bar m(4)
=\frac{4+8+4+10}{4}
=\frac{26}{4}
=\frac{13}{2}.
\]

Both preserve every retained value and violate no retained constraint. Their means differ:

\[
\frac{13}{2}-\frac{11}{2}=1\ne0.
\]

Therefore no unique exact numerical mean follows from the supplied record.

## Missing prerequisite

A unique answer requires **the original third measurement, or equivalent retained evidence that uniquely determines it**. If that evidence fixed \(x=c\), the unique mean would be

\[
\frac{22+c}{4}.
\]

## Verification and retained comparison

Exact `fractions.Fraction` checks verified:

- \(4+8+10=22\);
- the symbolic affine identity \((4+8+x+10)/4=(22+x)/4\);
- witness means \(11/2\) and \(13/2\);
- exact difference \(1\).

All assertions passed. The three accepted analytic records and accepted evidence-extraction record agree with this certificate; no comparison conflict was found.

Full certificate, exact executed `eval` code, outputs, evidence inventory, limitations, and execution record:

`agents/analytic/build_mean_certificate/attempt-01.md`

No external sources were used and no tool call failed. The sole unresolved fact is the original third measurement.
