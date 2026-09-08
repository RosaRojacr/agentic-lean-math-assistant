# Current-run counterexample applicability certificate

## Applicability

The current claim remains exactly:

> Every odd integer greater than \(1\) is prime.

See `problem.md:3-7`. The operative definitions remain unchanged: odd means not divisible by \(2\), and a prime \(p>1\) has only \(1\) and \(p\) as positive divisors (`references/source.md:1-3`).

The retained counterexample certificate and adjudication both have status `accepted`:

- `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.json:21-29`
- `knowledge/arithmetic/20260823T015635Z-1e574b-adjudicate_claim.json:19-27`

Therefore the retained witness \(9\) applies directly to the current, unchanged claim and definitions.

## 1. Admissibility of \(9\)

- \(9\in\mathbb Z\).
- \(9>1\).
- Explicitly,
  \[
  9=2\cdot4+1=8+1.
  \]
  Euclidean division of \(9\) by \(2\) thus has quotient \(4\) and remainder \(1\). By uniqueness of Euclidean quotient and remainder, there is no integer \(k\) for which \(9=2k\), since that would give remainder \(0\). Hence
  \[
  2\nmid9.
  \]
  Under the operative definition, \(9\) is odd.

Retained evidence: `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.md:3-5` and `knowledge/arithmetic/20260823T015635Z-1e574b-adjudicate_claim.md:11-24`.

## 2. Non-primality of \(9\)

Explicitly,
\[
9=3\cdot3.
\]
Therefore \(3\mid9\). Moreover,
\[
3>0,\qquad 3\ne1,\qquad 3\ne9.
\]
Thus \(9\) has a positive divisor distinct from both \(1\) and \(9\). Under the operative prime definition, \(9\) is not prime.

Retained evidence: `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.md:6-8` and `knowledge/arithmetic/20260823T015635Z-1e574b-adjudicate_claim.md:26-38`.

## 3. Quantified consequence

Let
\[
P(n)\equiv(n\in\mathbb Z\land n>1\land 2\nmid n),\qquad
Q(n)\equiv n\text{ is prime}.
\]
The calculations establish \(P(9)\land\neg Q(9)\). Therefore
\[
\neg\forall n\in\mathbb Z\,
\bigl((n>1\land 2\nmid n)\rightarrow Q(n)\bigr).
\]

Hence **“Every odd integer greater than \(1\) is prime” is false**. No valid proof of that universal theorem can be supplied under the unchanged hypotheses and definitions. This certificate is a **disproof by counterexample**, not a successful proof of the requested theorem.

Accepted adjudication: `knowledge/arithmetic/20260823T015635Z-1e574b-adjudicate_claim.md:40-49`.

Evidence was inspected through workspace reads. External commands: none. Failures: none. Unresolved arithmetic or semantic obligations: none.
