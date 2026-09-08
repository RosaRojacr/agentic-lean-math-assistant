# Current-run certificate: counterexample-based disproof

## 1. Current applicability

The frozen claim remains:

> Every odd integer greater than `1` is prime.

Exact locator: `problem.md:3-7`.

The operative definitions remain:

- An integer \(p>1\) is prime exactly when its only positive divisors are \(1\) and \(p\).
- An integer is odd exactly when it is not divisible by \(2\).
- The claim ranges over every integer satisfying those hypotheses.

Exact locator: `references/source.md:1-3`.

These match the claim and definitions used by the latest retained certificate:  
`knowledge/arithmetic/20260823T053918Z-793a32-apply_retained_witness.md:3-26`.

The latest retained evidence is accepted and independently verified:

- Evidence artifacts and audit artifact:  
  `knowledge/arithmetic/20260823T053918Z-793a32-apply_retained_witness.json:4-15`
- Acceptance status:  
  `knowledge/arithmetic/20260823T053918Z-793a32-apply_retained_witness.json:21`
- Independent verifier `audit_retained_witness`:  
  `knowledge/arithmetic/20260823T053918Z-793a32-apply_retained_witness.json:27-29`
- Retained witness calculation and quantified consequence:  
  `knowledge/arithmetic/20260823T053918Z-793a32-apply_retained_witness.md:28-93`

Thus the current theorem and operative definitions are unchanged, and the retained witness applies directly.

## 2. Admissible witness: \(9\)

First,

\[
9\in\mathbb Z
\qquad\text{and}\qquad
9>1.
\]

For oddness,

\[
9=2\cdot4+1.
\]

Division by \(2\) therefore leaves remainder \(1\). Equivalently, if \(2\mid9\), then \(9=2k\) for some \(k\in\mathbb Z\); combined with \(9=2\cdot4+1\), this would give

\[
1=2(k-4),
\]

which is impossible for an integer \(k-4\). Hence

\[
2\nmid9.
\]

Therefore \(9\) is odd under the operative definition at `references/source.md:3`.

## 3. \(9\) is not prime

Explicitly,

\[
9=3\cdot3,
\]

so \(3\mid9\). Moreover,

\[
3>0,\qquad 3\ne1,\qquad 3\ne9.
\]

Thus \(3\) is a positive divisor of \(9\) distinct from both \(1\) and \(9\). Under the operative definition at `references/source.md:3`, \(9\) is not prime.

## 4. Universal instantiation and consequence

Let

\[
P(n)\equiv
\bigl(n\in\mathbb Z\land n>1\land 2\nmid n\bigr)
\]

and let \(Q(n)\) mean that \(n\) is prime under the operative definition.

The preceding checks establish

\[
P(9)\land\neg Q(9).
\]

The frozen universal claim would require, upon instantiation at \(n=9\),

\[
P(9)\rightarrow Q(9).
\]

Its antecedent is true and its conclusion is false. Consequently,

\[
\neg\forall n\in\mathbb Z\,
\bigl((n>1\land 2\nmid n)\rightarrow Q(n)\bigr).
\]

Therefore **“Every odd integer greater than \(1\) is prime” is false**. No valid proof of the requested universal theorem can be supplied under the frozen hypotheses.

**Classification:** counterexample-based disproof, not a successful proof of the requested theorem.

Evidence inspection used workspace reads only; no external commands or definitions were used. Failures: none. Limitation: the retained verification is an independent written audit, not a proof-assistant formalization. Unresolved obligations: none.
