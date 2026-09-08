# Campaign certificate: adjudication of the universal primality claim

## Requested claim

> **Every odd integer greater than `1` is prime.**

This is the unchanged campaign goal stated at `problem.md:3-7`.

## Certified counterexample

Take \(9\).

1. **Integer and greater than \(1\).**  
   \(9\in\mathbb Z\), and \(9>1\).

2. **Odd under the retained definition.**  
   The retained definition says that an integer is odd exactly when it is not divisible by \(2\) (`references/source.md:3`).

   We have
   \[
   9=2\cdot4+1.
   \]
   If \(2\mid9\), there would be an integer \(k\) such that \(9=2k\). But Euclidean division of \(9\) by \(2\) has quotient \(4\) and remainder \(1\); uniqueness of quotient and remainder precludes a representation with remainder \(0\). Therefore \(2\nmid9\), so \(9\) is odd.

3. **Not prime under the retained definition.**  
   The retained definition says that \(p>1\) is prime exactly when its only positive divisors are \(1\) and \(p\) (`references/source.md:3`).

   Now
   \[
   9=3\cdot3.
   \]
   Thus \(3\mid9\). Moreover,
   \[
   3>0,\qquad 3\ne1,\qquad 3\ne9.
   \]
   Hence \(9\) has a positive divisor distinct from both \(1\) and \(9\). Therefore \(9\) is not prime.

## Adjudication

The integer \(9\) satisfies every hypothesis of the requested theorem—it is an odd integer greater than \(1\)—but fails its conclusion because it is not prime. A universally quantified statement is false when one admissible instance has a false conclusion. Therefore:

\[
\boxed{\text{“Every odd integer greater than \(1\) is prime” is false.}}
\]

Consequently, no valid proof of the theorem can be supplied under the unchanged hypotheses and retained definitions. This counterexample is a disproof, **not** a successful proof of the requested universal claim.

## Retained artifact locators

- Current theorem and campaign constraint: `problem.md:1-7`
- Retained definitions of prime and odd: `references/source.md:1-3`
- Accepted counterexample certificate:
  `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.md:1-13`
- Accepted metadata, including limitations:
  `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.json:1-30`
- Acceptance status, strategy, and retained summary:
  `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.json:21-29`

Evidence was inspected through workspace reads; no external commands were run. Failures: none. Unresolved obligations: none. The retained metadata notes that the arithmetic checks are deterministic while the parity and universal-quantifier conclusions use the written arguments above, and that the result is audited but not proof-assistant formalized (`knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.json:12-15`).
