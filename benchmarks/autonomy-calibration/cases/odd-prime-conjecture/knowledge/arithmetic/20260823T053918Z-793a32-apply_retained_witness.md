# Counterexample-based disproof

## Current applicability and retained status

The frozen theorem is unchanged:

> Every odd integer greater than \(1\) is prime.

Locator: `problem.md:3-7`.

The operative definitions are also unchanged:

- \(p>1\) is prime exactly when its only positive divisors are \(1\) and \(p\).
- An integer is odd exactly when it is not divisible by \(2\).
- The theorem ranges over every integer satisfying its hypotheses.

Locator: `references/source.md:1-3`.

The retained evidence is accepted and independently verified:

- Counterexample certificate: status `accepted` at `knowledge/arithmetic/20260823T004744Z-eb4e4b-certify_counterexample.json:21-29`; independent audit evidence and limitation recorded at lines `4-15`, with `verified_by: audit_counterexample` at lines `27-29`.
- Claim adjudication: status `accepted` at `knowledge/arithmetic/20260823T015635Z-1e574b-adjudicate_claim.json:21-29`; independent audit evidence and limitation recorded at lines `4-15`, with `verified_by: audit_adjudication` at lines `27-29`.
- Current-applicability certificate: status `accepted` at `knowledge/arithmetic/20260823T023612Z-a9f76f-apply_retained_certificate.json:20-28`; its independent applicability audit is recorded at lines `4-14`, with `verified_by: audit_current_applicability` at lines `26-28`.

Thus the accepted witness has been checked against this exact frozen theorem and these exact operative definitions.

## Self-contained certificate for \(9\)

### 1. Integer and greater than \(1\)

\[
9\in\mathbb Z,\qquad 9>1.
\]

### 2. Oddness

Explicitly,

\[
9=2\cdot4+1.
\]

This is Euclidean division by \(2\), with quotient \(4\) and remainder \(1\). If \(2\mid9\), some \(k\in\mathbb Z\) would satisfy \(9=2k\), giving remainder \(0\). Uniqueness of Euclidean division excludes that possibility. Hence

\[
2\nmid9,
\]

so \(9\) is odd under `references/source.md:3`.

### 3. Non-primality

Explicitly,

\[
9=3\cdot3.
\]

Therefore \(3\mid9\). Moreover,

\[
3>0,\qquad 3\ne1,\qquad 3\ne9.
\]

Thus \(3\) is a positive divisor of \(9\) distinct from both permitted divisors \(1\) and \(9\). Under the operative definition, \(9\) is not prime.

## Universal consequence

Let

\[
P(n)\equiv n\in\mathbb Z\land n>1\land 2\nmid n,
\qquad
Q(n)\equiv n\text{ is prime}.
\]

The certificate establishes

\[
P(9)\land\neg Q(9).
\]

Instantiating the claimed universal quantifier at \(n=9\) would require \(P(9)\to Q(9)\), but its antecedent is true and its conclusion is false. Therefore

\[
\neg\forall n\in\mathbb Z\,
\bigl((n>1\land 2\nmid n)\rightarrow Q(n)\bigr).
\]

Hence **“Every odd integer greater than \(1\) is prime” is false**, and no valid proof of that theorem can be supplied under the frozen hypotheses.

This is a **counterexample-based disproof**, not a successful proof of the requested universal theorem.

Evidence inspection used workspace reads only; no external commands or publications were used. Failures: none. Limitation: the retained audits are written and independently verified but not proof-assistant formalizations. Unresolved arithmetic or semantic obligations: none.
