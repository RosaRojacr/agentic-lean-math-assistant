Counterexample:  
\[
(a,b,c,d)=(0,1,1,-1).
\]

Exact substitution certificate:

1. \(b=1\neq 0\).
2. \(d=-1\neq 0\).
3. The denominator signs are mixed: \(b=1>0\), while \(d=-1<0\).
4. \[
   \frac ab=\frac01=0,\qquad \frac cd=\frac1{-1}=-1,
   \]
   so \(\frac ab>\frac cd\) because \(0>-1\).
5. \[
   ad=0(-1)=0,\qquad bc=1(1)=1,
   \]
   so \(ad>bc\) is false because \(0\not>1\).

Thus every premise and the strict antecedent hold, while the conclusion fails. The universal statement is false as written; no valid universal proof exists without additional sign hypotheses.

Verified using Python `fractions.Fraction` exact arithmetic with assertions; output ended with `exact certificate verified`. No floating-point arithmetic was used.

Recorded at `agents/computational/construct_counterexample/certificate.json`. No failures, limitations, or unresolved obligations.
