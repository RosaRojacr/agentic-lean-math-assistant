## Result

The requested universal statement is **false as written**. The exact mixed-sign witness is

\[
(a,b,c,d)=(0,1,1,-1).
\]

- \(b=1\ne0\)
- \(d=-1\ne0\)
- \(b>0\), \(d<0\), and \(bd=-1<0\)
- \(\frac ab=\frac01=0\)
- \(\frac cd=\frac1{-1}=-1\)
- Therefore \(\frac ab>\frac cd\) is true
- \(ad=0(-1)=0\)
- \(bc=1(1)=1\)
- Therefore \(ad>bc\) is false

Thus all hypotheses and the antecedent hold, but the conclusion fails. No universal proof can be reported as successful.

Artifacts:

- `agents/computational/verify_exact_counterexample/attempt-01.md`
- `agents/computational/verify_exact_counterexample/verify.py`
- `agents/computational/verify_exact_counterexample/certificate.json`
- `agents/computational/verify_exact_counterexample/certificate-output.txt`

Verification command:

```sh
python agents/computational/verify_exact_counterexample/verify.py
```

Exact `fractions.Fraction` assertions passed, ending with `exact certificate verified`. A fresh run also matched the saved machine-readable certificate.
