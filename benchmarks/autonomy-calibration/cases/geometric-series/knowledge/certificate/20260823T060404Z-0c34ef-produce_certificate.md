Completed the self-contained certificate:

`agents/certificate/produce_certificate/certificate.md`

It includes:

- Definition of \(S_m=1+r+\cdots+r^{m-1}\) for positive integer \(m\).
- Explicit display of \(rS_m\).
- Endpoint-preserving subtraction and cancellation yielding
  \[
  (r-1)S_m=r^m-1.
  \]
- The hypothesis \(r\ne1\) before division by \(r-1\).
- Exact specialization:
  \[
  3\frac{2^8-1}{2-1}=3\cdot255=765.
  \]
- A separate independent check listing
  \[
  3,6,12,24,48,96,192,384
  \]
  and cumulative exact additions ending at \(765\).
- Retained source, pilot/reconciliation, and continue-gate evidence locators.

Verification used the current-run exact-integer transcript at:

`agents/verification/reconcile_dual_routes/exact-integer-transcript.txt`

Recorded command:

```text
python3 -c "import json; terms = [3 * (2 ** k) for k in range(8)]; print('terms=' + json.dumps(terms, separators=(',', ':'))); print('sum=' + str(sum(terms)))"
```

Recorded result:

```text
terms=[3,6,12,24,48,96,192,384]
sum=765
exit_code=0
stderr=<empty>
```

Failures or unresolved obligations: none. No decimal approximation was used.
