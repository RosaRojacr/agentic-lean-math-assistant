Created the self-contained certificate:

`agents/certificate/produce_certificate/certificate.md`

It contains:

- First-principles derivation of  
  \[
  \sum_{k=0}^{m-1}r^k=\frac{r^m-1}{r-1}
  \]
  for positive integer \(m\) and \(r\ne1\), including multiplication by \(r\), endpoint-visible subtraction, cancellation, and justification for division.
- Exact specialization with \(m=8\), \(r=2\), and coefficient \(3\):
  \[
  3\left(\frac{2^8-1}{2-1}\right)=3(256-1)=765.
  \]
- An independent check, explicitly not using the closed form, listing all eight terms and cumulative exact additions ending at \(765\).
- No decimal approximations or historical-path dependencies.

Commands executed: none; the artifact was written directly through the workspace file tool.

Failures, limitations, or unresolved obligations: none.
