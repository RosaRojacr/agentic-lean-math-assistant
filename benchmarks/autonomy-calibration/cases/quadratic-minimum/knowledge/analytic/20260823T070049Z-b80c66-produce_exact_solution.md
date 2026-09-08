For arbitrary \(x\in\mathbb R\), complete the square:

\[
\begin{aligned}
f(x)
&=x^2-6x+13\\
&=x^2-6x+9+4\\
&=(x-3)^2+4.
\end{aligned}
\]

Expanding back verifies the identity exactly:

\[
(x-3)^2+4=x^2-6x+9+4=x^2-6x+13.
\]

Since \(x-3\in\mathbb R\), nonnegativity of real squares gives

\[
(x-3)^2\ge 0.
\]

Therefore, for every \(x\in\mathbb R\),

\[
f(x)=(x-3)^2+4\ge 4.
\]

Thus \(4\) is a global lower bound. Direct evaluation in the original polynomial proves that it is attained:

\[
f(3)=3^2-6(3)+13=9-18+13=4.
\]

The equality case identifies all attaining points. For every \(x\in\mathbb R\),

\[
\begin{aligned}
f(x)=4
&\iff (x-3)^2+4=4\\
&\iff (x-3)^2=0\\
&\iff x-3=0\\
&\iff x=3.
\end{aligned}
\]

Here \((x-3)^2=0\iff x-3=0\) uses the exact equality condition for real-square nonnegativity. The reverse direction is also directly checked above by \(f(3)=4\).

Hence

\[
\boxed{\min_{x\in\mathbb R} f(x)=4},
\qquad
\boxed{\{x\in\mathbb R:f(x)=4\}=\{3\}}.
\]

Evidence consulted: `problem.md`, `references/source.md`, `knowledge/index.json`, and `knowledge/analytic/20260823T062624Z-74c75c-synthesize_minimum.md`. No shell commands were run; no failures, limitations, or unresolved obligations remain.
