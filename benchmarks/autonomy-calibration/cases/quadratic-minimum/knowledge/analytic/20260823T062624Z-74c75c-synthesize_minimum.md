Let \(x\in\mathbb R\). Completing the square gives

\[
\begin{aligned}
f(x)
&=x^2-6x+13\\
&=x^2-6x+9+4\\
&=(x-3)^2+4.
\end{aligned}
\]

Expanding the completed-square form verifies the identity exactly:

\[
(x-3)^2+4
=x^2-6x+9+4
=x^2-6x+13.
\]

Because \(x-3\in\mathbb R\), real-square nonnegativity gives

\[
(x-3)^2\ge 0.
\]

Hence, for every \(x\in\mathbb R\),

\[
f(x)=(x-3)^2+4\ge 4.
\]

Thus \(4\) is a global lower bound. It is attained, as direct substitution shows:

\[
f(3)=3^2-6(3)+13=9-18+13=4.
\]

Therefore \(4\) is the global minimum. The equality case is exhaustive: for every real \(x\),

\[
\begin{aligned}
f(x)=4
&\iff (x-3)^2+4=4\\
&\iff (x-3)^2=0\\
&\iff x-3=0\\
&\iff x=3.
\end{aligned}
\]

The reverse direction is also confirmed directly by \(f(3)=4\). Consequently,

\[
\boxed{\min_{x\in\mathbb R} f(x)=4}
\qquad\text{and}\qquad
\boxed{\{x\in\mathbb R:f(x)=4\}=\{3\}}.
\]

**Evidence:** Read `problem.md`, `knowledge/analytic/20260823T041027Z-0cf247-derive_minimum.md`, and its metadata file `knowledge/analytic/20260823T041027Z-0cf247-derive_minimum.json`. The metadata marks the retained proof as accepted and independently audited. No calculus, graphing, numerical sampling, external research, or shell commands were used. No failures or unresolved obligations remain.
