# CMV Ball-Density Isoperimetry

## Problem

Resolve Question 2 of Cañete–Miranda–Vittone for the planar ball density

\[
f(x)=\begin{cases}
\lambda,&x\in \overline{B(0,1)},\\
1,&x\notin \overline{B(0,1)},
\end{cases}
\qquad 0<\lambda<1.
\]

Theorem 3.23 gives thresholds \(v_1,v_2>\lambda\pi\) and leaves open whether \(v_1=v_2\). Prove that the comparison between candidates (B) and (C) has a single transition: once a type-(C) orthogonal ball is no worse than the equal-area type-(B) two-arc candidate, type (B) never becomes optimal again at any larger weighted area.

## Source candidates

Use Proposition 3.22 and Theorem 3.23 of `references/Canete2010.pdf` as claims to audit, not as unformalized axioms.

- Type (A): balls entirely contained in the unit ball.
- Type (B): a region bounded by an arc of the unit circle and an exterior circular arc meeting it at angle \(\arccos\lambda\).
- Type (C): balls meeting the unit ball orthogonally.

For type (B), the paper uses

\[
0\le\beta\le\pi-\arccos\lambda,\qquad
\alpha=\beta+\arccos\lambda,\qquad
r=\frac{\sin\alpha}{\sin\beta},
\]

with

\[
P_B=2\bigl((\pi-\beta)r+\lambda\alpha\bigr),
\]

\[
A_B=r^2(\pi-\beta+\sin\beta\cos\beta)
 +(\alpha-\sin\alpha\cos\alpha)-(1-\lambda)\pi.
\]

For type (C), with \(0<\widehat\beta<\pi/2\) and \(\widehat r=1/\tan\widehat\beta\), the paper gives

\[
P_C=\frac{2\bigl(\pi-(1-\lambda)\widehat\beta\bigr)}
 {\tan\widehat\beta},
\]

\[
A_C=
\frac{\pi-(1-\lambda)(\widehat\beta-
 \sin\widehat\beta\cos\widehat\beta)}{\tan^2\widehat\beta}
-(1-\lambda)\left(\frac\pi2-\widehat\beta-
 \sin\widehat\beta\cos\widehat\beta\right).
\]

Audit every formula, orientation, endpoint, and parameter domain against printed pages 33–36 before using it.

## Required work

1. Reconstruct the weighted areas and perimeters of types (B) and (C) directly from the geometry and Snell law.
2. Prove the relevant area maps have the monotonicity and range needed to define equal-area perimeter profiles without selecting an arbitrary numerical branch.
3. Search for counterexamples and multiple crossings over the complete domain \(0<\lambda<1\), especially as \(\lambda\to0^+\), \(\lambda\to1^-\), \(v\downarrow\lambda\pi\), and \(v\to\infty\).
4. Derive a rigorous single-crossing mechanism—analytic monotonicity, an exact change of variables, a validated differential inequality, or a complete exact certificate.
5. Connect the profile comparison to the actual type-(B)/(C) candidates and Theorem 3.23's classification. Do not stop at detached scalar formulas.
6. Formalize the decisive argument in Lean with explicit parameter domains and equal-area quantification.

## Formal target

Produce `CMVBallCase.lean` defining mathematically faithful equal-area profiles `typeBPerimeterAtArea` and `typeCPerimeterAtArea`, and prove

```lean
CMVBallCase.typeC_dominance_persists
```

with exactly this observable type:

```lean
∀ {lam v₀ v : ℝ},
  0 < lam → lam < 1 → lam * Real.pi < v₀ → v₀ < v →
  typeCPerimeterAtArea lam v₀ ≤ typeBPerimeterAtArea lam v₀ →
  typeCPerimeterAtArea lam v < typeBPerimeterAtArea lam v
```

The profile definitions must be derived from all admissible equal-area candidates and must not encode the desired ordering, choose a favorable branch, or use a default value that makes the theorem vacuous.

## Completion criteria

1. `lake build` succeeds from the retained `proof/` project.
2. The exact target declaration has only `propext`, `Quot.sound`, and `Classical.choice`, or a strict subset, in `#print axioms`.
3. No target dependency contains `sorry`, `admit`, a project axiom, `native_decide`, or an unchecked numerical oracle.
4. An independent semantic audit verifies the formulas, parameter domains, equal-area quantifiers, existence and uniqueness claims, endpoint behavior, and the implication for \(v_1=v_2\).
5. Any computational certificate is regenerated independently and connected to real inequalities by kernel-checked soundness theorems.
6. The final report distinguishes the analytic profile theorem from any still-unformalized finite-perimeter classification or regularity premise.

## Evidence rules

- Primary-source claims require a printed page, theorem, proposition, equation, figure, or remark locator.
- Computed claims require retained code, parameters, precision, command, and output.
- Formal claims require exact declarations and successful clean Lean checks.
- Numerical plots, sampled monotonicity, optimizer trajectories, agent agreement, and process exit codes are not proofs.
- A counterexample is an acceptable resolution only if it is rigorously enclosed and translated back to admissible equal-area candidates.
