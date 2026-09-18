import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section

namespace CMVBallCase

/-- The density parameter in CMV Question 2. -/
def AdmissibleDensity (lam : ℝ) : Prop := 0 < lam ∧ lam < 1

/-- The source angle α = β + arccos λ for a type-(B) candidate. -/
def typeBAlpha (lam beta : ℝ) : ℝ := beta + Real.arccos lam

/-- The exterior-circle radius for a type-(B) candidate. -/
def typeBRadius (lam beta : ℝ) : ℝ :=
  Real.sin (typeBAlpha lam beta) / Real.sin beta

/-- CMV's weighted perimeter formula for a type-(B) candidate. -/
def typeBPerimeter (lam beta : ℝ) : ℝ :=
  2 * ((Real.pi - beta) * typeBRadius lam beta + lam * typeBAlpha lam beta)

/-- CMV's weighted area formula for a type-(B) candidate. -/
def typeBArea (lam beta : ℝ) : ℝ :=
  (typeBRadius lam beta) ^ 2 *
      (Real.pi - beta + Real.sin beta * Real.cos beta) +
    (typeBAlpha lam beta -
      Real.sin (typeBAlpha lam beta) * Real.cos (typeBAlpha lam beta)) -
    (1 - lam) * Real.pi

/-- The orthogonal-ball radius for a type-(C) candidate. -/
def typeCRadius (beta : ℝ) : ℝ := 1 / Real.tan beta

/-- CMV's weighted perimeter formula for a type-(C) candidate. -/
def typeCPerimeter (lam beta : ℝ) : ℝ :=
  2 * (Real.pi - (1 - lam) * beta) / Real.tan beta

/-- CMV's weighted area formula for a type-(C) candidate. -/
def typeCArea (lam beta : ℝ) : ℝ :=
  (Real.pi - (1 - lam) * (beta - Real.sin beta * Real.cos beta)) /
      (Real.tan beta) ^ 2 -
    (1 - lam) *
      (Real.pi / 2 - beta - Real.sin beta * Real.cos beta)

end CMVBallCase
