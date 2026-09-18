import CMVBallCase

example : ∀ {lam v₀ v : ℝ}, 0 < lam → lam < 1 → lam * Real.pi < v₀ → v₀ < v → CMVBallCase.typeCPerimeterAtArea lam v₀ ≤ CMVBallCase.typeBPerimeterAtArea lam v₀ → CMVBallCase.typeCPerimeterAtArea lam v < CMVBallCase.typeBPerimeterAtArea lam v := by
  exact CMVBallCase.typeC_dominance_persists
#print axioms CMVBallCase.typeC_dominance_persists
