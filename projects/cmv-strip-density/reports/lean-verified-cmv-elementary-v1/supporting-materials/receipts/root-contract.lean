import CMVElementary
import CMVElementaryGeometry

example : ∀ lam : ℝ, 1 < lam → 0 < CMVElementary.gamma lam ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∃ r : ℝ, 0 < r ∧ r < h ∧ WeightedArea lam (CMVElementary.E lam r) = WeightedArea lam (CMVElementary.C lam h) ∧ CMVElementary.gamma lam / h < WeightedPerimeter lam (FrontierMeasure (CMVElementary.C lam h)) - WeightedPerimeter lam (FrontierMeasure (CMVElementary.E lam r)) ∧ 0 < CMVElementary.gamma lam / h := by
  exact CMVElementary.geometric_comparison
#print axioms CMVElementary.geometric_comparison

example : ∀ lam : ℝ, 1 < lam → 0 < CMVElementary.gamma lam ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∃ r : ℝ, 0 < r ∧ r < h ∧ CMVElementary.A3 lam r = CMVElementary.A4 lam h ∧ CMVElementary.gamma lam / h < CMVElementary.P4 lam h - CMVElementary.P3 lam r ∧ 0 < CMVElementary.gamma lam / h := by
  exact CMVElementary.scalar_comparison
#print axioms CMVElementary.scalar_comparison

example : ∀ lam : ℝ, 1 < lam → CMVElementary.ElementaryRoute lam := by
  exact CMVElementary.elementary_route
#print axioms CMVElementary.elementary_route

example : ∀ lam : ℝ, 1 < lam → (∀ h : ℝ, 0 < h → h ≤ 1 → CMVElementary.FourArcRealization lam h) ∧ (∀ r : ℝ, 0 < r → r < 1 → CMVElementary.ThreeArcRealization lam r) := by
  exact CMVElementary.geometric_realization
#print axioms CMVElementary.geometric_realization
