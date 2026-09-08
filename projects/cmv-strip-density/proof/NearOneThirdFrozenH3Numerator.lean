/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenBase

/-!
# Exact low-order cancellation in the frozen third-row numerator

This module isolates the two low-order coefficient calculations needed to
remove the apparent quadratic pole from the frozen third-row path.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
-- Exact polynomial normalization exceeds the default heartbeat budget.
theorem frozenH3PathNumerator_coeff_zero (q : Fin 3 → ℝ) :
    (frozenH3PathNumerator q).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [frozenH3PathNumerator, frozenAlgThirdNumerator,
    frozenAlgAreaNumerator, frozenAlgAreaL, frozenAlgAreaZ, frozenAlgAreaX,
    frozenAlgW, frozenAlgU, frozenAlgK, frozenAlgCosineNumerator,
    frozenAlgFoldNumerator, frozenAlgQPrime, frozenAlgDoubleB,
    frozenAlgDoubleE, frozenAlgR, frozenAlgA]
  norm_num at ⊢
  ring

set_option maxHeartbeats 0 in
-- Exact derivative normalization exceeds the default heartbeat budget.
theorem frozenH3PathNumerator_coeff_one (q : Fin 3 → ℝ) :
    (frozenH3PathNumerator q).coeff 1 = 0 := by
  have hcoeff :
      (frozenH3PathNumerator q).derivative.coeff 0 =
        (frozenH3PathNumerator q).coeff 1 := by
    simpa using coeff_derivative (frozenH3PathNumerator q) 0
  rw [← hcoeff, coeff_zero_eq_eval_zero]
  simp [frozenH3PathNumerator, frozenAlgThirdNumerator,
    frozenAlgAreaNumerator, frozenAlgAreaL, frozenAlgAreaZ, frozenAlgAreaX,
    frozenAlgW, frozenAlgU, frozenAlgK, frozenAlgCosineNumerator,
    frozenAlgFoldNumerator, frozenAlgQPrime, frozenAlgDoubleB,
    frozenAlgDoubleE, frozenAlgR, frozenAlgA, derivative_pow]
  norm_num at ⊢
  ring

theorem X_sq_mul_frozenH3PathPolynomial (q : Fin 3 → ℝ) :
    X ^ 2 * frozenH3PathPolynomial q = frozenH3PathNumerator q := by
  have h0 := frozenH3PathNumerator_coeff_zero q
  have h1 := frozenH3PathNumerator_coeff_one q
  have hd0 : ((frozenH3PathNumerator q).divX).coeff 0 = 0 := by
    simpa [coeff_divX] using h1
  have hx1 : X * (frozenH3PathNumerator q).divX.divX =
      (frozenH3PathNumerator q).divX := by
    simpa [hd0] using X_mul_divX_add (frozenH3PathNumerator q).divX
  have hx0 : X * (frozenH3PathNumerator q).divX =
      frozenH3PathNumerator q := by
    simpa [h0] using X_mul_divX_add (frozenH3PathNumerator q)
  calc
    X ^ 2 * frozenH3PathPolynomial q =
        X * (X * (frozenH3PathNumerator q).divX.divX) := by
      simp [frozenH3PathPolynomial, pow_two, mul_assoc]
    _ = X * (frozenH3PathNumerator q).divX := by rw [hx1]
    _ = frozenH3PathNumerator q := hx0

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
