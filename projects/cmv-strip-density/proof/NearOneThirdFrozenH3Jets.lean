/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenH3Numerator

/-!
# Exact low-order jets of the frozen normalized third row

The three coefficient calculations are separated from the frozen numerator
cancellation so each algebraic checkpoint can be compiled independently.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
-- Exact second-derivative normalization exceeds the default heartbeat budget.
@[simp] theorem frozenH3PathPolynomial_coeff_zero (q : Fin 3 → ℝ) :
    (frozenH3PathPolynomial q).coeff 0 = 0 := by
  simp only [frozenH3PathPolynomial, coeff_divX]
  rw [polynomial_coeff_via_derivative]
  norm_num [Function.iterate_succ_apply, frozenH3PathNumerator,
    frozenAlgThirdNumerator, frozenAlgAreaNumerator, frozenAlgAreaL,
    frozenAlgAreaZ, frozenAlgAreaX, frozenAlgW, frozenAlgU, frozenAlgK,
    frozenAlgCosineNumerator, frozenAlgFoldNumerator, frozenAlgQPrime,
    frozenAlgDoubleB, frozenAlgDoubleE, frozenAlgR, frozenAlgA,
    rescaledZPathPolynomial, rescaledAPathPolynomial,
    rescaledBPathPolynomial, derivative_pow]
  ring

set_option maxHeartbeats 0 in
-- Exact third-derivative normalization exceeds the default heartbeat budget.
@[simp] theorem frozenH3PathPolynomial_coeff_one (q : Fin 3 → ℝ) :
    (frozenH3PathPolynomial q).coeff 1 = 32 * π ^ 2 := by
  simp only [frozenH3PathPolynomial, coeff_divX]
  rw [polynomial_coeff_via_derivative]
  norm_num [Function.iterate_succ_apply, frozenH3PathNumerator,
    frozenAlgThirdNumerator, frozenAlgAreaNumerator, frozenAlgAreaL,
    frozenAlgAreaZ, frozenAlgAreaX, frozenAlgW, frozenAlgU, frozenAlgK,
    frozenAlgCosineNumerator, frozenAlgFoldNumerator, frozenAlgQPrime,
    frozenAlgDoubleB, frozenAlgDoubleE, frozenAlgR, frozenAlgA,
    rescaledZPathPolynomial, rescaledAPathPolynomial,
    rescaledBPathPolynomial, derivative_pow]
  field_simp [Real.pi_ne_zero]
  ring

set_option maxHeartbeats 0 in
-- Exact fourth-derivative normalization exceeds the default heartbeat budget.
@[simp] theorem frozenH3PathPolynomial_coeff_two (q : Fin 3 → ℝ) :
    (frozenH3PathPolynomial q).coeff 2 =
      (1193 * π ^ 5 + 3656952 * π ^ 3 - 31104 * π * q 2 -
        172606464 * π + 1492992 * q 1) / 7776 := by
  simp only [frozenH3PathPolynomial, coeff_divX]
  rw [polynomial_coeff_via_derivative]
  norm_num [Function.iterate_succ_apply, frozenH3PathNumerator,
    frozenAlgThirdNumerator, frozenAlgAreaNumerator, frozenAlgAreaL,
    frozenAlgAreaZ, frozenAlgAreaX, frozenAlgW, frozenAlgU, frozenAlgK,
    frozenAlgCosineNumerator, frozenAlgFoldNumerator, frozenAlgQPrime,
    frozenAlgDoubleB, frozenAlgDoubleE, frozenAlgR, frozenAlgA,
    rescaledZPathPolynomial, rescaledAPathPolynomial,
    rescaledBPathPolynomial, derivative_pow]
  field_simp [Real.pi_ne_zero]
  ring

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
