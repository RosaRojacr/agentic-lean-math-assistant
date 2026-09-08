/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenCubic

/-!
# Cubic coefficient of the frozen normalized third row

This fifth-derivative calculation is isolated from the final cleared-error
coefficient so Lean need not normalize both large expressions simultaneously.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
/-- Exact cubic coefficient of the frozen normalized third-row path. -/
theorem frozenH3PathPolynomial_coeff_three (q : Fin 3 → ℝ) :
    (frozenH3PathPolynomial q).coeff 3 =
      -(90263 * π ^ 7 - 28880772 * π ^ 5 - 54756 * π ^ 4 * q 0 +
        310608 * π ^ 4 * q 1 + 18144 * π ^ 3 * q 2 +
        1202992128 * π ^ 3 - 8581248 * π ^ 2 * q 0 -
        100154880 * π ^ 2 * q 1 - 8211456 * π * q 2 +
        613122048 * q 0 - 3941498880 * q 1) / (23328 * π) := by
  simp only [frozenH3PathPolynomial, coeff_divX]
  rw [polynomial_coeff_via_derivative]
  norm_num (config := { maxSteps := 2000000 })
    [Function.iterate_succ_apply, frozenH3PathNumerator,
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
