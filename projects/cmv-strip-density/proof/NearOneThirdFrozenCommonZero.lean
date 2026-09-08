/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenH3Jets

/-!
# Constant cancellation in the cleared frozen third-row path

This module isolates the common-numerator constant calculation from the
higher-order cleared-error coefficients.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
-- Exact evaluation of the cleared numerator exceeds the default heartbeat budget.
theorem frozenPathCommonNumerator_coeff_zero (q : Fin 3 → ℝ) :
    (frozenPathCommonNumerator q).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [frozenPathCommonNumerator, frozenPathCommonDenominator,
    frozenPathThreeCoefficient, frozenPathFourCoefficient,
    frozenPathPiCoefficient, frozenPathFoldCoefficient,
    frozenPathThreeBarNumerator, frozenPathFourBarNumerator,
    frozenPathThreeIncrementNumerator, frozenPathFourIncrementNumerator,
    frozenPathDensityNumerator, frozenPathRhoNumerator,
    frozenPathDensityDenominator, frozenPathD3, frozenPathD4, frozenPathV,
    frozenPathW, frozenPathY, frozenPathE, frozenPathR, frozenPathA,
    frozenAlgA, frozenAlgR, frozenAlgE, frozenAlgK,
    rescaledZPathPolynomial, rescaledAPathPolynomial,
    rescaledBPathPolynomial]
  rw [← coeff_zero_eq_eval_zero, frozenH3PathPolynomial_coeff_zero]
  ring

theorem frozenPathClearedError_coeff_zero (q : Fin 3 → ℝ) :
    (frozenPathClearedError q).coeff 0 = 0 := by
  simp [frozenPathClearedError, frozenPathCommonNumerator_coeff_zero]


end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
