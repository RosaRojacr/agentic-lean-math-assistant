/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenCommonZero

/-!
# Linear cancellation in the cleared frozen third-row path
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
-- Exact coefficient normalization exceeds the default heartbeat budget.
theorem frozenPathClearedError_coeff_one (q : Fin 3 → ℝ) :
    (frozenPathClearedError q).coeff 1 = 0 := by
  norm_num [frozenPathClearedError, frozenPathCommonNumerator,
    frozenPathCommonDenominator, frozenPathThreeCoefficient,
    frozenPathFourCoefficient, frozenPathPiCoefficient,
    frozenPathFoldCoefficient, frozenPathThreeBarNumerator,
    frozenPathFourBarNumerator, frozenPathThreeIncrementNumerator,
    frozenPathFourIncrementNumerator, frozenPathDensityNumerator,
    frozenPathRhoNumerator, frozenPathDensityDenominator, frozenPathD3,
    frozenPathD4, frozenPathV, frozenPathW, frozenPathY, frozenPathE,
    frozenPathR, frozenPathA, frozenAlgA, frozenAlgR, frozenAlgE,
    frozenAlgK, rescaledZPathPolynomial, rescaledAPathPolynomial,
    rescaledBPathPolynomial, mul_coeff_one, coeff_one, pow_succ]
  ring

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
