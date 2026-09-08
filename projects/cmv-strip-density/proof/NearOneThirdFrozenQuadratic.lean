/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenLinear

/-!
# Quadratic cancellation in the cleared frozen third-row path
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
-- Exact coefficient normalization exceeds the default heartbeat budget.
theorem frozenPathClearedError_coeff_two (q : Fin 3 → ℝ) :
    (frozenPathClearedError q).coeff 2 = 0 := by
  norm_num (config := { maxSteps := 1000000 })
    [frozenPathClearedError, frozenPathCommonNumerator,
    frozenPathCommonDenominator, frozenPathThreeCoefficient,
    frozenPathFourCoefficient, frozenPathPiCoefficient,
    frozenPathFoldCoefficient, frozenPathThreeBarNumerator,
    frozenPathFourBarNumerator, frozenPathThreeIncrementNumerator,
    frozenPathFourIncrementNumerator, frozenPathDensityNumerator,
    frozenPathRhoNumerator, frozenPathDensityDenominator, frozenPathD3,
    frozenPathD4, frozenPathV, frozenPathW, frozenPathY, frozenPathE,
    frozenPathR, frozenPathA, frozenAlgA, frozenAlgR, frozenAlgE,
    frozenAlgK, rescaledZPathPolynomial, rescaledAPathPolynomial,
    rescaledBPathPolynomial, frozenEndpointQuadratic, coeff_mul,
    Finset.Nat.antidiagonal_succ, coeff_one, coeff_X, pow_succ]
  field_simp [Real.pi_ne_zero]
  ring

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
