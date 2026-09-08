/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenH3Cubic

/-!
# Cubic coefficient of the cleared frozen third-row error

This isolates the first nonzero coefficient needed by the quantitative
frozen-path estimate.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
/-- The first nonzero cleared-error coefficient has the explicit compact form
used by the quantitative estimate. -/
theorem frozenPathClearedError_coeff_three (q : Fin 3 → ℝ) :
    (frozenPathClearedError q).coeff 3 = frozenCommonCubic q := by
  norm_num (config := { maxSteps := 2000000 })
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
    rescaledBPathPolynomial, frozenEndpointQuadratic, frozenCommonCubic,
    coeff_mul, Finset.Nat.antidiagonal_succ, coeff_one, coeff_X, pow_succ]
  rw [frozenH3PathPolynomial_coeff_three]
  field_simp [Real.pi_ne_zero]
  ring

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
