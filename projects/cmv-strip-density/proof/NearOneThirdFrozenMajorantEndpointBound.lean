/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenMajorantTailDefs

/-! # Endpoint-correction tail bound for the frozen third-row majorant -/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

set_option maxHeartbeats 0 in
/-- The endpoint-quadratic correction uses less than one unit of the scaled
fourth-tail budget. -/
theorem frozenEndpointErrorMajorant_scaled_tail_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    frozenTailRadius *
      ((frozenEndpointErrorMajorantPolynomial q hq).divX.divX.divX.divX.eval
        frozenTailRadius) ≤ 1 := by
  norm_num [frozenTailRadius, frozenEndpointErrorMajorantPolynomial,
    frozenEndpointQuadraticMajorant, frozenPathCommonDenominatorMajorant,
    frozenPathDensityDenominatorMajorant, frozenPathD3Majorant,
    frozenPathD4Majorant, frozenPathVMajorant, frozenPathWMajorant,
    frozenPathYMajorant, frozenPathEMajorant, frozenPathRMajorant,
    frozenPathAMajorant, zPathMajorant, aPathMajorant, bPathMajorant,
    boundedC, natMajorant, oneMajorant, oneSubX2Majorant, oneAddX2Majorant,
    PolynomialMajorant.divX, PolynomialMajorant.add, PolynomialMajorant.sub,
    PolynomialMajorant.neg, PolynomialMajorant.mul, PolynomialMajorant.pow]

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
