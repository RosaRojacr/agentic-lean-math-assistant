/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenMajorantCore

/-!
# Top-level summands of the frozen third-row error majorant

The seven summands isolate the numerical tail estimates so no Lean process has
to normalize the complete degree-96 majorant at once.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

/-- Radius of the explicit frozen third-row endpoint cell. -/
def frozenTailRadius : ℝ := 1 / 1000000

/-- Common-denominator times normalized-third-row summand. -/
def frozenH3ErrorMajorantPolynomial (q : Fin 3 → ℝ) (hq : InEndpointBox q) : ℝ[X] :=
  (frozenPathCommonDenominatorMajorant q hq).majorant *
    (frozenH3PathPolynomialMajorant q hq).majorant

/-- Type-(iii)-bar summand. -/
def frozenThreeBarErrorMajorantPolynomial (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : ℝ[X] :=
  ((frozenPathD4Majorant q hq).majorant ^ 3 *
    (frozenPathThreeCoefficientMajorant q hq).majorant) *
      (frozenPathThreeBarNumeratorMajorant q hq).majorant

/-- Type-(iv)-bar summand. -/
def frozenFourBarErrorMajorantPolynomial (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : ℝ[X] :=
  ((frozenPathD3Majorant q hq).majorant ^ 3 *
    (frozenPathFourCoefficientMajorant q hq).majorant) *
      (frozenPathFourBarNumeratorMajorant q hq).majorant

/-- Area-π coefficient summand. -/
def frozenPiErrorMajorantPolynomial (q : Fin 3 → ℝ) (hq : InEndpointBox q) : ℝ[X] :=
  (frozenPathCommonDenominatorMajorant q hq).majorant *
    (frozenPathPiCoefficientMajorant q hq).majorant

/-- Fold coefficient times the unshifted `2 Z` term. -/
def frozenFoldZeroErrorMajorantPolynomial (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : ℝ[X] :=
  ((frozenPathCommonDenominatorMajorant q hq).majorant *
    (frozenPathFoldCoefficientMajorant q hq).majorant) *
      ((natMajorant 2).majorant * (zPathMajorant q hq).majorant)

/-- Fold coefficient times the shifted type-(iv)-bar term. -/
def frozenFoldTwoErrorMajorantPolynomial (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : ℝ[X] :=
  (((frozenPathD3Majorant q hq).majorant ^ 3 *
    (frozenPathFoldCoefficientMajorant q hq).majorant) * X ^ 2) *
      (frozenPathFourBarNumeratorMajorant q hq).majorant

/-- Endpoint-quadratic correction summand. -/
def frozenEndpointErrorMajorantPolynomial (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : ℝ[X] :=
  ((frozenPathCommonDenominatorMajorant q hq).majorant * X ^ 2) *
    (frozenEndpointQuadraticMajorant q hq).majorant


end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
