/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalInterval

/-!
# Shared source transcription for the scale-local atlas

This module records the exact analytic remainder retained by the generated atlas
DAG and the genuine fourth-order normalization of its third source row.  It is
cell-independent; cell certificates must still prove the denominator guards and
all numerical value and derivative enclosures.
-/

namespace NearOneLocalTranscription

open NearOneAnalyticSystem NearOneRegularizedThirdRow
noncomputable section

abbrev QInterval := LeanSuffixReflective.QInterval

/-- Five-coordinate mean-value enclosure obtained by changing one coordinate at
a time.  Every derivative hypothesis is about the actual scalar slice used at
that step; no multivariable derivative or unchecked AD rule is assumed. -/
theorem realContains_coordinatewise_meanValue_five
    (f : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)
    (f0' f1' f2' f3' f4' : ℝ → ℝ)
    {c0 c1 c2 c3 c4 h0 h1 h2 h3 h4 : ℝ}
    (base slope0 slope1 slope2 slope3 slope4
      displacement0 displacement1 displacement2 displacement3 displacement4 :
      QInterval)
    (hderiv0 : ∀ x ∈ Set.uIcc c0 h0,
      HasDerivAt (fun y => f y c1 c2 c3 c4) (f0' x) x)
    (hderiv1 : ∀ x ∈ Set.uIcc c1 h1,
      HasDerivAt (fun y => f h0 y c2 c3 c4) (f1' x) x)
    (hderiv2 : ∀ x ∈ Set.uIcc c2 h2,
      HasDerivAt (fun y => f h0 h1 y c3 c4) (f2' x) x)
    (hderiv3 : ∀ x ∈ Set.uIcc c3 h3,
      HasDerivAt (fun y => f h0 h1 h2 y c4) (f3' x) x)
    (hderiv4 : ∀ x ∈ Set.uIcc c4 h4,
      HasDerivAt (fun y => f h0 h1 h2 h3 y) (f4' x) x)
    (hbase : base.RealContains (f c0 c1 c2 c3 c4))
    (hslope0 : ∀ x ∈ Set.uIcc c0 h0, slope0.RealContains (f0' x))
    (hslope1 : ∀ x ∈ Set.uIcc c1 h1, slope1.RealContains (f1' x))
    (hslope2 : ∀ x ∈ Set.uIcc c2 h2, slope2.RealContains (f2' x))
    (hslope3 : ∀ x ∈ Set.uIcc c3 h3, slope3.RealContains (f3' x))
    (hslope4 : ∀ x ∈ Set.uIcc c4 h4, slope4.RealContains (f4' x))
    (hdisplacement0 : displacement0.RealContains (h0 - c0))
    (hdisplacement1 : displacement1.RealContains (h1 - c1))
    (hdisplacement2 : displacement2.RealContains (h2 - c2))
    (hdisplacement3 : displacement3.RealContains (h3 - c3))
    (hdisplacement4 : displacement4.RealContains (h4 - c4)) :
    (((((base.add (ScalarSuffixCertificate.QInterval.mul
      slope0 displacement0)).add
      (ScalarSuffixCertificate.QInterval.mul slope1 displacement1)).add
      (ScalarSuffixCertificate.QInterval.mul slope2 displacement2)).add
      (ScalarSuffixCertificate.QInterval.mul slope3 displacement3)).add
      (ScalarSuffixCertificate.QInterval.mul slope4 displacement4)).RealContains
        (f h0 h1 h2 h3 h4) := by
  have hstep0 := ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (fun y => f y c1 c2 c3 c4) f0' base slope0 displacement0
    hderiv0 hbase hslope0 hdisplacement0
  have hstep1 := ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (fun y => f h0 y c2 c3 c4) f1'
    (base.add (ScalarSuffixCertificate.QInterval.mul slope0 displacement0))
      slope1 displacement1
    hderiv1 hstep0 hslope1 hdisplacement1
  have hstep2 := ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (fun y => f h0 h1 y c3 c4) f2'
    ((base.add (ScalarSuffixCertificate.QInterval.mul slope0 displacement0)).add
      (ScalarSuffixCertificate.QInterval.mul slope1 displacement1))
      slope2 displacement2
    hderiv2 hstep1 hslope2 hdisplacement2
  have hstep3 := ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (fun y => f h0 h1 h2 y c4) f3'
    (((base.add (ScalarSuffixCertificate.QInterval.mul slope0 displacement0)).add
      (ScalarSuffixCertificate.QInterval.mul slope1 displacement1)).add
      (ScalarSuffixCertificate.QInterval.mul slope2 displacement2))
      slope3 displacement3
    hderiv3 hstep2 hslope3 hdisplacement3
  exact ScalarSuffixCertificate.QInterval.realContains_centered_meanValue
    (fun y => f h0 h1 h2 h3 y) f4'
    ((((base.add (ScalarSuffixCertificate.QInterval.mul slope0 displacement0)).add
      (ScalarSuffixCertificate.QInterval.mul slope1 displacement1)).add
      (ScalarSuffixCertificate.QInterval.mul slope2 displacement2)).add
      (ScalarSuffixCertificate.QInterval.mul slope3 displacement3))
      slope4 displacement4
    hderiv4 hstep3 hslope4 hdisplacement4

/-- The two exact recurrence steps which leave the generated `R₃` tail. -/
theorem atanQuotientSqRemainder_eq_orderFour (x : ℝ) :
    atanQuotientSqRemainder x =
      -(1 / 3 : ℝ) + x ^ 2 / 5 + x ^ 4 * NearOneAtanRemainder.atanRemainder 3 x := by
  rw [← NearOneAtanRemainder.atanRemainder_one,
    NearOneAtanRemainder.atanRemainder_finite_expansion 1 2]
  norm_num [Finset.sum_range_succ]

/-- Exact polynomial-plus-tail expression evaluated by every generated
`atanQuotient` node.  The analytic tail is retained, not truncated. -/
theorem atanQuotient_eq_orderSix (x : ℝ) :
    atanQuotient x = 1 - x ^ 2 / 3 + x ^ 4 / 5 +
      x ^ 6 * NearOneAtanRemainder.atanRemainder 3 x := by
  rw [atanQuotient_eq_one_add_sq_mul,
    atanQuotientSqRemainder_eq_orderFour]
  ring

/-- Actual derivative of the polynomial-plus-`R₃` expression.  This is the
analytic derivative identity that generated slice derivatives must compose. -/
theorem hasDerivAt_atanQuotient_orderSix (x : ℝ) :
    HasDerivAt atanQuotient
      (-2 * x / 3 + 4 * x ^ 3 / 5 +
        6 * x ^ 5 * NearOneAtanRemainder.atanRemainder 3 x +
        x ^ 6 * NearOneAtanRemainder.atanRemainderDerivative 3 x) x := by
  rw [show atanQuotient = fun y : ℝ =>
      1 - y ^ 2 / 3 + y ^ 4 / 5 +
        y ^ 6 * NearOneAtanRemainder.atanRemainder 3 y by
    funext y
    exact atanQuotient_eq_orderSix y]
  convert (((hasDerivAt_const x (1 : ℝ)).sub
      (((hasDerivAt_id x).pow 2).div_const 3)).add
      (((hasDerivAt_id x).pow 4).div_const 5)).add
      (((hasDerivAt_id x).pow 6).mul
        (NearOneAtanRemainder.hasDerivAt_atanRemainder 3 x)) using 1
  all_goals first | rfl | (norm_num; ring)

/-- Exact fourth-order source normalization.  Since the pole-free row equals
`T / s²` and `s² * regularizedThirdRow = T`, the generated third quantity is
`T / s⁴`.  The three denominator guards are prerequisites of the existing
source reconstruction and `s ≠ 0` is required for division. -/
theorem regularizedThirdRow_div_sq_eq_complete_div_four
    (s z a b pi : ℝ) (hs : s ≠ 0)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hdFour : 1 + s * yCoord s z ≠ 0)
    (hdThree : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    regularizedThirdRow s z a b pi / s ^ 2 =
      completeThirdRowNumerator s z a b pi / s ^ 4 := by
  rw [← sq_mul_regularizedThirdRow_eq_complete s z a b pi hy hdFour hdThree]
  field_simp [hs]

end
end NearOneLocalTranscription
