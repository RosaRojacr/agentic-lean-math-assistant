/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneAnalyticSystem
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
/-!
# Pole-free complete near-one third row

This module regularizes the complete analytic third-row combination, including
the arctangent corrections omitted from the algebraic polynomial summand in
`NearOneNormalizedFlow`.  The second arctangent remainder is represented by an
interval integral, so the normalized row has no removable division by `s` and
is continuous at `s = 0`.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real
open scoped Interval

noncomputable section
set_option maxRecDepth 10000

/-- Pole-free second remainder of `arctan x / x`. -/
def atanQuotientSqRemainder (x : ℝ) : ℝ :=
  - ∫ t in (0 : ℝ)..1, t ^ 2 / (1 + (x * t) ^ 2)

@[simp] theorem atanQuotientSqRemainder_zero :
    atanQuotientSqRemainder 0 = -(1 / 3 : ℝ) := by
  simp [atanQuotientSqRemainder]
  norm_num

theorem atanQuotient_eq_integral (x : ℝ) :
    NearOneAnalyticSystem.atanQuotient x =
      ∫ t in (0 : ℝ)..1, (1 + (x * t) ^ 2)⁻¹ := by
  by_cases hx : x = 0
  · simp [NearOneAnalyticSystem.atanQuotient, hx]
  · apply (mul_left_cancel₀ hx)
    rw [NearOneAnalyticSystem.mul_atanQuotient]
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => x * t) (f' := fun _ : ℝ => x)
      (g := fun u : ℝ => (1 + u ^ 2)⁻¹)
      (fun t _ => hasDerivAt_const_mul (x := t) x)
      (by fun_prop)
      ((continuous_const.add (continuous_id.pow 2)).inv₀
        (fun u hu => by
          change 1 + u ^ 2 = 0 at hu
          nlinarith [sq_nonneg u]))
    simp only [Function.comp_apply] at hsub
    rw [← intervalIntegral.integral_const_mul]
    simpa [mul_comm] using hsub.symm

theorem atanQuotient_eq_one_add_sq_mul (x : ℝ) :
    NearOneAnalyticSystem.atanQuotient x =
      1 + x ^ 2 * atanQuotientSqRemainder x := by
  rw [atanQuotient_eq_integral]
  rw [show (∫ t in (0 : ℝ)..1, (1 + (x * t) ^ 2)⁻¹) =
      ∫ t in (0 : ℝ)..1, (1 - x ^ 2 * (t ^ 2 / (1 + (x * t) ^ 2))) by
    apply intervalIntegral.integral_congr
    intro t _
    change (1 + (x * t) ^ 2)⁻¹ =
      1 - x ^ 2 * (t ^ 2 / (1 + (x * t) ^ 2))
    rw [inv_eq_one_div]
    field_simp
    ring]
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hrat : IntervalIntegrable
      (fun t : ℝ => x ^ 2 * (t ^ 2 / (1 + (x * t) ^ 2)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    exact (continuous_id.pow 2).div
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (fun t => by positivity)
  rw [intervalIntegral.integral_sub hone hrat]
  simp [atanQuotientSqRemainder]
  ring

@[continuity, fun_prop] theorem continuous_atanQuotientSqRemainder :
    Continuous atanQuotientSqRemainder := by
  apply Continuous.neg
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_snd.pow 2).div
    (continuous_const.add ((continuous_fst.mul continuous_snd).pow 2))
    (fun p => by positivity)

/-- Global lower rational enclosure for the second arctangent remainder. -/
theorem atanQuotientSqRemainder_rational_lower (x : ℝ) :
    -(1 / 3 : ℝ) + x ^ 2 / 5 - x ^ 4 / 7 +
        x ^ 6 / (9 * (1 + x ^ 2)) ≤ atanQuotientSqRemainder x := by
  have hrat : IntervalIntegrable
      (fun t : ℝ => -(t ^ 2 / (1 + (x * t) ^ 2)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.neg
    exact (continuous_id.pow 2).div
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (fun t => by positivity)
  have hpoly : IntervalIntegrable
      (fun t : ℝ => -t ^ 2 + x ^ 2 * t ^ 4 - x ^ 4 * t ^ 6 +
        (x ^ 6 / (1 + x ^ 2)) * t ^ 8)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hpoly hrat
  have hineq :
      (∫ t in (0 : ℝ)..1,
        (-t ^ 2 + x ^ 2 * t ^ 4 - x ^ 4 * t ^ 6 +
          (x ^ 6 / (1 + x ^ 2)) * t ^ 8)) ≤
      ∫ t in (0 : ℝ)..1, -(t ^ 2 / (1 + (x * t) ^ 2)) := by
    apply hmono
    intro t ht
    have ht2 : t ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg t, ht.1, ht.2]
    have hd : 0 < 1 + (x * t) ^ 2 := by positivity
    have hx : 0 < 1 + x ^ 2 := by positivity
    have hden : 1 + (x * t) ^ 2 ≤ 1 + x ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr ht2)]
    have hfrac : x ^ 6 * t ^ 8 / (1 + x ^ 2) ≤
        x ^ 6 * t ^ 8 / (1 + (x * t) ^ 2) := by
      rw [div_le_div_iff₀ hx hd]
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    have hid : -(t ^ 2 / (1 + (x * t) ^ 2)) =
        -t ^ 2 + x ^ 2 * t ^ 4 - x ^ 4 * t ^ 6 +
          x ^ 6 * t ^ 8 / (1 + (x * t) ^ 2) := by
      field_simp
      ring
    rw [hid]
    rw [show (x ^ 6 / (1 + x ^ 2)) * t ^ 8 =
      x ^ 6 * t ^ 8 / (1 + x ^ 2) by ring]
    linarith
  rw [show (∫ t in (0 : ℝ)..1,
        (-t ^ 2 + x ^ 2 * t ^ 4 - x ^ 4 * t ^ 6 +
          (x ^ 6 / (1 + x ^ 2)) * t ^ 8)) =
      -(1 / 3 : ℝ) + x ^ 2 / 5 - x ^ 4 / 7 +
        x ^ 6 / (9 * (1 + x ^ 2)) by
    have hint (f : ℝ → ℝ) (hf : Continuous f) :
        IntervalIntegrable f MeasureTheory.volume 0 1 :=
      hf.intervalIntegrable 0 1
    rw [intervalIntegral.integral_add
      (hint _ (by fun_prop))
      (hint _ (by fun_prop))]
    rw [intervalIntegral.integral_sub
      (hint _ (by fun_prop))
      (hint _ (by fun_prop))]
    rw [intervalIntegral.integral_add
      (hint _ (by fun_prop))
      (hint _ (by fun_prop))]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
    field_simp [show 1 + x ^ 2 ≠ 0 by positivity]
    ] at hineq
  simpa [atanQuotientSqRemainder] using hineq


/-- Global upper rational enclosure for the second arctangent remainder. -/
theorem atanQuotientSqRemainder_rational_upper (x : ℝ) :
    atanQuotientSqRemainder x ≤
      -(1 / 3 : ℝ) + x ^ 2 / 5 - x ^ 4 / (7 * (1 + x ^ 2)) := by
  have hrat : IntervalIntegrable
      (fun t : ℝ => -(t ^ 2 / (1 + (x * t) ^ 2)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.neg
    exact (continuous_id.pow 2).div
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (fun t => by positivity)
  have hpoly : IntervalIntegrable
      (fun t : ℝ => -t ^ 2 + x ^ 2 * t ^ 4 -
        (x ^ 4 / (1 + x ^ 2)) * t ^ 6)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hrat hpoly
  have hineq :
      (∫ t in (0 : ℝ)..1, -(t ^ 2 / (1 + (x * t) ^ 2))) ≤
      ∫ t in (0 : ℝ)..1,
        (-t ^ 2 + x ^ 2 * t ^ 4 -
          (x ^ 4 / (1 + x ^ 2)) * t ^ 6) := by
    apply hmono
    intro t ht
    have ht2 : t ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg t, ht.1, ht.2]
    have hd : 0 < 1 + (x * t) ^ 2 := by positivity
    have hx : 0 < 1 + x ^ 2 := by positivity
    have hden : 1 + (x * t) ^ 2 ≤ 1 + x ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr ht2)]
    have hfrac : x ^ 4 * t ^ 6 / (1 + x ^ 2) ≤
        x ^ 4 * t ^ 6 / (1 + (x * t) ^ 2) := by
      rw [div_le_div_iff₀ hx hd]
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    have hid : -(t ^ 2 / (1 + (x * t) ^ 2)) =
        -t ^ 2 + x ^ 2 * t ^ 4 -
          x ^ 4 * t ^ 6 / (1 + (x * t) ^ 2) := by
      field_simp
      ring
    rw [hid]
    rw [show (x ^ 4 / (1 + x ^ 2)) * t ^ 6 =
      x ^ 4 * t ^ 6 / (1 + x ^ 2) by ring]
    exact sub_le_sub_left hfrac _
  rw [show (∫ t in (0 : ℝ)..1,
        (-t ^ 2 + x ^ 2 * t ^ 4 -
          (x ^ 4 / (1 + x ^ 2)) * t ^ 6)) =
      -(1 / 3 : ℝ) + x ^ 2 / 5 -
        x ^ 4 / (7 * (1 + x ^ 2)) by
    have hint (f : ℝ → ℝ) (hf : Continuous f) :
        IntervalIntegrable f MeasureTheory.volume 0 1 :=
      hf.intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub
      (hint _ (by fun_prop))
      (hint _ (by fun_prop))]
    rw [intervalIntegral.integral_add
      (hint _ (by fun_prop))
      (hint _ (by fun_prop))]
    rw [intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_pow]
    norm_num
    field_simp [show 1 + x ^ 2 ≠ 0 by positivity]
    ] at hineq
  simpa [atanQuotientSqRemainder] using hineq

/-- On the unit interval, the second arctangent remainder differs from its
constant term `-1 / 3` by a nonnegative error bounded by `x² / 5`.

This quantitative centered form preserves the cancellations needed in explicit
near-one third-row estimates. -/
theorem atanQuotientSqRemainder_centered_bounds {x : ℝ} (hx : x ^ 2 ≤ 1) :
    0 ≤ atanQuotientSqRemainder x + 1 / 3 ∧
      atanQuotientSqRemainder x + 1 / 3 ≤ x ^ 2 / 5 := by
  have hx0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hx4 : x ^ 4 ≤ x ^ 2 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hfactor : 0 ≤ x ^ 2 * (63 + 18 * x ^ 2 - 10 * x ^ 4) := by
    apply mul_nonneg hx0
    nlinarith
  have hcorrection :
      0 ≤ x ^ 2 / 5 - x ^ 4 / 7 + x ^ 6 / (9 * (1 + x ^ 2)) := by
    calc
      0 ≤ x ^ 2 * (63 + 18 * x ^ 2 - 10 * x ^ 4) /
          (315 * (1 + x ^ 2)) := by positivity
      _ = x ^ 2 / 5 - x ^ 4 / 7 +
          x ^ 6 / (9 * (1 + x ^ 2)) := by
        field_simp [show 1 + x ^ 2 ≠ 0 by positivity]
        ring
  have hlower := atanQuotientSqRemainder_rational_lower x
  have hupper := atanQuotientSqRemainder_rational_upper x
  have hlast : 0 ≤ x ^ 4 / (7 * (1 + x ^ 2)) := by positivity
  constructor <;> linarith


@[continuity, fun_prop] theorem continuous_atanQuotient :
    Continuous NearOneAnalyticSystem.atanQuotient := by
  rw [show NearOneAnalyticSystem.atanQuotient =
      fun x : ℝ => ∫ t in (0 : ℝ)..1, (1 + (x * t) ^ 2)⁻¹ from
    funext atanQuotient_eq_integral]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_const.add ((continuous_fst.mul continuous_snd).pow 2)).inv₀
    (fun p hp => by
      change 1 + (p.1 * p.2) ^ 2 = 0 at hp
      nlinarith [sq_nonneg (p.1 * p.2)])


/-- `(typeFourAngleIncrement s z - 2z) / s²`, without division by `s`. -/
def typeFourAngleIncrementBar2 (s z : ℝ) : ℝ :=
  let d := 1 + s * yCoord s z
  let q := s ^ 2 * z / d
  2 * z / d *
    (s ^ 2 * z ^ 2 / d ^ 2 * atanQuotientSqRemainder q - aCoord s z)

/-- `(typeThreeAngleIncrement s z a b - 2e) / s²`, without division by `s`. -/
def typeThreeAngleIncrementBar2 (s z a b : ℝ) : ℝ :=
  let e := eCoord s z a b
  let r := rCoord s a
  let d := 1 + wCoord s a * vCoord s z a b
  let q := s ^ 2 * e / d
  2 * e / d *
    (s ^ 2 * e ^ 2 / d ^ 2 * atanQuotientSqRemainder q -
      r * (r + s * e))

theorem sq_mul_typeFourAngleIncrementBar2 (s z : ℝ)
    (hd : 1 + s * yCoord s z ≠ 0) :
    s ^ 2 * typeFourAngleIncrementBar2 s z =
      typeFourAngleIncrement s z - 2 * z := by
  simp only [typeFourAngleIncrementBar2, typeFourAngleIncrement]
  rw [atanQuotient_eq_one_add_sq_mul]
  field_simp [hd]
  simp [yCoord, aCoord]
  ring

theorem sq_mul_typeThreeAngleIncrementBar2 (s z a b : ℝ)
    (hd : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    s ^ 2 * typeThreeAngleIncrementBar2 s z a b =
      typeThreeAngleIncrement s z a b - 2 * eCoord s z a b := by
  simp only [typeThreeAngleIncrementBar2, typeThreeAngleIncrement]
  rw [atanQuotient_eq_one_add_sq_mul]
  field_simp [hd]
  simp [wCoord, vCoord]
  ring

/-- `(typeFourAngleBar s z - 2z) / s²`, without division by `s`. -/
def typeFourAngleBar2 (s z : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * atanQuotient s +
    density s z * typeFourAngleIncrementBar2 s z +
    2 * s * z * densityCubeQuotient s z

/-- `(typeThreeAngleBar s z a b - 2e) / s²`, without division by `s`. -/
def typeThreeAngleBar2 (s z a b : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * rCoord s a *
      atanQuotient (wCoord s a) +
    density s z * typeThreeAngleIncrementBar2 s z a b +
    2 * s * eCoord s z a b * densityCubeQuotient s z

theorem sq_mul_typeFourAngleBar2 (s z : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hd : 1 + s * yCoord s z ≠ 0) :
    s ^ 2 * typeFourAngleBar2 s z =
      typeFourAngleBar s z - 2 * z := by
  have hrho : density s z = 1 + s ^ 3 * densityCubeQuotient s z := by
    linarith [density_sub_one_eq_cube_mul s z hy]
  have hinc : typeFourAngleIncrement s z =
      2 * z + s ^ 2 * typeFourAngleIncrementBar2 s z := by
    linarith [sq_mul_typeFourAngleIncrementBar2 s z hd]
  rw [typeFourAngleBar, hrho, hinc, ← mul_atanQuotient]
  simp only [typeFourAngleBar2, hrho]
  ring

theorem sq_mul_typeThreeAngleBar2 (s z a b : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hd : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    s ^ 2 * typeThreeAngleBar2 s z a b =
      typeThreeAngleBar s z a b - 2 * eCoord s z a b := by
  have hrho : density s z = 1 + s ^ 3 * densityCubeQuotient s z := by
    linarith [density_sub_one_eq_cube_mul s z hy]
  have hinc : typeThreeAngleIncrement s z a b =
      2 * eCoord s z a b +
        s ^ 2 * typeThreeAngleIncrementBar2 s z a b := by
    linarith [sq_mul_typeThreeAngleIncrementBar2 s z a b hd]
  have hatan : Real.arctan (wCoord s a) =
      s * rCoord s a * atanQuotient (wCoord s a) := by
    rw [← mul_atanQuotient]
    simp [wCoord]
  rw [typeThreeAngleBar, hrho, hinc, hatan]
  simp only [typeThreeAngleBar2, hrho]
  ring

/-- The fold-angle correction after its exact `s²` factor is removed. -/
def foldAngleCorrectionBar (s z : ℝ) : ℝ :=
  -foldDenominator s z * typeFourSineProductBar s z * typeFourAngleBar s z

theorem sq_mul_foldAngleCorrectionBar (s z pi : ℝ) :
    s ^ 2 * foldAngleCorrectionBar s z =
      completeFoldNumerator s z pi -
        (NearOneNormalizedFlow.H1 z pi).eval s := by
  simp [foldAngleCorrectionBar, completeFoldNumerator]
  ring

/-- The area-angle correction after its exact `s²` factor is removed. -/
def areaAngleCorrectionBar (s z a b : ℝ) : ℝ :=
  areaDenominator s z a b *
    (2 * halfCos s ^ 2 * typeThreeAngleBar2 s z a b -
      (1 + halfCos (wCoord s a)) ^ 2 * typeFourAngleBar2 s z +
      4 * z * areaPiWeight s a)

theorem sq_mul_areaAngleCorrectionBar (s z a b pi : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hdFour : 1 + s * yCoord s z ≠ 0)
    (hdThree : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    s ^ 2 * areaAngleCorrectionBar s z a b =
      completeAreaNumerator s z a b pi -
        (NearOneNormalizedFlow.areaNumerator z a b pi).eval s := by
  rw [areaAngleCorrectionBar]
  rw [show s ^ 2 *
      (areaDenominator s z a b *
        (2 * halfCos s ^ 2 * typeThreeAngleBar2 s z a b -
          (1 + halfCos (wCoord s a)) ^ 2 * typeFourAngleBar2 s z +
          4 * z * areaPiWeight s a)) =
      areaDenominator s z a b *
        (2 * halfCos s ^ 2 *
            (s ^ 2 * typeThreeAngleBar2 s z a b) -
          (1 + halfCos (wCoord s a)) ^ 2 *
            (s ^ 2 * typeFourAngleBar2 s z) +
          4 * z * (s ^ 2 * areaPiWeight s a)) by ring]
  rw [sq_mul_typeThreeAngleBar2 s z a b hy hdThree,
    sq_mul_typeFourAngleBar2 s z hy hdFour, sq_mul_areaPiWeight]
  simp only [completeAreaNumerator]
  ring

/-- The complete analytic analogue of `thirdRowNumerator.eval`. -/
def completeThirdRowNumerator (s z a b pi : ℝ) : ℝ :=
  completeH3Numerator s z a b pi -
    2 * (NearOneNormalizedFlow.H2 z a b).eval s +
    4 * completeFoldNumerator s z pi +
    (2 * pi / 3) * s *
      ((NearOneNormalizedFlow.H2 z a b).eval s -
        completeFoldNumerator s z pi)

/-- The honest, pole-free regularized third row. -/
def regularizedThirdRow (s z a b pi : ℝ) : ℝ :=
  NearOneNormalizedFlow.H3hatPolynomial s z a b pi +
    areaAngleCorrectionBar s z a b +
    (4 - 2 * z * s / 3) * foldAngleCorrectionBar s z


private theorem continuousAt_densityCubeQuotient_zero (z : ℝ) :
    ContinuousAt (fun s => densityCubeQuotient s z) 0 := by
  unfold densityCubeQuotient yCoord aCoord
  fun_prop (disch := norm_num)

private theorem continuousAt_density_zero (z : ℝ) :
    ContinuousAt (fun s => density s z) 0 := by
  unfold density halfCos yCoord aCoord
  fun_prop (disch := norm_num)

private theorem continuousAt_typeFourAngleIncrementBar2_zero (z : ℝ) :
    ContinuousAt (fun s => typeFourAngleIncrementBar2 s z) 0 := by
  unfold typeFourAngleIncrementBar2 yCoord aCoord
  have hrem : ContinuousAt
      (fun s : ℝ => atanQuotientSqRemainder
        (s ^ 2 * z / (1 + s * (s * (1 + s * z))))) 0 :=
    continuous_atanQuotientSqRemainder.continuousAt.comp
      (by fun_prop (disch := norm_num))
  fun_prop (disch := first | exact hrem | norm_num)

private theorem continuousAt_typeThreeAngleIncrementBar2_zero
    (z a b : ℝ) :
    ContinuousAt (fun s => typeThreeAngleIncrementBar2 s z a b) 0 := by
  unfold typeThreeAngleIncrementBar2 wCoord vCoord rCoord eCoord
  have hrem : ContinuousAt
      (fun s : ℝ => atanQuotientSqRemainder
        (s ^ 2 * (6 * a - 2 * z + s * b) /
          (1 + s * (2 + s * a) *
            (s * (2 + s * a + s * (6 * a - 2 * z + s * b)))))) 0 :=
    continuous_atanQuotientSqRemainder.continuousAt.comp
      (by fun_prop (disch := norm_num))
  fun_prop (disch := first | exact hrem | norm_num)

private theorem continuousAt_typeFourAngleBar2_zero (z : ℝ) :
    ContinuousAt (fun s => typeFourAngleBar2 s z) 0 := by
  have hdelta := continuousAt_densityCubeQuotient_zero z
  have hrho := continuousAt_density_zero z
  have hinc := continuousAt_typeFourAngleIncrementBar2_zero z
  have hatan : ContinuousAt (fun s : ℝ => atanQuotient s) 0 :=
    continuous_atanQuotient.continuousAt
  unfold typeFourAngleBar2
  fun_prop (disch := assumption)

private theorem continuousAt_typeThreeAngleBar2_zero (z a b : ℝ) :
    ContinuousAt (fun s => typeThreeAngleBar2 s z a b) 0 := by
  have hdelta := continuousAt_densityCubeQuotient_zero z
  have hrho := continuousAt_density_zero z
  have hinc := continuousAt_typeThreeAngleIncrementBar2_zero z a b
  have hatan : ContinuousAt
      (fun s => atanQuotient (wCoord s a)) 0 :=
    continuous_atanQuotient.continuousAt.comp (by
      unfold wCoord rCoord
      fun_prop)
  unfold typeThreeAngleBar2 rCoord eCoord
  fun_prop (disch := assumption)

private theorem continuousAt_typeFourAngleBar_zero (z : ℝ) :
    ContinuousAt (fun s => typeFourAngleBar s z) 0 := by
  have hdelta := continuousAt_densityCubeQuotient_zero z
  have hrho := continuousAt_density_zero z
  have hatan : ContinuousAt (fun s : ℝ => Real.arctan s) 0 :=
    Real.continuous_arctan.continuousAt
  have hquot : ContinuousAt
      (fun s => atanQuotient
        (s ^ 2 * z / (1 + s * yCoord s z))) 0 :=
    continuous_atanQuotient.continuousAt.comp (by
      unfold yCoord aCoord
      fun_prop (disch := norm_num))
  unfold typeFourAngleBar typeFourAngleIncrement yCoord aCoord
  fun_prop (disch := first | assumption | norm_num [yCoord, aCoord])

private theorem continuousAt_foldAngleCorrectionBar_zero (z : ℝ) :
    ContinuousAt (fun s => foldAngleCorrectionBar s z) 0 := by
  have hangle := continuousAt_typeFourAngleBar_zero z
  unfold foldAngleCorrectionBar foldDenominator typeFourSineProductBar
    yCoord aCoord
  fun_prop (disch := first | exact hangle | norm_num)

private theorem continuousAt_areaAngleCorrectionBar_zero (z a b : ℝ) :
    ContinuousAt (fun s => areaAngleCorrectionBar s z a b) 0 := by
  have hthree := continuousAt_typeThreeAngleBar2_zero z a b
  have hfour := continuousAt_typeFourAngleBar2_zero z
  unfold areaAngleCorrectionBar areaDenominator areaPiWeight halfCos
    wCoord vCoord yCoord rCoord eCoord aCoord
  fun_prop (disch := first | assumption | norm_num)


theorem continuousAt_regularizedThirdRow_zero (z a b pi : ℝ) :
    ContinuousAt (fun s => regularizedThirdRow s z a b pi) 0 := by
  have hpoly : ContinuousAt
      (fun s => NearOneNormalizedFlow.H3hatPolynomial s z a b pi) 0 := by
    unfold NearOneNormalizedFlow.H3hatPolynomial
    exact (Polynomial.continuous _).continuousAt
  have harea := continuousAt_areaAngleCorrectionBar_zero z a b
  have hfold := continuousAt_foldAngleCorrectionBar_zero z
  unfold regularizedThirdRow
  fun_prop (disch := assumption)



/-- The regularized row has its genuine endpoint value, not the endpoint of the
algebraic polynomial summand. -/
theorem regularizedThirdRow_zero (z a b pi : ℝ) :
    regularizedThirdRow 0 z a b pi =
      NearOneNormalizedFlow.H3hatPolynomial 0 z a b pi +
        80 * z - 192 * a := by
  simp [regularizedThirdRow, areaAngleCorrectionBar, foldAngleCorrectionBar,
    typeThreeAngleBar2, typeFourAngleBar2, typeThreeAngleIncrementBar2,
    typeFourAngleIncrementBar2, areaDenominator, foldDenominator,
    typeFourSineProductBar, typeFourAngleBar, typeFourAngleIncrement,
    areaPiWeight, NearOneNormalizedFlow.K, NearOneNormalizedFlow.R,
    densityCubeQuotient, density, halfCos, yCoord, wCoord, vCoord,
    aCoord, rCoord, eCoord, atanQuotient]
  ring


private theorem exactCuspSeed_fold :
    foldRow 0 Real.pi Real.pi = 0 := by
  simp [foldRow, halfCos, typeFourSineBar, typeFourSineProductBar,
    yCoord, aCoord]
  ring

private theorem exactCuspSeed_H2 :
    (NearOneNormalizedFlow.H2 Real.pi (5 * Real.pi / 12)
      (-44 + 19 * Real.pi ^ 2 / 24)).eval 0 = 0 := by
  simp [NearOneNormalizedFlow.H2, NearOneNormalizedFlow.cosineNumerator,
    NearOneNormalizedFlow.E, NearOneNormalizedFlow.R]
  ring

private theorem exactCuspSeed_regularizedThirdRow :
    regularizedThirdRow 0 Real.pi (5 * Real.pi / 12)
      (-44 + 19 * Real.pi ^ 2 / 24) Real.pi = 0 := by
  rw [regularizedThirdRow_zero]
  let p := NearOneNormalizedFlow.thirdRowNumerator Real.pi
    (5 * Real.pi / 12) (-44 + 19 * Real.pi ^ 2 / 24) Real.pi
  have hder : p.derivative.derivative.eval 0 = 0 := by
    dsimp [p]
    simp [NearOneNormalizedFlow.thirdRowNumerator,
      NearOneNormalizedFlow.areaNumerator,
      NearOneNormalizedFlow.cosineNumerator,
      NearOneNormalizedFlow.foldNumerator, NearOneNormalizedFlow.qPrime,
      NearOneNormalizedFlow.areaL, NearOneNormalizedFlow.areaZ,
      NearOneNormalizedFlow.areaX, NearOneNormalizedFlow.W,
      NearOneNormalizedFlow.U, NearOneNormalizedFlow.K,
      NearOneNormalizedFlow.B, NearOneNormalizedFlow.E,
      NearOneNormalizedFlow.R, NearOneNormalizedFlow.A, derivative_pow]
    ring
  have hcoeff : p.derivative.derivative.coeff 0 = 2 * p.coeff 2 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    norm_num
    ring
  rw [← Polynomial.coeff_zero_eq_eval_zero] at hder
  have hp : p.coeff 2 = 0 := by linarith
  simp only [NearOneNormalizedFlow.H3hatPolynomial,
    NearOneNormalizedFlow.normalizedThirdRow]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.coeff_divX, Polynomial.coeff_divX]
  norm_num
  change p.coeff 2 + 80 * Real.pi -
    192 * (5 * Real.pi / 12) = 0
  rw [hp]
  ring

/-- Exact root of all three complete normalized near-one equations at the cusp.
The third coordinate is the first derivative coefficient of the type-(iii)
upper-angle increment in this chart. -/
theorem exactCuspSeed :
    foldRow 0 Real.pi Real.pi = 0 ∧
      (NearOneNormalizedFlow.H2 Real.pi (5 * Real.pi / 12)
        (-44 + 19 * Real.pi ^ 2 / 24)).eval 0 = 0 ∧
      regularizedThirdRow 0 Real.pi (5 * Real.pi / 12)
        (-44 + 19 * Real.pi ^ 2 / 24) Real.pi = 0 :=
  ⟨exactCuspSeed_fold, exactCuspSeed_H2,
    exactCuspSeed_regularizedThirdRow⟩

/-- The complete regularized third row at `s = 0`, expanded as a polynomial
in the three branch coordinates. -/
def thirdRowEndpointPolynomial (z a b pi : ℝ) : ℝ :=
  -(4 / 3) *
    (-576 * a ^ 3 + 42 * a ^ 2 * pi + 432 * a ^ 2 * z +
      36 * a * b - 28 * a * pi * z - 92 * a * z ^ 2 + 144 * a +
      4 * b * pi - 16 * b * z + pi * z ^ 2 - 48 * pi +
      6 * z ^ 3 + 120 * z)

/-- Exact polynomial form of the complete third row at the cusp endpoint. -/
theorem regularizedThirdRow_zero_eq_endpointPolynomial (z a b pi : ℝ) :
    regularizedThirdRow 0 z a b pi =
      thirdRowEndpointPolynomial z a b pi := by
  rw [regularizedThirdRow_zero]
  let q := NearOneNormalizedFlow.thirdRowNumerator z a b pi
  have hder : q.derivative.derivative.eval 0 =
      2 * (thirdRowEndpointPolynomial z a b pi - 80 * z + 192 * a) := by
    dsimp [q]
    simp [NearOneNormalizedFlow.thirdRowNumerator,
      NearOneNormalizedFlow.areaNumerator,
      NearOneNormalizedFlow.cosineNumerator,
      NearOneNormalizedFlow.foldNumerator, NearOneNormalizedFlow.qPrime,
      NearOneNormalizedFlow.areaL, NearOneNormalizedFlow.areaZ,
      NearOneNormalizedFlow.areaX, NearOneNormalizedFlow.W,
      NearOneNormalizedFlow.U, NearOneNormalizedFlow.K,
      NearOneNormalizedFlow.B, NearOneNormalizedFlow.E,
      NearOneNormalizedFlow.R, NearOneNormalizedFlow.A, derivative_pow,
      thirdRowEndpointPolynomial]
    ring
  have hcoeff : q.derivative.derivative.coeff 0 = 2 * q.coeff 2 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    norm_num
    ring
  rw [← Polynomial.coeff_zero_eq_eval_zero] at hder
  rw [hcoeff] at hder
  have hq : q.coeff 2 =
      thirdRowEndpointPolynomial z a b pi - 80 * z + 192 * a := by
    linarith
  simp only [NearOneNormalizedFlow.H3hatPolynomial,
    NearOneNormalizedFlow.normalizedThirdRow]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [Polynomial.coeff_divX, Polynomial.coeff_divX]
  norm_num
  change q.coeff 2 + 80 * z - 192 * a =
    thirdRowEndpointPolynomial z a b pi
  rw [hq]
  ring


/-- The three complete normalized near-one equations, ordered as fold,
cosine/incidence, and equal area. -/
def nearOneRootMap (s pi : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![foldRow s (x 0) pi,
    (NearOneNormalizedFlow.H2 (x 0) (x 1) (x 2)).eval s,
    regularizedThirdRow s (x 0) (x 1) (x 2) pi]

/-- The coordinate Jacobian of a three-row map. Column `j` differentiates
along the `j`th coordinate while the other two coordinates stay fixed. -/
def coordinateJacobian
    (f : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => deriv (fun t => f (Function.update x j t) i) (x j)

/-- Coordinate Jacobian of the complete normalized near-one root map. -/
def nearOneJacobian (s pi : ℝ) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  coordinateJacobian (nearOneRootMap s pi) x

/-- The exact cusp point in `(z,a,b)` coordinates. -/
def exactCuspPoint : Fin 3 → ℝ :=
  ![Real.pi, 5 * Real.pi / 12, -44 + 19 * Real.pi ^ 2 / 24]

/-- The complete normalized root map vanishes at the exact cusp point. -/
theorem nearOneRootMap_exactCusp :
    nearOneRootMap 0 Real.pi exactCuspPoint = 0 := by
  rcases exactCuspSeed with ⟨hfold, hcosine, harea⟩
  ext i
  fin_cases i
  · simpa [nearOneRootMap, exactCuspPoint] using hfold
  · simpa [nearOneRootMap, exactCuspPoint] using hcosine
  · simpa [nearOneRootMap, exactCuspPoint] using harea


/-- Exact endpoint reduction of all three complete normalized rows. -/
theorem nearOneRootMap_zero (pi : ℝ) (x : Fin 3 → ℝ) :
    nearOneRootMap 0 pi x =
      ![2 * x 0 - 2 * pi,
        -40 * x 0 + 96 * x 1,
        thirdRowEndpointPolynomial (x 0) (x 1) (x 2) pi] := by
  ext i
  fin_cases i
  · simp [nearOneRootMap, foldRow, halfCos, typeFourSineBar,
      typeFourSineProductBar, yCoord, aCoord]
    ring
  · simp [nearOneRootMap, NearOneNormalizedFlow.H2,
      NearOneNormalizedFlow.cosineNumerator, NearOneNormalizedFlow.E,
      NearOneNormalizedFlow.R]
    ring
  · simp [nearOneRootMap,
      regularizedThirdRow_zero_eq_endpointPolynomial]


theorem thirdRowEndpointPolynomial_deriv_z (z a b pi : ℝ) :
    deriv (fun z' => thirdRowEndpointPolynomial z' a b pi) z =
      -8 * (216 * a ^ 2 - 14 * a * pi - 92 * a * z - 8 * b +
        pi * z + 9 * z ^ 2 + 60) / 3 := by
  let q : ℝ[X] := C (-(4 / 3 : ℝ)) *
    (C (-576 * a ^ 3 + 42 * a ^ 2 * pi + 36 * a * b + 144 * a +
        4 * b * pi - 48 * pi) +
      C (432 * a ^ 2 - 28 * a * pi - 16 * b + 120) * X +
      C (-92 * a + pi) * X ^ 2 + 6 * X ^ 3)
  rw [show (fun u => thirdRowEndpointPolynomial u a b pi) =
      fun u => q.eval u by
    funext u
    simp [q, thirdRowEndpointPolynomial]
    ring]
  rw [q.deriv]
  simp [q, derivative_pow]
  ring


theorem thirdRowEndpointPolynomial_deriv_a (z a b pi : ℝ) :
    deriv (fun a' => thirdRowEndpointPolynomial z a' b pi) a =
      16 * (432 * a ^ 2 - 21 * a * pi - 216 * a * z - 9 * b +
        7 * pi * z + 23 * z ^ 2 - 36) / 3 := by
  let q : ℝ[X] := C (-(4 / 3 : ℝ)) *
    (C (4 * b * pi - 16 * b * z + pi * z ^ 2 - 48 * pi +
        6 * z ^ 3 + 120 * z) +
      C (36 * b - 28 * pi * z - 92 * z ^ 2 + 144) * X +
      C (42 * pi + 432 * z) * X ^ 2 - 576 * X ^ 3)
  rw [show (fun u => thirdRowEndpointPolynomial z u b pi) =
      fun u => q.eval u by
    funext u
    simp [q, thirdRowEndpointPolynomial]
    ring]
  rw [q.deriv]
  simp [q, derivative_pow]
  ring


theorem thirdRowEndpointPolynomial_deriv_b (z a b pi : ℝ) :
    deriv (fun b' => thirdRowEndpointPolynomial z a b' pi) b =
      16 * (-9 * a - pi + 4 * z) / 3 := by
  let q : ℝ[X] := C (-(4 / 3 : ℝ)) *
    (C (-576 * a ^ 3 + 42 * a ^ 2 * pi + 432 * a ^ 2 * z -
        28 * a * pi * z - 92 * a * z ^ 2 + 144 * a +
        pi * z ^ 2 - 48 * pi + 6 * z ^ 3 + 120 * z) +
      C (36 * a + 4 * pi - 16 * z) * X)
  rw [show (fun u => thirdRowEndpointPolynomial z a u pi) =
      fun u => q.eval u by
    funext u
    simp [q, thirdRowEndpointPolynomial]
    ring]
  rw [q.deriv]
  simp [q, derivative_pow]
  ring


/-- Exact `(z,a,b)` Jacobian matrix at the cusp. -/
def exactCuspJacobian : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 0, 0;
    -40, 96, 0;
    8 * (3 * Real.pi ^ 2 - 412) / 3,
      -2 * (7 * Real.pi ^ 2 - 2880) / 3,
      -4 * Real.pi]

/-- The coordinate derivatives of the complete rows give the claimed exact
Jacobian, including the analytic correction in the third row. -/
theorem nearOneJacobian_exactCusp :
    nearOneJacobian 0 Real.pi exactCuspPoint = exactCuspJacobian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nearOneJacobian, coordinateJacobian, nearOneRootMap_zero,
      exactCuspPoint, exactCuspJacobian,
      thirdRowEndpointPolynomial_deriv_z,
      thirdRowEndpointPolynomial_deriv_a,
      thirdRowEndpointPolynomial_deriv_b] <;>
    ring

/-- Exact determinant of the complete endpoint Jacobian. -/
theorem exactCuspJacobian_det :
    Matrix.det exactCuspJacobian = -768 * Real.pi := by
  rw [Matrix.det_fin_three]
  simp [exactCuspJacobian]
  ring

/-- Exact determinant of the actual root-map Jacobian at the cusp. -/
theorem nearOneJacobian_exactCusp_det :
    Matrix.det (nearOneJacobian 0 Real.pi exactCuspPoint) =
      -768 * Real.pi := by
  rw [nearOneJacobian_exactCusp, exactCuspJacobian_det]

/-- The complete endpoint Jacobian is nondegenerate, with negative
determinant. -/
theorem nearOneJacobian_exactCusp_det_neg :
    Matrix.det (nearOneJacobian 0 Real.pi exactCuspPoint) < 0 := by
  rw [nearOneJacobian_exactCusp_det]
  nlinarith [Real.pi_pos]


theorem sq_mul_regularizedThirdRow_eq_complete
    (s z a b pi : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hdFour : 1 + s * yCoord s z ≠ 0)
    (hdThree : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    s ^ 2 * regularizedThirdRow s z a b pi =
      completeThirdRowNumerator s z a b pi := by
  calc
    s ^ 2 * regularizedThirdRow s z a b pi =
        s ^ 2 * NearOneNormalizedFlow.H3hatPolynomial s z a b pi +
          s ^ 2 * areaAngleCorrectionBar s z a b +
          (4 - 2 * z * s / 3) *
            (s ^ 2 * foldAngleCorrectionBar s z) := by
      simp only [regularizedThirdRow]
      ring
    _ = _ := by
      rw [NearOneNormalizedFlow.H3hatPolynomial_identity,
        sq_mul_areaAngleCorrectionBar s z a b pi hy hdFour hdThree,
        sq_mul_foldAngleCorrectionBar s z pi]
      rw [completeThirdRowNumerator,
        completeH3Numerator_eq_H3_add_corrections]
      ring


theorem completeThirdRowNumerator_zero (z a b pi : ℝ) :
    completeThirdRowNumerator 0 z a b pi = 0 := by
  have h := sq_mul_regularizedThirdRow_eq_complete 0 z a b pi
    (by simp [yCoord])
    (by simp [yCoord])
    (by simp [wCoord, vCoord])
  simpa using h.symm

theorem regularizedThirdRow_eq_zero_iff_complete
    (s z a b pi : ℝ) (hs : s ≠ 0)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hdFour : 1 + s * yCoord s z ≠ 0)
    (hdThree : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    regularizedThirdRow s z a b pi = 0 ↔
      completeThirdRowNumerator s z a b pi = 0 := by
  rw [← sq_mul_regularizedThirdRow_eq_complete s z a b pi
    hy hdFour hdThree]
  exact (mul_eq_zero.trans (or_iff_right (pow_ne_zero 2 hs))).symm

theorem sourceAreaResidual_eq_zero_iff_regularizedThirdRow
    (s z a b pi : ℝ) (hs : s ≠ 0)
    (hy : yCoord s z ^ 2 < 1)
    (hdenFour : 1 + s * yCoord s z ≠ 0)
    (haddFour : s *
      ((yCoord s z - s) / (1 + s * yCoord s z)) < 1)
    (hdenThree : 1 + wCoord s a * vCoord s z a b ≠ 0)
    (haddThree : wCoord s a *
      ((vCoord s z a b - wCoord s a) /
        (1 + wCoord s a * vCoord s z a b)) < 1)
    (hfoldSource : sourceFoldResidual s z pi = 0)
    (hcosineSource : sourceCosineResidual s z a b = 0) :
    sourceAreaResidual s z a b pi = 0 ↔
      regularizedThirdRow s z a b pi = 0 := by
  have hyne : 1 - yCoord s z ^ 2 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hy)
  have hfold : completeFoldNumerator s z pi = 0 :=
    (sourceFoldResidual_eq_zero_iff_complete s z pi hs hyne
      hdenFour haddFour).mp hfoldSource
  have hcosine : (NearOneNormalizedFlow.H2 z a b).eval s = 0 :=
    (sourceCosineResidual_eq_zero_iff_H2 s z a b hs hy).mp hcosineSource
  have hcombination : completeThirdRowNumerator s z a b pi =
      completeH3Numerator s z a b pi := by
    simp [completeThirdRowNumerator, hfold, hcosine]
  rw [sourceAreaResidual_eq_zero_iff_completeH3 s z a b pi hs hy
    hdenFour haddFour hdenThree haddThree hfoldSource hcosineSource]
  rw [← hcombination]
  exact (regularizedThirdRow_eq_zero_iff_complete s z a b pi hs hyne
    hdenFour hdenThree).symm

end
end NearOneRegularizedThirdRow
