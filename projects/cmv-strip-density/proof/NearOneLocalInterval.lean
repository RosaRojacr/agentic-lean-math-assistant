/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import ScalarSuffixCertificate
import NearOneAtanRemainder

/-!
# Exact interval primitives for the scale-local atlas

This module supplies the shared soundness boundary for outward-rounded
multiplication nodes and the exact 160-bit dyadic enclosure of `Real.pi` used
by the scale-local generated expressions.
-/

namespace NearOneLocalInterval

open Real
open scoped BigOperators
noncomputable section

abbrev QInterval := LeanSuffixReflective.QInterval

/-- A wider rational interval preserves a real enclosure. -/
theorem realContains_of_subset {inner outer : QInterval} {x : ℝ}
    (hlo : outer.lo ≤ inner.lo) (hhi : inner.hi ≤ outer.hi)
    (hx : inner.RealContains x) : outer.RealContains x := by
  have hloR : (outer.lo : ℝ) ≤ (inner.lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (inner.hi : ℝ) ≤ (outer.hi : ℝ) := by exact_mod_cast hhi
  exact ⟨hloR.trans hx.1, hx.2.trans hhiR⟩

/-- Soundness of an outward-rounded multiplication node.  The two rational
side conditions are exactly what a generated certificate must check after
rounding the tight product outward. -/
theorem outwardMul_sound {left right outer : QInterval} {x y : ℝ}
    (hlo : outer.lo ≤ (ScalarSuffixCertificate.QInterval.mul left right).lo)
    (hhi : (ScalarSuffixCertificate.QInterval.mul left right).hi ≤ outer.hi)
    (hx : left.RealContains x) (hy : right.RealContains y) :
    outer.RealContains (x * y) :=
  realContains_of_subset hlo hhi
    (ScalarSuffixCertificate.QInterval.realContains_mul hx hy)

/-- The first 36 terms of the odd arctangent series, represented through the
same quotient remainder expansion used by the atlas. -/
def atanSeries36 (x : ℝ) : ℝ :=
  x * (1 + x ^ 2 *
    ∑ j ∈ Finset.range 35,
      (-1 : ℝ) ^ (1 + j) * x ^ (2 * j) / (2 * (1 + j) + 1 : ℕ))

/-- The retained 36-term rational arctangent evaluator has a proved analytic
remainder, rather than an unchecked alternating-series oracle. -/
theorem abs_arctan_sub_atanSeries36_le (x : ℝ) :
    |Real.arctan x - atanSeries36 x| ≤ |x| ^ 73 / 73 := by
  have hExpansion := NearOneAtanRemainder.atanRemainder_finite_expansion 1 35 x
  have hQuotient := NearOneRegularizedThirdRow.atanQuotient_eq_one_add_sq_mul x
  rw [← NearOneAtanRemainder.atanRemainder_one, hExpansion] at hQuotient
  have hIdentity :
      Real.arctan x - atanSeries36 x =
        x ^ 73 * NearOneAtanRemainder.atanRemainder 36 x := by
    rw [← NearOneAnalyticSystem.mul_atanQuotient, hQuotient]
    simp only [atanSeries36]
    ring
  rw [hIdentity, abs_mul, abs_pow]
  have hRemainder := NearOneAtanRemainder.abs_atanRemainder_le 36 x
  norm_num at hRemainder
  calc
    |x| ^ 73 * |NearOneAtanRemainder.atanRemainder 36 x| ≤
        |x| ^ 73 * (1 / 73 : ℝ) :=
      mul_le_mul_of_nonneg_left hRemainder (pow_nonneg (abs_nonneg x) _)
    _ = |x| ^ 73 / 73 := by ring

/-- Exact 160-bit dyadic enclosure used by scale-local expression replay. -/
def piInterval : QInterval :=
  ⟨2295721403524109460692402599871655564227077512209 /
      730750818665451459101842416358141509827966271488,
    4591442807048218921384805199743311128454155024419 /
      1461501637330902918203684832716283019655932542976,
    by norm_num⟩

/-- Machin's identity and the checked arctangent remainder certify the exact
160-bit dyadic `pi` enclosure used by the retained atlas checker. -/
theorem piInterval_sound : piInterval.RealContains Real.pi := by
  have h5 := abs_arctan_sub_atanSeries36_le (1 / 5 : ℝ)
  have h239 := abs_arctan_sub_atanSeries36_le (1 / 239 : ℝ)
  rw [abs_le] at h5 h239
  have hMachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hpi :
      Real.pi = 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
    rw [show (5 : ℝ)⁻¹ = 1 / 5 by norm_num,
      show (239 : ℝ)⁻¹ = 1 / 239 by norm_num] at hMachin
    linarith
  rw [hpi]
  constructor
  · calc
      (piInterval.lo : ℝ) ≤
          16 * (atanSeries36 (1 / 5) - (1 / 5 : ℝ) ^ 73 / 73) -
            4 * (atanSeries36 (1 / 239) + (1 / 239 : ℝ) ^ 73 / 73) := by
        norm_num [piInterval, atanSeries36]
      _ ≤ 16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) := by
        linarith [h5.1, h239.2]
  · calc
      16 * Real.arctan (1 / 5) - 4 * Real.arctan (1 / 239) ≤
          16 * (atanSeries36 (1 / 5) + (1 / 5 : ℝ) ^ 73 / 73) -
            4 * (atanSeries36 (1 / 239) - (1 / 239 : ℝ) ^ 73 / 73) := by
        linarith [h5.2, h239.1]
      _ ≤ (piInterval.hi : ℝ) := by
        norm_num [piInterval, atanSeries36]

/-! ## Scalar `R₃` interval replay -/

/-- The twenty exact coefficients retained by the scale-local checker, in
ascending powers of `x²`. -/
def atanRemainderThreeCoefficients20 : List ℚ :=
  [-1/7, 1/9, -1/11, 1/13, -1/15, 1/17, -1/19, 1/21, -1/23, 1/25,
    -1/27, 1/29, -1/31, 1/33, -1/35, 1/37, -1/39, 1/41, -1/43, 1/45]

/-- Horner evaluation used only for the one-variable remainder polynomial. -/
def rationalHorner : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: rest, y => (a : ℝ) + y * rationalHorner rest y

/-- Exact interval Horner evaluation. -/
def intervalHorner : List ℚ → QInterval → QInterval
  | [], _ => LeanSuffixReflective.QInterval.point 0
  | a :: rest, y => (LeanSuffixReflective.QInterval.point a).add
      (ScalarSuffixCertificate.QInterval.mul y (intervalHorner rest y))

/-- Interval Horner evaluation encloses the corresponding real polynomial. -/
theorem intervalHorner_sound (coefficients : List ℚ) (i : QInterval) {x : ℝ}
    (hx : i.RealContains x) :
    (intervalHorner coefficients i).RealContains
      (rationalHorner coefficients x) := by
  induction coefficients with
  | nil =>
      exact (LeanSuffixReflective.QInterval.realContains_point
        (0 : ℚ) (0 : ℝ)).2 (by norm_num)
  | cons a rest ih =>
      exact LeanSuffixReflective.QInterval.realContains_add
        ((LeanSuffixReflective.QInterval.realContains_point a (a : ℝ)).2 rfl)
        (ScalarSuffixCertificate.QInterval.realContains_mul hx ih)

/-- The explicit Horner polynomial is definitionally the retained twenty-term
finite expansion of `R₃`. -/
theorem atanRemainder_three_series20_eq_horner (x : ℝ) :
    (∑ j ∈ Finset.range 20,
      (-1 : ℝ) ^ (3 + j) * x ^ (2 * j) /
        (2 * (3 + j) + 1 : ℕ)) =
      rationalHorner atanRemainderThreeCoefficients20 (x ^ 2) := by
  norm_num [Finset.sum_range_succ, rationalHorner,
    atanRemainderThreeCoefficients20]
  ring

/-- Exact interval evaluation of the retained twenty-term scalar polynomial. -/
def atanRemainderThreeSeries20Interval (argument : QInterval) : QInterval :=
  intervalHorner atanRemainderThreeCoefficients20
    (ScalarSuffixCertificate.QInterval.mul argument argument)

/-- Soundness of the twenty-term scalar polynomial interval. -/
theorem atanRemainderThreeSeries20Interval_sound
    (argument : QInterval) {x : ℝ} (hx : argument.RealContains x) :
    (atanRemainderThreeSeries20Interval argument).RealContains
      (∑ j ∈ Finset.range 20,
        (-1 : ℝ) ^ (3 + j) * x ^ (2 * j) /
          (2 * (3 + j) + 1 : ℕ)) := by
  rw [atanRemainder_three_series20_eq_horner]
  apply intervalHorner_sound
  simpa [pow_two] using
    ScalarSuffixCertificate.QInterval.realContains_mul hx hx

/-- A generated scalar certificate supplies an argument interval, an absolute
argument bound `B`, and a rational result interval containing the exact Horner
range enlarged by the checked analytic tail `B^40/47`. -/
theorem atanRemainder_three_interval_sound
    (argument result : QInterval) (B : ℚ) {x : ℝ}
    (hx : argument.RealContains x)
    (hBnonneg : 0 ≤ B)
    (hloArg : -B ≤ argument.lo) (hhiArg : argument.hi ≤ B)
    (hlo :
      result.lo ≤
        (atanRemainderThreeSeries20Interval argument).lo - B ^ 40 / 47)
    (hhi :
      (atanRemainderThreeSeries20Interval argument).hi + B ^ 40 / 47 ≤
        result.hi) :
    result.RealContains (NearOneAtanRemainder.atanRemainder 3 x) := by
  have hlowArgR : (-(B : ℝ)) ≤ (argument.lo : ℝ) := by
    exact_mod_cast hloArg
  have hhighArgR : (argument.hi : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hhiArg
  have habs : |x| ≤ (B : ℝ) := by
    rw [abs_le]
    exact ⟨hlowArgR.trans hx.1, hx.2.trans hhighArgR⟩
  have htail := NearOneAtanRemainder.atanRemainder_three_tail_value_le
    (x := x) (B := (B : ℝ)) (by exact_mod_cast hBnonneg) habs
  have hseries := atanRemainderThreeSeries20Interval_sound argument hx
  rw [abs_le] at htail
  constructor
  · have hloR : (result.lo : ℝ) ≤
        ((atanRemainderThreeSeries20Interval argument).lo : ℝ) -
          (B : ℝ) ^ 40 / 47 := by
      exact_mod_cast hlo
    exact hloR.trans (by linarith [hseries.1, htail.1])
  · have hhiR :
        ((atanRemainderThreeSeries20Interval argument).hi : ℝ) +
            (B : ℝ) ^ 40 / 47 ≤
          (result.hi : ℝ) := by
      exact_mod_cast hhi
    have hvalue : NearOneAtanRemainder.atanRemainder 3 x ≤
        ((atanRemainderThreeSeries20Interval argument).hi : ℝ) +
          (B : ℝ) ^ 40 / 47 := by
      linarith [hseries.2, htail.2]
    exact hvalue.trans hhiR

end

end NearOneLocalInterval
