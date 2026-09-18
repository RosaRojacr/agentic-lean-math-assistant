/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import LeanSuffixAnalytic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A universal stationary type-(iv) height

The raw type-(iv) fold is singular at height `1`.  This module clears its two
radical denominators before taking the endpoint, proves opposite endpoint signs,
and applies the intermediate value theorem to recover a regular zero of the
actual source fold.
-/

open Real
open scoped Topology

noncomputable section

namespace LeanSuffixAnalytic

/-- The denominator-free extension of the type-(iv) fold numerator. -/
def typeFourClearedFold (lam h : ℝ) : ℝ :=
  h * (sqrt (lam ^ 2 - h ^ 2) - lam * sqrt (1 - h ^ 2)) -
    typeFourAngle lam h * sqrt (1 - h ^ 2) * sqrt (lam ^ 2 - h ^ 2)

/-- The cleared fold is continuous even at the singular endpoint `h = 1`. -/
theorem typeFourClearedFold_continuous (lam : ℝ) :
    Continuous (typeFourClearedFold lam) := by
  unfold typeFourClearedFold typeFourAngle
  fun_prop

/-- Closed-interval continuity used by the endpoint-sign IVT. -/
theorem typeFourClearedFold_continuousOn (lam : ℝ) :
    ContinuousOn (typeFourClearedFold lam) (Set.Icc (9 / 10 : ℝ) 1) :=
  (typeFourClearedFold_continuous lam).continuousOn

/-- On the regular domain, the cleared expression is the actual source fold
multiplied by its two positive radical denominators. -/
theorem typeFourClearedFold_eq_fold {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    typeFourClearedFold lam h =
      sqrt (1 - h ^ 2) * sqrt (lam ^ 2 - h ^ 2) *
        typeFourFold lam h / 4 := by
  have hu_arg : 0 < 1 - h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - h ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - h ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - h ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd_arg)
  unfold typeFourClearedFold typeFourFold
  field_simp [hu_ne, hd_ne]

/-- The multiplier relating the cleared expression to the source fold is
strictly positive throughout the regular domain. -/
theorem typeFourClearedFold_multiplier_pos {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    0 < sqrt (1 - h ^ 2) * sqrt (lam ^ 2 - h ^ 2) / 4 := by
  have hu_arg : 0 < 1 - h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - h ^ 2 := by nlinarith
  positivity

private theorem typeFourFold_nine_tenths_neg {lam : ℝ} (hlam : 1 < lam) :
    typeFourFold lam (9 / 10 : ℝ) < 0 := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  let u : ℝ := sqrt (1 - (9 / 10 : ℝ) ^ 2)
  let d : ℝ := sqrt (lam ^ 2 - (9 / 10 : ℝ) ^ 2)
  have hu_arg : 0 < 1 - (9 / 10 : ℝ) ^ 2 := by norm_num
  have hd_arg : 0 < lam ^ 2 - (9 / 10 : ℝ) ^ 2 := by nlinarith
  have hu : 0 < u := Real.sqrt_pos.2 hu_arg
  have hd : 0 < d := Real.sqrt_pos.2 hd_arg
  have hu_lower : (2 / 5 : ℝ) < u := by
    apply (sq_lt_sq₀ (by norm_num) hu.le).mp
    rw [show u ^ 2 = 1 - (9 / 10 : ℝ) ^ 2 by
      exact Real.sq_sqrt hu_arg.le]
    norm_num
  have hd_le_lam : d ≤ lam := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hlam_pos.le
    · norm_num
  have hlam_div_d : (1 : ℝ) ≤ lam / d := by
    exact (le_div_iff₀ hd).2 (by simpa using hd_le_lam)
  have hone_div_u : (1 : ℝ) / u < 5 / 2 := by
    apply (div_lt_iff₀ hu).2
    nlinarith
  have hratio : (9 / 10 : ℝ) / lam ≤ 9 / 10 := by
    apply (div_le_iff₀ hlam_pos).2
    nlinarith
  have hacos_order :
      arccos (9 / 10 : ℝ) ≤ arccos ((9 / 10 : ℝ) / lam) :=
    Real.arccos_le_arccos hratio
  have hacos_nonneg : 0 ≤ arccos ((9 / 10 : ℝ) / lam) :=
    Real.arccos_nonneg _
  have hacos_scaled :
      arccos ((9 / 10 : ℝ) / lam) ≤
        lam * arccos ((9 / 10 : ℝ) / lam) := by
    nlinarith
  have hangle : π / 2 ≤ typeFourAngle lam (9 / 10 : ℝ) := by
    rw [typeFourAngle, Real.arcsin_eq_pi_div_two_sub_arccos]
    linarith
  have hfirst :
      (9 / 10 : ℝ) * ((1 : ℝ) / u - lam / d) < 27 / 20 := by
    nlinarith
  have hpi : (27 / 20 : ℝ) < π / 2 := by
    nlinarith [Real.pi_gt_three]
  unfold typeFourFold
  change 4 * ((9 / 10 : ℝ) * ((1 : ℝ) / u - lam / d) -
    typeFourAngle lam (9 / 10 : ℝ)) < 0
  nlinarith

/-- The cleared fold is strictly negative at the fixed regular left endpoint. -/
theorem typeFourClearedFold_nine_tenths_neg {lam : ℝ} (hlam : 1 < lam) :
    typeFourClearedFold lam (9 / 10 : ℝ) < 0 := by
  rw [typeFourClearedFold_eq_fold hlam (by norm_num) (by norm_num)]
  calc
    _ = (sqrt (1 - (9 / 10 : ℝ) ^ 2) *
        sqrt (lam ^ 2 - (9 / 10 : ℝ) ^ 2) / 4) *
          typeFourFold lam (9 / 10 : ℝ) := by ring
    _ < 0 := mul_neg_of_pos_of_neg
      (typeFourClearedFold_multiplier_pos hlam (by norm_num) (by norm_num))
      (typeFourFold_nine_tenths_neg hlam)

/-- The endpoint value is the surviving outer radical and is strictly positive.
No value of the singular raw fold at `h = 1` is used. -/
theorem typeFourClearedFold_one_pos {lam : ℝ} (hlam : 1 < lam) :
    0 < typeFourClearedFold lam 1 := by
  have hrad : 0 < lam ^ 2 - 1 := by nlinarith
  simpa [typeFourClearedFold] using Real.sqrt_pos.2 hrad

/-- Every density `lam > 1` has a regular stationary type-(iv) height strictly
between `9/10` and `1`. -/
theorem typeFourFold_zero_exists {lam : ℝ} (hlam : 1 < lam) :
    ∃ h : ℝ, 9 / 10 < h ∧ h < 1 ∧ typeFourFold lam h = 0 := by
  have hcont : ContinuousOn (typeFourClearedFold lam)
      (Set.Icc (9 / 10 : ℝ) 1) :=
    typeFourClearedFold_continuousOn lam
  have htarget : (0 : ℝ) ∈ Set.Icc
      (typeFourClearedFold lam (9 / 10 : ℝ))
      (typeFourClearedFold lam 1) :=
    ⟨(typeFourClearedFold_nine_tenths_neg hlam).le,
      (typeFourClearedFold_one_pos hlam).le⟩
  rcases intermediate_value_Icc (show (9 / 10 : ℝ) ≤ 1 by norm_num)
      hcont htarget with ⟨h, hh, hzero⟩
  have hh_left : (9 / 10 : ℝ) < h := by
    apply lt_of_le_of_ne hh.1
    intro heq
    subst h
    linarith [typeFourClearedFold_nine_tenths_neg hlam]
  have hh_right : h < 1 := by
    apply lt_of_le_of_ne hh.2
    intro heq
    subst h
    linarith [typeFourClearedFold_one_pos hlam]
  have hfactor_pos := typeFourClearedFold_multiplier_pos
    hlam (by linarith) hh_right
  have hproduct :
      (sqrt (1 - h ^ 2) * sqrt (lam ^ 2 - h ^ 2) / 4) *
        typeFourFold lam h = 0 := by
    calc
      _ = typeFourClearedFold lam h := by
        rw [typeFourClearedFold_eq_fold hlam (by linarith) hh_right]
        ring
      _ = 0 := hzero
  exact ⟨h, hh_left, hh_right,
    (mul_eq_zero.mp hproduct).resolve_left (ne_of_gt hfactor_pos)⟩

end LeanSuffixAnalytic
