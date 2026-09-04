/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Direct analytic reduction for the CMV suffix

This module records the exact scalar type-(iii) and type-(iv) quantities used
by the retained suffix checkers.  The main lemma eliminates the type-(iii)
angle from the equal-area perimeter comparison and then eliminates the
stationary type-(iv) angle.  Thus the remaining strict inequality is a single
explicit radical expression, rather than an unrelated arithmetic condition.
-/

open Real
open Filter
open scoped Topology

noncomputable section

namespace LeanSuffixAnalytic

/-- `q = 2h-1` in the regular type-(iii) parametrization. -/
def typeThreeShape (h : ℝ) : ℝ := 2 * h - 1

/-- The angle contribution in the exact type-(iii) formulas. -/
def typeThreeAngle (lam h : ℝ) : ℝ :=
  lam * arccos (typeThreeShape h / lam) + arcsin (typeThreeShape h)

/-- The radial displacement in the exact type-(iii) formulas. -/
def typeThreeDelta (lam h : ℝ) : ℝ :=
  sqrt (lam ^ 2 - typeThreeShape h ^ 2) / lam -
    sqrt (1 - typeThreeShape h ^ 2)

/-- Exact regular type-(iii) weighted area used by the suffix comparison. -/
def typeThreeArea (lam h : ℝ) : ℝ :=
  (typeThreeAngle lam h + π / 2 +
      (typeThreeShape h + 2) * typeThreeDelta lam h) / h ^ 2

/-- Exact regular type-(iii) weighted perimeter used by the suffix comparison. -/
def typeThreePerimeter (lam h : ℝ) : ℝ :=
  2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h) / h

/-- The angle contribution in the exact regular type-(iv) formulas. -/
def typeFourAngle (lam h : ℝ) : ℝ :=
  lam * arccos (h / lam) + arcsin h

/-- The radial displacement in the exact regular type-(iv) formulas. -/
def typeFourDelta (lam h : ℝ) : ℝ :=
  sqrt (lam ^ 2 - h ^ 2) / lam - sqrt (1 - h ^ 2)

/-- Exact regular type-(iv) weighted area used by the suffix comparison. -/
def typeFourArea (lam h : ℝ) : ℝ :=
  2 * (typeFourAngle lam h + h * typeFourDelta lam h) / h ^ 2

/-- Exact regular type-(iv) weighted perimeter used by the suffix comparison. -/
def typeFourPerimeter (lam h : ℝ) : ℝ :=
  4 * typeFourAngle lam h / h

/-- The checker numerator for the derivative of the regular type-(iii) area.
It is kept as one expression in the shared height argument so interval
evaluation does not decorrelate its repeated occurrences. -/
def typeThreeFold (lam h : ℝ) : ℝ :=
  4 * h * ((1 + typeThreeShape h) / sqrt (1 - typeThreeShape h ^ 2) -
    (lam ^ 2 + typeThreeShape h) /
      (lam * sqrt (lam ^ 2 - typeThreeShape h ^ 2))) -
    2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h)

/-- The stationary-fold equation for the regular type-(iv) profile. -/
def typeFourFold (lam h : ℝ) : ℝ :=
  4 * (h * (1 / sqrt (1 - h ^ 2) -
    lam / sqrt (lam ^ 2 - h ^ 2)) - typeFourAngle lam h)

/-- The radical expression left after equal-area and fold elimination. -/
def reducedFoldGap (lam h₃ h₄ : ℝ) : ℝ :=
  (h₃ - h₄) / h₄ *
      (1 / sqrt (1 - h₄ ^ 2) - lam / sqrt (lam ^ 2 - h₄ ^ 2)) +
    h₃ / h₄ * typeFourDelta lam h₄ - typeThreeDelta lam h₃

/-- Correlation-preserving centered mean-value identity.  Unlike a bound
assumed as part of a certificate schema, this produces the intermediate point
from the mean value theorem.  Every occurrence in `f' ξ` therefore shares the
same `ξ`, which is the analytic justification for evaluating a derivative
expression once on the whole height interval. -/
theorem centered_meanValue_exists
    (f f' : ℝ → ℝ) {c h : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc c h, HasDerivAt f (f' x) x) :
    ∃ ξ ∈ Set.uIcc c h, f h = f c + f' ξ * (h - c) := by
  rcases lt_trichotomy c h with hlt | heq | hgt
  · have hcont : ContinuousOn f (Set.Icc c h) := by
      intro x hx
      exact (hderiv x (Set.mem_uIcc.mpr (Or.inl hx))).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo c h) := by
      intro x hx
      exact (hderiv x (Set.mem_uIcc.mpr
        (Or.inl ⟨hx.1.le, hx.2.le⟩))).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f hlt hcont hdiff with ⟨ξ, hξ, hslope⟩
    have hξu : ξ ∈ Set.uIcc c h :=
      Set.mem_uIcc.mpr (Or.inl ⟨hξ.1.le, hξ.2.le⟩)
    refine ⟨ξ, hξu, ?_⟩
    rw [(hderiv ξ hξu).deriv] at hslope
    field_simp [ne_of_gt (sub_pos.mpr hlt)] at hslope
    linarith
  · subst h
    exact ⟨c, by simp, by ring⟩
  · have hcont : ContinuousOn f (Set.Icc h c) := by
      intro x hx
      exact (hderiv x (Set.mem_uIcc.mpr (Or.inr hx))).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ f (Set.Ioo h c) := by
      intro x hx
      exact (hderiv x (Set.mem_uIcc.mpr
        (Or.inr ⟨hx.1.le, hx.2.le⟩))).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope f hgt hcont hdiff with ⟨ξ, hξ, hslope⟩
    have hξu : ξ ∈ Set.uIcc c h :=
      Set.mem_uIcc.mpr (Or.inr ⟨hξ.1.le, hξ.2.le⟩)
    refine ⟨ξ, hξu, ?_⟩
    rw [(hderiv ξ hξu).deriv] at hslope
    field_simp [ne_of_gt (sub_pos.mpr hgt)] at hslope
    linarith
/-- The type-(iii) angle term is exactly the checkers' `B3` expression after
the substitution `q = cos w`. -/
theorem typeThreeAngle_add_halfPi (lam h : ℝ) :
    typeThreeAngle lam h + π / 2 =
      lam * arccos (typeThreeShape h / lam) + π -
        arccos (typeThreeShape h) := by
  rw [typeThreeAngle, Real.arcsin_eq_pi_div_two_sub_arccos]
  ring

/-- The type-(iv) angle term is exactly the checkers' `B4` expression after
the substitution `h = cos x`. -/
theorem typeFourAngle_eq_checker (lam h : ℝ) :
    typeFourAngle lam h =
      lam * arccos (h / lam) + π / 2 - arccos h := by
  rw [typeFourAngle, Real.arcsin_eq_pi_div_two_sub_arccos]
  ring

/-- Exact derivative of the affine type-(iii) shape parameter. -/
theorem hasDerivAt_typeThreeShape (h : ℝ) :
    HasDerivAt typeThreeShape 2 h := by
  unfold typeThreeShape
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id h).const_mul (2 : ℝ)).sub_const 1)

/-- Exact derivative of the regular type-(iii) angle contribution on its
natural open domain. -/
theorem hasDerivAt_typeThreeAngle {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreeAngle lam)
      (2 * (1 / sqrt (1 - typeThreeShape h ^ 2) -
        lam / sqrt (lam ^ 2 - typeThreeShape h ^ 2))) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hshape := hasDerivAt_typeThreeShape h
  have hq_low : -1 < typeThreeShape h := by
    unfold typeThreeShape
    linarith
  have hq_high : typeThreeShape h < 1 := by
    unfold typeThreeShape
    linarith
  have hu_arg : 0 < 1 - typeThreeShape h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - typeThreeShape h ^ 2 := by nlinarith
  have hd_ne : sqrt (lam ^ 2 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hratio_low : -1 < typeThreeShape h / lam :=
    (lt_div_iff₀ hlam_pos).2 (by linarith)
  have hratio_high : typeThreeShape h / lam < 1 :=
    (div_lt_one hlam_pos).2 (by linarith)
  have hratio_ne_neg_one : typeThreeShape h / lam ≠ -1 :=
    ne_of_gt hratio_low
  have hratio_ne_one : typeThreeShape h / lam ≠ 1 :=
    ne_of_lt hratio_high
  have hq_ne_neg_one : typeThreeShape h ≠ -1 := ne_of_gt hq_low
  have hq_ne_one : typeThreeShape h ≠ 1 := ne_of_lt hq_high
  have hsqrt_scale :
      sqrt (1 - (typeThreeShape h / lam) ^ 2) =
        sqrt (lam ^ 2 - typeThreeShape h ^ 2) / lam := by
    have hratio_identity :
        1 - (typeThreeShape h / lam) ^ 2 =
          (lam ^ 2 - typeThreeShape h ^ 2) / lam ^ 2 := by
      field_simp [hlam_ne]
    rw [hratio_identity, Real.sqrt_div hd_arg.le, Real.sqrt_sq_eq_abs,
      abs_of_pos hlam_pos]
  unfold typeThreeAngle
  have harccos :=
    (Real.hasDerivAt_arccos (x := typeThreeShape h / lam)
      hratio_ne_neg_one hratio_ne_one).comp h (hshape.div_const lam)
  have harcsin :=
    (Real.hasDerivAt_arcsin (x := typeThreeShape h)
      hq_ne_neg_one hq_ne_one).comp h hshape
  have hraw := (harccos.const_mul lam).add harcsin
  simpa only [Function.comp_apply, id_eq] using! hraw.congr_deriv (by
    rw [hsqrt_scale]
    field_simp [hlam_ne, hd_ne]
    ring)

/-- Exact derivative of the regular type-(iii) radial displacement on its
natural open domain. -/
theorem hasDerivAt_typeThreeDelta {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreeDelta lam)
      (2 * typeThreeShape h *
        (1 / sqrt (1 - typeThreeShape h ^ 2) -
          1 / (lam * sqrt (lam ^ 2 - typeThreeShape h ^ 2)))) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hshape := hasDerivAt_typeThreeShape h
  have hq_low : -1 < typeThreeShape h := by
    unfold typeThreeShape
    linarith
  have hq_high : typeThreeShape h < 1 := by
    unfold typeThreeShape
    linarith
  have hu_arg : 0 < 1 - typeThreeShape h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - typeThreeShape h ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  unfold typeThreeDelta
  have houter :=
    ((((hasDerivAt_const h (lam ^ 2)).sub (hshape.pow 2)).sqrt
      (ne_of_gt hd_arg)).div_const lam)
  have hinner :=
    (((hasDerivAt_const h 1).sub (hshape.pow 2)).sqrt (ne_of_gt hu_arg))
  have hraw := houter.sub hinner
  simpa only [id_eq] using! hraw.congr_deriv (by
    norm_num [id_eq, Pi.sub_apply, Pi.pow_apply]
    field_simp [hlam_ne, hu_ne, hd_ne]
    ring)

/-- Exact derivative of the regular type-(iv) angle contribution on its
natural open domain. -/
theorem hasDerivAt_typeFourAngle {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeFourAngle lam)
      (1 / sqrt (1 - h ^ 2) - lam / sqrt (lam ^ 2 - h ^ 2)) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hu_arg : 0 < 1 - h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - h ^ 2 := by nlinarith
  have hd_ne : sqrt (lam ^ 2 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hratio_pos : 0 < h / lam := div_pos hh hlam_pos
  have hratio_lt_one : h / lam < 1 :=
    (div_lt_one hlam_pos).2 (lt_trans hh1 hlam)
  have hratio_ne_neg_one : h / lam ≠ -1 := by linarith
  have hratio_ne_one : h / lam ≠ 1 := ne_of_lt hratio_lt_one
  have hh_ne_neg_one : h ≠ -1 := by linarith
  have hh_ne_one : h ≠ 1 := ne_of_lt hh1
  have hsqrt_scale :
      sqrt (1 - (h / lam) ^ 2) = sqrt (lam ^ 2 - h ^ 2) / lam := by
    have hratio_identity :
        1 - (h / lam) ^ 2 = (lam ^ 2 - h ^ 2) / lam ^ 2 := by
      field_simp [hlam_ne]
    rw [hratio_identity, Real.sqrt_div hd_arg.le, Real.sqrt_sq_eq_abs,
      abs_of_pos hlam_pos]
  unfold typeFourAngle
  have harccos :=
    (Real.hasDerivAt_arccos (x := h / lam) hratio_ne_neg_one
      hratio_ne_one).comp h ((hasDerivAt_id h).div_const lam)
  have harcsin :=
    Real.hasDerivAt_arcsin (x := h) hh_ne_neg_one hh_ne_one
  have hraw := (harccos.const_mul lam).add harcsin
  simpa only [Function.comp_apply, id_eq] using! hraw.congr_deriv (by
    rw [hsqrt_scale]
    field_simp [hlam_ne, hd_ne]
    ring)

/-- Exact derivative of the regular type-(iv) radial displacement on its
natural open domain. -/
theorem hasDerivAt_typeFourDelta {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeFourDelta lam)
      (h / sqrt (1 - h ^ 2) -
        h / (lam * sqrt (lam ^ 2 - h ^ 2))) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hu_arg : 0 < 1 - h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - h ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  unfold typeFourDelta
  have houter := ((((hasDerivAt_const h (lam ^ 2)).sub
    ((hasDerivAt_id h).pow 2)).sqrt (ne_of_gt hd_arg)).div_const lam)
  have hinner := (((hasDerivAt_const h 1).sub
    ((hasDerivAt_id h).pow 2)).sqrt (ne_of_gt hu_arg))
  have hraw := houter.sub hinner
  simpa only [id_eq] using! hraw.congr_deriv (by
    norm_num [id_eq, Pi.sub_apply, Pi.pow_apply]
    field_simp [hlam_ne, hu_ne, hd_ne]
    ring)

/-- The positive radical-cube gap on the positive half of the regular domain.
Its square witness is the exact factorization
`(lam²-x²) - lam²(1-x²) = x²(lam²-1)`. -/
private theorem radicalCubeGap_pos_of_pos {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    0 < 1 / sqrt (1 - x ^ 2) ^ 3 -
      lam / sqrt (lam ^ 2 - x ^ 2) ^ 3 := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_sq : 1 < lam ^ 2 := by
    have hfactor : 0 < (lam - 1) * (lam + 1) :=
      mul_pos (sub_pos.mpr hlam) (by linarith)
    nlinarith
  have hu_arg : 0 < 1 - x ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - x ^ 2 := by nlinarith
  have hu : 0 < sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hu_arg
  have hd : 0 < sqrt (lam ^ 2 - x ^ 2) := Real.sqrt_pos.2 hd_arg
  have hsquares :
      (lam * sqrt (1 - x ^ 2)) ^ 2 <
        sqrt (lam ^ 2 - x ^ 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
    nlinarith [sq_pos_of_pos hx, hlam_sq]
  have hradical :
      lam * sqrt (1 - x ^ 2) < sqrt (lam ^ 2 - x ^ 2) :=
    (sq_lt_sq₀ (mul_nonneg hlam_pos.le hu.le) hd.le).mp hsquares
  have hcubes := pow_lt_pow_left₀ hradical
    (mul_nonneg hlam_pos.le hu.le) (show (3 : ℕ) ≠ 0 by norm_num)
  have hlam_cube : lam < lam ^ 3 := by
    calc
      lam = lam * 1 := by ring
      _ < lam * lam ^ 2 := mul_lt_mul_of_pos_left hlam_sq hlam_pos
      _ = lam ^ 3 := by ring
  have hu_cube : 0 < sqrt (1 - x ^ 2) ^ 3 := pow_pos hu 3
  have hnumerator :
      lam * sqrt (1 - x ^ 2) ^ 3 <
        sqrt (lam ^ 2 - x ^ 2) ^ 3 := by
    calc
      lam * sqrt (1 - x ^ 2) ^ 3 <
          lam ^ 3 * sqrt (1 - x ^ 2) ^ 3 :=
        mul_lt_mul_of_pos_right hlam_cube hu_cube
      _ = (lam * sqrt (1 - x ^ 2)) ^ 3 := by ring
      _ < sqrt (lam ^ 2 - x ^ 2) ^ 3 := hcubes
  rw [sub_pos]
  exact (div_lt_div_iff₀ (pow_pos hd 3) (pow_pos hu 3)).2 (by
    simpa only [one_mul] using hnumerator)

/-- The positive radical-cube gap throughout the regular shape domain. -/
theorem radicalCubeGap_pos {lam x : ℝ}
    (hlam : 1 < lam) (hx : -1 < x) (hx1 : x < 1) :
    0 < 1 / sqrt (1 - x ^ 2) ^ 3 -
      lam / sqrt (lam ^ 2 - x ^ 2) ^ 3 := by
  rcases lt_trichotomy x 0 with hxneg | rfl | hxpos
  · have habs_pos : 0 < |x| := abs_pos.mpr (ne_of_lt hxneg)
    have habs_lt_one : |x| < 1 := (abs_lt).2 ⟨hx, hx1⟩
    simpa only [sq_abs] using
      radicalCubeGap_pos_of_pos hlam habs_pos habs_lt_one
  · have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
    have hlam_sq : 1 < lam ^ 2 := by nlinarith
    have hsqrt : sqrt (lam ^ 2) = lam := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hlam_pos]
    simp only [zero_pow (show (2 : ℕ) ≠ 0 by norm_num), sub_zero,
      Real.sqrt_one, one_pow]
    rw [hsqrt]
    have hquot : lam / lam ^ 3 = 1 / lam ^ 2 := by
      field_simp [hlam_ne]
    rw [hquot, sub_pos]
    simpa only [div_one] using
      (div_lt_one (sq_pos_of_pos hlam_pos)).2 hlam_sq
  · exact radicalCubeGap_pos_of_pos hlam hxpos hx1

/-- Exact derivative of the regular type-(iii) stationary-fold function on its
natural open domain. -/
theorem hasDerivAt_typeThreeFold {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreeFold lam)
      (16 * h ^ 2 * (1 / sqrt (1 - typeThreeShape h ^ 2) ^ 3 -
        lam / sqrt (lam ^ 2 - typeThreeShape h ^ 2) ^ 3)) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hq_low : -1 < typeThreeShape h := by
    unfold typeThreeShape
    linarith
  have hq_high : typeThreeShape h < 1 := by
    unfold typeThreeShape
    linarith
  have hu_arg : 0 < 1 - typeThreeShape h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - typeThreeShape h ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  let U := fun x : ℝ => 1 / sqrt (1 - typeThreeShape x ^ 2)
  let V := fun x : ℝ => (1 / sqrt (lam ^ 2 - typeThreeShape x ^ 2)) / lam
  have hshape := hasDerivAt_typeThreeShape h
  have hunitBase :
      HasDerivAt (fun x : ℝ => 1 / sqrt (1 - x ^ 2))
        (typeThreeShape h / sqrt (1 - typeThreeShape h ^ 2) ^ 3)
        (typeThreeShape h) := by
    have hraw := ((((hasDerivAt_const (typeThreeShape h) 1).sub
      ((hasDerivAt_id (typeThreeShape h)).pow 2)).sqrt
        (ne_of_gt hu_arg)).inv hu_ne)
    simpa only [one_div] using! hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
      field_simp [hu_ne]
      ring)
  have houterBase :
      HasDerivAt (fun x : ℝ => 1 / sqrt (lam ^ 2 - x ^ 2))
        (typeThreeShape h / sqrt (lam ^ 2 - typeThreeShape h ^ 2) ^ 3)
        (typeThreeShape h) := by
    have hraw := ((((hasDerivAt_const (typeThreeShape h) (lam ^ 2)).sub
      ((hasDerivAt_id (typeThreeShape h)).pow 2)).sqrt
        (ne_of_gt hd_arg)).inv hd_ne)
    simpa only [one_div] using! hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
      field_simp [hd_ne]
      ring)
  have hunit :
      HasDerivAt U
        (2 * typeThreeShape h / sqrt (1 - typeThreeShape h ^ 2) ^ 3) h := by
    simpa only [U, Function.comp_apply] using!
      (hunitBase.comp h hshape).congr_deriv (by ring)
  have hscaled :
      HasDerivAt V
        (2 * typeThreeShape h /
          (lam * sqrt (lam ^ 2 - typeThreeShape h ^ 2) ^ 3)) h := by
    simpa only [V, Function.comp_apply] using!
      ((houterBase.comp h hshape).div_const lam).congr_deriv (by
        field_simp [hlam_ne])
  have hA :=
    ((((hasDerivAt_const h 1).add hshape).mul hunit).sub
      (((hasDerivAt_const h (lam ^ 2)).add hshape).mul hscaled))
  have hangle := hasDerivAt_typeThreeAngle hlam hh hh1
  have hdelta := hasDerivAt_typeThreeDelta hlam hh hh1
  have hraw :=
    (((hasDerivAt_id h).mul hA).const_mul 4).sub
      (((hangle.add_const (π / 2)).add hdelta).const_mul 2)
  have hderiv : HasDerivAt _
      (16 * h ^ 2 * (1 / sqrt (1 - typeThreeShape h ^ 2) ^ 3 -
        lam / sqrt (lam ^ 2 - typeThreeShape h ^ 2) ^ 3)) h :=
    hraw.congr_deriv (by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, zero_add]
      dsimp only [U, V]
      simp only [id_eq]
      field_simp [hlam_ne, hu_ne, hd_ne]
      rw [Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
      unfold typeThreeShape
      ring)
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [] with x
  simp only [typeThreeFold, U, V, id_eq, Pi.add_apply, Pi.sub_apply,
    Pi.mul_apply]
  field_simp [hlam_ne]
/-- Exact derivative of the regular type-(iv) stationary-fold function on its
natural open domain. -/
theorem hasDerivAt_typeFourFold {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeFourFold lam)
      (4 * h ^ 2 * (1 / sqrt (1 - h ^ 2) ^ 3 -
        lam / sqrt (lam ^ 2 - h ^ 2) ^ 3)) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hu_arg : 0 < 1 - h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - h ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hunit :
      HasDerivAt (fun x : ℝ => 1 / sqrt (1 - x ^ 2))
        (h / sqrt (1 - h ^ 2) ^ 3) h := by
    have hraw := ((((hasDerivAt_const h 1).sub
      ((hasDerivAt_id h).pow 2)).sqrt (ne_of_gt hu_arg)).inv hu_ne)
    simpa only [one_div] using! hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
      field_simp [hu_ne]
      ring)
  have hscaled :
      HasDerivAt (fun x : ℝ => lam / sqrt (lam ^ 2 - x ^ 2))
        (lam * h / sqrt (lam ^ 2 - h ^ 2) ^ 3) h := by
    have hraw := (((((hasDerivAt_const h (lam ^ 2)).sub
      ((hasDerivAt_id h).pow 2)).sqrt (ne_of_gt hd_arg)).inv hd_ne).const_mul lam)
    simpa only [div_eq_mul_inv] using! hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply, Pi.pow_apply]
      field_simp [hd_ne]
      ring)
  have hangle := hasDerivAt_typeFourAngle hlam hh hh1
  have hraw :=
    (((hasDerivAt_id h).mul (hunit.sub hscaled)).sub hangle).const_mul 4
  simpa only [typeFourFold, id_eq] using! hraw.congr_deriv (by
    simp only [id_eq, Pi.sub_apply]
    ring)

/-- Exact derivative of the regular type-(iv) weighted area on its natural
open domain.  Its numerator is precisely the stationary-fold function. -/
theorem hasDerivAt_typeFourArea {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeFourArea lam) (typeFourFold lam h / h ^ 3) h := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hh_ne : h ≠ 0 := ne_of_gt hh
  have hu_arg : 0 < 1 - h ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - h ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hangle := hasDerivAt_typeFourAngle hlam hh hh1
  have hdelta := hasDerivAt_typeFourDelta hlam hh hh1
  have hdelta_key :
      h * (h / sqrt (1 - h ^ 2) -
          h / (lam * sqrt (lam ^ 2 - h ^ 2))) -
        typeFourDelta lam h =
      1 / sqrt (1 - h ^ 2) -
        lam / sqrt (lam ^ 2 - h ^ 2) := by
    unfold typeFourDelta
    calc
      h * (h / sqrt (1 - h ^ 2) -
            h / (lam * sqrt (lam ^ 2 - h ^ 2))) -
          (sqrt (lam ^ 2 - h ^ 2) / lam - sqrt (1 - h ^ 2)) =
          (h ^ 2 + sqrt (1 - h ^ 2) ^ 2) / sqrt (1 - h ^ 2) -
            (h ^ 2 + sqrt (lam ^ 2 - h ^ 2) ^ 2) /
              (lam * sqrt (lam ^ 2 - h ^ 2)) := by
        field_simp [hlam_ne, hu_ne, hd_ne]
        ring
      _ = 1 / sqrt (1 - h ^ 2) -
          lam / sqrt (lam ^ 2 - h ^ 2) := by
        rw [Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
        field_simp [hlam_ne, hu_ne, hd_ne]
        ring
  have hquotient_identity (B D p dp : ℝ) (hk : h * dp - D = p) :
      (2 * (p + (D + h * dp)) * h ^ 2 -
          2 * (B + h * D) * (2 * h)) / (h ^ 2) ^ 2 =
        4 * (h * p - B) / h ^ 3 := by
    rw [← hk]
    field_simp [hh_ne]
    ring
  have hnumerator :=
    (hangle.add ((hasDerivAt_id h).mul hdelta)).const_mul 2
  have hraw := hnumerator.div ((hasDerivAt_id h).pow 2)
    (pow_ne_zero 2 hh_ne)
  simpa only [typeFourArea, typeFourFold, id_eq] using! hraw.congr_deriv (by
    norm_num [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    exact hquotient_identity
      (typeFourAngle lam h) (typeFourDelta lam h)
      ((sqrt (1 - h ^ 2))⁻¹ -
        lam / sqrt (lam ^ 2 - h ^ 2))
      (h / sqrt (1 - h ^ 2) -
        h / (lam * sqrt (lam ^ 2 - h ^ 2)))
      (by simpa only [one_div] using hdelta_key))

/-- The regular type-(iii) area and perimeter are differentiable, and their
derivatives satisfy the exact variational identity `P₃' = h A₃'`. -/
theorem typeThree_variational_hasDerivAt {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreeArea lam) (deriv (typeThreeArea lam) h) h ∧
      HasDerivAt (typeThreePerimeter lam)
        (h * deriv (typeThreeArea lam) h) h := by
  let q := typeThreeShape h
  let D := typeThreeDelta lam h
  let p := 2 * (1 / sqrt (1 - q ^ 2) -
    lam / sqrt (lam ^ 2 - q ^ 2))
  let dp := 2 * q * (1 / sqrt (1 - q ^ 2) -
    1 / (lam * sqrt (lam ^ 2 - q ^ 2)))
  have hh_ne : h ≠ 0 := ne_of_gt hh
  have hshape := hasDerivAt_typeThreeShape h
  have hangle : HasDerivAt (typeThreeAngle lam) p h := by
    simpa only [p, q] using hasDerivAt_typeThreeAngle hlam hh hh1
  have hdelta : HasDerivAt (typeThreeDelta lam) dp h := by
    simpa only [dp, q] using hasDerivAt_typeThreeDelta hlam hh hh1
  have hq_arg : 0 < 1 - q ^ 2 := by
    dsimp only [q, typeThreeShape]
    nlinarith
  have hd_arg : 0 < lam ^ 2 - q ^ 2 := by
    have hlam_sq : 1 < lam ^ 2 := by nlinarith
    have hq_sq : q ^ 2 < 1 := by
      dsimp only [q, typeThreeShape]
      nlinarith
    linarith
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlam)
  have hq_ne : sqrt (1 - q ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq_arg)
  have hd_ne : sqrt (lam ^ 2 - q ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hkey : p - q * dp + 2 * D = 0 := by
    dsimp only [p, dp, D, typeThreeDelta]
    change
      2 * (1 / sqrt (1 - q ^ 2) - lam / sqrt (lam ^ 2 - q ^ 2)) -
        q * (2 * q * (1 / sqrt (1 - q ^ 2) -
          1 / (lam * sqrt (lam ^ 2 - q ^ 2)))) +
        2 * (sqrt (lam ^ 2 - q ^ 2) / lam - sqrt (1 - q ^ 2)) = 0
    field_simp [hlam_ne, hq_ne, hd_ne]
    ring_nf
    rw [Real.sq_sqrt hq_arg.le, Real.sq_sqrt hd_arg.le]
    ring
  have hB := hangle.add_const (π / 2)
  have hareaRaw :=
    (hB.add ((hshape.add_const 2).mul hdelta)).div
      ((hasDerivAt_id h).pow 2) (pow_ne_zero 2 hh_ne)
  have harea : HasDerivAt (typeThreeArea lam)
      (((p + (2 * D + (q + 2) * dp)) * h ^ 2 -
        (typeThreeAngle lam h + π / 2 + (q + 2) * D) * (2 * h)) /
          (h ^ 2) ^ 2) h := by
    simpa only [typeThreeArea, q, D, id_eq] using!
      hareaRaw.congr_deriv (by
        norm_num [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply])
  have hperimeterRaw :=
    ((hB.add hdelta).const_mul (2 : ℝ)).div (hasDerivAt_id h) hh_ne
  have hperimeter : HasDerivAt (typeThreePerimeter lam)
      (((2 * (p + dp)) * h -
        2 * (typeThreeAngle lam h + π / 2 + D)) / h ^ 2) h := by
    simpa only [typeThreePerimeter, D, id_eq] using!
      hperimeterRaw.congr_deriv (by
        norm_num [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply])
  refine ⟨harea.congr_deriv harea.deriv.symm, hperimeter.congr_deriv ?_⟩
  rw [harea.deriv]
  have halgebra : ∀ (q D p dp B h : ℝ), h ≠ 0 → q = 2 * h - 1 →
      p - q * dp + 2 * D = 0 →
      ((2 * (p + dp)) * h - 2 * (B + D)) / h ^ 2 =
        h * (((p + (2 * D + (q + 2) * dp)) * h ^ 2 -
          (B + (q + 2) * D) * (2 * h)) / (h ^ 2) ^ 2) := by
    intro q D p dp B h hh_ne hq hkey
    calc
      ((2 * (p + dp)) * h - 2 * (B + D)) / h ^ 2 =
          h * (((p + (2 * D + (q + 2) * dp)) * h ^ 2 -
            (B + (q + 2) * D) * (2 * h)) / (h ^ 2) ^ 2) +
            (p - q * dp + 2 * D) / h := by
              rw [hq]
              field_simp [hh_ne]
              ring
      _ = h * (((p + (2 * D + (q + 2) * dp)) * h ^ 2 -
          (B + (q + 2) * D) * (2 * h)) / (h ^ 2) ^ 2) := by
            rw [hkey]
            ring
  exact halgebra
    q D p dp (typeThreeAngle lam h + π / 2) h hh_ne (by
      simp only [q, typeThreeShape]) hkey

/-- Exact type-(iii) variational identity on the regular domain. -/
theorem typeThreePerimeter_deriv_eq_height_mul_area_deriv {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    deriv (typeThreePerimeter lam) h =
      h * deriv (typeThreeArea lam) h :=
  (typeThree_variational_hasDerivAt hlam hh hh1).2.deriv

/-- Explicit numerator for the type-(iii) area derivative.  This form is
designed for interval certificates: after replacing the two radicals by their
angle parametrizations, the numerator is exactly the checker quantity `K3`. -/
theorem typeThreeArea_deriv_eq_explicit {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    deriv (typeThreeArea lam) h =
      ((2 * (2 * (1 / sqrt (1 - typeThreeShape h ^ 2) -
          lam / sqrt (lam ^ 2 - typeThreeShape h ^ 2)) +
        2 * typeThreeShape h *
          (1 / sqrt (1 - typeThreeShape h ^ 2) -
            1 / (lam * sqrt (lam ^ 2 - typeThreeShape h ^ 2)))) * h -
        2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h)) /
          h ^ 3) := by
  let q := typeThreeShape h
  let p := 2 * (1 / sqrt (1 - q ^ 2) -
    lam / sqrt (lam ^ 2 - q ^ 2))
  let dp := 2 * q * (1 / sqrt (1 - q ^ 2) -
    1 / (lam * sqrt (lam ^ 2 - q ^ 2)))
  have hh_ne : h ≠ 0 := ne_of_gt hh
  have hangle : HasDerivAt (typeThreeAngle lam) p h := by
    simpa only [p, q] using hasDerivAt_typeThreeAngle hlam hh hh1
  have hdelta : HasDerivAt (typeThreeDelta lam) dp h := by
    simpa only [dp, q] using hasDerivAt_typeThreeDelta hlam hh hh1
  have hperimeterRaw :=
    (((hangle.add_const (π / 2)).add hdelta).const_mul (2 : ℝ)).div
      (hasDerivAt_id h) hh_ne
  have hperimeter : HasDerivAt (typeThreePerimeter lam)
      (((2 * (p + dp)) * h -
        2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h)) /
          h ^ 2) h := by
    simpa only [typeThreePerimeter, id_eq] using!
      hperimeterRaw.congr_deriv (by
        norm_num [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply])
  have hvariational :=
    typeThreePerimeter_deriv_eq_height_mul_area_deriv hlam hh hh1
  rw [hperimeter.deriv] at hvariational
  change deriv (typeThreeArea lam) h =
    (((2 * (p + dp)) * h -
      2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h)) /
        h ^ 3)
  apply (eq_div_iff (pow_ne_zero 3 hh_ne)).2
  calc
    deriv (typeThreeArea lam) h * h ^ 3 =
        (h * deriv (typeThreeArea lam) h) * h ^ 2 := by ring
    _ = (((2 * (p + dp)) * h -
        2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h)) /
          h ^ 2) * h ^ 2 := by rw [hvariational]
    _ = (2 * (p + dp)) * h -
        2 * (typeThreeAngle lam h + π / 2 + typeThreeDelta lam h) := by
      field_simp [hh_ne]


/-- The checker quantity `typeThreeFold` is exactly the numerator of the
type-(iii) area derivative. -/
theorem hasDerivAt_typeThreeArea {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreeArea lam) (typeThreeFold lam h / h ^ 3) h := by
  refine (typeThree_variational_hasDerivAt hlam hh hh1).1.congr_deriv ?_
  rw [typeThreeArea_deriv_eq_explicit hlam hh hh1]
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlam)
  have hq_arg : 0 < 1 - typeThreeShape h ^ 2 := by
    unfold typeThreeShape
    nlinarith
  have hd_arg : 0 < lam ^ 2 - typeThreeShape h ^ 2 := by
    have hlam_sq : 1 < lam ^ 2 := by nlinarith
    have hq_sq : typeThreeShape h ^ 2 < 1 := by
      unfold typeThreeShape
      nlinarith
    linarith
  have hu_ne : sqrt (1 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq_arg)
  have hd_ne : sqrt (lam ^ 2 - typeThreeShape h ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  unfold typeThreeFold
  field_simp [hlam_ne, hu_ne, hd_ne]
  ring

/-- The same type-(iii) fold numerator controls the perimeter derivative,
with one fewer power of the shared height. -/
theorem hasDerivAt_typeThreePerimeter {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreePerimeter lam) (typeThreeFold lam h / h ^ 2) h := by
  refine (typeThree_variational_hasDerivAt hlam hh hh1).2.congr_deriv ?_
  rw [(hasDerivAt_typeThreeArea hlam hh hh1).deriv]
  field_simp [ne_of_gt hh]
/-- The regular type-(iv) area and perimeter are differentiable, and their
derivatives satisfy the exact variational identity `P₄' = h A₄'`. -/
theorem typeFour_variational_hasDerivAt {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeFourArea lam) (deriv (typeFourArea lam) h) h ∧
      HasDerivAt (typeFourPerimeter lam)
        (h * deriv (typeFourArea lam) h) h := by
  have hh_ne : h ≠ 0 := ne_of_gt hh
  have hangle := hasDerivAt_typeFourAngle hlam hh hh1
  have hraw := (hangle.const_mul (4 : ℝ)).div (hasDerivAt_id h) hh_ne
  have hperimeter : HasDerivAt (typeFourPerimeter lam)
      ((4 * (1 / sqrt (1 - h ^ 2) - lam / sqrt (lam ^ 2 - h ^ 2)) * h -
        4 * typeFourAngle lam h) / h ^ 2) h := by
    simpa only [typeFourPerimeter, id_eq] using! hraw.congr_deriv (by
      simp only [id_eq]
      ring)
  have harea := hasDerivAt_typeFourArea hlam hh hh1
  refine ⟨harea.congr_deriv harea.deriv.symm, hperimeter.congr_deriv ?_⟩
  rw [harea.deriv]
  unfold typeFourFold
  field_simp [hh_ne]

/-- Exact type-(iv) variational identity on the regular domain. -/
theorem typeFourPerimeter_deriv_eq_height_mul_area_deriv {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    deriv (typeFourPerimeter lam) h =
      h * deriv (typeFourArea lam) h :=
  (typeFour_variational_hasDerivAt hlam hh hh1).2.deriv

/-- The type-(iv) perimeter derivative has the checker form `K₄ / h²`. -/
theorem hasDerivAt_typeFourPerimeter {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeFourPerimeter lam) (typeFourFold lam h / h ^ 2) h := by
  refine (typeFour_variational_hasDerivAt hlam hh hh1).2.congr_deriv ?_
  rw [(hasDerivAt_typeFourArea hlam hh hh1).deriv]
  field_simp [ne_of_gt hh]

private theorem uIcc_subset_regular {c h x : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hh : h ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.uIcc c h) : x ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases Set.mem_uIcc.mp hx with hx | hx
  · exact ⟨hc.1.trans_le hx.1, hx.2.trans_lt hh.2⟩
  · exact ⟨hh.1.trans_le hx.1, hx.2.trans_lt hc.2⟩

/-- Exact centered enclosure witness for the type-(iii) area.  In particular,
the fold numerator and all three denominator factors are evaluated at one
common intermediate height. -/
theorem typeThreeArea_centered_meanValue {lam c h : ℝ}
    (hlam : 1 < lam) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.uIcc c h,
      typeThreeArea lam h = typeThreeArea lam c +
        typeThreeFold lam ξ / ξ ^ 3 * (h - c) := by
  apply centered_meanValue_exists
  intro x hx
  have hxreg := uIcc_subset_regular hc hh hx
  exact hasDerivAt_typeThreeArea hlam hxreg.1 hxreg.2

/-- Exact centered enclosure witness for the type-(iii) perimeter. -/
theorem typeThreePerimeter_centered_meanValue {lam c h : ℝ}
    (hlam : 1 < lam) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.uIcc c h,
      typeThreePerimeter lam h = typeThreePerimeter lam c +
        typeThreeFold lam ξ / ξ ^ 2 * (h - c) := by
  apply centered_meanValue_exists
  intro x hx
  have hxreg := uIcc_subset_regular hc hh hx
  exact hasDerivAt_typeThreePerimeter hlam hxreg.1 hxreg.2

/-- Exact centered enclosure witness for the type-(iv) area. -/
theorem typeFourArea_centered_meanValue {lam c h : ℝ}
    (hlam : 1 < lam) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.uIcc c h,
      typeFourArea lam h = typeFourArea lam c +
        typeFourFold lam ξ / ξ ^ 3 * (h - c) := by
  apply centered_meanValue_exists
  intro x hx
  have hxreg := uIcc_subset_regular hc hh hx
  exact hasDerivAt_typeFourArea hlam hxreg.1 hxreg.2

/-- Exact centered enclosure witness for the type-(iv) perimeter. -/
theorem typeFourPerimeter_centered_meanValue {lam c h : ℝ}
    (hlam : 1 < lam) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.uIcc c h,
      typeFourPerimeter lam h = typeFourPerimeter lam c +
        typeFourFold lam ξ / ξ ^ 2 * (h - c) := by
  apply centered_meanValue_exists
  intro x hx
  have hxreg := uIcc_subset_regular hc hh hx
  exact hasDerivAt_typeFourPerimeter hlam hxreg.1 hxreg.2

/-- The regular type-(iii) weighted area diverges to `+∞` as the curvature
approaches zero from above.  The proof keeps the exact positive limiting
numerator and compares against a positive multiple of `h⁻¹`. -/
theorem typeThreeArea_tendsto_atRight_zero {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (typeThreeArea lam) (𝓝[>] 0) atTop := by
  let numerator : ℝ → ℝ := fun h =>
    typeThreeAngle lam h + π / 2 +
      (typeThreeShape h + 2) * typeThreeDelta lam h
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hrad : 0 < lam ^ 2 - 1 := by nlinarith
  have hnum_cont : ContinuousAt numerator 0 := by
    dsimp [numerator, typeThreeAngle, typeThreeDelta, typeThreeShape]
    fun_prop
  have hnum_zero : numerator 0 =
      lam * arccos (-1 / lam) + sqrt (lam ^ 2 - 1) / lam := by
    simp [numerator, typeThreeAngle, typeThreeDelta, typeThreeShape]
    ring
  have hC : 0 < numerator 0 := by
    rw [hnum_zero]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hlam_pos.le (Real.arccos_nonneg _))
      (div_pos (Real.sqrt_pos.2 hrad) hlam_pos)
  have hnum_tendsto : Tendsto numerator (𝓝[>] (0 : ℝ)) (𝓝 (numerator 0)) :=
    hnum_cont.tendsto.mono_left inf_le_left
  have hnum_lb : ∀ᶠ h in 𝓝[>] (0 : ℝ), numerator 0 / 2 < numerator h :=
    hnum_tendsto.eventually_const_lt (by linarith)
  have hsmall : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left
  have hlower : Tendsto (fun h : ℝ => numerator 0 / 2 * h⁻¹)
      (𝓝[>] 0) atTop :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by linarith)
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ hlower
  filter_upwards [hnum_lb, self_mem_nhdsWithin, hsmall] with h hnum hh hlt
  have hhpos : 0 < h := hh
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_pos hhpos
  have hsquare_le : h ^ 2 ≤ h := by nlinarith
  calc
    numerator 0 / 2 * h⁻¹ = numerator 0 / 2 / h := by
      simp only [div_eq_mul_inv]
    _ ≤ numerator 0 / 2 / h ^ 2 :=
      div_le_div_of_nonneg_left (by linarith) hsq_pos hsquare_le
    _ ≤ numerator h / h ^ 2 :=
      div_le_div₀ (by linarith) hnum.le hsq_pos le_rfl
    _ = typeThreeArea lam h := by rfl

/-- For `lam > 1`, the regular type-(iii) fold is strictly increasing
throughout the admissible height interval. -/
theorem typeThreeFold_strictMonoOn {lam : ℝ} (hlam : 1 < lam) :
    StrictMonoOn (typeThreeFold lam) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo (0 : ℝ) 1)
  · intro h hh
    exact
      (hasDerivAt_typeThreeFold hlam hh.1 hh.2).continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    exact (hasDerivAt_typeThreeFold hlam hh.1 hh.2).hasDerivWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    have hq_low : -1 < typeThreeShape h := by
      unfold typeThreeShape
      linarith [hh.1]
    have hq_high : typeThreeShape h < 1 := by
      unfold typeThreeShape
      linarith [hh.2]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hh.1))
      (radicalCubeGap_pos hlam hq_low hq_high)

/-- The regular type-(iii) fold has at most one zero in its admissible height
interval. -/
theorem typeThreeFold_zero_unique {lam h₁ h₂ : ℝ}
    (hlam : 1 < lam) (hh₁ : h₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hh₂ : h₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hz₁ : typeThreeFold lam h₁ = 0) (hz₂ : typeThreeFold lam h₂ = 0) :
    h₁ = h₂ := by
  apply (typeThreeFold_strictMonoOn hlam).injOn hh₁ hh₂
  exact hz₁.trans hz₂.symm

/-- Rolle's theorem turns two equal type-(iii) areas into a regular fold zero.
The right height may be the closure endpoint `b = 1`; the intermediate point
where the derivative vanishes is still in the regular open domain. -/
theorem typeThreeFold_zero_between_of_area_eq {lam a b : ℝ}
    (hlam : 1 < lam) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hb : b ∈ Set.Ioc (0 : ℝ) 1) (hab : a < b)
    (harea : typeThreeArea lam a = typeThreeArea lam b) :
    ∃ c ∈ Set.Ioo a b, typeThreeFold lam c = 0 := by
  have hcont : ContinuousOn (typeThreeArea lam) (Set.Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (ha.1.trans_le hx.1)
    unfold typeThreeArea typeThreeAngle typeThreeDelta typeThreeShape
    fun_prop (disch := simp_all)
  rcases exists_deriv_eq_zero hab hcont harea with ⟨c, hc, hzero⟩
  have hcreg : c ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨ha.1.trans hc.1, hc.2.trans_le hb.2⟩
  rw [(hasDerivAt_typeThreeArea hlam hcreg.1 hcreg.2).deriv] at hzero
  refine ⟨c, hc, ?_⟩
  exact (div_eq_zero_iff.mp hzero).resolve_right
    (pow_ne_zero 3 (ne_of_gt hcreg.1))

/-- A horizontal level meets the type-(iii) area profile at no more than two
heights in `0 < h ≤ 1`.  This includes a possible third height at the closure
endpoint. -/
theorem typeThreeArea_not_three_roots {lam a b c : ℝ}
    (hlam : 1 < lam) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (hb : b ∈ Set.Ioc (0 : ℝ) 1) (hc : c ∈ Set.Ioc (0 : ℝ) 1)
    (hab : a < b) (hbc : b < c) :
    ¬(typeThreeArea lam a = typeThreeArea lam b ∧
      typeThreeArea lam b = typeThreeArea lam c) := by
  intro hareas
  have hareg : a ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨ha.1, hab.trans_le hb.2⟩
  have hbreg : b ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hb.1, hbc.trans_le hc.2⟩
  rcases typeThreeFold_zero_between_of_area_eq
      hlam hareg hb hab hareas.1 with ⟨x, hx, hfoldX⟩
  rcases typeThreeFold_zero_between_of_area_eq
      hlam hbreg hc hbc hareas.2 with ⟨y, hy, hfoldY⟩
  have hxreg : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hareg.1.trans hx.1, hx.2.trans hbreg.2⟩
  have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hbreg.1.trans hy.1, hy.2.trans_le hc.2⟩
  have hmono := typeThreeFold_strictMonoOn
    hlam hxreg hyreg (hx.2.trans hy.1)
  rw [hfoldX, hfoldY] at hmono
  exact (lt_irrefl 0 hmono).elim

/-- A regular equal-area root with negative type-(iii) fold is the least root
of that horizontal level in `0 < h ≤ 1`.  Thus a certified negative-fold root
is globally identified as the descending root, not merely isolated in its
certificate slab. -/
theorem typeThreeArea_root_le_of_fold_neg {lam root y : ℝ}
    (hlam : 1 < lam) (hroot : root ∈ Set.Ioo (0 : ℝ) 1)
    (hy : y ∈ Set.Ioc (0 : ℝ) 1) (hfold : typeThreeFold lam root < 0)
    (harea : typeThreeArea lam root = typeThreeArea lam y) :
    root ≤ y := by
  apply le_of_not_gt
  intro hyroot
  have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hy.1, hyroot.trans hroot.2⟩
  rcases typeThreeFold_zero_between_of_area_eq
      hlam hyreg ⟨hroot.1, hroot.2.le⟩ hyroot harea.symm with
    ⟨c, hc, hfoldC⟩
  have hcreg : c ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hyreg.1.trans hc.1, hc.2.trans hroot.2⟩
  have hmono := typeThreeFold_strictMonoOn hlam hcreg hroot hc.2
  rw [hfoldC] at hmono
  linarith

/-- If one regular point on the descending type-(iii) branch lies below a
target area, the target is attained before that point. -/
private theorem typeThreeArea_descending_root_exists_below
    {lam anchor target : ℝ}
    (hlam : 1 < lam) (hanchor : anchor ∈ Set.Ioo (0 : ℝ) 1)
    (hfold : typeThreeFold lam anchor < 0)
    (htarget : typeThreeArea lam anchor ≤ target) :
    ∃ root : ℝ, root ∈ Set.Ioc (0 : ℝ) anchor ∧
      typeThreeArea lam root = target ∧ typeThreeFold lam root < 0 := by
  have hlarge :=
    (typeThreeArea_tendsto_atRight_zero hlam).eventually_gt_atTop target
  have hbelow : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < anchor :=
    (eventually_lt_nhds hanchor.1).filter_mono inf_le_left
  have hpositive : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h :=
    self_mem_nhdsWithin
  rcases (hlarge.and (hbelow.and hpositive)).exists with
    ⟨a, htarget_a, ha_anchor, ha_pos⟩
  have hcont : ContinuousOn (typeThreeArea lam) (Set.Icc a anchor) := by
    intro x hx
    exact (hasDerivAt_typeThreeArea hlam
      (ha_pos.trans_le hx.1) (hx.2.trans_lt hanchor.2)
    ).continuousAt.continuousWithinAt
  have htarget_mem :
      target ∈ Set.Icc (typeThreeArea lam anchor) (typeThreeArea lam a) :=
    ⟨htarget, htarget_a.le⟩
  rcases intermediate_value_Icc' ha_anchor.le hcont htarget_mem with
    ⟨root, hroot_interval, hroot_area⟩
  have hroot_mem : root ∈ Set.Ioc (0 : ℝ) anchor :=
    ⟨ha_pos.trans_le hroot_interval.1, hroot_interval.2⟩
  have hroot_fold : typeThreeFold lam root < 0 := by
    rcases hroot_interval.2.eq_or_lt with hroot_eq | hroot_lt
    · simpa [hroot_eq] using hfold
    · exact lt_trans
        (typeThreeFold_strictMonoOn hlam
          ⟨hroot_mem.1, hroot_lt.trans hanchor.2⟩ hanchor hroot_lt)
        hfold
  exact ⟨root, hroot_mem, hroot_area, hroot_fold⟩

/-- Every area above a negative-fold anchor has exactly one regular
negative-fold type-(iii) root.  This is the global descending root; uniqueness
is not restricted to the compact interval used by the existence proof. -/
theorem typeThreeArea_descending_root_existsUnique
    {lam anchor target : ℝ}
    (hlam : 1 < lam) (hanchor : anchor ∈ Set.Ioo (0 : ℝ) 1)
    (hfold : typeThreeFold lam anchor < 0)
    (htarget : typeThreeArea lam anchor ≤ target) :
    ∃! root : ℝ, root ∈ Set.Ioo (0 : ℝ) 1 ∧
      typeThreeArea lam root = target ∧ typeThreeFold lam root < 0 := by
  rcases typeThreeArea_descending_root_exists_below
      hlam hanchor hfold htarget with
    ⟨root, hroot_mem, hroot_area, hroot_fold⟩
  have hroot_regular : root ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hroot_mem.1, hroot_mem.2.trans_lt hanchor.2⟩
  refine ⟨root, ⟨hroot_regular, hroot_area, hroot_fold⟩, ?_⟩
  intro y hy
  apply le_antisymm
  · exact typeThreeArea_root_le_of_fold_neg
      (root := y) (y := root) hlam hy.1
      ⟨hroot_regular.1, hroot_regular.2.le⟩ hy.2.2
      (hy.2.1.trans hroot_area.symm)
  · exact typeThreeArea_root_le_of_fold_neg
      (root := root) (y := y) hlam hroot_regular
      ⟨hy.1.1, hy.1.2.le⟩ hroot_fold
      (hroot_area.trans hy.2.1.symm)

/-- Above a fixed equal-area root there is at most one further root in
`0 < h ≤ 1`.  Combined with `typeThreeArea_root_le_of_fold_neg`, this classifies
all roots as the certified descending root and at most one upper root. -/
theorem typeThreeArea_upper_root_unique {lam root y z : ℝ}
    (hlam : 1 < lam) (hroot : root ∈ Set.Ioc (0 : ℝ) 1)
    (hy : y ∈ Set.Ioc (0 : ℝ) 1) (hz : z ∈ Set.Ioc (0 : ℝ) 1)
    (hrootY : root < y) (hrootZ : root < z)
    (hareaY : typeThreeArea lam root = typeThreeArea lam y)
    (hareaZ : typeThreeArea lam root = typeThreeArea lam z) :
    y = z := by
  rcases lt_trichotomy y z with hyz | rfl | hzy
  · exact (typeThreeArea_not_three_roots hlam hroot hy hz hrootY hyz
      ⟨hareaY, hareaY.symm.trans hareaZ⟩).elim
  · rfl
  · exact (typeThreeArea_not_three_roots hlam hroot hz hy hrootZ hzy
      ⟨hareaZ, hareaZ.symm.trans hareaY⟩).elim

/-- For `lam > 1`, the regular type-(iv) fold is strictly increasing throughout
the admissible height interval. -/
theorem typeFourFold_strictMonoOn {lam : ℝ} (hlam : 1 < lam) :
    StrictMonoOn (typeFourFold lam) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo (0 : ℝ) 1)
  · intro h hh
    exact (hasDerivAt_typeFourFold hlam hh.1 hh.2).continuousAt.continuousWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    exact (hasDerivAt_typeFourFold hlam hh.1 hh.2).hasDerivWithinAt
  · intro h hh
    rw [interior_Ioo] at hh
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hh.1))
      (radicalCubeGap_pos hlam (by linarith [hh.1]) hh.2)

/-- Before a regular zero of the fold, the type-(iv) weighted area has
strictly negative derivative. -/
theorem typeFourArea_deriv_neg_before_zero {lam fold h : ℝ}
    (hlam : 1 < lam) (hfold : fold ∈ Set.Ioo (0 : ℝ) 1)
    (hzero : typeFourFold lam fold = 0)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) (hlt : h < fold) :
    deriv (typeFourArea lam) h < 0 := by
  rw [(hasDerivAt_typeFourArea hlam hh.1 hh.2).deriv]
  exact div_neg_of_neg_of_pos
    (by simpa [hzero] using typeFourFold_strictMonoOn hlam hh hfold hlt)
    (pow_pos hh.1 3)

/-- After a regular zero of the fold, the type-(iv) weighted area has
strictly positive derivative. -/
theorem typeFourArea_deriv_pos_after_zero {lam fold h : ℝ}
    (hlam : 1 < lam) (hfold : fold ∈ Set.Ioo (0 : ℝ) 1)
    (hzero : typeFourFold lam fold = 0)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) (hlt : fold < h) :
    0 < deriv (typeFourArea lam) h := by
  rw [(hasDerivAt_typeFourArea hlam hh.1 hh.2).deriv]
  exact div_pos
    (by simpa [hzero] using typeFourFold_strictMonoOn hlam hfold hh hlt)
    (pow_pos hh.1 3)

/-- A regular zero of the type-(iv) fold is a global minimum of the
type-(iv) area on `0 < h ≤ 1`, including the closure endpoint. -/
theorem typeFourArea_fold_le {lam fold h : ℝ} (hlam : 1 < lam)
    (hfold : fold ∈ Set.Ioo (0 : ℝ) 1)
    (hzero : typeFourFold lam fold = 0)
    (hh : h ∈ Set.Ioc (0 : ℝ) 1) :
    typeFourArea lam fold ≤ typeFourArea lam h := by
  rcases lt_trichotomy h fold with hlt | rfl | hgt
  · have hanti : StrictAntiOn (typeFourArea lam) (Set.Icc h fold) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc h fold)
      · intro x hx
        exact (hasDerivAt_typeFourArea hlam
          (hh.1.trans_le hx.1) (hx.2.trans_lt hfold.2)
        ).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact typeFourArea_deriv_neg_before_zero
          hlam hfold hzero
          ⟨hh.1.trans hx.1, hx.2.trans hfold.2⟩ hx.2
    exact (hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt).le
  · exact le_rfl
  · have hmono : StrictMonoOn (typeFourArea lam) (Set.Icc fold h) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc fold h)
      · intro x hx
        have hx0 : x ≠ 0 := ne_of_gt (hfold.1.trans_le hx.1)
        unfold typeFourArea typeFourAngle typeFourDelta
        fun_prop (disch := simp_all)
      · intro x hx
        rw [interior_Icc] at hx
        exact typeFourArea_deriv_pos_after_zero
          hlam hfold hzero
          ⟨hfold.1.trans hx.1, hx.2.trans_le hh.2⟩ hx.1
    exact (hmono ⟨le_rfl, hgt.le⟩ ⟨hgt.le, le_rfl⟩ hgt).le

/-- A stationary equal-area pair with negative type-(iii) fold constructs the
unique descending equal-area root for every regular or endpoint type-(iv)
curvature. -/
theorem typeThreeArea_descending_root_existsUnique_of_stationary_pair
    {lam h₃fold h₄fold h₄ : ℝ}
    (hlam : 1 < lam)
    (hh₃fold : h₃fold ∈ Set.Ioo (0 : ℝ) 1)
    (hh₄fold : h₄fold ∈ Set.Ioo (0 : ℝ) 1)
    (hh₄ : h₄ ∈ Set.Ioc (0 : ℝ) 1)
    (hfoldThree : typeThreeFold lam h₃fold < 0)
    (hfoldFour : typeFourFold lam h₄fold = 0)
    (hequalFold :
      typeThreeArea lam h₃fold = typeFourArea lam h₄fold) :
    ∃! root : ℝ, root ∈ Set.Ioo (0 : ℝ) 1 ∧
      typeThreeArea lam root = typeFourArea lam h₄ ∧
      typeThreeFold lam root < 0 := by
  apply typeThreeArea_descending_root_existsUnique
    hlam hh₃fold hfoldThree
  rw [hequalFold]
  exact typeFourArea_fold_le hlam hh₄fold hfoldFour hh₄

/-- The regular type-(iv) fold has at most one zero in its admissible height
interval. -/
theorem typeFourFold_zero_unique {lam h₁ h₂ : ℝ}
    (hlam : 1 < lam) (hh₁ : h₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hh₂ : h₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hz₁ : typeFourFold lam h₁ = 0) (hz₂ : typeFourFold lam h₂ = 0) :
    h₁ = h₂ := by
  apply (typeFourFold_strictMonoOn hlam).injOn hh₁ hh₂
  exact hz₁.trans hz₂.symm

/-- Closed lambda interval covered by the retained scalar suffix evidence. -/
def InRetainedSuffix (lam : ℝ) : Prop :=
  (51 / 50 : ℝ) ≤ lam ∧ lam ≤ 9 / 7

theorem InRetainedSuffix.one_lt {lam : ℝ} (h : InRetainedSuffix lam) :
    1 < lam := by
  unfold InRetainedSuffix at h
  norm_num at h ⊢
  linarith

/-- The retained suffix overlaps the existing `1.2581840884` exclusion and
extends beyond it to the rational seam `9/7`. -/
theorem existingCutoff_mem_retainedSuffix :
    InRetainedSuffix (1.2581840884 : ℝ) := by
  unfold InRetainedSuffix
  norm_num

/-- A selected stationary type-(iv) scalar and its descending-branch,
equal-area regular type-(iii) scalar. -/
structure StationaryEqualAreaPair (lam : ℝ) where
  h₃ : ℝ
  h₄ : ℝ
  h₃_gt_half : 1 / 2 < h₃
  h₃_lt_one : h₃ < 1
  h₄_pos : 0 < h₄
  h₄_lt_one : h₄ < 1
  equalArea : typeThreeArea lam h₃ = typeFourArea lam h₄
  stationary : typeFourFold lam h₄ = 0

/-- Concrete universal counter-obligation left by the direct reduction.  It
contains the exact cutoff, root equations, branch domains, and radical gap. -/
def ReducedGapNegativeOnRetainedSuffix : Prop :=
  ∀ (lam : ℝ), InRetainedSuffix lam →
    ∀ pair : StationaryEqualAreaPair lam,
      reducedFoldGap lam pair.h₃ pair.h₄ < 0


/-- Algebraic core of equal-area elimination, independent of the analytic
definitions of the four angle and displacement terms. -/
private theorem equalArea_gap_algebra {B₃ B₄ d₃ d₄ h₃ h₄ : ℝ}
    (hh₃ : h₃ ≠ 0) (hh₄ : h₄ ≠ 0)
    (harea : (B₃ + (2 * h₃ + 1) * d₃) / h₃ ^ 2 =
      2 * (B₄ + h₄ * d₄) / h₄ ^ 2) :
    2 * (B₃ + d₃) / h₃ - 4 * B₄ / h₄ =
      4 * (((h₃ - h₄) / h₄ ^ 2) * B₄ + h₃ / h₄ * d₄ - d₃) := by
  field_simp [hh₃, hh₄] at harea ⊢
  linear_combination 2 * harea

/-- Exact equal-area elimination.  It applies to the complete type-(iii)
formula on either side of `h₃ = 1/2`; no minor-arc branch is assumed. -/
theorem equalArea_gap_identity {lam h₃ h₄ : ℝ}
    (hh₃ : h₃ ≠ 0) (hh₄ : h₄ ≠ 0)
    (harea : typeThreeArea lam h₃ = typeFourArea lam h₄) :
    typeThreePerimeter lam h₃ - typeFourPerimeter lam h₄ =
      4 * (((h₃ - h₄) / h₄ ^ 2) * typeFourAngle lam h₄ +
        h₃ / h₄ * typeFourDelta lam h₄ - typeThreeDelta lam h₃) := by
  apply equalArea_gap_algebra hh₃ hh₄
  unfold typeThreeArea typeFourArea typeThreeShape at harea
  convert harea using 1
  all_goals ring

/-- At a stationary type-(iv) fold, the exact perimeter gap is four times the
single reduced radical expression. -/
theorem stationaryEqualArea_gap_identity {lam h₃ h₄ : ℝ}
    (hh₃ : h₃ ≠ 0) (hh₄ : h₄ ≠ 0)
    (harea : typeThreeArea lam h₃ = typeFourArea lam h₄)
    (hfold : typeFourFold lam h₄ = 0) :
    typeThreePerimeter lam h₃ - typeFourPerimeter lam h₄ =
      4 * reducedFoldGap lam h₃ h₄ := by
  rw [equalArea_gap_identity hh₃ hh₄ harea]
  unfold typeFourFold at hfold
  unfold reducedFoldGap
  have hangle : typeFourAngle lam h₄ =
      h₄ * (1 / sqrt (1 - h₄ ^ 2) -
        lam / sqrt (lam ^ 2 - h₄ ^ 2)) := by
    linarith
  rw [hangle]
  field_simp [hh₄]

/-- Precise remaining scalar obligation for a direct suffix proof: negativity
of the reduced fold gap is equivalent to strict type-(iii) improvement. -/
theorem stationaryEqualArea_typeThree_improves_iff {lam h₃ h₄ : ℝ}
    (hh₃ : h₃ ≠ 0) (hh₄ : h₄ ≠ 0)
    (harea : typeThreeArea lam h₃ = typeFourArea lam h₄)
    (hfold : typeFourFold lam h₄ = 0) :
    typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄ ↔
      reducedFoldGap lam h₃ h₄ < 0 := by
  rw [← sub_lt_zero]
  rw [stationaryEqualArea_gap_identity hh₃ hh₄ harea hfold]
  constructor <;> intro h <;> linarith


/-- Both strict radical inequalities used by the retained fold- and
equal-area-root uniqueness arguments follow uniformly from the suffix domain;
they do not require interval cells. -/
theorem StationaryEqualAreaPair.radicalCubeGaps {lam : ℝ}
    (hlam : InRetainedSuffix lam) (pair : StationaryEqualAreaPair lam) :
    (0 < 1 / sqrt (1 - typeThreeShape pair.h₃ ^ 2) ^ 3 -
      lam / sqrt (lam ^ 2 - typeThreeShape pair.h₃ ^ 2) ^ 3) ∧
    (0 < 1 / sqrt (1 - pair.h₄ ^ 2) ^ 3 -
      lam / sqrt (lam ^ 2 - pair.h₄ ^ 2) ^ 3) := by
  have hq_pos : 0 < typeThreeShape pair.h₃ := by
    unfold typeThreeShape
    linarith [pair.h₃_gt_half]
  have hq_lt_one : typeThreeShape pair.h₃ < 1 := by
    unfold typeThreeShape
    linarith [pair.h₃_lt_one]
  exact ⟨radicalCubeGap_pos hlam.one_lt (by linarith [hq_pos]) hq_lt_one,
    radicalCubeGap_pos hlam.one_lt (by linarith [pair.h₄_pos]) pair.h₄_lt_one⟩

/-- Exact scalar suffix contract.  Proving the single reduced radical
obligation is equivalent to proving strict type-(iii) perimeter improvement
for every selected stationary equal-area pair in `[51/50, 9/7]`. -/
theorem reducedGapNegative_iff_typeThreeImproves :
    ReducedGapNegativeOnRetainedSuffix ↔
      ∀ (lam : ℝ), InRetainedSuffix lam →
        ∀ pair : StationaryEqualAreaPair lam,
          typeThreePerimeter lam pair.h₃ <
            typeFourPerimeter lam pair.h₄ := by
  constructor
  · intro hgap lam hlam pair
    apply (stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) pair.h₃_gt_half))
      (ne_of_gt pair.h₄_pos) pair.equalArea pair.stationary).2
    exact hgap lam hlam pair
  · intro himproves lam hlam pair
    apply (stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) pair.h₃_gt_half))
      (ne_of_gt pair.h₄_pos) pair.equalArea pair.stationary).1
    exact himproves lam hlam pair

/-- Existence-and-sign obligation matching the retained scalar certificates:
each stationary regular type-(iv) scalar has a descending-branch equal-area
type-(iii) scalar with negative reduced gap. -/
def ReducedEqualAreaRootOnRetainedSuffix : Prop :=
  ∀ (lam h₄ : ℝ), InRetainedSuffix lam →
    0 < h₄ → h₄ < 1 → typeFourFold lam h₄ = 0 →
      ∃ h₃ : ℝ, 1 / 2 < h₃ ∧ h₃ < 1 ∧
        typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
        reducedFoldGap lam h₃ h₄ < 0

/-- The actual scalar equal-area competitor contract needed by integration,
before the separate geometric carrier and source-profile bridges. -/
def TypeThreeImprovementOnRetainedSuffix : Prop :=
  ∀ (lam h₄ : ℝ), InRetainedSuffix lam →
    0 < h₄ → h₄ < 1 → typeFourFold lam h₄ = 0 →
      ∃ h₃ : ℝ, 1 / 2 < h₃ ∧ h₃ < 1 ∧
        typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
        typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄

/-- Fold-gap elimination is exact even at the existential root-selection
level: no geometric or numerical premise is hidden in the reformulation. -/
theorem reducedEqualAreaRoot_iff_typeThreeImprovement :
    ReducedEqualAreaRootOnRetainedSuffix ↔
      TypeThreeImprovementOnRetainedSuffix := by
  constructor
  · intro hroot lam h₄ hlam hh₄ hh₄_one hfold
    rcases hroot lam h₄ hlam hh₄ hh₄_one hfold with
      ⟨h₃, hh₃, hh₃_one, harea, hgap⟩
    refine ⟨h₃, hh₃, hh₃_one, harea, ?_⟩
    exact (stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) hh₃)) (ne_of_gt hh₄)
      harea hfold).2 hgap
  · intro himproves lam h₄ hlam hh₄ hh₄_one hfold
    rcases himproves lam h₄ hlam hh₄ hh₄_one hfold with
      ⟨h₃, hh₃, hh₃_one, harea, himproves⟩
    refine ⟨h₃, hh₃, hh₃_one, harea, ?_⟩
    exact (stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) hh₃)) (ne_of_gt hh₄)
      harea hfold).1 himproves
end LeanSuffixAnalytic
