/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import LeanSuffixAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Deriv

/-!
# Same-curvature area comparison

This module proves that the exact regular type-(iii) area is strictly smaller
than the exact type-(iv) area at the same positive curvature.  It then uses the
negative-fold branch monotonicity to place every descending equal-area
type-(iii) root strictly below the corresponding type-(iv) curvature.
-/

open Real

noncomputable section

namespace LeanSuffixAnalytic

private def angleGap (lam x : ℝ) : ℝ :=
  typeFourAngle lam x - π / 2

private def sameCurvatureMargin (lam x : ℝ) : ℝ :=
  angleGap lam x - (2 - x) * typeFourDelta lam x

private theorem scaled_sqrt_lt {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    lam * sqrt (1 - x ^ 2) < sqrt (lam ^ 2 - x ^ 2) := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_sq : 1 < lam ^ 2 := by nlinarith
  have hu_arg : 0 < 1 - x ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - x ^ 2 := by nlinarith
  have hu : 0 < sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hu_arg
  have hd : 0 < sqrt (lam ^ 2 - x ^ 2) := Real.sqrt_pos.2 hd_arg
  apply (sq_lt_sq₀ (mul_nonneg hlam_pos.le hu.le) hd.le).mp
  rw [mul_pow, Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
  nlinarith [sq_pos_of_pos hx, hlam_sq]

private theorem angleGap_hasDerivAt {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (angleGap lam)
      (1 / sqrt (1 - x ^ 2) -
        lam / sqrt (lam ^ 2 - x ^ 2)) x := by
  exact (hasDerivAt_typeFourAngle hlam hx hx1).sub_const (π / 2)

private theorem angleGap_deriv_pos {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    0 < deriv (angleGap lam) x := by
  have hu_arg : 0 < 1 - x ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - x ^ 2 := by nlinarith
  have hu : 0 < sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hu_arg
  have hd : 0 < sqrt (lam ^ 2 - x ^ 2) := Real.sqrt_pos.2 hd_arg
  rw [(angleGap_hasDerivAt hlam hx hx1).deriv, sub_pos]
  exact (div_lt_div_iff₀ hd hu).2 (by
    simpa only [one_mul] using scaled_sqrt_lt hlam hx hx1)

private theorem angleGap_strictMonoOn {lam : ℝ} (hlam : 1 < lam) :
    StrictMonoOn (angleGap lam) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
  · intro x hx
    unfold angleGap typeFourAngle
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact angleGap_deriv_pos hlam hx.1 hx.2

private theorem typeFourDelta_deriv_pos {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    0 < deriv (typeFourDelta lam) x := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hu_arg : 0 < 1 - x ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - x ^ 2 := by nlinarith
  have hu : 0 < sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hu_arg
  have hd : 0 < sqrt (lam ^ 2 - x ^ 2) := Real.sqrt_pos.2 hd_arg
  have hu_lt_hd : sqrt (1 - x ^ 2) < sqrt (lam ^ 2 - x ^ 2) := by
    apply (sq_lt_sq₀ hu.le hd.le).mp
    rw [Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
    nlinarith [show 1 < lam ^ 2 by nlinarith]
  have hdenom : sqrt (1 - x ^ 2) <
      lam * sqrt (lam ^ 2 - x ^ 2) :=
    hu_lt_hd.trans (by nlinarith [mul_pos (sub_pos.mpr hlam) hd])
  rw [(hasDerivAt_typeFourDelta hlam hx hx1).deriv, sub_pos]
  exact (div_lt_div_iff₀ (mul_pos hlam_pos hd) hu).2
    (mul_lt_mul_of_pos_left hdenom hx)

private theorem typeFourDelta_strictMonoOn {lam : ℝ} (hlam : 1 < lam) :
    StrictMonoOn (typeFourDelta lam) (Set.Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
  · intro x hx
    unfold typeFourDelta
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact typeFourDelta_deriv_pos hlam hx.1 hx.2

private theorem typeFourDelta_nonneg {lam x : ℝ}
    (hlam : 1 < lam) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ typeFourDelta lam x := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hzero : typeFourDelta lam 0 = 0 := by
    simp [typeFourDelta, Real.sqrt_sq_eq_abs, abs_of_pos hlam_pos,
      ne_of_gt hlam_pos]
  rw [← hzero]
  exact (typeFourDelta_strictMonoOn hlam).monotoneOn
    (by norm_num) hx hx.1

private theorem sameCurvatureMargin_hasDerivAt {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (sameCurvatureMargin lam)
      (2 * (x - 1) *
        (x / sqrt (1 - x ^ 2) -
          x / (lam * sqrt (lam ^ 2 - x ^ 2)))) x := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hu_arg : 0 < 1 - x ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - x ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hraw := (angleGap_hasDerivAt hlam hx hx1).sub
    (((hasDerivAt_const x 2).sub (hasDerivAt_id x)).mul
      (hasDerivAt_typeFourDelta hlam hx hx1))
  simpa only [sameCurvatureMargin, id_eq] using! hraw.congr_deriv (by
    unfold typeFourDelta
    simp only [Pi.sub_apply, id_eq]
    field_simp [hlam_ne, hu_ne, hd_ne]
    ring_nf
    rw [Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
    ring)

private theorem sameCurvatureMargin_antitoneOn {lam : ℝ} (hlam : 1 < lam) :
    AntitoneOn (sameCurvatureMargin lam) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) 1)
  · intro x hx
    unfold sameCurvatureMargin angleGap typeFourAngle typeFourDelta
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact (sameCurvatureMargin_hasDerivAt
      hlam hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(sameCurvatureMargin_hasDerivAt hlam hx.1 hx.2).deriv]
    have hdpos := typeFourDelta_deriv_pos hlam hx.1 hx.2
    rw [(hasDerivAt_typeFourDelta hlam hx.1 hx.2).deriv] at hdpos
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (sub_nonpos.mpr hx.2.le))
      hdpos.le

private theorem sameCurvatureMargin_one_pos {lam : ℝ} (hlam : 1 < lam) :
    0 < sameCurvatureMargin lam 1 := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hrad : 0 ≤ lam ^ 2 - 1 := by nlinarith
  have hsqrt_scale :
      sqrt (1 - (1 / lam) ^ 2) = sqrt (lam ^ 2 - 1) / lam := by
    calc
      sqrt (1 - (1 / lam) ^ 2) =
          sqrt ((lam ^ 2 - 1) / lam ^ 2) := by
        congr 1
        field_simp [hlam_ne]
      _ = sqrt (lam ^ 2 - 1) / sqrt (lam ^ 2) := by
        rw [Real.sqrt_div hrad]
      _ = sqrt (lam ^ 2 - 1) / lam := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hlam_pos]
  have hratio_lt_one : 1 / lam < 1 :=
    (div_lt_one hlam_pos).2 hlam
  have htheta : 0 < arccos (1 / lam) :=
    Real.arccos_pos.mpr hratio_lt_one
  have hsin : sqrt (lam ^ 2 - 1) / lam < arccos (1 / lam) := by
    rw [← hsqrt_scale, ← Real.sin_arccos]
    exact Real.sin_lt htheta
  have hstrict : sqrt (lam ^ 2 - 1) / lam <
      lam * arccos (1 / lam) := by
    nlinarith [mul_pos (sub_pos.mpr hlam) htheta]
  unfold sameCurvatureMargin angleGap typeFourAngle typeFourDelta
  rw [Real.arcsin_one]
  norm_num
  simpa [one_div] using hstrict

private theorem angleGap_gt_mul_delta {lam x : ℝ}
    (hlam : 1 < lam) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 - x) * typeFourDelta lam x < angleGap lam x := by
  have hle := sameCurvatureMargin_antitoneOn hlam hx
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) hx.2
  have hpos := sameCurvatureMargin_one_pos hlam
  unfold sameCurvatureMargin at hle hpos
  linarith

private theorem angleGap_neg (lam x : ℝ) :
    angleGap lam (-x) = π * (lam - 1) - angleGap lam x := by
  unfold angleGap typeFourAngle
  rw [show -x / lam = -(x / lam) by ring,
    Real.arccos_neg, Real.arcsin_neg]
  ring

private theorem typeFourDelta_neg (lam x : ℝ) :
    typeFourDelta lam (-x) = typeFourDelta lam x := by
  unfold typeFourDelta
  congr 2 <;> ring_nf

private theorem area_normal_forms (lam h : ℝ) :
    typeThreeArea lam h =
        (π + angleGap lam (2 * h - 1) +
          (2 * h + 1) * typeFourDelta lam (2 * h - 1)) / h ^ 2 ∧
      typeFourArea lam h =
        (π + 2 * angleGap lam h +
          2 * h * typeFourDelta lam h) / h ^ 2 := by
  constructor
  · simp only [typeThreeArea, typeThreeAngle, typeThreeShape,
      typeThreeDelta, angleGap, typeFourAngle, typeFourDelta,
      Real.arcsin_eq_pi_div_two_sub_arccos]
    ring
  · simp only [typeFourArea, angleGap, typeFourAngle,
      Real.arcsin_eq_pi_div_two_sub_arccos]
    ring

/-- At fixed `lam > 1` and positive admissible curvature, the regular
 type-(iii) weighted area is strictly smaller than the type-(iv) weighted area.
 The statement includes the finite formula closure at `h = 1`. -/
theorem typeThreeArea_lt_typeFourArea {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h ≤ 1) :
    typeThreeArea lam h < typeFourArea lam h := by
  rw [(area_normal_forms lam h).1, (area_normal_forms lam h).2]
  apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hh)).2
  let q := 2 * h - 1
  have hhmem : h ∈ Set.Icc (0 : ℝ) 1 := ⟨hh.le, hh1⟩
  have hqb : -1 < q ∧ q ≤ h := by
    dsimp [q]
    constructor <;> linarith
  rcases le_total 0 q with hq | hq
  · have hqmem : q ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hq, hqb.2.trans hh1⟩
    have hF : angleGap lam q ≤ angleGap lam h :=
      (angleGap_strictMonoOn hlam).monotoneOn hqmem hhmem hqb.2
    have hd : typeFourDelta lam q ≤ typeFourDelta lam h :=
      (typeFourDelta_strictMonoOn hlam).monotoneOn hqmem hhmem hqb.2
    have hd0 := typeFourDelta_nonneg hlam hhmem
    have hk := angleGap_gt_mul_delta hlam hhmem
    change π + angleGap lam q + (2 * h + 1) * typeFourDelta lam q <
      π + 2 * angleGap lam h + 2 * h * typeFourDelta lam h
    nlinarith
  · have hxmem : -q ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> dsimp [q] at hqb hq ⊢ <;> linarith
    have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hF : angleGap lam 0 < angleGap lam h :=
      angleGap_strictMonoOn hlam hz hhmem hh
    have hd0 := typeFourDelta_nonneg hlam hhmem
    have hk := angleGap_gt_mul_delta hlam hxmem
    have hsF := angleGap_neg lam (-q)
    have hsd := typeFourDelta_neg lam (-q)
    have hF0 := angleGap_neg lam 0
    simp only [neg_neg] at hsF hsd
    simp only [neg_zero] at hF0
    change π + angleGap lam q + (2 * h + 1) * typeFourDelta lam q <
      π + 2 * angleGap lam h + 2 * h * typeFourDelta lam h
    dsimp [q] at hsF hsd hk ⊢
    nlinarith

/-- The support term whose concavity compares the two regular topologies at
the same curvature. -/
def typeFourSupport (lam x : ℝ) : ℝ :=
  typeFourAngle lam x - x * typeFourDelta lam x

/-- Exact derivative of the type-(iv) support term on the regular domain. -/
theorem typeFourSupport_hasDerivAt {lam x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (typeFourSupport lam) (-2 * typeFourDelta lam x) x := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hu_arg : 0 < 1 - x ^ 2 := by nlinarith
  have hd_arg : 0 < lam ^ 2 - x ^ 2 := by nlinarith
  have hu_ne : sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hu_arg)
  have hd_ne : sqrt (lam ^ 2 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hd_arg)
  have hraw := (hasDerivAt_typeFourAngle hlam hx hx1).sub
    ((hasDerivAt_id x).mul (hasDerivAt_typeFourDelta hlam hx hx1))
  simpa only [typeFourSupport, id_eq] using! hraw.congr_deriv (by
    simp only [id_eq]
    unfold typeFourDelta
    field_simp [hlam_ne, hu_ne, hd_ne]
    ring_nf
    rw [Real.sq_sqrt hu_arg.le, Real.sq_sqrt hd_arg.le]
    ring)

/-- The type-(iv) support term is concave on the complete closed regular
height interval.  Only interior derivatives are used. -/
theorem typeFourSupport_concaveOn {lam : ℝ} (hlam : 1 < lam) :
    ConcaveOn ℝ (Set.Icc 0 1) (typeFourSupport lam) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc (0 : ℝ) 1)
  · intro x hx
    unfold typeFourSupport typeFourAngle typeFourDelta
    fun_prop
  · intro x hx
    rw [interior_Icc] at hx
    exact (typeFourSupport_hasDerivAt
      hlam hx.1 hx.2).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    rw [interior_Icc] at hx hy
    rw [(typeFourSupport_hasDerivAt hlam hx.1 hx.2).deriv,
      (typeFourSupport_hasDerivAt hlam hy.1 hy.2).deriv]
    have hdelta := (typeFourDelta_strictMonoOn hlam).monotoneOn
      ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy
    nlinarith

/-- Strict endpoint margin for the support term. -/
theorem typeFourSupport_one_gt_halfPi {lam : ℝ} (hlam : 1 < lam) :
    π / 2 < typeFourSupport lam 1 := by
  have hmargin := sameCurvatureMargin_one_pos hlam
  unfold sameCurvatureMargin angleGap at hmargin
  unfold typeFourSupport
  norm_num at hmargin ⊢
  linarith

/-- Concavity at the exact midpoint `h = ((2h-1)+1)/2`. -/
theorem typeFourSupport_midpoint {lam h : ℝ}
    (hlam : 1 < lam) (hh : 1 / 2 < h) (hh1 : h < 1) :
    typeFourSupport lam (2 * h - 1) + typeFourSupport lam 1 ≤
      2 * typeFourSupport lam h := by
  let q := 2 * h - 1
  have hq0 : 0 < q := by
    dsimp only [q]
    linarith
  have hq1 : q < 1 := by
    dsimp only [q]
    linarith
  have hqh : q < h := by
    dsimp only [q]
    linarith
  have hslope := (typeFourSupport_concaveOn hlam).slope_anti_adjacent
    (show q ∈ Set.Icc (0 : ℝ) 1 from ⟨hq0.le, hq1.le⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) hqh hh1
  have hden : 0 < 1 - h := sub_pos.mpr hh1
  have hqden : h - q = 1 - h := by
    dsimp only [q]
    ring
  rw [hqden] at hslope
  have hnum := (div_le_div_iff_of_pos_right hden).mp hslope
  dsimp only [q] at hnum ⊢
  linarith

/-- Exact same-height identity relating the support terms to `P-hA`. -/
theorem sameHeight_support_identity (lam h : ℝ) (hh : h ≠ 0) :
    h * ((typeThreePerimeter lam h - h * typeThreeArea lam h) -
      (typeFourPerimeter lam h - h * typeFourArea lam h)) =
      typeFourSupport lam (2 * h - 1) + π / 2 -
        2 * typeFourSupport lam h := by
  unfold typeThreePerimeter typeThreeArea typeThreeAngle typeThreeShape
  unfold typeThreeDelta typeFourPerimeter typeFourArea typeFourSupport
  unfold typeFourAngle typeFourDelta
  unfold typeThreeShape
  field_simp [hh]
  ring

/-- At a common regular curvature above one half, the type-(iii) value of
`P-hA` is strictly smaller than the type-(iv) value. -/
theorem typeThree_support_lt_typeFour_support {lam h : ℝ}
    (hlam : 1 < lam) (hh : 1 / 2 < h) (hh1 : h < 1) :
    typeThreePerimeter lam h - h * typeThreeArea lam h <
      typeFourPerimeter lam h - h * typeFourArea lam h := by
  have hhpos : 0 < h := lt_trans (by norm_num) hh
  have hmid := typeFourSupport_midpoint hlam hh hh1
  have hend := typeFourSupport_one_gt_halfPi hlam
  have hnegative :
      typeFourSupport lam (2 * h - 1) + π / 2 -
          2 * typeFourSupport lam h < 0 := by
    nlinarith
  rw [← sameHeight_support_identity lam h (ne_of_gt hhpos)] at hnegative
  apply lt_of_not_ge
  intro hnonneg
  have hdiff : 0 ≤
      (typeThreePerimeter lam h - h * typeThreeArea lam h) -
        (typeFourPerimeter lam h - h * typeFourArea lam h) := by
    linarith
  exact (not_lt_of_ge (mul_nonneg hhpos.le hdiff)) hnegative

/-- The actual type-(iii) area is continuous at the closed height endpoint.
No endpoint fold value is used. -/
theorem typeThreeArea_continuousAt_one {lam : ℝ} (hlam : 1 < lam) :
    ContinuousAt (typeThreeArea lam) 1 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlam)
  unfold typeThreeArea typeThreeAngle typeThreeDelta typeThreeShape
  fun_prop (disch := simp_all)

/-- A type-(iii) area profile with increasing fold cannot exceed both endpoint
areas on a regular interval whose right endpoint may be the closed height
`b = 1`.  The endpoint case uses continuity of the source formula, never the
totalized fold at one. -/
theorem typeThreeArea_le_max_endpoints {lam a b x : ℝ}
    (hlam : 1 < lam) (ha : 0 < a) (hax : a ≤ x)
    (hxb : x ≤ b) (hb : b ≤ 1) :
    typeThreeArea lam x ≤
      max (typeThreeArea lam a) (typeThreeArea lam b) := by
  by_cases hx_one : x = 1
  · subst x
    have hb_one : b = 1 := le_antisymm hb hxb
    subst b
    exact le_max_right _ _
  have hx1 : x < 1 := lt_of_le_of_ne (hxb.trans hb) hx_one
  have hxreg : x ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨ha.trans_le hax, hx1⟩
  by_cases hxFold : typeThreeFold lam x ≤ 0
  · have hanti : AntitoneOn (typeThreeArea lam) (Set.Icc a x) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos
        (f' := fun y => typeThreeFold lam y / y ^ 3)
        (convex_Icc a x)
      · intro y hy
        have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨ha.trans_le hy.1, hy.2.trans_lt hx1⟩
        exact (hasDerivAt_typeThreeArea
          hlam hyreg.1 hyreg.2).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨ha.trans hy.1, hy.2.trans hx1⟩
        exact (hasDerivAt_typeThreeArea
          hlam hyreg.1 hyreg.2).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨ha.trans hy.1, hy.2.trans hx1⟩
        have hfold := (typeThreeFold_strictMonoOn hlam).monotoneOn
          hyreg hxreg hy.2.le
        exact div_nonpos_of_nonpos_of_nonneg
          (hfold.trans hxFold) (pow_pos hyreg.1 3).le
    exact (hanti ⟨le_rfl, hax⟩ ⟨hax, le_rfl⟩ hax).trans
      (le_max_left _ _)
  · have hxFoldPos : 0 < typeThreeFold lam x := lt_of_not_ge hxFold
    have hmono : MonotoneOn (typeThreeArea lam) (Set.Icc x b) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg
        (f' := fun y => typeThreeFold lam y / y ^ 3)
        (convex_Icc x b)
      · intro y hy
        by_cases hy_one : y = 1
        · subst y
          exact (typeThreeArea_continuousAt_one hlam).continuousWithinAt
        · have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
            ⟨hxreg.1.trans_le hy.1,
              lt_of_le_of_ne (hy.2.trans hb) hy_one⟩
          exact (hasDerivAt_typeThreeArea
            hlam hyreg.1 hyreg.2).continuousAt.continuousWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨hxreg.1.trans hy.1, hy.2.trans_le hb⟩
        exact (hasDerivAt_typeThreeArea
          hlam hyreg.1 hyreg.2).hasDerivWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨hxreg.1.trans hy.1, hy.2.trans_le hb⟩
        have hfold := (typeThreeFold_strictMonoOn hlam).monotoneOn
          hxreg hyreg hy.1.le
        exact div_nonneg (hxFoldPos.le.trans hfold)
          (pow_pos hyreg.1 3).le
    exact (hmono ⟨le_rfl, hxb⟩ ⟨hxb, le_rfl⟩ hxb).trans
      (le_max_right _ _)

def typeThreeAreaSupport (lam V x : ℝ) : ℝ :=
  typeThreePerimeter lam x + x * (V - typeThreeArea lam x)

theorem typeThreeAreaSupport_hasDerivAt {lam V x : ℝ}
    (hlam : 1 < lam) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (typeThreeAreaSupport lam V)
      (V - typeThreeArea lam x) x := by
  have hvar := typeThree_variational_hasDerivAt hlam hx hx1
  have hraw := hvar.2.add
    ((hasDerivAt_id x).mul ((hasDerivAt_const x V).sub hvar.1))
  simpa only [typeThreeAreaSupport, id_eq, Pi.sub_apply] using!
    hraw.congr_deriv (by
      simp only [id_eq, Pi.sub_apply]
      ring)

/-- The shared type-(iii) area-support function is continuous through the
closed endpoint on every interval bounded away from zero. -/
theorem typeThreeAreaSupport_continuousOn_Icc {lam V a b : ℝ}
    (hlam : 1 < lam) (ha : 0 < a) :
    ContinuousOn (typeThreeAreaSupport lam V) (Set.Icc a b) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlam)
  intro x hx
  have hx_ne : x ≠ 0 := ne_of_gt (ha.trans_le hx.1)
  apply ContinuousAt.continuousWithinAt
  unfold typeThreeAreaSupport typeThreePerimeter typeThreeArea
    typeThreeAngle typeThreeDelta typeThreeShape
  fun_prop (disch := simp_all)

/-- Universal equal-area transfer.  The only hypotheses are the regular
heights, their strict order, and actual equality of the two source areas; the
type-(iii) sublevel bound is derived internally from fold monotonicity. -/
theorem typeThreePerimeter_lt_typeFourPerimeter_of_equalArea
    {lam r h : ℝ}
    (hlam : 1 < lam) (hr : 1 / 2 < r) (hrh : r < h) (hh1 : h < 1)
    (harea : typeThreeArea lam r = typeFourArea lam h) :
    typeThreePerimeter lam r < typeFourPerimeter lam h := by
  have hrpos : 0 < r := lt_trans (by norm_num) hr
  have hhpos : 0 < h := hrpos.trans hrh
  have hsame := typeThreeArea_lt_typeFourArea hlam hhpos hh1.le
  have hareaHlt : typeThreeArea lam h < typeThreeArea lam r := by
    rw [harea]
    exact hsame
  have hsublevel : ∀ x ∈ Set.Icc r h,
      typeThreeArea lam x ≤ typeThreeArea lam r := by
    intro x hx
    have hbound := typeThreeArea_le_max_endpoints
      hlam hrpos hx.1 hx.2 hh1.le
    simpa [max_eq_left hareaHlt.le] using hbound
  have hsupport := typeThree_support_lt_typeFour_support
    hlam (hr.trans hrh) hh1
  have hmono : MonotoneOn
      (typeThreeAreaSupport lam (typeThreeArea lam r))
      (Set.Icc r h) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun x => typeThreeArea lam r - typeThreeArea lam x)
      (convex_Icc r h)
    · intro x hx
      have hxreg : x ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨hrpos.trans_le hx.1, hx.2.trans_lt hh1⟩
      exact (typeThreeAreaSupport_hasDerivAt
        hlam hxreg.1 hxreg.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxreg : x ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨hrpos.trans hx.1, hx.2.trans hh1⟩
      exact (typeThreeAreaSupport_hasDerivAt
        hlam hxreg.1 hxreg.2).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact sub_nonneg.mpr (hsublevel x ⟨hx.1.le, hx.2.le⟩)
  have hends := hmono
    (show r ∈ Set.Icc r h from ⟨le_rfl, hrh.le⟩)
    (show h ∈ Set.Icc r h from ⟨hrh.le, le_rfl⟩) hrh.le
  have hright :
      typeThreeAreaSupport lam (typeThreeArea lam r) h <
        typeFourPerimeter lam h := by
    unfold typeThreeAreaSupport
    rw [harea]
    linarith
  calc
    typeThreePerimeter lam r =
        typeThreeAreaSupport lam (typeThreeArea lam r) r := by
          unfold typeThreeAreaSupport
          ring
    _ ≤ typeThreeAreaSupport lam (typeThreeArea lam r) h := hends
    _ < typeFourPerimeter lam h := hright


/-- Conversely, an equal-area type-(iii) curvature below the compared
type-(iv) curvature lies on the negative-fold branch. -/
theorem typeThreeFold_neg_of_equalArea_of_lt
    {lam root h : ℝ}
    (hlam : 1 < lam)
    (hroot : root ∈ Set.Ioo (0 : ℝ) 1)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1)
    (hroot_lt : root < h)
    (harea : typeThreeArea lam root = typeFourArea lam h) :
    typeThreeFold lam root < 0 := by
  have hsame := typeThreeArea_lt_typeFourArea hlam hh.1 hh.2.le
  have harea_lt : typeThreeArea lam h < typeThreeArea lam root := by
    rw [harea]
    exact hsame
  rcases typeThreeArea_centered_meanValue hlam hroot hh with
    ⟨ξ, hξ, hmean⟩
  have hξIcc : ξ ∈ Set.Icc root h := by
    simpa [Set.uIcc_of_le hroot_lt.le] using hξ
  have hξreg : ξ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨hroot.1.trans_le hξIcc.1, hξIcc.2.trans_lt hh.2⟩
  have hfoldξ : typeThreeFold lam ξ < 0 := by
    apply lt_of_not_ge
    intro hnonneg
    have hquot : 0 ≤ typeThreeFold lam ξ / ξ ^ 3 :=
      div_nonneg hnonneg (pow_nonneg hξreg.1.le 3)
    have hterm : 0 ≤ typeThreeFold lam ξ / ξ ^ 3 * (h - root) :=
      mul_nonneg hquot (sub_nonneg.mpr hroot_lt.le)
    linarith
  exact lt_of_le_of_lt
    ((typeThreeFold_strictMonoOn hlam).monotoneOn
      hroot hξreg hξIcc.1) hfoldξ
/-- A regular negative-fold type-(iii) root at the type-(iv) area lies strictly
below the type-(iv) curvature.  This supplies the order invariant required by
the descending equal-area envelope. -/
theorem typeThreeArea_descending_root_lt
    {lam root h : ℝ}
    (hlam : 1 < lam)
    (hroot : root ∈ Set.Ioo (0 : ℝ) 1)
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hfold : typeThreeFold lam root < 0)
    (harea : typeThreeArea lam root = typeFourArea lam h) :
    root < h := by
  have hsame := typeThreeArea_lt_typeFourArea hlam hh hh1
  apply lt_of_not_ge
  intro hle
  have hne : h ≠ root := by
    intro heq
    subst root
    linarith
  have hlt : h < root := lt_of_le_of_ne hle hne
  have hanti : StrictAntiOn (typeThreeArea lam) (Set.Icc h root) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc h root)
    · intro y hy
      exact (hasDerivAt_typeThreeArea hlam
        (hh.trans_le hy.1) (hy.2.trans_lt hroot.2)
      ).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hyreg : y ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨hh.trans hy.1, hy.2.trans hroot.2⟩
      rw [(hasDerivAt_typeThreeArea hlam hyreg.1 hyreg.2).deriv]
      exact div_neg_of_neg_of_pos
        (lt_trans (typeThreeFold_strictMonoOn hlam hyreg hroot hy.2) hfold)
        (pow_pos hyreg.1 3)
  have hc := hanti
    (show h ∈ Set.Icc h root from ⟨le_rfl, hle⟩)
    (show root ∈ Set.Icc h root from ⟨hle, le_rfl⟩) hlt
  rw [harea] at hc
  linarith

end LeanSuffixAnalytic
