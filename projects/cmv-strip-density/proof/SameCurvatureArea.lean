/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import LeanSuffixAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

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
