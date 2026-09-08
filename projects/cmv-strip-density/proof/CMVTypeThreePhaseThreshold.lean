/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFiveAngular
import Mathlib.Analysis.Convex.Deriv

/-!
# Type-(ii)/type-(iii) support-gap threshold

This module proves the scalar type-(ii)/type-(iii) phase comparison using the
actual type-(iii) area and perimeter formulas: the support-gap derivative and
endpoint values, the unique crossing height, its complete strict sign
partition, and the resulting phase threshold above `π`.  No value or
derivative of the singular fold at `h = 1` is used.
-/

open Set
open Real

noncomputable section

namespace LeanSuffixAnalytic

/-- Difference between the actual type-(iii) perimeter and the type-(ii)
support line `V + π` at the same scalar area. -/
def typeThreeSupportGap (lam h : ℝ) : ℝ :=
  typeThreePerimeter lam h - typeThreeArea lam h - π

/-- Exact regular derivative of the actual support gap. -/
theorem typeThreeSupportGap_hasDerivAt {lam h : ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1) :
    HasDerivAt (typeThreeSupportGap lam)
      ((h - 1) * typeThreeFold lam h / h ^ 3) h := by
  have hperimeter := hasDerivAt_typeThreePerimeter hlam hh hh1
  have harea := hasDerivAt_typeThreeArea hlam hh hh1
  have hraw := (hperimeter.sub harea).sub_const π
  simpa only [typeThreeSupportGap] using! hraw.congr_deriv (by
    field_simp [ne_of_gt hh])

/-- At half height, the type-(iii) perimeter equals its area, so the support
gap is exactly `-π`. -/
theorem typeThreeSupportGap_half {lam : ℝ} (hlam : 1 < lam) :
    typeThreeSupportGap lam (1 / 2) = -π := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  unfold typeThreeSupportGap typeThreePerimeter typeThreeArea typeThreeAngle
    typeThreeDelta typeThreeShape
  norm_num [Real.sqrt_sq_eq_abs, abs_of_pos hlam_pos, ne_of_gt hlam_pos]
  ring

/-- The actual finite area and perimeter formulas make the support gap
continuous at the closed endpoint.  This does not evaluate the fold there. -/
theorem typeThreeSupportGap_continuousAt_one {lam : ℝ} (hlam : 1 < lam) :
    ContinuousAt (typeThreeSupportGap lam) 1 := by
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlam)
  have hperimeter : ContinuousAt (typeThreePerimeter lam) 1 := by
    unfold typeThreePerimeter typeThreeAngle typeThreeDelta typeThreeShape
    fun_prop (disch := simp_all)
  exact (hperimeter.sub (typeThreeArea_continuousAt_one hlam)).sub_const π

/-- The closed endpoint support gap is the positive angular endpoint gap. -/
theorem typeThreeSupportGap_one_eq_endpointGap {lam : ℝ} (hlam : 1 < lam) :
    typeThreeSupportGap lam 1 = CMVFigureFive.endpointGap lam := by
  unfold typeThreeSupportGap
  rw [CMVFigureFive.typeThree_endpoint_support hlam]
  ring

/-- The actual support gap is strictly positive at the closed endpoint. -/
theorem typeThreeSupportGap_one_pos {lam : ℝ} (hlam : 1 < lam) :
    0 < typeThreeSupportGap lam 1 := by
  rw [typeThreeSupportGap_one_eq_endpointGap hlam]
  exact CMVFigureFive.endpointGap_pos hlam

/-- A nonpositive support gap can occur only on the negative-fold branch.
The proof compares to the positive continuous endpoint and never evaluates the
fold at `h = 1`. -/
theorem typeThreeFold_neg_of_supportGap_nonpos {lam h : ℝ}
    (hlam : 1 < lam) (hh : h ∈ Ioo (0 : ℝ) 1)
    (hgap : typeThreeSupportGap lam h ≤ 0) :
    typeThreeFold lam h < 0 := by
  apply lt_of_not_ge
  intro hfold
  have hanti : StrictAntiOn (typeThreeSupportGap lam) (Icc h 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc h (1 : ℝ))
    · intro x hx
      by_cases hx1 : x = 1
      · subst x
        exact (typeThreeSupportGap_continuousAt_one hlam).continuousWithinAt
      · have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
          ⟨hh.1.trans_le hx.1, lt_of_le_of_ne hx.2 hx1⟩
        exact (typeThreeSupportGap_hasDerivAt
          hlam hxreg.1 hxreg.2).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
        ⟨hh.1.trans hx.1, hx.2⟩
      rw [(typeThreeSupportGap_hasDerivAt
        hlam hxreg.1 hxreg.2).deriv]
      have hfoldx : 0 < typeThreeFold lam x :=
        lt_of_le_of_lt hfold
          (typeThreeFold_strictMonoOn hlam hh hxreg hx.1)
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (sub_neg.mpr hx.2) hfoldx)
        (pow_pos hxreg.1 3)
  have hendpoint_lt :
      typeThreeSupportGap lam 1 < typeThreeSupportGap lam h :=
    hanti ⟨le_rfl, hh.2.le⟩ ⟨hh.2.le, le_rfl⟩ hh.2
  linarith [typeThreeSupportGap_one_pos hlam]

/-- On the half-height-to-endpoint range, the actual type-(iii) area is
strictly above `π`. -/
theorem typeThreeArea_gt_pi_of_half_le {lam h : ℝ}
    (hlam : 1 < lam) (hhalf : 1 / 2 ≤ h) (hh1 : h < 1) :
    π < typeThreeArea lam h := by
  let q := typeThreeShape h
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hq_nonneg : 0 ≤ q := by
    dsimp only [q, typeThreeShape]
    linarith
  have hq_lt_one : q < 1 := by
    dsimp only [q, typeThreeShape]
    linarith
  have hq_div_le : q / lam ≤ q := by
    apply (div_le_iff₀ hlam_pos).2
    nlinarith
  have hacos_compare : arccos q ≤ arccos (q / lam) :=
    Real.arccos_le_arccos hq_div_le
  have hacos_nonneg : 0 ≤ arccos (q / lam) := Real.arccos_nonneg _
  have hacos_scaled : arccos q ≤ lam * arccos (q / lam) := by
    have : arccos (q / lam) ≤ lam * arccos (q / lam) := by
      nlinarith
    exact hacos_compare.trans this
  have hu_arg : 0 ≤ 1 - q ^ 2 := by nlinarith
  have hd_arg : 0 ≤ lam ^ 2 - q ^ 2 := by nlinarith
  have hradical_product : 0 ≤ q ^ 2 * (lam ^ 2 - 1) :=
    mul_nonneg (sq_nonneg q) (by nlinarith)
  have hscaledRadical :
      lam * sqrt (1 - q ^ 2) ≤ sqrt (lam ^ 2 - q ^ 2) := by
    apply (sq_le_sq₀
      (mul_nonneg hlam_pos.le (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hu_arg, Real.sq_sqrt hd_arg]
    nlinarith [hradical_product]
  have hdelta : 0 ≤ typeThreeDelta lam h := by
    change 0 ≤ sqrt (lam ^ 2 - q ^ 2) / lam - sqrt (1 - q ^ 2)
    rw [sub_nonneg, le_div_iff₀ hlam_pos]
    simpa [mul_comm] using hscaledRadical
  have hangle : π / 2 ≤ typeThreeAngle lam h := by
    change π / 2 ≤ lam * arccos (q / lam) + arcsin q
    rw [Real.arcsin_eq_pi_div_two_sub_arccos]
    linarith
  have hcoefficient : 0 ≤ q + 2 := by linarith
  have hnumerator :
      π ≤ typeThreeAngle lam h + π / 2 +
        (typeThreeShape h + 2) * typeThreeDelta lam h := by
    change π ≤ typeThreeAngle lam h + π / 2 + (q + 2) * typeThreeDelta lam h
    nlinarith [mul_nonneg hcoefficient hdelta]
  have hh_pos : 0 < h := lt_of_lt_of_le (by norm_num) hhalf
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_pos hh_pos
  have hsq_lt_one : h ^ 2 < 1 := by nlinarith
  unfold typeThreeArea
  apply (lt_div_iff₀ hsq_pos).2
  exact (mul_lt_of_lt_one_right Real.pi_pos hsq_lt_one).trans_le hnumerator


private theorem typeThreeSupportGap_continuousOn_Icc {lam a b : ℝ}
    (hlam : 1 < lam) (ha : 0 < a) (hb : b ≤ 1) :
    ContinuousOn (typeThreeSupportGap lam) (Icc a b) := by
  intro x hx
  by_cases hx1 : x = 1
  · subst x
    exact (typeThreeSupportGap_continuousAt_one hlam).continuousWithinAt
  · have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha.trans_le hx.1, lt_of_le_of_ne (hx.2.trans hb) hx1⟩
    exact (typeThreeSupportGap_hasDerivAt
      hlam hxreg.1 hxreg.2).continuousAt.continuousWithinAt

private theorem typeThreeSupportGap_strictMonoOn_Icc_of_fold_neg_right
    {lam a b : ℝ} (hlam : 1 < lam)
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hfold : typeThreeFold lam b < 0) :
    StrictMonoOn (typeThreeSupportGap lam) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · exact typeThreeSupportGap_continuousOn_Icc hlam ha.1 hb.2.le
  · intro x hx
    rw [interior_Icc] at hx
    have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
    rw [(typeThreeSupportGap_hasDerivAt
      hlam hxreg.1 hxreg.2).deriv]
    have hfold_x : typeThreeFold lam x < 0 :=
      (typeThreeFold_strictMonoOn hlam hxreg hb hx.2).trans hfold
    exact div_pos
      (mul_pos_of_neg_of_neg (sub_neg.mpr hxreg.2) hfold_x)
      (pow_pos hxreg.1 3)

/-- For every density above one, the support gap has exactly one zero in the
regular interval, and that zero lies strictly above half height. -/
theorem typeThreeSupportGap_existsUnique_zero {lam : ℝ} (hlam : 1 < lam) :
    ∃! h : ℝ, h ∈ Ioo (1 / 2 : ℝ) 1 ∧
      typeThreeSupportGap lam h = 0 := by
  have hcont : ContinuousOn (typeThreeSupportGap lam) (Icc (1 / 2 : ℝ) 1) :=
    typeThreeSupportGap_continuousOn_Icc hlam (by norm_num) le_rfl
  have htarget : (0 : ℝ) ∈ Icc
      (typeThreeSupportGap lam (1 / 2)) (typeThreeSupportGap lam 1) := by
    rw [typeThreeSupportGap_half hlam]
    exact ⟨neg_nonpos.mpr Real.pi_pos.le,
      (typeThreeSupportGap_one_pos hlam).le⟩
  rcases intermediate_value_Icc (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      hcont htarget with ⟨root, hroot, hroot_zero⟩
  have hroot_half : (1 / 2 : ℝ) < root := by
    apply lt_of_le_of_ne hroot.1
    intro heq
    subst root
    rw [typeThreeSupportGap_half hlam] at hroot_zero
    linarith [Real.pi_pos]
  have hroot_one : root < 1 := by
    apply lt_of_le_of_ne hroot.2
    intro heq
    subst root
    linarith [typeThreeSupportGap_one_pos hlam]
  refine ⟨root, ⟨⟨hroot_half, hroot_one⟩, hroot_zero⟩, ?_⟩
  intro other hother
  rcases hother with ⟨hother_mem, hother_zero⟩
  have hroot_reg : root ∈ Ioo (0 : ℝ) 1 :=
    ⟨(by linarith [hroot_half]), hroot_one⟩
  have hother_reg : other ∈ Ioo (0 : ℝ) 1 :=
    ⟨(by linarith [hother_mem.1]), hother_mem.2⟩
  rcases lt_trichotomy other root with hlt | heq | hgt
  · have hfold_root : typeThreeFold lam root < 0 :=
      typeThreeFold_neg_of_supportGap_nonpos
        hlam hroot_reg hroot_zero.le
    have hmono := typeThreeSupportGap_strictMonoOn_Icc_of_fold_neg_right
      hlam hother_reg hroot_reg hfold_root
    have := hmono
      (show other ∈ Icc other root from ⟨le_rfl, hlt.le⟩)
      (show root ∈ Icc other root from ⟨hlt.le, le_rfl⟩) hlt
    linarith
  · exact heq
  · have hfold_other : typeThreeFold lam other < 0 :=
      typeThreeFold_neg_of_supportGap_nonpos
        hlam hother_reg hother_zero.le
    have hmono := typeThreeSupportGap_strictMonoOn_Icc_of_fold_neg_right
      hlam hroot_reg hother_reg hfold_other
    have := hmono
      (show root ∈ Icc root other from ⟨le_rfl, hgt.le⟩)
      (show other ∈ Icc root other from ⟨hgt.le, le_rfl⟩) hgt
    linarith

/-- The canonical support-gap crossing height. -/
def typeThreeSupportGapRoot (lam : ℝ) (hlam : 1 < lam) : ℝ :=
  Classical.choose (typeThreeSupportGap_existsUnique_zero hlam)

/-- The canonical crossing height lies in `(1/2, 1)` and has zero support
gap. -/
theorem typeThreeSupportGapRoot_spec (lam : ℝ) (hlam : 1 < lam) :
    typeThreeSupportGapRoot lam hlam ∈ Ioo (1 / 2 : ℝ) 1 ∧
      typeThreeSupportGap lam (typeThreeSupportGapRoot lam hlam) = 0 :=
  (Classical.choose_spec (typeThreeSupportGap_existsUnique_zero hlam)).1

/-- Complete strict sign partition of the support gap around its unique
crossing height. -/
theorem typeThreeSupportGap_sign_partition {lam h : ℝ} (hlam : 1 < lam)
    (hh : h ∈ Ioo (0 : ℝ) 1) :
    (h < typeThreeSupportGapRoot lam hlam ↔
        typeThreeSupportGap lam h < 0) ∧
    (h = typeThreeSupportGapRoot lam hlam ↔
        typeThreeSupportGap lam h = 0) ∧
    (typeThreeSupportGapRoot lam hlam < h ↔
        0 < typeThreeSupportGap lam h) := by
  let root := typeThreeSupportGapRoot lam hlam
  change (h < root ↔ typeThreeSupportGap lam h < 0) ∧
    (h = root ↔ typeThreeSupportGap lam h = 0) ∧
    (root < h ↔ 0 < typeThreeSupportGap lam h)
  have hroot_spec := typeThreeSupportGapRoot_spec lam hlam
  have hroot : root ∈ Ioo (1 / 2 : ℝ) 1 := hroot_spec.1
  have hroot_reg : root ∈ Ioo (0 : ℝ) 1 :=
    ⟨(by linarith [hroot.1]), hroot.2⟩
  have hroot_zero : typeThreeSupportGap lam root = 0 := hroot_spec.2
  have hfold_root : typeThreeFold lam root < 0 :=
    typeThreeFold_neg_of_supportGap_nonpos hlam hroot_reg hroot_zero.le
  have hleft_sign : h < root → typeThreeSupportGap lam h < 0 := by
    intro hlt
    have hmono := typeThreeSupportGap_strictMonoOn_Icc_of_fold_neg_right
      hlam hh hroot_reg hfold_root
    simpa [hroot_zero] using hmono
      (show h ∈ Icc h root from ⟨le_rfl, hlt.le⟩)
      (show root ∈ Icc h root from ⟨hlt.le, le_rfl⟩) hlt
  have hright_sign : root < h → 0 < typeThreeSupportGap lam h := by
    intro hlt
    apply lt_of_not_ge
    intro hgap
    have hfold_h : typeThreeFold lam h < 0 :=
      typeThreeFold_neg_of_supportGap_nonpos hlam hh hgap
    have hmono := typeThreeSupportGap_strictMonoOn_Icc_of_fold_neg_right
      hlam hroot_reg hh hfold_h
    have := hmono
      (show root ∈ Icc root h from ⟨le_rfl, hlt.le⟩)
      (show h ∈ Icc root h from ⟨hlt.le, le_rfl⟩) hlt
    linarith
  constructor
  · constructor
    · exact hleft_sign
    · intro hneg
      rcases lt_trichotomy h root with hlt | heq | hgt
      · exact hlt
      · subst h
        linarith
      · linarith [hright_sign hgt]
  constructor
  · constructor
    · rintro rfl
      exact hroot_zero
    · intro hzero
      rcases lt_trichotomy h root with hlt | heq | hgt
      · linarith [hleft_sign hlt]
      · exact heq
      · linarith [hright_sign hgt]
  · constructor
    · exact hright_sign
    · intro hpos
      rcases lt_trichotomy h root with hlt | heq | hgt
      · linarith [hleft_sign hlt]
      · subst h
        linarith
      · exact hgt

/-- The internally defined phase threshold is the type-(iii) area at the
canonical support-gap crossing. -/
def typeThreePhaseThreshold (lam : ℝ) (hlam : 1 < lam) : ℝ :=
  typeThreeArea lam (typeThreeSupportGapRoot lam hlam)

/-- Identification of the phase threshold with the area at the unique
support-gap crossing. -/
theorem typeThreePhaseThreshold_eq (lam : ℝ) (hlam : 1 < lam) :
    typeThreePhaseThreshold lam hlam =
      typeThreeArea lam (typeThreeSupportGapRoot lam hlam) := rfl

/-- The type-(ii)/type-(iii) phase threshold is strictly above `π`. -/
theorem typeThreePhaseThreshold_gt_pi (lam : ℝ) (hlam : 1 < lam) :
    π < typeThreePhaseThreshold lam hlam := by
  rw [typeThreePhaseThreshold_eq]
  exact typeThreeArea_gt_pi_of_half_le hlam
    (typeThreeSupportGapRoot_spec lam hlam).1.1.le
    (typeThreeSupportGapRoot_spec lam hlam).1.2
end LeanSuffixAnalytic
