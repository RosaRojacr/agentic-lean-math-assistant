/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSquaredWidthRecovery

/-!
# Profilewise squared-width geometry

This module supplies the parameter-safe source coordinates needed to generalize
the frozen squared-width recovery to every regular canonical type-(iv) profile.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal MeasureTheory symmDiff

noncomputable section

namespace CMVRelaxation.ProfileSquaredRecovery

variable {lam : ℝ} (profile : CanonicalTypeIVProfile lam)

private lemma lam_pos (profile : CanonicalTypeIVProfile lam) : 0 < lam :=
  lt_trans zero_lt_one profile.density_jump

lemma radius_pos : 0 < profile.radius := by
  rw [CanonicalTypeIVProfile.radius]
  exact one_div_pos.mpr profile.h_pos

lemma radius_gt_one : 1 < profile.radius := by
  rw [CanonicalTypeIVProfile.radius]
  exact (lt_div_iff₀ profile.h_pos).2 (by simpa using profile.h_lt_one)

lemma cos_alpha : Real.cos profile.alpha = profile.h / lam := by
  rw [CanonicalTypeIVProfile.alpha, Real.cos_arccos]
  · exact (by norm_num : (-1 : ℝ) ≤ 0).trans
      (div_nonneg profile.h_pos.le (lam_pos profile).le)
  · exact (div_le_one (lam_pos profile)).2
      (profile.h_lt_one.le.trans profile.density_jump.le)

lemma sin_alpha_pos : 0 < Real.sin profile.alpha := by
  simpa only [CanonicalTypeIVProfile.toCandidate_alpha] using
    profile.toCandidate.sin_alpha_pos

lemma outerHalfWidth_pos : 0 < profile.outerHalfWidth := by
  rw [CanonicalTypeIVProfile.outerHalfWidth]
  exact mul_pos (radius_pos profile) (sin_alpha_pos profile)

/-- Signed height of the upper exterior-circle center. -/
def capCenter : ℝ :=
  1 - profile.radius * Real.cos profile.alpha

lemma radius_mul_cos_alpha :
    profile.radius * Real.cos profile.alpha = 1 / lam := by
  rw [cos_alpha profile, CanonicalTypeIVProfile.radius]
  field_simp [profile.h_pos.ne', (lam_pos profile).ne']

lemma capCenter_eq_one_sub_inv :
    capCenter profile = 1 - 1 / lam := by
  rw [capCenter, radius_mul_cos_alpha profile]

lemma capCenter_pos : 0 < capCenter profile := by
  rw [capCenter_eq_one_sub_inv profile]
  have hinv : 1 / lam < 1 := (div_lt_one (lam_pos profile)).2 profile.density_jump
  linarith

lemma capCenter_lt_one : capCenter profile < 1 := by
  rw [capCenter_eq_one_sub_inv profile]
  exact sub_lt_self 1 (one_div_pos.mpr (lam_pos profile))

/-- Start of the profile-dependent cutoff, strictly above the actual strip. -/
def safeStart : ℝ :=
  (3 + profile.radius ^ 2) / 4

/-- End of the profile-dependent cutoff, strictly below the radius square. -/
def safeStop : ℝ :=
  (1 + profile.radius ^ 2) / 2

lemma one_lt_safeStart : 1 < safeStart profile := by
  unfold safeStart
  nlinarith [radius_gt_one profile, sq_nonneg (profile.radius - 1)]

lemma safeStart_lt_safeStop : safeStart profile < safeStop profile := by
  unfold safeStart safeStop
  nlinarith [radius_gt_one profile, sq_nonneg (profile.radius - 1)]

lemma safeStop_lt_radius_sq : safeStop profile < profile.radius ^ 2 := by
  unfold safeStop
  nlinarith [radius_gt_one profile, sq_nonneg (profile.radius - 1)]

/-- Smooth global replacement for `y²`. It is exact throughout `|y| ≤ 1`
and stays strictly below the profile's radius square everywhere. -/
def safeSquare (y : ℝ) : ℝ :=
  y ^ 2 *
    (1 - Real.smoothTransition
      ((y ^ 2 - safeStart profile) /
        (safeStop profile - safeStart profile)))

lemma safeSquare_eq_sq {y : ℝ} (hy : y ^ 2 ≤ safeStart profile) :
    safeSquare profile y = y ^ 2 := by
  have hden : 0 < safeStop profile - safeStart profile :=
    sub_pos.mpr (safeStart_lt_safeStop profile)
  have harg :
      (y ^ 2 - safeStart profile) /
          (safeStop profile - safeStart profile) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hden.le
  rw [safeSquare, Real.smoothTransition.zero_of_nonpos harg]
  ring

lemma safeSquare_eq_sq_of_sq_le_one {y : ℝ} (hy : y ^ 2 ≤ 1) :
    safeSquare profile y = y ^ 2 :=
  safeSquare_eq_sq profile (hy.trans (one_lt_safeStart profile).le)

lemma safeSquare_mem_Icc (y : ℝ) :
    safeSquare profile y ∈ Icc (0 : ℝ) (safeStop profile) := by
  have hχ0 : 0 ≤ Real.smoothTransition
      ((y ^ 2 - safeStart profile) /
        (safeStop profile - safeStart profile)) :=
    Real.smoothTransition.nonneg _
  have hχ1 : Real.smoothTransition
      ((y ^ 2 - safeStart profile) /
        (safeStop profile - safeStart profile)) ≤ 1 :=
    Real.smoothTransition.le_one _
  by_cases hy : y ^ 2 ≤ safeStop profile
  · constructor
    · exact mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hχ1)
    · calc
        safeSquare profile y ≤ y ^ 2 * 1 := by
          unfold safeSquare
          exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg y)
        _ ≤ safeStop profile := by simpa using hy
  · have hden : 0 < safeStop profile - safeStart profile :=
      sub_pos.mpr (safeStart_lt_safeStop profile)
    have harg : 1 ≤
        (y ^ 2 - safeStart profile) /
          (safeStop profile - safeStart profile) := by
      rw [le_div_iff₀ hden]
      simp only [not_le] at hy
      linarith
    rw [safeSquare, Real.smoothTransition.one_of_one_le harg]
    constructor
    · norm_num
    · norm_num only [sub_self, mul_zero]
      exact zero_le_one.trans ((one_lt_safeStart profile).le.trans
        (safeStart_lt_safeStop profile).le)

lemma safeSquare_lt_radius_sq (y : ℝ) :
    safeSquare profile y < profile.radius ^ 2 :=
  (safeSquare_mem_Icc profile y).2.trans_lt (safeStop_lt_radius_sq profile)

lemma contDiff_safeSquare : ContDiff ℝ ∞ (safeSquare profile) := by
  unfold safeSquare
  have harg : ContDiff ℝ ∞ (fun y : ℝ =>
      (y ^ 2 - safeStart profile) /
        (safeStop profile - safeStart profile)) :=
    ((contDiff_id.pow 2).sub contDiff_const).div_const _
  exact (contDiff_id.pow 2).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp harg))

/-- Globally smooth extension of the strip-side squared half-width. -/
def sideSquare (y : ℝ) : ℝ :=
  (profile.sideCenterOffset +
    √(profile.radius ^ 2 - safeSquare profile y)) ^ 2

lemma contDiff_sideSquare : ContDiff ℝ ∞ (sideSquare profile) := by
  have hrad : ∀ y, profile.radius ^ 2 - safeSquare profile y ≠ 0 := by
    intro y
    exact (sub_pos.mpr (safeSquare_lt_radius_sq profile y)).ne'
  unfold sideSquare
  exact (contDiff_const.add
    ((contDiff_const.sub (contDiff_safeSquare profile)).sqrt hrad)).pow 2

lemma sideSquare_eq_actual {y : ℝ} (hy : y ^ 2 ≤ 1) :
    sideSquare profile y =
      (profile.sideCenterOffset + √(profile.radius ^ 2 - y ^ 2)) ^ 2 := by
  rw [sideSquare, safeSquare_eq_sq_of_sq_le_one profile hy]

/-- Smooth extension of the exterior-cap squared half-width. -/
def capSquare (y : ℝ) : ℝ :=
  profile.radius ^ 2 -
    (FrozenSquaredRecovery.smoothAbs y - capCenter profile) ^ 2

lemma contDiff_capSquare : ContDiff ℝ ∞ (capSquare profile) := by
  unfold capSquare
  exact contDiff_const.sub
    ((FrozenSquaredRecovery.contDiff_smoothAbs.sub contDiff_const).pow 2)

lemma capSquare_eq_actual_of_half_le_abs {y : ℝ} (hy : 1 / 2 ≤ |y|) :
    capSquare profile y =
      profile.radius ^ 2 - (|y| - capCenter profile) ^ 2 := by
  rw [capSquare, FrozenSquaredRecovery.smoothAbs_eq_of_half_le_abs hy]


lemma inner_argument_pos : 0 < 1 - profile.h ^ 2 := by
  nlinarith [profile.h_pos, profile.h_lt_one]

lemma innerRadial_pos : 0 < profile.innerRadial := by
  rw [CanonicalTypeIVProfile.innerRadial]
  exact Real.sqrt_pos.2 (inner_argument_pos profile)

lemma radius_mul_innerRadial_sq :
    (profile.radius * profile.innerRadial) ^ 2 =
      profile.radius ^ 2 - 1 := by
  rw [CanonicalTypeIVProfile.radius, CanonicalTypeIVProfile.innerRadial,
    mul_pow, Real.sq_sqrt (inner_argument_pos profile).le]
  field_simp [profile.h_pos.ne']

lemma sqrt_radius_sq_sub_one :
    √(profile.radius ^ 2 - 1) =
      profile.radius * profile.innerRadial := by
  rw [← radius_mul_innerRadial_sq profile, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos (radius_pos profile) (innerRadial_pos profile))]

lemma sideCenterOffset_add_attachment :
    profile.sideCenterOffset + profile.radius * profile.innerRadial =
      profile.outerHalfWidth := by
  simp only [CanonicalTypeIVProfile.sideCenterOffset,
    CanonicalTypeIVProfile.outerHalfWidth]
  ring

lemma sideSquare_one :
    sideSquare profile 1 = profile.outerHalfWidth ^ 2 := by
  rw [sideSquare_eq_actual profile (by norm_num : (1 : ℝ) ^ 2 ≤ 1)]
  norm_num only [one_pow]
  rw [sqrt_radius_sq_sub_one profile, sideCenterOffset_add_attachment profile]

lemma sideSquare_neg_one :
    sideSquare profile (-1) = profile.outerHalfWidth ^ 2 := by
  rw [sideSquare_eq_actual profile (by norm_num : (-1 : ℝ) ^ 2 ≤ 1)]
  norm_num only [neg_sq, one_pow]
  rw [sqrt_radius_sq_sub_one profile, sideCenterOffset_add_attachment profile]

lemma one_sub_capCenter :
    1 - capCenter profile = profile.radius * Real.cos profile.alpha := by
  unfold capCenter
  ring

lemma outerHalfWidth_sq :
    profile.outerHalfWidth ^ 2 =
      profile.radius ^ 2 - (1 - capCenter profile) ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq profile.alpha
  rw [CanonicalTypeIVProfile.outerHalfWidth, one_sub_capCenter profile]
  nlinarith

lemma capSquare_one :
    capSquare profile 1 = profile.outerHalfWidth ^ 2 := by
  rw [capSquare_eq_actual_of_half_le_abs profile (by norm_num)]
  norm_num only [abs_one]
  exact (outerHalfWidth_sq profile).symm

lemma capSquare_neg_one :
    capSquare profile (-1) = profile.outerHalfWidth ^ 2 := by
  rw [capSquare_eq_actual_of_half_le_abs profile (by norm_num)]
  norm_num only [abs_neg, abs_one]
  exact (outerHalfWidth_sq profile).symm

/-- The two extensions have the same strictly positive squared width at both
source interfaces. -/
theorem attachmentSquares :
    sideSquare profile 1 = capSquare profile 1 ∧
      sideSquare profile (-1) = capSquare profile (-1) ∧
      0 < profile.outerHalfWidth ^ 2 := by
  constructor
  · rw [sideSquare_one profile, capSquare_one profile]
  constructor
  · rw [sideSquare_neg_one profile, capSquare_neg_one profile]
  · exact sq_pos_of_pos (outerHalfWidth_pos profile)

/-- The largest junction scale used by the profilewise geometry.  It is
constructed solely from the profile and stays below both `1/16` and the
positive cap attachment height. -/
def safeScale : ℝ :=
  min (1 / 16) (1 - capCenter profile)

lemma safeScale_pos : 0 < safeScale profile := by
  rw [safeScale, lt_min_iff]
  exact ⟨by norm_num, sub_pos.mpr (capCenter_lt_one profile)⟩

lemma safeScale_le_sixteenth : safeScale profile ≤ 1 / 16 :=
  min_le_left _ _

lemma safeScale_le_half : safeScale profile ≤ 1 / 2 :=
  (safeScale_le_sixteenth profile).trans (by norm_num)

lemma safeScale_le_one_sub_capCenter :
    safeScale profile ≤ 1 - capCenter profile :=
  min_le_right _ _

lemma sideSquare_ge_attachment {y : ℝ} (hy : |y| ≤ 1) :
    profile.outerHalfWidth ^ 2 ≤ sideSquare profile y := by
  have hysq : y ^ 2 ≤ 1 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)).2 hy
    simpa only [sq_abs, one_pow] using hsquare
  have hrad : 0 ≤ profile.radius ^ 2 - y ^ 2 := by
    nlinarith [radius_gt_one profile]
  have hroot :
      √(profile.radius ^ 2 - 1) ≤
        √(profile.radius ^ 2 - y ^ 2) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hwidth :
      profile.outerHalfWidth ≤
        profile.sideCenterOffset +
          √(profile.radius ^ 2 - y ^ 2) := by
    rw [← sideCenterOffset_add_attachment profile,
      ← sqrt_radius_sq_sub_one profile]
    linarith
  rw [sideSquare_eq_actual profile hysq]
  exact (sq_le_sq₀ (outerHalfWidth_pos profile).le
    ((outerHalfWidth_pos profile).le.trans hwidth)).2 hwidth

lemma capSquare_ge_attachment
    {epsilon y : ℝ}
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : |y| ∈ Icc (1 - epsilon : ℝ) 1) :
    profile.outerHalfWidth ^ 2 ≤ capSquare profile y := by
  have hepsilon_half : epsilon ≤ 1 / 2 :=
    hepsilon_le.trans (safeScale_le_half profile)
  have habs_half : 1 / 2 ≤ |y| := by linarith [hy.1]
  have hcap_le_abs : capCenter profile ≤ |y| := by
    have := hepsilon_le.trans (safeScale_le_one_sub_capCenter profile)
    linarith [hy.1]
  have hgap0 : 0 ≤ |y| - capCenter profile := sub_nonneg.mpr hcap_le_abs
  have hgap_le : |y| - capCenter profile ≤ 1 - capCenter profile := by
    linarith [hy.2]
  have honeGap0 : 0 ≤ 1 - capCenter profile :=
    sub_nonneg.mpr (capCenter_lt_one profile).le
  have hsq :
      (|y| - capCenter profile) ^ 2 ≤
        (1 - capCenter profile) ^ 2 :=
    (sq_le_sq₀ hgap0 honeGap0).2 hgap_le
  rw [capSquare_eq_actual_of_half_le_abs profile habs_half,
    outerHalfWidth_sq profile]
  linarith

/-- Profilewise squared-width blend across the two junction collars. -/
def q (epsilon y : ℝ) : ℝ :=
  sideSquare profile y +
    FrozenSquaredRecovery.junctionWeight epsilon y *
      (capSquare profile y - sideSquare profile y)

lemma contDiff_q (epsilon : ℝ) : ContDiff ℝ ∞ (q profile epsilon) := by
  have hratio : ContDiff ℝ ∞
      (fun y : ℝ =>
        (y ^ 2 - (1 - epsilon) ^ 2) /
          (1 - (1 - epsilon) ^ 2)) :=
    ((contDiff_id.pow 2).sub contDiff_const).div_const _
  have hweight : ContDiff ℝ ∞
      (FrozenSquaredRecovery.junctionWeight epsilon) := by
    unfold FrozenSquaredRecovery.junctionWeight
    exact Real.smoothTransition.contDiff.comp hratio
  unfold q
  exact (contDiff_sideSquare profile).add
    (hweight.mul ((contDiff_capSquare profile).sub
      (contDiff_sideSquare profile)))

lemma q_eq_side
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : y ^ 2 ≤ (1 - epsilon) ^ 2) :
    q profile epsilon y = sideSquare profile y := by
  rw [q, FrozenSquaredRecovery.junctionWeight_eq_zero hepsilon
    (hepsilon_le.trans (safeScale_le_sixteenth profile)) hy]
  ring

lemma q_eq_cap
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : 1 ≤ y ^ 2) :
    q profile epsilon y = capSquare profile y := by
  rw [q, FrozenSquaredRecovery.junctionWeight_eq_one hepsilon
    (hepsilon_le.trans (safeScale_le_sixteenth profile)) hy]
  ring

/-- Both actual source widths and therefore their smooth convex blend stay
above the positive attachment square on the internally constructed collar. -/
theorem q_ge_positive_attachment
    {epsilon y : ℝ} (_hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : |y| ∈ Icc (1 - epsilon : ℝ) 1) :
    0 < profile.outerHalfWidth ^ 2 ∧
      profile.outerHalfWidth ^ 2 ≤ q profile epsilon y := by
  have hs := sideSquare_ge_attachment profile hy.2
  have hc := capSquare_ge_attachment profile hepsilon_le hy
  let w := FrozenSquaredRecovery.junctionWeight epsilon y
  have hw := FrozenSquaredRecovery.junctionWeight_mem_Icc epsilon y
  constructor
  · exact sq_pos_of_pos (outerHalfWidth_pos profile)
  · rw [show q profile epsilon y =
        (1 - w) * sideSquare profile y + w * capSquare profile y by
      unfold q w
      ring]
    calc
      profile.outerHalfWidth ^ 2 =
          (1 - w) * profile.outerHalfWidth ^ 2 +
            w * profile.outerHalfWidth ^ 2 := by ring
      _ ≤ (1 - w) * sideSquare profile y + w * capSquare profile y :=
        add_le_add
          (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hw.2))
          (mul_le_mul_of_nonneg_left hc hw.1)


/-- Piecewise squared half-width of the actual closed canonical carrier. -/
def targetQ (y : ℝ) : ℝ :=
  if |y| ≤ 1 then sideSquare profile y else capSquare profile y

/-- Every interface and pole is included: the actual five-piece closed source
carrier is exactly the non-strict squared-width sublevel. -/
theorem mem_profile_iff_sq_le_targetQ (p : PlanePoint) :
    p ∈ profile.carrier ↔ p.1 ^ 2 ≤ targetQ profile p.2 := by
  have hWpos := outerHalfWidth_pos profile
  have hRpos := radius_pos profile
  have hRone := radius_gt_one profile
  have hattachPos :
      0 < profile.radius * profile.innerRadial :=
    mul_pos hRpos (innerRadial_pos profile)
  have hL : profile.leftCenter =
      (-profile.sideCenterOffset, 0) := rfl
  have hRt : profile.rightCenter =
      (profile.sideCenterOffset, 0) := rfl
  have hU : profile.upperCenter = (0, capCenter profile) := by
    rw [CanonicalTypeIVProfile.upperCenter]
    rfl
  have hD : profile.lowerCenter = (0, -capCenter profile) := by
    rw [CanonicalTypeIVProfile.lowerCenter]
    apply Prod.ext
    · rfl
    · dsimp [capCenter]
      ring
  simp only [CanonicalTypeIVProfile.carrier,
    CanonicalTypeIVProfile.rectangleCarrier,
    CanonicalTypeIVProfile.leftSegmentCarrier,
    CanonicalTypeIVProfile.rightSegmentCarrier,
    CanonicalTypeIVProfile.upperCapCarrier,
    CanonicalTypeIVProfile.lowerCapCarrier,
    Set.mem_union, Set.mem_ofPred_eq, hL, hRt, hU, hD,
    sub_zero, sub_neg_eq_add, targetQ]
  by_cases hy : |p.2| ≤ 1
  · rw [if_pos hy]
    have hysq : p.2 ^ 2 ≤ 1 := by
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 1)).2 hy
      simpa only [sq_abs, one_pow] using hsquare
    rw [sideSquare_eq_actual profile hysq]
    have hrad : 0 ≤ profile.radius ^ 2 - p.2 ^ 2 := by
      nlinarith
    have hroot0 : 0 ≤ √(profile.radius ^ 2 - p.2 ^ 2) :=
      Real.sqrt_nonneg _
    have hrootSq :
        (√(profile.radius ^ 2 - p.2 ^ 2)) ^ 2 =
          profile.radius ^ 2 - p.2 ^ 2 :=
      Real.sq_sqrt hrad
    have hroot :
        profile.radius * profile.innerRadial ≤
          √(profile.radius ^ 2 - p.2 ^ 2) := by
      rw [← sqrt_radius_sq_sub_one profile]
      exact Real.sqrt_le_sqrt (by linarith)
    have hwidth :
        profile.outerHalfWidth ≤
          profile.sideCenterOffset +
            √(profile.radius ^ 2 - p.2 ^ 2) := by
      rw [← sideCenterOffset_add_attachment profile]
      linarith
    have hwidth0 :
        0 ≤ profile.sideCenterOffset +
          √(profile.radius ^ 2 - p.2 ^ 2) :=
      hWpos.le.trans hwidth
    constructor
    · rintro ((((hrect | hleft) | hright) | hupper) | hlower)
      · rcases hrect with ⟨hxlo, hxhi, _⟩
        have habsx : |p.1| ≤ profile.outerHalfWidth :=
          (abs_le).2 ⟨by linarith, hxhi⟩
        have hsquared :=
          (sq_le_sq₀ (abs_nonneg p.1) hWpos.le).2 habsx
        have hWsq := (sq_le_sq₀ hWpos.le hwidth0).2 hwidth
        simpa only [sq_abs] using hsquared.trans hWsq
      · rcases hleft with ⟨hdisk, hxside, _⟩
        have hx0 : p.1 ≤ 0 := by linarith
        have hshift0 : p.1 + profile.sideCenterOffset ≤ 0 := by
          rw [← sideCenterOffset_add_attachment profile] at hxside
          linarith
        have hshiftSq :
            (p.1 + profile.sideCenterOffset) ^ 2 ≤
              (√(profile.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
          nlinarith
        have hshiftAbs :
            |p.1 + profile.sideCenterOffset| ≤
              √(profile.radius ^ 2 - p.2 ^ 2) :=
          (sq_le_sq₀ (abs_nonneg _) hroot0).1
            (by simpa only [sq_abs] using hshiftSq)
        rw [abs_of_nonpos hshift0] at hshiftAbs
        have habsx :
            |p.1| ≤ profile.sideCenterOffset +
              √(profile.radius ^ 2 - p.2 ^ 2) := by
          rw [abs_of_nonpos hx0]
          linarith
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg p.1) hwidth0).2 habsx
      · rcases hright with ⟨hdisk, hxside, _⟩
        have hx0 : 0 ≤ p.1 := by linarith
        have hshift0 : 0 ≤ p.1 - profile.sideCenterOffset := by
          rw [← sideCenterOffset_add_attachment profile] at hxside
          linarith
        have hshiftSq :
            (p.1 - profile.sideCenterOffset) ^ 2 ≤
              (√(profile.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
          nlinarith
        have hshiftAbs :
            |p.1 - profile.sideCenterOffset| ≤
              √(profile.radius ^ 2 - p.2 ^ 2) :=
          (sq_le_sq₀ (abs_nonneg _) hroot0).1
            (by simpa only [sq_abs] using hshiftSq)
        rw [abs_of_nonneg hshift0] at hshiftAbs
        have habsx :
            |p.1| ≤ profile.sideCenterOffset +
              √(profile.radius ^ 2 - p.2 ^ 2) := by
          rw [abs_of_nonneg hx0]
          linarith
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg p.1) hwidth0).2 habsx
      · rcases hupper with ⟨hdisk, hyupper⟩
        have hyeq : p.2 = 1 := by
          have := (le_abs_self p.2).trans hy
          linarith
        rw [hyeq]
        norm_num only [one_pow]
        rw [sqrt_radius_sq_sub_one profile,
          sideCenterOffset_add_attachment profile]
        rw [hyeq] at hdisk
        have houter := outerHalfWidth_sq profile
        nlinarith
      · rcases hlower with ⟨hdisk, hylower⟩
        have hyeq : p.2 = -1 := by
          have := (neg_le_abs p.2).trans hy
          linarith
        rw [hyeq]
        norm_num only [neg_sq, one_pow]
        rw [sqrt_radius_sq_sub_one profile,
          sideCenterOffset_add_attachment profile]
        rw [hyeq] at hdisk
        have houter := outerHalfWidth_sq profile
        nlinarith
    · intro hx
      have habsx :
          |p.1| ≤ profile.sideCenterOffset +
            √(profile.radius ^ 2 - p.2 ^ 2) := by
        exact (sq_le_sq₀ (abs_nonneg p.1) hwidth0).1
          (by simpa only [sq_abs] using hx)
      by_cases hxleft : p.1 ≤ -profile.outerHalfWidth
      · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
        refine ⟨?_, hxleft, hy⟩
        have hxlower :
            -(profile.sideCenterOffset +
              √(profile.radius ^ 2 - p.2 ^ 2)) ≤ p.1 :=
          neg_le_of_abs_le habsx
        have hshift0 : p.1 + profile.sideCenterOffset ≤ 0 := by
          rw [← sideCenterOffset_add_attachment profile] at hxleft
          linarith
        have hshiftAbs :
            |p.1 + profile.sideCenterOffset| ≤
              √(profile.radius ^ 2 - p.2 ^ 2) := by
          rw [abs_of_nonpos hshift0]
          linarith
        have hshiftSq :
            (p.1 + profile.sideCenterOffset) ^ 2 ≤
              (√(profile.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) hroot0).2 hshiftAbs
        nlinarith
      · by_cases hxright : profile.outerHalfWidth ≤ p.1
        · refine Or.inl (Or.inl (Or.inr ?_))
          refine ⟨?_, hxright, hy⟩
          have hxupper :
              p.1 ≤ profile.sideCenterOffset +
                √(profile.radius ^ 2 - p.2 ^ 2) :=
            le_of_abs_le habsx
          have hshift0 : 0 ≤ p.1 - profile.sideCenterOffset := by
            rw [← sideCenterOffset_add_attachment profile] at hxright
            linarith
          have hshiftAbs :
              |p.1 - profile.sideCenterOffset| ≤
                √(profile.radius ^ 2 - p.2 ^ 2) := by
            rw [abs_of_nonneg hshift0]
            linarith
          have hshiftSq :
              (p.1 - profile.sideCenterOffset) ^ 2 ≤
                (√(profile.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg _) hroot0).2 hshiftAbs
          nlinarith
        · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
          exact ⟨le_of_not_ge hxleft, le_of_not_ge hxright, hy⟩
  · rw [if_neg hy]
    have hy' : 1 < |p.2| := lt_of_not_ge hy
    rw [capSquare_eq_actual_of_half_le_abs profile (by linarith)]
    simp only [hy, and_false, or_false]
    rcases le_total 0 p.2 with hy0 | hy0
    · have hpos : 1 < p.2 := by
        rw [abs_of_nonneg hy0] at hy'
        exact hy'
      have hnotLower : ¬p.2 ≤ -1 := by linarith
      simp only [hpos.le, hnotLower, and_false, or_false, false_or, and_true,
        abs_of_nonneg hy0]
      constructor <;> intro h <;> nlinarith
    · have hneg : p.2 < -1 := by
        rw [abs_of_nonpos hy0] at hy'
        linarith
      have hnotUpper : ¬1 ≤ p.2 := by linarith
      simp only [hneg.le, hnotUpper, and_false, false_or, or_false, and_true,
        abs_of_nonpos hy0]
      constructor <;> intro h <;> nlinarith


/-- The height of either exterior cap pole. -/
def poleHeight : ℝ :=
  profile.radius + capCenter profile

lemma poleHeight_gt_one : 1 < poleHeight profile := by
  unfold poleHeight
  linarith [radius_gt_one profile, capCenter_pos profile]

lemma q_pos_of_abs_lt_one
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : |y| < 1) :
    0 < q profile epsilon y := by
  have honeMinus : 0 ≤ 1 - epsilon := by
    linarith [hepsilon_le, safeScale_le_sixteenth profile]
  by_cases hcentral : |y| ≤ 1 - epsilon
  · have hsq : y ^ 2 ≤ (1 - epsilon) ^ 2 := by
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg y) honeMinus).2 hcentral
      simpa only [sq_abs] using hsquare
    rw [q_eq_side profile hepsilon hepsilon_le hsq]
    exact lt_of_lt_of_le
      (sq_pos_of_pos (outerHalfWidth_pos profile))
      (sideSquare_ge_attachment profile hy.le)
  · have hcollar : |y| ∈ Icc (1 - epsilon : ℝ) 1 :=
      ⟨le_of_not_ge hcentral, hy.le⟩
    exact lt_of_lt_of_le
      (q_ge_positive_attachment profile hepsilon hepsilon_le hcollar).1
      (q_ge_positive_attachment profile hepsilon hepsilon_le hcollar).2

lemma one_le_abs_of_q_eq_zero
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : q profile epsilon y = 0) :
    1 ≤ |y| := by
  by_contra hnot
  exact (q_pos_of_abs_lt_one profile hepsilon hepsilon_le
    (lt_of_not_ge hnot)).ne' hy

lemma abs_eq_poleHeight_of_q_eq_zero
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : q profile epsilon y = 0) :
    |y| = poleHeight profile := by
  have habs := one_le_abs_of_q_eq_zero profile hepsilon hepsilon_le hy
  have hsq : 1 ≤ y ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 habs
    simpa only [sq_abs, one_pow] using hsquare
  have hhalf : 1 / 2 ≤ |y| := by linarith
  rw [q_eq_cap profile hepsilon hepsilon_le hsq,
    capSquare_eq_actual_of_half_le_abs profile hhalf] at hy
  have hgap : 0 ≤ |y| - capCenter profile := by
    linarith [capCenter_lt_one profile]
  have hR := radius_pos profile
  unfold poleHeight
  nlinarith

lemma q_eq_zero_iff
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    q profile epsilon y = 0 ↔
      y = -poleHeight profile ∨ y = poleHeight profile := by
  constructor
  · intro hy
    have habs :=
      abs_eq_poleHeight_of_q_eq_zero profile hepsilon hepsilon_le hy
    rcases le_total 0 y with hy0 | hy0
    · right
      rwa [abs_of_nonneg hy0] at habs
    · left
      rw [abs_of_nonpos hy0] at habs
      linarith
  · rintro (rfl | rfl)
    · have hp : 1 < poleHeight profile := poleHeight_gt_one profile
      have hsq : 1 ≤ (-poleHeight profile) ^ 2 := by
        nlinarith [sq_nonneg (poleHeight profile - 1)]
      rw [q_eq_cap profile hepsilon hepsilon_le hsq,
        capSquare_eq_actual_of_half_le_abs profile]
      · rw [abs_neg, abs_of_pos (by linarith : 0 < poleHeight profile)]
        unfold poleHeight
        ring
      · rw [abs_neg, abs_of_pos (by linarith : 0 < poleHeight profile)]
        linarith
    · have hp : 1 < poleHeight profile := poleHeight_gt_one profile
      have hsq : 1 ≤ poleHeight profile ^ 2 := by
        nlinarith [sq_nonneg (poleHeight profile - 1)]
      rw [q_eq_cap profile hepsilon hepsilon_le hsq,
        capSquare_eq_actual_of_half_le_abs profile]
      · rw [abs_of_pos (by linarith : 0 < poleHeight profile)]
        unfold poleHeight
        ring
      · rw [abs_of_pos (by linarith : 0 < poleHeight profile)]
        linarith

lemma q_eventuallyEq_upperCap
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    q profile epsilon =ᶠ[𝓝 (poleHeight profile)]
      (fun y : ℝ =>
        profile.radius ^ 2 - (y - capCenter profile) ^ 2) := by
  filter_upwards [Ioi_mem_nhds (poleHeight_gt_one profile)] with y hy
  change (1 : ℝ) < y at hy
  have hy0 : 0 ≤ y := by linarith
  have hsq : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  rw [q_eq_cap profile hepsilon hepsilon_le hsq, capSquare,
    FrozenSquaredRecovery.smoothAbs_eq_of_half_le_abs]
  · rw [abs_of_nonneg hy0]
  · rw [abs_of_nonneg hy0]
    linarith

lemma q_eventuallyEq_lowerCap
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    q profile epsilon =ᶠ[𝓝 (-poleHeight profile)]
      (fun y : ℝ =>
        profile.radius ^ 2 - (y + capCenter profile) ^ 2) := by
  have hp : -poleHeight profile < (-1 : ℝ) := by
    linarith [poleHeight_gt_one profile]
  filter_upwards [Iio_mem_nhds hp] with y hy
  change y < (-1 : ℝ) at hy
  have hy0 : y ≤ 0 := by linarith
  have hsq : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y + 1)]
  rw [q_eq_cap profile hepsilon hepsilon_le hsq, capSquare,
    FrozenSquaredRecovery.smoothAbs_eq_of_half_le_abs]
  · rw [abs_of_nonpos hy0]
    ring
  · rw [abs_of_nonpos hy0]
    linarith

lemma hasDerivAt_q_upperPole
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    HasDerivAt (q profile epsilon) (-2 * profile.radius)
      (poleHeight profile) := by
  have hpoly : HasDerivAt
      (fun y : ℝ =>
        profile.radius ^ 2 - (y - capCenter profile) ^ 2)
      (-2 * profile.radius) (poleHeight profile) := by
    have hraw :=
      (hasDerivAt_const (poleHeight profile) (profile.radius ^ 2)).sub
        (((hasDerivAt_id (poleHeight profile)).sub_const
          (capCenter profile)).pow 2)
    simpa [Pi.sub_apply, poleHeight] using! hraw
  exact hpoly.congr_of_eventuallyEq
    (q_eventuallyEq_upperCap profile hepsilon hepsilon_le)

lemma hasDerivAt_q_lowerPole
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    HasDerivAt (q profile epsilon) (2 * profile.radius)
      (-poleHeight profile) := by
  have hpoly : HasDerivAt
      (fun y : ℝ =>
        profile.radius ^ 2 - (y + capCenter profile) ^ 2)
      (2 * profile.radius) (-poleHeight profile) := by
    have hraw :=
      (hasDerivAt_const (-poleHeight profile) (profile.radius ^ 2)).sub
        (((hasDerivAt_id (-poleHeight profile)).add_const
          (capCenter profile)).pow 2)
    simpa [Pi.sub_apply, poleHeight] using! hraw
  exact hpoly.congr_of_eventuallyEq
    (q_eventuallyEq_lowerCap profile hepsilon hepsilon_le)

lemma q_regularZeros
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    ∀ y, q profile epsilon y = 0 →
      deriv (q profile epsilon) y ≠ 0 := by
  intro y hy
  rcases (q_eq_zero_iff profile hepsilon hepsilon_le).1 hy with rfl | rfl
  · rw [(hasDerivAt_q_lowerPole profile hepsilon hepsilon_le).deriv]
    exact mul_ne_zero (by norm_num) (radius_pos profile).ne'
  · rw [(hasDerivAt_q_upperPole profile hepsilon hepsilon_le).deriv]
    exact mul_ne_zero (by norm_num) (radius_pos profile).ne'

/-- The profilewise smooth recovery domain. -/
def domain (epsilon : ℝ) : Set PlanePoint :=
  squaredWidthDomain (q profile epsilon)

/-- Every internally admissible positive scale gives one global smooth domain,
including both moving collars and the two cap poles. -/
theorem isSmoothDomain_domain
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    IsSmoothDomain (domain profile epsilon) := by
  unfold domain
  exact isSmoothDomain_squaredWidth (contDiff_q profile epsilon)
    (q_regularZeros profile hepsilon hepsilon_le)


/-- A profile-dependent finite horizontal radius containing every recovery and
target section. -/
def horizontalRadius : ℝ :=
  |profile.sideCenterOffset| + 2 * profile.radius

lemma horizontalRadius_pos : 0 < horizontalRadius profile := by
  unfold horizontalRadius
  exact add_pos_of_nonneg_of_pos (abs_nonneg _)
    (mul_pos (by norm_num) (radius_pos profile))

lemma radius_lt_horizontalRadius :
    profile.radius < horizontalRadius profile := by
  unfold horizontalRadius
  nlinarith [abs_nonneg profile.sideCenterOffset, radius_pos profile]

lemma sideSquare_le_horizontalRadius_sq (y : ℝ) :
    sideSquare profile y ≤ horizontalRadius profile ^ 2 := by
  have hsafe0 := (safeSquare_mem_Icc profile y).1
  have hrad :
      0 ≤ profile.radius ^ 2 - safeSquare profile y :=
    (sub_pos.mpr (safeSquare_lt_radius_sq profile y)).le
  have hsqrtSq :
      (√(profile.radius ^ 2 - safeSquare profile y)) ^ 2 =
        profile.radius ^ 2 - safeSquare profile y :=
    Real.sq_sqrt hrad
  have hsqrt0 :
      0 ≤ √(profile.radius ^ 2 - safeSquare profile y) :=
    Real.sqrt_nonneg _
  have hsqrt_le :
      √(profile.radius ^ 2 - safeSquare profile y) ≤
        profile.radius := by
    nlinarith [radius_pos profile]
  have hupper :
      profile.sideCenterOffset +
          √(profile.radius ^ 2 - safeSquare profile y) ≤
        horizontalRadius profile := by
    unfold horizontalRadius
    linarith [le_abs_self profile.sideCenterOffset, radius_pos profile]
  have hlower :
      -horizontalRadius profile ≤
        profile.sideCenterOffset +
          √(profile.radius ^ 2 - safeSquare profile y) := by
    unfold horizontalRadius
    linarith [neg_abs_le profile.sideCenterOffset, radius_pos profile]
  have habs :
      |profile.sideCenterOffset +
          √(profile.radius ^ 2 - safeSquare profile y)| ≤
        horizontalRadius profile :=
    (abs_le).2 ⟨hlower, hupper⟩
  have hsquared :=
    (sq_le_sq₀
      (abs_nonneg
        (profile.sideCenterOffset +
          √(profile.radius ^ 2 - safeSquare profile y)))
      (horizontalRadius_pos profile).le).2 habs
  rw [sideSquare]
  simpa only [sq_abs] using hsquared

lemma capSquare_le_horizontalRadius_sq (y : ℝ) :
    capSquare profile y ≤ horizontalRadius profile ^ 2 := by
  calc
    capSquare profile y ≤ profile.radius ^ 2 := by
      unfold capSquare
      nlinarith [sq_nonneg
        (FrozenSquaredRecovery.smoothAbs y - capCenter profile)]
    _ ≤ horizontalRadius profile ^ 2 :=
      (sq_le_sq₀ (radius_pos profile).le
        (horizontalRadius_pos profile).le).2
        (radius_lt_horizontalRadius profile).le

lemma q_le_horizontalRadius_sq (epsilon y : ℝ) :
    q profile epsilon y ≤ horizontalRadius profile ^ 2 := by
  let w := FrozenSquaredRecovery.junctionWeight epsilon y
  have hw := FrozenSquaredRecovery.junctionWeight_mem_Icc epsilon y
  rw [show q profile epsilon y =
      (1 - w) * sideSquare profile y + w * capSquare profile y by
    unfold q w
    ring]
  calc
    (1 - w) * sideSquare profile y + w * capSquare profile y ≤
        (1 - w) * horizontalRadius profile ^ 2 +
          w * horizontalRadius profile ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (sideSquare_le_horizontalRadius_sq profile y)
          (sub_nonneg.mpr hw.2))
        (mul_le_mul_of_nonneg_left
          (capSquare_le_horizontalRadius_sq profile y) hw.1)
    _ = horizontalRadius profile ^ 2 := by ring

lemma targetQ_le_horizontalRadius_sq (y : ℝ) :
    targetQ profile y ≤ horizontalRadius profile ^ 2 := by
  rw [targetQ]
  split_ifs
  · exact sideSquare_le_horizontalRadius_sq profile y
  · exact capSquare_le_horizontalRadius_sq profile y

/-- Away from the two shrinking junction collars, the smooth squared width is
exactly the profile's piecewise squared width. -/
lemma recovery_q_eq_targetQ_outside_junction
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile)
    (hy : ¬(1 - epsilon < |y| ∧ |y| < 1)) :
    q profile epsilon y = targetQ profile y := by
  by_cases hlow : |y| ≤ 1 - epsilon
  · have honeMinus : 0 ≤ 1 - epsilon := by
      linarith [hepsilon_le, safeScale_le_sixteenth profile]
    have hone : |y| ≤ 1 := hlow.trans (by
      linarith [hepsilon_le, safeScale_le_sixteenth profile])
    rw [targetQ, if_pos hone]
    apply q_eq_side profile hepsilon hepsilon_le
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg y) honeMinus).2 hlow
    simpa only [sq_abs] using hsquare
  · have hhigh : 1 ≤ |y| := by
      by_contra hnot
      exact hy ⟨lt_of_not_ge hlow, lt_of_not_ge hnot⟩
    have hsq : 1 ≤ y ^ 2 := by
      have hsquare :=
        (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 hhigh
      simpa only [sq_abs, one_pow] using hsquare
    rw [q_eq_cap profile hepsilon hepsilon_le hsq]
    by_cases hone : |y| ≤ 1
    · have habs : |y| = 1 := le_antisymm hone hhigh
      have hyEq : y = -1 ∨ y = 1 := by
        rcases le_total 0 y with hy0 | hy0
        · right
          rwa [abs_of_nonneg hy0] at habs
        · left
          rw [abs_of_nonpos hy0] at habs
          linarith
      rcases hyEq with rfl | rfl
      · rw [targetQ, if_pos (by norm_num), sideSquare_neg_one profile,
          capSquare_neg_one profile]
      · rw [targetQ, if_pos (by norm_num), sideSquare_one profile,
          capSquare_one profile]
    · rw [targetQ, if_neg hone]

lemma continuous_targetQ : Continuous (targetQ profile) := by
  unfold targetQ
  apply continuous_if_le continuous_id.abs continuous_const
    (contDiff_sideSquare profile).continuous.continuousOn
    (contDiff_capSquare profile).continuous.continuousOn
  intro y hy
  change |y| = 1 at hy
  have hyEq : y = -1 ∨ y = 1 := by
    rcases le_total 0 y with hy0 | hy0
    · right
      rw [abs_of_nonneg hy0] at hy
      exact hy
    · left
      rw [abs_of_nonpos hy0] at hy
      linarith
  rcases hyEq with rfl | rfl
  · rw [sideSquare_neg_one profile, capSquare_neg_one profile]
  · rw [sideSquare_one profile, capSquare_one profile]


/-- The profilewise recovery differs from the actual carrier only in the two
shrinking junction rectangles, modulo its null squared-width frontier. -/
theorem characteristicDistance_domain_profile_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale profile) :
    characteristicDistance (domain profile epsilon) profile.carrier ≤
      (4 : ℝ≥0∞) * ENNReal.ofReal (horizontalRadius profile) *
        ENNReal.ofReal epsilon := by
  let X : ℝ := horizontalRadius profile
  let L : Set PlanePoint :=
    Icc (-X) X ×ˢ Icc (-1) (-(1 - epsilon))
  let U : Set PlanePoint :=
    Icc (-X) X ×ˢ Icc (1 - epsilon) 1
  let B : Set PlanePoint :=
    {p | p.1 ^ 2 = q profile epsilon p.2}
  have hX : 0 < X := horizontalRadius_pos profile
  have hsubset :
      domain profile epsilon ∆ profile.carrier ⊆ (L ∪ U) ∪ B := by
    intro p hp
    by_cases hband : 1 - epsilon < |p.2| ∧ |p.2| < 1
    · have hx : p.1 ∈ Icc (-X) X := by
        rcases hp with ⟨hpD, _hnotP⟩ | ⟨hpP, _hnotD⟩
        · change p.1 ^ 2 < q profile epsilon p.2 at hpD
          have hq :=
            q_le_horizontalRadius_sq profile epsilon p.2
          change q profile epsilon p.2 ≤ X ^ 2 at hq
          constructor <;> nlinarith
        · have hpTarget : p.1 ^ 2 ≤ targetQ profile p.2 :=
            (mem_profile_iff_sq_le_targetQ profile p).1 hpP
          have ht := targetQ_le_horizontalRadius_sq profile p.2
          change targetQ profile p.2 ≤ X ^ 2 at ht
          constructor <;> nlinarith
      rcases le_total 0 p.2 with hy0 | hy0
      · left
        right
        exact ⟨hx, by
          rw [abs_of_nonneg hy0] at hband
          exact ⟨hband.1.le, hband.2.le⟩⟩
      · left
        left
        exact ⟨hx, by
          rw [abs_of_nonpos hy0] at hband
          constructor <;> linarith [hband.1, hband.2]⟩
    · right
      have hqeq :=
        recovery_q_eq_targetQ_outside_junction profile
          hepsilon hepsilon_le hband
      rcases hp with ⟨hpD, hnotP⟩ | ⟨hpP, hnotD⟩
      · exfalso
        change p.1 ^ 2 < q profile epsilon p.2 at hpD
        exact hnotP ((mem_profile_iff_sq_le_targetQ profile p).2
          (by
            rw [hqeq] at hpD
            exact hpD.le))
      · change p.1 ^ 2 = q profile epsilon p.2
        have hle :=
          (mem_profile_iff_sq_le_targetQ profile p).1 hpP
        have hnlt : ¬p.1 ^ 2 < q profile epsilon p.2 := hnotD
        rw [hqeq]
        rw [hqeq] at hnlt
        exact le_antisymm hle (le_of_not_gt hnlt)
  have hB : volume B = 0 := by
    exact FrozenCanonicalCap.volume_squaredWidthBoundary
      (q profile epsilon) (contDiff_q profile epsilon).continuous
  have hL :
      volume L =
        (2 : ℝ≥0∞) * ENNReal.ofReal X * ENNReal.ofReal epsilon := by
    dsimp only [L]
    rw [Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc,
      show X - -X = 2 * X by ring,
      show -(1 - epsilon) - -1 = epsilon by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hU :
      volume U =
        (2 : ℝ≥0∞) * ENNReal.ofReal X * ENNReal.ofReal epsilon := by
    dsimp only [U]
    rw [Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc,
      show X - -X = 2 * X by ring,
      show (1 : ℝ) - (1 - epsilon) = epsilon by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  change volume (domain profile epsilon ∆ profile.carrier) ≤ _
  calc
    volume (domain profile epsilon ∆ profile.carrier) ≤
        volume ((L ∪ U) ∪ B) :=
      measure_mono hsubset
    _ ≤ volume (L ∪ U) + volume B := measure_union_le _ _
    _ ≤ (volume L + volume U) + volume B :=
      add_le_add (measure_union_le L U) le_rfl
    _ = (4 : ℝ≥0∞) * ENNReal.ofReal (horizontalRadius profile) *
        ENNReal.ofReal epsilon := by
      rw [hL, hU, hB]
      rw [show X = horizontalRadius profile by rfl]
      ring

/-- Positive profilewise scales tending to zero. -/
def recoveryScale (n : ℕ) : ℝ :=
  safeScale profile / ((n : ℝ) + 1)

lemma recoveryScale_pos (n : ℕ) : 0 < recoveryScale profile n := by
  unfold recoveryScale
  exact div_pos (safeScale_pos profile) (by positivity)

lemma recoveryScale_le (n : ℕ) :
    recoveryScale profile n ≤ safeScale profile := by
  unfold recoveryScale
  have hn : 0 ≤ (n : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  nlinarith [safeScale_pos profile]

lemma tendsto_recoveryScale :
    Tendsto (recoveryScale profile) atTop (𝓝 0) := by
  unfold recoveryScale
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- The smooth squared-width approximants for an arbitrary canonical profile. -/
def recoverySequence : SmoothSequence where
  carrier n := domain profile (recoveryScale profile n)
  smooth n := isSmoothDomain_domain profile
    (recoveryScale_pos profile n) (recoveryScale_le profile n)

/-- The profilewise recovery sequence converges globally in characteristic
function distance to the actual five-piece carrier. -/
theorem recoverySequence_converges :
    (recoverySequence profile).ConvergesTo profile.carrier := by
  unfold SmoothSequence.ConvergesTo
  let C : ℝ≥0∞ :=
    (4 : ℝ≥0∞) * ENNReal.ofReal (horizontalRadius profile)
  have hbound : Tendsto
      (fun n : ℕ => C * ENNReal.ofReal (recoveryScale profile n))
      atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun n : ℕ => C * ENNReal.ofReal (recoveryScale profile n))
        atTop (𝓝 (C * ENNReal.ofReal 0)) :=
      ENNReal.Tendsto.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => C) atTop (𝓝 C))
        (by simp [C]) (ENNReal.tendsto_ofReal (tendsto_recoveryScale profile))
        (by
          dsimp [C]
          exact Or.inr (ENNReal.mul_ne_top
            (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) ENNReal.ofReal_ne_top))
    simpa using hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun n => by
      simpa [C, recoverySequence, mul_assoc] using
        characteristicDistance_domain_profile_le profile
          (recoveryScale_pos profile n) (recoveryScale_le profile n))

end CMVRelaxation.ProfileSquaredRecovery
