/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSquaredWidthRecovery

/-!
# Assembly-level squared-width geometry

This module constructs the squared-width recovery directly from a four-arc
assembly.  The strip and exterior radii are independent; the only additional
hypothesis is strict strip curvature.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal MeasureTheory symmDiff

noncomputable section

namespace CMVRelaxation.FourArcSquaredRecovery

/-- A four-arc source whose strip-side circles have radius strictly larger
than the strip half-height. -/
structure StrictFourArcAssembly where
  assembly : FourArcAssembly
  curvature_lt_one : assembly.core.curvature < 1

variable (source : StrictFourArcAssembly)

/-- The half-width of both attachment chords. -/
def StrictFourArcAssembly.attachmentHalfWidth : ℝ :=
  source.assembly.core.chord / 2

/-- Horizontal center coordinate of the right strip-side circle, expressed
without any exterior-radius incidence identity. -/
def StrictFourArcAssembly.sideCenterOffset : ℝ :=
  source.attachmentHalfWidth -
    √(source.assembly.core.radius ^ 2 - 1)

/-- Dimensionless positive strip attachment radial factor. -/
def StrictFourArcAssembly.innerRadial : ℝ :=
  √(1 - source.assembly.core.curvature ^ 2)

lemma radius_pos : 0 < source.assembly.core.radius :=
  source.assembly.core.radius_pos

lemma radius_gt_one : 1 < source.assembly.core.radius := by
  rw [StripCore.radius]
  exact (lt_div_iff₀ source.assembly.core.curvature_pos).2
    (by simpa using source.curvature_lt_one)

lemma sin_outerAngle_pos : 0 < Real.sin source.assembly.outerAngle :=
  Real.sin_pos_of_pos_of_lt_pi source.assembly.outerAngle_pos
    (source.assembly.outerAngle_lt_pi_div_two.trans
      (by linarith [Real.pi_pos]))

lemma cos_outerAngle_pos : 0 < Real.cos source.assembly.outerAngle :=
  Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, source.assembly.outerAngle_pos],
      source.assembly.outerAngle_lt_pi_div_two⟩

lemma attachmentHalfWidth_pos : 0 < source.attachmentHalfWidth := by
  exact div_pos source.assembly.core.chord_pos (by norm_num)

/-- Signed height of the upper exterior-circle center.  This uses the
exterior cap radius, independently of the strip radius. -/
def capCenter : ℝ :=
  1 - source.assembly.upperCap.radius *
    Real.cos source.assembly.outerAngle

lemma capCenter_lt_one : capCenter source < 1 := by
  unfold capCenter
  exact sub_lt_self 1
    (mul_pos source.assembly.upperCap.radius_pos (cos_outerAngle_pos source))

private lemma outerHalfWidth_pos : 0 < source.attachmentHalfWidth :=
  attachmentHalfWidth_pos source

private lemma sin_alpha_pos : 0 < Real.sin source.assembly.outerAngle :=
  sin_outerAngle_pos source

/-- Start of the source-dependent cutoff, strictly above the actual strip. -/
def safeStart : ℝ :=
  (3 + source.assembly.core.radius ^ 2) / 4

/-- End of the source-dependent cutoff, strictly below the radius square. -/
def safeStop : ℝ :=
  (1 + source.assembly.core.radius ^ 2) / 2

lemma one_lt_safeStart : 1 < safeStart source := by
  unfold safeStart
  nlinarith [radius_gt_one source, sq_nonneg (source.assembly.core.radius - 1)]

lemma safeStart_lt_safeStop : safeStart source < safeStop source := by
  unfold safeStart safeStop
  nlinarith [radius_gt_one source, sq_nonneg (source.assembly.core.radius - 1)]

lemma safeStop_lt_radius_sq : safeStop source < source.assembly.core.radius ^ 2 := by
  unfold safeStop
  nlinarith [radius_gt_one source, sq_nonneg (source.assembly.core.radius - 1)]

/-- Smooth global replacement for `y²`. It is exact throughout `|y| ≤ 1`
and stays strictly below the source's radius square everywhere. -/
def safeSquare (y : ℝ) : ℝ :=
  y ^ 2 *
    (1 - Real.smoothTransition
      ((y ^ 2 - safeStart source) /
        (safeStop source - safeStart source)))

lemma safeSquare_eq_sq {y : ℝ} (hy : y ^ 2 ≤ safeStart source) :
    safeSquare source y = y ^ 2 := by
  have hden : 0 < safeStop source - safeStart source :=
    sub_pos.mpr (safeStart_lt_safeStop source)
  have harg :
      (y ^ 2 - safeStart source) /
          (safeStop source - safeStart source) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hden.le
  rw [safeSquare, Real.smoothTransition.zero_of_nonpos harg]
  ring

lemma safeSquare_eq_sq_of_sq_le_one {y : ℝ} (hy : y ^ 2 ≤ 1) :
    safeSquare source y = y ^ 2 :=
  safeSquare_eq_sq source (hy.trans (one_lt_safeStart source).le)

lemma safeSquare_mem_Icc (y : ℝ) :
    safeSquare source y ∈ Icc (0 : ℝ) (safeStop source) := by
  have hχ0 : 0 ≤ Real.smoothTransition
      ((y ^ 2 - safeStart source) /
        (safeStop source - safeStart source)) :=
    Real.smoothTransition.nonneg _
  have hχ1 : Real.smoothTransition
      ((y ^ 2 - safeStart source) /
        (safeStop source - safeStart source)) ≤ 1 :=
    Real.smoothTransition.le_one _
  by_cases hy : y ^ 2 ≤ safeStop source
  · constructor
    · exact mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hχ1)
    · calc
        safeSquare source y ≤ y ^ 2 * 1 := by
          unfold safeSquare
          exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg y)
        _ ≤ safeStop source := by simpa using hy
  · have hden : 0 < safeStop source - safeStart source :=
      sub_pos.mpr (safeStart_lt_safeStop source)
    have harg : 1 ≤
        (y ^ 2 - safeStart source) /
          (safeStop source - safeStart source) := by
      rw [le_div_iff₀ hden]
      simp only [not_le] at hy
      linarith
    rw [safeSquare, Real.smoothTransition.one_of_one_le harg]
    constructor
    · norm_num
    · norm_num only [sub_self, mul_zero]
      exact zero_le_one.trans ((one_lt_safeStart source).le.trans
        (safeStart_lt_safeStop source).le)

lemma safeSquare_lt_radius_sq (y : ℝ) :
    safeSquare source y < source.assembly.core.radius ^ 2 :=
  (safeSquare_mem_Icc source y).2.trans_lt (safeStop_lt_radius_sq source)

lemma contDiff_safeSquare : ContDiff ℝ ∞ (safeSquare source) := by
  unfold safeSquare
  have harg : ContDiff ℝ ∞ (fun y : ℝ =>
      (y ^ 2 - safeStart source) /
        (safeStop source - safeStart source)) :=
    ((contDiff_id.pow 2).sub contDiff_const).div_const _
  exact (contDiff_id.pow 2).mul
    (contDiff_const.sub (Real.smoothTransition.contDiff.comp harg))

/-- Globally smooth extension of the strip-side squared half-width. -/
def sideSquare (y : ℝ) : ℝ :=
  (source.sideCenterOffset +
    √(source.assembly.core.radius ^ 2 - safeSquare source y)) ^ 2

lemma contDiff_sideSquare : ContDiff ℝ ∞ (sideSquare source) := by
  have hrad : ∀ y, source.assembly.core.radius ^ 2 - safeSquare source y ≠ 0 := by
    intro y
    exact (sub_pos.mpr (safeSquare_lt_radius_sq source y)).ne'
  unfold sideSquare
  exact (contDiff_const.add
    ((contDiff_const.sub (contDiff_safeSquare source)).sqrt hrad)).pow 2

lemma sideSquare_eq_actual {y : ℝ} (hy : y ^ 2 ≤ 1) :
    sideSquare source y =
      (source.sideCenterOffset + √(source.assembly.core.radius ^ 2 - y ^ 2)) ^ 2 := by
  rw [sideSquare, safeSquare_eq_sq_of_sq_le_one source hy]

/-- Smooth extension of the exterior-cap squared half-width. -/
def capSquare (y : ℝ) : ℝ :=
  source.assembly.upperCap.radius ^ 2 -
    (FrozenSquaredRecovery.smoothAbs y - capCenter source) ^ 2

lemma contDiff_capSquare : ContDiff ℝ ∞ (capSquare source) := by
  unfold capSquare
  exact contDiff_const.sub
    ((FrozenSquaredRecovery.contDiff_smoothAbs.sub contDiff_const).pow 2)

lemma capSquare_eq_actual_of_half_le_abs {y : ℝ} (hy : 1 / 2 ≤ |y|) :
    capSquare source y =
      source.assembly.upperCap.radius ^ 2 -
        (|y| - capCenter source) ^ 2 := by
  rw [capSquare, FrozenSquaredRecovery.smoothAbs_eq_of_half_le_abs hy]


lemma inner_argument_pos : 0 < 1 - source.assembly.core.curvature ^ 2 := by
  nlinarith [source.assembly.core.curvature_pos, source.curvature_lt_one]

lemma innerRadial_pos : 0 < source.innerRadial := by
  rw [StrictFourArcAssembly.innerRadial]
  exact Real.sqrt_pos.2 (inner_argument_pos source)

lemma radius_mul_innerRadial_sq :
    (source.assembly.core.radius * source.innerRadial) ^ 2 =
      source.assembly.core.radius ^ 2 - 1 := by
  rw [StripCore.radius, StrictFourArcAssembly.innerRadial,
    mul_pow, Real.sq_sqrt (inner_argument_pos source).le]
  field_simp [source.assembly.core.curvature_pos.ne']

lemma sqrt_radius_sq_sub_one :
    √(source.assembly.core.radius ^ 2 - 1) =
      source.assembly.core.radius * source.innerRadial := by
  rw [← radius_mul_innerRadial_sq source, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos (radius_pos source) (innerRadial_pos source))]

lemma sideCenterOffset_add_attachment :
    source.sideCenterOffset +
        source.assembly.core.radius * source.innerRadial =
      source.attachmentHalfWidth := by
  rw [StrictFourArcAssembly.sideCenterOffset,
    sqrt_radius_sq_sub_one source]
  ring

lemma sideSquare_one :
    sideSquare source 1 = source.attachmentHalfWidth ^ 2 := by
  rw [sideSquare_eq_actual source (by norm_num : (1 : ℝ) ^ 2 ≤ 1)]
  norm_num only [one_pow]
  rw [sqrt_radius_sq_sub_one source, sideCenterOffset_add_attachment source]

lemma sideSquare_neg_one :
    sideSquare source (-1) = source.attachmentHalfWidth ^ 2 := by
  rw [sideSquare_eq_actual source (by norm_num : (-1 : ℝ) ^ 2 ≤ 1)]
  norm_num only [neg_sq, one_pow]
  rw [sqrt_radius_sq_sub_one source, sideCenterOffset_add_attachment source]

lemma one_sub_capCenter :
    1 - capCenter source =
      source.assembly.upperCap.radius *
        Real.cos source.assembly.outerAngle := by
  unfold capCenter
  ring

lemma outerHalfWidth_sq :
    source.attachmentHalfWidth ^ 2 =
      source.assembly.upperCap.radius ^ 2 -
        (1 - capCenter source) ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq source.assembly.outerAngle
  have hchord :
      source.assembly.upperCap.radius *
          Real.sin source.assembly.outerAngle =
        source.attachmentHalfWidth := by
    simpa [StrictFourArcAssembly.attachmentHalfWidth,
      FourArcAssembly.upperCap] using
        source.assembly.upperCap.radius_mul_sin
  have hattach :
      source.attachmentHalfWidth =
        source.assembly.upperCap.radius *
          Real.sin source.assembly.outerAngle :=
    hchord.symm
  rw [hattach, one_sub_capCenter source]
  nlinarith

lemma capSquare_one :
    capSquare source 1 = source.attachmentHalfWidth ^ 2 := by
  rw [capSquare_eq_actual_of_half_le_abs source (by norm_num)]
  norm_num only [abs_one]
  exact (outerHalfWidth_sq source).symm

lemma capSquare_neg_one :
    capSquare source (-1) = source.attachmentHalfWidth ^ 2 := by
  rw [capSquare_eq_actual_of_half_le_abs source (by norm_num)]
  norm_num only [abs_neg, abs_one]
  exact (outerHalfWidth_sq source).symm

/-- The two extensions have the same strictly positive squared width at both
source interfaces. -/
theorem attachmentSquares :
    sideSquare source 1 = capSquare source 1 ∧
      sideSquare source (-1) = capSquare source (-1) ∧
      0 < source.attachmentHalfWidth ^ 2 := by
  constructor
  · rw [sideSquare_one source, capSquare_one source]
  constructor
  · rw [sideSquare_neg_one source, capSquare_neg_one source]
  · exact sq_pos_of_pos (outerHalfWidth_pos source)

/-- The largest junction scale used by the sourcewise geometry.  It is
constructed solely from the source and stays below both `1/16` and the
positive cap attachment height. -/
def safeScale : ℝ :=
  min (1 / 16) (1 - capCenter source)

lemma safeScale_pos : 0 < safeScale source := by
  rw [safeScale, lt_min_iff]
  exact ⟨by norm_num, sub_pos.mpr (capCenter_lt_one source)⟩

lemma safeScale_le_sixteenth : safeScale source ≤ 1 / 16 :=
  min_le_left _ _

lemma safeScale_le_half : safeScale source ≤ 1 / 2 :=
  (safeScale_le_sixteenth source).trans (by norm_num)

lemma safeScale_le_one_sub_capCenter :
    safeScale source ≤ 1 - capCenter source :=
  min_le_right _ _

lemma sideSquare_ge_attachment {y : ℝ} (hy : |y| ≤ 1) :
    source.attachmentHalfWidth ^ 2 ≤ sideSquare source y := by
  have hysq : y ^ 2 ≤ 1 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)).2 hy
    simpa only [sq_abs, one_pow] using hsquare
  have hrad : 0 ≤ source.assembly.core.radius ^ 2 - y ^ 2 := by
    nlinarith [radius_gt_one source]
  have hroot :
      √(source.assembly.core.radius ^ 2 - 1) ≤
        √(source.assembly.core.radius ^ 2 - y ^ 2) := by
    exact Real.sqrt_le_sqrt (by linarith)
  have hwidth :
      source.attachmentHalfWidth ≤
        source.sideCenterOffset +
          √(source.assembly.core.radius ^ 2 - y ^ 2) := by
    rw [← sideCenterOffset_add_attachment source,
      ← sqrt_radius_sq_sub_one source]
    linarith
  rw [sideSquare_eq_actual source hysq]
  exact (sq_le_sq₀ (outerHalfWidth_pos source).le
    ((outerHalfWidth_pos source).le.trans hwidth)).2 hwidth

lemma capSquare_ge_attachment
    {epsilon y : ℝ}
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : |y| ∈ Icc (1 - epsilon : ℝ) 1) :
    source.attachmentHalfWidth ^ 2 ≤ capSquare source y := by
  have hepsilon_half : epsilon ≤ 1 / 2 :=
    hepsilon_le.trans (safeScale_le_half source)
  have habs_half : 1 / 2 ≤ |y| := by linarith [hy.1]
  have hcap_le_abs : capCenter source ≤ |y| := by
    have := hepsilon_le.trans (safeScale_le_one_sub_capCenter source)
    linarith [hy.1]
  have hgap0 : 0 ≤ |y| - capCenter source := sub_nonneg.mpr hcap_le_abs
  have hgap_le : |y| - capCenter source ≤ 1 - capCenter source := by
    linarith [hy.2]
  have honeGap0 : 0 ≤ 1 - capCenter source :=
    sub_nonneg.mpr (capCenter_lt_one source).le
  have hsq :
      (|y| - capCenter source) ^ 2 ≤
        (1 - capCenter source) ^ 2 :=
    (sq_le_sq₀ hgap0 honeGap0).2 hgap_le
  rw [capSquare_eq_actual_of_half_le_abs source habs_half,
    outerHalfWidth_sq source]
  linarith

/-- Profilewise squared-width blend across the two junction collars. -/
def q (epsilon y : ℝ) : ℝ :=
  sideSquare source y +
    FrozenSquaredRecovery.junctionWeight epsilon y *
      (capSquare source y - sideSquare source y)

lemma contDiff_q (epsilon : ℝ) : ContDiff ℝ ∞ (q source epsilon) := by
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
  exact (contDiff_sideSquare source).add
    (hweight.mul ((contDiff_capSquare source).sub
      (contDiff_sideSquare source)))

lemma q_eq_side
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : y ^ 2 ≤ (1 - epsilon) ^ 2) :
    q source epsilon y = sideSquare source y := by
  rw [q, FrozenSquaredRecovery.junctionWeight_eq_zero hepsilon
    (hepsilon_le.trans (safeScale_le_sixteenth source)) hy]
  ring

lemma q_eq_cap
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : 1 ≤ y ^ 2) :
    q source epsilon y = capSquare source y := by
  rw [q, FrozenSquaredRecovery.junctionWeight_eq_one hepsilon
    (hepsilon_le.trans (safeScale_le_sixteenth source)) hy]
  ring

/-- Both actual source widths and therefore their smooth convex blend stay
above the positive attachment square on the internally constructed collar. -/
theorem q_ge_positive_attachment
    {epsilon y : ℝ} (_hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : |y| ∈ Icc (1 - epsilon : ℝ) 1) :
    0 < source.attachmentHalfWidth ^ 2 ∧
      source.attachmentHalfWidth ^ 2 ≤ q source epsilon y := by
  have hs := sideSquare_ge_attachment source hy.2
  have hc := capSquare_ge_attachment source hepsilon_le hy
  let w := FrozenSquaredRecovery.junctionWeight epsilon y
  have hw := FrozenSquaredRecovery.junctionWeight_mem_Icc epsilon y
  constructor
  · exact sq_pos_of_pos (outerHalfWidth_pos source)
  · rw [show q source epsilon y =
        (1 - w) * sideSquare source y + w * capSquare source y by
      unfold q w
      ring]
    calc
      source.attachmentHalfWidth ^ 2 =
          (1 - w) * source.attachmentHalfWidth ^ 2 +
            w * source.attachmentHalfWidth ^ 2 := by ring
      _ ≤ (1 - w) * sideSquare source y + w * capSquare source y :=
        add_le_add
          (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hw.2))
          (mul_le_mul_of_nonneg_left hc hw.1)


/-- Piecewise squared half-width of the actual closed assembly carrier. -/
def targetQ (y : ℝ) : ℝ :=
  if |y| ≤ 1 then sideSquare source y else capSquare source y

/-- Every interface and pole is included: the actual five-piece closed source
carrier is exactly the non-strict squared-width sublevel. -/
theorem mem_source_iff_sq_le_targetQ (p : PlanePoint) :
    p ∈ source.assembly.carrier ↔ p.1 ^ 2 ≤ targetQ source p.2 := by
  have hWpos := outerHalfWidth_pos source
  have hRpos := radius_pos source
  have hRone := radius_gt_one source
  have hattachPos :
      0 < source.assembly.core.radius * source.innerRadial :=
    mul_pos hRpos (innerRadial_pos source)
  have hRt : source.assembly.core.rightCenterX =
      source.sideCenterOffset := by
    rw [StripCore.rightCenterX, source.assembly.core.cos_sideAngle]
    change source.assembly.core.chord / 2 -
        source.assembly.core.radius * source.innerRadial =
      source.sideCenterOffset
    rw [← sqrt_radius_sq_sub_one source]
    rfl
  have hL : source.assembly.core.leftCenterX =
      -source.sideCenterOffset := by
    rw [StripCore.leftCenterX, source.assembly.core.cos_sideAngle]
    change -source.assembly.core.chord / 2 +
        source.assembly.core.radius * source.innerRadial =
      -source.sideCenterOffset
    rw [← sqrt_radius_sq_sub_one source,
      StrictFourArcAssembly.sideCenterOffset,
      StrictFourArcAssembly.attachmentHalfWidth]
    ring
  have hhalf :
      source.assembly.core.chord / 2 = source.attachmentHalfWidth := rfl
  simp only [FourArcAssembly.carrier, StripCore.carrier,
    StripCore.rectangleCarrier, StripCore.leftCapCarrier,
    StripCore.rightCapCarrier, OneSidedCircularCap.carrier,
    OneSidedCircularCap.radiusSquaredAt, OneSidedCircularCap.center,
    FourArcAssembly.upperCap, FourArcAssembly.lowerCap,
    Set.mem_union, Set.mem_ofPred_eq, hL, hRt, hhalf,
    sub_zero, sub_neg_eq_add, targetQ]
  by_cases hy : |p.2| ≤ 1
  · rw [if_pos hy]
    have hysq : p.2 ^ 2 ≤ 1 := by
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 1)).2 hy
      simpa only [sq_abs, one_pow] using hsquare
    rw [sideSquare_eq_actual source hysq]
    have hrad : 0 ≤ source.assembly.core.radius ^ 2 - p.2 ^ 2 := by
      nlinarith
    have hroot0 : 0 ≤ √(source.assembly.core.radius ^ 2 - p.2 ^ 2) :=
      Real.sqrt_nonneg _
    have hrootSq :
        (√(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ^ 2 =
          source.assembly.core.radius ^ 2 - p.2 ^ 2 :=
      Real.sq_sqrt hrad
    have hroot :
        source.assembly.core.radius * source.innerRadial ≤
          √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
      rw [← sqrt_radius_sq_sub_one source]
      exact Real.sqrt_le_sqrt (by linarith)
    have hwidth :
        source.attachmentHalfWidth ≤
          source.sideCenterOffset +
            √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
      rw [← sideCenterOffset_add_attachment source]
      linarith
    have hwidth0 :
        0 ≤ source.sideCenterOffset +
          √(source.assembly.core.radius ^ 2 - p.2 ^ 2) :=
      hWpos.le.trans hwidth
    constructor
    · rintro ((((hrect | hleft) | hright) | hupper) | hlower)
      · rcases hrect with ⟨hxlo, hxhi, _⟩
        have hxlo' : -source.attachmentHalfWidth ≤ p.1 := by
          rw [← hhalf]
          linarith
        have hxhi' : p.1 ≤ source.attachmentHalfWidth := by
          rwa [← hhalf]
        have habsx : |p.1| ≤ source.attachmentHalfWidth :=
          (abs_le).2 ⟨hxlo', hxhi'⟩
        have hsquared :=
          (sq_le_sq₀ (abs_nonneg p.1) hWpos.le).2 habsx
        have hWsq := (sq_le_sq₀ hWpos.le hwidth0).2 hwidth
        simpa only [sq_abs] using hsquared.trans hWsq
      · rcases hleft with ⟨hdisk, hxside, _⟩
        have hxside' : p.1 ≤ -source.attachmentHalfWidth := by
          rw [← hhalf]
          linarith
        have hx0 : p.1 ≤ 0 := by linarith
        have hshift0 : p.1 + source.sideCenterOffset ≤ 0 := by
          rw [← sideCenterOffset_add_attachment source] at hxside'
          linarith
        have hshiftSq :
            (p.1 + source.sideCenterOffset) ^ 2 ≤
              (√(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
          nlinarith
        have hshiftAbs :
            |p.1 + source.sideCenterOffset| ≤
              √(source.assembly.core.radius ^ 2 - p.2 ^ 2) :=
          (sq_le_sq₀ (abs_nonneg _) hroot0).1
            (by simpa only [sq_abs] using hshiftSq)
        rw [abs_of_nonpos hshift0] at hshiftAbs
        have habsx :
            |p.1| ≤ source.sideCenterOffset +
              √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
          rw [abs_of_nonpos hx0]
          linarith
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg p.1) hwidth0).2 habsx
      · rcases hright with ⟨hdisk, hxside, _⟩
        change source.attachmentHalfWidth ≤ p.1 at hxside
        have hx0 : 0 ≤ p.1 := by linarith
        have hshift0 : 0 ≤ p.1 - source.sideCenterOffset := by
          rw [← sideCenterOffset_add_attachment source] at hxside
          linarith
        have hshiftSq :
            (p.1 - source.sideCenterOffset) ^ 2 ≤
              (√(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
          nlinarith
        have hshiftAbs :
            |p.1 - source.sideCenterOffset| ≤
              √(source.assembly.core.radius ^ 2 - p.2 ^ 2) :=
          (sq_le_sq₀ (abs_nonneg _) hroot0).1
            (by simpa only [sq_abs] using hshiftSq)
        rw [abs_of_nonneg hshift0] at hshiftAbs
        have habsx :
            |p.1| ≤ source.sideCenterOffset +
              √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
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
        rw [sqrt_radius_sq_sub_one source,
          sideCenterOffset_add_attachment source]
        rw [hyeq] at hdisk
        change p.1 ^ 2 + (1 - capCenter source) ^ 2 ≤
          source.assembly.upperCap.radius ^ 2 at hdisk
        have houter := outerHalfWidth_sq source
        nlinarith
      · rcases hlower with ⟨hdisk, hylower⟩
        have hyeq : p.2 = -1 := by
          have := (neg_le_abs p.2).trans hy
          linarith
        rw [hyeq]
        norm_num only [neg_sq, one_pow]
        rw [sqrt_radius_sq_sub_one source,
          sideCenterOffset_add_attachment source]
        rw [hyeq] at hdisk
        have hdisk' :
            p.1 ^ 2 + (1 - capCenter source) ^ 2 ≤
              source.assembly.upperCap.radius ^ 2 := by
          dsimp [FourArcAssembly.lowerCap, FourArcAssembly.upperCap,
            OneSidedCircularCap.radius, capCenter] at hdisk ⊢
          nlinarith
        have houter := outerHalfWidth_sq source
        nlinarith
    · intro hx
      have habsx :
          |p.1| ≤ source.sideCenterOffset +
            √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
        exact (sq_le_sq₀ (abs_nonneg p.1) hwidth0).1
          (by simpa only [sq_abs] using hx)
      by_cases hxleft : p.1 ≤ -source.attachmentHalfWidth
      · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
        have hxleftCore :
            p.1 ≤ -source.assembly.core.chord / 2 := by
          linarith [hhalf, hxleft]
        have hxlower :
            -(source.sideCenterOffset +
              √(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ≤ p.1 :=
          neg_le_of_abs_le habsx
        have hshift0 : p.1 + source.sideCenterOffset ≤ 0 := by
          rw [← sideCenterOffset_add_attachment source] at hxleft
          linarith
        have hshiftAbs :
            |p.1 + source.sideCenterOffset| ≤
              √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
          rw [abs_of_nonpos hshift0]
          linarith
        have hshiftSq :
            (p.1 + source.sideCenterOffset) ^ 2 ≤
              (√(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) hroot0).2 hshiftAbs
        refine ⟨?_, hxleftCore, hy⟩
        calc
          (p.1 + source.sideCenterOffset) ^ 2 + p.2 ^ 2 ≤
              (√(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ^ 2 +
                p.2 ^ 2 := by nlinarith [hshiftSq]
          _ = source.assembly.core.radius ^ 2 := by
            rw [hrootSq]
            ring
      · by_cases hxright : source.attachmentHalfWidth ≤ p.1
        · refine Or.inl (Or.inl (Or.inr ?_))
          have hxrightCore :
              source.assembly.core.chord / 2 ≤ p.1 := by
            simpa [StrictFourArcAssembly.attachmentHalfWidth] using hxright
          refine ⟨?_, hxrightCore, hy⟩
          have hxupper :
              p.1 ≤ source.sideCenterOffset +
                √(source.assembly.core.radius ^ 2 - p.2 ^ 2) :=
            le_of_abs_le habsx
          have hshift0 : 0 ≤ p.1 - source.sideCenterOffset := by
            rw [← sideCenterOffset_add_attachment source] at hxright
            linarith
          have hshiftAbs :
              |p.1 - source.sideCenterOffset| ≤
                √(source.assembly.core.radius ^ 2 - p.2 ^ 2) := by
            rw [abs_of_nonneg hshift0]
            linarith
          have hshiftSq :
              (p.1 - source.sideCenterOffset) ^ 2 ≤
                (√(source.assembly.core.radius ^ 2 - p.2 ^ 2)) ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg _) hroot0).2 hshiftAbs
          nlinarith
        · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
          have hxlo : -source.assembly.core.chord / 2 ≤ p.1 := by
            linarith [hhalf, le_of_not_ge hxleft]
          have hxhi : p.1 ≤ source.assembly.core.chord / 2 := by
            simpa [StrictFourArcAssembly.attachmentHalfWidth] using
              (le_of_not_ge hxright)
          exact ⟨hxlo, hxhi, hy⟩
  · rw [if_neg hy]
    have hy' : 1 < |p.2| := lt_of_not_ge hy
    rw [capSquare_eq_actual_of_half_le_abs source (by linarith)]
    simp only [hy, and_false, or_false]
    rcases le_total 0 p.2 with hy0 | hy0
    · have hpos : 1 < p.2 := by
        rw [abs_of_nonneg hy0] at hy'
        exact hy'
      have hnotLower : ¬p.2 ≤ -1 := by linarith
      simp only [hpos.le, hnotLower, and_false, or_false, false_or, and_true,
        abs_of_nonneg hy0]
      change
        (p.1 ^ 2 + (p.2 - capCenter source) ^ 2 ≤
            source.assembly.upperCap.radius ^ 2) ↔
          p.1 ^ 2 ≤ source.assembly.upperCap.radius ^ 2 -
            (p.2 - capCenter source) ^ 2
      constructor <;> intro h <;> nlinarith
    · have hneg : p.2 < -1 := by
        rw [abs_of_nonpos hy0] at hy'
        linarith
      have hnotUpper : ¬1 ≤ p.2 := by linarith
      simp only [hneg.le, hnotUpper, and_false, false_or, or_false, and_true,
        abs_of_nonpos hy0]
      constructor
      · intro h
        dsimp [FourArcAssembly.lowerCap, FourArcAssembly.upperCap,
          OneSidedCircularCap.radius, capCenter] at h ⊢
        nlinarith
      · intro h
        dsimp [FourArcAssembly.lowerCap, FourArcAssembly.upperCap,
          OneSidedCircularCap.radius, capCenter] at h ⊢
        nlinarith


/-- The height of either exterior cap pole. -/
def poleHeight : ℝ :=
  source.assembly.upperCap.radius + capCenter source

lemma poleHeight_gt_one : 1 < poleHeight source := by
  have hcosLt : Real.cos source.assembly.outerAngle < 1 := by
    have hanti := Real.strictAntiOn_cos
      (by
        exact (show (0 : ℝ) ∈ Icc 0 Real.pi from
          ⟨le_rfl, Real.pi_pos.le⟩))
      (by
        exact (show source.assembly.outerAngle ∈ Icc 0 Real.pi from
          ⟨source.assembly.outerAngle_pos.le,
            (source.assembly.outerAngle_lt_pi_div_two.trans
              (by linarith [Real.pi_pos])).le⟩))
      source.assembly.outerAngle_pos
    simpa using hanti
  unfold poleHeight capCenter
  nlinarith [source.assembly.upperCap.radius_pos]

lemma q_pos_of_abs_lt_one
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : |y| < 1) :
    0 < q source epsilon y := by
  have honeMinus : 0 ≤ 1 - epsilon := by
    linarith [hepsilon_le, safeScale_le_sixteenth source]
  by_cases hcentral : |y| ≤ 1 - epsilon
  · have hsq : y ^ 2 ≤ (1 - epsilon) ^ 2 := by
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg y) honeMinus).2 hcentral
      simpa only [sq_abs] using hsquare
    rw [q_eq_side source hepsilon hepsilon_le hsq]
    exact lt_of_lt_of_le
      (sq_pos_of_pos (outerHalfWidth_pos source))
      (sideSquare_ge_attachment source hy.le)
  · have hcollar : |y| ∈ Icc (1 - epsilon : ℝ) 1 :=
      ⟨le_of_not_ge hcentral, hy.le⟩
    exact lt_of_lt_of_le
      (q_ge_positive_attachment source hepsilon hepsilon_le hcollar).1
      (q_ge_positive_attachment source hepsilon hepsilon_le hcollar).2

lemma one_le_abs_of_q_eq_zero
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : q source epsilon y = 0) :
    1 ≤ |y| := by
  by_contra hnot
  exact (q_pos_of_abs_lt_one source hepsilon hepsilon_le
    (lt_of_not_ge hnot)).ne' hy

lemma abs_eq_poleHeight_of_q_eq_zero
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : q source epsilon y = 0) :
    |y| = poleHeight source := by
  have habs := one_le_abs_of_q_eq_zero source hepsilon hepsilon_le hy
  have hsq : 1 ≤ y ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 habs
    simpa only [sq_abs, one_pow] using hsquare
  have hhalf : 1 / 2 ≤ |y| := by linarith
  rw [q_eq_cap source hepsilon hepsilon_le hsq,
    capSquare_eq_actual_of_half_le_abs source hhalf] at hy
  have hgap : 0 ≤ |y| - capCenter source := by
    linarith [capCenter_lt_one source]
  have hR := source.assembly.upperCap.radius_pos
  unfold poleHeight
  nlinarith

lemma q_eq_zero_iff
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    q source epsilon y = 0 ↔
      y = -poleHeight source ∨ y = poleHeight source := by
  constructor
  · intro hy
    have habs :=
      abs_eq_poleHeight_of_q_eq_zero source hepsilon hepsilon_le hy
    rcases le_total 0 y with hy0 | hy0
    · right
      rwa [abs_of_nonneg hy0] at habs
    · left
      rw [abs_of_nonpos hy0] at habs
      linarith
  · rintro (rfl | rfl)
    · have hp : 1 < poleHeight source := poleHeight_gt_one source
      have hsq : 1 ≤ (-poleHeight source) ^ 2 := by
        nlinarith [sq_nonneg (poleHeight source - 1)]
      rw [q_eq_cap source hepsilon hepsilon_le hsq,
        capSquare_eq_actual_of_half_le_abs source]
      · rw [abs_neg, abs_of_pos (by linarith : 0 < poleHeight source)]
        unfold poleHeight
        ring
      · rw [abs_neg, abs_of_pos (by linarith : 0 < poleHeight source)]
        linarith
    · have hp : 1 < poleHeight source := poleHeight_gt_one source
      have hsq : 1 ≤ poleHeight source ^ 2 := by
        nlinarith [sq_nonneg (poleHeight source - 1)]
      rw [q_eq_cap source hepsilon hepsilon_le hsq,
        capSquare_eq_actual_of_half_le_abs source]
      · rw [abs_of_pos (by linarith : 0 < poleHeight source)]
        unfold poleHeight
        ring
      · rw [abs_of_pos (by linarith : 0 < poleHeight source)]
        linarith

lemma q_eventuallyEq_upperCap
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    q source epsilon =ᶠ[𝓝 (poleHeight source)]
      (fun y : ℝ =>
        source.assembly.upperCap.radius ^ 2 -
          (y - capCenter source) ^ 2) := by
  filter_upwards [Ioi_mem_nhds (poleHeight_gt_one source)] with y hy
  change (1 : ℝ) < y at hy
  have hy0 : 0 ≤ y := by linarith
  have hsq : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  rw [q_eq_cap source hepsilon hepsilon_le hsq, capSquare,
    FrozenSquaredRecovery.smoothAbs_eq_of_half_le_abs]
  · rw [abs_of_nonneg hy0]
  · rw [abs_of_nonneg hy0]
    linarith

lemma q_eventuallyEq_lowerCap
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    q source epsilon =ᶠ[𝓝 (-poleHeight source)]
      (fun y : ℝ =>
        source.assembly.upperCap.radius ^ 2 -
          (y + capCenter source) ^ 2) := by
  have hp : -poleHeight source < (-1 : ℝ) := by
    linarith [poleHeight_gt_one source]
  filter_upwards [Iio_mem_nhds hp] with y hy
  change y < (-1 : ℝ) at hy
  have hy0 : y ≤ 0 := by linarith
  have hsq : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y + 1)]
  rw [q_eq_cap source hepsilon hepsilon_le hsq, capSquare,
    FrozenSquaredRecovery.smoothAbs_eq_of_half_le_abs]
  · rw [abs_of_nonpos hy0]
    ring
  · rw [abs_of_nonpos hy0]
    linarith

lemma hasDerivAt_q_upperPole
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    HasDerivAt (q source epsilon)
      (-2 * source.assembly.upperCap.radius)
      (poleHeight source) := by
  have hpoly : HasDerivAt
      (fun y : ℝ =>
        source.assembly.upperCap.radius ^ 2 -
          (y - capCenter source) ^ 2)
      (-2 * source.assembly.upperCap.radius) (poleHeight source) := by
    have hraw :=
      (hasDerivAt_const (poleHeight source)
        (source.assembly.upperCap.radius ^ 2)).sub
        (((hasDerivAt_id (poleHeight source)).sub_const
          (capCenter source)).pow 2)
    simpa [Pi.sub_apply, poleHeight] using! hraw
  exact hpoly.congr_of_eventuallyEq
    (q_eventuallyEq_upperCap source hepsilon hepsilon_le)

lemma hasDerivAt_q_lowerPole
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    HasDerivAt (q source epsilon)
      (2 * source.assembly.upperCap.radius)
      (-poleHeight source) := by
  have hpoly : HasDerivAt
      (fun y : ℝ =>
        source.assembly.upperCap.radius ^ 2 -
          (y + capCenter source) ^ 2)
      (2 * source.assembly.upperCap.radius) (-poleHeight source) := by
    have hraw :=
      (hasDerivAt_const (-poleHeight source)
        (source.assembly.upperCap.radius ^ 2)).sub
        (((hasDerivAt_id (-poleHeight source)).add_const
          (capCenter source)).pow 2)
    simpa [Pi.sub_apply, poleHeight] using! hraw
  exact hpoly.congr_of_eventuallyEq
    (q_eventuallyEq_lowerCap source hepsilon hepsilon_le)

lemma q_regularZeros
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    ∀ y, q source epsilon y = 0 →
      deriv (q source epsilon) y ≠ 0 := by
  intro y hy
  rcases (q_eq_zero_iff source hepsilon hepsilon_le).1 hy with rfl | rfl
  · rw [(hasDerivAt_q_lowerPole source hepsilon hepsilon_le).deriv]
    exact mul_ne_zero (by norm_num)
      source.assembly.upperCap.radius_pos.ne'
  · rw [(hasDerivAt_q_upperPole source hepsilon hepsilon_le).deriv]
    exact mul_ne_zero (by norm_num)
      source.assembly.upperCap.radius_pos.ne'

/-- The sourcewise smooth recovery domain. -/
def domain (epsilon : ℝ) : Set PlanePoint :=
  squaredWidthDomain (q source epsilon)

/-- Every internally admissible positive scale gives one global smooth domain,
including both moving collars and the two cap poles. -/
theorem isSmoothDomain_domain
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    IsSmoothDomain (domain source epsilon) := by
  unfold domain
  exact isSmoothDomain_squaredWidth (contDiff_q source epsilon)
    (q_regularZeros source hepsilon hepsilon_le)


/-- A source-dependent finite horizontal radius containing every recovery and
target section. -/
def horizontalRadius : ℝ :=
  |source.sideCenterOffset| + 2 * source.assembly.core.radius +
    source.assembly.upperCap.radius

lemma horizontalRadius_pos : 0 < horizontalRadius source := by
  unfold horizontalRadius
  nlinarith [abs_nonneg source.sideCenterOffset,
    source.assembly.core.radius_pos, source.assembly.upperCap.radius_pos]

lemma radius_lt_horizontalRadius :
    source.assembly.core.radius < horizontalRadius source := by
  unfold horizontalRadius
  nlinarith [abs_nonneg source.sideCenterOffset,
    source.assembly.core.radius_pos, source.assembly.upperCap.radius_pos]

lemma capRadius_lt_horizontalRadius :
    source.assembly.upperCap.radius < horizontalRadius source := by
  unfold horizontalRadius
  nlinarith [abs_nonneg source.sideCenterOffset,
    source.assembly.core.radius_pos]

lemma sideSquare_le_horizontalRadius_sq (y : ℝ) :
    sideSquare source y ≤ horizontalRadius source ^ 2 := by
  have hsafe0 := (safeSquare_mem_Icc source y).1
  have hrad :
      0 ≤ source.assembly.core.radius ^ 2 - safeSquare source y :=
    (sub_pos.mpr (safeSquare_lt_radius_sq source y)).le
  have hsqrtSq :
      (√(source.assembly.core.radius ^ 2 - safeSquare source y)) ^ 2 =
        source.assembly.core.radius ^ 2 - safeSquare source y :=
    Real.sq_sqrt hrad
  have hsqrt0 :
      0 ≤ √(source.assembly.core.radius ^ 2 - safeSquare source y) :=
    Real.sqrt_nonneg _
  have hsqrt_le :
      √(source.assembly.core.radius ^ 2 - safeSquare source y) ≤
        source.assembly.core.radius := by
    nlinarith [radius_pos source]
  have hupper :
      source.sideCenterOffset +
          √(source.assembly.core.radius ^ 2 - safeSquare source y) ≤
        horizontalRadius source := by
    unfold horizontalRadius
    nlinarith [le_abs_self source.sideCenterOffset,
      source.assembly.core.radius_pos, source.assembly.upperCap.radius_pos]
  have hlower :
      -horizontalRadius source ≤
        source.sideCenterOffset +
          √(source.assembly.core.radius ^ 2 - safeSquare source y) := by
    unfold horizontalRadius
    nlinarith [neg_abs_le source.sideCenterOffset,
      source.assembly.core.radius_pos, source.assembly.upperCap.radius_pos]
  have habs :
      |source.sideCenterOffset +
          √(source.assembly.core.radius ^ 2 - safeSquare source y)| ≤
        horizontalRadius source :=
    (abs_le).2 ⟨hlower, hupper⟩
  have hsquared :=
    (sq_le_sq₀
      (abs_nonneg
        (source.sideCenterOffset +
          √(source.assembly.core.radius ^ 2 - safeSquare source y)))
      (horizontalRadius_pos source).le).2 habs
  rw [sideSquare]
  simpa only [sq_abs] using hsquared

lemma capSquare_le_horizontalRadius_sq (y : ℝ) :
    capSquare source y ≤ horizontalRadius source ^ 2 := by
  calc
    capSquare source y ≤ source.assembly.upperCap.radius ^ 2 := by
      unfold capSquare
      nlinarith [sq_nonneg
        (FrozenSquaredRecovery.smoothAbs y - capCenter source)]
    _ ≤ horizontalRadius source ^ 2 :=
      (sq_le_sq₀ source.assembly.upperCap.radius_pos.le
        (horizontalRadius_pos source).le).2
        (capRadius_lt_horizontalRadius source).le

lemma q_le_horizontalRadius_sq (epsilon y : ℝ) :
    q source epsilon y ≤ horizontalRadius source ^ 2 := by
  let w := FrozenSquaredRecovery.junctionWeight epsilon y
  have hw := FrozenSquaredRecovery.junctionWeight_mem_Icc epsilon y
  rw [show q source epsilon y =
      (1 - w) * sideSquare source y + w * capSquare source y by
    unfold q w
    ring]
  calc
    (1 - w) * sideSquare source y + w * capSquare source y ≤
        (1 - w) * horizontalRadius source ^ 2 +
          w * horizontalRadius source ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (sideSquare_le_horizontalRadius_sq source y)
          (sub_nonneg.mpr hw.2))
        (mul_le_mul_of_nonneg_left
          (capSquare_le_horizontalRadius_sq source y) hw.1)
    _ = horizontalRadius source ^ 2 := by ring

lemma targetQ_le_horizontalRadius_sq (y : ℝ) :
    targetQ source y ≤ horizontalRadius source ^ 2 := by
  rw [targetQ]
  split_ifs
  · exact sideSquare_le_horizontalRadius_sq source y
  · exact capSquare_le_horizontalRadius_sq source y

/-- Away from the two shrinking junction collars, the smooth squared width is
exactly the source's piecewise squared width. -/
lemma recovery_q_eq_targetQ_outside_junction
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source)
    (hy : ¬(1 - epsilon < |y| ∧ |y| < 1)) :
    q source epsilon y = targetQ source y := by
  by_cases hlow : |y| ≤ 1 - epsilon
  · have honeMinus : 0 ≤ 1 - epsilon := by
      linarith [hepsilon_le, safeScale_le_sixteenth source]
    have hone : |y| ≤ 1 := hlow.trans (by
      linarith [hepsilon_le, safeScale_le_sixteenth source])
    rw [targetQ, if_pos hone]
    apply q_eq_side source hepsilon hepsilon_le
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
    rw [q_eq_cap source hepsilon hepsilon_le hsq]
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
      · rw [targetQ, if_pos (by norm_num), sideSquare_neg_one source,
          capSquare_neg_one source]
      · rw [targetQ, if_pos (by norm_num), sideSquare_one source,
          capSquare_one source]
    · rw [targetQ, if_neg hone]

lemma continuous_targetQ : Continuous (targetQ source) := by
  unfold targetQ
  apply continuous_if_le continuous_id.abs continuous_const
    (contDiff_sideSquare source).continuous.continuousOn
    (contDiff_capSquare source).continuous.continuousOn
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
  · rw [sideSquare_neg_one source, capSquare_neg_one source]
  · rw [sideSquare_one source, capSquare_one source]


/-- The sourcewise recovery differs from the actual carrier only in the two
shrinking junction rectangles, modulo its null squared-width frontier. -/
theorem characteristicDistance_domain_source_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ safeScale source) :
    characteristicDistance (domain source epsilon) source.assembly.carrier ≤
      (4 : ℝ≥0∞) * ENNReal.ofReal (horizontalRadius source) *
        ENNReal.ofReal epsilon := by
  let X : ℝ := horizontalRadius source
  let L : Set PlanePoint :=
    Icc (-X) X ×ˢ Icc (-1) (-(1 - epsilon))
  let U : Set PlanePoint :=
    Icc (-X) X ×ˢ Icc (1 - epsilon) 1
  let B : Set PlanePoint :=
    {p | p.1 ^ 2 = q source epsilon p.2}
  have hX : 0 < X := horizontalRadius_pos source
  have hsubset :
      domain source epsilon ∆ source.assembly.carrier ⊆ (L ∪ U) ∪ B := by
    intro p hp
    by_cases hband : 1 - epsilon < |p.2| ∧ |p.2| < 1
    · have hx : p.1 ∈ Icc (-X) X := by
        rcases hp with ⟨hpD, _hnotP⟩ | ⟨hpP, _hnotD⟩
        · change p.1 ^ 2 < q source epsilon p.2 at hpD
          have hq :=
            q_le_horizontalRadius_sq source epsilon p.2
          change q source epsilon p.2 ≤ X ^ 2 at hq
          constructor <;> nlinarith
        · have hpTarget : p.1 ^ 2 ≤ targetQ source p.2 :=
            (mem_source_iff_sq_le_targetQ source p).1 hpP
          have ht := targetQ_le_horizontalRadius_sq source p.2
          change targetQ source p.2 ≤ X ^ 2 at ht
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
        recovery_q_eq_targetQ_outside_junction source
          hepsilon hepsilon_le hband
      rcases hp with ⟨hpD, hnotP⟩ | ⟨hpP, hnotD⟩
      · exfalso
        change p.1 ^ 2 < q source epsilon p.2 at hpD
        exact hnotP ((mem_source_iff_sq_le_targetQ source p).2
          (by
            rw [hqeq] at hpD
            exact hpD.le))
      · change p.1 ^ 2 = q source epsilon p.2
        have hle :=
          (mem_source_iff_sq_le_targetQ source p).1 hpP
        have hnlt : ¬p.1 ^ 2 < q source epsilon p.2 := hnotD
        rw [hqeq]
        rw [hqeq] at hnlt
        exact le_antisymm hle (le_of_not_gt hnlt)
  have hB : volume B = 0 := by
    exact FrozenCanonicalCap.volume_squaredWidthBoundary
      (q source epsilon) (contDiff_q source epsilon).continuous
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
  change volume (domain source epsilon ∆ source.assembly.carrier) ≤ _
  calc
    volume (domain source epsilon ∆ source.assembly.carrier) ≤
        volume ((L ∪ U) ∪ B) :=
      measure_mono hsubset
    _ ≤ volume (L ∪ U) + volume B := measure_union_le _ _
    _ ≤ (volume L + volume U) + volume B :=
      add_le_add (measure_union_le L U) le_rfl
    _ = (4 : ℝ≥0∞) * ENNReal.ofReal (horizontalRadius source) *
        ENNReal.ofReal epsilon := by
      rw [hL, hU, hB]
      rw [show X = horizontalRadius source by rfl]
      ring

/-- Positive sourcewise scales tending to zero. -/
def recoveryScale (n : ℕ) : ℝ :=
  safeScale source / ((n : ℝ) + 1)

lemma recoveryScale_pos (n : ℕ) : 0 < recoveryScale source n := by
  unfold recoveryScale
  exact div_pos (safeScale_pos source) (by positivity)

lemma recoveryScale_le (n : ℕ) :
    recoveryScale source n ≤ safeScale source := by
  unfold recoveryScale
  have hn : 0 ≤ (n : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  nlinarith [safeScale_pos source]

lemma tendsto_recoveryScale :
    Tendsto (recoveryScale source) atTop (𝓝 0) := by
  unfold recoveryScale
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- Smooth squared-width approximants for an arbitrary strict four-arc assembly. -/
def recoverySequence : SmoothSequence where
  carrier n := domain source (recoveryScale source n)
  smooth n := isSmoothDomain_domain source
    (recoveryScale_pos source n) (recoveryScale_le source n)

/-- The sourcewise recovery sequence converges globally in characteristic
function distance to the actual five-piece carrier. -/
theorem recoverySequence_converges :
    (recoverySequence source).ConvergesTo source.assembly.carrier := by
  unfold SmoothSequence.ConvergesTo
  let C : ℝ≥0∞ :=
    (4 : ℝ≥0∞) * ENNReal.ofReal (horizontalRadius source)
  have hbound : Tendsto
      (fun n : ℕ => C * ENNReal.ofReal (recoveryScale source n))
      atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun n : ℕ => C * ENNReal.ofReal (recoveryScale source n))
        atTop (𝓝 (C * ENNReal.ofReal 0)) :=
      ENNReal.Tendsto.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => C) atTop (𝓝 C))
        (by simp [C]) (ENNReal.tendsto_ofReal (tendsto_recoveryScale source))
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
        characteristicDistance_domain_source_le source
          (recoveryScale_pos source n) (recoveryScale_le source n))

end CMVRelaxation.FourArcSquaredRecovery
