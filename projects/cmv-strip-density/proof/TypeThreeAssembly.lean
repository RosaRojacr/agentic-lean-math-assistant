/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import FourArcCandidate

/-!
# Branch-complete CMV type-(iii) coordinate carrier

This file implements the regular type-(iii) carrier described in Cañete,
Miranda Jr., and Vittone, Lemma 3.8(iii) and equation (26).  Unlike the
minor-arc-only type-(iv) constructor, the outer arc here crosses the major,
semicircular, and minor branches as the curvature crosses `h = 1 / 2`.

The source-to-model normalization and reduced-boundary comparison remain
separate obligations.  This module supplies the genuine closed coordinate
carrier needed before either theorem can be stated without a scalar-only
surrogate.
-/

open Set
open Real
open MeasureTheory

noncomputable section

/-- Regular source parameters for a type-(iii) profile.  The source radius is
strictly greater than one, so the curvature has the strict domain `0 < h < 1`.
-/
structure TypeThreeAssembly (lam : ℝ) where
  h : ℝ
  density_jump : 1 < lam
  h_pos : 0 < h
  h_lt_one : h < 1

/-- The three geometric branches of the source type-(iii) upper arc. -/
inductive TypeThreeBranch where
  | major
  | semicircular
  | minor
  deriving DecidableEq, Repr

namespace TypeThreeAssembly

variable {lam : ℝ} (a : TypeThreeAssembly lam)

/-- Common radius `R = 1 / h`. -/
def radius : ℝ := 1 / a.h

/-- Source scalar `2h - 1`, equal to `cos b₃`. -/
def shapeParameter : ℝ := 2 * a.h - 1

/-- The source angle `b₃`, represented by its principal arccosine. -/
def innerAngle : ℝ := arccos a.shapeParameter

/-- Snell-adjusted arccosine argument for the exterior angle `a₃`. -/
def outerArgument : ℝ := a.shapeParameter / lam

/-- The exterior half-central-angle `a₃`. -/
def outerAngle : ℝ := arccos a.outerArgument


/-- Half-central-angle of either strip-side arc.  This is the complementary
branch to `innerAngle`, so it remains valid on both sides of `h = 1 / 2`. -/
def sideArcAngle : ℝ := π - a.innerAngle
/-- Half the bottom-segment length. -/
def sideHalfWidth : ℝ :=
  a.radius * (sin a.outerAngle - sin a.innerAngle)

/-- Source circle center for the left strip arc. -/
def leftCenter : PlanePoint := (-a.sideHalfWidth, a.radius - 1)

/-- Source circle center for the right strip arc. -/
def rightCenter : PlanePoint := (a.sideHalfWidth, a.radius - 1)

/-- Source circle center for the exterior upper arc. -/
def upperCenter : PlanePoint :=
  (0, 1 - a.radius * cos a.outerAngle)

/-- Closed central rectangle of `K₃`. -/
def rectangleCarrier : Set PlanePoint :=
  ({p | -a.sideHalfWidth ≤ p.1} ∩ {p | p.1 ≤ a.sideHalfWidth}) ∩
    ({p | (-1 : ℝ) ≤ p.2} ∩ {p | p.2 ≤ 1})

/-- Closed left disk segment of `K₃`. -/
def leftSegmentCarrier : Set PlanePoint :=
  {p | (p.1 - a.leftCenter.1) ^ 2 + (p.2 - a.leftCenter.2) ^ 2 ≤
      a.radius ^ 2} ∩
    ({p | p.1 ≤ a.leftCenter.1} ∩
      ({p | (-1 : ℝ) ≤ p.2} ∩ {p | p.2 ≤ 1}))

/-- Closed right disk segment of `K₃`. -/
def rightSegmentCarrier : Set PlanePoint :=
  {p | (p.1 - a.rightCenter.1) ^ 2 + (p.2 - a.rightCenter.2) ^ 2 ≤
      a.radius ^ 2} ∩
    ({p | a.rightCenter.1 ≤ p.1} ∩
      ({p | (-1 : ℝ) ≤ p.2} ∩ {p | p.2 ≤ 1}))

/-- The part of the type-(iii) carrier inside the closed strip. -/
def coreCarrier : Set PlanePoint :=
  a.rectangleCarrier ∪ a.leftSegmentCarrier ∪ a.rightSegmentCarrier


/-- The exact left circular trace of the type-(iii) strip-side boundary. -/
def leftArcTrace : Set PlanePoint :=
  {p | (p.1 - a.leftCenter.1) ^ 2 + (p.2 - a.leftCenter.2) ^ 2 =
      a.radius ^ 2 ∧
    p.1 ≤ a.leftCenter.1 ∧
    (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1}

/-- The exact right circular trace of the type-(iii) strip-side boundary. -/
def rightArcTrace : Set PlanePoint :=
  {p | (p.1 - a.rightCenter.1) ^ 2 + (p.2 - a.rightCenter.2) ^ 2 =
      a.radius ^ 2 ∧
    a.rightCenter.1 ≤ p.1 ∧
    (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1}

/-- Signed-arclength parameter for the left strip-side half-circle.  The
parameter runs from the upper junction at `-radius * sideArcAngle` to the
bottom point at zero. -/
def leftArcParam (s : ℝ) : PlanePoint :=
  (a.leftCenter.1 + a.radius * sin (s / a.radius),
    a.leftCenter.2 - a.radius * cos (s / a.radius))

/-- Signed-arclength parameter for the right strip-side half-circle.  The
parameter runs from the bottom point at zero to the upper junction at
`radius * sideArcAngle`. -/
def rightArcParam (s : ℝ) : PlanePoint :=
  (a.rightCenter.1 + a.radius * sin (s / a.radius),
    a.rightCenter.2 - a.radius * cos (s / a.radius))

/-- The possibly degenerate bottom segment. -/
def bottomSegmentCarrier : Set PlanePoint :=
  {p | p.2 = -1} ∩ {p | |p.1| ≤ a.sideHalfWidth}

/-- Bottom-segment length, including the zero-length semicircular transition. -/
def bottomChord : ℝ := 2 * a.sideHalfWidth

/-- Finite branch selection; it does not assert membership in a later
area-fold branch. -/
def branch : TypeThreeBranch :=
  if a.h < 1 / 2 then .major
  else if a.h = 1 / 2 then .semicircular
  else .minor

theorem radius_pos : 0 < a.radius := by
  exact one_div_pos.mpr a.h_pos

theorem one_lt_radius : 1 < a.radius := by
  rw [radius]
  apply (lt_div_iff₀ a.h_pos).2
  nlinarith [a.h_lt_one]

theorem shapeParameter_mem : -1 < a.shapeParameter ∧ a.shapeParameter < 1 := by
  constructor <;> simp only [shapeParameter] <;> linarith [a.h_pos, a.h_lt_one]

theorem outerArgument_mem : -1 < a.outerArgument ∧ a.outerArgument < 1 := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) a.density_jump
  have hx := a.shapeParameter_mem
  constructor
  · apply (lt_div_iff₀ hlam_pos).2
    nlinarith [a.density_jump, hx.1]
  · apply (div_lt_iff₀ hlam_pos).2
    nlinarith [a.density_jump, hx.2]

theorem innerAngle_pos : 0 < a.innerAngle :=
  Real.arccos_pos.mpr a.shapeParameter_mem.2

theorem innerAngle_lt_pi : a.innerAngle < π :=
  Real.arccos_lt_pi.mpr a.shapeParameter_mem.1

theorem outerAngle_pos : 0 < a.outerAngle :=
  Real.arccos_pos.mpr a.outerArgument_mem.2

theorem outerAngle_lt_pi : a.outerAngle < π :=
  Real.arccos_lt_pi.mpr a.outerArgument_mem.1

/-- The principal-angle definitions recover the source strip angle exactly. -/
theorem cos_innerAngle : cos a.innerAngle = a.shapeParameter := by
  rw [innerAngle, Real.cos_arccos a.shapeParameter_mem.1.le
    a.shapeParameter_mem.2.le]

/-- The principal-angle definitions recover the Snell-adjusted exterior
argument exactly. -/
theorem cos_outerAngle : cos a.outerAngle = a.outerArgument := by
  rw [outerAngle, Real.cos_arccos a.outerArgument_mem.1.le
    a.outerArgument_mem.2.le]

/-- CMV's type-(iii) incidence equation, derived rather than assumed. -/
theorem snell_incidence :
    lam * cos a.outerAngle = cos a.innerAngle := by
  rw [a.cos_outerAngle, a.cos_innerAngle, outerArgument]
  have hlam_ne : lam ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) a.density_jump)
  field_simp [hlam_ne]

/-- The reciprocal-radius convention is exact on the regular source domain. -/
theorem radius_mul_h : a.radius * a.h = 1 := by
  rw [radius]
  field_simp [ne_of_gt a.h_pos]

private theorem radius_mul_cos_innerAngle :
    a.radius * cos a.innerAngle = 2 - a.radius := by
  rw [a.cos_innerAngle, shapeParameter]
  nlinarith [a.radius_mul_h]

private theorem side_circle_at_top :
    (a.radius * sin a.innerAngle) ^ 2 + (2 - a.radius) ^ 2 =
      a.radius ^ 2 := by
  have htrig := congrArg (fun z : ℝ => a.radius ^ 2 * z)
    (Real.sin_sq_add_cos_sq a.innerAngle)
  nlinarith [a.radius_mul_cos_innerAngle]

theorem outerSin_pos : 0 < sin a.outerAngle :=
  sin_pos_of_pos_of_lt_pi a.outerAngle_pos a.outerAngle_lt_pi

theorem innerSin_pos : 0 < sin a.innerAngle :=
  sin_pos_of_pos_of_lt_pi a.innerAngle_pos a.innerAngle_lt_pi

theorem sideArcAngle_pos : 0 < a.sideArcAngle := by
  rw [sideArcAngle]
  linarith [a.innerAngle_lt_pi]

theorem sideArcAngle_lt_pi : a.sideArcAngle < π := by
  rw [sideArcAngle]
  linarith [a.innerAngle_pos]

theorem sin_sideArcAngle :
    sin a.sideArcAngle = sin a.innerAngle := by
  rw [sideArcAngle, Real.sin_pi_sub]

theorem cos_sideArcAngle :
    cos a.sideArcAngle = -a.shapeParameter := by
  rw [sideArcAngle, Real.cos_pi_sub, a.cos_innerAngle]

/-- A full lower cap with the same radius and angle as the two translated
half-caps forming the strip-side pieces.  Its area and arc length are exactly
the sums of those two congruent halves. -/
def sideCap : OneSidedCircularCap where
  chord := 2 * a.radius * sin a.innerAngle
  theta := a.sideArcAngle
  midpointX := 0
  baseY := 1
  side := .lower
  chord_pos := mul_pos (mul_pos (by norm_num) a.radius_pos) a.innerSin_pos
  theta_pos := a.sideArcAngle_pos
  theta_lt_pi := a.sideArcAngle_lt_pi

/-- The upper one-sided cap.  `OneSidedCircularCap` deliberately permits a
half-central-angle above `π / 2`, so this definition covers the major branch.
-/
def outerCap : OneSidedCircularCap where
  chord := 2 * a.radius * sin a.outerAngle
  theta := a.outerAngle
  midpointX := 0
  baseY := 1
  side := .upper
  chord_pos := mul_pos (mul_pos (by norm_num) a.radius_pos) a.outerSin_pos
  theta_pos := a.outerAngle_pos
  theta_lt_pi := a.outerAngle_lt_pi

/-- Genuine closed coordinate carrier `E₃ = K₃ ∪ upper_cap`. -/
def carrier : Set PlanePoint := a.coreCarrier ∪ a.outerCap.carrier

/-- Ambient weighted-area integral of the coordinate carrier. -/
def WeightedArea : ℝ := _root_.WeightedArea lam a.carrier

/-- Density integral against the complete topological frontier of the
coordinate carrier. -/
def WeightedPerimeter : ℝ :=
  _root_.WeightedPerimeter lam (FrontierMeasure a.carrier)

/-- The horizontal expansion between the two translated side half-caps. -/
def rectangleArea : ℝ := 4 * a.sideHalfWidth

/-- Component area of the modeled type-(iii) profile.  The side-cap term is
the sum of the two congruent translated half-caps; the outer cap has density
`lam`. -/
def modeledWeightedArea : ℝ :=
  a.rectangleArea + a.sideCap.euclideanArea +
    lam * a.outerCap.euclideanArea

/-- Component perimeter of the modeled type-(iii) profile.  The side-cap arc
is the sum of the two translated side arcs; `bottomChord` also covers the
zero-length transition at `h = 1 / 2`. -/
def modeledWeightedPerimeter : ℝ :=
  a.sideCap.arcLength + lam * a.outerCap.arcLength + a.bottomChord

/-- The angle term `lambda * a₃ + π - b₃` in CMV equation (26). -/
def angleTerm : ℝ := lam * a.outerAngle + π - a.innerAngle

/-- The horizontal sine displacement between the upper and side arcs. -/
def sineGap : ℝ := sin a.outerAngle - sin a.innerAngle

/-- Scalar type-(iii) weighted-area formula used by the suffix certificate. -/
def scalarWeightedArea : ℝ :=
  (a.angleTerm + (a.shapeParameter + 2) * a.sineGap) / a.h ^ 2

/-- Scalar type-(iii) weighted-perimeter formula used by the suffix
certificate. -/
def scalarWeightedPerimeter : ℝ :=
  2 * (a.angleTerm + a.sineGap) / a.h

theorem sin_inner_le_sin_outer : sin a.innerAngle ≤ sin a.outerAngle := by
  rw [innerAngle, outerAngle, Real.sin_arccos, Real.sin_arccos]
  apply Real.sqrt_le_sqrt
  have hlam_pos : 0 < lam := lt_trans (by norm_num) a.density_jump
  have habs : |a.outerArgument| ≤ |a.shapeParameter| := by
    rw [outerArgument, abs_div, abs_of_pos hlam_pos]
    exact div_le_self (abs_nonneg _) (le_of_lt a.density_jump)
  exact sub_le_sub_left (sq_le_sq.mpr habs) 1

theorem sin_inner_lt_sin_outer (hh : a.h ≠ 1 / 2) :
    sin a.innerAngle < sin a.outerAngle := by
  rw [innerAngle, outerAngle, Real.sin_arccos, Real.sin_arccos]
  have hlam_pos : 0 < lam := lt_trans (by norm_num) a.density_jump
  have hx : a.shapeParameter ≠ 0 := by
    intro hzero
    apply hh
    simp only [shapeParameter] at hzero
    linarith
  have hx_sq : 0 < a.shapeParameter ^ 2 := sq_pos_of_ne_zero hx
  have hlam_sq : 1 < lam ^ 2 := by nlinarith [a.density_jump]
  have harg_sq : a.outerArgument ^ 2 < a.shapeParameter ^ 2 := by
    rw [outerArgument, div_pow]
    apply (div_lt_iff₀ (sq_pos_of_pos hlam_pos)).2
    nlinarith
  have habs : |a.shapeParameter| < 1 := abs_lt.mpr a.shapeParameter_mem
  have hshape_sq : a.shapeParameter ^ 2 ≤ 1 := by
    have habs_le : |a.shapeParameter| ≤ |(1 : ℝ)| := by
      simpa using le_of_lt habs
    have hsq : a.shapeParameter ^ 2 ≤ (1 : ℝ) ^ 2 :=
      sq_le_sq.mpr habs_le
    simpa using hsq
  have hleft : 0 ≤ 1 - a.shapeParameter ^ 2 := by
    linarith
  exact Real.sqrt_lt_sqrt hleft (by nlinarith)

theorem sideHalfWidth_nonneg : 0 ≤ a.sideHalfWidth := by
  exact mul_nonneg a.radius_pos.le (sub_nonneg.mpr a.sin_inner_le_sin_outer)

theorem sideHalfWidth_pos (hh : a.h ≠ 1 / 2) : 0 < a.sideHalfWidth := by
  exact mul_pos a.radius_pos (sub_pos.mpr (a.sin_inner_lt_sin_outer hh))

theorem sideHalfWidth_eq_zero_iff : a.sideHalfWidth = 0 ↔ a.h = 1 / 2 := by
  constructor
  · intro hzero
    by_contra hh
    linarith [a.sideHalfWidth_pos hh]
  · intro hh
    simp [sideHalfWidth, innerAngle, outerAngle, outerArgument, shapeParameter, hh]

theorem bottomChord_nonneg : 0 ≤ a.bottomChord := by
  exact mul_nonneg (by norm_num) a.sideHalfWidth_nonneg

theorem bottomChord_eq_zero_iff : a.bottomChord = 0 ↔ a.h = 1 / 2 := by
  rw [bottomChord, mul_eq_zero]
  norm_num
  exact a.sideHalfWidth_eq_zero_iff
theorem bottomChord_pos (hh : a.h ≠ 1 / 2) : 0 < a.bottomChord := by
  exact mul_pos (by norm_num) (a.sideHalfWidth_pos hh)


theorem outerAngle_major (hh : a.h < 1 / 2) : π / 2 < a.outerAngle := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) a.density_jump
  have hx : a.outerArgument < 0 := by
    exact div_neg_of_neg_of_pos (by simp [shapeParameter]; linarith) hlam_pos
  apply lt_of_not_ge
  simpa only [outerAngle, Real.arccos_le_pi_div_two] using not_le_of_gt hx

theorem innerAngle_semicircular (hh : a.h = 1 / 2) :
    a.innerAngle = π / 2 := by
  simp [innerAngle, shapeParameter, hh]

theorem outerAngle_semicircular (hh : a.h = 1 / 2) :
    a.outerAngle = π / 2 := by
  simp [outerAngle, outerArgument, shapeParameter, hh]

theorem outerAngle_minor (hh : 1 / 2 < a.h) : a.outerAngle < π / 2 := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) a.density_jump
  rw [outerAngle, Real.arccos_lt_pi_div_two]
  exact div_pos (by simp [shapeParameter]; linarith) hlam_pos

@[simp] theorem branch_eq_major (hh : a.h < 1 / 2) :
    a.branch = .major := by
  rw [branch, if_pos hh]

@[simp] theorem branch_eq_semicircular (hh : a.h = 1 / 2) :
    a.branch = .semicircular := by
  rw [branch, if_neg (by linarith), if_pos hh]

@[simp] theorem branch_eq_minor (hh : 1 / 2 < a.h) :
    a.branch = .minor := by
  rw [branch, if_neg (not_lt_of_ge hh.le), if_neg (ne_of_gt hh)]

/-- Machine-checkable finite branch contract for every regular type-(iii)
profile.  The bottom segment is positive on both open branches and degenerates
exactly at the semicircular transition. -/
theorem branch_complete :
    (a.h < 1 / 2 →
      a.branch = .major ∧ π / 2 < a.outerAngle ∧ 0 < a.bottomChord) ∧
    (a.h = 1 / 2 →
      a.branch = .semicircular ∧
        a.outerAngle = π / 2 ∧ a.bottomChord = 0) ∧
    (1 / 2 < a.h →
      a.branch = .minor ∧ a.outerAngle < π / 2 ∧ 0 < a.bottomChord) := by
  constructor
  · intro hh
    exact ⟨a.branch_eq_major hh, a.outerAngle_major hh,
      a.bottomChord_pos (ne_of_lt hh)⟩
  constructor
  · intro hh
    exact ⟨a.branch_eq_semicircular hh, a.outerAngle_semicircular hh,
      a.bottomChord_eq_zero_iff.mpr hh⟩
  · intro hh
    exact ⟨a.branch_eq_minor hh, a.outerAngle_minor hh,
      a.bottomChord_pos (ne_of_gt hh)⟩


theorem outerCap_radius : a.outerCap.radius = a.radius := by
  change (2 * a.radius * sin a.outerAngle) / (2 * sin a.outerAngle) = a.radius
  field_simp [ne_of_gt a.outerSin_pos]

theorem sideCap_radius : a.sideCap.radius = a.radius := by
  change
    (2 * a.radius * sin a.innerAngle) /
        (2 * sin a.sideArcAngle) = a.radius
  rw [a.sin_sideArcAngle]
  field_simp [ne_of_gt a.innerSin_pos]

theorem sideCap_center :
    a.sideCap.center = (0, a.radius - 1) := by
  change
    (0, 1 + a.sideCap.radius * cos a.sideArcAngle) =
      (0, a.radius - 1)
  rw [a.sideCap_radius, a.cos_sideArcAngle, radius, shapeParameter]
  field_simp [ne_of_gt a.h_pos]
  ring

private theorem radius_mul_cos_sideArcAngle :
    a.radius * cos a.sideArcAngle = a.radius - 2 := by
  rw [a.cos_sideArcAngle, shapeParameter]
  nlinarith [a.radius_mul_h]

/-- The left signed-arclength parameter fills exactly the left strip-side
trace, on every geometric branch (including the semicircular transition). -/
theorem leftArcParam_image_Icc :
    a.leftArcParam ''
        Icc (-a.radius * a.sideArcAngle) 0 = a.leftArcTrace := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hu :
        s / a.radius ∈ Icc (-a.sideArcAngle) 0 := by
      constructor
      · apply (le_div_iff₀ a.radius_pos).2
        nlinarith [hs.1, a.radius_pos]
      · exact div_nonpos_of_nonpos_of_nonneg hs.2 a.radius_pos.le
    have hsin_nonpos : sin (s / a.radius) ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le hu.2
        (by linarith [hu.1, a.sideArcAngle_lt_pi])
    have habs : |s / a.radius| ≤ a.sideArcAngle := by
      rw [abs_le]
      exact ⟨hu.1, hu.2.trans a.sideArcAngle_pos.le⟩
    have hcos :
        cos a.sideArcAngle ≤ cos (s / a.radius) := by
      simpa only [Real.cos_abs] using
        (Real.cos_le_cos_of_nonneg_of_le_pi
          (abs_nonneg (s / a.radius)) a.sideArcAngle_lt_pi.le habs)
    have hcircle := Real.sin_sq_add_cos_sq (s / a.radius)
    change
      ((a.leftCenter.1 + a.radius * sin (s / a.radius)) -
            a.leftCenter.1) ^ 2 +
          ((a.leftCenter.2 - a.radius * cos (s / a.radius)) -
            a.leftCenter.2) ^ 2 = a.radius ^ 2 ∧
        a.leftCenter.1 + a.radius * sin (s / a.radius) ≤
          a.leftCenter.1 ∧
        (-1 : ℝ) ≤
          a.leftCenter.2 - a.radius * cos (s / a.radius) ∧
        a.leftCenter.2 - a.radius * cos (s / a.radius) ≤ 1
    refine ⟨by nlinarith [sq_nonneg a.radius], ?_, ?_, ?_⟩
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos a.radius_pos.le hsin_nonpos]
    · change
        (-1 : ℝ) ≤
          (a.radius - 1) - a.radius * cos (s / a.radius)
      nlinarith [mul_le_mul_of_nonneg_left
        (Real.cos_le_one (s / a.radius)) a.radius_pos.le]
    · change
        (a.radius - 1) - a.radius * cos (s / a.radius) ≤ 1
      nlinarith [mul_le_mul_of_nonneg_left hcos a.radius_pos.le,
        a.radius_mul_cos_sideArcAngle]
  · intro hp
    change
      (p.1 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 = a.radius ^ 2 ∧
        p.1 ≤ a.leftCenter.1 ∧
        (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hp
    let z : ℂ :=
      ⟨a.leftCenter.2 - p.2, p.1 - a.leftCenter.1⟩
    have hnorm_sq : ‖z‖ ^ 2 = a.radius ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [z]
      nlinarith [hp.1]
    have hnorm : ‖z‖ = a.radius := by
      nlinarith [norm_nonneg z, a.radius_pos]
    have hsin :
        a.radius * sin z.arg = p.1 - a.leftCenter.1 := by
      simpa [hnorm, z] using Complex.norm_mul_sin_arg z
    have hcos :
        a.radius * cos z.arg = a.leftCenter.2 - p.2 := by
      simpa [hnorm, z] using Complex.norm_mul_cos_arg z
    have hcos_le : cos a.sideArcAngle ≤ cos z.arg := by
      have hmul :
          a.radius * cos a.sideArcAngle ≤ a.radius * cos z.arg := by
        rw [a.radius_mul_cos_sideArcAngle, hcos]
        change a.radius - 2 ≤ (a.radius - 1) - p.2
        linarith [hp.2.2.2]
      nlinarith [hmul, a.radius_pos]
    have harg : |z.arg| ≤ a.sideArcAngle := by
      by_contra h
      have hlt : a.sideArcAngle < |z.arg| := lt_of_not_ge h
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
        a.sideArcAngle_pos.le (Complex.abs_arg_le_pi z) hlt
      rw [Real.cos_abs] at hc
      linarith
    have harg_nonpos : z.arg ≤ 0 := by
      by_contra h
      have harg_pos : 0 < z.arg := lt_of_not_ge h
      have harg_lt_pi : z.arg < π :=
        lt_of_le_of_lt (le_trans (le_abs_self z.arg) harg)
          a.sideArcAngle_lt_pi
      have hsin_pos := Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt_pi
      nlinarith [a.radius_pos, hp.2.1]
    refine ⟨a.radius * z.arg, ?_, ?_⟩
    · constructor
      · nlinarith [a.radius_pos, (abs_le.mp harg).1]
      · exact mul_nonpos_of_nonneg_of_nonpos a.radius_pos.le harg_nonpos
    · have hangle : a.radius * z.arg / a.radius = z.arg := by
        field_simp [a.radius_pos.ne']
      apply Prod.ext
      · simp only [leftArcParam, hangle]
        linarith
      · simp only [leftArcParam, hangle]
        linarith

/-- The right signed-arclength parameter fills exactly the right strip-side
trace, on every geometric branch (including the semicircular transition). -/
theorem rightArcParam_image_Icc :
    a.rightArcParam ''
        Icc 0 (a.radius * a.sideArcAngle) = a.rightArcTrace := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hu :
        s / a.radius ∈ Icc 0 a.sideArcAngle := by
      constructor
      · exact div_nonneg hs.1 a.radius_pos.le
      · apply (div_le_iff₀ a.radius_pos).2
        nlinarith [hs.2, a.radius_pos]
    have hsin_nonneg : 0 ≤ sin (s / a.radius) :=
      Real.sin_nonneg_of_nonneg_of_le_pi hu.1
        (hu.2.trans a.sideArcAngle_lt_pi.le)
    have habs : |s / a.radius| ≤ a.sideArcAngle := by
      rw [abs_le]
      exact ⟨by linarith [hu.1, a.sideArcAngle_pos], hu.2⟩
    have hcos :
        cos a.sideArcAngle ≤ cos (s / a.radius) := by
      simpa only [Real.cos_abs] using
        (Real.cos_le_cos_of_nonneg_of_le_pi
          (abs_nonneg (s / a.radius)) a.sideArcAngle_lt_pi.le habs)
    have hcircle := Real.sin_sq_add_cos_sq (s / a.radius)
    change
      ((a.rightCenter.1 + a.radius * sin (s / a.radius)) -
            a.rightCenter.1) ^ 2 +
          ((a.rightCenter.2 - a.radius * cos (s / a.radius)) -
            a.rightCenter.2) ^ 2 = a.radius ^ 2 ∧
        a.rightCenter.1 ≤
          a.rightCenter.1 + a.radius * sin (s / a.radius) ∧
        (-1 : ℝ) ≤
          a.rightCenter.2 - a.radius * cos (s / a.radius) ∧
        a.rightCenter.2 - a.radius * cos (s / a.radius) ≤ 1
    refine ⟨by nlinarith [sq_nonneg a.radius], ?_, ?_, ?_⟩
    · nlinarith [mul_nonneg a.radius_pos.le hsin_nonneg]
    · change
        (-1 : ℝ) ≤
          (a.radius - 1) - a.radius * cos (s / a.radius)
      nlinarith [mul_le_mul_of_nonneg_left
        (Real.cos_le_one (s / a.radius)) a.radius_pos.le]
    · change
        (a.radius - 1) - a.radius * cos (s / a.radius) ≤ 1
      nlinarith [mul_le_mul_of_nonneg_left hcos a.radius_pos.le,
        a.radius_mul_cos_sideArcAngle]
  · intro hp
    change
      (p.1 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 = a.radius ^ 2 ∧
        a.rightCenter.1 ≤ p.1 ∧
        (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hp
    let z : ℂ :=
      ⟨a.rightCenter.2 - p.2, p.1 - a.rightCenter.1⟩
    have hnorm_sq : ‖z‖ ^ 2 = a.radius ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [z]
      nlinarith [hp.1]
    have hnorm : ‖z‖ = a.radius := by
      nlinarith [norm_nonneg z, a.radius_pos]
    have hsin :
        a.radius * sin z.arg = p.1 - a.rightCenter.1 := by
      simpa [hnorm, z] using Complex.norm_mul_sin_arg z
    have hcos :
        a.radius * cos z.arg = a.rightCenter.2 - p.2 := by
      simpa [hnorm, z] using Complex.norm_mul_cos_arg z
    have hcos_le : cos a.sideArcAngle ≤ cos z.arg := by
      have hmul :
          a.radius * cos a.sideArcAngle ≤ a.radius * cos z.arg := by
        rw [a.radius_mul_cos_sideArcAngle, hcos]
        change a.radius - 2 ≤ (a.radius - 1) - p.2
        linarith [hp.2.2.2]
      nlinarith [hmul, a.radius_pos]
    have harg : |z.arg| ≤ a.sideArcAngle := by
      by_contra h
      have hlt : a.sideArcAngle < |z.arg| := lt_of_not_ge h
      have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
        a.sideArcAngle_pos.le (Complex.abs_arg_le_pi z) hlt
      rw [Real.cos_abs] at hc
      linarith
    have harg_nonneg : 0 ≤ z.arg := by
      by_contra h
      have harg_neg : z.arg < 0 := lt_of_not_ge h
      have harg_gt_neg_pi : -π < z.arg :=
        lt_of_lt_of_le (neg_lt_neg a.sideArcAngle_lt_pi)
          (abs_le.mp harg).1
      have hsin_neg :=
        Real.sin_neg_of_neg_of_neg_pi_lt harg_neg harg_gt_neg_pi
      nlinarith [a.radius_pos, hp.2.1]
    refine ⟨a.radius * z.arg, ?_, ?_⟩
    · constructor
      · exact mul_nonneg a.radius_pos.le harg_nonneg
      · nlinarith [a.radius_pos, (abs_le.mp harg).2]
    · have hangle : a.radius * z.arg / a.radius = z.arg := by
        field_simp [a.radius_pos.ne']
      apply Prod.ext
      · simp only [rightArcParam, hangle]
        linarith
      · simp only [rightArcParam, hangle]
        linarith

/-- Euclidean isometry that places the standard signed-arclength circle at a
strip-side center, with the orientation used by both side parameters. -/
noncomputable def sideArcComplexIsometryMap
    (center : PlanePoint) (z : ℂ) : EuclideanPlane :=
  WithLp.toLp 2 (center.1 + z.im, center.2 - z.re)

theorem isometry_sideArcComplexIsometryMap (center : PlanePoint) :
    Isometry (sideArcComplexIsometryMap center) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  simp only [sideArcComplexIsometryMap]
  norm_num [Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow, Complex.dist_eq_re_im]
  congr 1
  ring

/-- Euclidean realization of the left signed-arclength parameter. -/
noncomputable def realizedLeftArcParam (s : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (a.leftArcParam s)

/-- Euclidean realization of the right signed-arclength parameter. -/
noncomputable def realizedRightArcParam (s : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (a.rightArcParam s)

lemma realizedLeftArcParam_eq (s : ℝ) :
    a.realizedLeftArcParam s =
      sideArcComplexIsometryMap a.leftCenter
        (unitCircleArc a.radius s) := by
  rw [show a.realizedLeftArcParam s =
    WithLp.toLp 2 (a.leftArcParam s) by rfl]
  simp [leftArcParam, sideArcComplexIsometryMap,
    unitCircleArc_re, unitCircleArc_im]

lemma realizedRightArcParam_eq (s : ℝ) :
    a.realizedRightArcParam s =
      sideArcComplexIsometryMap a.rightCenter
        (unitCircleArc a.radius s) := by
  rw [show a.realizedRightArcParam s =
    WithLp.toLp 2 (a.rightArcParam s) by rfl]
  simp [rightArcParam, sideArcComplexIsometryMap,
    unitCircleArc_re, unitCircleArc_im]

lemma continuous_realizedLeftArcParam :
    Continuous a.realizedLeftArcParam := by
  rw [show a.realizedLeftArcParam =
      sideArcComplexIsometryMap a.leftCenter ∘
        unitCircleArc a.radius by
    funext s
    exact a.realizedLeftArcParam_eq s]
  exact (isometry_sideArcComplexIsometryMap a.leftCenter).continuous.comp
    (continuous_unitCircleArc a.radius)

lemma continuous_realizedRightArcParam :
    Continuous a.realizedRightArcParam := by
  rw [show a.realizedRightArcParam =
      sideArcComplexIsometryMap a.rightCenter ∘
        unitCircleArc a.radius by
    funext s
    exact a.realizedRightArcParam_eq s]
  exact (isometry_sideArcComplexIsometryMap a.rightCenter).continuous.comp
    (continuous_unitCircleArc a.radius)

theorem realizedLeftArcParam_image_Icc :
    a.realizedLeftArcParam ''
        Icc (-a.radius * a.sideArcAngle) 0 =
      planeEuclideanHomeomorph '' a.leftArcTrace := by
  calc
    _ = planeEuclideanHomeomorph ''
        (a.leftArcParam '' Icc (-a.radius * a.sideArcAngle) 0) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [a.leftArcParam_image_Icc]

theorem realizedRightArcParam_image_Icc :
    a.realizedRightArcParam ''
        Icc 0 (a.radius * a.sideArcAngle) =
      planeEuclideanHomeomorph '' a.rightArcTrace := by
  calc
    _ = planeEuclideanHomeomorph ''
        (a.rightArcParam '' Icc 0 (a.radius * a.sideArcAngle)) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [a.rightArcParam_image_Icc]

theorem measurableSet_euclidean_leftArcTrace :
    MeasurableSet (planeEuclideanHomeomorph '' a.leftArcTrace) := by
  rw [← a.realizedLeftArcParam_image_Icc]
  exact (isCompact_Icc.image a.continuous_realizedLeftArcParam).measurableSet

theorem measurableSet_euclidean_rightArcTrace :
    MeasurableSet (planeEuclideanHomeomorph '' a.rightArcTrace) := by
  rw [← a.realizedRightArcParam_image_Icc]
  exact (isCompact_Icc.image a.continuous_realizedRightArcParam).measurableSet

theorem exact_euclidean_leftArcParam_hausdorffMeasure :
    (μH[1] : Measure EuclideanPlane)
        (a.realizedLeftArcParam ''
          Icc (-a.radius * a.sideArcAngle) 0) =
      ENNReal.ofReal (a.radius * a.sideArcAngle) := by
  have hfun : a.realizedLeftArcParam =
      sideArcComplexIsometryMap a.leftCenter ∘
        unitCircleArc a.radius := by
    funext s
    exact a.realizedLeftArcParam_eq s
  have huv : -a.radius * a.sideArcAngle < 0 := by
    nlinarith [a.radius_pos, a.sideArcAngle_pos]
  have hspan :
      0 - (-a.radius * a.sideArcAngle) < 2 * π * a.radius := by
    have hangle : a.sideArcAngle < 2 * π := by
      linarith [a.sideArcAngle_lt_pi, Real.pi_pos]
    have hmul :=
      mul_lt_mul_of_pos_left hangle a.radius_pos
    nlinarith
  calc
    _ = (μH[1] : Measure EuclideanPlane)
        (sideArcComplexIsometryMap a.leftCenter ''
          (unitCircleArc a.radius ''
            Icc (-a.radius * a.sideArcAngle) 0)) := by
      rw [hfun]
      congr 1
      simpa only [Function.comp_apply] using (Set.image_image _ _ _).symm
    _ = (μH[1] : Measure ℂ)
        (unitCircleArc a.radius ''
          Icc (-a.radius * a.sideArcAngle) 0) :=
      (isometry_sideArcComplexIsometryMap a.leftCenter).hausdorffMeasure_image
        (Or.inl (by norm_num)) _
    _ = ENNReal.ofReal (a.radius * a.sideArcAngle) := by
      simpa using
        (hausdorffMeasure_unitCircleArc_image_eq_of_span_lt_two_pi
          a.radius_pos huv hspan)

theorem exact_euclidean_rightArcParam_hausdorffMeasure :
    (μH[1] : Measure EuclideanPlane)
        (a.realizedRightArcParam ''
          Icc 0 (a.radius * a.sideArcAngle)) =
      ENNReal.ofReal (a.radius * a.sideArcAngle) := by
  have hfun : a.realizedRightArcParam =
      sideArcComplexIsometryMap a.rightCenter ∘
        unitCircleArc a.radius := by
    funext s
    exact a.realizedRightArcParam_eq s
  have huv : 0 < a.radius * a.sideArcAngle :=
    mul_pos a.radius_pos a.sideArcAngle_pos
  have hspan :
      a.radius * a.sideArcAngle - 0 < 2 * π * a.radius := by
    have hangle : a.sideArcAngle < 2 * π := by
      linarith [a.sideArcAngle_lt_pi, Real.pi_pos]
    have hmul :=
      mul_lt_mul_of_pos_left hangle a.radius_pos
    nlinarith
  calc
    _ = (μH[1] : Measure EuclideanPlane)
        (sideArcComplexIsometryMap a.rightCenter ''
          (unitCircleArc a.radius ''
            Icc 0 (a.radius * a.sideArcAngle))) := by
      rw [hfun]
      congr 1
      simpa only [Function.comp_apply] using (Set.image_image _ _ _).symm
    _ = (μH[1] : Measure ℂ)
        (unitCircleArc a.radius ''
          Icc 0 (a.radius * a.sideArcAngle)) :=
      (isometry_sideArcComplexIsometryMap a.rightCenter).hausdorffMeasure_image
        (Or.inl (by norm_num)) _
    _ = ENNReal.ofReal (a.radius * a.sideArcAngle) := by
      simpa using
        (hausdorffMeasure_unitCircleArc_image_eq_of_span_lt_two_pi
          a.radius_pos huv hspan)

/-- Exact Euclidean H¹ mass of the left strip-side trace. -/
theorem exact_euclidean_leftArcTrace_hausdorffMeasure :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' a.leftArcTrace) =
      ENNReal.ofReal (a.radius * a.sideArcAngle) := by
  rw [← a.realizedLeftArcParam_image_Icc]
  exact a.exact_euclidean_leftArcParam_hausdorffMeasure

/-- Exact Euclidean H¹ mass of the right strip-side trace. -/
theorem exact_euclidean_rightArcTrace_hausdorffMeasure :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' a.rightArcTrace) =
      ENNReal.ofReal (a.radius * a.sideArcAngle) := by
  rw [← a.realizedRightArcParam_image_Icc]
  exact a.exact_euclidean_rightArcParam_hausdorffMeasure

/-- The two translated strip-side half-caps have the area of `sideCap`. -/
theorem sideCap_euclideanArea :
    a.sideCap.euclideanArea =
      a.radius ^ 2 *
        (a.sideArcAngle -
          sin a.sideArcAngle * cos a.sideArcAngle) := by
  rw [OneSidedCircularCap.euclideanArea, area]
  change
    (2 * a.radius * sin a.innerAngle) ^ 2 *
        ((a.sideArcAngle -
            sin a.sideArcAngle * cos a.sideArcAngle) /
          (4 * sin a.sideArcAngle ^ 2)) =
      a.radius ^ 2 *
        (a.sideArcAngle -
          sin a.sideArcAngle * cos a.sideArcAngle)
  rw [a.sin_sideArcAngle]
  field_simp [ne_of_gt a.innerSin_pos]
  ring

theorem outerCap_euclideanArea :
    a.outerCap.euclideanArea =
      a.radius ^ 2 *
        (a.outerAngle - sin a.outerAngle * cos a.outerAngle) := by
  rw [OneSidedCircularCap.euclideanArea, area]
  change
    (2 * a.radius * sin a.outerAngle) ^ 2 *
        ((a.outerAngle - sin a.outerAngle * cos a.outerAngle) /
          (4 * sin a.outerAngle ^ 2)) =
      a.radius ^ 2 *
        (a.outerAngle - sin a.outerAngle * cos a.outerAngle)
  field_simp [ne_of_gt a.outerSin_pos]
  ring

theorem sideCap_arcLength :
    a.sideCap.arcLength = 2 * a.radius * a.sideArcAngle := by
  rw [OneSidedCircularCap.arcLength, ell]
  change
    (2 * a.radius * sin a.innerAngle) *
        (a.sideArcAngle / sin a.sideArcAngle) =
      2 * a.radius * a.sideArcAngle
  rw [a.sin_sideArcAngle]
  field_simp [ne_of_gt a.innerSin_pos]

theorem outerCap_arcLength :
    a.outerCap.arcLength = 2 * a.radius * a.outerAngle := by
  rw [OneSidedCircularCap.arcLength, ell]
  change
    (2 * a.radius * sin a.outerAngle) *
        (a.outerAngle / sin a.outerAngle) =
      2 * a.radius * a.outerAngle
  field_simp [ne_of_gt a.outerSin_pos]

/-- CMV equation (26), derived from the branch-complete component geometry. -/
theorem modeledWeightedArea_formula :
    a.modeledWeightedArea = a.scalarWeightedArea := by
  rw [modeledWeightedArea, rectangleArea, a.sideCap_euclideanArea,
    a.outerCap_euclideanArea, scalarWeightedArea, angleTerm, sineGap,
    sideHalfWidth, a.sin_sideArcAngle, a.cos_sideArcAngle, a.cos_outerAngle,
    outerArgument, sideArcAngle, radius, shapeParameter]
  field_simp [ne_of_gt a.h_pos,
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) a.density_jump)]
  ring

/-- CMV equation (26), including the degenerate bottom-chord branch. -/
theorem modeledWeightedPerimeter_formula :
    a.modeledWeightedPerimeter = a.scalarWeightedPerimeter := by
  rw [modeledWeightedPerimeter, a.sideCap_arcLength,
    a.outerCap_arcLength, scalarWeightedPerimeter, angleTerm, sineGap,
    bottomChord, sideHalfWidth, sideArcAngle, radius]
  field_simp [ne_of_gt a.h_pos]
  ring

theorem scalarWeightedArea_semicircular (hh : a.h = 1 / 2) :
    a.scalarWeightedArea = 2 * π * (lam + 1) := by
  rw [scalarWeightedArea, angleTerm, sineGap, shapeParameter, hh,
    a.innerAngle_semicircular hh, a.outerAngle_semicircular hh,
    sin_pi_div_two]
  ring

theorem scalarWeightedPerimeter_semicircular (hh : a.h = 1 / 2) :
    a.scalarWeightedPerimeter = 2 * π * (lam + 1) := by
  rw [scalarWeightedPerimeter, angleTerm, sineGap, hh,
    a.innerAngle_semicircular hh, a.outerAngle_semicircular hh,
    sin_pi_div_two]
  ring

/-- At the transition the zero-width rectangle and zero bottom segment vanish,
and the two weighted component values agree. -/
theorem modeled_semicircular (hh : a.h = 1 / 2) :
    a.modeledWeightedArea = 2 * π * (lam + 1) ∧
      a.modeledWeightedPerimeter = 2 * π * (lam + 1) := by
  constructor
  · rw [a.modeledWeightedArea_formula,
      a.scalarWeightedArea_semicircular hh]
  · rw [a.modeledWeightedPerimeter_formula,
      a.scalarWeightedPerimeter_semicircular hh]

theorem outerCap_center : a.outerCap.center = a.upperCenter := by
  change (0, 1 - a.outerCap.radius * cos a.outerAngle) =
    (0, 1 - a.radius * cos a.outerAngle)
  rw [a.outerCap_radius]

theorem outerCap_leftEndpoint :
    a.outerCap.leftEndpoint = (-a.radius * sin a.outerAngle, 1) := by
  simp [OneSidedCircularCap.leftEndpoint, outerCap]
  ring

theorem outerCap_rightEndpoint :
    a.outerCap.rightEndpoint = (a.radius * sin a.outerAngle, 1) := by
  simp [OneSidedCircularCap.rightEndpoint, outerCap]
  ring

/-- The left strip arc and exterior cap use the same upper junction
coordinate. -/
theorem leftUpperJunction :
    (a.leftCenter.1 - a.radius * sin a.innerAngle, 1) =
      a.outerCap.leftEndpoint := by
  rw [a.outerCap_leftEndpoint]
  change
    (-a.sideHalfWidth - a.radius * sin a.innerAngle, 1) =
      (-a.radius * sin a.outerAngle, 1)
  rw [sideHalfWidth]
  ring_nf

/-- The right strip arc and exterior cap use the same upper junction
coordinate. -/
theorem rightUpperJunction :
    (a.rightCenter.1 + a.radius * sin a.innerAngle, 1) =
      a.outerCap.rightEndpoint := by
  rw [a.outerCap_rightEndpoint]
  change
    (a.sideHalfWidth + a.radius * sin a.innerAngle, 1) =
      (a.radius * sin a.outerAngle, 1)
  rw [sideHalfWidth]
  ring_nf

/-- The core and upper cap overlap exactly along the upper cap's chord. -/
theorem core_inter_outerCap_eq_chord :
    a.coreCarrier ∩ a.outerCap.carrier = a.outerCap.chordCarrier := by
  apply Set.Subset.antisymm
  · intro p hp
    have hy_core : p.2 ≤ 1 := by
      rcases hp.1 with (hrect | hleft) | hright
      · exact hrect.2.2
      · exact hleft.2.2.2
      · exact hright.2.2.2
    have hy_cap : (1 : ℝ) ≤ p.2 := by
      simpa [outerCap, OneSidedCircularCap.carrier] using hp.2.2
    exact a.outerCap.mem_chordCarrier_of_mem_carrier_of_eq_base hp.2
      (by simpa [outerCap] using le_antisymm hy_core hy_cap)
  · intro p hp
    have hy : p.2 = (1 : ℝ) := by
      simpa [outerCap, OneSidedCircularCap.chordCarrier] using hp.1
    have hxraw : |p.1| ≤ 2 * a.radius * sin a.outerAngle / 2 := by
      simpa only [outerCap, sub_zero] using hp.2
    have hx : |p.1| ≤ a.radius * sin a.outerAngle := by linarith
    have hcircle :
        (a.radius * sin a.innerAngle) ^ 2 + (2 - a.radius) ^ 2 =
          a.radius ^ 2 := by
      have htrig := congrArg (fun z : ℝ => a.radius ^ 2 * z)
        (Real.sin_sq_add_cos_sq a.innerAngle)
      have hcos : a.radius * cos a.innerAngle = 2 - a.radius := by
        rw [a.cos_innerAngle, shapeParameter]
        nlinarith [a.radius_mul_h]
      nlinarith
    refine ⟨?_, a.outerCap.chordCarrier_subset_carrier hp⟩
    rcases le_total p.1 (-a.sideHalfWidth) with hleft | hnleft
    · left
      right
      refine ⟨?_, hleft, by simp [hy], by simp [hy]⟩
      have hxmin : -(a.radius * sin a.outerAngle) ≤ p.1 :=
        (abs_le.mp hx).1
      have hdx :
          -(a.radius * sin a.innerAngle) ≤ p.1 + a.sideHalfWidth := by
        rw [sideHalfWidth]
        linarith
      have hdx_nonpos : p.1 + a.sideHalfWidth ≤ 0 := by linarith
      change (p.1 - a.leftCenter.1) ^ 2 +
          (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2
      simp only [leftCenter, hy]
      nlinarith [a.radius_pos, a.innerSin_pos]
    · rcases le_total a.sideHalfWidth p.1 with hright | hnright
      · right
        refine ⟨?_, hright, by simp [hy], by simp [hy]⟩
        have hxmax : p.1 ≤ a.radius * sin a.outerAngle :=
          (abs_le.mp hx).2
        have hdx :
            p.1 - a.sideHalfWidth ≤ a.radius * sin a.innerAngle := by
          rw [sideHalfWidth]
          linarith
        have hdx_nonneg : 0 ≤ p.1 - a.sideHalfWidth := by linarith
        change (p.1 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2
        simp only [rightCenter, hy]
        nlinarith [a.radius_pos, a.innerSin_pos]
      · left
        left
        exact ⟨⟨hnleft, hnright⟩, by simp [hy]⟩

private theorem bottomSegmentCarrier_subset_carrier :
    a.bottomSegmentCarrier ⊆ a.carrier := by
  intro p hp
  have hy : p.2 = (-1 : ℝ) := hp.1
  have hx : -a.sideHalfWidth ≤ p.1 ∧ p.1 ≤ a.sideHalfWidth :=
    abs_le.mp hp.2
  exact Or.inl (Or.inl (Or.inl ⟨hx, by simp [hy]⟩))

private theorem below_bottomSegmentCarrier_not_mem
    {p : PlanePoint} (hp : p ∈ a.bottomSegmentCarrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (p.1, p.2 - epsilon) ∉ a.carrier := by
  intro hbelow
  have hpY : p.2 = (-1 : ℝ) := hp.1
  rcases hbelow with hcore | hcap
  · have hy : (-1 : ℝ) ≤ p.2 - epsilon := by
      rcases hcore with (hrect | hleft) | hright
      · exact hrect.2.1
      · exact hleft.2.2.1
      · exact hright.2.2.1
    exact (not_lt_of_ge hy) (by linarith)
  · have hy : (1 : ℝ) ≤ p.2 - epsilon := by
      simpa [outerCap, OneSidedCircularCap.carrier] using hcap.2
    exact (not_lt_of_ge hy) (by linarith)

/-- The possibly degenerate bottom segment is an exposed part of the complete
frontier of the type-(iii) carrier. -/
theorem bottomSegmentCarrier_subset_frontier :
    a.bottomSegmentCarrier ⊆ frontier a.carrier := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior
    (a.bottomSegmentCarrier_subset_carrier hp)]
  intro hinterior
  have hnhds : interior a.carrier ∈ nhds p :=
    isOpen_interior.mem_nhds hinterior
  rcases Metric.mem_nhds_iff.mp hnhds with
    ⟨epsilon, hepsilon, hball⟩
  have hhalf : 0 < epsilon / 2 := div_pos hepsilon (by norm_num)
  have hnear :
      (p.1, p.2 - epsilon / 2) ∈ Metric.ball p epsilon := by
    rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq,
      show p.2 - epsilon / 2 - p.2 = -(epsilon / 2) by ring,
      abs_neg, abs_of_pos hhalf, max_eq_right hhalf.le]
    linarith
  have hmember :
      (p.1, p.2 - epsilon / 2) ∈ a.carrier :=
    interior_subset (hball hnear)
  exact a.below_bottomSegmentCarrier_not_mem hp hhalf hmember

private def bottomHorizontalSegment (hh : a.h ≠ 1 / 2) :
    HorizontalSegment where
  chord := a.bottomChord
  midpointX := 0
  baseY := -1
  chord_pos := a.bottomChord_pos hh

private theorem bottomHorizontalSegment_carrier
    (hh : a.h ≠ 1 / 2) :
    (a.bottomHorizontalSegment hh).carrier = a.bottomSegmentCarrier := by
  ext p
  simp only [HorizontalSegment.carrier, bottomHorizontalSegment,
    bottomSegmentCarrier, mem_inter_iff, mem_ofPred_eq, sub_zero, bottomChord]
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨hy, by linarith⟩
  · rintro ⟨hy, hx⟩
    exact ⟨hy, by linarith⟩

/-- Exact Euclidean one-dimensional Hausdorff mass of the possibly degenerate
bottom segment. -/
theorem exact_euclidean_bottomSegmentCarrier_hausdorffMeasure :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' a.bottomSegmentCarrier) =
      ENNReal.ofReal a.bottomChord := by
  rcases eq_or_ne a.h (1 / 2) with hh | hh
  · have hw : a.sideHalfWidth = 0 :=
      a.sideHalfWidth_eq_zero_iff.mpr hh
    have hc : a.bottomChord = 0 :=
      a.bottomChord_eq_zero_iff.mpr hh
    have hcarrier : a.bottomSegmentCarrier = {(0, -1)} := by
      ext p
      simp only [bottomSegmentCarrier, mem_inter_iff, mem_ofPred_eq,
        hw, abs_nonpos_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hy, hx⟩
        exact Prod.ext hx hy
      · intro hp
        rw [hp]
        exact ⟨rfl, rfl⟩
    rw [hcarrier, image_singleton, hc, ENNReal.ofReal_zero]
    let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
      Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
    exact measure_singleton _
  · rw [← a.bottomHorizontalSegment_carrier hh,
      exact_euclidean_segmentCarrier_hausdorffMeasure]
    rfl

/-- The four primitive boundary joins.  The two bottom points coincide at the
semicircular transition. -/
def boundaryJoinSet : Set PlanePoint :=
  {(-a.radius * sin a.outerAngle, 1),
    (a.radius * sin a.outerAngle, 1),
    (-a.sideHalfWidth, -1),
    (a.sideHalfWidth, -1)}

theorem boundaryJoinSet_finite : a.boundaryJoinSet.Finite := by
  simp [boundaryJoinSet]

/-- Every pairwise overlap of the four primitive frontier traces is a boundary
join.  In particular, when `h = 1 / 2`, the two side arcs meet only at the
shared bottom point. -/
theorem pairwiseOverlap_subset_boundaryJoinSet :
    pairwiseOverlap a.leftArcTrace a.rightArcTrace
      (OneSidedCircularCap.arcTrace a.outerCap)
      a.bottomSegmentCarrier ⊆ a.boundaryJoinSet := by
  intro p hp
  simp only [pairwiseOverlap, mem_union, mem_inter_iff] at hp
  rcases hp with hLR | hLU | hLB | hRU | hRB | hUB
  · by_cases hw : a.sideHalfWidth = 0
    · have hx : p.1 = 0 := by
        have hl := hLR.1.2.1
        have hr := hLR.2.2.1
        simp only [leftCenter, rightCenter, hw, neg_zero] at hl hr
        linarith
      have hcircle := hLR.1.1
      rw [hx] at hcircle
      simp only [leftCenter, hw, neg_zero, sub_zero] at hcircle
      have hfactor :
          (p.2 + 1) * (p.2 - (2 * a.radius - 1)) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfactor with hy | hy
      · have hy' : p.2 = -1 := by linarith
        have hpEq : p = (0, -1) := Prod.ext hx hy'
        simp [boundaryJoinSet, hpEq, hw]
      · have hy' : p.2 = 2 * a.radius - 1 := by linarith
        have hyUpper := hLR.1.2.2.2
        exfalso
        nlinarith [a.one_lt_radius]
    · have hwpos : 0 < a.sideHalfWidth :=
        lt_of_le_of_ne a.sideHalfWidth_nonneg (Ne.symm hw)
      have hl := hLR.1.2.1
      have hr := hLR.2.2.1
      simp only [leftCenter, rightCenter] at hl hr
      exfalso
      linarith
  · have hyCore : p.2 ≤ 1 := hLU.1.2.2.2
    have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [outerCap] using hLU.2.2
    have hy : p.2 = 1 := le_antisymm hyCore hyCap
    have hdx : p.1 - a.leftCenter.1 ≤ 0 := by
      linarith [hLU.1.2.1]
    have hsq :
        (p.1 - a.leftCenter.1) ^ 2 =
          (a.radius * sin a.innerAngle) ^ 2 := by
      have hpCircle := hLU.1.1
      rw [hy] at hpCircle
      simp only [leftCenter] at hpCircle
      rw [leftCenter]
      nlinarith [a.side_circle_at_top]
    have habs := (sq_eq_sq_iff_abs_eq_abs
      (p.1 - a.leftCenter.1)
      (a.radius * sin a.innerAngle)).mp hsq
    rw [abs_of_nonpos hdx,
      abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] at habs
    have hdxEq :
        p.1 - a.leftCenter.1 =
          -(a.radius * sin a.innerAngle) := by linarith
    have hx : p.1 = -(a.radius * sin a.outerAngle) := by
      simp only [leftCenter] at hdxEq
      rw [sideHalfWidth] at hdxEq
      linarith
    have hpEq : p = (-a.radius * sin a.outerAngle, 1) := by
      apply Prod.ext
      · simpa using hx
      · simpa using hy
    simp [boundaryJoinSet, hpEq]
  · have hy : p.2 = -1 := hLB.2.1
    have hbound : |p.1| ≤ a.sideHalfWidth := hLB.2.2
    have hxLower := (abs_le.mp hbound).1
    have hxUpper := hLB.1.2.1
    simp only [leftCenter] at hxUpper
    have hx : p.1 = -a.sideHalfWidth := by linarith
    have hpEq : p = (-a.sideHalfWidth, -1) := Prod.ext hx hy
    simp [boundaryJoinSet, hpEq]
  · have hyCore : p.2 ≤ 1 := hRU.1.2.2.2
    have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [outerCap] using hRU.2.2
    have hy : p.2 = 1 := le_antisymm hyCore hyCap
    have hdx : 0 ≤ p.1 - a.rightCenter.1 := by
      linarith [hRU.1.2.1]
    have hsq :
        (p.1 - a.rightCenter.1) ^ 2 =
          (a.radius * sin a.innerAngle) ^ 2 := by
      have hpCircle := hRU.1.1
      rw [hy] at hpCircle
      simp only [rightCenter] at hpCircle
      rw [rightCenter]
      nlinarith [a.side_circle_at_top]
    have habs := (sq_eq_sq_iff_abs_eq_abs
      (p.1 - a.rightCenter.1)
      (a.radius * sin a.innerAngle)).mp hsq
    rw [abs_of_nonneg hdx,
      abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] at habs
    have hdxEq :
        p.1 - a.rightCenter.1 =
          a.radius * sin a.innerAngle := habs
    have hx : p.1 = a.radius * sin a.outerAngle := by
      simp only [rightCenter] at hdxEq
      rw [sideHalfWidth] at hdxEq
      linarith
    have hpEq : p = (a.radius * sin a.outerAngle, 1) := Prod.ext hx hy
    simp [boundaryJoinSet, hpEq]
  · have hy : p.2 = -1 := hRB.2.1
    have hbound : |p.1| ≤ a.sideHalfWidth := hRB.2.2
    have hxUpper := (abs_le.mp hbound).2
    have hxLower := hRB.1.2.1
    simp only [rightCenter] at hxLower
    have hx : p.1 = a.sideHalfWidth := by linarith
    have hpEq : p = (a.sideHalfWidth, -1) := Prod.ext hx hy
    simp [boundaryJoinSet, hpEq]
  · have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [outerCap] using hUB.1.2
    have hyBottom : p.2 = -1 := hUB.2.1
    exfalso
    linarith

/-- Pairwise primitive overlaps carry no Euclidean `H¹` mass. -/
theorem pairwiseOverlap_h1_null :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' pairwiseOverlap
        a.leftArcTrace a.rightArcTrace
        (OneSidedCircularCap.arcTrace a.outerCap)
        a.bottomSegmentCarrier) = 0 := by
  let _ := Measure.nullSingletonClass_hausdorff EuclideanPlane
    (by norm_num : (0 : ℝ) < 1)
  have hjoin :
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' a.boundaryJoinSet) = 0 :=
    (a.boundaryJoinSet_finite.image planeEuclideanHomeomorph).measure_zero
      μH[1]
  exact measure_mono_null
    (image_mono a.pairwiseOverlap_subset_boundaryJoinSet) hjoin

private theorem isClosed_disk (center : PlanePoint) (r : ℝ) :
    IsClosed {p : PlanePoint |
      (p.1 - center.1) ^ 2 + (p.2 - center.2) ^ 2 ≤ r ^ 2} := by
  exact isClosed_le
    (((continuous_fst.sub continuous_const).pow 2).add
      ((continuous_snd.sub continuous_const).pow 2))
    continuous_const

theorem isClosed_rectangleCarrier : IsClosed a.rectangleCarrier := by
  unfold rectangleCarrier
  exact ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst continuous_const)).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const))

theorem isClosed_leftSegmentCarrier : IsClosed a.leftSegmentCarrier := by
  unfold leftSegmentCarrier
  exact (isClosed_disk a.leftCenter a.radius).inter
    ((isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const)))

theorem isClosed_rightSegmentCarrier : IsClosed a.rightSegmentCarrier := by
  unfold rightSegmentCarrier
  exact (isClosed_disk a.rightCenter a.radius).inter
    ((isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le continuous_snd continuous_const)))

theorem isClosed_coreCarrier : IsClosed a.coreCarrier := by
  exact (a.isClosed_rectangleCarrier.union a.isClosed_leftSegmentCarrier).union
    a.isClosed_rightSegmentCarrier

theorem isClosed_carrier : IsClosed a.carrier := by
  exact a.isClosed_coreCarrier.union a.outerCap.isClosed_carrier

theorem measurableSet_carrier : MeasurableSet a.carrier :=
  a.isClosed_carrier.measurableSet

/-! ## Carrier-derived weighted area -/

/-- The left half of the standard side cap.  Translating it horizontally gives
the actual left strip-side segment. -/
private def sideCapLeftHalf : Set PlanePoint :=
  a.sideCap.carrier ∩ {p | p.1 ≤ 0}

/-- The right half of the standard side cap.  Translating it horizontally gives
the actual right strip-side segment. -/
private def sideCapRightHalf : Set PlanePoint :=
  a.sideCap.carrier ∩ {p | 0 ≤ p.1}

private theorem measurableSet_sideCapLeftHalf :
    MeasurableSet a.sideCapLeftHalf := by
  exact a.sideCap.measurableSet_carrier.inter
    (isClosed_le continuous_fst continuous_const).measurableSet

private theorem measurableSet_sideCapRightHalf :
    MeasurableSet a.sideCapRightHalf := by
  exact a.sideCap.measurableSet_carrier.inter
    (isClosed_le continuous_const continuous_fst).measurableSet

private theorem leftSegment_preimage_sideCapLeftHalf :
    (fun p : PlanePoint => (a.sideHalfWidth, 0) + p) ⁻¹'
        a.sideCapLeftHalf =
      a.leftSegmentCarrier := by
  ext p
  simp only [sideCapLeftHalf, mem_preimage, mem_inter_iff, mem_ofPred_eq,
    OneSidedCircularCap.carrier, OneSidedCircularCap.radiusSquaredAt,
    Prod.fst_add, Prod.snd_add, zero_add]
  rw [a.sideCap_center, a.sideCap_radius]
  simp only [sideCap, leftSegmentCarrier, leftCenter, sub_zero,
    sub_neg_eq_add, mem_inter_iff, mem_ofPred_eq]
  change
    ((((a.sideHalfWidth + p.1) ^ 2 +
          (p.2 - (a.radius - 1)) ^ 2 ≤ a.radius ^ 2) ∧
        p.2 ≤ 1) ∧ a.sideHalfWidth + p.1 ≤ 0) ↔
      ((p.1 + a.sideHalfWidth) ^ 2 +
          (p.2 - (a.radius - 1)) ^ 2 ≤ a.radius ^ 2) ∧
        p.1 ≤ -a.sideHalfWidth ∧ (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1
  constructor
  · rintro ⟨⟨hdisk, hyhi⟩, hx⟩
    refine ⟨?_, (by linarith), ?_, hyhi⟩
    · convert hdisk using 1
      ring
    · nlinarith [sq_nonneg (a.sideHalfWidth + p.1), a.radius_pos]
  · rintro ⟨hdisk, hx, _hylo, hyhi⟩
    refine ⟨⟨?_, hyhi⟩, by linarith⟩
    convert hdisk using 1
    ring

private theorem rightSegment_preimage_sideCapRightHalf :
    (fun p : PlanePoint => (-a.sideHalfWidth, 0) + p) ⁻¹'
        a.sideCapRightHalf =
      a.rightSegmentCarrier := by
  ext p
  simp only [sideCapRightHalf, mem_preimage, mem_inter_iff, mem_ofPred_eq,
    OneSidedCircularCap.carrier, OneSidedCircularCap.radiusSquaredAt,
    Prod.fst_add, Prod.snd_add, zero_add]
  rw [a.sideCap_center, a.sideCap_radius]
  simp only [sideCap, rightSegmentCarrier, rightCenter, sub_zero,
    mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hdisk, hyhi⟩, hx⟩
    refine ⟨?_, (by linarith), ?_, hyhi⟩
    · convert hdisk using 1
      ring
    · nlinarith [sq_nonneg (-a.sideHalfWidth + p.1), a.radius_pos]
  · rintro ⟨hdisk, hx, _hylo, hyhi⟩
    refine ⟨⟨?_, hyhi⟩, by linarith⟩
    convert hdisk using 1
    ring

private theorem volume_leftSegmentCarrier :
    volume a.leftSegmentCarrier = volume a.sideCapLeftHalf := by
  rw [← a.leftSegment_preimage_sideCapLeftHalf]
  exact
    (measurePreserving_add_left volume
      (a.sideHalfWidth, 0)).measure_preimage
        a.measurableSet_sideCapLeftHalf.nullMeasurableSet

private theorem volume_rightSegmentCarrier :
    volume a.rightSegmentCarrier = volume a.sideCapRightHalf := by
  rw [← a.rightSegment_preimage_sideCapRightHalf]
  exact
    (measurePreserving_add_left volume
      (-a.sideHalfWidth, 0)).measure_preimage
        a.measurableSet_sideCapRightHalf.nullMeasurableSet

private theorem volume_sideCap_partition :
    volume a.sideCap.carrier =
      volume a.sideCapLeftHalf + volume a.sideCapRightHalf := by
  have hunion :
      a.sideCapLeftHalf ∪ a.sideCapRightHalf = a.sideCap.carrier := by
    ext p
    constructor
    · rintro (hp | hp) <;> exact hp.1
    · intro hp
      rcases le_total p.1 0 with hx | hx
      · exact Or.inl ⟨hp, hx⟩
      · exact Or.inr ⟨hp, hx⟩
  have hdisjoint :
      AEDisjoint volume a.sideCapLeftHalf a.sideCapRightHalf := by
    refine measure_mono_null ?_ (volume_verticalLine 0)
    rintro p ⟨hpLeft, hpRight⟩
    exact le_antisymm hpLeft.2 hpRight.2
  rw [← hunion]
  exact measure_union₀
    a.measurableSet_sideCapRightHalf.nullMeasurableSet hdisjoint

private theorem volume_rectangleCarrier :
    volume a.rectangleCarrier = ENNReal.ofReal a.rectangleArea := by
  have hset :
      a.rectangleCarrier =
        Icc (-a.sideHalfWidth) a.sideHalfWidth ×ˢ Icc (-1 : ℝ) 1 := by
    ext p
    simp only [rectangleCarrier, mem_inter_iff, mem_ofPred_eq,
      mem_prod, mem_Icc]
  rw [hset, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc, rectangleArea]
  have hw : 0 ≤ 2 * a.sideHalfWidth :=
    mul_nonneg (by norm_num) a.sideHalfWidth_nonneg
  rw [show a.sideHalfWidth - -a.sideHalfWidth =
      2 * a.sideHalfWidth by ring,
    show (1 : ℝ) - -1 = 2 by ring]
  calc
    ENNReal.ofReal (2 * a.sideHalfWidth) * ENNReal.ofReal 2 =
        ENNReal.ofReal ((2 * a.sideHalfWidth) * 2) := by
          exact (ENNReal.ofReal_mul hw).symm
    _ = ENNReal.ofReal (4 * a.sideHalfWidth) := by
      congr 1
      ring

/-- Every point of the coordinate core lies in the closed unit strip. -/
theorem coreCarrier_y_bounds {p : PlanePoint}
    (hp : p ∈ a.coreCarrier) : |p.2| ≤ 1 := by
  rcases hp with (hrect | hleft) | hright
  · exact abs_le.mpr ⟨hrect.2.1, hrect.2.2⟩
  · exact abs_le.mpr hleft.2.2
  · exact abs_le.mpr hright.2.2

/-- Exact planar volume of the strip core.  The two translated half-segments
partition the standard side cap, including its major and semicircular
branches. -/
theorem volume_coreCarrier :
    volume a.coreCarrier =
      ENNReal.ofReal (a.rectangleArea + a.sideCap.euclideanArea) := by
  have hrectLeft :
      AEDisjoint volume a.rectangleCarrier a.leftSegmentCarrier := by
    refine measure_mono_null ?_ (volume_verticalLine (-a.sideHalfWidth))
    rintro p ⟨hrect, hleft⟩
    exact le_antisymm hleft.2.1 hrect.1.1
  have hfirstRight :
      AEDisjoint volume
        (a.rectangleCarrier ∪ a.leftSegmentCarrier)
        a.rightSegmentCarrier := by
    refine measure_mono_null ?_ (volume_verticalLine a.sideHalfWidth)
    rintro p ⟨hfirst, hright⟩
    rcases hfirst with hrect | hleft
    · exact le_antisymm hrect.1.2 hright.2.1
    · have hxl : p.1 ≤ -a.sideHalfWidth := hleft.2.1
      have hxr : a.sideHalfWidth ≤ p.1 := hright.2.1
      exact le_antisymm (by linarith [a.sideHalfWidth_nonneg]) hxr
  have hrectangle : 0 ≤ a.rectangleArea := by
    exact mul_nonneg (by norm_num) a.sideHalfWidth_nonneg
  calc
    volume a.coreCarrier =
        volume a.rectangleCarrier + volume a.leftSegmentCarrier +
          volume a.rightSegmentCarrier := by
      rw [coreCarrier,
        measure_union₀
          a.isClosed_rightSegmentCarrier.measurableSet.nullMeasurableSet
          hfirstRight,
        measure_union₀
          a.isClosed_leftSegmentCarrier.measurableSet.nullMeasurableSet
          hrectLeft]
    _ = ENNReal.ofReal a.rectangleArea +
        (volume a.sideCapLeftHalf + volume a.sideCapRightHalf) := by
      rw [a.volume_rectangleCarrier, a.volume_leftSegmentCarrier,
        a.volume_rightSegmentCarrier, add_assoc]
    _ = ENNReal.ofReal a.rectangleArea + volume a.sideCap.carrier := by
      rw [a.volume_sideCap_partition]
    _ = ENNReal.ofReal a.rectangleArea +
        ENNReal.ofReal a.sideCap.euclideanArea := by
      rw [a.sideCap.volume_carrier]
    _ = ENNReal.ofReal
        (a.rectangleArea + a.sideCap.euclideanArea) := by
      exact
        (ENNReal.ofReal_add hrectangle
          a.sideCap.euclideanArea_pos.le).symm

/-- The actual density integral over the strip core is its Euclidean component
area. -/
theorem core_weightedArea_formula :
    _root_.WeightedArea lam a.coreCarrier =
      a.rectangleArea + a.sideCap.euclideanArea := by
  rw [_root_.WeightedArea]
  calc
    (∫ p in a.coreCarrier, StripDensity lam p) =
        ∫ _p in a.coreCarrier, (1 : ℝ) := by
      apply setIntegral_congr_fun a.isClosed_coreCarrier.measurableSet
      intro p hp
      rw [StripDensity, if_pos (a.coreCarrier_y_bounds hp)]
    _ = a.rectangleArea + a.sideCap.euclideanArea := by
      have hnonneg :
          0 ≤ a.rectangleArea + a.sideCap.euclideanArea :=
        add_nonneg
          (mul_nonneg (by norm_num) a.sideHalfWidth_nonneg)
          a.sideCap.euclideanArea_pos.le
      rw [integral_const, measureReal_restrict_apply_univ,
        Measure.real, a.volume_coreCarrier,
        ENNReal.toReal_ofReal hnonneg]
      simp

private theorem carrier_core_outer_aedisjoint :
    AEDisjoint volume a.coreCarrier a.outerCap.carrier := by
  refine measure_mono_null ?_ (volume_horizontalLine 1)
  rintro p ⟨hcore, hcap⟩
  have hyCore := (abs_le.mp (a.coreCarrier_y_bounds hcore)).2
  have hyCap : (1 : ℝ) ≤ p.2 := by
    simpa [outerCap, OneSidedCircularCap.carrier] using hcap.2
  exact le_antisymm hyCore hyCap

/-- The ambient weighted-area integral of the coordinate carrier equals the
modeled rectangle, side-cap, and exterior-cap component sum. -/
theorem weightedArea_eq_modeledWeightedArea :
    a.WeightedArea = a.modeledWeightedArea := by
  have hcore : IntegrableOn (StripDensity lam) a.coreCarrier := by
    apply stripDensity_integrableOn_of_volume_ne_top
    rw [a.volume_coreCarrier]
    exact ENNReal.ofReal_ne_top
  have hcap := cap_integrableOn lam a.outerCap
  unfold TypeThreeAssembly.WeightedArea _root_.WeightedArea
  rw [carrier,
    setIntegral_union₀ a.carrier_core_outer_aedisjoint
      a.outerCap.measurableSet_carrier.nullMeasurableSet hcore hcap]
  rw [show (∫ p in a.coreCarrier, StripDensity lam p) =
      a.rectangleArea + a.sideCap.euclideanArea by
        simpa [_root_.WeightedArea] using a.core_weightedArea_formula,
    show (∫ p in a.outerCap.carrier, StripDensity lam p) =
      lam * a.outerCap.euclideanArea by
        simpa [_root_.WeightedArea] using
          cap_upper_weightedArea lam a.outerCap rfl rfl,
    modeledWeightedArea]

/-- CMV equation (26) is the exact canonical weighted area of the coordinate
carrier, not only a sum assigned to its modeled components. -/
theorem weightedArea_formula :
    a.WeightedArea = a.scalarWeightedArea := by
  rw [a.weightedArea_eq_modeledWeightedArea,
    a.modeledWeightedArea_formula]

theorem isClosed_bottomSegmentCarrier : IsClosed a.bottomSegmentCarrier := by
  unfold bottomSegmentCarrier
  exact (isClosed_eq continuous_snd continuous_const).inter
    (isClosed_le continuous_fst.abs continuous_const)

/-- The exact complete trace of the type-(iii) boundary. -/
def boundaryTrace : Set PlanePoint :=
  a.leftArcTrace ∪
    (a.rightArcTrace ∪
      (OneSidedCircularCap.arcTrace a.outerCap ∪ a.bottomSegmentCarrier))

private theorem strictRectangle_subset_interior :
    {p : PlanePoint | -a.sideHalfWidth < p.1 ∧
      p.1 < a.sideHalfWidth ∧ (-1 : ℝ) < p.2 ∧ p.2 < 1} ⊆
      interior a.coreCarrier := by
  apply interior_maximal
  · intro p hp
    exact Or.inl (Or.inl
      ⟨⟨hp.1.le, hp.2.1.le⟩, ⟨hp.2.2.1.le, hp.2.2.2.le⟩⟩)
  · change IsOpen
      ({p : PlanePoint | -a.sideHalfWidth < p.1} ∩
        ({p : PlanePoint | p.1 < a.sideHalfWidth} ∩
          ({p : PlanePoint | (-1 : ℝ) < p.2} ∩
            {p : PlanePoint | p.2 < 1})))
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const)))

private theorem strictLeftSegment_subset_interior :
    {p : PlanePoint |
      (p.1 - a.leftCenter.1) ^ 2 + (p.2 - a.leftCenter.2) ^ 2 <
        a.radius ^ 2 ∧
      p.1 < a.leftCenter.1 ∧ (-1 : ℝ) < p.2 ∧ p.2 < 1} ⊆
      interior a.coreCarrier := by
  apply interior_maximal
  · intro p hp
    exact Or.inl (Or.inr
      ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩)
  · change IsOpen
      ({p : PlanePoint |
          (p.1 - a.leftCenter.1) ^ 2 +
              (p.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2} ∩
        ({p : PlanePoint | p.1 < a.leftCenter.1} ∩
          ({p : PlanePoint | (-1 : ℝ) < p.2} ∩
            {p : PlanePoint | p.2 < 1})))
    exact (isOpen_lt
      (((continuous_fst.sub continuous_const).pow 2).add
        ((continuous_snd.sub continuous_const).pow 2))
      continuous_const).inter
        ((isOpen_lt continuous_fst continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_const)))

private theorem strictRightSegment_subset_interior :
    {p : PlanePoint |
      (p.1 - a.rightCenter.1) ^ 2 + (p.2 - a.rightCenter.2) ^ 2 <
        a.radius ^ 2 ∧
      a.rightCenter.1 < p.1 ∧ (-1 : ℝ) < p.2 ∧ p.2 < 1} ⊆
      interior a.coreCarrier := by
  apply interior_maximal
  · intro p hp
    exact Or.inr
      ⟨hp.1.le, hp.2.1.le, hp.2.2.1.le, hp.2.2.2.le⟩
  · change IsOpen
      ({p : PlanePoint |
          (p.1 - a.rightCenter.1) ^ 2 +
              (p.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2} ∩
        ({p : PlanePoint | a.rightCenter.1 < p.1} ∩
          ({p : PlanePoint | (-1 : ℝ) < p.2} ∩
            {p : PlanePoint | p.2 < 1})))
    exact (isOpen_lt
      (((continuous_fst.sub continuous_const).pow 2).add
        ((continuous_snd.sub continuous_const).pow 2))
      continuous_const).inter
        ((isOpen_lt continuous_const continuous_fst).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_const)))

private theorem leftInterface_subset_interior {p : PlanePoint}
    (hx : p.1 = a.leftCenter.1) (hylo : (-1 : ℝ) < p.2)
    (hyhi : p.2 < 1) : p ∈ interior a.coreCarrier := by
  have hdisk :
      (p.1 - a.leftCenter.1) ^ 2 +
          (p.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 := by
    simp only [hx, sub_self, leftCenter]
    nlinarith [a.one_lt_radius]
  by_cases hw : a.sideHalfWidth = 0
  · let U : Set PlanePoint :=
      {q | (q.1 - a.leftCenter.1) ^ 2 +
          (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 ∧
        (-1 : ℝ) < q.2 ∧ q.2 < 1}
    have hopen : IsOpen U := by
      change IsOpen
        ({q : PlanePoint |
            (q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2} ∩
          ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
            {q : PlanePoint | q.2 < 1}))
      exact (isOpen_lt
        (((continuous_fst.sub continuous_const).pow 2).add
          ((continuous_snd.sub continuous_const).pow 2))
        continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt continuous_snd continuous_const))
    have hsub : U ⊆ a.coreCarrier := by
      intro q hq
      by_cases hqx : q.1 ≤ 0
      · apply Or.inl
        apply Or.inr
        change
          (q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2 ∧
            q.1 ≤ a.leftCenter.1 ∧
              (-1 : ℝ) ≤ q.2 ∧ q.2 ≤ 1
        exact ⟨hq.1.le, by simpa [leftCenter, hw] using hqx,
          hq.2.1.le, hq.2.2.le⟩
      · apply Or.inr
        change
          (q.1 - a.rightCenter.1) ^ 2 +
                (q.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2 ∧
            a.rightCenter.1 ≤ q.1 ∧
              (-1 : ℝ) ≤ q.2 ∧ q.2 ≤ 1
        exact ⟨by simpa [leftCenter, rightCenter, hw] using hq.1.le,
          by simpa [rightCenter, hw] using le_of_not_ge hqx,
          hq.2.1.le, hq.2.2.le⟩
    exact interior_maximal hsub hopen ⟨hdisk, hylo, hyhi⟩
  · have hwpos : 0 < a.sideHalfWidth :=
      lt_of_le_of_ne a.sideHalfWidth_nonneg (Ne.symm hw)
    let U : Set PlanePoint :=
      {q | (q.1 - a.leftCenter.1) ^ 2 +
          (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 ∧
        (-1 : ℝ) < q.2 ∧ q.2 < 1 ∧ q.1 < a.sideHalfWidth}
    have hopen : IsOpen U := by
      change IsOpen
        ({q : PlanePoint |
            (q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2} ∩
          ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
            ({q : PlanePoint | q.2 < 1} ∩
              {q : PlanePoint | q.1 < a.sideHalfWidth})))
      exact (isOpen_lt
        (((continuous_fst.sub continuous_const).pow 2).add
          ((continuous_snd.sub continuous_const).pow 2))
        continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            ((isOpen_lt continuous_snd continuous_const).inter
              (isOpen_lt continuous_fst continuous_const)))
    have hsub : U ⊆ a.coreCarrier := by
      intro q hq
      by_cases hqx : q.1 ≤ a.leftCenter.1
      · exact Or.inl (Or.inr
          ⟨hq.1.le, hqx, hq.2.1.le, hq.2.2.1.le⟩)
      · apply Or.inl
        apply Or.inl
        exact ⟨⟨by simpa [leftCenter] using le_of_not_ge hqx,
          hq.2.2.2.le⟩, ⟨hq.2.1.le, hq.2.2.1.le⟩⟩
    apply interior_maximal hsub hopen
    exact ⟨hdisk, hylo, hyhi, by
      rw [hx]
      simp only [leftCenter]
      linarith⟩

private theorem rightInterface_subset_interior {p : PlanePoint}
    (hx : p.1 = a.rightCenter.1) (hylo : (-1 : ℝ) < p.2)
    (hyhi : p.2 < 1) : p ∈ interior a.coreCarrier := by
  have hdisk :
      (p.1 - a.rightCenter.1) ^ 2 +
          (p.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 := by
    simp only [hx, sub_self, rightCenter]
    nlinarith [a.one_lt_radius]
  by_cases hw : a.sideHalfWidth = 0
  · have hcenters : a.rightCenter = a.leftCenter := by
      simp [rightCenter, leftCenter, hw]
    rw [hcenters] at hx hdisk
    exact a.leftInterface_subset_interior hx hylo hyhi
  · have hwpos : 0 < a.sideHalfWidth :=
      lt_of_le_of_ne a.sideHalfWidth_nonneg (Ne.symm hw)
    let U : Set PlanePoint :=
      {q | (q.1 - a.rightCenter.1) ^ 2 +
          (q.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 ∧
        (-1 : ℝ) < q.2 ∧ q.2 < 1 ∧ -a.sideHalfWidth < q.1}
    have hopen : IsOpen U := by
      change IsOpen
        ({q : PlanePoint |
            (q.1 - a.rightCenter.1) ^ 2 +
                (q.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2} ∩
          ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
            ({q : PlanePoint | q.2 < 1} ∩
              {q : PlanePoint | -a.sideHalfWidth < q.1})))
      exact (isOpen_lt
        (((continuous_fst.sub continuous_const).pow 2).add
          ((continuous_snd.sub continuous_const).pow 2))
        continuous_const).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            ((isOpen_lt continuous_snd continuous_const).inter
              (isOpen_lt continuous_const continuous_fst)))
    have hsub : U ⊆ a.coreCarrier := by
      intro q hq
      by_cases hqx : a.rightCenter.1 ≤ q.1
      · exact Or.inr
          ⟨hq.1.le, hqx, hq.2.1.le, hq.2.2.1.le⟩
      · apply Or.inl
        apply Or.inl
        exact ⟨⟨hq.2.2.2.le,
          by simpa [rightCenter] using le_of_not_ge hqx⟩,
          ⟨hq.2.1.le, hq.2.2.1.le⟩⟩
    apply interior_maximal hsub hopen
    exact ⟨hdisk, hylo, hyhi, by
      rw [hx]
      simp only [rightCenter]
      linarith⟩


private theorem mem_outerChord_of_top_bounds {p : PlanePoint}
    (hy : p.2 = 1)
    (hx : -(a.radius * sin a.outerAngle) ≤ p.1 ∧
      p.1 ≤ a.radius * sin a.outerAngle) :
    p ∈ a.outerCap.chordCarrier := by
  change p.2 = 1 ∧
    |p.1 - 0| ≤ (2 * a.radius * sin a.outerAngle) / 2
  constructor
  · exact hy
  · rw [sub_zero]
    apply abs_le.mpr
    constructor <;> linarith

private theorem frontier_coreCarrier_subset :
    frontier a.coreCarrier ⊆
      a.leftArcTrace ∪
        (a.rightArcTrace ∪
          (a.outerCap.chordCarrier ∪ a.bottomSegmentCarrier)) := by
  intro p hp
  have hpc : p ∈ a.coreCarrier :=
    a.isClosed_coreCarrier.frontier_subset hp
  have hnint : p ∉ interior a.coreCarrier :=
    (mem_frontier_iff_notMem_interior hpc).mp hp
  rcases hpc with (hrect | hleft) | hright
  · change
      (-a.sideHalfWidth ≤ p.1 ∧ p.1 ≤ a.sideHalfWidth) ∧
        ((-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1) at hrect
    by_cases htop : p.2 = 1
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      apply a.mem_outerChord_of_top_bounds htop
      have hw := a.sideHalfWidth_nonneg
      have hs := a.innerSin_pos
      rw [sideHalfWidth] at hrect
      constructor <;> nlinarith [a.radius_pos]
    by_cases hbottom : p.2 = -1
    · exact Or.inr (Or.inr (Or.inr
        ⟨hbottom, abs_le.mpr hrect.1⟩))
    have hylo : (-1 : ℝ) < p.2 :=
      lt_of_le_of_ne hrect.2.1 (Ne.symm hbottom)
    have hyhi : p.2 < 1 :=
      lt_of_le_of_ne hrect.2.2 htop
    by_cases hxl : p.1 = -a.sideHalfWidth
    · exfalso
      apply hnint
      apply a.leftInterface_subset_interior
      · simpa [leftCenter] using hxl
      · exact hylo
      · exact hyhi
    by_cases hxr : p.1 = a.sideHalfWidth
    · exfalso
      apply hnint
      apply a.rightInterface_subset_interior
      · simpa [rightCenter] using hxr
      · exact hylo
      · exact hyhi
    · exfalso
      apply hnint
      exact a.strictRectangle_subset_interior
        ⟨lt_of_le_of_ne hrect.1.1 (Ne.symm hxl),
          lt_of_le_of_ne hrect.1.2 hxr, hylo, hyhi⟩
  · change
      ((p.1 - a.leftCenter.1) ^ 2 +
          (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
        p.1 ≤ a.leftCenter.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hleft
    by_cases hcircle :
        (p.1 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 = a.radius ^ 2
    · exact Or.inl ⟨hcircle, hleft.2⟩
    have hdisk :
        (p.1 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 :=
      lt_of_le_of_ne hleft.1 hcircle
    by_cases htop : p.2 = 1
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      apply a.mem_outerChord_of_top_bounds htop
      have hdx : p.1 - a.leftCenter.1 ≤ 0 := by linarith [hleft.2.1]
      have hdx' : p.1 + a.sideHalfWidth ≤ 0 := by
        simpa only [leftCenter, sub_neg_eq_add] using hdx
      have hdiskTop :
          (p.1 + a.sideHalfWidth) ^ 2 + (2 - a.radius) ^ 2 ≤
            a.radius ^ 2 := by
        have := hleft.1
        simp only [leftCenter, htop, sub_neg_eq_add] at this
        convert this using 1 <;> ring
      have hsquare :
          (p.1 + a.sideHalfWidth) ^ 2 ≤
            (a.radius * sin a.innerAngle) ^ 2 := by
        nlinarith [a.side_circle_at_top]
      have habs :
          |p.1 + a.sideHalfWidth| ≤
            |a.radius * sin a.innerAngle| :=
        sq_le_sq.mp hsquare
      rw [abs_of_nonpos hdx',
        abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] at habs
      have hdxlo :
          -(a.radius * sin a.innerAngle) ≤
            p.1 + a.sideHalfWidth := by linarith
      have hxnonpos : p.1 ≤ 0 := by
        have hbound := hleft.2.1
        simp only [leftCenter] at hbound
        linarith [a.sideHalfWidth_nonneg]
      constructor
      · rw [sideHalfWidth] at hdxlo
        linarith
      · exact le_trans hxnonpos (mul_nonneg a.radius_pos.le a.outerSin_pos.le)
    by_cases hbottom : p.2 = -1
    · have hx : p.1 = a.leftCenter.1 := by
        have hd := hleft.1
        simp only [leftCenter, hbottom, sub_neg_eq_add] at hd
        ring_nf at hd
        have hsq := sq_nonneg (p.1 + a.sideHalfWidth)
        have hxeq : p.1 + a.sideHalfWidth = 0 := by nlinarith
        change p.1 = -a.sideHalfWidth
        linarith
      exact Or.inl ⟨by rw [hx, hbottom]; simp [leftCenter]; ring,
        hleft.2.1, hleft.2.2.1, hleft.2.2.2⟩
    have hylo : (-1 : ℝ) < p.2 :=
      lt_of_le_of_ne hleft.2.2.1 (Ne.symm hbottom)
    have hyhi : p.2 < 1 :=
      lt_of_le_of_ne hleft.2.2.2 htop
    by_cases hx : p.1 = a.leftCenter.1
    · exact False.elim (hnint
        (a.leftInterface_subset_interior hx hylo hyhi))
    · exact False.elim (hnint
        (a.strictLeftSegment_subset_interior
          ⟨hdisk, lt_of_le_of_ne hleft.2.1 hx, hylo, hyhi⟩))
  · change
      ((p.1 - a.rightCenter.1) ^ 2 +
          (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
        a.rightCenter.1 ≤ p.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hright
    by_cases hcircle :
        (p.1 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 = a.radius ^ 2
    · exact Or.inr (Or.inl ⟨hcircle, hright.2⟩)
    have hdisk :
        (p.1 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 :=
      lt_of_le_of_ne hright.1 hcircle
    by_cases htop : p.2 = 1
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      apply a.mem_outerChord_of_top_bounds htop
      have hdx : 0 ≤ p.1 - a.rightCenter.1 := by linarith [hright.2.1]
      have hdx' : 0 ≤ p.1 - a.sideHalfWidth := by
        simpa only [rightCenter] using hdx
      have hdiskTop :
          (p.1 - a.sideHalfWidth) ^ 2 + (2 - a.radius) ^ 2 ≤
            a.radius ^ 2 := by
        have := hright.1
        simp only [rightCenter, htop] at this
        convert this using 1 <;> ring
      have hsquare :
          (p.1 - a.sideHalfWidth) ^ 2 ≤
            (a.radius * sin a.innerAngle) ^ 2 := by
        nlinarith [a.side_circle_at_top]
      have habs :
          |p.1 - a.sideHalfWidth| ≤
            |a.radius * sin a.innerAngle| :=
        sq_le_sq.mp hsquare
      rw [abs_of_nonneg hdx',
        abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] at habs
      have hdxhi :
          p.1 - a.sideHalfWidth ≤
            a.radius * sin a.innerAngle := habs
      have hxnonneg : 0 ≤ p.1 := by
        have hbound := hright.2.1
        simp only [rightCenter] at hbound
        linarith [a.sideHalfWidth_nonneg]
      constructor
      · exact le_trans (neg_nonpos.mpr
          (mul_nonneg a.radius_pos.le a.outerSin_pos.le)) hxnonneg
      · rw [sideHalfWidth] at hdxhi
        linarith
    by_cases hbottom : p.2 = -1
    · have hx : p.1 = a.rightCenter.1 := by
        have hd := hright.1
        simp only [rightCenter, hbottom] at hd
        ring_nf at hd
        have hsq := sq_nonneg (p.1 - a.sideHalfWidth)
        have hxeq : p.1 - a.sideHalfWidth = 0 := by nlinarith
        change p.1 = a.sideHalfWidth
        linarith
      exact Or.inr (Or.inl
        ⟨by rw [hx, hbottom]; simp [rightCenter]; ring,
          hright.2.1, hright.2.2.1, hright.2.2.2⟩)
    have hylo : (-1 : ℝ) < p.2 :=
      lt_of_le_of_ne hright.2.2.1 (Ne.symm hbottom)
    have hyhi : p.2 < 1 :=
      lt_of_le_of_ne hright.2.2.2 htop
    by_cases hx : p.1 = a.rightCenter.1
    · exact False.elim (hnint
        (a.rightInterface_subset_interior hx hylo hyhi))
    · exact False.elim (hnint
        (a.strictRightSegment_subset_interior
          ⟨hdisk, lt_of_le_of_ne hright.2.1 (Ne.symm hx),
            hylo, hyhi⟩))

private theorem outerCap_strictDisk_at_top {p : PlanePoint}
    (hy : p.2 = 1)
    (hx : |p.1| < a.radius * sin a.outerAngle) :
    a.outerCap.radiusSquaredAt p < a.outerCap.radius ^ 2 := by
  have hxsq : p.1 ^ 2 <
      (a.radius * sin a.outerAngle) ^ 2 := by
    rw [sq_lt_sq]
    simpa [abs_of_pos (mul_pos a.radius_pos a.outerSin_pos)] using hx
  have htrig := congrArg (fun z : ℝ => a.radius ^ 2 * z)
    (Real.sin_sq_add_cos_sq a.outerAngle)
  rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
    a.outerCap_radius, hy]
  dsimp [upperCenter]
  nlinarith

private theorem upper_strictChord_mem_interior {p : PlanePoint}
    (hy : p.2 = 1)
    (hx : |p.1| < a.radius * sin a.outerAngle) :
    p ∈ interior a.carrier := by
  have houter := a.outerCap_strictDisk_at_top hy hx
  have hylo : (-1 : ℝ) < p.2 := by rw [hy]; norm_num
  by_cases hw : a.sideHalfWidth = 0
  · have hcenters : a.rightCenter = a.leftCenter := by
      simp [rightCenter, leftCenter, hw]
    have hside :
        (p.1 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 := by
      have harg :
          |p.1| < a.radius * sin a.innerAngle := by
        have hsine :
            sin a.outerAngle = sin a.innerAngle := by
          have hz := a.sideHalfWidth_eq_zero_iff.mp hw
          rw [a.innerAngle_semicircular hz, a.outerAngle_semicircular hz]
        simpa [hsine] using hx
      have hxsq : p.1 ^ 2 <
          (a.radius * sin a.innerAngle) ^ 2 := by
        rw [sq_lt_sq]
        simpa [abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] using harg
      have hc := a.side_circle_at_top
      simp only [leftCenter, hw, hy, neg_zero, sub_zero]
      nlinarith
    let U : Set PlanePoint :=
      {q | (q.1 - a.leftCenter.1) ^ 2 +
              (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 ∧
        a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2 ∧
        (-1 : ℝ) < q.2}
    have hopen : IsOpen U := by
      change IsOpen
        ({q : PlanePoint |
            (q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2} ∩
          ({q : PlanePoint |
              a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2} ∩
            {q : PlanePoint | (-1 : ℝ) < q.2}))
      exact (isOpen_lt
        (((continuous_fst.sub continuous_const).pow 2).add
          ((continuous_snd.sub continuous_const).pow 2))
        continuous_const).inter
          ((isOpen_lt (by
            change Continuous (fun q : PlanePoint =>
              (q.1 - a.outerCap.center.1) ^ 2 +
                (q.2 - a.outerCap.center.2) ^ 2)
            fun_prop) continuous_const).inter
              (isOpen_lt continuous_const continuous_snd))
    have hsub : U ⊆ a.carrier := by
      intro q hq
      by_cases hqy : q.2 ≤ 1
      · apply Or.inl
        by_cases hqx : q.1 ≤ 0
        · apply Or.inl
          apply Or.inr
          change
            ((q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
              q.1 ≤ a.leftCenter.1 ∧
                (-1 : ℝ) ≤ q.2 ∧ q.2 ≤ 1
          exact ⟨hq.1.le, by simpa [leftCenter, hw] using hqx,
            hq.2.2.le, hqy⟩
        · apply Or.inr
          change
            ((q.1 - a.rightCenter.1) ^ 2 +
                (q.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
              a.rightCenter.1 ≤ q.1 ∧
                (-1 : ℝ) ≤ q.2 ∧ q.2 ≤ 1
          exact ⟨by simpa [hcenters] using hq.1.le,
            by simpa [rightCenter, hw] using le_of_not_ge hqx,
            hq.2.2.le, hqy⟩
      · exact Or.inr ⟨hq.2.1.le, by
          simpa [outerCap, OneSidedCircularCap.carrier] using
            (le_of_not_ge hqy)⟩
    exact interior_maximal hsub hopen ⟨hside, houter, hylo⟩
  · have hwpos : 0 < a.sideHalfWidth :=
      lt_of_le_of_ne a.sideHalfWidth_nonneg (Ne.symm hw)
    rcases lt_trichotomy p.1 a.leftCenter.1 with hleft | hleftEq | hnleft
    · have hside :
          (p.1 - a.leftCenter.1) ^ 2 +
              (p.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 := by
        have hxlower := (abs_lt.mp hx).1
        have hdxlo :
            -(a.radius * sin a.innerAngle) <
              p.1 + a.sideHalfWidth := by
          rw [sideHalfWidth]
          linarith
        have hdxhi : p.1 + a.sideHalfWidth < 0 := by
          have hc : a.leftCenter.1 = -a.sideHalfWidth := rfl
          rw [hc] at hleft
          linarith
        have habs :
            |p.1 + a.sideHalfWidth| <
              a.radius * sin a.innerAngle := by
          rw [abs_of_nonpos hdxhi.le]
          linarith
        have habs' :
            |p.1 + a.sideHalfWidth| <
              |a.radius * sin a.innerAngle| := by
          rw [abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)]
          exact habs
        have hsq := (sq_lt_sq).2 habs'
        simp only [leftCenter, hy, sub_neg_eq_add]
        nlinarith [a.side_circle_at_top]
      let U : Set PlanePoint :=
        {q | (q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 ∧
          a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2 ∧
          (-1 : ℝ) < q.2 ∧ q.1 < a.rightCenter.1}
      have hopen : IsOpen U := by
        change IsOpen
          ({q : PlanePoint |
              (q.1 - a.leftCenter.1) ^ 2 +
                  (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2} ∩
            ({q : PlanePoint |
                a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2} ∩
              ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
                {q : PlanePoint | q.1 < a.rightCenter.1})))
        exact (isOpen_lt
          (((continuous_fst.sub continuous_const).pow 2).add
            ((continuous_snd.sub continuous_const).pow 2))
          continuous_const).inter
            ((isOpen_lt (by
              change Continuous (fun q : PlanePoint =>
                (q.1 - a.outerCap.center.1) ^ 2 +
                  (q.2 - a.outerCap.center.2) ^ 2)
              fun_prop) continuous_const).inter
                ((isOpen_lt continuous_const continuous_snd).inter
                  (isOpen_lt continuous_fst continuous_const)))
      have hsub : U ⊆ a.carrier := by
        intro q hq
        by_cases hqy : q.2 ≤ 1
        · apply Or.inl
          by_cases hqx : q.1 ≤ a.leftCenter.1
          · exact Or.inl (Or.inr
              ⟨hq.1.le, hqx, hq.2.2.1.le, hqy⟩)
          · apply Or.inl
            apply Or.inl
            exact ⟨⟨by simpa [leftCenter] using le_of_not_ge hqx,
              by simpa [rightCenter] using hq.2.2.2.le⟩,
              hq.2.2.1.le, hqy⟩
        · exact Or.inr ⟨hq.2.1.le, by
            simpa [outerCap, OneSidedCircularCap.carrier] using
              (le_of_not_ge hqy)⟩
      apply interior_maximal hsub hopen
      exact ⟨hside, houter, hylo, by
        simp only [rightCenter]
        have hlc : a.leftCenter.1 = -a.sideHalfWidth := rfl
        rw [hlc] at hleft
        linarith⟩
    · have hside :
          (p.1 - a.leftCenter.1) ^ 2 +
              (p.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 := by
        rw [hleftEq, hy]
        simp only [sub_self, leftCenter]
        nlinarith [a.one_lt_radius]
      let U : Set PlanePoint :=
        {q | (q.1 - a.leftCenter.1) ^ 2 +
                (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2 ∧
          a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2 ∧
          (-1 : ℝ) < q.2 ∧ q.1 < a.rightCenter.1}
      have hopen : IsOpen U := by
        change IsOpen
          ({q : PlanePoint |
              (q.1 - a.leftCenter.1) ^ 2 +
                  (q.2 - a.leftCenter.2) ^ 2 < a.radius ^ 2} ∩
            ({q : PlanePoint |
                a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2} ∩
              ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
                {q : PlanePoint | q.1 < a.rightCenter.1})))
        exact (isOpen_lt
          (((continuous_fst.sub continuous_const).pow 2).add
            ((continuous_snd.sub continuous_const).pow 2))
          continuous_const).inter
            ((isOpen_lt (by
              change Continuous (fun q : PlanePoint =>
                (q.1 - a.outerCap.center.1) ^ 2 +
                  (q.2 - a.outerCap.center.2) ^ 2)
              fun_prop) continuous_const).inter
                ((isOpen_lt continuous_const continuous_snd).inter
                  (isOpen_lt continuous_fst continuous_const)))
      have hsub : U ⊆ a.carrier := by
        intro q hq
        by_cases hqy : q.2 ≤ 1
        · apply Or.inl
          by_cases hqx : q.1 ≤ a.leftCenter.1
          · exact Or.inl (Or.inr
              ⟨hq.1.le, hqx, hq.2.2.1.le, hqy⟩)
          · exact Or.inl (Or.inl
              ⟨⟨by simpa [leftCenter] using le_of_not_ge hqx,
                by simpa [rightCenter] using hq.2.2.2.le⟩,
                hq.2.2.1.le, hqy⟩)
        · exact Or.inr ⟨hq.2.1.le, by
            simpa [outerCap, OneSidedCircularCap.carrier] using
              (le_of_not_ge hqy)⟩
      apply interior_maximal hsub hopen
      exact ⟨hside, houter, hylo, by
        rw [hleftEq]
        simp only [leftCenter, rightCenter]
        linarith⟩
    · rcases lt_trichotomy p.1 a.rightCenter.1 with hmiddle | hrightEq | hright
      · let U : Set PlanePoint :=
          {q | -a.sideHalfWidth < q.1 ∧ q.1 < a.sideHalfWidth ∧
            (-1 : ℝ) < q.2 ∧
            a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2}
        have hopen : IsOpen U := by
          change IsOpen
            ({q : PlanePoint | -a.sideHalfWidth < q.1} ∩
              ({q : PlanePoint | q.1 < a.sideHalfWidth} ∩
                ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
                  {q : PlanePoint |
                    a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2})))
          exact (isOpen_lt continuous_const continuous_fst).inter
            ((isOpen_lt continuous_fst continuous_const).inter
              ((isOpen_lt continuous_const continuous_snd).inter
                (isOpen_lt (by
                  change Continuous (fun q : PlanePoint =>
                    (q.1 - a.outerCap.center.1) ^ 2 +
                      (q.2 - a.outerCap.center.2) ^ 2)
                  fun_prop) continuous_const)))
        have hsub : U ⊆ a.carrier := by
          intro q hq
          by_cases hqy : q.2 ≤ 1
          · exact Or.inl (Or.inl (Or.inl
              ⟨⟨hq.1.le, hq.2.1.le⟩, hq.2.2.1.le, hqy⟩))
          · exact Or.inr ⟨hq.2.2.2.le, by
              simpa [outerCap, OneSidedCircularCap.carrier] using
                (le_of_not_ge hqy)⟩
        apply interior_maximal hsub hopen
        exact ⟨by simpa [leftCenter] using hnleft,
          by simpa [rightCenter] using hmiddle, hylo, houter⟩
      · have hside :
            (p.1 - a.rightCenter.1) ^ 2 +
                (p.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 := by
          rw [hrightEq, hy]
          simp only [sub_self, rightCenter]
          nlinarith [a.one_lt_radius]
        let U : Set PlanePoint :=
          {q | (q.1 - a.rightCenter.1) ^ 2 +
                  (q.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 ∧
            a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2 ∧
            (-1 : ℝ) < q.2 ∧ a.leftCenter.1 < q.1}
        have hopen : IsOpen U := by
          change IsOpen
            ({q : PlanePoint |
                (q.1 - a.rightCenter.1) ^ 2 +
                    (q.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2} ∩
              ({q : PlanePoint |
                  a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2} ∩
                ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
                  {q : PlanePoint | a.leftCenter.1 < q.1})))
          exact (isOpen_lt
            (((continuous_fst.sub continuous_const).pow 2).add
              ((continuous_snd.sub continuous_const).pow 2))
            continuous_const).inter
              ((isOpen_lt (by
                change Continuous (fun q : PlanePoint =>
                  (q.1 - a.outerCap.center.1) ^ 2 +
                    (q.2 - a.outerCap.center.2) ^ 2)
                fun_prop) continuous_const).inter
                  ((isOpen_lt continuous_const continuous_snd).inter
                    (isOpen_lt continuous_const continuous_fst)))
        have hsub : U ⊆ a.carrier := by
          intro q hq
          by_cases hqy : q.2 ≤ 1
          · apply Or.inl
            by_cases hqx : a.rightCenter.1 ≤ q.1
            · exact Or.inr ⟨hq.1.le, hqx, hq.2.2.1.le, hqy⟩
            · exact Or.inl (Or.inl
                ⟨⟨by simpa [leftCenter] using hq.2.2.2.le,
                  by simpa [rightCenter] using le_of_not_ge hqx⟩,
                  hq.2.2.1.le, hqy⟩)
          · exact Or.inr ⟨hq.2.1.le, by
              simpa [outerCap, OneSidedCircularCap.carrier] using
                (le_of_not_ge hqy)⟩
        apply interior_maximal hsub hopen
        exact ⟨hside, houter, hylo, by
          rw [hrightEq]
          simp only [leftCenter, rightCenter]
          linarith⟩
      · have hside :
            (p.1 - a.rightCenter.1) ^ 2 +
                (p.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 := by
          have hxupper := (abs_lt.mp hx).2
          have hdxhi :
              p.1 - a.sideHalfWidth <
                a.radius * sin a.innerAngle := by
            rw [sideHalfWidth]
            linarith
          have hdxlo : 0 < p.1 - a.sideHalfWidth := by
            have hc : a.rightCenter.1 = a.sideHalfWidth := rfl
            rw [hc] at hright
            linarith
          have habs :
              |p.1 - a.sideHalfWidth| <
                a.radius * sin a.innerAngle := by
            rw [abs_of_nonneg hdxlo.le]
            exact hdxhi
          have habs' :
              |p.1 - a.sideHalfWidth| <
                |a.radius * sin a.innerAngle| := by
            rw [abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)]
            exact habs
          have hsq := (sq_lt_sq).2 habs'
          simp only [rightCenter, hy]
          nlinarith [a.side_circle_at_top]
        let U : Set PlanePoint :=
          {q | (q.1 - a.rightCenter.1) ^ 2 +
                  (q.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2 ∧
            a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2 ∧
            (-1 : ℝ) < q.2 ∧ a.leftCenter.1 < q.1}
        have hopen : IsOpen U := by
          change IsOpen
            ({q : PlanePoint |
                (q.1 - a.rightCenter.1) ^ 2 +
                    (q.2 - a.rightCenter.2) ^ 2 < a.radius ^ 2} ∩
              ({q : PlanePoint |
                  a.outerCap.radiusSquaredAt q < a.outerCap.radius ^ 2} ∩
                ({q : PlanePoint | (-1 : ℝ) < q.2} ∩
                  {q : PlanePoint | a.leftCenter.1 < q.1})))
          exact (isOpen_lt
            (((continuous_fst.sub continuous_const).pow 2).add
              ((continuous_snd.sub continuous_const).pow 2))
            continuous_const).inter
              ((isOpen_lt (by
                change Continuous (fun q : PlanePoint =>
                  (q.1 - a.outerCap.center.1) ^ 2 +
                    (q.2 - a.outerCap.center.2) ^ 2)
                fun_prop) continuous_const).inter
                  ((isOpen_lt continuous_const continuous_snd).inter
                    (isOpen_lt continuous_const continuous_fst)))
        have hsub : U ⊆ a.carrier := by
          intro q hq
          by_cases hqy : q.2 ≤ 1
          · apply Or.inl
            by_cases hqx : a.rightCenter.1 ≤ q.1
            · exact Or.inr ⟨hq.1.le, hqx, hq.2.2.1.le, hqy⟩
            · exact Or.inl (Or.inl
                ⟨⟨by simpa [leftCenter] using hq.2.2.2.le,
                  by simpa [rightCenter] using le_of_not_ge hqx⟩,
                  hq.2.2.1.le, hqy⟩)
          · exact Or.inr ⟨hq.2.1.le, by
              simpa [outerCap, OneSidedCircularCap.carrier] using
                (le_of_not_ge hqy)⟩
        apply interior_maximal hsub hopen
        exact ⟨hside, houter, hylo, by
          simp only [leftCenter]
          have hrc : a.rightCenter.1 = a.sideHalfWidth := rfl
          rw [hrc] at hright
          linarith⟩

private theorem outerCap_leftEndpoint_mem_leftArc :
    a.outerCap.leftEndpoint ∈ a.leftArcTrace := by
  rw [← a.leftUpperJunction]
  change
    ((a.leftCenter.1 - a.radius * sin a.innerAngle) -
        a.leftCenter.1) ^ 2 +
          ((1 : ℝ) - a.leftCenter.2) ^ 2 = a.radius ^ 2 ∧
      a.leftCenter.1 - a.radius * sin a.innerAngle ≤
        a.leftCenter.1 ∧
      (-1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1
  exact ⟨by
    simp only [leftCenter]
    nlinarith [a.side_circle_at_top],
    by nlinarith [a.radius_pos, a.innerSin_pos], by norm_num, by norm_num⟩

private theorem outerCap_rightEndpoint_mem_rightArc :
    a.outerCap.rightEndpoint ∈ a.rightArcTrace := by
  rw [← a.rightUpperJunction]
  change
    ((a.rightCenter.1 + a.radius * sin a.innerAngle) -
        a.rightCenter.1) ^ 2 +
          ((1 : ℝ) - a.rightCenter.2) ^ 2 = a.radius ^ 2 ∧
      a.rightCenter.1 ≤
        a.rightCenter.1 + a.radius * sin a.innerAngle ∧
      (-1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1
  exact ⟨by
    simp only [rightCenter]
    nlinarith [a.side_circle_at_top],
    by nlinarith [a.radius_pos, a.innerSin_pos], by norm_num, by norm_num⟩

private theorem outerChord_to_boundaryTrace {p : PlanePoint}
    (hpchord : p ∈ a.outerCap.chordCarrier)
    (hpfrontier : p ∈ frontier a.carrier) :
    p ∈ a.boundaryTrace := by
  have hy : p.2 = 1 := by
    simpa [outerCap, OneSidedCircularCap.chordCarrier] using hpchord.1
  have hxle : |p.1| ≤ a.radius * sin a.outerAngle := by
    have hxraw := hpchord.2
    change |p.1 - 0| ≤ (2 * a.radius * sin a.outerAngle) / 2 at hxraw
    rw [sub_zero] at hxraw
    nlinarith
  by_cases hstrict : |p.1| < a.radius * sin a.outerAngle
  · exfalso
    have hpCarrier := a.isClosed_carrier.frontier_subset hpfrontier
    exact (mem_frontier_iff_notMem_interior hpCarrier).mp hpfrontier
      (a.upper_strictChord_mem_interior hy hstrict)
  · have habs : |p.1| = a.radius * sin a.outerAngle :=
      le_antisymm hxle (le_of_not_gt hstrict)
    by_cases hnonneg : 0 ≤ p.1
    · have hpx : p.1 = a.radius * sin a.outerAngle := by
        rw [abs_of_nonneg hnonneg] at habs
        exact habs
      have hpEq : p = a.outerCap.rightEndpoint := by
        rw [a.outerCap_rightEndpoint]
        exact Prod.ext (by simpa using hpx) (by simpa using hy)
      exact Or.inr (Or.inl (by
        rw [hpEq]
        exact a.outerCap_rightEndpoint_mem_rightArc))
    · have hnonpos : p.1 ≤ 0 := le_of_not_ge hnonneg
      have hpx : p.1 = -(a.radius * sin a.outerAngle) := by
        rw [abs_of_nonpos hnonpos] at habs
        linarith
      have hpEq : p = a.outerCap.leftEndpoint := by
        rw [a.outerCap_leftEndpoint]
        exact Prod.ext (by simpa using hpx) (by simpa using hy)
      exact Or.inl (by
        rw [hpEq]
        exact a.outerCap_leftEndpoint_mem_leftArc)

theorem frontier_carrier_subset_boundaryTrace :
    frontier a.carrier ⊆ a.boundaryTrace := by
  intro p hp
  have htop := frontier_union_subset a.coreCarrier a.outerCap.carrier hp
  rcases htop with hcore | hcap
  · rcases a.frontier_coreCarrier_subset hcore.1 with
      hleft | hright | hchord | hbottom
    · exact Or.inl hleft
    · exact Or.inr (Or.inl hright)
    · exact a.outerChord_to_boundaryTrace hchord hp
    · exact Or.inr (Or.inr (Or.inr hbottom))
  · rw [a.outerCap.frontier_carrier] at hcap
    rcases hcap.2 with harc | hchord
    · exact Or.inr (Or.inr (Or.inl harc))
    · exact a.outerChord_to_boundaryTrace hchord hp

private lemma mem_frontier_union_of_mem_frontier_of_not_mem
    {s t : Set PlanePoint} {p : PlanePoint}
    (hs : IsClosed s) (ht : IsClosed t) (hp : p ∈ frontier s)
    (hpt : p ∉ t) : p ∈ frontier (s ∪ t) := by
  have hps : p ∈ s := hs.frontier_subset hp
  have hpUnion : p ∈ s ∪ t := Or.inl hps
  rw [mem_frontier_iff_notMem_interior hpUnion]
  intro hi
  have hUnion : interior (s ∪ t) ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  have hCompl : tᶜ ∈ nhds p := ht.isOpen_compl.mem_nhds hpt
  have hInter : interior (s ∪ t) ∩ tᶜ ∈ nhds p :=
    Filter.inter_mem hUnion hCompl
  have hsNhd : s ∈ nhds p := Filter.mem_of_superset hInter (by
    intro q hq
    rcases interior_subset hq.1 with hqs | hqt
    · exact hqs
    · exact False.elim (hq.2 hqt))
  have hpInterior : p ∈ interior s := mem_interior_iff_mem_nhds.mpr hsNhd
  exact (mem_frontier_iff_notMem_interior hps).mp hp hpInterior

private theorem leftArc_mem_frontier_core {p : PlanePoint}
    (hp : p ∈ a.leftArcTrace) : p ∈ frontier a.coreCarrier := by
  have hpCore : p ∈ a.coreCarrier :=
    Or.inl (Or.inr ⟨hp.1.le, hp.2.1, hp.2.2.1, hp.2.2.2⟩)
  rw [mem_frontier_iff_notMem_interior hpCore]
  intro hi
  have hn : interior a.coreCarrier ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 - ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_neg (by linarith : p.1 - ε / 2 - p.1 < 0)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqc := interior_subset (hball hqball)
  rcases hqc with (hrect | hleft) | hright
  · change
      (-a.sideHalfWidth ≤ p.1 - ε / 2 ∧
        p.1 - ε / 2 ≤ a.sideHalfWidth) ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hrect
    have hbound := hp.2.1
    simp only [leftCenter] at hbound
    linarith
  · have hcenter : p.1 - a.leftCenter.1 ≤ 0 := by
      linarith [hp.2.1]
    change
      ((p.1 - ε / 2 - a.leftCenter.1) ^ 2 +
          (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
        p.1 - ε / 2 ≤ a.leftCenter.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hleft
    nlinarith [hp.1]
  · change
      ((p.1 - ε / 2 - a.rightCenter.1) ^ 2 +
          (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
        a.rightCenter.1 ≤ p.1 - ε / 2 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hright
    have hw := a.sideHalfWidth_nonneg
    have hbound := hp.2.1
    simp only [leftCenter, rightCenter] at hbound hright
    linarith

private theorem rightArc_mem_frontier_core {p : PlanePoint}
    (hp : p ∈ a.rightArcTrace) : p ∈ frontier a.coreCarrier := by
  have hpCore : p ∈ a.coreCarrier :=
    Or.inr ⟨hp.1.le, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  rw [mem_frontier_iff_notMem_interior hpCore]
  intro hi
  have hn : interior a.coreCarrier ∈ nhds p :=
    isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 + ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_pos (by linarith : 0 < p.1 + ε / 2 - p.1)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqc := interior_subset (hball hqball)
  rcases hqc with (hrect | hleft) | hright
  · change
      (-a.sideHalfWidth ≤ p.1 + ε / 2 ∧
        p.1 + ε / 2 ≤ a.sideHalfWidth) ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hrect
    have hbound := hp.2.1
    simp only [rightCenter] at hbound
    linarith
  · change
      ((p.1 + ε / 2 - a.leftCenter.1) ^ 2 +
          (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
        p.1 + ε / 2 ≤ a.leftCenter.1 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hleft
    have hw := a.sideHalfWidth_nonneg
    have hbound := hp.2.1
    simp only [leftCenter, rightCenter] at hbound hleft
    linarith
  · have hcenter : 0 ≤ p.1 - a.rightCenter.1 := by
      linarith [hp.2.1]
    change
      ((p.1 + ε / 2 - a.rightCenter.1) ^ 2 +
          (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
        a.rightCenter.1 ≤ p.1 + ε / 2 ∧
          (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hright
    nlinarith [hp.1]

private theorem left_upper_endpoint_mem_frontier {p : PlanePoint}
    (hx : p.1 = -(a.radius * sin a.outerAngle))
    (hy : p.2 = 1) : p ∈ frontier a.carrier := by
  have hpEq : p = a.outerCap.leftEndpoint := by
    rw [a.outerCap_leftEndpoint]
    exact Prod.ext (by simpa using hx) (by simpa using hy)
  have hpArc : p ∈ a.leftArcTrace := by
    rw [hpEq]
    exact a.outerCap_leftEndpoint_mem_leftArc
  have hpCore : p ∈ a.coreCarrier :=
    Or.inl (Or.inr
      ⟨hpArc.1.le, hpArc.2.1, hpArc.2.2.1, hpArc.2.2.2⟩)
  have hpCarrier : p ∈ a.carrier := Or.inl hpCore
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hi
  have hn : interior a.carrier ∈ nhds p := isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 - ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_neg (by linarith : p.1 - ε / 2 - p.1 < 0)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqc := interior_subset (hball hqball)
  rcases hqc with hcore | hcap
  · rcases hcore with (hrect | hleft) | hright
    · change
        (-a.sideHalfWidth ≤ p.1 - ε / 2 ∧
          p.1 - ε / 2 ≤ a.sideHalfWidth) ∧
            (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hrect
      rw [hx, sideHalfWidth] at hrect
      nlinarith [a.radius_pos, a.innerSin_pos]
    · have hcenter : p.1 - a.leftCenter.1 < 0 := by
        rw [hx, leftCenter, sideHalfWidth]
        nlinarith [a.radius_pos, a.innerSin_pos]
      change
        ((p.1 - ε / 2 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
          p.1 - ε / 2 ≤ a.leftCenter.1 ∧
            (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hleft
      nlinarith [hpArc.1]
    · change
        ((p.1 - ε / 2 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
          a.rightCenter.1 ≤ p.1 - ε / 2 ∧
            (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hright
      have hqneg : p.1 - ε / 2 < 0 := by
        rw [hx]
        nlinarith [a.radius_pos, a.outerSin_pos]
      have hcnonneg : 0 ≤ a.rightCenter.1 := by
        simp only [rightCenter]
        exact a.sideHalfWidth_nonneg
      linarith [hright.2.1]
  · have hpCapCircle :
        a.outerCap.radiusSquaredAt p = a.outerCap.radius ^ 2 := by
      rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
        a.outerCap_radius, hx, hy]
      dsimp [upperCenter]
      have ht := congrArg (fun z : ℝ => a.radius ^ 2 * z)
        (Real.sin_sq_add_cos_sq a.outerAngle)
      nlinarith
    have hcenter : p.1 - a.outerCap.center.1 < 0 := by
      rw [a.outerCap_center, hx]
      dsimp [upperCenter]
      nlinarith [a.radius_pos, a.outerSin_pos]
    have hcapDisk := hcap.1
    rw [OneSidedCircularCap.radiusSquaredAt] at hpCapCircle
    change
      (p.1 - ε / 2 - a.outerCap.center.1) ^ 2 +
          (p.2 - a.outerCap.center.2) ^ 2 ≤
        a.outerCap.radius ^ 2 at hcapDisk
    nlinarith

private theorem right_upper_endpoint_mem_frontier {p : PlanePoint}
    (hx : p.1 = a.radius * sin a.outerAngle)
    (hy : p.2 = 1) : p ∈ frontier a.carrier := by
  have hpEq : p = a.outerCap.rightEndpoint := by
    rw [a.outerCap_rightEndpoint]
    exact Prod.ext (by simpa using hx) (by simpa using hy)
  have hpArc : p ∈ a.rightArcTrace := by
    rw [hpEq]
    exact a.outerCap_rightEndpoint_mem_rightArc
  have hpCore : p ∈ a.coreCarrier :=
    Or.inr ⟨hpArc.1.le, hpArc.2.1, hpArc.2.2.1, hpArc.2.2.2⟩
  have hpCarrier : p ∈ a.carrier := Or.inl hpCore
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hi
  have hn : interior a.carrier ∈ nhds p := isOpen_interior.mem_nhds hi
  rcases Metric.mem_nhds_iff.mp hn with ⟨ε, hε, hball⟩
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  let q : PlanePoint := (p.1 + ε / 2, p.2)
  have hqball : q ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    dsimp [q]
    rw [abs_of_pos (by linarith : 0 < p.1 + ε / 2 - p.1)]
    simp only [sub_self, abs_zero]
    ring_nf
    rw [max_eq_left (by positivity)]
    linarith
  have hqc := interior_subset (hball hqball)
  rcases hqc with hcore | hcap
  · rcases hcore with (hrect | hleft) | hright
    · change
        (-a.sideHalfWidth ≤ p.1 + ε / 2 ∧
          p.1 + ε / 2 ≤ a.sideHalfWidth) ∧
            (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hrect
      rw [hx, sideHalfWidth] at hrect
      nlinarith [a.radius_pos, a.innerSin_pos]
    · change
        ((p.1 + ε / 2 - a.leftCenter.1) ^ 2 +
            (p.2 - a.leftCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
          p.1 + ε / 2 ≤ a.leftCenter.1 ∧
            (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hleft
      have hqpos : 0 < p.1 + ε / 2 := by
        rw [hx]
        nlinarith [a.radius_pos, a.outerSin_pos]
      have hcnonpos : a.leftCenter.1 ≤ 0 := by
        simp only [leftCenter]
        linarith [a.sideHalfWidth_nonneg]
      linarith [hleft.2.1]
    · have hcenter : 0 < p.1 - a.rightCenter.1 := by
        rw [hx, rightCenter, sideHalfWidth]
        nlinarith [a.radius_pos, a.innerSin_pos]
      change
        ((p.1 + ε / 2 - a.rightCenter.1) ^ 2 +
            (p.2 - a.rightCenter.2) ^ 2 ≤ a.radius ^ 2) ∧
          a.rightCenter.1 ≤ p.1 + ε / 2 ∧
            (-1 : ℝ) ≤ p.2 ∧ p.2 ≤ 1 at hright
      nlinarith [hpArc.1]
  · have hpCapCircle :
        a.outerCap.radiusSquaredAt p = a.outerCap.radius ^ 2 := by
      rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
        a.outerCap_radius, hx, hy]
      dsimp [upperCenter]
      have ht := congrArg (fun z : ℝ => a.radius ^ 2 * z)
        (Real.sin_sq_add_cos_sq a.outerAngle)
      nlinarith
    have hcenter : 0 < p.1 - a.outerCap.center.1 := by
      rw [a.outerCap_center, hx]
      dsimp [upperCenter]
      nlinarith [a.radius_pos, a.outerSin_pos]
    have hcapDisk := hcap.1
    rw [OneSidedCircularCap.radiusSquaredAt] at hpCapCircle
    change
      (p.1 + ε / 2 - a.outerCap.center.1) ^ 2 +
          (p.2 - a.outerCap.center.2) ^ 2 ≤
        a.outerCap.radius ^ 2 at hcapDisk
    nlinarith

private theorem leftArc_mem_frontier {p : PlanePoint}
    (hp : p ∈ a.leftArcTrace) : p ∈ frontier a.carrier := by
  by_cases hy : p.2 = 1
  · have hdx : p.1 - a.leftCenter.1 ≤ 0 := by linarith [hp.2.1]
    have hsq :
        (p.1 - a.leftCenter.1) ^ 2 =
          (a.radius * sin a.innerAngle) ^ 2 := by
      have hc := a.side_circle_at_top
      have hpCircle := hp.1
      rw [hy] at hpCircle
      simp only [leftCenter] at hpCircle
      rw [leftCenter]
      nlinarith
    have habs := (sq_eq_sq_iff_abs_eq_abs
      (p.1 - a.leftCenter.1)
      (a.radius * sin a.innerAngle)).mp hsq
    rw [abs_of_nonpos hdx,
      abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] at habs
    have hdxEq :
        p.1 - a.leftCenter.1 =
          -(a.radius * sin a.innerAngle) := by linarith
    have hx : p.1 = -(a.radius * sin a.outerAngle) := by
      simp only [leftCenter] at hdxEq
      rw [sideHalfWidth] at hdxEq
      linarith
    exact a.left_upper_endpoint_mem_frontier hx hy
  · have hpCore := a.leftArc_mem_frontier_core hp
    have hnotCap : p ∉ a.outerCap.carrier := by
      intro hcap
      have hyge : (1 : ℝ) ≤ p.2 := by
        simpa [outerCap, OneSidedCircularCap.carrier] using hcap.2
      exact hy (le_antisymm hp.2.2.2 hyge)
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      a.isClosed_coreCarrier a.outerCap.isClosed_carrier hpCore hnotCap

private theorem rightArc_mem_frontier {p : PlanePoint}
    (hp : p ∈ a.rightArcTrace) : p ∈ frontier a.carrier := by
  by_cases hy : p.2 = 1
  · have hdx : 0 ≤ p.1 - a.rightCenter.1 := by linarith [hp.2.1]
    have hsq :
        (p.1 - a.rightCenter.1) ^ 2 =
          (a.radius * sin a.innerAngle) ^ 2 := by
      have hc := a.side_circle_at_top
      have hpCircle := hp.1
      rw [hy] at hpCircle
      simp only [rightCenter] at hpCircle
      rw [rightCenter]
      nlinarith
    have habs := (sq_eq_sq_iff_abs_eq_abs
      (p.1 - a.rightCenter.1)
      (a.radius * sin a.innerAngle)).mp hsq
    rw [abs_of_nonneg hdx,
      abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)] at habs
    have hdxEq :
        p.1 - a.rightCenter.1 =
          a.radius * sin a.innerAngle := habs
    have hx : p.1 = a.radius * sin a.outerAngle := by
      simp only [rightCenter] at hdxEq
      rw [sideHalfWidth] at hdxEq
      linarith
    exact a.right_upper_endpoint_mem_frontier hx hy
  · have hpCore := a.rightArc_mem_frontier_core hp
    have hnotCap : p ∉ a.outerCap.carrier := by
      intro hcap
      have hyge : (1 : ℝ) ≤ p.2 := by
        simpa [outerCap, OneSidedCircularCap.carrier] using hcap.2
      exact hy (le_antisymm hp.2.2.2 hyge)
    exact mem_frontier_union_of_mem_frontier_of_not_mem
      a.isClosed_coreCarrier a.outerCap.isClosed_carrier hpCore hnotCap

private theorem upperArc_mem_frontier {p : PlanePoint}
    (hp : p ∈ OneSidedCircularCap.arcTrace a.outerCap) :
    p ∈ frontier a.carrier := by
  by_cases hy : p.2 = 1
  · have hcircle := hp.1
    rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
      a.outerCap_radius, hy] at hcircle
    dsimp [upperCenter] at hcircle
    have ht := congrArg (fun z : ℝ => a.radius ^ 2 * z)
      (Real.sin_sq_add_cos_sq a.outerAngle)
    have hsq :
        p.1 ^ 2 = (a.radius * sin a.outerAngle) ^ 2 := by
      nlinarith
    have habs := (sq_eq_sq_iff_abs_eq_abs p.1
      (a.radius * sin a.outerAngle)).mp hsq
    rw [abs_of_pos (mul_pos a.radius_pos a.outerSin_pos)] at habs
    by_cases hnonneg : 0 ≤ p.1
    · rw [abs_of_nonneg hnonneg] at habs
      exact a.right_upper_endpoint_mem_frontier habs hy
    · have hnonpos : p.1 ≤ 0 := le_of_not_ge hnonneg
      rw [abs_of_nonpos hnonpos] at habs
      apply a.left_upper_endpoint_mem_frontier
      · linarith
      · exact hy
  · have hpCapFrontier : p ∈ frontier a.outerCap.carrier := by
      rw [a.outerCap.frontier_carrier]
      exact Or.inl hp
    have hnotCore : p ∉ a.coreCarrier := by
      intro hcore
      have hyCore : p.2 ≤ 1 := by
        rcases hcore with (hrect | hleft) | hright
        · exact hrect.2.2
        · exact hleft.2.2.2
        · exact hright.2.2.2
      have hyge : (1 : ℝ) ≤ p.2 := by
        simpa [outerCap, OneSidedCircularCap.arcTrace] using hp.2
      exact hy (le_antisymm hyCore hyge)
    have hfront : p ∈ frontier
        (a.outerCap.carrier ∪ a.coreCarrier) :=
      mem_frontier_union_of_mem_frontier_of_not_mem
        a.outerCap.isClosed_carrier a.isClosed_coreCarrier
          hpCapFrontier hnotCore
    rw [union_comm a.outerCap.carrier a.coreCarrier] at hfront
    exact hfront

theorem boundaryTrace_subset_frontier_carrier :
    a.boundaryTrace ⊆ frontier a.carrier := by
  rintro p (hleft | hright | hupper | hbottom)
  · exact a.leftArc_mem_frontier hleft
  · exact a.rightArc_mem_frontier hright
  · exact a.upperArc_mem_frontier hupper
  · exact a.bottomSegmentCarrier_subset_frontier hbottom

theorem frontier_carrier :
    frontier a.carrier = a.boundaryTrace :=
  Set.Subset.antisymm a.frontier_carrier_subset_boundaryTrace
    a.boundaryTrace_subset_frontier_carrier

/-- The Euclidean realization of the bottom segment is measurable, including
the singleton occurring at the semicircular transition. -/
theorem measurableSet_euclidean_bottomSegmentCarrier :
    MeasurableSet
      (planeEuclideanHomeomorph '' a.bottomSegmentCarrier) :=
  (planeEuclideanHomeomorph.isClosedMap _
    a.isClosed_bottomSegmentCarrier).measurableSet

private theorem strip_component_integral
    {s : Set PlanePoint} {length : ℝ}
    (hs : MeasurableSet (planeEuclideanHomeomorph '' s))
    (hstrip : ∀ p ∈ s, |p.2| ≤ 1)
    (hmass : (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' s) = ENNReal.ofReal length)
    (hlength : 0 ≤ length) :
    (∫ z in planeEuclideanHomeomorph '' s,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      length := by
  calc
    _ = ∫ _z in planeEuclideanHomeomorph '' s,
        (1 : ℝ) ∂(μH[1] : Measure EuclideanPlane) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hs] with z hz
      rcases hz with ⟨p, hp, rfl⟩
      change StripDensity lam
        (planeEuclideanHomeomorph.symm
          (planeEuclideanHomeomorph p)) = 1
      rw [planeEuclideanHomeomorph.symm_apply_apply]
      simp [StripDensity, hstrip p hp]
    _ = length := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one, Measure.real, hmass]
      exact ENNReal.toReal_ofReal hlength

private theorem leftArc_integral :
    (∫ z in planeEuclideanHomeomorph '' a.leftArcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      a.radius * a.sideArcAngle := by
  apply strip_component_integral
    a.measurableSet_euclidean_leftArcTrace
    (fun _ hp => abs_le.mpr ⟨hp.2.2.1, hp.2.2.2⟩)
    a.exact_euclidean_leftArcTrace_hausdorffMeasure
  exact (mul_pos a.radius_pos a.sideArcAngle_pos).le

private theorem rightArc_integral :
    (∫ z in planeEuclideanHomeomorph '' a.rightArcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      a.radius * a.sideArcAngle := by
  apply strip_component_integral
    a.measurableSet_euclidean_rightArcTrace
    (fun _ hp => abs_le.mpr ⟨hp.2.2.1, hp.2.2.2⟩)
    a.exact_euclidean_rightArcTrace_hausdorffMeasure
  exact (mul_pos a.radius_pos a.sideArcAngle_pos).le

private theorem bottomSegment_integral :
    (∫ z in planeEuclideanHomeomorph '' a.bottomSegmentCarrier,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      a.bottomChord := by
  apply strip_component_integral
    a.measurableSet_euclidean_bottomSegmentCarrier
    (fun _ hp => by rw [hp.1]; norm_num)
    a.exact_euclidean_bottomSegmentCarrier_hausdorffMeasure
    a.bottomChord_nonneg

private theorem boundaryTrace_pairwise :
    let A := planeEuclideanHomeomorph '' a.leftArcTrace
    let B := planeEuclideanHomeomorph '' a.rightArcTrace
    let C := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace a.outerCap
    let D := planeEuclideanHomeomorph '' a.bottomSegmentCarrier
    AEDisjoint (μH[1] : Measure EuclideanPlane) A B ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) C D := by
  dsimp only
  apply pairwise_aedisjoint_of_overlap_null
  simpa only [euclideanPairwiseOverlap, pairwiseOverlap, image_union,
    Set.image_inter planeEuclideanHomeomorph.injective] using
    a.pairwiseOverlap_h1_null

/-- The Euclidean complete frontier is the union of the two strip-side arcs,
the upper exterior arc, and the possibly degenerate bottom segment. -/
theorem euclidean_frontier :
    frontier (planeEuclideanHomeomorph '' a.carrier) =
      (planeEuclideanHomeomorph '' a.leftArcTrace) ∪
        ((planeEuclideanHomeomorph '' a.rightArcTrace) ∪
          ((planeEuclideanHomeomorph ''
              OneSidedCircularCap.arcTrace a.outerCap) ∪
            (planeEuclideanHomeomorph '' a.bottomSegmentCarrier))) := by
  rw [← planeEuclideanHomeomorph.image_frontier, a.frontier_carrier]
  simp only [boundaryTrace, image_union]

/-- The component perimeter is the canonical weighted `H¹` integral over the
complete topological frontier.  This includes the exposed bottom segment and
is valid at its zero-length semicircular transition. -/
theorem weightedPerimeter_eq_modeledWeightedPerimeter :
    a.WeightedPerimeter = a.modeledWeightedPerimeter := by
  rcases a.boundaryTrace_pairwise with
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  have hAint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' a.leftArcTrace) (by
      rw [a.exact_euclidean_leftArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  have hBint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' a.rightArcTrace) (by
      rw [a.exact_euclidean_rightArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  have hCint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace a.outerCap) (by
        rw [exact_euclidean_capTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hDint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' a.bottomSegmentCarrier) (by
      rw [a.exact_euclidean_bottomSegmentCarrier_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  unfold TypeThreeAssembly.WeightedPerimeter _root_.WeightedPerimeter
    FrontierMeasure
  rw [integral_map
    planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable
    (measurable_stripDensity lam).aestronglyMeasurable]
  change (∫ z in frontier (planeEuclideanHomeomorph '' a.carrier),
    euclideanStripDensity lam z
      ∂(μH[1] : Measure EuclideanPlane)) =
    a.modeledWeightedPerimeter
  rw [a.euclidean_frontier]
  rw [integral_four_union hAB hAC hAD hBC hBD hCD
    a.measurableSet_euclidean_rightArcTrace
    (measurableSet_euclidean_capTrace a.outerCap)
    a.measurableSet_euclidean_bottomSegmentCarrier
    hAint hBint hCint hDint]
  rw [a.leftArc_integral, a.rightArc_integral,
    upper_cap_integral lam a.outerCap rfl rfl,
    a.bottomSegment_integral, modeledWeightedPerimeter,
    a.sideCap_arcLength]
  ring

/-- CMV equation (26) is the exact canonical weighted perimeter of the
coordinate carrier, not only a sum assigned to its modeled components. -/
theorem weightedPerimeter_formula :
    a.WeightedPerimeter = a.scalarWeightedPerimeter := by
  rw [a.weightedPerimeter_eq_modeledWeightedPerimeter,
    a.modeledWeightedPerimeter_formula]

/-- The density is integrable over the complete coordinate carrier. -/
theorem integrableOn_carrier :
    IntegrableOn (StripDensity lam) a.carrier := by
  rw [carrier]
  have hcore : IntegrableOn (StripDensity lam) a.coreCarrier := by
    apply stripDensity_integrableOn_of_volume_ne_top
    rw [a.volume_coreCarrier]
    exact ENNReal.ofReal_ne_top
  exact hcore.union (cap_integrableOn lam a.outerCap)

/-- The density is integrable against the canonical frontier measure.  This is
the finite-perimeter obligation for treating the coordinate carrier as a
general admissible competitor. -/
theorem integrable_frontierMeasure :
    Integrable (StripDensity lam) (FrontierMeasure a.carrier) := by
  have hfrontier :
      (μH[1] : Measure EuclideanPlane)
          (frontier (planeEuclideanHomeomorph '' a.carrier)) ≠ ⊤ := by
    rw [a.euclidean_frontier]
    apply measure_union_ne_top
    · rw [a.exact_euclidean_leftArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
    apply measure_union_ne_top
    · rw [a.exact_euclidean_rightArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
    apply measure_union_ne_top
    · rw [exact_euclidean_capTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
    · rw [a.exact_euclidean_bottomSegmentCarrier_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top
  unfold FrontierMeasure
  rw [integrable_map_measure
    (measurable_stripDensity lam).aestronglyMeasurable
    planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable]
  change IntegrableOn (euclideanStripDensity lam)
    (frontier (planeEuclideanHomeomorph '' a.carrier))
    (μH[1] : Measure EuclideanPlane)
  exact euclideanStripDensity_integrableOn_of_measure_ne_top lam hfrontier



/-- Geometric realization contract for the coordinate carrier.  Both weighted
measure formulas follow from `carrier_eq`; neither is independently selectable
data. -/
structure ModeledCompetitorRealization where
  competitor : AdmissibleCompetitor lam
  carrier_eq : competitor.carrier = a.carrier

namespace ModeledCompetitorRealization

variable {a : TypeThreeAssembly lam}
    (realization : ModeledCompetitorRealization a)

/-- The genuine admissible competitor selected by a geometric realization. -/
def asCompetitor : AdmissibleCompetitor lam := realization.competitor

theorem asCompetitor_carrier :
    realization.asCompetitor.carrier = a.carrier :=
  realization.carrier_eq

theorem asCompetitor_weightedArea :
    realization.asCompetitor.WeightedArea = a.scalarWeightedArea := by
  rw [asCompetitor, realization.competitor.weightedArea_eq_carrier,
    realization.carrier_eq]
  exact a.weightedArea_formula

theorem asCompetitor_weightedPerimeter :
    realization.asCompetitor.WeightedPerimeter =
      a.scalarWeightedPerimeter := by
  change _root_.WeightedPerimeter lam
      (FrontierMeasure realization.competitor.carrier) =
    a.scalarWeightedPerimeter
  rw [realization.carrier_eq]
  exact a.weightedPerimeter_formula

end ModeledCompetitorRealization

def HasModeledCompetitor : Prop :=
  Nonempty (ModeledCompetitorRealization a)

/-- Every regular type-(iii) coordinate carrier is a genuine admissible
finite-perimeter region; no external realization hypothesis is needed. -/
theorem hasModeledCompetitor : a.HasModeledCompetitor := by
  refine ⟨{
    competitor := .general {
      carrier := a.carrier
      measurable_carrier := a.measurableSet_carrier
      finite_weighted_area := a.integrableOn_carrier
      finite_weighted_perimeter := a.integrable_frontierMeasure }
    carrier_eq := rfl }⟩


end TypeThreeAssembly

namespace FourArcCandidate

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Observable modeled-geometry bridge.  Once the coordinate type-(iii)
carrier is realized as an admissible competitor, the scalar certificate needs
only equal weighted area and strict scalar perimeter improvement.  Minimality
then fails against that genuine competitor. -/
theorem not_isWeightedPerimeterMinimizer_of_typeThree
    (a : TypeThreeAssembly lam)
    (realization : TypeThreeAssembly.ModeledCompetitorRealization a)
    (equalArea :
      a.scalarWeightedArea = candidate.WeightedArea)
    (strictPerimeter :
      a.scalarWeightedPerimeter < candidate.WeightedPerimeter) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  intro hmin
  have harea :
      realization.asCompetitor.WeightedArea =
        candidate.WeightedArea := by
    rw [realization.asCompetitor_weightedArea, equalArea]
  have hle := hmin realization.asCompetitor harea
  rw [realization.asCompetitor_weightedPerimeter] at hle
  exact (not_le_of_gt strictPerimeter) hle

end FourArcCandidate
