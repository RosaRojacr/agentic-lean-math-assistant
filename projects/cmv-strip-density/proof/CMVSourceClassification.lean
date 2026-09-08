/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSourceBridge

/-!
# Source-located type-(iv) classification reduction

Cañete--Miranda--Vittone, Lemma 3.8 and its Step 2 (printed pages 15--17),
describe a regular type-(iv) candidate by four arcs of one radius, horizontal
symmetry, the strip incidence law, and a density-preserving horizontal
placement. Proposition 3.9 (printed page 18) supplies vertical reflective
symmetry for an isoperimetric region. Equation (27) and the paragraph following
it (printed page 19) use curvature `0 < h ≤ 1`; the regular case here is
`0 < h < 1`.

`RawFourArcCoordinates` records the five closed coordinate pieces using only the
source radius, exterior half-angle, and horizontal placement. It does not
mention `FourArcCandidate` or `CanonicalTypeIVProfile`. Strict regular Snell
data determine the existing canonical principal-angle profile. The shared
closed-Snell interface additionally allows `sourceRadius = 1`, identifies the
literal carrier with one `FourArcCandidate`, and proves that its strict branch
is the canonical normalization while its radius-one branch is the explicit
endpoint.

The remaining universal classification obligation is geometric/GMT: prove that
every source-admissible type-(iv) minimizer is almost everywhere equal to one
of these raw carriers. This module does not assume or claim that result.
-/

open Set
open Real
open MeasureTheory

noncomputable section

namespace CMVSourceClassification

/-- Raw source coordinates for a four-arc carrier. Geometry is kept separate
from density, regularity, and Snell's law. -/
structure RawFourArcCoordinates where
  sourceRadius : ℝ
  exteriorHalfAngle : ℝ
  horizontalPlacement : ℝ

namespace RawFourArcCoordinates

variable (raw : RawFourArcCoordinates)

/-- Source mean curvature `h = 1 / R`. -/
def curvature : ℝ := 1 / raw.sourceRadius

def innerRadial : ℝ := √(1 - raw.curvature ^ 2)
def outerHalfWidth : ℝ := raw.sourceRadius * sin raw.exteriorHalfAngle
def sideCenterOffset : ℝ :=
  raw.sourceRadius * (sin raw.exteriorHalfAngle - raw.innerRadial)
def leftCenter : PlanePoint := (-raw.sideCenterOffset, 0)
def rightCenter : PlanePoint := (raw.sideCenterOffset, 0)
def upperCenter : PlanePoint :=
  (0, 1 - raw.sourceRadius * cos raw.exteriorHalfAngle)
def lowerCenter : PlanePoint :=
  (0, -1 + raw.sourceRadius * cos raw.exteriorHalfAngle)

def rectangleCarrier : Set PlanePoint :=
  {p | -raw.outerHalfWidth ≤ p.1 ∧
    p.1 ≤ raw.outerHalfWidth ∧ |p.2| ≤ 1}

def leftSegmentCarrier : Set PlanePoint :=
  {p | (p.1 - raw.leftCenter.1) ^ 2 +
      (p.2 - raw.leftCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2 ∧
    p.1 ≤ -raw.outerHalfWidth ∧ |p.2| ≤ 1}

def rightSegmentCarrier : Set PlanePoint :=
  {p | (p.1 - raw.rightCenter.1) ^ 2 +
      (p.2 - raw.rightCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2 ∧
    raw.outerHalfWidth ≤ p.1 ∧ |p.2| ≤ 1}

def upperCapCarrier : Set PlanePoint :=
  {p | (p.1 - raw.upperCenter.1) ^ 2 +
      (p.2 - raw.upperCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2 ∧
    1 ≤ p.2}

def lowerCapCarrier : Set PlanePoint :=
  {p | (p.1 - raw.lowerCenter.1) ^ 2 +
      (p.2 - raw.lowerCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2 ∧
    p.2 ≤ -1}

/-- Centered union of the rectangle, two strip-side circular segments, and two
exterior circular caps. -/
def centeredCarrier : Set PlanePoint :=
  ((raw.rectangleCarrier ∪ raw.leftSegmentCarrier ∪
      raw.rightSegmentCarrier) ∪ raw.upperCapCarrier) ∪
    raw.lowerCapCarrier

/-- Arbitrary horizontal placement allowed by the source classification. -/
def carrier : Set PlanePoint :=
  horizontalTranslation raw.horizontalPlacement '' raw.centeredCarrier

/-- Closed geometric domain for a raw four-arc carrier.  It records only the
radius and minor-angle conditions needed to construct the literal candidate;
density and transverse contact laws are deliberately separate. -/
structure SatisfiesClosedGeometry : Prop where
  radius_ge_one : 1 ≤ raw.sourceRadius
  exteriorHalfAngle_pos : 0 < raw.exteriorHalfAngle
  exteriorHalfAngle_lt_pi_div_two : raw.exteriorHalfAngle < π / 2

/-- The source regularity and Snell data, kept independent of the coordinate
carrier and of all modeled-candidate declarations. -/
structure SatisfiesRegularSnell (lam : ℝ) : Prop where
  density_jump : 1 < lam
  radius_gt_one : 1 < raw.sourceRadius
  exteriorHalfAngle_pos : 0 < raw.exteriorHalfAngle
  exteriorHalfAngle_lt_pi_div_two : raw.exteriorHalfAngle < π / 2
  snell_incidence : lam * cos raw.exteriorHalfAngle = raw.curvature

/-- Source Snell data allowing the closed-curvature branch `R = 1`.
The strict structure above remains the interface for regular canonical profiles
and sectionwise reconstruction. -/
structure SatisfiesClosedSnell (lam : ℝ) : Prop where
  density_jump : 1 < lam
  radius_ge_one : 1 ≤ raw.sourceRadius
  exteriorHalfAngle_pos : 0 < raw.exteriorHalfAngle
  exteriorHalfAngle_lt_pi_div_two : raw.exteriorHalfAngle < π / 2
  snell_incidence : lam * cos raw.exteriorHalfAngle = raw.curvature

theorem SatisfiesRegularSnell.toClosed {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) : raw.SatisfiesClosedSnell lam where
  density_jump := h.density_jump
  radius_ge_one := h.radius_gt_one.le
  exteriorHalfAngle_pos := h.exteriorHalfAngle_pos
  exteriorHalfAngle_lt_pi_div_two := h.exteriorHalfAngle_lt_pi_div_two
  snell_incidence := h.snell_incidence

theorem SatisfiesRegularSnell.toClosedGeometry {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) : raw.SatisfiesClosedGeometry where
  radius_ge_one := h.radius_gt_one.le
  exteriorHalfAngle_pos := h.exteriorHalfAngle_pos
  exteriorHalfAngle_lt_pi_div_two := h.exteriorHalfAngle_lt_pi_div_two

theorem SatisfiesClosedSnell.toGeometry {lam : ℝ}
    (h : raw.SatisfiesClosedSnell lam) : raw.SatisfiesClosedGeometry where
  radius_ge_one := h.radius_ge_one
  exteriorHalfAngle_pos := h.exteriorHalfAngle_pos
  exteriorHalfAngle_lt_pi_div_two := h.exteriorHalfAngle_lt_pi_div_two

theorem SatisfiesClosedSnell.toRegular {lam : ℝ}
    (h : raw.SatisfiesClosedSnell lam) (hradius : 1 < raw.sourceRadius) :
    raw.SatisfiesRegularSnell lam where
  density_jump := h.density_jump
  radius_gt_one := hradius
  exteriorHalfAngle_pos := h.exteriorHalfAngle_pos
  exteriorHalfAngle_lt_pi_div_two := h.exteriorHalfAngle_lt_pi_div_two
  snell_incidence := h.snell_incidence

private theorem sourceRadius_pos {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) : 0 < raw.sourceRadius :=
  lt_trans zero_lt_one h.radius_gt_one

private theorem lam_pos {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) : 0 < lam :=
  lt_trans zero_lt_one h.density_jump

/-- The source radius and strict regularity produce the canonical curvature
parameter. -/
def toCanonicalProfile {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) : CanonicalTypeIVProfile lam where
  h := raw.curvature
  density_jump := h.density_jump
  h_pos := one_div_pos.mpr (raw.sourceRadius_pos h)
  h_lt_one := (div_lt_one (raw.sourceRadius_pos h)).2 h.radius_gt_one

@[simp] theorem toCanonicalProfile_radius {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    (raw.toCanonicalProfile h).radius = raw.sourceRadius := by
  simp [toCanonicalProfile, CanonicalTypeIVProfile.radius, curvature]

/-- Snell's law and the minor-angle branch force the canonical principal
exterior angle. -/
theorem exteriorHalfAngle_eq_profile_alpha {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    raw.exteriorHalfAngle = (raw.toCanonicalProfile h).alpha := by
  symm
  apply Real.arccos_eq_of_eq_cos h.exteriorHalfAngle_pos.le
    (le_trans h.exteriorHalfAngle_lt_pi_div_two.le
      (by linarith [Real.pi_pos]))
  change raw.curvature / lam = cos raw.exteriorHalfAngle
  exact (div_eq_iff (ne_of_gt (raw.lam_pos h))).2 (by
    simpa [mul_comm] using h.snell_incidence.symm)

/-- Literal equality for the independently defined centered source carrier. -/
theorem centeredCarrier_eq_profile_carrier {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    raw.centeredCarrier = (raw.toCanonicalProfile h).carrier := by
  rw [centeredCarrier, CanonicalTypeIVProfile.carrier]
  rw [rectangleCarrier, leftSegmentCarrier, rightSegmentCarrier,
    upperCapCarrier, lowerCapCarrier]
  rw [CanonicalTypeIVProfile.rectangleCarrier,
    CanonicalTypeIVProfile.leftSegmentCarrier,
    CanonicalTypeIVProfile.rightSegmentCarrier,
    CanonicalTypeIVProfile.upperCapCarrier,
    CanonicalTypeIVProfile.lowerCapCarrier]
  rw [leftCenter, rightCenter, upperCenter, lowerCenter,
    sideCenterOffset, outerHalfWidth, innerRadial]
  rw [CanonicalTypeIVProfile.leftCenter,
    CanonicalTypeIVProfile.rightCenter,
    CanonicalTypeIVProfile.upperCenter,
    CanonicalTypeIVProfile.lowerCenter,
    CanonicalTypeIVProfile.sideCenterOffset,
    CanonicalTypeIVProfile.outerHalfWidth,
    CanonicalTypeIVProfile.innerRadial]
  rw [raw.toCanonicalProfile_radius h,
    ← raw.exteriorHalfAngle_eq_profile_alpha h]
  rfl

/-- Arbitrary placement is exactly a horizontal translate of the canonical
profile. -/
theorem carrier_eq_horizontalTranslation_profile {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    raw.carrier = horizontalTranslation raw.horizontalPlacement ''
      (raw.toCanonicalProfile h).carrier := by
  rw [carrier, raw.centeredCarrier_eq_profile_carrier h]

/-- Exact classification of the independently defined source-coordinate
carrier. -/
theorem horizontallyCongruent_profile {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    HorizontallyCongruent raw.carrier (raw.toCanonicalProfile h).carrier :=
  ⟨raw.horizontalPlacement,
    raw.carrier_eq_horizontalTranslation_profile h⟩

/-- Representative-level classification used by the relaxed perimeter. -/
theorem almostEverywhereHorizontallyCongruent_profile {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    AlmostEverywhereHorizontallyCongruent
      raw.carrier (raw.toCanonicalProfile h).carrier :=
  almostEverywhereHorizontallyCongruent_of_horizontallyCongruent
    (raw.horizontallyCongruent_profile h)

/-- Once the unresolved GMT classification identifies a source representative
almost everywhere with the raw coordinate carrier, no further geometric
normalization premise is needed. -/
theorem almostEverywhereHorizontallyCongruent_profile_of_ae
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (h : raw.SatisfiesRegularSnell lam)
    (hsource : sourceCarrier =ᵐ[volume] raw.carrier) :
    AlmostEverywhereHorizontallyCongruent
      sourceCarrier (raw.toCanonicalProfile h).carrier := by
  refine ⟨raw.horizontalPlacement, ?_⟩
  rw [← raw.carrier_eq_horizontalTranslation_profile h]
  exact hsource

/-- The complete modeled output of the source coordinate reduction. -/
theorem exists_profile_and_candidate {lam : ℝ}
    (h : raw.SatisfiesRegularSnell lam) :
    ∃ profile : CanonicalTypeIVProfile lam,
      HorizontallyCongruent raw.carrier profile.carrier ∧
        profile.toCandidate.SatisfiesCMVTypeIVHypotheses :=
  ⟨raw.toCanonicalProfile h, raw.horizontallyCongruent_profile h,
    (raw.toCanonicalProfile h).toCandidate_satisfiesCMVTypeIVHypotheses⟩

private theorem sourceRadius_pos_geometry
    (h : raw.SatisfiesClosedGeometry) : 0 < raw.sourceRadius :=
  lt_of_lt_of_le zero_lt_one h.radius_ge_one

private theorem lam_pos_closed {lam : ℝ}
    (h : raw.SatisfiesClosedSnell lam) : 0 < lam :=
  lt_trans zero_lt_one h.density_jump

/-- The principal exterior angle is forced on both the regular and endpoint
branches. -/
theorem exteriorHalfAngle_eq_arccos_curvature {lam : ℝ}
    (h : raw.SatisfiesClosedSnell lam) :
    raw.exteriorHalfAngle = arccos (raw.curvature / lam) := by
  symm
  apply Real.arccos_eq_of_eq_cos h.exteriorHalfAngle_pos.le
    (le_trans h.exteriorHalfAngle_lt_pi_div_two.le
      (by linarith [Real.pi_pos]))
  exact (div_eq_iff (ne_of_gt (raw.lam_pos_closed h))).2 (by
    simpa [mul_comm] using h.snell_incidence.symm)

/-- Candidate normalization shared by `R > 1` and the closed branch `R = 1`.
Only the closed geometric domain is needed; density and Snell incidence are not
part of this construction. -/
def toFourArcCandidate {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) : FourArcCandidate lam where
  h := raw.curvature
  alpha := raw.exteriorHalfAngle
  h_pos := one_div_pos.mpr (raw.sourceRadius_pos_geometry h)
  h_le_one := by
    change 1 / raw.sourceRadius ≤ 1
    exact (div_le_iff₀ (raw.sourceRadius_pos_geometry h)).2 (by
      simpa using h.radius_ge_one)
  alpha_pos := h.exteriorHalfAngle_pos
  alpha_lt_pi_div_two := h.exteriorHalfAngle_lt_pi_div_two

theorem toFourArcCandidate_satisfiesCMVTypeIVHypotheses {lam : ℝ}
    (h : raw.SatisfiesClosedSnell lam) :
    (raw.toFourArcCandidate (lam := lam) h.toGeometry)
      |>.SatisfiesCMVTypeIVHypotheses where
  density_jump := h.density_jump
  snell_incidence := h.snell_incidence

private theorem closedCandidate_chord_half {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.chord / 2 =
      raw.outerHalfWidth := by
  simp only [FourArcCandidate.stripCore, FourArcCandidate.capChord,
    toFourArcCandidate, outerHalfWidth, curvature]
  field_simp [ne_of_gt (raw.sourceRadius_pos_geometry h)]

private theorem closedCandidate_neg_chord_half {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    -(raw.toFourArcCandidate (lam := lam) h).stripCore.chord / 2 =
      -raw.outerHalfWidth := by
  rw [show -(raw.toFourArcCandidate (lam := lam) h).stripCore.chord / 2 =
      -((raw.toFourArcCandidate (lam := lam) h).stripCore.chord / 2) by ring,
    raw.closedCandidate_chord_half h]

private theorem closedCandidate_core_radius {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.radius =
      raw.sourceRadius := by
  unfold FourArcCandidate.stripCore StripCore.radius toFourArcCandidate curvature
  field_simp [ne_of_gt (raw.sourceRadius_pos_geometry h)]

private theorem closedCandidate_core_cos_sideAngle {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    cos (raw.toFourArcCandidate (lam := lam) h).stripCore.sideAngle =
      raw.innerRadial := by
  rw [StripCore.cos_sideAngle]
  rfl

private theorem closedCandidate_leftCenter {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.leftCenterX =
      raw.leftCenter.1 := by
  rw [StripCore.leftCenterX,
    show -(raw.toFourArcCandidate (lam := lam) h).stripCore.chord / 2 =
      -((raw.toFourArcCandidate (lam := lam) h).stripCore.chord / 2) by ring,
    raw.closedCandidate_chord_half h, raw.closedCandidate_core_radius h,
    raw.closedCandidate_core_cos_sideAngle h]
  simp only [leftCenter, sideCenterOffset, outerHalfWidth]
  ring

private theorem closedCandidate_rightCenter {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.rightCenterX =
      raw.rightCenter.1 := by
  rw [StripCore.rightCenterX, raw.closedCandidate_chord_half h,
    raw.closedCandidate_core_radius h,
    raw.closedCandidate_core_cos_sideAngle h]
  simp only [rightCenter, sideCenterOffset, outerHalfWidth]
  ring

private theorem closedCandidate_upperCap_radius {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).assembly.upperCap.radius =
      raw.sourceRadius := by
  rw [((raw.toFourArcCandidate (lam := lam) h).four_arcs_common_radius).1,
    raw.closedCandidate_core_radius h]

private theorem closedCandidate_lowerCap_radius {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).assembly.lowerCap.radius =
      raw.sourceRadius := by
  rw [((raw.toFourArcCandidate (lam := lam) h).four_arcs_common_radius).2,
    raw.closedCandidate_core_radius h]

private theorem closedCandidate_upperCenter {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).assembly.upperCap.center =
      raw.upperCenter := by
  change (0, 1 -
    (raw.toFourArcCandidate (lam := lam) h).assembly.upperCap.radius *
      cos raw.exteriorHalfAngle) = raw.upperCenter
  rw [raw.closedCandidate_upperCap_radius h]
  rfl

private theorem closedCandidate_lowerCenter {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).assembly.lowerCap.center =
      raw.lowerCenter := by
  change (0, -1 +
    (raw.toFourArcCandidate (lam := lam) h).assembly.lowerCap.radius *
      cos raw.exteriorHalfAngle) = raw.lowerCenter
  rw [raw.closedCandidate_lowerCap_radius h]
  rfl

private theorem closedCandidate_rectangleCarrier {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.rectangleCarrier =
      raw.rectangleCarrier := by
  ext p
  simp only [StripCore.rectangleCarrier, rectangleCarrier, mem_ofPred_eq]
  rw [raw.closedCandidate_chord_half h,
    raw.closedCandidate_neg_chord_half h]

private theorem closedCandidate_leftSegmentCarrier {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.leftCapCarrier =
      raw.leftSegmentCarrier := by
  ext p
  simp only [StripCore.leftCapCarrier, leftSegmentCarrier, mem_ofPred_eq]
  rw [raw.closedCandidate_leftCenter h, raw.closedCandidate_core_radius h,
    raw.closedCandidate_neg_chord_half h]
  simp only [leftCenter, sub_zero]

private theorem closedCandidate_rightSegmentCarrier {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).stripCore.rightCapCarrier =
      raw.rightSegmentCarrier := by
  ext p
  simp only [StripCore.rightCapCarrier, rightSegmentCarrier, mem_ofPred_eq]
  rw [raw.closedCandidate_rightCenter h, raw.closedCandidate_core_radius h,
    raw.closedCandidate_chord_half h]
  simp only [rightCenter, sub_zero]

private theorem closedCandidate_upperCapCarrier {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).assembly.upperCap.carrier =
      raw.upperCapCarrier := by
  ext p
  change
    ((raw.toFourArcCandidate (lam := lam) h).assembly.upperCap.radiusSquaredAt p ≤
        (raw.toFourArcCandidate (lam := lam) h).assembly.upperCap.radius ^ 2 ∧
      1 ≤ p.2) ↔
    ((p.1 - raw.upperCenter.1) ^ 2 +
      (p.2 - raw.upperCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2 ∧ 1 ≤ p.2)
  rw [OneSidedCircularCap.radiusSquaredAt,
    raw.closedCandidate_upperCenter h, raw.closedCandidate_upperCap_radius h]

private theorem closedCandidate_lowerCapCarrier {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    (raw.toFourArcCandidate (lam := lam) h).assembly.lowerCap.carrier =
      raw.lowerCapCarrier := by
  ext p
  change
    ((raw.toFourArcCandidate (lam := lam) h).assembly.lowerCap.radiusSquaredAt p ≤
        (raw.toFourArcCandidate (lam := lam) h).assembly.lowerCap.radius ^ 2 ∧
      p.2 ≤ -1) ↔
    ((p.1 - raw.lowerCenter.1) ^ 2 +
      (p.2 - raw.lowerCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2 ∧ p.2 ≤ -1)
  rw [OneSidedCircularCap.radiusSquaredAt,
    raw.closedCandidate_lowerCenter h, raw.closedCandidate_lowerCap_radius h]

/-- Literal carrier identification shared by the strict regular branch and the
source-radius-one endpoint.  No density or contact law is used. -/
theorem centeredCarrier_eq_candidate_assembly {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    raw.centeredCarrier =
      (raw.toFourArcCandidate (lam := lam) h).assembly.carrier := by
  rw [FourArcAssembly.carrier, StripCore.carrier,
    FourArcCandidate.assembly_core,
    raw.closedCandidate_rectangleCarrier h,
    raw.closedCandidate_leftSegmentCarrier h,
    raw.closedCandidate_rightSegmentCarrier h,
    raw.closedCandidate_upperCapCarrier h,
    raw.closedCandidate_lowerCapCarrier h]
  rfl

theorem carrier_eq_horizontalTranslation_candidate {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    raw.carrier = horizontalTranslation raw.horizontalPlacement ''
      (raw.toFourArcCandidate (lam := lam) h).assembly.carrier := by
  rw [carrier, raw.centeredCarrier_eq_candidate_assembly h]

theorem horizontallyCongruent_candidate {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    HorizontallyCongruent raw.carrier
      (raw.toFourArcCandidate (lam := lam) h).assembly.carrier :=
  ⟨raw.horizontalPlacement,
    raw.carrier_eq_horizontalTranslation_candidate h⟩

theorem almostEverywhereHorizontallyCongruent_candidate {lam : ℝ}
    (h : raw.SatisfiesClosedGeometry) :
    AlmostEverywhereHorizontallyCongruent raw.carrier
      (raw.toFourArcCandidate (lam := lam) h).assembly.carrier :=
  almostEverywhereHorizontallyCongruent_of_horizontallyCongruent
    (raw.horizontallyCongruent_candidate h)

theorem almostEverywhereHorizontallyCongruent_candidate_of_ae
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (h : raw.SatisfiesClosedGeometry)
    (hsource : sourceCarrier =ᵐ[volume] raw.carrier) :
    AlmostEverywhereHorizontallyCongruent sourceCarrier
      (raw.toFourArcCandidate (lam := lam) h).assembly.carrier := by
  refine ⟨raw.horizontalPlacement, ?_⟩
  rw [← raw.carrier_eq_horizontalTranslation_candidate h]
  exact hsource

private theorem fourArcCandidate_eq_of_h_alpha_eq
    {lam : ℝ} {left right : FourArcCandidate lam}
    (hh : left.h = right.h) (halpha : left.alpha = right.alpha) :
    left = right := by
  cases left
  cases right
  simp_all

/-- On the radius-one branch the shared candidate is exactly the explicit
closed-curvature endpoint. -/
theorem toFourArcCandidate_eq_endpoint_of_sourceRadius_eq_one
    {lam : ℝ} (h : raw.SatisfiesClosedSnell lam)
    (hradius : raw.sourceRadius = 1) :
    raw.toFourArcCandidate h.toGeometry =
      FourArcCandidate.endpoint h.density_jump := by
  apply fourArcCandidate_eq_of_h_alpha_eq
  · simp [toFourArcCandidate, curvature, hradius]
  · simp only [toFourArcCandidate, FourArcCandidate.endpoint]
    rw [raw.exteriorHalfAngle_eq_arccos_curvature h, curvature, hradius]
    norm_num

/-- On `R > 1` the shared candidate agrees exactly with the pre-existing
strict canonical normalization. -/
theorem toFourArcCandidate_eq_regular_toCandidate
    {lam : ℝ} (h : raw.SatisfiesClosedSnell lam)
    (hradius : 1 < raw.sourceRadius) :
    raw.toFourArcCandidate h.toGeometry =
      (raw.toCanonicalProfile
        (SatisfiesClosedSnell.toRegular raw h hradius)).toCandidate := by
  apply fourArcCandidate_eq_of_h_alpha_eq
  · rfl
  · exact raw.exteriorHalfAngle_eq_profile_alpha
      (SatisfiesClosedSnell.toRegular raw h hradius)

end RawFourArcCoordinates

set_option maxHeartbeats 800000 in
-- The repeated nonlinear square-root cancellations exceed the default budget.
/-- Scalar form of Cañete--Miranda--Vittone Lemma 3.8, Step 2, equations
(24)--(25) and the vertical-axis center alignment. Here `a, b` are
`sin α, sin β`, while `c, d` are `sin γ, sin δ`. The nonnegative square roots
are the principal cosine branches. The hypotheses force horizontal symmetry
and the source curvature relation, rather than assuming either. -/
theorem figure4_scalar_reduction
    {lam R a b c d : ℝ}
    (hlam : 1 < lam) (hR : 0 < R)
    (ha_lo : -1 ≤ a) (ha_hi : a ≤ 1)
    (hb_lo : -1 ≤ b) (hb_hi : b ≤ 1)
    (hc_lo : -1 ≤ c) (hc_hi : c ≤ 1)
    (hd_lo : -1 ≤ d) (hd_hi : d ≤ 1)
    (hsnell_a : a = lam * c) (hsnell_b : b = lam * d)
    (hheight : R * (a + b) = 2)
    (halign :
      √(1 - a ^ 2) - √(1 - c ^ 2) =
        √(1 - b ^ 2) - √(1 - d ^ 2)) :
    a = b ∧ a = 1 / R ∧ b = 1 / R := by
  have hlam0 : 0 < lam := by linarith
  have hlam_sq : 1 < lam ^ 2 := by nlinarith
  have ha_sq : a ^ 2 ≤ 1 := by nlinarith
  have hb_sq : b ^ 2 ≤ 1 := by nlinarith
  have hc_sq : c ^ 2 ≤ 1 := by nlinarith
  have hd_sq : d ^ 2 ≤ 1 := by nlinarith
  have hc_sq_lt : c ^ 2 < 1 := by
    rw [hsnell_a] at ha_sq
    nlinarith [sq_nonneg c]
  have hd_sq_lt : d ^ 2 < 1 := by
    rw [hsnell_b] at hb_sq
    nlinarith [sq_nonneg d]
  let x := √(1 - a ^ 2)
  let y := √(1 - b ^ 2)
  let u := √(1 - c ^ 2)
  let v := √(1 - d ^ 2)
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hu_pos : 0 < u := Real.sqrt_pos.2 (by linarith)
  have hv_pos : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hx_sq : x ^ 2 = 1 - a ^ 2 := by
    dsimp [x]
    exact Real.sq_sqrt (by linarith)
  have hy_sq : y ^ 2 = 1 - b ^ 2 := by
    dsimp [y]
    exact Real.sq_sqrt (by linarith)
  have hu_sq : u ^ 2 = 1 - c ^ 2 := by
    dsimp [u]
    exact Real.sq_sqrt (by linarith)
  have hv_sq : v ^ 2 = 1 - d ^ 2 := by
    dsimp [v]
    exact Real.sq_sqrt (by linarith)
  have hx_le_u : x ≤ u := by
    apply (Real.sqrt_le_sqrt_iff (by linarith)).2
    rw [hsnell_a]
    nlinarith [sq_nonneg c]
  have hy_le_v : y ≤ v := by
    apply (Real.sqrt_le_sqrt_iff (by linarith)).2
    rw [hsnell_b]
    nlinarith [sq_nonneg d]
  have halign' : x - u = y - v := by
    simpa [x, y, u, v] using halign
  have hsquares : x ^ 2 - y ^ 2 =
      lam ^ 2 * (u ^ 2 - v ^ 2) := by
    rw [hx_sq, hy_sq, hu_sq, hv_sq, hsnell_a, hsnell_b]
    ring
  have hxy : x = y := by
    by_contra hne
    have hsum_le : x + y ≤ u + v :=
      add_le_add hx_le_u hy_le_v
    have huv_pos : 0 < u + v := add_pos hu_pos hv_pos
    have hscaled : 0 < (lam ^ 2 - 1) * (u + v) :=
      mul_pos (sub_pos.mpr hlam_sq) huv_pos
    have hsum_lt : x + y < lam ^ 2 * (u + v) := by
      nlinarith
    have hfactor : (x - y) * (x + y) =
        lam ^ 2 * ((u - v) * (u + v)) := by
      calc
        (x - y) * (x + y) = x ^ 2 - y ^ 2 := by ring
        _ = lam ^ 2 * (u ^ 2 - v ^ 2) := hsquares
        _ = lam ^ 2 * ((u - v) * (u + v)) := by ring
    have hdiff : x - y = u - v := by linarith [halign']
    have hcanceled :
        (x - y) * (x + y) =
          (x - y) * (lam ^ 2 * (u + v)) := by
      calc
        (x - y) * (x + y) =
            lam ^ 2 * ((u - v) * (u + v)) := hfactor
        _ = (x - y) * (lam ^ 2 * (u + v)) := by
          rw [← hdiff]
          ring
    have hsum_eq : x + y = lam ^ 2 * (u + v) :=
      mul_left_cancel₀ (sub_ne_zero.mpr hne) hcanceled
    exact (ne_of_lt hsum_lt hsum_eq).elim
  have hab_sq : a ^ 2 = b ^ 2 := by nlinarith [hx_sq, hy_sq]
  have hab_sum_ne : a + b ≠ 0 := by
    intro hab_sum
    rw [hab_sum, mul_zero] at hheight
    norm_num at hheight
  have hab : a = b := by
    have hprod : (a - b) * (a + b) = 0 := by
      nlinarith [hab_sq]
    rcases mul_eq_zero.mp hprod with hab_diff | hab_sum
    · exact sub_eq_zero.mp hab_diff
    · exact (hab_sum_ne hab_sum).elim
  have ha_inv : a = 1 / R := by
    apply (eq_div_iff (ne_of_gt hR)).2
    rw [hab] at hheight
    nlinarith [hheight]
  exact ⟨hab, ha_inv, hab ▸ ha_inv⟩

end CMVSourceClassification
