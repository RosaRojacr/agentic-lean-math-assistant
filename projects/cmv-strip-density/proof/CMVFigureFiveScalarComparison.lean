/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFiveSourceGeometry
import CMVFigureFourBilateralIncidence
import CMVFigureFiveAngular

/-!
# Scalar accounting for CMV Figure 5

The independent Figure-5 source geometry already forces common radius one.  This
module computes the resulting cap angle, chord, area, and boundary excess for
each of its one or two capped interfaces.  It then proves that the component
model lies above the closed type-(iii) endpoint area and perimeter support line.

These are component identities for the literal traces stored by `SourceGeometry`.
They do not identify the actual source carrier with a component carrier and do
not assert a relaxed-perimeter lower bound.
-/

open Set Real MeasureTheory

noncomputable section

namespace CMVFigureThree.DegenerateHorizontalSegment

/-- Euclidean length of a possibly degenerate horizontal segment. -/
def length (s : DegenerateHorizontalSegment) : ℝ := s.rightX - s.leftX

lemma length_nonneg (s : DegenerateHorizontalSegment) : 0 ≤ s.length :=
  sub_nonneg.mpr s.left_le_right

end CMVFigureThree.DegenerateHorizontalSegment

namespace CMVFigureFive

/-- A possibly degenerate horizontal interface segment has planar measure
zero. -/
theorem volume_degenerateHorizontalSegment
    (s : CMVFigureThree.DegenerateHorizontalSegment) :
    volume s.carrier = 0 := by
  apply measure_mono_null
    (t := {p : PlanePoint | p.2 = s.baseY})
  · intro p hp
    exact hp.1
  · exact volume_horizontalLine s.baseY

/-- Every literal cap arc is planar-null. -/
theorem volume_capArcTrace (c : OneSidedCircularCap) :
    volume c.arcTrace = 0 := by
  apply measure_mono_null
    (t := {p : PlanePoint |
      CMVFigureFour.circleValue c.center c.radius p = 0})
  · intro p hp
    change CMVFigureFour.circleValue c.center c.radius p = 0
    have hcircle := hp.1
    unfold CMVFigureFour.circleValue OneSidedCircularCap.radiusSquaredAt at *
    nlinarith
  · exact CMVFigureFour.volume_circleValue_eq_zero _ _

/-- Every literal strip-side trace is planar-null. -/
theorem volume_stripCircleTrace
    (branch : CMVFigureFour.HorizontalCircleBranch)
    (center : PlanePoint) (radius : ℝ) :
    volume (CMVFigureFour.stripCircleTrace branch center radius) = 0 := by
  apply measure_mono_null
    (t := {p : PlanePoint |
      CMVFigureFour.circleValue center radius p = 0})
  · intro p hp
    exact hp.1
  · exact CMVFigureFour.volume_circleValue_eq_zero _ _

namespace CappedInterface

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

/-- The positive signed contact law selects the principal Figure-5 cap angle. -/
theorem theta_eq_endpointAngle
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) :
    b.cap.theta = endpointAngle lam := by
  have hlam_ne : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  have hcos : cos b.cap.theta = 1 / lam := by
    apply (eq_div_iff hlam_ne).2
    simpa only [mul_comm] using b.signed_contact_law
  calc
    b.cap.theta = arccos (cos b.cap.theta) :=
      (Real.arccos_cos b.cap.theta_pos.le b.cap.theta_lt_pi.le).symm
    _ = endpointAngle lam := by rw [hcos]; rfl

/-- At source radius one, every Figure-5 cap has the endpoint chord. -/
theorem chord_eq_two_mul_sin_endpointAngle
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.cap.chord = 2 * sin (endpointAngle lam) := by
  have hcapRadius : b.cap.radius = 1 := b.cap_radius.trans hRadius
  have h := b.cap.radius_mul_sin
  rw [hcapRadius, b.theta_eq_endpointAngle hlam] at h
  linarith

/-- At source radius one, the cap arc length is twice its principal half-angle. -/
theorem arcLength_eq_two_mul_endpointAngle
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.cap.arcLength = 2 * endpointAngle lam := by
  rw [cap_arcLength_eq_two_radius_theta]
  rw [show b.cap.radius = 1 from b.cap_radius.trans hRadius,
    b.theta_eq_endpointAngle hlam]
  ring

/-- Exact radius-one cap area in principal-angle coordinates. -/
theorem euclideanArea_eq_endpointAngle_sub
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.cap.euclideanArea =
      endpointAngle lam - sin (endpointAngle lam) * cos (endpointAngle lam) := by
  have hsin : 0 < sin (endpointAngle lam) :=
    sin_pos_of_pos_of_lt_pi (endpointAngle_mem hlam).1
      ((endpointAngle_mem hlam).2.trans (half_lt_self Real.pi_pos))
  rw [OneSidedCircularCap.euclideanArea, area,
    b.chord_eq_two_mul_sin_endpointAngle hlam hRadius,
    b.theta_eq_endpointAngle hlam]
  field_simp [ne_of_gt hsin]
  ring

/-- The density-weighted area of one source cap is the endpoint support gap. -/
theorem weightedAreaContribution_eq_endpointGap
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    lam * b.cap.euclideanArea = endpointGap lam := by
  rw [b.euclideanArea_eq_endpointAngle_sub hlam hRadius]
  calc
    lam * (endpointAngle lam - sin (endpointAngle lam) *
        cos (endpointAngle lam)) =
        lam * endpointAngle lam - sin (endpointAngle lam) *
          (lam * cos (endpointAngle lam)) := by ring
    _ = lam * endpointAngle lam - sin (endpointAngle lam) := by
      rw [← b.theta_eq_endpointAngle hlam, b.signed_contact_law]
      ring
    _ = endpointGap lam := rfl

/-- Replacing the cap chord by its exterior weighted arc adds twice the endpoint
support gap to boundary cost. -/
theorem weightedArc_sub_chord_eq_two_mul_endpointGap
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    lam * b.cap.arcLength - b.cap.chord = 2 * endpointGap lam := by
  rw [b.arcLength_eq_two_mul_endpointAngle hlam hRadius,
    b.chord_eq_two_mul_sin_endpointAngle hlam hRadius]
  unfold endpointGap
  ring

/-- The cap chord is contained in the full interval between strip tangencies. -/
theorem chord_le_tangent_span
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side) :
    b.cap.chord ≤ rightTangentX - leftTangentX := by
  have hbetween := b.cap_endpoints_between
  simp only [OneSidedCircularCap.leftEndpoint,
    OneSidedCircularCap.rightEndpoint] at hbetween
  linarith

end CappedInterface

namespace InterfaceBoundary

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

/-- Real-valued cap indicator, used only for the finite one-or-two case split. -/
def capIndicator
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : ℝ :=
  match b with
  | .exposed _ => 0
  | .capped _ => 1

/-- The finite cap indicator is nonnegative. -/
theorem capIndicator_nonneg
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    0 ≤ b.capIndicator := by
  cases b <;> norm_num [capIndicator]

/-- The indicator records exactly the exposed/capped dichotomy. -/
theorem capIndicator_eq_zero_or_one
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    b.capIndicator = 0 ∨ b.capIndicator = 1 := by
  cases b <;> simp [capIndicator]

/-- Density-weighted area contributed outside the strip by this interface. -/
def weightedAreaContribution
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : ℝ :=
  match b with
  | .exposed _ => 0
  | .capped data => lam * data.cap.euclideanArea

/-- Weighted cost of the complete trace on this density interface. -/
def weightedBoundaryCost
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : ℝ :=
  match b with
  | .exposed data => data.segment.length
  | .capped data =>
      data.leftSegment.length + lam * data.cap.arcLength +
        data.rightSegment.length

/-- A capped interface contributes exactly one endpoint gap to weighted area. -/
theorem weightedAreaContribution_eq
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.weightedAreaContribution = b.capIndicator * endpointGap lam := by
  cases b with
  | exposed data => simp [weightedAreaContribution, capIndicator]
  | capped data =>
      simp only [weightedAreaContribution, capIndicator, one_mul]
      exact data.weightedAreaContribution_eq_endpointGap hlam hRadius

/-- The complete interface cost is its full tangency span plus twice the endpoint
gap when a cap replaces part of the flat interface. -/
theorem weightedBoundaryCost_eq
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1) :
    b.weightedBoundaryCost = rightTangentX - leftTangentX +
      2 * b.capIndicator * endpointGap lam := by
  cases b with
  | exposed data =>
      simp only [weightedBoundaryCost, capIndicator, mul_zero, zero_mul, add_zero]
      unfold CMVFigureThree.DegenerateHorizontalSegment.length
      rw [data.segment_starts_at_left_tangency,
        data.segment_ends_at_right_tangency]
  | capped data =>
      simp only [weightedBoundaryCost, capIndicator, mul_one]
      unfold CMVFigureThree.DegenerateHorizontalSegment.length
      rw [data.left_segment_starts_at_tangency,
        data.left_segment_ends_at_cap,
        data.right_segment_starts_at_cap,
        data.right_segment_ends_at_tangency]
      have hgap := data.weightedArc_sub_chord_eq_two_mul_endpointGap
        hlam hRadius
      simp only [OneSidedCircularCap.leftEndpoint,
        OneSidedCircularCap.rightEndpoint] at hgap ⊢
      linarith

/-- If this boundary is capped, its endpoint chord fits inside the tangency span. -/
theorem endpointChord_le_span_of_isCapped
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) (hRadius : sourceRadius = 1)
    (hcapped : b.IsCapped) :
    2 * sin (endpointAngle lam) ≤ rightTangentX - leftTangentX := by
  cases b with
  | exposed data => simp [IsCapped] at hcapped
  | capped data =>
      rw [← data.chord_eq_two_mul_sin_endpointAngle hlam hRadius]
      exact data.chord_le_tangent_span

/-- The complete trace of either interface is planar-null. -/
theorem volume_trace
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    volume b.trace = 0 := by
  cases b with
  | exposed data =>
      simpa [trace] using volume_degenerateHorizontalSegment data.segment
  | capped data =>
      simp only [trace, CappedInterface.trace]
      exact measure_union_null
        (volume_degenerateHorizontalSegment data.leftSegment)
        (measure_union_null (volume_capArcTrace data.cap)
          (volume_degenerateHorizontalSegment data.rightSegment))

end InterfaceBoundary

namespace SourceGeometry

variable {lam : ℝ} (g : SourceGeometry lam)

/-- Number of capped interfaces, represented in `ℝ`; the source signature makes
this value either one or two. -/
def capCount : ℝ :=
  g.upperBoundary.capIndicator + g.lowerBoundary.capIndicator

/-- Component weighted area: radius-one stadium area plus exterior cap areas. -/
def modeledWeightedArea : ℝ :=
  Real.pi + 2 * g.width +
    g.upperBoundary.weightedAreaContribution +
      g.lowerBoundary.weightedAreaContribution

/-- Component weighted boundary cost: the two unit semicircles plus both
interface traces. -/
def modeledWeightedPerimeter : ℝ :=
  2 * Real.pi + g.upperBoundary.weightedBoundaryCost +
    g.lowerBoundary.weightedBoundaryCost

/-- The literal complete frontier in every frozen Figure-5 source geometry has
planar measure zero. -/
theorem volume_frontier_representative :
    volume (frontier g.representative) = 0 := by
  rw [g.frontier_eq_components]
  exact measure_union_null
    (volume_stripCircleTrace .left g.leftStripCenter g.sourceRadius)
    (measure_union_null
      (volume_stripCircleTrace .right g.rightStripCenter g.sourceRadius)
      (measure_union_null g.upperBoundary.volume_trace
        g.lowerBoundary.volume_trace))

/-- Closing the bounded open representative changes it only on its null
complete frontier. -/
theorem representative_ae_closure :
    g.representative =ᵐ[volume] closure g.representative :=
  (closure_ae_eq_of_null_frontier g.volume_frontier_representative).symm

/-- The actual source carrier is almost everywhere the closed topological
carrier determined by its frozen representative.  This does not yet identify
that closure with the explicit segmented component model. -/
theorem sourceCarrier_ae_closure_representative :
    g.sourceCarrier =ᵐ[volume] closure g.representative :=
  g.sourceRepresentative.source_ae_representative.trans
    g.representative_ae_closure

/-- Weighted area may be computed on the closed representative without any
pointwise carrier equality. -/
theorem weightedArea_sourceCarrier_eq_closure :
    _root_.WeightedArea lam g.sourceCarrier =
      _root_.WeightedArea lam (closure g.representative) :=
  CMVRelaxation.weightedArea_congr_ae lam
    g.sourceCarrier_ae_closure_representative

/-- The extended relaxed perimeter is likewise invariant under passage to the
closed representative. -/
theorem relaxedPerimeter_sourceCarrier_eq_closure :
    CMVRelaxation.relaxedPerimeter lam g.sourceCarrier =
      CMVRelaxation.relaxedPerimeter lam (closure g.representative) :=
  CMVRelaxation.relaxedPerimeter_congr_ae lam
    g.sourceCarrier_ae_closure_representative

/-- Figure 5 has at least one capped interface. -/
theorem one_le_capCount : 1 ≤ g.capCount := by
  rcases g.has_exterior_cap with hupper | hlower
  · cases h : g.upperBoundary with
    | exposed data => simp [InterfaceBoundary.IsCapped, h] at hupper
    | capped data =>
        rw [capCount, h]
        change 1 ≤ 1 + g.lowerBoundary.capIndicator
        linarith [g.lowerBoundary.capIndicator_nonneg]
  · cases h : g.lowerBoundary with
    | exposed data => simp [InterfaceBoundary.IsCapped, h] at hlower
    | capped data =>
        rw [capCount, h]
        change 1 ≤ g.upperBoundary.capIndicator + 1
        linarith [g.upperBoundary.capIndicator_nonneg]

/-- The source signature's cap count is exactly one or two. -/
theorem capCount_eq_one_or_two : g.capCount = 1 ∨ g.capCount = 2 := by
  rcases g.upperBoundary.capIndicator_eq_zero_or_one with hupper | hupper <;>
    rcases g.lowerBoundary.capIndicator_eq_zero_or_one with hlower | hlower
  · exfalso
    have hcount := g.one_le_capCount
    rw [capCount, hupper, hlower] at hcount
    norm_num at hcount
  · left
    rw [capCount, hupper, hlower]
    norm_num
  · left
    rw [capCount, hupper, hlower]
    norm_num
  · right
    rw [capCount, hupper, hlower]
    norm_num

/-- Any one exterior cap forces the full source width to contain the common
endpoint chord. -/
theorem endpointChord_le_width :
    2 * sin (endpointAngle lam) ≤ g.width := by
  rcases g.has_exterior_cap with hupper | hlower
  · exact g.upperBoundary.endpointChord_le_span_of_isCapped g.density_jump
      g.sourceRadius_eq_one hupper
  · exact g.lowerBoundary.endpointChord_le_span_of_isCapped g.density_jump
      g.sourceRadius_eq_one hlower

/-- Exact component area after summing the one or two radius-one caps. -/
theorem modeledWeightedArea_eq :
    g.modeledWeightedArea =
      Real.pi + 2 * g.width + g.capCount * endpointGap lam := by
  rw [modeledWeightedArea, capCount,
    g.upperBoundary.weightedAreaContribution_eq g.density_jump
      g.sourceRadius_eq_one,
    g.lowerBoundary.weightedAreaContribution_eq g.density_jump
      g.sourceRadius_eq_one]
  ring

/-- Exact component boundary cost after summing both interface traces. -/
theorem modeledWeightedPerimeter_eq :
    g.modeledWeightedPerimeter =
      2 * Real.pi + 2 * g.width + 2 * g.capCount * endpointGap lam := by
  rw [modeledWeightedPerimeter,
    g.upperBoundary.weightedBoundaryCost_eq g.density_jump
      g.sourceRadius_eq_one,
    g.lowerBoundary.weightedBoundaryCost_eq g.density_jump
      g.sourceRadius_eq_one]
  unfold width capCount
  ring

/-- Exact support identity before specializing the cap count to one or two. -/
theorem modeledWeightedPerimeter_sub_modeledWeightedArea :
    g.modeledWeightedPerimeter - g.modeledWeightedArea =
      Real.pi + g.capCount * endpointGap lam := by
  rw [g.modeledWeightedPerimeter_eq, g.modeledWeightedArea_eq]
  ring

/-- Closed type-(iii) endpoint area in the same support-gap coordinates. -/
theorem typeThreeArea_one_eq (hlam : 1 < lam) :
    LeanSuffixAnalytic.typeThreeArea lam 1 =
      Real.pi + 4 * sin (endpointAngle lam) + endpointGap lam := by
  have hsine := endpointSine_eq_scaledRadical hlam
  unfold LeanSuffixAnalytic.typeThreeArea LeanSuffixAnalytic.typeThreeAngle
    LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape
  norm_num [Real.arcsin_one]
  rw [← hsine]
  unfold endpointGap endpointAngle
  ring

/-- Every Figure-5 component model has at least the closed type-(iii) endpoint
area.  Equality is possible only at the one-cap, zero-extra-segment geometry;
that refinement is not needed here. -/
theorem typeThreeArea_one_le_modeledWeightedArea :
    LeanSuffixAnalytic.typeThreeArea lam 1 ≤ g.modeledWeightedArea := by
  rw [typeThreeArea_one_eq g.density_jump, g.modeledWeightedArea_eq]
  have hgap : 0 ≤ endpointGap lam := (endpointGap_pos g.density_jump).le
  have hcount := mul_le_mul_of_nonneg_right g.one_le_capCount hgap
  linarith [g.endpointChord_le_width]

/-- The component boundary cost lies on or above the one-cap endpoint support
line at its own component area. -/
theorem modeledWeightedArea_add_support_le_modeledWeightedPerimeter :
    g.modeledWeightedArea + Real.pi + endpointGap lam ≤
      g.modeledWeightedPerimeter := by
  rw [g.modeledWeightedArea_eq, g.modeledWeightedPerimeter_eq]
  have hgap : 0 ≤ endpointGap lam := (endpointGap_pos g.density_jump).le
  have hcount := mul_le_mul_of_nonneg_right g.one_le_capCount hgap
  linarith

/-- The checked type-(iii) recovery produces an actual source-admissible carrier
with the component area and boundary cost strictly below the Figure-5 component
accounting.  Relating those component values to the actual source carrier is a
separate geometric/relaxation theorem. -/
theorem exists_admissible_typeThree_below_modeledWeightedPerimeter :
    ∃ a : _root_.TypeThreeAssembly lam,
      a.h ∈ Ioo (0 : ℝ) 1 ∧
      (CMVRelaxation.relaxedSourceSemantics lam).IsAdmissible a.carrier ∧
      _root_.WeightedArea lam a.carrier = g.modeledWeightedArea ∧
      a.WeightedPerimeter < g.modeledWeightedPerimeter := by
  rcases exists_admissible_typeThree_below_endpoint_support g.density_jump
      g.typeThreeArea_one_le_modeledWeightedArea with
    ⟨a, ha, hadmissible, harea, hperimeter⟩
  exact ⟨a, ha, hadmissible, harea,
    hperimeter.trans_le g.modeledWeightedArea_add_support_le_modeledWeightedPerimeter⟩

end SourceGeometry

end CMVFigureFive
