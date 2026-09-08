/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFiveScalarComparison
import CMVFigureFourBilateralExamples

/-!
# Concrete Figure-5 source geometry

A radius-one four-arc assembly is a literal two-cap Figure-5 source: its strip
circle centers coincide with the four interface tangencies, so all four exposed
interface segments degenerate.  The generic constructor below establishes this
at the geometric interface and the endpoint example instantiates it at
`lambda = 2`.
-/

open Set
open Real

noncomputable section

namespace CMVFigureFive

private def pointSegment (x y : ℝ) :
    CMVFigureThree.DegenerateHorizontalSegment where
  leftX := x
  rightX := x
  baseY := y
  left_le_right := le_rfl

@[simp] private theorem pointSegment_carrier (x y : ℝ) :
    (pointSegment x y).carrier = {(x, y)} := by
  ext p
  simp only [CMVFigureThree.DegenerateHorizontalSegment.carrier,
    pointSegment, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hy, hleft, hright⟩
    apply Prod.ext
    · dsimp only
      exact le_antisymm hright hleft
    · exact hy
  · rintro rfl
    exact ⟨rfl, le_rfl, le_rfl⟩

namespace SourceGeometry

variable {lam : ℝ} (candidate : FourArcCandidate lam)

private theorem candidate_h_eq_one
    (hradius : candidate.stripCore.radius = 1) :
    candidate.h = 1 := by
  have hne : candidate.h ≠ 0 := ne_of_gt candidate.h_pos
  change 1 / candidate.h = 1 at hradius
  simpa only [one_mul] using ((div_eq_iff hne).mp hradius).symm

private theorem core_cos_sideAngle_eq_zero
    (hradius : candidate.stripCore.radius = 1) :
    cos candidate.stripCore.sideAngle = 0 := by
  rw [candidate.stripCore.cos_sideAngle]
  rw [show candidate.stripCore.curvature = candidate.h by rfl,
    candidate_h_eq_one candidate hradius]
  norm_num

private theorem core_leftCenterX_eq_leftEndpoint
    (hradius : candidate.stripCore.radius = 1) :
    candidate.stripCore.leftCenterX =
      candidate.assembly.upperCap.leftEndpoint.1 := by
  rw [StripCore.leftCenterX,
    core_cos_sideAngle_eq_zero candidate hradius]
  simp [FourArcCandidate.assembly, FourArcCandidate.stripCore,
    FourArcAssembly.upperCap, OneSidedCircularCap.leftEndpoint]

private theorem core_rightCenterX_eq_rightEndpoint
    (hradius : candidate.stripCore.radius = 1) :
    candidate.stripCore.rightCenterX =
      candidate.assembly.upperCap.rightEndpoint.1 := by
  rw [StripCore.rightCenterX,
    core_cos_sideAngle_eq_zero candidate hradius]
  simp [FourArcCandidate.assembly, FourArcCandidate.stripCore,
    FourArcAssembly.upperCap, OneSidedCircularCap.rightEndpoint]

private theorem lower_leftEndpoint_fst_eq_upper
    : candidate.assembly.lowerCap.leftEndpoint.1 =
      candidate.assembly.upperCap.leftEndpoint.1 := by
  rfl

private theorem lower_rightEndpoint_fst_eq_upper
    : candidate.assembly.lowerCap.rightEndpoint.1 =
      candidate.assembly.upperCap.rightEndpoint.1 := by
  rfl

private def upperEndpointBoundary
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hradius : candidate.stripCore.radius = 1) :
    CappedInterface lam candidate.stripCore.radius
      candidate.stripCore.leftCenterX candidate.stripCore.rightCenterX
      .upper where
  cap := candidate.assembly.upperCap
  leftSegment := pointSegment
    candidate.assembly.upperCap.leftEndpoint.1 1
  rightSegment := pointSegment
    candidate.assembly.upperCap.rightEndpoint.1 1
  cap_side := rfl
  cap_base := rfl
  cap_radius := candidate.four_arcs_common_radius.1
  signed_contact_law := by
    change lam * cos candidate.alpha = 1
    rw [hcandidate.snell_incidence,
      candidate_h_eq_one candidate hradius]
  left_segment_base := rfl
  right_segment_base := rfl
  left_segment_starts_at_tangency :=
    (core_leftCenterX_eq_leftEndpoint candidate hradius).symm
  left_segment_ends_at_cap := rfl
  right_segment_starts_at_cap := rfl
  right_segment_ends_at_tangency :=
    (core_rightCenterX_eq_rightEndpoint candidate hradius).symm

private def lowerEndpointBoundary
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hradius : candidate.stripCore.radius = 1) :
    CappedInterface lam candidate.stripCore.radius
      candidate.stripCore.leftCenterX candidate.stripCore.rightCenterX
      .lower where
  cap := candidate.assembly.lowerCap
  leftSegment := pointSegment
    candidate.assembly.lowerCap.leftEndpoint.1 (-1)
  rightSegment := pointSegment
    candidate.assembly.lowerCap.rightEndpoint.1 (-1)
  cap_side := rfl
  cap_base := rfl
  cap_radius := candidate.four_arcs_common_radius.2
  signed_contact_law := by
    change lam * cos candidate.alpha = 1
    rw [hcandidate.snell_incidence,
      candidate_h_eq_one candidate hradius]
  left_segment_base := rfl
  right_segment_base := rfl
  left_segment_starts_at_tangency := by
    rw [lower_leftEndpoint_fst_eq_upper candidate]
    exact (core_leftCenterX_eq_leftEndpoint candidate hradius).symm
  left_segment_ends_at_cap := rfl
  right_segment_starts_at_cap := rfl
  right_segment_ends_at_tangency := by
    rw [lower_rightEndpoint_fst_eq_upper candidate]
    exact (core_rightCenterX_eq_rightEndpoint candidate hradius).symm

private theorem upperEndpointBoundary_trace
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hradius : candidate.stripCore.radius = 1) :
    (upperEndpointBoundary candidate hcandidate hradius).trace =
      candidate.assembly.upperCap.arcTrace := by
  rw [CappedInterface.trace]
  simp only [upperEndpointBoundary, pointSegment_carrier]
  ext p
  simp only [mem_union, mem_singleton_iff]
  constructor
  · rintro (rfl | hp | rfl)
    · exact CMVFigureFour.OneSidedCircularCap.leftEndpoint_mem_arcTrace _
    · exact hp
    · exact CMVFigureFour.OneSidedCircularCap.rightEndpoint_mem_arcTrace _
  · exact fun hp => Or.inr (Or.inl hp)

private theorem lowerEndpointBoundary_trace
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hradius : candidate.stripCore.radius = 1) :
    (lowerEndpointBoundary candidate hcandidate hradius).trace =
      candidate.assembly.lowerCap.arcTrace := by
  rw [CappedInterface.trace]
  simp only [lowerEndpointBoundary, pointSegment_carrier]
  ext p
  simp only [mem_union, mem_singleton_iff]
  constructor
  · rintro (rfl | hp | rfl)
    · exact CMVFigureFour.OneSidedCircularCap.leftEndpoint_mem_arcTrace _
    · exact hp
    · exact CMVFigureFour.OneSidedCircularCap.rightEndpoint_mem_arcTrace _
  · exact fun hp => Or.inr (Or.inl hp)

/-- Every closed-Snell radius-one four-arc candidate realizes the complete
Figure-5 two-cap source signature.  No target reconstruction or perimeter lower
bound is assumed by this producer. -/
def ofRadiusOneFourArcCandidate
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hradius : candidate.stripCore.radius = 1) : SourceGeometry lam where
  sourceCarrier := candidate.assembly.carrier
  representative := interior candidate.assembly.carrier
  sourceRepresentative := CMVFigureFour.fourArcSourceRepresentative _
  sourceRadius := candidate.stripCore.radius
  leftStripCenter := (candidate.stripCore.leftCenterX, 0)
  rightStripCenter := (candidate.stripCore.rightCenterX, 0)
  upperLeftTangent := (candidate.stripCore.leftCenterX, 1)
  upperRightTangent := (candidate.stripCore.rightCenterX, 1)
  lowerLeftTangent := (candidate.stripCore.leftCenterX, -1)
  lowerRightTangent := (candidate.stripCore.rightCenterX, -1)
  density_jump := hcandidate.density_jump
  sourceRadius_pos := candidate.stripCore.radius_pos
  strip_centers_ordered := by
    rw [core_leftCenterX_eq_leftEndpoint candidate hradius,
      core_rightCenterX_eq_rightEndpoint candidate hradius]
    change -candidate.capChord / 2 < candidate.capChord / 2
    linarith [candidate.capChord_pos]
  upper_left_tangent_coordinate := rfl
  upper_right_tangent_coordinate := rfl
  lower_left_tangent_coordinate := rfl
  lower_right_tangent_coordinate := rfl
  upper_left_on_strip_circle := by
    unfold CMVFigureFour.circleValue
    dsimp only
    rw [hradius]
    norm_num
  upper_right_on_strip_circle := by
    unfold CMVFigureFour.circleValue
    dsimp only
    rw [hradius]
    norm_num
  lower_left_on_strip_circle := by
    unfold CMVFigureFour.circleValue
    dsimp only
    rw [hradius]
    norm_num
  lower_right_on_strip_circle := by
    unfold CMVFigureFour.circleValue
    dsimp only
    rw [hradius]
    norm_num
  upperBoundary := .capped (upperEndpointBoundary candidate hcandidate hradius)
  lowerBoundary := .capped (lowerEndpointBoundary candidate hcandidate hradius)
  has_exterior_cap := Or.inl trivial
  frontier_eq_components := by
    rw [CMVFigureFour.FourArcAssembly.frontier_interior_carrier,
      FourArcAssembly.boundaryTrace,
      CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace,
      CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace,
      InterfaceBoundary.trace,
      upperEndpointBoundary_trace candidate hcandidate hradius,
      lowerEndpointBoundary_trace candidate hcandidate hradius]
  left_strip_one_sided := by
    intro p hp hupper hlower
    rw [← CMVFigureFour.FourArcAssembly.leftArcTrace_eq_stripCircleTrace]
      at hp
    apply CMVFigureFour.FourArcAssembly.left_locallyOneSided
      candidate.assembly hp
    · simpa [core_leftCenterX_eq_leftEndpoint candidate hradius,
        FourArcAssembly.upperCap, OneSidedCircularCap.leftEndpoint]
        using hupper
    · simpa [core_leftCenterX_eq_leftEndpoint candidate hradius,
        FourArcAssembly.upperCap, OneSidedCircularCap.leftEndpoint]
        using hlower
  right_strip_one_sided := by
    intro p hp hupper hlower
    rw [← CMVFigureFour.FourArcAssembly.rightArcTrace_eq_stripCircleTrace]
      at hp
    apply CMVFigureFour.FourArcAssembly.right_locallyOneSided
      candidate.assembly hp
    · simpa [core_rightCenterX_eq_rightEndpoint candidate hradius,
        FourArcAssembly.upperCap, OneSidedCircularCap.rightEndpoint]
        using hupper
    · simpa [core_rightCenterX_eq_rightEndpoint candidate hradius,
        FourArcAssembly.upperCap, OneSidedCircularCap.rightEndpoint]
        using hlower
  upper_cap_one_sided := by
    intro p hp hleft hright
    rw [candidate.four_arcs_common_radius.1]
    exact CMVFigureFour.FourArcAssembly.upper_locallyOneSided
      candidate.assembly hp hleft hright
  lower_cap_one_sided := by
    intro p hp hleft hright
    rw [candidate.four_arcs_common_radius.2]
    exact CMVFigureFour.FourArcAssembly.lower_locallyOneSided
      candidate.assembly hp hleft hright

end SourceGeometry

namespace Examples

/-- The endpoint candidate used by the concrete Figure-5 specimen. -/
def endpointCandidate : FourArcCandidate 2 :=
  CMVFigureFour.Examples.endpointRaw.toFourArcCandidate
    CMVFigureFour.Examples.endpointRaw_satisfiesClosedSnell.toGeometry

private theorem endpointCandidate_satisfies :
    endpointCandidate.SatisfiesCMVTypeIVHypotheses :=
  CMVFigureFour.Examples.endpointRaw.toFourArcCandidate_satisfiesCMVTypeIVHypotheses
    CMVFigureFour.Examples.endpointRaw_satisfiesClosedSnell

@[simp] theorem endpointCandidate_radius :
    endpointCandidate.stripCore.radius = 1 := by
  norm_num [endpointCandidate, FourArcCandidate.stripCore,
    StripCore.radius,
    CMVSourceClassification.RawFourArcCoordinates.toFourArcCandidate,
    CMVSourceClassification.RawFourArcCoordinates.curvature,
    CMVFigureFour.Examples.endpointRaw]

/-- A literal two-cap Figure-5 source at `lambda = 2`, with a bounded open
representative and complete frontier.  This witnesses non-vacuity of the full
source signature at the radius-one endpoint. -/
def twoCapEndpointSource : SourceGeometry 2 :=
  SourceGeometry.ofRadiusOneFourArcCandidate endpointCandidate
    endpointCandidate_satisfies endpointCandidate_radius

@[simp] theorem twoCapEndpointSource_sourceRadius :
    twoCapEndpointSource.sourceRadius = 1 := by
  simp [twoCapEndpointSource,
    SourceGeometry.ofRadiusOneFourArcCandidate]

@[simp] theorem twoCapEndpointSource_capCount :
    twoCapEndpointSource.capCount = 2 := by
  simp [twoCapEndpointSource,
    SourceGeometry.ofRadiusOneFourArcCandidate,
    SourceGeometry.capCount, InterfaceBoundary.capIndicator]

end Examples
end CMVFigureFive
