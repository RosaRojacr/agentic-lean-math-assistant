/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourSourceGeometry
import CMVFigureThreeIncidence

/-!
# Independent source geometry for CMV Figure 5

This module freezes the source-facing input for Cañete--Miranda--Vittone,
Lemma 3.8, Step 3 (printed pages 17--18, Figure 5).  The source passage permits
one exterior arc on either density interface, or one on each interface; all
exposed interface segments may degenerate.  The representative contract carries
only bounded openness and almost-everywhere source agreement; its generic
sections must be derived from the complete boundary and local one-sidedness.

The signature contains an actual source set and bounded open almost-everywhere
representative, two literal common-radius strip-circle traces and their four
interface tangencies, one or two actual exterior caps with signed contact law,
ordered exposed interface segments, the complete actual frontier, and local
one-sided circle geometry away from junctions.

It deliberately contains no radius-one conclusion, normalized strip centers,
principal cap angle, chord or placement bound, target horizontal section,
coordinate-carrier identification, target area, relaxed-perimeter lower bound,
recovery hypothesis, or comparison theorem.  Source minimality is not an input.
The cap-free case is CMV type (ii), not Figure 5, and is excluded only by the
`has_exterior_cap` field.
-/

open Set
open Real
open MeasureTheory

noncomputable section

namespace CMVFigureFive

/-- The density interface selected by a cap or exposed segment. -/
def interfaceY : CapSide → ℝ
  | .upper => 1
  | .lower => -1

/-- One actual exterior cap and the two possibly degenerate exposed pieces of
its density interface.  Endpoint order is carried only by the literal segment
objects; cap placement bounds are downstream consequences. -/
structure CappedInterface (lam sourceRadius leftTangentX rightTangentX : ℝ)
    (side : CapSide) where
  cap : OneSidedCircularCap
  leftSegment : CMVFigureThree.DegenerateHorizontalSegment
  rightSegment : CMVFigureThree.DegenerateHorizontalSegment
  cap_side : cap.side = side
  cap_base : cap.baseY = interfaceY side
  cap_radius : cap.radius = sourceRadius
  signed_contact_law : lam * cos cap.theta = 1
  left_segment_base : leftSegment.baseY = interfaceY side
  right_segment_base : rightSegment.baseY = interfaceY side
  left_segment_starts_at_tangency : leftSegment.leftX = leftTangentX
  left_segment_ends_at_cap : leftSegment.rightX = cap.leftEndpoint.1
  right_segment_starts_at_cap : rightSegment.leftX = cap.rightEndpoint.1
  right_segment_ends_at_tangency : rightSegment.rightX = rightTangentX

namespace CappedInterface

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

/-- Literal complete trace on one capped density interface. -/
def trace
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side) :
    Set PlanePoint :=
  b.leftSegment.carrier ∪
    (b.cap.arcTrace ∪ b.rightSegment.carrier)

/-- The cap chord lies between the actual strip tangencies.  This is derived
from the two non-strict segment orders, including either degenerate segment. -/
theorem cap_endpoints_between
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side) :
    leftTangentX ≤ b.cap.leftEndpoint.1 ∧
      b.cap.rightEndpoint.1 ≤ rightTangentX := by
  constructor
  · calc
      leftTangentX = b.leftSegment.leftX :=
        b.left_segment_starts_at_tangency.symm
      _ ≤ b.leftSegment.rightX := b.leftSegment.left_le_right
      _ = b.cap.leftEndpoint.1 := b.left_segment_ends_at_cap
  · calc
      b.cap.rightEndpoint.1 = b.rightSegment.leftX :=
        b.right_segment_starts_at_cap.symm
      _ ≤ b.rightSegment.rightX := b.rightSegment.left_le_right
      _ = rightTangentX := b.right_segment_ends_at_tangency
end CappedInterface

/-- A cap-free density interface contributes one complete exposed segment.
Figure 5 permits this on exactly one side when there is only one exterior cap. -/
structure ExposedInterface (leftTangentX rightTangentX : ℝ)
    (side : CapSide) where
  segment : CMVFigureThree.DegenerateHorizontalSegment
  segment_base : segment.baseY = interfaceY side
  segment_starts_at_left_tangency : segment.leftX = leftTangentX
  segment_ends_at_right_tangency : segment.rightX = rightTangentX

/-- Complete source boundary data on one density interface. -/
inductive InterfaceBoundary (lam sourceRadius leftTangentX rightTangentX : ℝ)
    (side : CapSide) where
  | exposed (data : ExposedInterface leftTangentX rightTangentX side)
  | capped
      (data : CappedInterface lam sourceRadius leftTangentX rightTangentX side)

namespace InterfaceBoundary

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

/-- Literal trace contributed by one density interface. -/
def trace
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    Set PlanePoint :=
  match b with
  | .exposed data => data.segment.carrier
  | .capped data => data.trace

/-- Propositional cap-count discriminator. -/
def IsCapped
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) : Prop :=
  match b with
  | .exposed _ => False
  | .capped _ => True

/-- Local one-sided circle data for the exterior arc, when this interface has
one.  The two cap endpoints are the only omitted junctions. -/
def CapLocallyOneSided
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side)
    (representative : Set PlanePoint) : Prop :=
  match b with
  | .exposed _ => True
  | .capped data =>
      ∀ p, p ∈ data.cap.arcTrace →
        p ≠ data.cap.leftEndpoint → p ≠ data.cap.rightEndpoint →
          CMVFigureFour.LocallyOneSided representative data.cap.center
            sourceRadius p

end InterfaceBoundary

/-- Frozen Figure-5 source geometry before radius, angle, carrier, area, or
perimeter reduction.  Upper and lower cap placement are independent. -/
structure SourceGeometry (lam : ℝ) where
  sourceCarrier : Set PlanePoint
  representative : Set PlanePoint
  sourceRepresentative :
    CMVFigureFour.SourceRepresentative sourceCarrier representative
  sourceRadius : ℝ
  leftStripCenter : PlanePoint
  rightStripCenter : PlanePoint
  upperLeftTangent : PlanePoint
  upperRightTangent : PlanePoint
  lowerLeftTangent : PlanePoint
  lowerRightTangent : PlanePoint
  density_jump : 1 < lam
  sourceRadius_pos : 0 < sourceRadius
  strip_centers_ordered : leftStripCenter.1 < rightStripCenter.1
  upper_left_tangent_coordinate : upperLeftTangent = (leftStripCenter.1, 1)
  upper_right_tangent_coordinate : upperRightTangent = (rightStripCenter.1, 1)
  lower_left_tangent_coordinate : lowerLeftTangent = (leftStripCenter.1, -1)
  lower_right_tangent_coordinate : lowerRightTangent = (rightStripCenter.1, -1)
  upper_left_on_strip_circle :
    CMVFigureFour.circleValue leftStripCenter sourceRadius upperLeftTangent = 0
  upper_right_on_strip_circle :
    CMVFigureFour.circleValue rightStripCenter sourceRadius upperRightTangent = 0
  lower_left_on_strip_circle :
    CMVFigureFour.circleValue leftStripCenter sourceRadius lowerLeftTangent = 0
  lower_right_on_strip_circle :
    CMVFigureFour.circleValue rightStripCenter sourceRadius lowerRightTangent = 0
  upperBoundary : InterfaceBoundary lam sourceRadius
    leftStripCenter.1 rightStripCenter.1 .upper
  lowerBoundary : InterfaceBoundary lam sourceRadius
    leftStripCenter.1 rightStripCenter.1 .lower
  has_exterior_cap : upperBoundary.IsCapped ∨ lowerBoundary.IsCapped
  frontier_eq_components :
    frontier representative =
      CMVFigureFour.stripCircleTrace .left leftStripCenter sourceRadius ∪
        (CMVFigureFour.stripCircleTrace .right rightStripCenter sourceRadius ∪
          (upperBoundary.trace ∪ lowerBoundary.trace))
  left_strip_one_sided : ∀ p,
    p ∈ CMVFigureFour.stripCircleTrace .left leftStripCenter sourceRadius →
    p ≠ upperLeftTangent → p ≠ lowerLeftTangent →
      CMVFigureFour.LocallyOneSided representative leftStripCenter sourceRadius p
  right_strip_one_sided : ∀ p,
    p ∈ CMVFigureFour.stripCircleTrace .right rightStripCenter sourceRadius →
    p ≠ upperRightTangent → p ≠ lowerRightTangent →
      CMVFigureFour.LocallyOneSided representative rightStripCenter sourceRadius p
  upper_cap_one_sided : upperBoundary.CapLocallyOneSided representative
  lower_cap_one_sided : lowerBoundary.CapLocallyOneSided representative

namespace SourceGeometry

variable {lam : ℝ} (g : SourceGeometry lam)

/-- Actual source width before any symmetry or normalization. -/
def width : ℝ := g.rightStripCenter.1 - g.leftStripCenter.1

/-- Every frozen Figure-5 source has positive finite width. -/
theorem width_pos : 0 < g.width :=
  sub_pos.mpr g.strip_centers_ordered

/-- The two left strip tangencies force the left supporting-circle center onto
the horizontal midline. -/
theorem leftStripCenter_snd_eq_zero : g.leftStripCenter.2 = 0 := by
  have hu := g.upper_left_on_strip_circle
  have hl := g.lower_left_on_strip_circle
  rw [g.upper_left_tangent_coordinate] at hu
  rw [g.lower_left_tangent_coordinate] at hl
  unfold CMVFigureFour.circleValue at hu hl
  simp only at hu hl
  nlinarith

/-- The two right strip tangencies independently force the right
supporting-circle center onto the same horizontal midline. -/
theorem rightStripCenter_snd_eq_zero : g.rightStripCenter.2 = 0 := by
  have hu := g.upper_right_on_strip_circle
  have hl := g.lower_right_on_strip_circle
  rw [g.upper_right_tangent_coordinate] at hu
  rw [g.lower_right_tangent_coordinate] at hl
  unfold CMVFigureFour.circleValue at hu hl
  simp only at hu hl
  nlinarith

/-- The upper and lower tangencies on either one of the two strip circles
already force the common Figure-5 radius to be exactly one.  Comparing the
upper-left and lower-left circle equations first
forces the strip-circle center onto the horizontal midline; positivity then
selects `sourceRadius = 1` rather than the negative algebraic root. -/
theorem sourceRadius_eq_one : g.sourceRadius = 1 := by
  have hu := g.upper_left_on_strip_circle
  have hl := g.lower_left_on_strip_circle
  rw [g.upper_left_tangent_coordinate] at hu
  rw [g.lower_left_tangent_coordinate] at hl
  unfold CMVFigureFour.circleValue at hu hl
  simp only at hu hl
  nlinarith [g.sourceRadius_pos]

/-- The source carrier is null measurable through its actual open
representative, without a target-carrier identification. -/
theorem sourceCarrier_nullMeasurableSet :
    NullMeasurableSet g.sourceCarrier volume :=
  g.sourceRepresentative.representative_open.measurableSet.nullMeasurableSet.congr
    g.sourceRepresentative.source_ae_representative.symm

/-- The signature covers exactly one or two exterior caps, never the cap-free
type-(ii) branch. -/
theorem one_or_two_exterior_caps :
    g.upperBoundary.IsCapped ∨ g.lowerBoundary.IsCapped :=
  g.has_exterior_cap

end SourceGeometry

end CMVFigureFive
