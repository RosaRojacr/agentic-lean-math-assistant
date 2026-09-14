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

/-- Left intersection of a horizontal line with the supporting circle of a
capped Figure-5 interface. -/
def exteriorLeftBoundaryPoint
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (y : ℝ) : PlanePoint :=
  (b.cap.center.1 -
    √(sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2), y)

/-- Right intersection of a horizontal line with the supporting circle of a
capped Figure-5 interface. -/
def exteriorRightBoundaryPoint
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (y : ℝ) : PlanePoint :=
  (b.cap.center.1 +
    √(sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2), y)

/-- The signed Figure-5 contact law forces a positive cap cosine. -/
theorem cos_theta_pos
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) :
    0 < cos b.cap.theta := by
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hlam
  nlinarith [b.signed_contact_law]

/-- Every genuine cap angle has cosine strictly below one. -/
theorem cos_theta_lt_one
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side) :
    cos b.cap.theta < 1 := by
  have hanti := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Icc 0 Real.pi from
      ⟨le_rfl, Real.pi_pos.le⟩)
    (show b.cap.theta ∈ Icc 0 Real.pi from
      ⟨b.cap.theta_pos.le, b.cap.theta_lt_pi.le⟩)
    b.cap.theta_pos
  simpa using hanti

/-- An upper cap center lies strictly below its density interface. -/
theorem upper_center_lt_interface
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX .upper)
    (hlam : 1 < lam) :
    b.cap.center.2 < 1 := by
  have hR := b.cap.radius_pos
  have hcos := b.cos_theta_pos hlam
  simp only [OneSidedCircularCap.center, b.cap_side, b.cap_base, interfaceY]
  nlinarith

/-- The upper cap has nonempty height support above the interface. -/
theorem upper_interface_lt_pole
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX .upper) :
    1 < b.cap.center.2 + sourceRadius := by
  have hR := b.cap.radius_pos
  have hcos := b.cos_theta_lt_one
  have hcenter :
      b.cap.center.2 = 1 - b.cap.radius * cos b.cap.theta := by
    simp only [OneSidedCircularCap.center, b.cap_side, b.cap_base, interfaceY]
  nlinarith [b.cap_radius]

/-- A lower cap center lies strictly above its density interface. -/
theorem lower_interface_lt_center
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX .lower)
    (hlam : 1 < lam) :
    -1 < b.cap.center.2 := by
  have hR := b.cap.radius_pos
  have hcos := b.cos_theta_pos hlam
  simp only [OneSidedCircularCap.center, b.cap_side, b.cap_base, interfaceY]
  nlinarith

/-- The lower cap has nonempty height support below the interface. -/
theorem lower_pole_lt_interface
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX .lower) :
    b.cap.center.2 - sourceRadius < -1 := by
  have hR := b.cap.radius_pos
  have hcos := b.cos_theta_lt_one
  have hcenter :
      b.cap.center.2 = -1 + b.cap.radius * cos b.cap.theta := by
    simp only [OneSidedCircularCap.center, b.cap_side, b.cap_base, interfaceY]
  nlinarith [b.cap_radius]

/-- Every cap-trace point at a height where the circle radicand is nonnegative
has one of the two derived abscissae. -/
theorem arcTrace_abscissa_eq_left_or_right
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    {x y : ℝ}
    (hrad : 0 ≤ sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2)
    (hp : (x, y) ∈ b.cap.arcTrace) :
    x = (b.exteriorLeftBoundaryPoint y).1 ∨
      x = (b.exteriorRightBoundaryPoint y).1 := by
  have hsqrtSq :
      (√(sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2)) ^ 2 =
        sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 :=
    Real.sq_sqrt hrad
  have hcircle := hp.1
  change b.cap.radiusSquaredAt (x, y) = b.cap.radius ^ 2 at hcircle
  rw [b.cap_radius] at hcircle
  unfold OneSidedCircularCap.radiusSquaredAt at hcircle
  unfold exteriorLeftBoundaryPoint exteriorRightBoundaryPoint
  dsimp only
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp
      (show (x - b.cap.center.1) ^ 2 =
          (√(sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2)) ^ 2 by
        nlinarith) with hright | hleft
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

/-- Both transverse intersections strictly between an upper interface and its
pole belong to the literal cap trace. -/
theorem upper_boundaryPoints_mem_arcTrace
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX .upper)
    (hlam : 1 < lam) {y : ℝ}
    (hbase : 1 < y) (hpole : y < b.cap.center.2 + sourceRadius) :
    b.exteriorLeftBoundaryPoint y ∈ b.cap.arcTrace ∧
      b.exteriorRightBoundaryPoint y ∈ b.cap.arcTrace := by
  have hcenter := b.upper_center_lt_interface hlam
  have hRadius : 0 < sourceRadius := by
    rw [← b.cap_radius]
    exact b.cap.radius_pos
  have hdiffPos : 0 < y - b.cap.center.2 := by linarith
  have hdiffLt : y - b.cap.center.2 < sourceRadius := by linarith
  have hrad :
      0 < sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have hsqrtSq :
      (√(sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2)) ^ 2 =
        sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 :=
    Real.sq_sqrt hrad.le
  constructor
  · change b.cap.radiusSquaredAt (b.exteriorLeftBoundaryPoint y) =
        b.cap.radius ^ 2 ∧
      (match b.cap.side with
        | .upper => b.cap.baseY ≤ (b.exteriorLeftBoundaryPoint y).2
        | .lower => (b.exteriorLeftBoundaryPoint y).2 ≤ b.cap.baseY)
    constructor
    · unfold OneSidedCircularCap.radiusSquaredAt exteriorLeftBoundaryPoint
      rw [b.cap_radius]
      dsimp only
      nlinarith
    · simp only [b.cap_side, b.cap_base, interfaceY,
        exteriorLeftBoundaryPoint]
      exact hbase.le
  · change b.cap.radiusSquaredAt (b.exteriorRightBoundaryPoint y) =
        b.cap.radius ^ 2 ∧
      (match b.cap.side with
        | .upper => b.cap.baseY ≤ (b.exteriorRightBoundaryPoint y).2
        | .lower => (b.exteriorRightBoundaryPoint y).2 ≤ b.cap.baseY)
    constructor
    · unfold OneSidedCircularCap.radiusSquaredAt exteriorRightBoundaryPoint
      rw [b.cap_radius]
      dsimp only
      nlinarith
    · simp only [b.cap_side, b.cap_base, interfaceY,
        exteriorRightBoundaryPoint]
      exact hbase.le

/-- Both transverse intersections strictly between a lower pole and its
interface belong to the literal cap trace. -/
theorem lower_boundaryPoints_mem_arcTrace
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX .lower)
    (hlam : 1 < lam) {y : ℝ}
    (hpole : b.cap.center.2 - sourceRadius < y) (hbase : y < -1) :
    b.exteriorLeftBoundaryPoint y ∈ b.cap.arcTrace ∧
      b.exteriorRightBoundaryPoint y ∈ b.cap.arcTrace := by
  have hcenter := b.lower_interface_lt_center hlam
  have hRadius : 0 < sourceRadius := by
    rw [← b.cap_radius]
    exact b.cap.radius_pos
  have hdiffNeg : -sourceRadius < y - b.cap.center.2 := by linarith
  have hdiffLt : y - b.cap.center.2 < 0 := by linarith
  have hrad :
      0 < sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have hsqrtSq :
      (√(sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2)) ^ 2 =
        sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 :=
    Real.sq_sqrt hrad.le
  constructor
  · change b.cap.radiusSquaredAt (b.exteriorLeftBoundaryPoint y) =
        b.cap.radius ^ 2 ∧
      (match b.cap.side with
        | .upper => b.cap.baseY ≤ (b.exteriorLeftBoundaryPoint y).2
        | .lower => (b.exteriorLeftBoundaryPoint y).2 ≤ b.cap.baseY)
    constructor
    · unfold OneSidedCircularCap.radiusSquaredAt exteriorLeftBoundaryPoint
      rw [b.cap_radius]
      dsimp only
      nlinarith
    · simp only [b.cap_side, b.cap_base, interfaceY,
        exteriorLeftBoundaryPoint]
      exact hbase.le
  · change b.cap.radiusSquaredAt (b.exteriorRightBoundaryPoint y) =
        b.cap.radius ^ 2 ∧
      (match b.cap.side with
        | .upper => b.cap.baseY ≤ (b.exteriorRightBoundaryPoint y).2
        | .lower => (b.exteriorRightBoundaryPoint y).2 ≤ b.cap.baseY)
    constructor
    · unfold OneSidedCircularCap.radiusSquaredAt exteriorRightBoundaryPoint
      rw [b.cap_radius]
      dsimp only
      nlinarith
    · simp only [b.cap_side, b.cap_base, interfaceY,
        exteriorRightBoundaryPoint]
      exact hbase.le

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

/-- Horizontal tangency heights of the exterior supporting circle, when this
interface is capped.  Exposed interfaces contribute no circle tangencies. -/
def tangentHeights
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX side) :
    Finset ℝ :=
  match b with
  | .exposed _ => ∅
  | .capped data =>
      {data.cap.center.2 - sourceRadius,
        data.cap.center.2 + sourceRadius}


/-- Every point of an upper Figure-5 interface trace lies on or above the
upper density interface. -/
theorem trace_second_ge_one
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX .upper)
    {p : PlanePoint} (hp : p ∈ b.trace) :
    1 ≤ p.2 := by
  cases b with
  | exposed data =>
      change p ∈ data.segment.carrier at hp
      have hy := hp.1
      rw [data.segment_base] at hy
      simpa [interfaceY] using hy.ge
  | capped data =>
      change p ∈ data.leftSegment.carrier ∪
        (data.cap.arcTrace ∪ data.rightSegment.carrier) at hp
      rcases hp with hleft | hcap | hright
      · have hy := hleft.1
        rw [data.left_segment_base] at hy
        simpa [interfaceY] using hy.ge
      · have hy := hcap.2
        rw [data.cap_side] at hy
        change data.cap.baseY ≤ p.2 at hy
        rw [data.cap_base] at hy
        simpa [interfaceY] using hy
      · have hy := hright.1
        rw [data.right_segment_base] at hy
        simpa [interfaceY] using hy.ge

/-- Every point of a lower Figure-5 interface trace lies on or below the
lower density interface. -/
theorem trace_second_le_neg_one
    (b : InterfaceBoundary lam sourceRadius leftTangentX rightTangentX .lower)
    {p : PlanePoint} (hp : p ∈ b.trace) :
    p.2 ≤ -1 := by
  cases b with
  | exposed data =>
      change p ∈ data.segment.carrier at hp
      have hy := hp.1
      rw [data.segment_base] at hy
      simpa [interfaceY] using hy.le
  | capped data =>
      change p ∈ data.leftSegment.carrier ∪
        (data.cap.arcTrace ∪ data.rightSegment.carrier) at hp
      rcases hp with hleft | hcap | hright
      · have hy := hleft.1
        rw [data.left_segment_base] at hy
        simpa [interfaceY] using hy.le
      · have hy := hcap.2
        rw [data.cap_side] at hy
        change p.2 ≤ data.cap.baseY at hy
        rw [data.cap_base] at hy
        simpa [interfaceY] using hy
      · have hy := hright.1
        rw [data.right_segment_base] at hy
        simpa [interfaceY] using hy.le

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

/-- The two density interfaces and every exterior-circle horizontal tangency.
This finite set is the complete exceptional-height policy for Figure-5 section
reconstruction. -/
def exteriorExceptionalHeights : Finset ℝ :=
  {-1, 1} ∪ g.upperBoundary.tangentHeights ∪
    g.lowerBoundary.tangentHeights

/-- The Figure-5 exterior exceptional-height policy is null. -/
theorem measure_exteriorExceptionalHeights :
    (volume : Measure ℝ) (g.exteriorExceptionalHeights : Set ℝ) = 0 := by
  exact g.exteriorExceptionalHeights.finite_toSet.measure_zero volume


/-- The left endpoint of the source representative's horizontal section at a
strict strip height.  Radius one and the derived horizontal center make this
the literal left-circle intersection. -/
def leftStripBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.leftStripCenter.1 - √(1 - y ^ 2), y)

/-- The right endpoint of the source representative's horizontal section at a
strict strip height. -/
def rightStripBoundaryPoint (y : ℝ) : PlanePoint :=
  (g.rightStripCenter.1 + √(1 - y ^ 2), y)

private theorem stripRadicand_pos {y : ℝ} (hy : |y| < 1) :
    0 < 1 - y ^ 2 := by
  have hyBounds := abs_lt.mp hy
  have hprod : 0 < (1 - y) * (1 + y) :=
    mul_pos (sub_pos.mpr hyBounds.2) (by linarith [hyBounds.1])
  nlinarith

/-- The derived left section endpoint lies on the actual left strip-circle
trace. -/
theorem leftStripBoundaryPoint_mem_trace {y : ℝ} (hy : |y| < 1) :
    g.leftStripBoundaryPoint y ∈
      CMVFigureFour.stripCircleTrace .left
        g.leftStripCenter g.sourceRadius := by
  have hrad := stripRadicand_pos hy
  have hsqrtSq : (√(1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad.le
  refine ⟨?_, hy.le, ?_⟩
  · unfold CMVFigureFour.circleValue leftStripBoundaryPoint
    dsimp only
    rw [g.leftStripCenter_snd_eq_zero, g.sourceRadius_eq_one]
    nlinarith
  · change g.leftStripCenter.1 - √(1 - y ^ 2) ≤ g.leftStripCenter.1
    linarith [Real.sqrt_nonneg (1 - y ^ 2)]

/-- The derived right section endpoint lies on the actual right strip-circle
trace. -/
theorem rightStripBoundaryPoint_mem_trace {y : ℝ} (hy : |y| < 1) :
    g.rightStripBoundaryPoint y ∈
      CMVFigureFour.stripCircleTrace .right
        g.rightStripCenter g.sourceRadius := by
  have hrad := stripRadicand_pos hy
  have hsqrtSq : (√(1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad.le
  refine ⟨?_, hy.le, ?_⟩
  · unfold CMVFigureFour.circleValue rightStripBoundaryPoint
    dsimp only
    rw [g.rightStripCenter_snd_eq_zero, g.sourceRadius_eq_one]
    nlinarith
  · change g.rightStripCenter.1 ≤
      g.rightStripCenter.1 + √(1 - y ^ 2)
    linarith [Real.sqrt_nonneg (1 - y ^ 2)]

/-- A strict-strip point on the left source trace has the derived left
abscissa. -/
theorem leftStripTrace_abscissa_eq
    {x y : ℝ} (hy : |y| < 1)
    (hp : (x, y) ∈ CMVFigureFour.stripCircleTrace .left
      g.leftStripCenter g.sourceRadius) :
    x = (g.leftStripBoundaryPoint y).1 := by
  have hrad := stripRadicand_pos hy
  have hsqrtSq : (√(1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad.le
  have hcircle := hp.1
  have hbranch := hp.2.2
  unfold CMVFigureFour.circleValue at hcircle
  rw [g.leftStripCenter_snd_eq_zero, g.sourceRadius_eq_one] at hcircle
  change x ≤ g.leftStripCenter.1 at hbranch
  unfold leftStripBoundaryPoint
  dsimp only
  nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]

/-- A strict-strip point on the right source trace has the derived right
abscissa. -/
theorem rightStripTrace_abscissa_eq
    {x y : ℝ} (hy : |y| < 1)
    (hp : (x, y) ∈ CMVFigureFour.stripCircleTrace .right
      g.rightStripCenter g.sourceRadius) :
    x = (g.rightStripBoundaryPoint y).1 := by
  have hrad := stripRadicand_pos hy
  have hsqrtSq : (√(1 - y ^ 2)) ^ 2 = 1 - y ^ 2 :=
    Real.sq_sqrt hrad.le
  have hcircle := hp.1
  have hbranch := hp.2.2
  unfold CMVFigureFour.circleValue at hcircle
  rw [g.rightStripCenter_snd_eq_zero, g.sourceRadius_eq_one] at hcircle
  change g.rightStripCenter.1 ≤ x at hbranch
  unfold rightStripBoundaryPoint
  dsimp only
  nlinarith [Real.sqrt_nonneg (1 - y ^ 2)]

/-- Both derived strict-strip endpoints are genuine frontier points of the
actual open representative's horizontal section. -/
theorem stripBoundaryPoints_mem_section_frontier
    {y : ℝ} (hy : |y| < 1) :
    (g.leftStripBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) ∧
      (g.rightStripBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) := by
  have hrad := stripRadicand_pos hy
  have hsqrtPos : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 hrad
  have hyBounds := abs_lt.mp hy
  constructor
  · have hp := g.leftStripBoundaryPoint_mem_trace hy
    apply CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hp.1
    · unfold leftStripBoundaryPoint
      dsimp only
      linarith
    · apply g.left_strip_one_sided _ hp
      · intro heq
        rw [g.upper_left_tangent_coordinate] at heq
        have hsnd := congrArg Prod.snd heq
        change y = 1 at hsnd
        linarith
      · intro heq
        rw [g.lower_left_tangent_coordinate] at heq
        have hsnd := congrArg Prod.snd heq
        change y = -1 at hsnd
        linarith
  · have hp := g.rightStripBoundaryPoint_mem_trace hy
    apply CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
      hp.1
    · unfold rightStripBoundaryPoint
      dsimp only
      linarith
    · apply g.right_strip_one_sided _ hp
      · intro heq
        rw [g.upper_right_tangent_coordinate] at heq
        have hsnd := congrArg Prod.snd heq
        change y = 1 at hsnd
        linarith
      · intro heq
        rw [g.lower_right_tangent_coordinate] at heq
        have hsnd := congrArg Prod.snd heq
        change y = -1 at hsnd
        linarith

/-- The complete frontier of every strict-strip horizontal section consists
exactly of the two transverse strip-circle intersections. -/
theorem frontier_strictStripSection_eq_pair
    {y : ℝ} (hy : |y| < 1) :
    frontier
        (CMVSourceClassification.horizontalSection g.representative y) =
      {(g.leftStripBoundaryPoint y).1,
        (g.rightStripBoundaryPoint y).1} := by
  have hknown := g.stripBoundaryPoints_mem_section_frontier hy
  have hyBounds := abs_lt.mp hy
  apply Set.Subset.antisymm
  · intro x hx
    have hplane :=
      CMVSourceClassification.frontier_horizontalSection_subset
        g.representative y hx
    rw [g.frontier_eq_components] at hplane
    rcases hplane with hleft | hright | hupper | hlower
    · exact Or.inl (g.leftStripTrace_abscissa_eq hy hleft)
    · exact Or.inr (g.rightStripTrace_abscissa_eq hy hright)
    · exact False.elim
        ((not_le_of_gt hyBounds.2)
          (g.upperBoundary.trace_second_ge_one hupper))
    · exact False.elim
        ((not_le_of_gt hyBounds.1)
          (g.lowerBoundary.trace_second_le_neg_one hlower))
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact hknown.1
    · subst x
      exact hknown.2

/-- The two strict-strip source intersections are strictly ordered. -/
theorem stripBoundaryPoint_order (y : ℝ) :
    (g.leftStripBoundaryPoint y).1 <
      (g.rightStripBoundaryPoint y).1 := by
  unfold leftStripBoundaryPoint rightStripBoundaryPoint
  dsimp only
  nlinarith [Real.sqrt_nonneg (1 - y ^ 2), g.strip_centers_ordered]

/-- Bounded openness, the literal complete Figure-5 frontier, and local
one-sidedness determine every strict-strip section.  No interval-section,
symmetry, normalized carrier, or source-minimality premise is used. -/
theorem actual_strictStripSection
    {y : ℝ} (hy : |y| < 1) :
    CMVSourceClassification.horizontalSection g.representative y =
      Ioo ((g.leftStripBoundaryPoint y).1)
        ((g.rightStripBoundaryPoint y).1) :=
  CMVSourceClassification.IsOpen.eq_Ioo_of_isBounded_frontier_eq_pair
    (CMVSourceClassification.isOpen_horizontalSection
      g.sourceRepresentative.representative_open y)
    (CMVSourceClassification.isBounded_horizontalSection
      g.sourceRepresentative.representative_bounded y)
    (g.stripBoundaryPoint_order y)
    (g.frontier_strictStripSection_eq_pair hy)

private theorem actualSection_eq_empty_of_frontier_eq_empty
    (y : ℝ)
    (hfrontier : frontier
      (CMVSourceClassification.horizontalSection g.representative y) = ∅) :
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  rcases frontier_eq_empty_iff.mp hfrontier with hempty | huniv
  · exact hempty
  · have hbounded :=
      CMVSourceClassification.isBounded_horizontalSection
        g.sourceRepresentative.representative_bounded y
    obtain ⟨upper, hupper⟩ := hbounded.bddAbove
    have hmem :
        upper + 1 ∈
          CMVSourceClassification.horizontalSection g.representative y := by
      rw [huniv]
      exact mem_univ _
    linarith [hupper hmem]

/-- The two transverse intersections of an actual upper cap are genuine
frontier points of the representative section. -/
theorem upperCappedBoundaryPoints_mem_section_frontier
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .upper)
    (hBoundary : g.upperBoundary = .capped b)
    {y : ℝ} (hbase : 1 < y)
    (hpole : y < b.cap.center.2 + g.sourceRadius) :
    (b.exteriorLeftBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) ∧
      (b.exteriorRightBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) := by
  have htrace :=
    b.upper_boundaryPoints_mem_arcTrace g.density_jump hbase hpole
  have hcenter := b.upper_center_lt_interface g.density_jump
  have hdiffLt : y - b.cap.center.2 < g.sourceRadius := by linarith
  have hdiffPos : 0 < y - b.cap.center.2 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have hroot :
      0 < √(g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hlocal := g.upper_cap_one_sided
  rw [hBoundary] at hlocal
  change ∀ p, p ∈ b.cap.arcTrace →
      p ≠ b.cap.leftEndpoint → p ≠ b.cap.rightEndpoint →
        CMVFigureFour.LocallyOneSided g.representative b.cap.center
          g.sourceRadius p at hlocal
  constructor
  · have hcircle :
        CMVFigureFour.circleValue b.cap.center g.sourceRadius
          (b.exteriorLeftBoundaryPoint y) = 0 := by
      have hc := htrace.1.1
      unfold CMVFigureFour.circleValue OneSidedCircularCap.radiusSquaredAt at *
      rw [b.cap_radius] at hc
      nlinarith
    apply
      CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
        hcircle
    · unfold CappedInterface.exteriorLeftBoundaryPoint
      dsimp only
      linarith
    · apply hlocal _ htrace.1
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorLeftBoundaryPoint,
            OneSidedCircularCap.leftEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorLeftBoundaryPoint,
            OneSidedCircularCap.rightEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
  · have hcircle :
        CMVFigureFour.circleValue b.cap.center g.sourceRadius
          (b.exteriorRightBoundaryPoint y) = 0 := by
      have hc := htrace.2.1
      unfold CMVFigureFour.circleValue OneSidedCircularCap.radiusSquaredAt at *
      rw [b.cap_radius] at hc
      nlinarith
    apply
      CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
        hcircle
    · unfold CappedInterface.exteriorRightBoundaryPoint
      dsimp only
      linarith
    · apply hlocal _ htrace.2
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorRightBoundaryPoint,
            OneSidedCircularCap.leftEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorRightBoundaryPoint,
            OneSidedCircularCap.rightEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith

/-- The complete section frontier strictly inside an upper cap consists of its
two transverse circle intersections. -/
theorem frontier_upperCappedSection_eq_pair
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .upper)
    (hBoundary : g.upperBoundary = .capped b)
    {y : ℝ} (hbase : 1 < y)
    (hpole : y < b.cap.center.2 + g.sourceRadius) :
    frontier
        (CMVSourceClassification.horizontalSection g.representative y) =
      {(b.exteriorLeftBoundaryPoint y).1,
        (b.exteriorRightBoundaryPoint y).1} := by
  have hknown :=
    g.upperCappedBoundaryPoints_mem_section_frontier b hBoundary hbase hpole
  have hcenter := b.upper_center_lt_interface g.density_jump
  have hdiffLt : y - b.cap.center.2 < g.sourceRadius := by linarith
  have hdiffPos : 0 < y - b.cap.center.2 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  apply Set.Subset.antisymm
  · intro x hx
    have hplane :=
      CMVSourceClassification.frontier_horizontalSection_subset
        g.representative y hx
    rw [g.frontier_eq_components] at hplane
    rcases hplane with hleft | hright | hupper | hlower
    · have hyBound := hleft.2.1
      rw [abs_of_pos (lt_trans zero_lt_one hbase)] at hyBound
      linarith
    · have hyBound := hright.2.1
      rw [abs_of_pos (lt_trans zero_lt_one hbase)] at hyBound
      linarith
    · rw [hBoundary] at hupper
      change (x, y) ∈ b.leftSegment.carrier ∪
        (b.cap.arcTrace ∪ b.rightSegment.carrier) at hupper
      rcases hupper with hsegment | hcap | hsegment
      · have hyEq := hsegment.1
        rw [b.left_segment_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
      · exact b.arcTrace_abscissa_eq_left_or_right hrad.le hcap
      · have hyEq := hsegment.1
        rw [b.right_segment_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
    · have hyBound := g.lowerBoundary.trace_second_le_neg_one hlower
      linarith
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact hknown.1
    · subst x
      exact hknown.2

/-- Every representative section strictly between an upper interface and its
cap pole is exactly the open circle interval. -/
theorem actual_upperCappedSection
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .upper)
    (hBoundary : g.upperBoundary = .capped b)
    {y : ℝ} (hbase : 1 < y)
    (hpole : y < b.cap.center.2 + g.sourceRadius) :
    CMVSourceClassification.horizontalSection g.representative y =
      Ioo ((b.exteriorLeftBoundaryPoint y).1)
        ((b.exteriorRightBoundaryPoint y).1) := by
  have hcenter := b.upper_center_lt_interface g.density_jump
  have hdiffLt : y - b.cap.center.2 < g.sourceRadius := by linarith
  have hdiffPos : 0 < y - b.cap.center.2 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have horder :
      (b.exteriorLeftBoundaryPoint y).1 <
        (b.exteriorRightBoundaryPoint y).1 := by
    have hroot :
        0 < √(g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2) :=
      Real.sqrt_pos.2 hrad
    unfold CappedInterface.exteriorLeftBoundaryPoint
      CappedInterface.exteriorRightBoundaryPoint
    dsimp only
    linarith
  exact CMVSourceClassification.IsOpen.eq_Ioo_of_isBounded_frontier_eq_pair
    (CMVSourceClassification.isOpen_horizontalSection
      g.sourceRepresentative.representative_open y)
    (CMVSourceClassification.isBounded_horizontalSection
      g.sourceRepresentative.representative_bounded y)
    horder
    (g.frontier_upperCappedSection_eq_pair b hBoundary hbase hpole)

/-- An exposed upper interface has no representative section at any exterior
height. -/
theorem actual_upperExposedSection_empty
    (b : ExposedInterface g.leftStripCenter.1
      g.rightStripCenter.1 .upper)
    (hBoundary : g.upperBoundary = .exposed b)
    {y : ℝ} (hbase : 1 < y) :
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  apply g.actualSection_eq_empty_of_frontier_eq_empty y
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hplane :=
    CMVSourceClassification.frontier_horizontalSection_subset
      g.representative y hx
  rw [g.frontier_eq_components] at hplane
  rcases hplane with hleft | hright | hupper | hlower
  · have hyBound := hleft.2.1
    rw [abs_of_pos (lt_trans zero_lt_one hbase)] at hyBound
    linarith
  · have hyBound := hright.2.1
    rw [abs_of_pos (lt_trans zero_lt_one hbase)] at hyBound
    linarith
  · rw [hBoundary] at hupper
    change (x, y) ∈ b.segment.carrier at hupper
    have hyEq := hupper.1
    rw [b.segment_base] at hyEq
    simp only [interfaceY] at hyEq
    linarith
  · have hyBound := g.lowerBoundary.trace_second_le_neg_one hlower
    linarith

/-- Above an upper cap's supporting-circle pole the representative section is
empty.  The tangent height itself belongs to the finite exceptional set. -/
theorem actual_upperCappedSection_empty_above
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .upper)
    (hBoundary : g.upperBoundary = .capped b)
    {y : ℝ} (hbase : 1 < y)
    (hpole : b.cap.center.2 + g.sourceRadius < y) :
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  apply g.actualSection_eq_empty_of_frontier_eq_empty y
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hplane :=
    CMVSourceClassification.frontier_horizontalSection_subset
      g.representative y hx
  rw [g.frontier_eq_components] at hplane
  rcases hplane with hleft | hright | hupper | hlower
  · have hyBound := hleft.2.1
    rw [abs_of_pos (lt_trans zero_lt_one hbase)] at hyBound
    linarith
  · have hyBound := hright.2.1
    rw [abs_of_pos (lt_trans zero_lt_one hbase)] at hyBound
    linarith
  · rw [hBoundary] at hupper
    change (x, y) ∈ b.leftSegment.carrier ∪
      (b.cap.arcTrace ∪ b.rightSegment.carrier) at hupper
    rcases hupper with hsegment | hcap | hsegment
    · have hyEq := hsegment.1
      rw [b.left_segment_base] at hyEq
      simp only [interfaceY] at hyEq
      linarith
    · have hcircle := hcap.1
      change b.cap.radiusSquaredAt (x, y) = b.cap.radius ^ 2 at hcircle
      unfold OneSidedCircularCap.radiusSquaredAt at hcircle
      rw [b.cap_radius] at hcircle
      dsimp only at hcircle
      have hdiff : g.sourceRadius < y - b.cap.center.2 := by linarith
      nlinarith [sq_nonneg (x - b.cap.center.1), g.sourceRadius_pos]
    · have hyEq := hsegment.1
      rw [b.right_segment_base] at hyEq
      simp only [interfaceY] at hyEq
      linarith
  · have hyBound := g.lowerBoundary.trace_second_le_neg_one hlower
    linarith

/-- The two transverse intersections of an actual lower cap are genuine
frontier points of the representative section. -/
theorem lowerCappedBoundaryPoints_mem_section_frontier
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .capped b)
    {y : ℝ} (hpole : b.cap.center.2 - g.sourceRadius < y)
    (hbase : y < -1) :
    (b.exteriorLeftBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) ∧
      (b.exteriorRightBoundaryPoint y).1 ∈ frontier
        (CMVSourceClassification.horizontalSection g.representative y) := by
  have htrace :=
    b.lower_boundaryPoints_mem_arcTrace g.density_jump hpole hbase
  have hcenter := b.lower_interface_lt_center g.density_jump
  have hdiffNeg : -g.sourceRadius < y - b.cap.center.2 := by linarith
  have hdiffLt : y - b.cap.center.2 < 0 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have hroot :
      0 < √(g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hlocal := g.lower_cap_one_sided
  rw [hBoundary] at hlocal
  change ∀ p, p ∈ b.cap.arcTrace →
      p ≠ b.cap.leftEndpoint → p ≠ b.cap.rightEndpoint →
        CMVFigureFour.LocallyOneSided g.representative b.cap.center
          g.sourceRadius p at hlocal
  constructor
  · have hcircle :
        CMVFigureFour.circleValue b.cap.center g.sourceRadius
          (b.exteriorLeftBoundaryPoint y) = 0 := by
      have hc := htrace.1.1
      unfold CMVFigureFour.circleValue OneSidedCircularCap.radiusSquaredAt at *
      rw [b.cap_radius] at hc
      nlinarith
    apply
      CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
        hcircle
    · unfold CappedInterface.exteriorLeftBoundaryPoint
      dsimp only
      linarith
    · apply hlocal _ htrace.1
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorLeftBoundaryPoint,
            OneSidedCircularCap.leftEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorLeftBoundaryPoint,
            OneSidedCircularCap.rightEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
  · have hcircle :
        CMVFigureFour.circleValue b.cap.center g.sourceRadius
          (b.exteriorRightBoundaryPoint y) = 0 := by
      have hc := htrace.2.1
      unfold CMVFigureFour.circleValue OneSidedCircularCap.radiusSquaredAt at *
      rw [b.cap_radius] at hc
      nlinarith
    apply
      CMVFigureFour.circlePoint_mem_frontier_horizontalSection_of_localOneSided
        hcircle
    · unfold CappedInterface.exteriorRightBoundaryPoint
      dsimp only
      linarith
    · apply hlocal _ htrace.2
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorRightBoundaryPoint,
            OneSidedCircularCap.leftEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
      · intro heq
        have hyEq : y = b.cap.baseY := by
          simpa [CappedInterface.exteriorRightBoundaryPoint,
            OneSidedCircularCap.rightEndpoint] using congrArg Prod.snd heq
        rw [b.cap_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith

/-- The complete section frontier strictly inside a lower cap consists of its
two transverse circle intersections. -/
theorem frontier_lowerCappedSection_eq_pair
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .capped b)
    {y : ℝ} (hpole : b.cap.center.2 - g.sourceRadius < y)
    (hbase : y < -1) :
    frontier
        (CMVSourceClassification.horizontalSection g.representative y) =
      {(b.exteriorLeftBoundaryPoint y).1,
        (b.exteriorRightBoundaryPoint y).1} := by
  have hknown :=
    g.lowerCappedBoundaryPoints_mem_section_frontier b hBoundary hpole hbase
  have hcenter := b.lower_interface_lt_center g.density_jump
  have hdiffNeg : -g.sourceRadius < y - b.cap.center.2 := by linarith
  have hdiffLt : y - b.cap.center.2 < 0 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  apply Set.Subset.antisymm
  · intro x hx
    have hplane :=
      CMVSourceClassification.frontier_horizontalSection_subset
        g.representative y hx
    rw [g.frontier_eq_components] at hplane
    rcases hplane with hleft | hright | hupper | hlower
    · have hyBound := hleft.2.1
      rw [abs_of_neg (lt_trans hbase (by norm_num))] at hyBound
      linarith
    · have hyBound := hright.2.1
      rw [abs_of_neg (lt_trans hbase (by norm_num))] at hyBound
      linarith
    · have hyBound := g.upperBoundary.trace_second_ge_one hupper
      linarith
    · rw [hBoundary] at hlower
      change (x, y) ∈ b.leftSegment.carrier ∪
        (b.cap.arcTrace ∪ b.rightSegment.carrier) at hlower
      rcases hlower with hsegment | hcap | hsegment
      · have hyEq := hsegment.1
        rw [b.left_segment_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
      · exact b.arcTrace_abscissa_eq_left_or_right hrad.le hcap
      · have hyEq := hsegment.1
        rw [b.right_segment_base] at hyEq
        simp only [interfaceY] at hyEq
        linarith
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst x
      exact hknown.1
    · subst x
      exact hknown.2

/-- Every representative section strictly between a lower cap pole and its
interface is exactly the open circle interval. -/
theorem actual_lowerCappedSection
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .capped b)
    {y : ℝ} (hpole : b.cap.center.2 - g.sourceRadius < y)
    (hbase : y < -1) :
    CMVSourceClassification.horizontalSection g.representative y =
      Ioo ((b.exteriorLeftBoundaryPoint y).1)
        ((b.exteriorRightBoundaryPoint y).1) := by
  have hcenter := b.lower_interface_lt_center g.density_jump
  have hdiffNeg : -g.sourceRadius < y - b.cap.center.2 := by linarith
  have hdiffLt : y - b.cap.center.2 < 0 := by linarith
  have hrad :
      0 < g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2 := by
    nlinarith
  have horder :
      (b.exteriorLeftBoundaryPoint y).1 <
        (b.exteriorRightBoundaryPoint y).1 := by
    have hroot :
        0 < √(g.sourceRadius ^ 2 - (y - b.cap.center.2) ^ 2) :=
      Real.sqrt_pos.2 hrad
    unfold CappedInterface.exteriorLeftBoundaryPoint
      CappedInterface.exteriorRightBoundaryPoint
    dsimp only
    linarith
  exact CMVSourceClassification.IsOpen.eq_Ioo_of_isBounded_frontier_eq_pair
    (CMVSourceClassification.isOpen_horizontalSection
      g.sourceRepresentative.representative_open y)
    (CMVSourceClassification.isBounded_horizontalSection
      g.sourceRepresentative.representative_bounded y)
    horder
    (g.frontier_lowerCappedSection_eq_pair b hBoundary hpole hbase)

/-- An exposed lower interface has no representative section at any exterior
height. -/
theorem actual_lowerExposedSection_empty
    (b : ExposedInterface g.leftStripCenter.1
      g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .exposed b)
    {y : ℝ} (hbase : y < -1) :
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  apply g.actualSection_eq_empty_of_frontier_eq_empty y
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hplane :=
    CMVSourceClassification.frontier_horizontalSection_subset
      g.representative y hx
  rw [g.frontier_eq_components] at hplane
  rcases hplane with hleft | hright | hupper | hlower
  · have hyBound := hleft.2.1
    rw [abs_of_neg (lt_trans hbase (by norm_num))] at hyBound
    linarith
  · have hyBound := hright.2.1
    rw [abs_of_neg (lt_trans hbase (by norm_num))] at hyBound
    linarith
  · have hyBound := g.upperBoundary.trace_second_ge_one hupper
    linarith
  · rw [hBoundary] at hlower
    change (x, y) ∈ b.segment.carrier at hlower
    have hyEq := hlower.1
    rw [b.segment_base] at hyEq
    simp only [interfaceY] at hyEq
    linarith

/-- Below a lower cap's supporting-circle pole the representative section is
empty.  The tangent height itself belongs to the finite exceptional set. -/
theorem actual_lowerCappedSection_empty_below
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .capped b)
    {y : ℝ} (hpole : y < b.cap.center.2 - g.sourceRadius)
    (hbase : y < -1) :
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  apply g.actualSection_eq_empty_of_frontier_eq_empty y
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hplane :=
    CMVSourceClassification.frontier_horizontalSection_subset
      g.representative y hx
  rw [g.frontier_eq_components] at hplane
  rcases hplane with hleft | hright | hupper | hlower
  · have hyBound := hleft.2.1
    rw [abs_of_neg (lt_trans hbase (by norm_num))] at hyBound
    linarith
  · have hyBound := hright.2.1
    rw [abs_of_neg (lt_trans hbase (by norm_num))] at hyBound
    linarith
  · have hyBound := g.upperBoundary.trace_second_ge_one hupper
    linarith
  · rw [hBoundary] at hlower
    change (x, y) ∈ b.leftSegment.carrier ∪
      (b.cap.arcTrace ∪ b.rightSegment.carrier) at hlower
    rcases hlower with hsegment | hcap | hsegment
    · have hyEq := hsegment.1
      rw [b.left_segment_base] at hyEq
      simp only [interfaceY] at hyEq
      linarith
    · have hcircle := hcap.1
      change b.cap.radiusSquaredAt (x, y) = b.cap.radius ^ 2 at hcircle
      unfold OneSidedCircularCap.radiusSquaredAt at hcircle
      rw [b.cap_radius] at hcircle
      dsimp only at hcircle
      have hdiff : y - b.cap.center.2 < -g.sourceRadius := by linarith
      nlinarith [sq_nonneg (x - b.cap.center.1), g.sourceRadius_pos]
    · have hyEq := hsegment.1
      rw [b.right_segment_base] at hyEq
      simp only [interfaceY] at hyEq
      linarith


/-- Complete reconstruction of every nonexceptional upper exterior section.
The capped alternative retains the cap's actual independent horizontal
placement; every other upper-exterior section is empty. -/
theorem actual_upperExteriorSection
    {y : ℝ} (hbase : 1 < y)
    (hyExceptional : y ∉ g.exteriorExceptionalHeights) :
    (∃ b : CappedInterface lam g.sourceRadius
        g.leftStripCenter.1 g.rightStripCenter.1 .upper,
      g.upperBoundary = .capped b ∧
      y < b.cap.center.2 + g.sourceRadius ∧
      CMVSourceClassification.horizontalSection g.representative y =
        Ioo ((b.exteriorLeftBoundaryPoint y).1)
          ((b.exteriorRightBoundaryPoint y).1)) ∨
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  cases hBoundary : g.upperBoundary with
  | exposed b =>
      exact Or.inr (g.actual_upperExposedSection_empty b hBoundary hbase)
  | capped b =>
      by_cases hpole : y < b.cap.center.2 + g.sourceRadius
      · exact Or.inl ⟨b, rfl, hpole,
          g.actual_upperCappedSection b hBoundary hbase hpole⟩
      · right
        apply g.actual_upperCappedSection_empty_above b hBoundary hbase
        have hne : y ≠ b.cap.center.2 + g.sourceRadius := by
          intro heq
          apply hyExceptional
          rw [heq]
          simp [exteriorExceptionalHeights, hBoundary,
            InterfaceBoundary.tangentHeights]
        exact lt_of_le_of_ne (le_of_not_gt hpole) hne.symm

/-- Complete reconstruction of every nonexceptional lower exterior section.
The capped alternative retains the cap's actual independent horizontal
placement; every other lower-exterior section is empty. -/
theorem actual_lowerExteriorSection
    {y : ℝ} (hbase : y < -1)
    (hyExceptional : y ∉ g.exteriorExceptionalHeights) :
    (∃ b : CappedInterface lam g.sourceRadius
        g.leftStripCenter.1 g.rightStripCenter.1 .lower,
      g.lowerBoundary = .capped b ∧
      b.cap.center.2 - g.sourceRadius < y ∧
      CMVSourceClassification.horizontalSection g.representative y =
        Ioo ((b.exteriorLeftBoundaryPoint y).1)
          ((b.exteriorRightBoundaryPoint y).1)) ∨
    CMVSourceClassification.horizontalSection g.representative y = ∅ := by
  cases hBoundary : g.lowerBoundary with
  | exposed b =>
      exact Or.inr (g.actual_lowerExposedSection_empty b hBoundary hbase)
  | capped b =>
      by_cases hpole : b.cap.center.2 - g.sourceRadius < y
      · exact Or.inl ⟨b, rfl, hpole,
          g.actual_lowerCappedSection b hBoundary hpole hbase⟩
      · right
        apply g.actual_lowerCappedSection_empty_below b hBoundary
        · have hne : y ≠ b.cap.center.2 - g.sourceRadius := by
            intro heq
            apply hyExceptional
            rw [heq]
            simp [exteriorExceptionalHeights, hBoundary,
              InterfaceBoundary.tangentHeights]
          exact lt_of_le_of_ne (le_of_not_gt hpole) hne
        · exact hbase
/-- Planar almost-everywhere source agreement descends to almost every
horizontal section. -/
theorem sourceCarrier_ae_representative_sections :
    ∀ᵐ y ∂(volume : Measure ℝ),
      CMVSourceClassification.horizontalSection g.sourceCarrier y
        =ᵐ[volume]
      CMVSourceClassification.horizontalSection g.representative y := by
  have hsource := g.sourceRepresentative.source_ae_representative
  rw [Measure.volume_eq_prod] at hsource
  have hswap :
      Filter.Tendsto Prod.swap (ae (volume.prod volume))
        (ae (volume.prod volume)) :=
    (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae
  have hsourceSwap :
      (fun p : ℝ × ℝ => g.sourceCarrier p.swap)
          =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => g.representative p.swap) :=
    hsource.comp_tendsto hswap
  filter_upwards [Measure.ae_ae_eq_curry_of_prod hsourceSwap] with y hy
  filter_upwards [hy] with x hx
  change ((x, y) ∈ g.sourceCarrier) = ((x, y) ∈ g.representative)
  exact hx

/-- Consequently, almost every strict-strip section of the actual source
carrier is the derived open interval.  The interface heights are not asserted
pointwise and remain irrelevant to planar measure. -/
theorem ae_sourceCarrier_strictStripSection :
    ∀ᵐ y ∂(volume : Measure ℝ), |y| < 1 →
      CMVSourceClassification.horizontalSection g.sourceCarrier y
        =ᵐ[volume]
      Ioo ((g.leftStripBoundaryPoint y).1)
        ((g.rightStripBoundaryPoint y).1) := by
  filter_upwards [g.sourceCarrier_ae_representative_sections] with y hy hyStrip
  rw [g.actual_strictStripSection hyStrip] at hy
  exact hy

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
