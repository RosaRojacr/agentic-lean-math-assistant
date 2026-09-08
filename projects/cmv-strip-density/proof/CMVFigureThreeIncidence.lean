/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureThreeNonfit

/-!
# Independent source incidence for CMV Figure 3

This is the source-facing signature for Lemma 3.8 Step 1 (printed pages 15--16,
Figure 3 and equation (23)).  It records circles, endpoints, tangencies,
possibly degenerate interface segments, vertical symmetry, and signed Snell
data.  It deliberately does not contain a `TypeThreeAssembly`, a carrier
normalization, an available-width formula, a chord comparison, or a non-fit
conclusion.

Both vertical orientations are represented.  The half-angle fields of
`OneSidedCircularCap` retain the complete `(0, pi)` range, so the primary
exterior arc is not restricted to the minor branch.  `sourceRadius = 1` is
allowed and remains the separate Figure-5 boundary; strict-radius elimination
will require an additional `1 < sourceRadius` hypothesis.
-/

open Set
open Real

noncomputable section

namespace CMVFigureThree

/-- Which exterior component starts the Figure-3 continuation.  The second
constructor is the reflection of the pictured upper-primary configuration. -/
inductive VerticalOrientation where
  | upperPrimary
  | lowerPrimary
  deriving DecidableEq, Repr

namespace VerticalOrientation

/-- Signed vertical direction from the strip core toward the primary exterior
arc. -/
def sign : VerticalOrientation → ℝ
  | .upperPrimary => 1
  | .lowerPrimary => -1

/-- Side occupied by the primary exterior cap. -/
def primaryCapSide : VerticalOrientation → CapSide
  | .upperPrimary => .upper
  | .lowerPrimary => .lower

/-- Side occupied by the added, opposite exterior cap. -/
def addedCapSide : VerticalOrientation → CapSide
  | .upperPrimary => .lower
  | .lowerPrimary => .upper

/-- Primary strip interface, `1` in the pictured orientation and `-1` after
vertical reflection. -/
def primaryInterfaceY (o : VerticalOrientation) : ℝ := o.sign

/-- Tangency interface carrying the two possibly degenerate segments. -/
def tangentInterfaceY (o : VerticalOrientation) : ℝ := -o.sign

end VerticalOrientation

/-- A literal closed horizontal segment which may degenerate to one point.
`HorizontalSegment` is intentionally not used because it requires positive
length. -/
structure DegenerateHorizontalSegment where
  leftX : ℝ
  rightX : ℝ
  baseY : ℝ
  left_le_right : leftX ≤ rightX

namespace DegenerateHorizontalSegment

/-- Coordinate carrier of a possibly degenerate interface segment. -/
def carrier (s : DegenerateHorizontalSegment) : Set PlanePoint :=
  {p | p.2 = s.baseY ∧ s.leftX ≤ p.1 ∧ p.1 ≤ s.rightX}

end DegenerateHorizontalSegment

/-- Primitive source geometry for the Figure-3 branch.

The two segment endpoint equalities and their internal orders encode actual
boundary incidence.  They imply that the added cap chord lies between the two
strip-side tangencies, but that containment is not a field.  The signed Snell
equation uses the oriented vertical radial component and therefore remains
valid when the common-radius primary cap crosses its major branch. -/
structure SourceIncidence (lam : ℝ) where
  orientation : VerticalOrientation
  sourceRadius : ℝ
  symmetryAxisX : ℝ
  primaryExterior : OneSidedCircularCap
  addedExterior : OneSidedCircularCap
  leftStripCenter : PlanePoint
  rightStripCenter : PlanePoint
  primaryLeft : PlanePoint
  primaryRight : PlanePoint
  tangentLeft : PlanePoint
  tangentRight : PlanePoint
  leftInterfaceSegment : DegenerateHorizontalSegment
  rightInterfaceSegment : DegenerateHorizontalSegment
  density_jump : 1 < lam
  radius_ge_one : 1 ≤ sourceRadius
  primary_side : primaryExterior.side = orientation.primaryCapSide
  primary_base : primaryExterior.baseY = orientation.primaryInterfaceY
  added_side : addedExterior.side = orientation.addedCapSide
  added_base : addedExterior.baseY = orientation.tangentInterfaceY
  primary_radius : primaryExterior.radius = sourceRadius
  added_radius : addedExterior.radius = sourceRadius
  primary_midpoint : primaryExterior.midpointX = symmetryAxisX
  primary_left_endpoint : primaryLeft = primaryExterior.leftEndpoint
  primary_right_endpoint : primaryRight = primaryExterior.rightEndpoint
  centers_symmetric_x :
    leftStripCenter.1 + rightStripCenter.1 = 2 * symmetryAxisX
  centers_same_y : leftStripCenter.2 = rightStripCenter.2
  primary_endpoints_symmetric_x :
    primaryLeft.1 + primaryRight.1 = 2 * symmetryAxisX
  primary_left_on_circle :
    (primaryLeft.1 - leftStripCenter.1) ^ 2 +
        (primaryLeft.2 - leftStripCenter.2) ^ 2 = sourceRadius ^ 2
  primary_right_on_circle :
    (primaryRight.1 - rightStripCenter.1) ^ 2 +
        (primaryRight.2 - rightStripCenter.2) ^ 2 = sourceRadius ^ 2
  primary_left_outward : primaryLeft.1 ≤ leftStripCenter.1
  primary_right_outward : rightStripCenter.1 ≤ primaryRight.1
  tangent_left_coordinate :
    tangentLeft =
      (leftStripCenter.1, orientation.tangentInterfaceY)
  tangent_right_coordinate :
    tangentRight =
      (rightStripCenter.1, orientation.tangentInterfaceY)
  left_center_tangency_coordinate :
    leftStripCenter.2 =
      orientation.tangentInterfaceY + orientation.sign * sourceRadius
  right_center_tangency_coordinate :
    rightStripCenter.2 =
      orientation.tangentInterfaceY + orientation.sign * sourceRadius
  primary_left_interface : primaryLeft.2 = orientation.primaryInterfaceY
  primary_right_interface : primaryRight.2 = orientation.primaryInterfaceY
  left_segment_base :
    leftInterfaceSegment.baseY = orientation.tangentInterfaceY
  right_segment_base :
    rightInterfaceSegment.baseY = orientation.tangentInterfaceY
  left_segment_starts_at_tangency :
    leftInterfaceSegment.leftX = tangentLeft.1
  left_segment_ends_at_added_cap :
    leftInterfaceSegment.rightX = addedExterior.leftEndpoint.1
  right_segment_starts_at_added_cap :
    rightInterfaceSegment.leftX = addedExterior.rightEndpoint.1
  right_segment_ends_at_tangency :
    rightInterfaceSegment.rightX = tangentRight.1
  primary_signed_snell :
    lam * cos primaryExterior.theta =
      orientation.sign *
        (primaryLeft.2 - leftStripCenter.2) / sourceRadius
  added_contact_law : lam * cos addedExterior.theta = 1

end CMVFigureThree
