/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureThreeContainment

/-!
# Actual-boundary realization for CMV Figure 3

This source-facing signature starts with an actual planar representative and a
literal decomposition of its topological frontier into two exterior circular
traces, two strip-side circular traces, and the two possibly degenerate
interface segments.  Its coordinate and incidence data derive
`SourceIncidence`; no type-(iii) assembly, normalized carrier, available-width
identity, chord containment, comparison, or contradiction is a premise.

The geometric extraction from a regular source minimizer into this signature is
still an upstream classification obligation.
-/

open Set
open Real

noncomputable section

namespace CMVFigureThree

namespace ActualBoundaryRealization

/-- Center of a strip-side source circle with tangency abscissa `x`. -/
def stripCenter (o : VerticalOrientation) (R x : ℝ) : PlanePoint :=
  (x, o.tangentInterfaceY + o.sign * R)

/-- The actual left strip-side circular trace between the strip interfaces. -/
def leftStripArcTrace (o : VerticalOrientation) (R x : ℝ) : Set PlanePoint :=
  {p | (p.1 - (stripCenter o R x).1) ^ 2 +
      (p.2 - (stripCenter o R x).2) ^ 2 = R ^ 2 ∧
    p.1 ≤ x ∧ |p.2| ≤ 1}

/-- The actual right strip-side circular trace between the strip interfaces. -/
def rightStripArcTrace (o : VerticalOrientation) (R x : ℝ) : Set PlanePoint :=
  {p | (p.1 - (stripCenter o R x).1) ^ 2 +
      (p.2 - (stripCenter o R x).2) ^ 2 = R ^ 2 ∧
    x ≤ p.1 ∧ |p.2| ≤ 1}

/-- Literal closed horizontal trace; endpoint equality permits degeneration. -/
def interfaceTrace (leftX rightX baseY : ℝ) : Set PlanePoint :=
  {p | p.2 = baseY ∧ leftX ≤ p.1 ∧ p.1 ≤ rightX}

/-- The six source pieces asserted to form the actual representative's complete
frontier in the Figure-3 configuration. -/
def boundaryTrace (o : VerticalOrientation) (R : ℝ)
    (primary added : OneSidedCircularCap) (leftX rightX : ℝ) : Set PlanePoint :=
  primary.arcTrace ∪
    (leftStripArcTrace o R leftX ∪
      (rightStripArcTrace o R rightX ∪
        (added.arcTrace ∪
          (interfaceTrace leftX added.leftEndpoint.1 o.tangentInterfaceY ∪
            interfaceTrace added.rightEndpoint.1 rightX
              o.tangentInterfaceY))))

end ActualBoundaryRealization

/-- Independent realization of the Figure-3 geometry on an actual planar
representative.  The endpoint orders are primitive boundary incidence; the
chord containment they imply is deliberately absent. -/
structure ActualBoundaryRealization (lam : ℝ) where
  carrier : Set PlanePoint
  orientation : VerticalOrientation
  sourceRadius : ℝ
  symmetryAxisX : ℝ
  primaryExterior : OneSidedCircularCap
  addedExterior : OneSidedCircularCap
  leftTangentX : ℝ
  rightTangentX : ℝ
  density_jump : 1 < lam
  radius_ge_one : 1 ≤ sourceRadius
  primary_side : primaryExterior.side = orientation.primaryCapSide
  primary_base : primaryExterior.baseY = orientation.primaryInterfaceY
  added_side : addedExterior.side = orientation.addedCapSide
  added_base : addedExterior.baseY = orientation.tangentInterfaceY
  primary_radius : primaryExterior.radius = sourceRadius
  added_radius : addedExterior.radius = sourceRadius
  primary_midpoint : primaryExterior.midpointX = symmetryAxisX
  tangent_abscissae_symmetric :
    leftTangentX + rightTangentX = 2 * symmetryAxisX
  primary_left_on_left_trace :
    primaryExterior.leftEndpoint ∈
      ActualBoundaryRealization.leftStripArcTrace
        orientation sourceRadius leftTangentX
  primary_right_on_right_trace :
    primaryExterior.rightEndpoint ∈
      ActualBoundaryRealization.rightStripArcTrace
        orientation sourceRadius rightTangentX
  left_segment_order :
    leftTangentX ≤ addedExterior.leftEndpoint.1
  right_segment_order :
    addedExterior.rightEndpoint.1 ≤ rightTangentX
  primary_signed_snell :
    lam * cos primaryExterior.theta =
      orientation.sign *
        (primaryExterior.leftEndpoint.2 -
          (ActualBoundaryRealization.stripCenter
            orientation sourceRadius leftTangentX).2) / sourceRadius
  added_contact_law : lam * cos addedExterior.theta = 1
  frontier_eq_boundaryTrace :
    frontier carrier =
      ActualBoundaryRealization.boundaryTrace orientation sourceRadius
        primaryExterior addedExterior leftTangentX rightTangentX

namespace ActualBoundaryRealization

variable {lam : ℝ} (b : ActualBoundaryRealization lam)

/-- The left interface segment extracted from its literal source endpoints. -/
def leftInterfaceSegment : DegenerateHorizontalSegment where
  leftX := b.leftTangentX
  rightX := b.addedExterior.leftEndpoint.1
  baseY := b.orientation.tangentInterfaceY
  left_le_right := b.left_segment_order

/-- The right interface segment extracted from its literal source endpoints. -/
def rightInterfaceSegment : DegenerateHorizontalSegment where
  leftX := b.addedExterior.rightEndpoint.1
  rightX := b.rightTangentX
  baseY := b.orientation.tangentInterfaceY
  left_le_right := b.right_segment_order

/-- Field-by-field extraction of independent boundary geometry into the checked
incidence interface.  Circle equations and outward inequalities come from
membership in the actual side traces; endpoint, center, and segment equalities
come from the literal coordinate definitions. -/
def toSourceIncidence : SourceIncidence lam where
  orientation := b.orientation
  sourceRadius := b.sourceRadius
  symmetryAxisX := b.symmetryAxisX
  primaryExterior := b.primaryExterior
  addedExterior := b.addedExterior
  leftStripCenter := stripCenter b.orientation b.sourceRadius b.leftTangentX
  rightStripCenter := stripCenter b.orientation b.sourceRadius b.rightTangentX
  primaryLeft := b.primaryExterior.leftEndpoint
  primaryRight := b.primaryExterior.rightEndpoint
  tangentLeft := (b.leftTangentX, b.orientation.tangentInterfaceY)
  tangentRight := (b.rightTangentX, b.orientation.tangentInterfaceY)
  leftInterfaceSegment := b.leftInterfaceSegment
  rightInterfaceSegment := b.rightInterfaceSegment
  density_jump := b.density_jump
  radius_ge_one := b.radius_ge_one
  primary_side := b.primary_side
  primary_base := b.primary_base
  added_side := b.added_side
  added_base := b.added_base
  primary_radius := b.primary_radius
  added_radius := b.added_radius
  primary_midpoint := b.primary_midpoint
  primary_left_endpoint := rfl
  primary_right_endpoint := rfl
  centers_symmetric_x := by
    simpa [stripCenter] using b.tangent_abscissae_symmetric
  centers_same_y := rfl
  primary_endpoints_symmetric_x := by
    rw [OneSidedCircularCap.leftEndpoint,
      OneSidedCircularCap.rightEndpoint]
    simp only
    rw [b.primary_midpoint]
    ring
  primary_left_on_circle := by
    simpa [leftStripArcTrace, stripCenter] using
      b.primary_left_on_left_trace.1
  primary_right_on_circle := by
    simpa [rightStripArcTrace, stripCenter] using
      b.primary_right_on_right_trace.1
  primary_left_outward := by
    simpa [leftStripArcTrace, stripCenter] using
      b.primary_left_on_left_trace.2.1
  primary_right_outward := by
    simpa [rightStripArcTrace, stripCenter] using
      b.primary_right_on_right_trace.2.1
  tangent_left_coordinate := rfl
  tangent_right_coordinate := rfl
  left_center_tangency_coordinate := rfl
  right_center_tangency_coordinate := rfl
  primary_left_interface := by
    simpa [OneSidedCircularCap.leftEndpoint] using b.primary_base
  primary_right_interface := by
    simpa [OneSidedCircularCap.rightEndpoint] using b.primary_base
  left_segment_base := rfl
  right_segment_base := rfl
  left_segment_starts_at_tangency := rfl
  left_segment_ends_at_added_cap := rfl
  right_segment_starts_at_added_cap := rfl
  right_segment_ends_at_tangency := rfl
  primary_signed_snell := b.primary_signed_snell
  added_contact_law := b.added_contact_law

/-- The extracted incidence retains the exact source radius. -/
@[simp] theorem toSourceIncidence_sourceRadius :
    b.toSourceIncidence.sourceRadius = b.sourceRadius := rfl

/-- The extracted incidence retains the exact actual added cap. -/
@[simp] theorem toSourceIncidence_addedExterior :
    b.toSourceIncidence.addedExterior = b.addedExterior := rfl

/-- The source frontier premise names exactly the six pieces used by the
extraction, rather than an unrelated carrier. -/
theorem actual_frontier_eq_boundaryTrace :
    frontier b.carrier =
      boundaryTrace b.orientation b.sourceRadius b.primaryExterior
        b.addedExterior b.leftTangentX b.rightTangentX :=
  b.frontier_eq_boundaryTrace

/-- The primary exterior trace is literally part of the actual frontier. -/
theorem primaryExterior_arcTrace_subset_frontier :
    b.primaryExterior.arcTrace ⊆ frontier b.carrier := by
  rw [b.actual_frontier_eq_boundaryTrace]
  intro p hp
  exact Or.inl hp

/-- The left strip-side circle is literally part of the actual frontier. -/
theorem leftStripArcTrace_subset_frontier :
    leftStripArcTrace b.orientation b.sourceRadius b.leftTangentX ⊆
      frontier b.carrier := by
  rw [b.actual_frontier_eq_boundaryTrace]
  intro p hp
  exact Or.inr (Or.inl hp)

/-- The right strip-side circle is literally part of the actual frontier. -/
theorem rightStripArcTrace_subset_frontier :
    rightStripArcTrace b.orientation b.sourceRadius b.rightTangentX ⊆
      frontier b.carrier := by
  rw [b.actual_frontier_eq_boundaryTrace]
  intro p hp
  exact Or.inr (Or.inr (Or.inl hp))

/-- The added exterior trace is literally part of the actual frontier. -/
theorem addedExterior_arcTrace_subset_frontier :
    b.addedExterior.arcTrace ⊆ frontier b.carrier := by
  rw [b.actual_frontier_eq_boundaryTrace]
  intro p hp
  exact Or.inr (Or.inr (Or.inr (Or.inl hp)))

/-- The possibly degenerate left interface is literally part of the actual
frontier. -/
theorem leftInterfaceTrace_subset_frontier :
    interfaceTrace b.leftTangentX b.addedExterior.leftEndpoint.1
        b.orientation.tangentInterfaceY ⊆ frontier b.carrier := by
  rw [b.actual_frontier_eq_boundaryTrace]
  intro p hp
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hp))))

/-- The possibly degenerate right interface is literally part of the actual
frontier. -/
theorem rightInterfaceTrace_subset_frontier :
    interfaceTrace b.addedExterior.rightEndpoint.1 b.rightTangentX
        b.orientation.tangentInterfaceY ⊆ frontier b.carrier := by
  rw [b.actual_frontier_eq_boundaryTrace]
  intro p hp
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hp))))

/-- The primary-left circle incidence used by `toSourceIncidence` is an
incidence point of the literal actual frontier. -/
theorem primaryLeft_mem_frontier :
    b.primaryExterior.leftEndpoint ∈ frontier b.carrier :=
  b.leftStripArcTrace_subset_frontier b.primary_left_on_left_trace

/-- The primary-right circle incidence used by `toSourceIncidence` is an
incidence point of the literal actual frontier. -/
theorem primaryRight_mem_frontier :
    b.primaryExterior.rightEndpoint ∈ frontier b.carrier :=
  b.rightStripArcTrace_subset_frontier b.primary_right_on_right_trace

/-- Every strict-radius actual Figure-3 boundary realization is impossible. -/
theorem strictRadius_false (hR : 1 < b.sourceRadius) : False :=
  b.toSourceIncidence.strictRadius_false hR

/-- Any actual boundary realization admitted by the closed-radius signature
leaves exactly the separate radius-one residual. -/
theorem sourceRadius_eq_one : b.sourceRadius = 1 := by
  simpa using b.toSourceIncidence.sourceRadius_eq_one

end ActualBoundaryRealization

end CMVFigureThree
