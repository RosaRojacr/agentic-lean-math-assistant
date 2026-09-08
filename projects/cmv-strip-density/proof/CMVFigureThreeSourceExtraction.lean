/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureThreeBoundaryRealization

/-!
# Source-located extraction of the CMV Figure 3 boundary

This file separates the inputs supplied by the source classification argument:
regular Snell data, vertical reflection symmetry, circular continuation, one
closed source boundary curve, and the subsequent Figure-3 branch selection.
The branch's five cuts and pointwise trace characterizations kernel-derive the
six exact component images; its two non-strict endpoint orders construct both
possibly degenerate interface segments and their incidence data.  These outputs
then produce the pointwise Figure-3 enumeration and an
`ActualBoundaryRealization` on the literal source carrier.

The configuration does not contain a type-(iii) assembly, a normalized carrier,
a width formula, chord containment, or a comparison conclusion.  Deriving the
closed boundary curve, Figure-3 branch selection, and remaining local data from
every regular source minimizer remains upstream.
-/

open Set
open Real

noncomputable section

namespace CMVFigureThree

namespace SourceBoundaryExtraction

/-- Regularity and the two source Snell laws for the common-radius Figure-3
continuation.  These are the local conclusions of first variation and regular
trace, not a model-side normalization. -/
structure RegularSnellData (lam : ℝ) (o : VerticalOrientation) (R : ℝ)
    (primary added : OneSidedCircularCap) : Prop where
  density_jump : 1 < lam
  radius_ge_one : 1 ≤ R
  primary_side : primary.side = o.primaryCapSide
  primary_base : primary.baseY = o.primaryInterfaceY
  added_side : added.side = o.addedCapSide
  added_base : added.baseY = o.tangentInterfaceY
  primary_radius : primary.radius = R
  added_radius : added.radius = R
  primary_signed_snell :
    lam * cos primary.theta =
      o.sign *
        (primary.leftEndpoint.2 -
          (o.tangentInterfaceY + o.sign * R)) / R
  added_contact_law : lam * cos added.theta = 1

/-- Vertical reflective symmetry from CMV Proposition 3.9, expressed only on
actual source coordinates. -/
structure VerticalSymmetryData (o : VerticalOrientation)
    (primary : OneSidedCircularCap) (axisX leftTangentX rightTangentX : ℝ) :
    Prop where
  primary_midpoint : primary.midpointX = axisX
  tangent_abscissae_symmetric :
    leftTangentX + rightTangentX = 2 * axisX

/-- Equal-curvature continuation from the primary exterior arc through the two
strip-side arcs.  Circle incidence and outward branch selection are primitive;
membership in the concrete side traces is derived below. -/
structure CircularContinuationData (o : VerticalOrientation) (R : ℝ)
    (primary : OneSidedCircularCap) (leftTangentX rightTangentX : ℝ) : Prop where
  primary_left_on_circle :
    (primary.leftEndpoint.1 -
        (ActualBoundaryRealization.stripCenter o R leftTangentX).1) ^ 2 +
      (primary.leftEndpoint.2 -
        (ActualBoundaryRealization.stripCenter o R leftTangentX).2) ^ 2 = R ^ 2
  primary_right_on_circle :
    (primary.rightEndpoint.1 -
        (ActualBoundaryRealization.stripCenter o R rightTangentX).1) ^ 2 +
      (primary.rightEndpoint.2 -
        (ActualBoundaryRealization.stripCenter o R rightTangentX).2) ^ 2 = R ^ 2
  primary_left_outward : primary.leftEndpoint.1 ≤ leftTangentX
  primary_right_outward : rightTangentX ≤ primary.rightEndpoint.1

/-- Regularity of one closed parameter interval of the source boundary curve.
The derivative condition is imposed only on the relative interior, so a
degenerate interface interval is allowed. -/
def IsRegularTracePiece (trace : ℝ → PlanePoint) (a b : ℝ) : Prop :=
  ContDiffOn ℝ 1 trace (Icc a b) ∧
    ∀ t ∈ Ioo a b, ∃ velocity : PlanePoint,
      HasDerivAt trace velocity t ∧ velocity ≠ 0

/-- One actual closed parameterization of a source representative's complete
topological frontier, before selecting a Lemma 3.8 configuration.  Piecewise
regularity and the geometric labels of its subintervals are deliberately not
part of this source-level object. -/
structure ClosedBoundaryTrace (carrier : Set PlanePoint) where
  trace : ℝ → PlanePoint
  start : ℝ
  finish : ℝ
  start_le_finish : start ≤ finish
  trace_closed : trace start = trace finish
  complete_image : trace '' Icc start finish = frontier carrier

/-- Endpoint incidence for the two horizontal Figure-3 interface pieces.
This record contains no boundary-exhaustion assertion. -/
structure InterfaceIncidenceData (o : VerticalOrientation)
    (added : OneSidedCircularCap) (leftTangentX rightTangentX : ℝ)
    (leftInterface rightInterface : DegenerateHorizontalSegment) : Prop where
  left_base : leftInterface.baseY = o.tangentInterfaceY
  right_base : rightInterface.baseY = o.tangentInterfaceY
  left_starts_at_tangency : leftInterface.leftX = leftTangentX
  left_ends_at_added_cap : leftInterface.rightX = added.leftEndpoint.1
  right_starts_at_added_cap : rightInterface.leftX = added.rightEndpoint.1
  right_ends_at_tangency : rightInterface.rightX = rightTangentX

/-- The two non-strict endpoint orders selected by the Figure-3 branch.
The actual interface segments are constructed from these inequalities instead
of being supplied with six separately repeated coordinate fields. -/
structure InterfaceEndpointOrder (added : OneSidedCircularCap)
    (leftTangentX rightTangentX : ℝ) : Prop where
  left_order : leftTangentX ≤ added.leftEndpoint.1
  right_order : added.rightEndpoint.1 ≤ rightTangentX

namespace InterfaceEndpointOrder

variable {added : OneSidedCircularCap} {leftTangentX rightTangentX : ℝ}
    (d : InterfaceEndpointOrder added leftTangentX rightTangentX)

/-- The actual possibly degenerate left interface determined by its source
endpoints. -/
def leftInterface (o : VerticalOrientation) : DegenerateHorizontalSegment where
  leftX := leftTangentX
  rightX := added.leftEndpoint.1
  baseY := o.tangentInterfaceY
  left_le_right := d.left_order

/-- The actual possibly degenerate right interface determined by its source
endpoints. -/
def rightInterface (o : VerticalOrientation) : DegenerateHorizontalSegment where
  leftX := added.rightEndpoint.1
  rightX := rightTangentX
  baseY := o.tangentInterfaceY
  left_le_right := d.right_order

/-- Constructing the interface pieces from their ordered source endpoints
derives the complete endpoint-incidence record definitionally. -/
theorem toInterfaceIncidenceData (o : VerticalOrientation) :
    InterfaceIncidenceData o added leftTangentX rightTangentX
      (d.leftInterface o) (d.rightInterface o) where
  left_base := rfl
  right_base := rfl
  left_starts_at_tangency := rfl
  left_ends_at_added_cap := rfl
  right_starts_at_added_cap := rfl
  right_ends_at_tangency := rfl

end InterfaceEndpointOrder

/-- Source-faithful piecewise-regular boundary output of the Figure-3 branch
in CMV Lemma 3.8, Step 1 (printed pages 15--16).

One actual parameterized curve traces the complete topological frontier.  Six
ordered closed parameter intervals have images equal to the two exterior arcs,
the two strip-side arcs, and the two possibly degenerate interface segments.
This is upstream of the pointwise configuration enumeration used by the
geometric contradiction. -/
structure PiecewiseRegularBoundaryTrace (carrier : Set PlanePoint)
    (o : VerticalOrientation) (R : ℝ)
    (primary added : OneSidedCircularCap)
    (leftTangentX rightTangentX : ℝ)
    (leftInterface rightInterface : DegenerateHorizontalSegment) where
  trace : ℝ → PlanePoint
  t0 : ℝ
  t1 : ℝ
  t2 : ℝ
  t3 : ℝ
  t4 : ℝ
  t5 : ℝ
  t6 : ℝ
  t0_le_t1 : t0 ≤ t1
  t1_le_t2 : t1 ≤ t2
  t2_le_t3 : t2 ≤ t3
  t3_le_t4 : t3 ≤ t4
  t4_le_t5 : t4 ≤ t5
  t5_le_t6 : t5 ≤ t6
  trace_closed : trace t0 = trace t6
  primary_regular : IsRegularTracePiece trace t0 t1
  right_strip_regular : IsRegularTracePiece trace t1 t2
  right_interface_regular : IsRegularTracePiece trace t2 t3
  added_regular : IsRegularTracePiece trace t3 t4
  left_interface_regular : IsRegularTracePiece trace t4 t5
  left_strip_regular : IsRegularTracePiece trace t5 t6
  primary_image : trace '' Icc t0 t1 = primary.arcTrace
  right_strip_image :
    trace '' Icc t1 t2 =
      ActualBoundaryRealization.rightStripArcTrace o R rightTangentX
  right_interface_image : trace '' Icc t2 t3 = rightInterface.carrier
  added_image : trace '' Icc t3 t4 = added.arcTrace
  left_interface_image : trace '' Icc t4 t5 = leftInterface.carrier
  left_strip_image :
    trace '' Icc t5 t6 =
      ActualBoundaryRealization.leftStripArcTrace o R leftTangentX
  complete_image : trace '' Icc t0 t6 = frontier carrier

/-- Output of selecting the Figure-3 branch on an already existing closed
source boundary trace.  The branch supplies five cuts, regularity on the six
pieces, and pointwise trace characterizations.  The global curve, its closing
condition, and its complete-frontier image remain inherited from
`ClosedBoundaryTrace`. -/
structure FigureThreeBranchSelection (carrier : Set PlanePoint)
    (o : VerticalOrientation) (R : ℝ)
    (primary added : OneSidedCircularCap)
    (leftTangentX rightTangentX : ℝ)
    (boundary : ClosedBoundaryTrace carrier) where
  interfaceOrder : InterfaceEndpointOrder added leftTangentX rightTangentX
  t1 : ℝ
  t2 : ℝ
  t3 : ℝ
  t4 : ℝ
  t5 : ℝ
  start_le_t1 : boundary.start ≤ t1
  t1_le_t2 : t1 ≤ t2
  t2_le_t3 : t2 ≤ t3
  t3_le_t4 : t3 ≤ t4
  t4_le_t5 : t4 ≤ t5
  t5_le_finish : t5 ≤ boundary.finish
  primary_regular :
    IsRegularTracePiece boundary.trace boundary.start t1
  right_strip_regular : IsRegularTracePiece boundary.trace t1 t2
  right_interface_regular : IsRegularTracePiece boundary.trace t2 t3
  added_regular : IsRegularTracePiece boundary.trace t3 t4
  left_interface_regular : IsRegularTracePiece boundary.trace t4 t5
  left_strip_regular :
    IsRegularTracePiece boundary.trace t5 boundary.finish
  primary_trace : ∀ p,
    p ∈ primary.arcTrace ↔
      ∃ t ∈ Icc boundary.start t1, boundary.trace t = p
  right_strip_trace : ∀ p,
    p ∈ ActualBoundaryRealization.rightStripArcTrace o R rightTangentX ↔
      ∃ t ∈ Icc t1 t2, boundary.trace t = p
  right_interface_trace : ∀ p,
    p ∈ (interfaceOrder.rightInterface o).carrier ↔
      ∃ t ∈ Icc t2 t3, boundary.trace t = p
  added_trace : ∀ p,
    p ∈ added.arcTrace ↔
      ∃ t ∈ Icc t3 t4, boundary.trace t = p
  left_interface_trace : ∀ p,
    p ∈ (interfaceOrder.leftInterface o).carrier ↔
      ∃ t ∈ Icc t4 t5, boundary.trace t = p
  left_strip_trace : ∀ p,
    p ∈ ActualBoundaryRealization.leftStripArcTrace o R leftTangentX ↔
      ∃ t ∈ Icc t5 boundary.finish, boundary.trace t = p

namespace FigureThreeBranchSelection

variable {carrier : Set PlanePoint} {o : VerticalOrientation} {R : ℝ}
    {primary added : OneSidedCircularCap}
    {leftTangentX rightTangentX : ℝ}
    {boundary : ClosedBoundaryTrace carrier}
    (branch : FigureThreeBranchSelection carrier o R primary added
      leftTangentX rightTangentX boundary)

private theorem image_eq_of_trace {a z : ℝ} {piece : Set PlanePoint}
    (h : ∀ p, p ∈ piece ↔
      ∃ t ∈ Icc a z, boundary.trace t = p) :
    boundary.trace '' Icc a z = piece := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (h _).2 ⟨t, ht, rfl⟩
  · intro hp
    rcases (h p).1 hp with ⟨t, ht, htp⟩
    exact ⟨t, ht, htp⟩

/-- The branch-local cuts and pointwise characterizations reconstruct the
piecewise trace expected by the geometric extraction. -/
def toPiecewiseRegularBoundaryTrace :
    PiecewiseRegularBoundaryTrace carrier o R primary added
      leftTangentX rightTangentX
      (branch.interfaceOrder.leftInterface o)
      (branch.interfaceOrder.rightInterface o) where
  trace := boundary.trace
  t0 := boundary.start
  t1 := branch.t1
  t2 := branch.t2
  t3 := branch.t3
  t4 := branch.t4
  t5 := branch.t5
  t6 := boundary.finish
  t0_le_t1 := branch.start_le_t1
  t1_le_t2 := branch.t1_le_t2
  t2_le_t3 := branch.t2_le_t3
  t3_le_t4 := branch.t3_le_t4
  t4_le_t5 := branch.t4_le_t5
  t5_le_t6 := branch.t5_le_finish
  trace_closed := boundary.trace_closed
  primary_regular := branch.primary_regular
  right_strip_regular := branch.right_strip_regular
  right_interface_regular := branch.right_interface_regular
  added_regular := branch.added_regular
  left_interface_regular := branch.left_interface_regular
  left_strip_regular := branch.left_strip_regular
  primary_image := image_eq_of_trace branch.primary_trace
  right_strip_image := image_eq_of_trace branch.right_strip_trace
  right_interface_image :=
    image_eq_of_trace branch.right_interface_trace
  added_image := image_eq_of_trace branch.added_trace
  left_interface_image :=
    image_eq_of_trace branch.left_interface_trace
  left_strip_image := image_eq_of_trace branch.left_strip_trace
  complete_image := boundary.complete_image

end FigureThreeBranchSelection

/-- Exhaustive Figure-3 configuration output.  It names the two actual,
possibly degenerate interface traces independently of their endpoint order and
records both directions of the six-piece frontier classification pointwise. -/
structure ConfigurationEnumerationData (carrier : Set PlanePoint)
    (o : VerticalOrientation) (R : ℝ)
    (primary added : OneSidedCircularCap)
    (leftTangentX rightTangentX : ℝ)
    (leftInterface rightInterface : DegenerateHorizontalSegment) : Prop where
  left_base : leftInterface.baseY = o.tangentInterfaceY
  right_base : rightInterface.baseY = o.tangentInterfaceY
  left_starts_at_tangency : leftInterface.leftX = leftTangentX
  left_ends_at_added_cap : leftInterface.rightX = added.leftEndpoint.1
  right_starts_at_added_cap : rightInterface.leftX = added.rightEndpoint.1
  right_ends_at_tangency : rightInterface.rightX = rightTangentX
  frontier_exhaustive : ∀ p ∈ frontier carrier,
    p ∈ primary.arcTrace ∨
      p ∈ ActualBoundaryRealization.leftStripArcTrace o R leftTangentX ∨
      p ∈ ActualBoundaryRealization.rightStripArcTrace o R rightTangentX ∨
      p ∈ added.arcTrace ∨
      p ∈ leftInterface.carrier ∨
      p ∈ rightInterface.carrier
  primary_actual : primary.arcTrace ⊆ frontier carrier
  left_strip_actual :
    ActualBoundaryRealization.leftStripArcTrace o R leftTangentX ⊆
      frontier carrier
  right_strip_actual :
    ActualBoundaryRealization.rightStripArcTrace o R rightTangentX ⊆
      frontier carrier
  added_actual : added.arcTrace ⊆ frontier carrier
  left_interface_actual : leftInterface.carrier ⊆ frontier carrier
  right_interface_actual : rightInterface.carrier ⊆ frontier carrier

namespace PiecewiseRegularBoundaryTrace

variable {carrier : Set PlanePoint} {o : VerticalOrientation} {R : ℝ}
    {primary added : OneSidedCircularCap}
    {leftTangentX rightTangentX : ℝ}
    {leftInterface rightInterface : DegenerateHorizontalSegment}
    (b : PiecewiseRegularBoundaryTrace carrier o R primary added
      leftTangentX rightTangentX leftInterface rightInterface)

/-- The six ordered parameter intervals cover the complete parameter interval.
No strict breakpoint inequality is used, so either interface piece may
degenerate. -/
theorem parameter_mem_piece {t : ℝ} (ht : t ∈ Icc b.t0 b.t6) :
    t ∈ Icc b.t0 b.t1 ∨
      t ∈ Icc b.t1 b.t2 ∨
      t ∈ Icc b.t2 b.t3 ∨
      t ∈ Icc b.t3 b.t4 ∨
      t ∈ Icc b.t4 b.t5 ∨
      t ∈ Icc b.t5 b.t6 := by
  by_cases h1 : t ≤ b.t1
  · exact Or.inl ⟨ht.1, h1⟩
  by_cases h2 : t ≤ b.t2
  · exact Or.inr (Or.inl ⟨(not_le.mp h1).le, h2⟩)
  by_cases h3 : t ≤ b.t3
  · exact Or.inr (Or.inr (Or.inl ⟨(not_le.mp h2).le, h3⟩))
  by_cases h4 : t ≤ b.t4
  · exact Or.inr (Or.inr (Or.inr
      (Or.inl ⟨(not_le.mp h3).le, h4⟩)))
  by_cases h5 : t ≤ b.t5
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨(not_le.mp h4).le, h5⟩))))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨(not_le.mp h5).le, ht.2⟩))))

private theorem interval_image_subset_complete
    {a z : ℝ} (ha : b.t0 ≤ a) (hz : z ≤ b.t6) :
    b.trace '' Icc a z ⊆ b.trace '' Icc b.t0 b.t6 := by
  rintro p ⟨t, ht, rfl⟩
  exact ⟨t, ⟨ha.trans ht.1, ht.2.trans hz⟩, rfl⟩

include b

/-- The primary exterior arc is an actual part of the source frontier. -/
theorem primary_actual : primary.arcTrace ⊆ frontier carrier := by
  rw [← b.primary_image, ← b.complete_image]
  apply b.interval_image_subset_complete le_rfl
  exact b.t1_le_t2.trans (b.t2_le_t3.trans
    (b.t3_le_t4.trans (b.t4_le_t5.trans b.t5_le_t6)))

/-- The left strip-side arc is an actual part of the source frontier. -/
theorem left_strip_actual :
    ActualBoundaryRealization.leftStripArcTrace o R leftTangentX ⊆
      frontier carrier := by
  rw [← b.left_strip_image, ← b.complete_image]
  apply b.interval_image_subset_complete
  · exact b.t0_le_t1.trans (b.t1_le_t2.trans
      (b.t2_le_t3.trans (b.t3_le_t4.trans b.t4_le_t5)))
  · exact le_rfl

/-- The right strip-side arc is an actual part of the source frontier. -/
theorem right_strip_actual :
    ActualBoundaryRealization.rightStripArcTrace o R rightTangentX ⊆
      frontier carrier := by
  rw [← b.right_strip_image, ← b.complete_image]
  apply b.interval_image_subset_complete b.t0_le_t1
  exact b.t2_le_t3.trans
    (b.t3_le_t4.trans (b.t4_le_t5.trans b.t5_le_t6))

/-- The added exterior arc is an actual part of the source frontier. -/
theorem added_actual : added.arcTrace ⊆ frontier carrier := by
  rw [← b.added_image, ← b.complete_image]
  apply b.interval_image_subset_complete
  · exact b.t0_le_t1.trans (b.t1_le_t2.trans b.t2_le_t3)
  · exact b.t4_le_t5.trans b.t5_le_t6

/-- The possibly degenerate left interface is an actual part of the source
frontier. -/
theorem left_interface_actual :
    leftInterface.carrier ⊆ frontier carrier := by
  rw [← b.left_interface_image, ← b.complete_image]
  apply b.interval_image_subset_complete
  · exact b.t0_le_t1.trans
      (b.t1_le_t2.trans (b.t2_le_t3.trans b.t3_le_t4))
  · exact b.t5_le_t6

/-- The possibly degenerate right interface is an actual part of the source
frontier. -/
theorem right_interface_actual :
    rightInterface.carrier ⊆ frontier carrier := by
  rw [← b.right_interface_image, ← b.complete_image]
  apply b.interval_image_subset_complete
  · exact b.t0_le_t1.trans b.t1_le_t2
  · exact b.t3_le_t4.trans
      (b.t4_le_t5.trans b.t5_le_t6)

/-- Every actual frontier point lies on one of the six Figure-3 source pieces.
This is derived from the global trace image and the ordered parameter
partition, rather than assumed pointwise. -/
theorem frontier_exhaustive (p : PlanePoint) (hp : p ∈ frontier carrier) :
    p ∈ primary.arcTrace ∨
      p ∈ ActualBoundaryRealization.leftStripArcTrace o R leftTangentX ∨
      p ∈ ActualBoundaryRealization.rightStripArcTrace o R rightTangentX ∨
      p ∈ added.arcTrace ∨
      p ∈ leftInterface.carrier ∨
      p ∈ rightInterface.carrier := by
  rw [← b.complete_image] at hp
  rcases hp with ⟨t, ht, rfl⟩
  rcases b.parameter_mem_piece ht with h | h | h | h | h | h
  · apply Or.inl
    rw [← b.primary_image]
    exact ⟨t, h, rfl⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inl
    rw [← b.right_strip_image]
    exact ⟨t, h, rfl⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    rw [← b.right_interface_image]
    exact ⟨t, h, rfl⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    rw [← b.added_image]
    exact ⟨t, h, rfl⟩
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    rw [← b.left_interface_image]
    exact ⟨t, h, rfl⟩
  · apply Or.inr
    apply Or.inl
    rw [← b.left_strip_image]
    exact ⟨t, h, rfl⟩

/-- A source piecewise-regular trace plus independent endpoint incidence
derives the complete pointwise enumeration interface. -/
theorem toConfigurationEnumerationData
    (incidence : InterfaceIncidenceData o added leftTangentX rightTangentX
      leftInterface rightInterface) :
    ConfigurationEnumerationData carrier o R primary added
      leftTangentX rightTangentX leftInterface rightInterface where
  left_base := incidence.left_base
  right_base := incidence.right_base
  left_starts_at_tangency := incidence.left_starts_at_tangency
  left_ends_at_added_cap := incidence.left_ends_at_added_cap
  right_starts_at_added_cap := incidence.right_starts_at_added_cap
  right_ends_at_tangency := incidence.right_ends_at_tangency
  frontier_exhaustive := b.frontier_exhaustive
  primary_actual := b.primary_actual
  left_strip_actual := b.left_strip_actual
  right_strip_actual := b.right_strip_actual
  added_actual := b.added_actual
  left_interface_actual := b.left_interface_actual
  right_interface_actual := b.right_interface_actual

end PiecewiseRegularBoundaryTrace

end SourceBoundaryExtraction

/-- Source-located regular Figure-3 configuration.  The minimizer field ties the
geometric data to the actual source carrier.  The global closed boundary curve
is produced before case selection; the Figure-3 branch then supplies its five
cuts, six pointwise component characterizations, and two endpoint orders.
Regular Snell data, symmetry, and circular continuation remain independent
upstream inputs. -/
structure RegularFigureThreeBoundaryConfiguration (lam : ℝ)
    (source : SourcePerimeterSemantics lam) where
  carrier : Set PlanePoint
  source_minimizer : source.IsMinimizer carrier
  orientation : VerticalOrientation
  sourceRadius : ℝ
  symmetryAxisX : ℝ
  primaryExterior : OneSidedCircularCap
  addedExterior : OneSidedCircularCap
  leftTangentX : ℝ
  rightTangentX : ℝ
  regularSnell : SourceBoundaryExtraction.RegularSnellData lam orientation
    sourceRadius primaryExterior addedExterior
  verticalSymmetry : SourceBoundaryExtraction.VerticalSymmetryData orientation
    primaryExterior symmetryAxisX leftTangentX rightTangentX
  circularContinuation : SourceBoundaryExtraction.CircularContinuationData
    orientation sourceRadius primaryExterior leftTangentX rightTangentX
  boundaryCurve : SourceBoundaryExtraction.ClosedBoundaryTrace carrier
  figureThreeBranch :
    SourceBoundaryExtraction.FigureThreeBranchSelection carrier orientation
      sourceRadius primaryExterior addedExterior leftTangentX rightTangentX
      boundaryCurve

namespace RegularFigureThreeBoundaryConfiguration

variable {lam : ℝ} {source : SourcePerimeterSemantics lam}
    (c : RegularFigureThreeBoundaryConfiguration lam source)

/-- The left interface is reconstructed from the branch-selected endpoints. -/
def leftInterface : DegenerateHorizontalSegment :=
  c.figureThreeBranch.interfaceOrder.leftInterface c.orientation

/-- The right interface is reconstructed from the branch-selected endpoints. -/
def rightInterface : DegenerateHorizontalSegment :=
  c.figureThreeBranch.interfaceOrder.rightInterface c.orientation

/-- Endpoint incidence is no longer an independent configuration input. -/
theorem interfaceIncidence :
    SourceBoundaryExtraction.InterfaceIncidenceData c.orientation
      c.addedExterior c.leftTangentX c.rightTangentX
      c.leftInterface c.rightInterface :=
  c.figureThreeBranch.interfaceOrder.toInterfaceIncidenceData c.orientation

/-- The pre-branch source curve and branch-local cuts reconstruct the retained
piecewise boundary interface. -/
def piecewiseBoundary :
    SourceBoundaryExtraction.PiecewiseRegularBoundaryTrace c.carrier
      c.orientation c.sourceRadius c.primaryExterior c.addedExterior
      c.leftTangentX c.rightTangentX c.leftInterface c.rightInterface :=
  c.figureThreeBranch.toPiecewiseRegularBoundaryTrace

/-- The source trace and endpoint incidence derive, rather than assume, the
pointwise six-component enumeration. -/
theorem configurationEnumeration :
    SourceBoundaryExtraction.ConfigurationEnumerationData c.carrier
      c.orientation c.sourceRadius c.primaryExterior c.addedExterior
      c.leftTangentX c.rightTangentX c.leftInterface c.rightInterface :=
  c.piecewiseBoundary.toConfigurationEnumerationData c.interfaceIncidence

/-- The source primary-left join belongs to the literal left strip-side trace.
The vertical range is derived from its interface coordinate. -/
theorem primary_left_on_left_trace :
    c.primaryExterior.leftEndpoint ∈
      ActualBoundaryRealization.leftStripArcTrace c.orientation c.sourceRadius
        c.leftTangentX := by
  refine ⟨c.circularContinuation.primary_left_on_circle,
    c.circularContinuation.primary_left_outward, ?_⟩
  rw [OneSidedCircularCap.leftEndpoint, c.regularSnell.primary_base]
  cases c.orientation <;>
    norm_num [VerticalOrientation.primaryInterfaceY, VerticalOrientation.sign]

/-- The source primary-right join belongs to the literal right strip-side trace.
The vertical range is derived from its interface coordinate. -/
theorem primary_right_on_right_trace :
    c.primaryExterior.rightEndpoint ∈
      ActualBoundaryRealization.rightStripArcTrace c.orientation c.sourceRadius
        c.rightTangentX := by
  refine ⟨c.circularContinuation.primary_right_on_circle,
    c.circularContinuation.primary_right_outward, ?_⟩
  rw [OneSidedCircularCap.rightEndpoint, c.regularSnell.primary_base]
  cases c.orientation <;>
    norm_num [VerticalOrientation.primaryInterfaceY, VerticalOrientation.sign]

/-- The left source trace is the corresponding coordinate interval in the
six-piece boundary realization. -/
theorem leftInterface_carrier_eq_interfaceTrace :
    c.leftInterface.carrier =
      ActualBoundaryRealization.interfaceTrace c.leftTangentX
        c.addedExterior.leftEndpoint.1 c.orientation.tangentInterfaceY := by
  ext p
  simp only [DegenerateHorizontalSegment.carrier,
    ActualBoundaryRealization.interfaceTrace, mem_ofPred_eq]
  rw [c.configurationEnumeration.left_base,
    c.configurationEnumeration.left_starts_at_tangency,
    c.configurationEnumeration.left_ends_at_added_cap]

/-- The right source trace is the corresponding coordinate interval in the
six-piece boundary realization. -/
theorem rightInterface_carrier_eq_interfaceTrace :
    c.rightInterface.carrier =
      ActualBoundaryRealization.interfaceTrace
        c.addedExterior.rightEndpoint.1 c.rightTangentX
        c.orientation.tangentInterfaceY := by
  ext p
  simp only [DegenerateHorizontalSegment.carrier,
    ActualBoundaryRealization.interfaceTrace, mem_ofPred_eq]
  rw [c.configurationEnumeration.right_base,
    c.configurationEnumeration.right_starts_at_added_cap,
    c.configurationEnumeration.right_ends_at_tangency]

/-- The non-strict endpoint order is a consequence of the actual left segment,
so the degenerate case is retained. -/
theorem left_segment_order :
    c.leftTangentX ≤ c.addedExterior.leftEndpoint.1 := by
  simpa [c.configurationEnumeration.left_starts_at_tangency,
    c.configurationEnumeration.left_ends_at_added_cap] using
      c.leftInterface.left_le_right

/-- The non-strict endpoint order is a consequence of the actual right segment,
so the degenerate case is retained. -/
theorem right_segment_order :
    c.addedExterior.rightEndpoint.1 ≤ c.rightTangentX := by
  simpa [c.configurationEnumeration.right_starts_at_added_cap,
    c.configurationEnumeration.right_ends_at_tangency] using
      c.rightInterface.left_le_right

/-- The pointwise source enumeration derives the exact six-piece topological
frontier equation required by `ActualBoundaryRealization`. -/
theorem frontier_eq_boundaryTrace :
    frontier c.carrier =
      ActualBoundaryRealization.boundaryTrace c.orientation c.sourceRadius
        c.primaryExterior c.addedExterior c.leftTangentX c.rightTangentX := by
  apply Subset.antisymm
  · intro p hp
    rcases c.configurationEnumeration.frontier_exhaustive p hp with
      hp | hp | hp | hp | hp | hp
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr (Or.inl hp))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (c.leftInterface_carrier_eq_interfaceTrace ▸ hp)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (c.rightInterface_carrier_eq_interfaceTrace ▸ hp)))))
  · intro p hp
    rcases hp with hp | hp | hp | hp | hp | hp
    · exact c.configurationEnumeration.primary_actual hp
    · exact c.configurationEnumeration.left_strip_actual hp
    · exact c.configurationEnumeration.right_strip_actual hp
    · exact c.configurationEnumeration.added_actual hp
    · exact c.configurationEnumeration.left_interface_actual
        (c.leftInterface_carrier_eq_interfaceTrace.symm ▸ hp)
    · exact c.configurationEnumeration.right_interface_actual
        (c.rightInterface_carrier_eq_interfaceTrace.symm ▸ hp)

/-- Extraction of the checked actual-boundary interface from independently
separated source classification outputs. -/
def toActualBoundaryRealization : ActualBoundaryRealization lam where
  carrier := c.carrier
  orientation := c.orientation
  sourceRadius := c.sourceRadius
  symmetryAxisX := c.symmetryAxisX
  primaryExterior := c.primaryExterior
  addedExterior := c.addedExterior
  leftTangentX := c.leftTangentX
  rightTangentX := c.rightTangentX
  density_jump := c.regularSnell.density_jump
  radius_ge_one := c.regularSnell.radius_ge_one
  primary_side := c.regularSnell.primary_side
  primary_base := c.regularSnell.primary_base
  added_side := c.regularSnell.added_side
  added_base := c.regularSnell.added_base
  primary_radius := c.regularSnell.primary_radius
  added_radius := c.regularSnell.added_radius
  primary_midpoint := c.verticalSymmetry.primary_midpoint
  tangent_abscissae_symmetric :=
    c.verticalSymmetry.tangent_abscissae_symmetric
  primary_left_on_left_trace := c.primary_left_on_left_trace
  primary_right_on_right_trace := c.primary_right_on_right_trace
  left_segment_order := c.left_segment_order
  right_segment_order := c.right_segment_order
  primary_signed_snell := by
    simpa [ActualBoundaryRealization.stripCenter] using
      c.regularSnell.primary_signed_snell
  added_contact_law := c.regularSnell.added_contact_law
  frontier_eq_boundaryTrace := c.frontier_eq_boundaryTrace

@[simp] theorem toActualBoundaryRealization_carrier :
    c.toActualBoundaryRealization.carrier = c.carrier := rfl

@[simp] theorem toActualBoundaryRealization_sourceRadius :
    c.toActualBoundaryRealization.sourceRadius = c.sourceRadius := rfl

/-- Every strict-radius source-located Figure-3 configuration is impossible. -/
theorem strictRadius_false (hR : 1 < c.sourceRadius) : False :=
  c.toActualBoundaryRealization.strictRadius_false hR

/-- The complete closed-radius source configuration retains exactly the
separate radius-one residual; it is not identified with any endpoint carrier. -/
theorem sourceRadius_eq_one : c.sourceRadius = 1 := by
  simpa using c.toActualBoundaryRealization.sourceRadius_eq_one

end RegularFigureThreeBoundaryConfiguration

/-- Source-facing elimination of the complete strict-radius Figure-3 branch.
The remaining existential classification work can therefore retain only
configurations whose radius is exactly one. -/
theorem not_exists_regularFigureThree_strictRadius
    {lam : ℝ} (source : SourcePerimeterSemantics lam) :
    ¬ ∃ c : RegularFigureThreeBoundaryConfiguration lam source,
      1 < c.sourceRadius := by
  rintro ⟨c, hR⟩
  exact c.strictRadius_false hR

end CMVFigureThree
