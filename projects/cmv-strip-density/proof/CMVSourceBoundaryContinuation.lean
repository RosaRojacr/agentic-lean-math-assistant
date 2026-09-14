/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTwoPatchCurvatureGeometry
import CMVFigureFourBilateralIncidence
import Mathlib.Topology.Connected.Clopen

/-!
# Branch-neutral continuation of regular source-boundary charts

This module starts from literal local graph charts on one actual carrier.  It
contains no selected CMV configuration, finite arc list, target carrier, or
source-minimality assertion.  The common occupied-side curvature remains an
explicit analytic input.
-/

open Set Function Filter Real
open scoped Topology ContDiff

noncomputable section
namespace CMVTwoPatchGraphVariation
namespace GraphPatch

/-- The supporting-circle center selected by an increasing horizontal graph
chart and its occupied-side curvature. -/
def supportingCenter (P : GraphPatch) (K x : ℝ) : PlanePoint :=
  CMVCurvatureIntegration.centerInvariant P.graphTrace
    (CMVCurvatureIntegration.normalizedTangent P.graphVelocity)
    (P.side.areaSign * K) x

/-- The literal supporting circle selected by a nonzero-curvature graph chart. -/
def supportingCircle (P : GraphPatch) (K x : ℝ) : Set PlanePoint :=
  {p | (p.1 - (P.supportingCenter K x).1) ^ 2 +
      (p.2 - (P.supportingCenter K x).2) ^ 2 =
        (1 / (P.side.areaSign * K)) ^ 2}

/-- The literal affine line through a graph point with the chart's actual
first derivative there. -/
def supportingLineAt (P : GraphPatch) (x : ℝ) : Set PlanePoint :=
  {p | p.2 = P.graph x + deriv P.graph x * (p.1 - x)}

end GraphPatch
end CMVTwoPatchGraphVariation

namespace CMVSourceBoundaryContinuation

open CMVTwoPatchGraphVariation

/-- Reversing a regular parameter changes both the unit tangent and signed
curvature.  Their two signs cancel in the supporting-center formula at a common
actual point. -/
theorem supportingCenter_eq_of_reversedContact
    {trace₁ trace₂ velocity₁ velocity₂ : ℝ → PlanePoint}
    {curvature s t : ℝ} (hcurvature : curvature ≠ 0)
    (hpoint : trace₁ s = trace₂ t)
    (htangent :
      CMVCurvatureIntegration.normalizedTangent velocity₂ t =
        (-(CMVCurvatureIntegration.normalizedTangent velocity₁ s).1,
          -(CMVCurvatureIntegration.normalizedTangent velocity₁ s).2)) :
    CMVCurvatureIntegration.centerInvariant trace₁
        (CMVCurvatureIntegration.normalizedTangent velocity₁) curvature s =
      CMVCurvatureIntegration.centerInvariant trace₂
        (CMVCurvatureIntegration.normalizedTangent velocity₂) (-curvature) t := by
  unfold CMVCurvatureIntegration.centerInvariant
  rw [← hpoint, htangent]
  apply Prod.ext <;> dsimp
  all_goals field_simp [hcurvature]

/-- A branch-neutral regular horizontal boundary chart on one actual carrier.
The local frontier equation is a chart premise, not a complete arc image: it only
identifies the frontier inside the chart's open coordinate neighborhood.  All
`C²`, positive-width, density-zone, and occupied-side data remain the explicit
fields of the existing `GraphPatch`. -/
structure ActualRegularGraphChart (carrier : Set PlanePoint) where
  patch : GraphPatch
  neighborhood : Set PlanePoint
  neighborhood_open : IsOpen neighborhood
  local_frontier :
    frontier carrier ∩ neighborhood =
      patch.graphTrace '' Ioo patch.a patch.b

namespace ActualRegularGraphChart

variable {carrier : Set PlanePoint}

/-- Every interior chart point is an actual point of the carrier frontier. -/
theorem graphTrace_mem_frontier (A : ActualRegularGraphChart carrier)
    {x : ℝ} (hx : x ∈ Ioo A.patch.a A.patch.b) :
    A.patch.graphTrace x ∈ frontier carrier := by
  have hmem : A.patch.graphTrace x ∈
      A.patch.graphTrace '' Ioo A.patch.a A.patch.b := ⟨x, hx, rfl⟩
  rw [← A.local_frontier] at hmem
  exact hmem.1

/-- Every interior chart point lies in its declared open coordinate
neighborhood. -/
theorem graphTrace_mem_neighborhood (A : ActualRegularGraphChart carrier)
    {x : ℝ} (hx : x ∈ Ioo A.patch.a A.patch.b) :
    A.patch.graphTrace x ∈ A.neighborhood := by
  have hmem : A.patch.graphTrace x ∈
      A.patch.graphTrace '' Ioo A.patch.a A.patch.b := ⟨x, hx, rfl⟩
  rw [← A.local_frontier] at hmem
  exact hmem.2

/-- Two charts overlap at an actual regular frontier point with the same
horizontal coordinate.  No interval overlap or equality of graph functions is
supplied. -/
structure OverlapAt (A B : ActualRegularGraphChart carrier) (x : ℝ) : Prop where
  left_interior : x ∈ Ioo A.patch.a A.patch.b
  right_interior : x ∈ Ioo B.patch.a B.patch.b
  point_eq : A.patch.graphTrace x = B.patch.graphTrace x

/-- Exact local frontier charts force their graph functions to agree on a whole
neighborhood of every actual overlap point. -/
theorem eventuallyEq_graph_of_overlap
    (A B : ActualRegularGraphChart carrier) {x : ℝ}
    (h : OverlapAt A B x) :
    A.patch.graph =ᶠ[𝓝 x] B.patch.graph := by
  have htraceContinuous : Continuous A.patch.graphTrace := by
    exact continuous_id.prodMk A.patch.graph_contDiff.continuous
  have hrightNeighborhood :
      A.patch.graphTrace x ∈ B.neighborhood := by
    rw [h.point_eq]
    exact B.graphTrace_mem_neighborhood h.right_interior
  have hnearNeighborhood :
      ∀ᶠ y in 𝓝 x, A.patch.graphTrace y ∈ B.neighborhood :=
    htraceContinuous.continuousAt
      (B.neighborhood_open.mem_nhds hrightNeighborhood)
  have hnearInterior : ∀ᶠ y in 𝓝 x, y ∈ Ioo A.patch.a A.patch.b :=
    isOpen_Ioo.mem_nhds h.left_interior
  filter_upwards [hnearNeighborhood, hnearInterior] with y hyNeighborhood hyInterior
  have hyFrontier : A.patch.graphTrace y ∈ frontier carrier :=
    A.graphTrace_mem_frontier hyInterior
  have hyRight : A.patch.graphTrace y ∈
      B.patch.graphTrace '' Ioo B.patch.a B.patch.b := by
    rw [← B.local_frontier]
    exact ⟨hyFrontier, hyNeighborhood⟩
  rcases hyRight with ⟨z, hzInterior, hz⟩
  have hyz : z = y := by
    have := congrArg Prod.fst hz
    simpa only [GraphPatch.graphTrace] using this
  have hsnd := congrArg Prod.snd hz
  simpa only [GraphPatch.graphTrace, hyz] using hsnd.symm

/-- The first derivatives of two exact actual-boundary charts agree at an
overlap.  This is derived from the local frontier equations, not supplied as
extra tangent data. -/
theorem deriv_eq_of_overlap
    (A B : ActualRegularGraphChart carrier) {x : ℝ}
    (h : OverlapAt A B x) :
    deriv A.patch.graph x = deriv B.patch.graph x := by
  exact (A.eventuallyEq_graph_of_overlap B h).deriv_eq

/-- The normalized increasing graph tangents agree at an actual overlap. -/
theorem normalizedTangent_eq_of_overlap
    (A B : ActualRegularGraphChart carrier) {x : ℝ}
    (h : OverlapAt A B x) :
    CMVCurvatureIntegration.normalizedTangent A.patch.graphVelocity x =
      CMVCurvatureIntegration.normalizedTangent B.patch.graphVelocity x := by
  have hvelocity : A.patch.graphVelocity x = B.patch.graphVelocity x := by
    apply Prod.ext
    · rfl
    · exact A.deriv_eq_of_overlap B h
  have hspeed :
      CMVCurvatureIntegration.euclideanSpeed A.patch.graphVelocity x =
        CMVCurvatureIntegration.euclideanSpeed B.patch.graphVelocity x := by
    unfold CMVCurvatureIntegration.euclideanSpeed
    rw [hvelocity]
  unfold CMVCurvatureIntegration.normalizedTangent
  rw [hvelocity, hspeed]

/-- Nonzero common occupied-side curvature and the actual occupied-side label
select one unique supporting-circle center across overlapping charts. -/
theorem supportingCenter_eq_of_overlap
    (A B : ActualRegularGraphChart carrier) {K x : ℝ}
    (h : OverlapAt A B x) (hside : A.patch.side = B.patch.side)
    (_hK : K ≠ 0) :
    A.patch.supportingCenter K x = B.patch.supportingCenter K x := by
  unfold GraphPatch.supportingCenter CMVCurvatureIntegration.centerInvariant
  rw [h.point_eq, A.normalizedTangent_eq_of_overlap B h, hside]

/-- Overlapping nonzero-curvature charts select the same literal supporting
circle, and both complete closed chart traces lie on it. -/
theorem unique_supportingCircle_of_overlap
    (A B : ActualRegularGraphChart carrier) {K x : ℝ}
    (h : OverlapAt A B x) (hside : A.patch.side = B.patch.side)
    (hK : K ≠ 0)
    (hcurvA : ∀ y ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature y = K)
    (hcurvB : ∀ y ∈ Ioo B.patch.a B.patch.b,
      B.patch.orientedGraphCurvature y = K) :
    A.patch.supportingCircle K x = B.patch.supportingCircle K x ∧
      (∀ y ∈ Icc A.patch.a A.patch.b,
        A.patch.graphTrace y ∈ A.patch.supportingCircle K x) ∧
      (∀ y ∈ Icc B.patch.a B.patch.b,
        B.patch.graphTrace y ∈ B.patch.supportingCircle K x) := by
  have hcenter := A.supportingCenter_eq_of_overlap B h hside hK
  have hcircles :
      A.patch.supportingCircle K x = B.patch.supportingCircle K x := by
    unfold GraphPatch.supportingCircle
    rw [hcenter, hside]
  refine ⟨hcircles, ?_, ?_⟩
  · intro y hy
    exact A.patch.closed_graph_circle_identity hcurvA hK
      ⟨h.left_interior.1.le, h.left_interior.2.le⟩ hy
  · intro y hy
    exact B.patch.closed_graph_circle_identity hcurvB hK
      ⟨h.right_interior.1.le, h.right_interior.2.le⟩ hy

/-- Zero occupied-side curvature makes the first derivative constant on the
whole closed graph interval. -/
theorem deriv_eq_of_orientedGraphCurvature_eq_zero
    (A : ActualRegularGraphChart carrier)
    (hzero : ∀ x ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature x = 0)
    {x y : ℝ} (hx : x ∈ Icc A.patch.a A.patch.b)
    (hy : y ∈ Icc A.patch.a A.patch.b) :
    deriv A.patch.graph x = deriv A.patch.graph y := by
  have hsecond : ∀ z ∈ Ioo A.patch.a A.patch.b,
      HasDerivAt (deriv A.patch.graph) 0 z := by
    intro z hz
    have hcurv := hzero z hz
    have hden : Real.sqrt (1 + deriv A.patch.graph z ^ 2) ^ 3 ≠ 0 := by
      positivity
    unfold GraphPatch.orientedGraphCurvature GraphPatch.graphCurvature at hcurv
    have hderiv : deriv (deriv A.patch.graph) z = 0 := by
      have hfrac :=
        (mul_eq_zero.mp hcurv).resolve_left A.patch.side.areaSign_ne_zero
      exact (div_eq_zero_iff.mp hfrac).resolve_right hden
    exact (A.patch.graph_deriv_contDiff.differentiable
      (by norm_num) z).hasDerivAt.congr_deriv hderiv
  have hconstant := CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero
    A.patch.a_lt_b A.patch.graph_deriv_contDiff.continuous.continuousOn hsecond
  exact (hconstant hx).trans (hconstant hy).symm

/-- The existing zero-curvature integration result can be re-anchored at any
closed point of the actual graph chart. -/
theorem closedTrace_subset_supportingLineAt
    (A : ActualRegularGraphChart carrier)
    (hzero : ∀ x ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature x = 0)
    {x : ℝ} (hx : x ∈ Icc A.patch.a A.patch.b) :
    ∀ y ∈ Icc A.patch.a A.patch.b,
      A.patch.graphTrace y ∈ A.patch.supportingLineAt x := by
  intro y hy
  have hxline := A.patch.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    hzero x hx
  have hyline := A.patch.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    hzero y hy
  have hslope := A.deriv_eq_of_orientedGraphCurvature_eq_zero hzero hx
    ⟨le_rfl, A.patch.a_lt_b.le⟩
  change A.patch.graph y =
    A.patch.graph x + deriv A.patch.graph x * (y - x)
  rw [hxline, hyline, hslope]
  ring

/-- Overlapping zero-curvature charts select the same literal supporting line,
and both complete closed chart traces lie on it. -/
theorem unique_supportingLine_of_overlap
    (A B : ActualRegularGraphChart carrier) {x : ℝ}
    (h : OverlapAt A B x)
    (hzeroA : ∀ y ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature y = 0)
    (hzeroB : ∀ y ∈ Ioo B.patch.a B.patch.b,
      B.patch.orientedGraphCurvature y = 0) :
    A.patch.supportingLineAt x = B.patch.supportingLineAt x ∧
      (∀ y ∈ Icc A.patch.a A.patch.b,
        A.patch.graphTrace y ∈ A.patch.supportingLineAt x) ∧
      (∀ y ∈ Icc B.patch.a B.patch.b,
        B.patch.graphTrace y ∈ B.patch.supportingLineAt x) := by
  have hgraph : A.patch.graph x = B.patch.graph x := by
    exact congrArg Prod.snd h.point_eq
  have hderiv := A.deriv_eq_of_overlap B h
  have hline : A.patch.supportingLineAt x = B.patch.supportingLineAt x := by
    unfold GraphPatch.supportingLineAt
    rw [hgraph, hderiv]
  refine ⟨hline, A.closedTrace_subset_supportingLineAt hzeroA
    ⟨h.left_interior.1.le, h.left_interior.2.le⟩, ?_⟩
  exact B.closedTrace_subset_supportingLineAt hzeroB
    ⟨h.right_interior.1.le, h.right_interior.2.le⟩


/-- A nonzero-curvature chart selects the same circle from every closed anchor
parameter. -/
theorem supportingCircle_eq_of_anchors
    (A : ActualRegularGraphChart carrier) {K x y : ℝ}
    (hK : K ≠ 0)
    (hcurv : ∀ z ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature z = K)
    (hx : x ∈ Icc A.patch.a A.patch.b)
    (hy : y ∈ Icc A.patch.a A.patch.b) :
    A.patch.supportingCircle K x = A.patch.supportingCircle K y := by
  have hregular :=
    A.patch.arbitrarySpeedConstantCurvatureOn_graph hcurv hK
  have hcenter :
      A.patch.supportingCenter K x = A.patch.supportingCenter K y := by
    exact hregular.center_invariant hx hy
  unfold GraphPatch.supportingCircle
  rw [hcenter]

/-- A zero-curvature chart selects the same affine line from every closed
anchor parameter. -/
theorem supportingLineAt_eq_of_anchors
    (A : ActualRegularGraphChart carrier) {x y : ℝ}
    (hzero : ∀ z ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature z = 0)
    (hx : x ∈ Icc A.patch.a A.patch.b)
    (hy : y ∈ Icc A.patch.a A.patch.b) :
    A.patch.supportingLineAt x = A.patch.supportingLineAt y := by
  have hslope :=
    A.deriv_eq_of_orientedGraphCurvature_eq_zero hzero hx hy
  have hxy := A.closedTrace_subset_supportingLineAt hzero hy x hx
  change A.patch.graph x =
    A.patch.graph y + deriv A.patch.graph y * (x - y) at hxy
  have haffine : ∀ z : ℝ,
      A.patch.graph x + deriv A.patch.graph x * (z - x) =
        A.patch.graph y + deriv A.patch.graph y * (z - y) := by
    intro z
    rw [hslope, hxy]
    ring
  ext p
  change (p.2 =
      A.patch.graph x + deriv A.patch.graph x * (p.1 - x)) ↔
    (p.2 = A.patch.graph y + deriv A.patch.graph y * (p.1 - y))
  rw [haffine p.1]
end ActualRegularGraphChart

/-! ## Branch-neutral graph atlases -/

/-- An unlabelled, possibly infinite atlas of actual regular boundary charts
on one locus.  The caller supplies no chart count, endpoint order, selected CMV
branch, circle center, line, or complete component image.  The common
occupied-side curvature and side are the explicit analytic inputs that remain
upstream of continuation. -/
structure BranchNeutralGraphAtlas
    (carrier locus : Set PlanePoint) (K : ℝ) where
  side : OccupiedSide
  locus_subset_frontier : locus ⊆ frontier carrier
  chart : locus → ActualRegularGraphChart carrier
  chart_window_subset_locus : ∀ p : locus,
    frontier carrier ∩ (chart p).neighborhood ⊆ locus
  base_interior : ∀ p : locus,
    p.1.1 ∈ Ioo (chart p).patch.a (chart p).patch.b
  base_eq : ∀ p : locus, (chart p).patch.graphTrace p.1.1 = p.1
  chart_side : ∀ p : locus, (chart p).patch.side = side
  chart_curvature : ∀ p : locus, ∀ x ∈
    Ioo (chart p).patch.a (chart p).patch.b,
      (chart p).patch.orientedGraphCurvature x = K

namespace BranchNeutralGraphAtlas

variable {carrier locus : Set PlanePoint} {K : ℝ}

/-- The supporting carrier selected at one atlas base point.  The zero and
nonzero curvature branches are kept explicit in the definition. -/
def supportAt (A : BranchNeutralGraphAtlas carrier locus K)
    (p : locus) : Set PlanePoint :=
  if K = 0 then
    (A.chart p).patch.supportingLineAt p.1.1
  else
    (A.chart p).patch.supportingCircle K p.1.1

/-- Every local chart trace belongs to the same actual continuation locus. -/
theorem chartTrace_image_subset_locus
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    (A.chart p).patch.graphTrace ''
        Ioo (A.chart p).patch.a (A.chart p).patch.b ⊆ locus := by
  intro q hq
  apply A.chart_window_subset_locus p
  rw [(A.chart p).local_frontier]
  exact hq

/-- A point in one chart window gives a genuine overlap with the chart based
at that point.  The overlap interval and graph equality are derived from the
two local frontier equations. -/
theorem overlapAt_chart_of_mem_neighborhood
    (A : BranchNeutralGraphAtlas carrier locus K)
    (p q : locus) (hq : q.1 ∈ (A.chart p).neighborhood) :
    ActualRegularGraphChart.OverlapAt (A.chart q) (A.chart p) q.1.1 := by
  have hqLocal : q.1 ∈
      frontier carrier ∩ (A.chart p).neighborhood :=
    ⟨A.locus_subset_frontier q.2, hq⟩
  rw [(A.chart p).local_frontier] at hqLocal
  rcases hqLocal with ⟨x, hx, htrace⟩
  have hxq : x = q.1.1 := by
    have := congrArg Prod.fst htrace
    simpa only [GraphPatch.graphTrace] using this
  refine {
    left_interior := A.base_interior q
    right_interior := by simpa only [← hxq] using hx
    point_eq := ?_
  }
  calc
    (A.chart q).patch.graphTrace q.1.1 = q.1 := A.base_eq q
    _ = (A.chart p).patch.graphTrace x := htrace.symm
    _ = (A.chart p).patch.graphTrace q.1.1 := by rw [hxq]

/-- Supporting geometry is constant throughout the actual part of one chart
window.  Circle or line uniqueness is derived by the overlap theorems above. -/
theorem supportAt_eq_of_mem_neighborhood
    (A : BranchNeutralGraphAtlas carrier locus K)
    (p q : locus) (hq : q.1 ∈ (A.chart p).neighborhood) :
    A.supportAt q = A.supportAt p := by
  have hoverlap := A.overlapAt_chart_of_mem_neighborhood p q hq
  unfold supportAt
  split_ifs with hzero
  · have hover :=
      (ActualRegularGraphChart.unique_supportingLine_of_overlap
        (A.chart q) (A.chart p) hoverlap)
        (fun x hx => by rw [A.chart_curvature q x hx, hzero])
        (fun x hx => by rw [A.chart_curvature p x hx, hzero]) |>.1
    exact hover.trans ((A.chart p).supportingLineAt_eq_of_anchors
      (fun x hx => by rw [A.chart_curvature p x hx, hzero])
      ⟨hoverlap.right_interior.1.le, hoverlap.right_interior.2.le⟩
      ⟨(A.base_interior p).1.le, (A.base_interior p).2.le⟩)
  · have hover :=
      (ActualRegularGraphChart.unique_supportingCircle_of_overlap
        (A.chart q) (A.chart p) hoverlap
        ((A.chart_side q).trans (A.chart_side p).symm) hzero
        (A.chart_curvature q) (A.chart_curvature p)) |>.1
    exact hover.trans ((A.chart p).supportingCircle_eq_of_anchors hzero
      (A.chart_curvature p)
      ⟨hoverlap.right_interior.1.le, hoverlap.right_interior.2.le⟩
      ⟨(A.base_interior p).1.le, (A.base_interior p).2.le⟩)

/-- The supporting carrier selected by the atlas is genuinely locally
constant; no finite subcover or overlap graph is supplied. -/
theorem supportAt_isLocallyConstant
    (A : BranchNeutralGraphAtlas carrier locus K) :
    IsLocallyConstant A.supportAt := by
  rw [IsLocallyConstant.iff_exists_open]
  intro p
  let U : Set locus := Subtype.val ⁻¹' (A.chart p).neighborhood
  have hUopen : IsOpen U :=
    (A.chart p).neighborhood_open.preimage continuous_subtype_val
  have hpNeighborhood : p.1 ∈ (A.chart p).neighborhood := by
    rw [← A.base_eq p]
    exact (A.chart p).graphTrace_mem_neighborhood (A.base_interior p)
  refine ⟨U, hUopen, hpNeighborhood, ?_⟩
  intro q hq
  exact A.supportAt_eq_of_mem_neighborhood p q hq

/-- Supporting geometry propagates across every actual connected atlas
component. -/
theorem supportAt_eq_of_mem_connectedComponent
    (A : BranchNeutralGraphAtlas carrier locus K)
    (p q : locus) (hq : q ∈ connectedComponent p) :
    A.supportAt q = A.supportAt p := by
  exact A.supportAt_isLocallyConstant.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hq mem_connectedComponent

/-- Every atlas base point lies on the supporting carrier selected there. -/
theorem base_mem_supportAt
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    p.1 ∈ A.supportAt p := by
  unfold supportAt
  split_ifs with hzero
  · rw [← A.base_eq p]
    exact (A.chart p).closedTrace_subset_supportingLineAt
      (fun x hx => by rw [A.chart_curvature p x hx, hzero])
      ⟨(A.base_interior p).1.le, (A.base_interior p).2.le⟩ p.1.1
      ⟨(A.base_interior p).1.le, (A.base_interior p).2.le⟩
  · rw [← A.base_eq p]
    exact (A.chart p).patch.closed_graph_circle_identity
      (A.chart_curvature p) hzero
      ⟨(A.base_interior p).1.le, (A.base_interior p).2.le⟩
      ⟨(A.base_interior p).1.le, (A.base_interior p).2.le⟩

/-- One literal circle or line contains the whole actual connected atlas
component.  This is continuation across an unbounded number of overlapping
charts, not merely chartwise containment. -/
theorem connectedComponent_subset_supportAt
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    ((↑) : locus → PlanePoint) '' connectedComponent p ⊆ A.supportAt p := by
  rintro _ ⟨q, hq, rfl⟩
  rw [← A.supportAt_eq_of_mem_connectedComponent p q hq]
  exact A.base_mem_supportAt q


/-- The union of every local chart trace based in the component of `p`.
This is derived from the unlabelled atlas rather than supplied as a complete
arc image. -/
def maximalComponentTraceImage
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    Set PlanePoint :=
  ⋃ (q : locus)
      (_hq : q.1 ∈ connectedComponentIn locus p.1),
    (A.chart q).patch.graphTrace ''
      Ioo (A.chart q).patch.a (A.chart q).patch.b

/-- The derived union of actual local traces is exactly the maximal connected
component of the continuation locus. -/
theorem maximalComponentTraceImage_eq
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    A.maximalComponentTraceImage p = connectedComponentIn locus p.1 := by
  apply Set.Subset.antisymm
  · unfold maximalComponentTraceImage
    rw [iUnion_subset_iff]
    intro q
    rw [iUnion_subset_iff]
    intro hq
    have hcontinuous : Continuous (A.chart q).patch.graphTrace :=
      continuous_id.prodMk (A.chart q).patch.graph_contDiff.continuous
    have hpreconnected :
        IsPreconnected ((A.chart q).patch.graphTrace ''
          Ioo (A.chart q).patch.a (A.chart q).patch.b) :=
      isPreconnected_Ioo.image _ hcontinuous.continuousOn
    have hqImage :
        q.1 ∈ (A.chart q).patch.graphTrace ''
          Ioo (A.chart q).patch.a (A.chart q).patch.b :=
      ⟨q.1.1, A.base_interior q, A.base_eq q⟩
    have himageSubset :
        (A.chart q).patch.graphTrace ''
            Ioo (A.chart q).patch.a (A.chart q).patch.b ⊆
          connectedComponentIn locus q.1 :=
      hpreconnected.subset_connectedComponentIn hqImage
        (A.chartTrace_image_subset_locus q)
    rw [← connectedComponentIn_eq hq] at himageSubset
    exact himageSubset
  · intro q hq
    have hqLocus : q ∈ locus :=
      connectedComponentIn_subset locus p.1 hq
    let q' : locus := ⟨q, hqLocus⟩
    refine mem_iUnion_of_mem q' ?_
    refine mem_iUnion_of_mem hq ?_
    exact ⟨q.1, A.base_interior q', A.base_eq q'⟩

/-- Every maximal continuation-component trace lies on its selected support. -/
theorem maximalComponentTraceImage_subset_supportAt
    (A : BranchNeutralGraphAtlas carrier locus K) (p : locus) :
    A.maximalComponentTraceImage p ⊆ A.supportAt p := by
  rw [A.maximalComponentTraceImage_eq,
    connectedComponentIn_eq_image p.2]
  exact A.connectedComponent_subset_supportAt p

/-- Every compact piece of an actual continuation locus is met by only finitely
many maximal continuation-component trace images. -/
theorem exists_finite_maximalComponentTraceImage_cover
    (A : BranchNeutralGraphAtlas carrier locus K)
    {S : Set PlanePoint} (hS : IsCompact S) (hSlocus : S ⊆ locus) :
    ∃ (N : ℕ) (p : Fin N → locus),
      (∀ i, (p i).1 ∈ S) ∧
        S ⊆ ⋃ i, A.maximalComponentTraceImage (p i) := by
  let base : S → locus := fun p => ⟨p.1, hSlocus p.2⟩
  have hcover : S ⊆ ⋃ p : S, (A.chart (base p)).neighborhood := by
    intro q hq
    let qS : S := ⟨q, hq⟩
    refine mem_iUnion.mpr ⟨qS, ?_⟩
    have hmem := (A.chart (base qS)).graphTrace_mem_neighborhood
      (A.base_interior (base qS))
    rw [A.base_eq (base qS)] at hmem
    exact hmem
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun p : S => (A.chart (base p)).neighborhood)
    (fun p => (A.chart (base p)).neighborhood_open) hcover
  let e : Fin (Fintype.card {p : S // p ∈ t}) ≃ {p : S // p ∈ t} :=
    (Fintype.equivFin {p : S // p ∈ t}).symm
  refine ⟨Fintype.card {p : S // p ∈ t}, fun i => base (e i).1,
    fun i => (e i).1.2, ?_⟩
  intro q hq
  rcases mem_iUnion.mp (ht hq) with ⟨p, hp⟩
  rcases mem_iUnion.mp hp with ⟨hpt, hqwindow⟩
  let i : Fin (Fintype.card {p : S // p ∈ t}) := e.symm ⟨p, hpt⟩
  refine mem_iUnion.mpr ⟨i, ?_⟩
  rw [A.maximalComponentTraceImage_eq]
  have hqFrontier : q ∈ frontier carrier :=
    A.locus_subset_frontier (hSlocus hq)
  have hqImage : q ∈
      (A.chart (base (e i).1)).patch.graphTrace ''
        Ioo (A.chart (base (e i).1)).patch.a
          (A.chart (base (e i).1)).patch.b := by
    rw [← (A.chart (base (e i).1)).local_frontier]
    exact ⟨hqFrontier, by simpa [i] using hqwindow⟩
  have hpreconnected : IsPreconnected
      ((A.chart (base (e i).1)).patch.graphTrace ''
        Ioo (A.chart (base (e i).1)).patch.a
          (A.chart (base (e i).1)).patch.b) :=
    isPreconnected_Ioo.image _
      (continuous_id.prodMk
        (A.chart (base (e i).1)).patch.graph_contDiff.continuous).continuousOn
  have hpImage : (base (e i).1).1 ∈
      (A.chart (base (e i).1)).patch.graphTrace ''
        Ioo (A.chart (base (e i).1)).patch.a
          (A.chart (base (e i).1)).patch.b :=
    ⟨(base (e i).1).1.1, A.base_interior (base (e i).1),
      A.base_eq (base (e i).1)⟩
  exact hpreconnected.subset_connectedComponentIn hpImage
    (A.chartTrace_image_subset_locus (base (e i).1)) hqImage

end BranchNeutralGraphAtlas

/-! ## Maximal actual-component image upgrade -/

/-- Local continuation inside a locus.  This is pointwise chart saturation,
not an assumed global component or complete trace-image equality. -/
def LocallySaturatedIn (arc locus : Set PlanePoint) : Prop :=
  ∀ p ∈ arc, ∃ U : Set PlanePoint,
    IsOpen U ∧ p ∈ U ∧ locus ∩ U ⊆ arc

/-- A continuous closed trace that is locally saturated in an actual locus is
exactly the connected component of any one of its points.  Thus local chart
containment is upgraded to an exact maximal-component trace image; no finite
arc inventory or selected configuration is an input. -/
theorem connectedComponentIn_eq_closedTraceImage
    {trace : ℝ → PlanePoint} {a b s : ℝ} {locus : Set PlanePoint}
    (_hab : a ≤ b) (hs : s ∈ Icc a b)
    (hcontinuous : ContinuousOn trace (Icc a b))
    (hsubset : trace '' Icc a b ⊆ locus)
    (hsaturated : LocallySaturatedIn (trace '' Icc a b) locus) :
    connectedComponentIn locus (trace s) = trace '' Icc a b := by
  let component : Set PlanePoint := connectedComponentIn locus (trace s)
  have hanchorLocus : trace s ∈ locus := hsubset ⟨s, hs, rfl⟩
  have hcomponentPreconnected : IsPreconnected component :=
    isPreconnected_connectedComponentIn
  have himagePreconnected : IsPreconnected (trace '' Icc a b) :=
    isPreconnected_Icc.image trace hcontinuous
  have himageSubsetComponent : trace '' Icc a b ⊆ component :=
    himagePreconnected.subset_connectedComponentIn ⟨s, hs, rfl⟩ hsubset
  let liftedArc : Set component := {q | q.1 ∈ trace '' Icc a b}
  have hliftedClosed : IsClosed liftedArc := by
    have himageCompact : IsCompact (trace '' Icc a b) :=
      isCompact_Icc.image_of_continuousOn hcontinuous
    exact himageCompact.isClosed.preimage continuous_subtype_val
  have hliftedOpen : IsOpen liftedArc := by
    rw [isOpen_iff_forall_mem_open]
    intro q hq
    rcases hsaturated q.1 hq with ⟨U, hUopen, hqU, hUsubset⟩
    refine ⟨Subtype.val ⁻¹' U, ?_, hUopen.preimage continuous_subtype_val, hqU⟩
    intro r hr
    exact hUsubset ⟨connectedComponentIn_subset locus (trace s) r.2, hr⟩
  have hliftedNonempty : liftedArc.Nonempty := by
    let q : component := ⟨trace s, mem_connectedComponentIn hanchorLocus⟩
    exact ⟨q, ⟨s, hs, rfl⟩⟩
  let _ : PreconnectedSpace component :=
    Subtype.preconnectedSpace hcomponentPreconnected
  have hliftedEq : liftedArc = Set.univ :=
    IsClopen.eq_univ ⟨hliftedClosed, hliftedOpen⟩ hliftedNonempty
  apply Set.Subset.antisymm
  · intro p hp
    have hpLifted : (⟨p, hp⟩ : component) ∈ liftedArc := by
      rw [hliftedEq]
      exact mem_univ _
    exact hpLifted
  · exact himageSubsetComponent



/-! ## Endpoint continuation alternatives -/

/-- Contact is geometric incidence with an actual interface, independent of
whether a chosen coordinate projection is regular. -/
def InterfaceContactAt (interface : Set PlanePoint)
    (trace : ℝ → PlanePoint) (t : ℝ) : Prop :=
  trace t ∈ interface

/-- Tangency is interface contact together with vanishing normal velocity. -/
def InterfaceTangentAt (interface : Set PlanePoint) (normal : PlanePoint)
    (trace velocity : ℝ → PlanePoint) (t : ℝ) : Prop :=
  InterfaceContactAt interface trace t ∧
    (velocity t).1 * normal.1 + (velocity t).2 * normal.2 = 0

/-- A positive-speed endpoint has four disjoint continuation causes:
ordinary continuation in the current horizontal chart, replacement by a
vertical chart without interface contact, transverse interface contact, or
actual interface tangency.  In particular, horizontal-coordinate failure
alone cannot be treated as interface incidence or as loss of regularity. -/
theorem endpointContinuation_partition
    {interface : Set PlanePoint} {normal : PlanePoint}
    {trace velocity : ℝ → PlanePoint} {t : ℝ}
    (hregular : 0 <
      CMVCurvatureIntegration.euclideanSpeed velocity t) :
    (¬InterfaceContactAt interface trace t ∧ (velocity t).1 ≠ 0) ∨
    (¬InterfaceContactAt interface trace t ∧
      (velocity t).1 = 0 ∧ (velocity t).2 ≠ 0) ∨
    (InterfaceContactAt interface trace t ∧
      (velocity t).1 * normal.1 + (velocity t).2 * normal.2 ≠ 0) ∨
    InterfaceTangentAt interface normal trace velocity t := by
  by_cases hcontact : InterfaceContactAt interface trace t
  · by_cases htangent :
        (velocity t).1 * normal.1 + (velocity t).2 * normal.2 = 0
    · exact Or.inr (Or.inr (Or.inr ⟨hcontact, htangent⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hcontact, htangent⟩))
  · by_cases hx : (velocity t).1 = 0
    · have hy : (velocity t).2 ≠ 0 := by
        intro hy
        simp [CMVCurvatureIntegration.euclideanSpeed, hx, hy] at hregular
      exact Or.inr (Or.inl ⟨hcontact, hx, hy⟩)
    · exact Or.inl ⟨hcontact, hx⟩

/-! ## Independent curved/reversed/tangent specimen -/

namespace CurvedCarrierExample

/-- A literal curved carrier independent of every CMV configuration record. -/
def carrier : Set PlanePoint := {p | p.1 ^ 2 + p.2 ^ 2 < 1}

theorem carrier_open : IsOpen carrier :=
  isOpen_lt (by fun_prop) continuous_const

/-- Counterclockwise unit-circle trace, starting at the lower pole. -/
def trace (t : ℝ) : PlanePoint := (sin t, -cos t)

def velocity (t : ℝ) : PlanePoint := (cos t, sin t)

def acceleration (t : ℝ) : PlanePoint := (-sin t, cos t)

/-- The same geometric trace with its parameter reversed. -/
def reversedTrace (t : ℝ) : PlanePoint := (-sin t, -cos t)

def reversedVelocity (t : ℝ) : PlanePoint := (-cos t, sin t)

def reversedAcceleration (t : ℝ) : PlanePoint := (sin t, cos t)

theorem speed_eq_one (t : ℝ) :
    CMVCurvatureIntegration.euclideanSpeed velocity t = 1 := by
  unfold CMVCurvatureIntegration.euclideanSpeed velocity
  have htrig := Real.sin_sq_add_cos_sq t
  rw [show cos t ^ 2 + sin t ^ 2 = 1 by nlinarith]
  norm_num

theorem reversedSpeed_eq_one (t : ℝ) :
    CMVCurvatureIntegration.euclideanSpeed reversedVelocity t = 1 := by
  unfold CMVCurvatureIntegration.euclideanSpeed reversedVelocity
  have htrig := Real.sin_sq_add_cos_sq t
  rw [show (-cos t) ^ 2 + sin t ^ 2 = 1 by nlinarith]
  norm_num

/-- Every nondegenerate closed parameter interval gives an actual positive-speed
constant-curvature chart on the curved carrier boundary. -/
theorem regular (a b : ℝ) (hab : a < b) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      trace velocity acceleration 1 a b := by
  refine {
    start_lt_finish := hab
    curvature_ne_zero := one_ne_zero
    trace_fst_continuous := ?_
    trace_snd_continuous := ?_
    velocity_fst_continuous := ?_
    velocity_snd_continuous := ?_
    trace_fst_derivative := ?_
    trace_snd_derivative := ?_
    velocity_fst_derivative := ?_
    velocity_snd_derivative := ?_
    positive_speed := ?_
    signed_curvature := ?_
  }
  · exact Real.continuous_sin.continuousOn
  · exact Real.continuous_cos.neg.continuousOn
  · exact Real.continuous_cos.continuousOn
  · exact Real.continuous_sin.continuousOn
  · intro t _ht
    simpa only [trace, velocity] using Real.hasDerivAt_sin t
  · intro t _ht
    change HasDerivAt (fun u : ℝ => -cos u) (sin t) t
    exact ((Real.hasDerivAt_cos t).neg).congr_deriv (by ring)
  · intro t _ht
    simpa only [velocity, acceleration] using Real.hasDerivAt_cos t
  · intro t _ht
    simpa only [velocity, acceleration] using Real.hasDerivAt_sin t
  · intro t _ht
    rw [speed_eq_one]
    norm_num
  · intro t _ht
    rw [speed_eq_one]
    simp only [velocity, acceleration]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Parameter reversal flips signed curvature and preserves positive speed. -/
theorem reversedRegular (a b : ℝ) (hab : a < b) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      reversedTrace reversedVelocity reversedAcceleration (-1) a b := by
  refine {
    start_lt_finish := hab
    curvature_ne_zero := by norm_num
    trace_fst_continuous := ?_
    trace_snd_continuous := ?_
    velocity_fst_continuous := ?_
    velocity_snd_continuous := ?_
    trace_fst_derivative := ?_
    trace_snd_derivative := ?_
    velocity_fst_derivative := ?_
    velocity_snd_derivative := ?_
    positive_speed := ?_
    signed_curvature := ?_
  }
  · change ContinuousOn (fun t : ℝ => -sin t) (Icc a b)
    exact Real.continuous_sin.neg.continuousOn
  · change ContinuousOn (fun t : ℝ => -cos t) (Icc a b)
    exact Real.continuous_cos.neg.continuousOn
  · exact Real.continuous_cos.neg.continuousOn
  · exact Real.continuous_sin.continuousOn
  · intro t _ht
    change HasDerivAt (fun u : ℝ => -sin u) (-cos t) t
    exact (Real.hasDerivAt_sin t).neg
  · intro t _ht
    change HasDerivAt (fun u : ℝ => -cos u) (sin t) t
    exact ((Real.hasDerivAt_cos t).neg).congr_deriv (by ring)
  · intro t _ht
    change HasDerivAt (fun u : ℝ => -cos u) (sin t) t
    exact ((Real.hasDerivAt_cos t).neg).congr_deriv (by ring)
  · intro t _ht
    simpa only [reversedVelocity, reversedAcceleration] using
      Real.hasDerivAt_sin t
  · intro t _ht
    rw [reversedSpeed_eq_one]
    norm_num
  · intro t _ht
    rw [reversedSpeed_eq_one]
    simp only [reversedVelocity, reversedAcceleration]
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Every point of the concrete curved trace is on the actual planar frontier
of the independently defined carrier. -/
theorem trace_mem_frontier (t : ℝ) : trace t ∈ frontier carrier := by
  have hcircle :
      CMVFigureFour.circleValue (0, 0) 1 (trace t) = 0 := by
    unfold CMVFigureFour.circleValue trace
    dsimp only
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hclosure := CMVFigureFour.circleSide_mem_closure
    CMVFigureFour.CircleSide.inside (0, 0) (trace t) 1 zero_lt_one hcircle
  rw [frontier, carrier_open.interior_eq]
  constructor
  · simpa [carrier, CMVFigureFour.CircleSide.sign,
      CMVFigureFour.circleValue] using hclosure
  · change ¬(sin t ^ 2 + (-cos t) ^ 2 < 1)
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Reversal preserves the complete closed trace image, not only a chosen
point. -/
theorem reversed_image_eq :
    reversedTrace '' Icc (-(π / 2)) (π / 2) =
      trace '' Icc (-(π / 2)) (π / 2) := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨-t, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [ht.2]
    · nlinarith [ht.1]
    · simp [reversedTrace, trace]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨-t, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [ht.2]
    · nlinarith [ht.1]
    · simp [reversedTrace, trace]


/-- The concrete carrier supplies two oppositely parameterized regular charts
with the same closed image and a genuine overlap point. -/
theorem overlappingReversedCharts :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
        trace velocity acceleration 1 (-(π / 2)) (π / 2) ∧
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
        reversedTrace reversedVelocity reversedAcceleration (-1)
          (-(π / 2)) (π / 2) ∧
    trace 0 = reversedTrace 0 ∧
    reversedTrace '' Icc (-(π / 2)) (π / 2) =
      trace '' Icc (-(π / 2)) (π / 2) := by
  refine ⟨regular _ _ (by nlinarith [Real.pi_pos]),
    reversedRegular _ _ (by nlinarith [Real.pi_pos]), ?_, reversed_image_eq⟩
  simp [trace, reversedTrace]
/-- The forward and reversed charts overlap at the lower pole and select the
same support center after their tangent/curvature signs cancel. -/
theorem reversal_supportingCenter_eq :
    CMVCurvatureIntegration.centerInvariant trace
        (CMVCurvatureIntegration.normalizedTangent velocity) 1 0 =
      CMVCurvatureIntegration.centerInvariant reversedTrace
        (CMVCurvatureIntegration.normalizedTangent reversedVelocity) (-1) 0 := by
  apply supportingCenter_eq_of_reversedContact one_ne_zero
  · simp [trace, reversedTrace]
  · unfold CMVCurvatureIntegration.normalizedTangent
    rw [speed_eq_one, reversedSpeed_eq_one]
    norm_num [velocity, reversedVelocity]

/-- A genuine geometric interface tangent to the unit circle at its right
endpoint. -/
def tangentInterface : Set PlanePoint := {p | p.1 = 1}

theorem tangentEndpoint_actualInterfaceTangency :
    InterfaceTangentAt tangentInterface (1, 0) trace velocity (π / 2) := by
  simp [InterfaceTangentAt, InterfaceContactAt, tangentInterface, trace,
    velocity]

/-- At the right tangent endpoint the horizontal graph coordinate fails, while
the actual trace stays regular, lies on the carrier frontier, and satisfies the
same closed supporting-circle identity.  This coordinate fact is proved
independently of the actual interface-tangency theorem above. -/
theorem tangentEndpoint_is_regular_frontier_support :
    (velocity (π / 2)).1 = 0 ∧
      trace (π / 2) ∈ frontier carrier ∧
      ((trace (π / 2)).1 -
          (CMVCurvatureIntegration.centerInvariant trace
            (CMVCurvatureIntegration.normalizedTangent velocity) 1
              (-(π / 2))).1) ^ 2 +
        ((trace (π / 2)).2 -
          (CMVCurvatureIntegration.centerInvariant trace
            (CMVCurvatureIntegration.normalizedTangent velocity) 1
              (-(π / 2))).2) ^ 2 = 1 := by
  refine ⟨by simp [velocity], trace_mem_frontier (π / 2), ?_⟩
  have hregular := regular (-(π / 2)) (π / 2) (by nlinarith [Real.pi_pos])
  have hcircle := hregular.closed_circle_identity
    (s := -(π / 2)) (t := π / 2)
    ⟨le_rfl, by nlinarith [Real.pi_pos]⟩
    ⟨by nlinarith [Real.pi_pos], le_rfl⟩
  norm_num at hcircle ⊢
  exact hcircle

end CurvedCarrierExample
end CMVSourceBoundaryContinuation
