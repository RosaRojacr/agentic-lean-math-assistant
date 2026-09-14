/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVAEIntervalSections
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Local half-space atlas on the selected source representative

This module starts from pointwise open partial homeomorphisms which identify the
unchanged selected representative with one strict half-plane.  It derives an
actual interval parameterization of the frontier in a smaller open window,
compatibility of the occupied side on every overlap, and a finite subcover by
compactness of the frontier.  No global boundary curve, component count,
frontier connectedness, or geometric component inventory is assumed.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

abbrev PlanePoint := ℝ × ℝ

/-- The two possible occupied sides in flattened local coordinates. -/
inductive OccupiedHalfPlane where
  | lower
  | upper
  deriving DecidableEq

namespace OccupiedHalfPlane

/-- The strict occupied half-plane in local coordinates. -/
def carrier : OccupiedHalfPlane → Set PlanePoint
  | .lower => Set.univ ×ˢ Iio 0
  | .upper => Set.univ ×ˢ Ioi 0

/-- The common coordinate axis bounding either strict half-plane. -/
def axis : Set PlanePoint := Set.univ ×ˢ ({0} : Set ℝ)

/-- Both strict half-plane models have the coordinate axis as their complete
frontier. -/
theorem frontier_carrier (side : OccupiedHalfPlane) :
    frontier side.carrier = axis := by
  cases side <;> simp [carrier, axis, frontier_prod_eq]

end OccupiedHalfPlane

/-- Pointwise source datum: an open ambient coordinate change identifies the
actual carrier with exactly one strict occupied half-plane on its source.  The
chart is local because `coord.source` and `coord.target` may be proper open
sets.  It supplies no boundary parameterization or global exhaustion. -/
structure PointwiseHalfSpaceChart (O : Set PlanePoint)
    (p : {q : PlanePoint // q ∈ frontier O}) where
  side : OccupiedHalfPlane
  coord : OpenPartialHomeomorph PlanePoint PlanePoint
  base_mem_source : p.1 ∈ coord.source
  coord_base : coord p.1 = (0, 0)
  carrier_image : coord.IsImage O side.carrier

namespace PointwiseHalfSpaceChart

variable {O : Set PlanePoint} {p : {q : PlanePoint // q ∈ frontier O}}

/-- Build a pointwise chart by restricting an ambient homeomorphism to an
explicit open neighborhood on which carrier membership is the chosen
half-plane model.  This constructor is useful for concrete specimens; the
generic producer never assumes a global homeomorphism. -/
noncomputable def ofHomeomorph (side : OccupiedHalfPlane)
    (H : PlanePoint ≃ₜ PlanePoint) (W : Set PlanePoint)
    (hWopen : IsOpen W) (hpW : p.1 ∈ W)
    (hbase : H p.1 = (0, 0))
    (hlocal : ∀ q ∈ W, H q ∈ side.carrier ↔ q ∈ O) :
    PointwiseHalfSpaceChart O p where
  side := side
  coord := H.toOpenPartialHomeomorphOfImageEq W hWopen (H '' W) rfl
  base_mem_source := hpW
  coord_base := hbase
  carrier_image := by
    intro q hq
    exact hlocal q hq

/-- The flattened origin belongs to the target of every pointwise chart. -/
theorem zero_mem_target (A : PointwiseHalfSpaceChart O p) :
    (0, 0) ∈ A.coord.target := by
  rw [← A.coord_base]
  exact A.coord.map_source A.base_mem_source

/-- The pointwise carrier identity transports the actual complete frontier to
the coordinate axis, with no regularity or global-curve premise. -/
theorem frontier_image (A : PointwiseHalfSpaceChart O p) :
    A.coord.IsImage (frontier O) OccupiedHalfPlane.axis := by
  simpa only [OccupiedHalfPlane.frontier_carrier] using A.carrier_image.frontier

end PointwiseHalfSpaceChart

/-- An actual local interval chart obtained by shrinking a pointwise ambient
half-space chart to a coordinate ball. -/
structure ActualFrontierIntervalChart (O : Set PlanePoint)
    (p : {q : PlanePoint // q ∈ frontier O}) where
  ambient : PointwiseHalfSpaceChart O p
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset_target : Metric.ball (0, 0) radius ⊆ ambient.coord.target

namespace ActualFrontierIntervalChart

variable {O : Set PlanePoint} {p : {q : PlanePoint // q ∈ frontier O}}

/-- The open ambient window supporting the derived interval chart. -/
def window (A : ActualFrontierIntervalChart O p) : Set PlanePoint :=
  A.ambient.coord.source ∩
    A.ambient.coord ⁻¹' Metric.ball (0, 0) A.radius

/-- The actual frontier trace in the original coordinates. -/
def trace (A : ActualFrontierIntervalChart O p) (t : ℝ) : PlanePoint :=
  A.ambient.coord.symm (t, 0)

/-- The shrunken source window is open. -/
theorem isOpen_window (A : ActualFrontierIntervalChart O p) :
    IsOpen A.window := by
  exact A.ambient.coord.isOpen_inter_preimage Metric.isOpen_ball

/-- The base frontier point remains in the shrunken source window. -/
theorem base_mem_window (A : ActualFrontierIntervalChart O p) :
    p.1 ∈ A.window := by
  refine ⟨A.ambient.base_mem_source, ?_⟩
  change A.ambient.coord p.1 ∈ Metric.ball (0, 0) A.radius
  rw [A.ambient.coord_base]
  exact Metric.mem_ball_self A.radius_pos

private theorem axisPoint_mem_ball (A : ActualFrontierIntervalChart O p)
    {t : ℝ} (ht : t ∈ Ioo (-A.radius) A.radius) :
    (t, 0) ∈ Metric.ball ((0, 0) : PlanePoint) A.radius := by
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  constructor
  · simpa only [Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht
  · simpa using A.radius_pos

/-- Every parameter in the chart interval lies in the target of the ambient
partial homeomorphism. -/
theorem axisPoint_mem_target (A : ActualFrontierIntervalChart O p)
    {t : ℝ} (ht : t ∈ Ioo (-A.radius) A.radius) :
    (t, 0) ∈ A.ambient.coord.target :=
  A.ball_subset_target (A.axisPoint_mem_ball ht)

/-- The derived trace is continuous on its actual parameter interval. -/
theorem continuousOn_trace (A : ActualFrontierIntervalChart O p) :
    ContinuousOn A.trace (Ioo (-A.radius) A.radius) := by
  exact A.ambient.coord.continuousOn_symm.comp
    (continuous_id.prodMk continuous_const).continuousOn
    (fun _t ht => A.axisPoint_mem_target ht)

/-- The derived trace does not retrace inside its local parameter interval. -/
theorem injOn_trace (A : ActualFrontierIntervalChart O p) :
    Set.InjOn A.trace (Ioo (-A.radius) A.radius) := by
  intro s hs t ht hst
  have hsTarget := A.axisPoint_mem_target hs
  have htTarget := A.axisPoint_mem_target ht
  have hcoords := congrArg A.ambient.coord hst
  simpa only [trace, A.ambient.coord.right_inv hsTarget,
    A.ambient.coord.right_inv htTarget, Prod.mk.injEq, and_true] using hcoords

/-- The local trace image is exactly the actual complete frontier inside the
shrunken source window. -/
theorem frontier_inter_window (A : ActualFrontierIntervalChart O p) :
    frontier O ∩ A.window =
      A.trace '' Ioo (-A.radius) A.radius := by
  ext q
  constructor
  · rintro ⟨hqFrontier, hqSource, hqBall⟩
    have hqAxis : A.ambient.coord q ∈ OccupiedHalfPlane.axis :=
      (A.ambient.frontier_image.apply_mem_iff hqSource).2 hqFrontier
    have hqZero : (A.ambient.coord q).2 = 0 := hqAxis.2
    have hqDist : dist (A.ambient.coord q).1 0 < A.radius := by
      change A.ambient.coord q ∈ Metric.ball (0, 0) A.radius at hqBall
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hqBall
      exact hqBall.1
    have ht : (A.ambient.coord q).1 ∈ Ioo (-A.radius) A.radius := by
      simpa only [Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hqDist
    refine ⟨(A.ambient.coord q).1, ht, ?_⟩
    unfold trace
    rw [← hqZero]
    exact A.ambient.coord.left_inv hqSource
  · rintro ⟨t, ht, rfl⟩
    have htBall := A.axisPoint_mem_ball ht
    have htTarget := A.axisPoint_mem_target ht
    have htraceSource : A.trace t ∈ A.ambient.coord.source :=
      A.ambient.coord.map_target htTarget
    have hcoord : A.ambient.coord (A.trace t) = (t, 0) := by
      exact A.ambient.coord.right_inv htTarget
    have haxis : (t, 0) ∈ OccupiedHalfPlane.axis := by
      simp [OccupiedHalfPlane.axis]
    have hfrontier : A.trace t ∈ frontier O := by
      exact (A.ambient.frontier_image.apply_mem_iff htraceSource).1
        (by simpa only [hcoord] using haxis)
    refine ⟨hfrontier, htraceSource, ?_⟩
    change A.ambient.coord (A.trace t) ∈ Metric.ball (0, 0) A.radius
    rw [hcoord]
    exact htBall

/-- On every overlap, the two coordinate transition descriptions assign the
same occupied label to each actual point.  The literal `lower`/`upper` tags may
differ because a transition may reverse the transverse coordinate. -/
theorem occupied_transition_iff
    {q : PlanePoint} (A : ActualFrontierIntervalChart O p)
    {p' : {z : PlanePoint // z ∈ frontier O}}
    (B : ActualFrontierIntervalChart O p')
    (hqA : q ∈ A.window) (hqB : q ∈ B.window) :
    A.ambient.coord q ∈ A.ambient.side.carrier ↔
      B.ambient.coord q ∈ B.ambient.side.carrier := by
  exact (A.ambient.carrier_image.apply_mem_iff hqA.1).trans
    (B.ambient.carrier_image.apply_mem_iff hqB.1).symm

end ActualFrontierIntervalChart

namespace PointwiseHalfSpaceChart

variable {O : Set PlanePoint} {p : {q : PlanePoint // q ∈ frontier O}}

/-- Openness of the coordinate target supplies a positive radius on which the
actual interval chart is defined. -/
theorem exists_actualFrontierIntervalChart
    (A : PointwiseHalfSpaceChart O p) :
    Nonempty (ActualFrontierIntervalChart O p) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp A.coord.open_target
    (0, 0) A.zero_mem_target
  exact ⟨{
    ambient := A
    radius := r
    radius_pos := hr
    ball_subset_target := hball
  }⟩

end PointwiseHalfSpaceChart

/-- A genuinely pointwise boundary atlas.  Its index is the actual frontier;
there is no supplied finite chart list, component partition, curve, or order. -/
structure BoundaryHalfSpaceAtlas (O : Set PlanePoint) where
  chart : ∀ p : {q : PlanePoint // q ∈ frontier O},
    PointwiseHalfSpaceChart O p

namespace BoundaryHalfSpaceAtlas

variable {O : Set PlanePoint}

/-- Choose the canonically needed shrunken interval chart at one actual
frontier point. -/
noncomputable def intervalAt (A : BoundaryHalfSpaceAtlas O)
    (p : {q : PlanePoint // q ∈ frontier O}) :
    ActualFrontierIntervalChart O p :=
  Classical.choice (A.chart p).exists_actualFrontierIntervalChart

/-- The chosen interval chart still contains its indexing frontier point. -/
theorem base_mem_intervalAt_window (A : BoundaryHalfSpaceAtlas O)
    (p : {q : PlanePoint // q ∈ frontier O}) :
    p.1 ∈ (A.intervalAt p).window :=
  (A.intervalAt p).base_mem_window

end BoundaryHalfSpaceAtlas

/-- A finite refinement selected from the pointwise atlas.  The finite centers
are obtained from compactness; they are not a geometric component inventory. -/
structure FiniteIntervalRefinement (O : Set PlanePoint) where
  centers : Finset {q : PlanePoint // q ∈ frontier O}
  chart : ∀ i : centers,
    ActualFrontierIntervalChart O i.1
  covers : frontier O ⊆ ⋃ i : centers, (chart i).window

namespace FiniteIntervalRefinement

variable {O : Set PlanePoint}

/-- Every pair of charts in the finite refinement has compatible occupied-side
labels on its overlap. -/
theorem occupied_transition_iff (R : FiniteIntervalRefinement O)
    (i j : R.centers) {q : PlanePoint}
    (hqi : q ∈ (R.chart i).window) (hqj : q ∈ (R.chart j).window) :
    (R.chart i).ambient.coord q ∈ (R.chart i).ambient.side.carrier ↔
      (R.chart j).ambient.coord q ∈ (R.chart j).ambient.side.carrier :=
  (R.chart i).occupied_transition_iff (R.chart j) hqi hqj

end FiniteIntervalRefinement

namespace BoundaryHalfSpaceAtlas

/-- A bounded planar carrier has compact frontier, so every pointwise
half-space atlas admits a finite actual interval-chart refinement. -/
theorem exists_finiteIntervalRefinement {O : Set PlanePoint}
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O) :
    Nonempty (FiniteIntervalRefinement O) := by
  classical
  have hcompact : IsCompact (frontier O) := by
    exact isCompact_iff_isClosed_bounded.2
      ⟨isClosed_frontier, hObounded.closure.subset frontier_subset_closure⟩
  have hcover : frontier O ⊆
      ⋃ p : {q : PlanePoint // q ∈ frontier O}, (A.intervalAt p).window := by
    intro q hq
    exact mem_iUnion.2 ⟨⟨q, hq⟩, A.base_mem_intervalAt_window ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover
    (fun p : {q : PlanePoint // q ∈ frontier O} => (A.intervalAt p).window)
    (fun p => (A.intervalAt p).isOpen_window) hcover
  exact ⟨{
    centers := t
    chart := fun i => A.intervalAt i.1
    covers := by simpa only [Set.iUnion_subtype] using ht
  }⟩

end BoundaryHalfSpaceAtlas

open CMVRelaxation
open CMVSourceClassification

/-- Explicit upstream hypotheses for topology on the selected representative.
None is inferred here from source minimality.  In particular, local ambient
charts remain supplied pointwise while finite refinement is derived below. -/
structure SelectedBoundaryTopologyInput (E U : Set PlanePoint) where
  representative_nonempty : U.Nonempty
  representative_open : IsOpen U
  representative_bounded : Bornology.IsBounded U
  representative_connected : IsConnected U
  carrier_ae : E =ᵐ[volume] U
  interval_sections : HasAEIntervalHorizontalSections E
  local_atlas : BoundaryHalfSpaceAtlas (aeOpenRepresentative E)

/-- Output of the local topology producer.  It records only selected-set
semantics, all-height interval sections, and the compactness-derived finite
local atlas.  Global component loops are deliberately not part of this object. -/
structure SelectedBoundaryAtlasOutput (E : Set PlanePoint) where
  selected_nonempty : (aeOpenRepresentative E).Nonempty
  selected_open : IsOpen (aeOpenRepresentative E)
  selected_bounded : Bornology.IsBounded (aeOpenRepresentative E)
  selected_connected : IsConnected (aeOpenRepresentative E)
  selected_ae : aeOpenRepresentative E =ᵐ[volume] E
  all_height_intervals : ∀ y : ℝ,
    horizontalSection (aeOpenRepresentative E) y = ∅ ∨
      ∃ a b : ℝ, a < b ∧
        horizontalSection (aeOpenRepresentative E) y = Ioo a b
  finite_refinement : FiniteIntervalRefinement (aeOpenRepresentative E)

namespace SelectedBoundaryTopologyInput

variable {E U : Set PlanePoint}

/-- Produce actual frontier interval charts and a finite compatible refinement
on `O = aeOpenRepresentative E` from exactly the explicit representative,
section, and pointwise local-chart hypotheses. -/
noncomputable def produce (D : SelectedBoundaryTopologyInput E U) :
    SelectedBoundaryAtlasOutput E where
  selected_nonempty :=
    D.representative_nonempty.mono
      (open_subset_aeOpenRepresentative D.representative_open D.carrier_ae)
  selected_open := isOpen_aeOpenRepresentative E
  selected_bounded :=
    isBounded_aeOpenRepresentative_of_ae D.carrier_ae D.representative_bounded
  selected_connected :=
    isConnected_aeOpenRepresentative_of_open_ae D.representative_open
      D.carrier_ae D.representative_connected
  selected_ae := aeOpenRepresentative_ae_eq D.representative_open D.carrier_ae
  all_height_intervals := fun y =>
    horizontalSection_empty_or_Ioo_aeOpenRepresentative
      D.representative_open D.carrier_ae D.representative_bounded
      D.interval_sections y
  finite_refinement := Classical.choice
    (D.local_atlas.exists_finiteIntervalRefinement
      (isBounded_aeOpenRepresentative_of_ae D.carrier_ae
        D.representative_bounded))

end SelectedBoundaryTopologyInput

end CMVBoundaryLocalAtlas
