/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryFiniteChartCuts
import CMVBoundaryGraphAtlas
import CMVBoundaryLocalAtlasSpecimen

/-!
# Independent specimens for finite compact chart cuts

The independently defined open unit disk and nonconvex shelf polygon instantiate
the same compactness-selected finite subarc construction.  Neither application
supplies a finite edge inventory, endpoint adjacency, cyclic order, or global
boundary trace.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

open BoundaryHalfSpaceAtlas
open ActualFrontierIntervalChart

namespace UnitDisk

/-- Finite compact chart cores for the independently defined unit disk. -/
noncomputable def finiteChartCuts : FiniteChartCutSystem boundaryAtlas :=
  boundaryAtlas.finiteChartCutSystem
    CMVFigureFour.FiniteCrossingExample.isBounded_openUnitDisk

/-- Relative interiors of the disk's selected compact subarcs cover its complete
actual frontier subtype. -/
theorem finiteChartCuts_cover :
    (⋃ i : finiteChartCuts.centers,
      (finiteChartCuts.arc i).coreInterior) = Set.univ := by
  exact Set.eq_univ_of_univ_subset finiteChartCuts.covers

/-- Every selected disk subarc is an embedded compact interval with distinct
actual endpoints, and its closure is exactly that compact interval. -/
theorem finiteChartCuts_arc_realization (i : finiteChartCuts.centers) :
    Topology.IsClosedEmbedding (finiteChartCuts.arc i).corePoint ∧
      closure (finiteChartCuts.arc i).coreInterior =
        (finiteChartCuts.arc i).closedCore ∧
      (finiteChartCuts.arc i).leftEndpoint ≠
        (finiteChartCuts.arc i).rightEndpoint :=
  ⟨(finiteChartCuts.arc i).isClosedEmbedding_corePoint,
    (finiteChartCuts.arc i).closure_coreInterior,
    (finiteChartCuts.arc i).leftEndpoint_ne_rightEndpoint⟩

/-- Every component of the disk frontier left after the finite actual endpoint
cuts is confined to one selected compact embedded subarc. -/
theorem finiteChartCuts_component_confined (x : finiteChartCuts.CutSpace) :
    ∃ i : finiteChartCuts.centers,
      ∀ y ∈ connectedComponent x,
        y.1 ∈ (finiteChartCuts.arc i).closedCore :=
  finiteChartCuts.exists_arc_containing_connectedComponent x

/-- The disk endpoint cuts produce only finitely many connected pieces. -/
theorem finiteChartCuts_finite_components :
    Finite (ConnectedComponents finiteChartCuts.CutSpace) :=
  finiteChartCuts.finite_cutSpace_connectedComponents

/-- Every disk cut piece is genuinely an open interval. -/
theorem finiteChartCuts_piece_homeomorph_Ioo
    (x : finiteChartCuts.CutSpace) :
    ∃ a b : ℝ, a < b ∧
      Nonempty (finiteChartCuts.CutComponent x ≃ₜ (Ioo a b : Set ℝ)) :=
  finiteChartCuts.exists_cutComponent_homeomorph_Ioo x

/-- In any selected disk chart containing a cut piece, its actual closure is
the compact embedded closed arc between two distinct global cut points. -/
theorem finiteChartCuts_piece_closure
    (i : finiteChartCuts.centers) (x : finiteChartCuts.CutSpace)
    (hx : x.1 ∈ (finiteChartCuts.arc i).coreInterior) :
    closure (finiteChartCuts.cutComponentImage x) =
        finiteChartCuts.cutComponentClosedArc i x ∧
      IsCompact (finiteChartCuts.cutComponentClosedArc i x) ∧
      finiteChartCuts.cutComponentLeftEndpoint i x hx ∈
        finiteChartCuts.cutPoints ∧
      finiteChartCuts.cutComponentRightEndpoint i x hx ∈
        finiteChartCuts.cutPoints ∧
      finiteChartCuts.cutComponentLeftEndpoint i x hx ≠
        finiteChartCuts.cutComponentRightEndpoint i x hx :=
  ⟨finiteChartCuts.closure_cutComponentImage i x hx,
    finiteChartCuts.isCompact_cutComponentClosedArc i x,
    finiteChartCuts.cutComponentLeftEndpoint_mem_cutPoints i x hx,
    finiteChartCuts.cutComponentRightEndpoint_mem_cutPoints i x hx,
    finiteChartCuts.cutComponentLeftEndpoint_ne_rightEndpoint i x hx⟩


/-- The derived finite disk arcs have pairwise-disjoint interiors and their
compact closures exhaust the complete actual circle frontier. -/
theorem finiteArcSystem_exhausts :
    (Pairwise fun e f : finiteChartCuts.ArcIndex =>
      Disjoint (finiteChartCuts.finiteArcInterior e)
        (finiteChartCuts.finiteArcInterior f)) ∧
    (⋃ e : finiteChartCuts.ArcIndex,
      finiteChartCuts.finiteArcClosure e) = Set.univ := by
  exact ⟨fun _ _ hef => finiteChartCuts.disjoint_finiteArcInterior hef,
    finiteChartCuts.iUnion_finiteArcClosure_eq_univ⟩

/-- Every derived compact disk arc adds exactly two distinct actual cut
endpoints to its open interior. -/
theorem finiteArcSystem_endpoint_boundary
    (e : finiteChartCuts.ArcIndex) :
    finiteChartCuts.finiteArcClosure e \
        finiteChartCuts.finiteArcInterior e =
      ({finiteChartCuts.finiteArcLeftEndpoint e,
        finiteChartCuts.finiteArcRightEndpoint e} :
        Set (FrontierSpace CMVFigureFour.FiniteCrossingExample.openUnitDisk)) ∧
      finiteChartCuts.finiteArcLeftEndpoint e ≠
        finiteChartCuts.finiteArcRightEndpoint e :=
  ⟨finiteChartCuts.finiteArcClosure_sdiff_finiteArcInterior e,
    finiteChartCuts.finiteArcLeftEndpoint_ne_rightEndpoint e⟩

/-- Every actual disk cut point is an endpoint of at least one derived compact
arc. -/
theorem finiteArcSystem_cutPoint_incident
    (v : finiteChartCuts.cutPoints) :
    Nonempty (finiteChartCuts.IncidentArc v) :=
  finiteChartCuts.incidentArc_nonempty v

/-- The selected disk cuts are exactly the endpoint vertices of the derived
finite arc system. -/
theorem finiteArcSystem_endpointPairs_exhaustCuts :
    (⋃ e : finiteChartCuts.ArcIndex,
      ({finiteChartCuts.finiteArcLeftEndpoint e,
        finiteChartCuts.finiteArcRightEndpoint e} :
        Set (FrontierSpace
          CMVFigureFour.FiniteCrossingExample.openUnitDisk))) =
      (finiteChartCuts.cutPoints :
        Set (FrontierSpace
          CMVFigureFour.FiniteCrossingExample.openUnitDisk)) :=
  finiteChartCuts.iUnion_finiteArcEndpointPair_eq_cutPoints


/-- The derived compact arcs belonging to any actual disk component exhaust
that complete component. -/
theorem finiteArcSystem_component_exhausts
    (p : FrontierSpace CMVFigureFour.FiniteCrossingExample.openUnitDisk) :
    (⋃ e : finiteChartCuts.ComponentArc p,
      finiteChartCuts.finiteArcClosure e.1) =
        connectedComponent p :=
  finiteChartCuts.iUnion_componentArcClosure_eq_connectedComponent p

end UnitDisk

namespace StepPolygon

/-- Finite compact chart cores for the literal nonconvex shelf polygon. -/
noncomputable def finiteChartCuts : FiniteChartCutSystem boundaryAtlas :=
  boundaryAtlas.finiteChartCutSystem isBounded_carrier

/-- Relative interiors of the polygon's selected compact subarcs cover all six
literal frontier sides, including every corner and the reentrant shelf point. -/
theorem finiteChartCuts_cover :
    (⋃ i : finiteChartCuts.centers,
      (finiteChartCuts.arc i).coreInterior) = Set.univ := by
  exact Set.eq_univ_of_univ_subset finiteChartCuts.covers

/-- Every selected polygon subarc is an embedded compact interval with distinct
actual endpoints, and its closure is exactly that compact interval. -/
theorem finiteChartCuts_arc_realization (i : finiteChartCuts.centers) :
    Topology.IsClosedEmbedding (finiteChartCuts.arc i).corePoint ∧
      closure (finiteChartCuts.arc i).coreInterior =
        (finiteChartCuts.arc i).closedCore ∧
      (finiteChartCuts.arc i).leftEndpoint ≠
        (finiteChartCuts.arc i).rightEndpoint :=
  ⟨(finiteChartCuts.arc i).isClosedEmbedding_corePoint,
    (finiteChartCuts.arc i).closure_coreInterior,
    (finiteChartCuts.arc i).leftEndpoint_ne_rightEndpoint⟩

/-- Every component of the cut polygon frontier, including one meeting a
reentrant-corner chart, is confined to one selected compact embedded subarc. -/
theorem finiteChartCuts_component_confined (x : finiteChartCuts.CutSpace) :
    ∃ i : finiteChartCuts.centers,
      ∀ y ∈ connectedComponent x,
        y.1 ∈ (finiteChartCuts.arc i).closedCore :=
  finiteChartCuts.exists_arc_containing_connectedComponent x

/-- The polygon endpoint cuts produce only finitely many connected pieces. -/
theorem finiteChartCuts_finite_components :
    Finite (ConnectedComponents finiteChartCuts.CutSpace) :=
  finiteChartCuts.finite_cutSpace_connectedComponents

/-- Every polygon cut piece, including pieces beside the reentrant shelf, is
genuinely an open interval. -/
theorem finiteChartCuts_piece_homeomorph_Ioo
    (x : finiteChartCuts.CutSpace) :
    ∃ a b : ℝ, a < b ∧
      Nonempty (finiteChartCuts.CutComponent x ≃ₜ (Ioo a b : Set ℝ)) :=
  finiteChartCuts.exists_cutComponent_homeomorph_Ioo x

/-- In any selected polygon chart containing a cut piece, its actual closure
is the compact embedded closed arc between two distinct global cut points. -/
theorem finiteChartCuts_piece_closure
    (i : finiteChartCuts.centers) (x : finiteChartCuts.CutSpace)
    (hx : x.1 ∈ (finiteChartCuts.arc i).coreInterior) :
    closure (finiteChartCuts.cutComponentImage x) =
        finiteChartCuts.cutComponentClosedArc i x ∧
      IsCompact (finiteChartCuts.cutComponentClosedArc i x) ∧
      finiteChartCuts.cutComponentLeftEndpoint i x hx ∈
        finiteChartCuts.cutPoints ∧
      finiteChartCuts.cutComponentRightEndpoint i x hx ∈
        finiteChartCuts.cutPoints ∧
      finiteChartCuts.cutComponentLeftEndpoint i x hx ≠
        finiteChartCuts.cutComponentRightEndpoint i x hx :=
  ⟨finiteChartCuts.closure_cutComponentImage i x hx,
    finiteChartCuts.isCompact_cutComponentClosedArc i x,
    finiteChartCuts.cutComponentLeftEndpoint_mem_cutPoints i x hx,
    finiteChartCuts.cutComponentRightEndpoint_mem_cutPoints i x hx,
    finiteChartCuts.cutComponentLeftEndpoint_ne_rightEndpoint i x hx⟩


/-- The derived finite polygon arcs have pairwise-disjoint interiors and their
compact closures exhaust every side, corner, and reentrant frontier point. -/
theorem finiteArcSystem_exhausts :
    (Pairwise fun e f : finiteChartCuts.ArcIndex =>
      Disjoint (finiteChartCuts.finiteArcInterior e)
        (finiteChartCuts.finiteArcInterior f)) ∧
    (⋃ e : finiteChartCuts.ArcIndex,
      finiteChartCuts.finiteArcClosure e) = Set.univ := by
  exact ⟨fun _ _ hef => finiteChartCuts.disjoint_finiteArcInterior hef,
    finiteChartCuts.iUnion_finiteArcClosure_eq_univ⟩

/-- Every derived compact polygon arc adds exactly two distinct actual cut
endpoints to its open interior. -/
theorem finiteArcSystem_endpoint_boundary
    (e : finiteChartCuts.ArcIndex) :
    finiteChartCuts.finiteArcClosure e \
        finiteChartCuts.finiteArcInterior e =
      ({finiteChartCuts.finiteArcLeftEndpoint e,
        finiteChartCuts.finiteArcRightEndpoint e} :
        Set (FrontierSpace carrier)) ∧
      finiteChartCuts.finiteArcLeftEndpoint e ≠
        finiteChartCuts.finiteArcRightEndpoint e :=
  ⟨finiteChartCuts.finiteArcClosure_sdiff_finiteArcInterior e,
    finiteChartCuts.finiteArcLeftEndpoint_ne_rightEndpoint e⟩

/-- Every actual polygon cut point is an endpoint of at least one derived
compact arc. -/
theorem finiteArcSystem_cutPoint_incident
    (v : finiteChartCuts.cutPoints) :
    Nonempty (finiteChartCuts.IncidentArc v) :=
  finiteChartCuts.incidentArc_nonempty v

/-- The selected polygon cuts are exactly the endpoint vertices of the derived
finite arc system. -/
theorem finiteArcSystem_endpointPairs_exhaustCuts :
    (⋃ e : finiteChartCuts.ArcIndex,
      ({finiteChartCuts.finiteArcLeftEndpoint e,
        finiteChartCuts.finiteArcRightEndpoint e} :
        Set (FrontierSpace carrier))) =
      (finiteChartCuts.cutPoints : Set (FrontierSpace carrier)) :=
  finiteChartCuts.iUnion_finiteArcEndpointPair_eq_cutPoints


/-- The derived compact arcs belonging to any actual polygon component exhaust
that complete component. -/
theorem finiteArcSystem_component_exhausts
    (p : FrontierSpace carrier) :
    (⋃ e : finiteChartCuts.ComponentArc p,
      finiteChartCuts.finiteArcClosure e.1) =
        connectedComponent p :=
  finiteChartCuts.iUnion_componentArcClosure_eq_connectedComponent p

end StepPolygon

end CMVBoundaryLocalAtlas
