import CMVBoundaryFiniteChartCutsSpecimen

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.parameterHomeomorph
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.frontierChart
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.frontierChartedSpace
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.frontierLocallyPathConnectedSpace
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.isConnected_localDomain
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.localDomain_subset_connectedComponent
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.parameterInterval_not_isCompact
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.isConnected_negativeParameterBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.isConnected_positiveParameterBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.isConnected_negativeBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.isConnected_positiveBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.disjoint_negativeBranch_positiveBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.negativeBranch_union_positiveBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.base_mem_closure_negativeBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.base_mem_closure_positiveBranch
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.twoBranchLocalTopology
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finite_frontier_connectedComponents
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.isPathConnected_componentAt
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.isCompact_componentAt
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.isOpen_componentAt_preimage
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.infinite_connectedComponent
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.connectedComponent_not_subset_localDomain
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.exists_mem_connectedComponent_not_mem_localDomain
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.infinite_componentAt
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.exists_mem_componentAt_not_mem_window
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finiteFrontierComponentDecomposition
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteFrontierComponentDecomposition.iUnion_componentAt_eq_frontier
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteFrontierComponentDecomposition.pairwise_disjoint_componentAt
#print axioms CMVBoundaryLocalAtlas.ConnectedPuncture.base_mem_closure_componentImage
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.puncturedComponent_meets_localArm
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.punctured_connectedComponent_eq_negative_or_positive
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.punctured_connectedComponents_eq_negative_or_positive
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.puncturedComponentClass_surjective
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finite_punctured_connectedComponents
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.punctured_connectedComponents_natCard_le_two
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteComponentDecomposition_exhausts
#print axioms CMVBoundaryLocalAtlas.StepPolygon.frontier_locallyPathConnected
#print axioms CMVBoundaryLocalAtlas.StepPolygon.componentAt_infinite
#print axioms CMVBoundaryLocalAtlas.StepPolygon.component_exits_intervalAt_window
#print axioms CMVBoundaryLocalAtlas.StepPolygon.intervalAt_twoBranchLocalTopology
#print axioms CMVBoundaryLocalAtlas.StepPolygon.puncturedComponentCount_le_two
#print axioms CMVBoundaryLocalAtlas.SmoothGraphAtlas.PointwiseHalfSpaceChart.nonempty_ofOrientedSmoothGraphGerm
#print axioms CMVBoundaryLocalAtlas.UnitDisk.boundaryAtlas
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteComponentDecomposition_exhausts
#print axioms CMVBoundaryLocalAtlas.UnitDisk.frontier_locallyPathConnected
#print axioms CMVBoundaryLocalAtlas.UnitDisk.componentAt_infinite
#print axioms CMVBoundaryLocalAtlas.UnitDisk.component_exits_intervalAt_window
#print axioms CMVBoundaryLocalAtlas.UnitDisk.intervalAt_twoBranchLocalTopology
#print axioms CMVBoundaryLocalAtlas.UnitDisk.puncturedComponentCount_le_two
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.isClosedEmbedding_corePoint
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.closure_coreInterior
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.closedCore_sdiff_coreInterior
#print axioms CMVBoundaryLocalAtlas.ActualFrontierIntervalChart.leftEndpoint_ne_rightEndpoint
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.exists_finiteChartCutSystem
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.leftEndpoint_mem_cutPoints
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.rightEndpoint_mem_cutPoints
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.isClopen_closedCoreInCutSpace
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.connectedComponent_subset_closedCore
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.exists_arc_containing_connectedComponent
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.iUnion_closedCore_eq_univ
#print axioms CMVBoundaryLocalAtlas.RealFiniteCuts.finite_connectedComponents_compl
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finite_coreCutParameter_connectedComponents
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.coreCutPointHomeomorph
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finite_cutSpace_connectedComponents
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.disjoint_cutComponentImage
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.iUnion_cutComponentImage_eq_cutSpaceCarrier
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.exists_cutComponent_homeomorph_Ioo
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.closure_cutComponentImage
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.isCompact_cutComponentClosedArc
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.cutComponentLeftEndpoint_mem_cutPoints
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.cutComponentRightEndpoint_mem_cutPoints
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.cutComponentLeftEndpoint_ne_rightEndpoint
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteChartCuts_cover
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteChartCuts_arc_realization
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteChartCuts_component_confined
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteChartCuts_finite_components
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteChartCuts_piece_homeomorph_Ioo
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteChartCuts_piece_closure
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteChartCuts_cover
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteChartCuts_arc_realization
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteChartCuts_component_confined
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteChartCuts_finite_components
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteChartCuts_piece_homeomorph_Ioo
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteChartCuts_piece_closure
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.frontier_punctured_nhds_neBot
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.disjoint_finiteArcInterior
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.iUnion_finiteArcInterior_eq_cutSpaceCarrier
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.dense_cutSpaceCarrier
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.iUnion_finiteArcClosure_eq_univ
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finiteArcClosure_eq_selectedClosedArc
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finiteArc_endpoints_mem_cutPoints
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finiteArcLeftEndpoint_ne_rightEndpoint
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.cutComponentClosedArc_sdiff_cutComponentImage
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finiteArcClosure_sdiff_finiteArcInterior
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.cutPoint_mem_finiteArcClosure_iff_endpoint
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.incidentArc_nonempty
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.finiteArcClosure_subset_connectedComponent
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.iUnion_componentArcClosure_eq_connectedComponent
#print axioms CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.iUnion_finiteArcEndpointPair_eq_cutPoints
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteArcSystem_exhausts
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteArcSystem_endpoint_boundary
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteArcSystem_cutPoint_incident
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteArcSystem_component_exhausts
#print axioms CMVBoundaryLocalAtlas.UnitDisk.finiteArcSystem_endpointPairs_exhaustCuts
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteArcSystem_exhausts
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteArcSystem_endpoint_boundary
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteArcSystem_cutPoint_incident
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteArcSystem_component_exhausts
#print axioms CMVBoundaryLocalAtlas.StepPolygon.finiteArcSystem_endpointPairs_exhaustCuts


namespace CMVBoundaryLocalAtlas

open BoundaryHalfSpaceAtlas

/-- Compiled dependency contract: boundedness and the pointwise atlas remain
explicit; no global trace, component count, or boundary order is accepted. -/
example {O : Set PlanePoint} (A : BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O) :
    ∃ D : FiniteFrontierComponentDecomposition O,
      (⋃ i : D.index, componentAt (D.center i)) = frontier O ∧
      Pairwise fun i j : D.index =>
        Disjoint (componentAt (D.center i)) (componentAt (D.center j)) := by
  let D := A.finiteFrontierComponentDecomposition hObounded
  exact ⟨D, D.iUnion_componentAt_eq_frontier,
    D.pairwise_disjoint_componentAt⟩

/-- Compiled global-transition contract: after deleting any point from its
complete frontier component, the two actual local arms account for every
remaining connected component. -/
example {O : Set PlanePoint} (A : BoundaryHalfSpaceAtlas O)
    {p : FrontierSpace O} :
    Nat.card
      (ConnectedComponents
        (PuncturedFrontierComponent p)) ≤ 2 :=
  A.punctured_connectedComponents_natCard_le_two (A.intervalAt p)

/-- Compiled finite-cut contract: boundedness and the actual pointwise atlas
derive the finite arc centers and endpoint cuts.  No edge list, endpoint
adjacency, cyclic order, or global trace is an argument. -/
example {O : Set PlanePoint} (A : BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O) :
    ∃ D : FiniteChartCutSystem A,
      (∀ i : D.centers,
        Topology.IsClosedEmbedding (D.arc i).corePoint ∧
          closure (D.arc i).coreInterior = (D.arc i).closedCore ∧
          (D.arc i).leftEndpoint ≠ (D.arc i).rightEndpoint) ∧
      (∀ x : D.CutSpace,
        ∃ i : D.centers,
          ∀ y ∈ connectedComponent x,
            y.1 ∈ (D.arc i).closedCore) ∧
      Finite (ConnectedComponents D.CutSpace) ∧
      (∀ x : D.CutSpace, ∃ a b : ℝ, a < b ∧
        Nonempty (D.CutComponent x ≃ₜ (Ioo a b : Set ℝ))) ∧
      (∀ (i : D.centers) (x : D.CutSpace)
          (hx : x.1 ∈ (D.arc i).coreInterior),
        closure (D.cutComponentImage x) = D.cutComponentClosedArc i x ∧
          IsCompact (D.cutComponentClosedArc i x) ∧
          D.cutComponentLeftEndpoint i x hx ∈ D.cutPoints ∧
          D.cutComponentRightEndpoint i x hx ∈ D.cutPoints ∧
          D.cutComponentLeftEndpoint i x hx ≠
            D.cutComponentRightEndpoint i x hx) := by
  let D := A.finiteChartCutSystem hObounded
  refine ⟨D, ?_, D.exists_arc_containing_connectedComponent,
    D.finite_cutSpace_connectedComponents,
    D.exists_cutComponent_homeomorph_Ioo, ?_⟩
  · intro i
    exact ⟨(D.arc i).isClosedEmbedding_corePoint,
      (D.arc i).closure_coreInterior,
      (D.arc i).leftEndpoint_ne_rightEndpoint⟩
  · intro i x hx
    exact ⟨D.closure_cutComponentImage i x hx,
      D.isCompact_cutComponentClosedArc i x,
      D.cutComponentLeftEndpoint_mem_cutPoints i x hx,
      D.cutComponentRightEndpoint_mem_cutPoints i x hx,
      D.cutComponentLeftEndpoint_ne_rightEndpoint i x hx⟩


/-- Compiled quotient-arc contract: boundedness and the pointwise atlas derive
the finite actual arc index, pairwise-disjoint interiors, exact two-endpoint
closures, complete closure exhaustion, componentwise exhaustion, and actual
incidence at every cut point.  No arc inventory or adjacency is accepted. -/
example {O : Set PlanePoint} (A : BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O) :
    ∃ D : FiniteChartCutSystem A,
      Finite D.ArcIndex ∧
      (Pairwise fun e f : D.ArcIndex =>
        Disjoint (D.finiteArcInterior e) (D.finiteArcInterior f)) ∧
      (⋃ e : D.ArcIndex, D.finiteArcClosure e) = Set.univ ∧
      (∀ e : D.ArcIndex,
        D.finiteArcClosure e \ D.finiteArcInterior e =
          ({D.finiteArcLeftEndpoint e, D.finiteArcRightEndpoint e} :
            Set (FrontierSpace O)) ∧
        D.finiteArcLeftEndpoint e ∈ D.cutPoints ∧
        D.finiteArcRightEndpoint e ∈ D.cutPoints ∧
        D.finiteArcLeftEndpoint e ≠ D.finiteArcRightEndpoint e) ∧
      (∀ v : D.cutPoints, Nonempty (D.IncidentArc v)) ∧
      (⋃ e : D.ArcIndex,
        ({D.finiteArcLeftEndpoint e, D.finiteArcRightEndpoint e} :
          Set (FrontierSpace O))) =
        (D.cutPoints : Set (FrontierSpace O)) ∧
      (∀ p : FrontierSpace O,
        (⋃ e : D.ComponentArc p, D.finiteArcClosure e.1) =
          connectedComponent p) := by
  let D := A.finiteChartCutSystem hObounded
  refine ⟨D, D.finite_cutSpace_connectedComponents,
    fun _ _ hef => D.disjoint_finiteArcInterior hef,
    D.iUnion_finiteArcClosure_eq_univ, ?_,
    D.incidentArc_nonempty,
    D.iUnion_finiteArcEndpointPair_eq_cutPoints,
    D.iUnion_componentArcClosure_eq_connectedComponent⟩
  intro e
  exact ⟨D.finiteArcClosure_sdiff_finiteArcInterior e,
    (D.finiteArc_endpoints_mem_cutPoints e).1,
    (D.finiteArc_endpoints_mem_cutPoints e).2,
    D.finiteArcLeftEndpoint_ne_rightEndpoint e⟩
end CMVBoundaryLocalAtlas
