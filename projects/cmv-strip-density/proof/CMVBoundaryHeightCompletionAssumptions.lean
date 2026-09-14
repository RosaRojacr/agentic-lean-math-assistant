/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryHeightCompletionSpecimen

/-! Allowed-axiom and compiled-contract audit for intrinsic height completion. -/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

#print axioms
  CMVRelaxation.continuousLinearMap_ne_zero_has_coordinate
#print axioms
  SmoothGraphAtlas.HasOrientedSmoothBoundaryGraphAtlas.of_isSmoothDomain
#print axioms UnitDisk.isSmoothDomain_openUnitDisk
#print axioms
  SelectedBoundaryTopologyInput.ofSmoothDomain
#print axioms
  SelectedBoundaryTopologyInput.exists_closedBoundaryTrace_of_smoothDomain
#print axioms
  CMVRelaxation.frontier_aeOpenRepresentative_subset_frontier_open
#print axioms
  CMVRelaxation.LocalChartPreservation.HasOrientedSmoothBoundaryGraphGermOnSide.selected
#print axioms
  SmoothGraphAtlas.HasOrientedSmoothBoundaryGraphAtlas.selected
#print axioms SmoothGraphAtlas.HasOrientedSmoothBoundaryGraphAtlas
#print axioms
  SmoothGraphAtlas.HasOrientedSmoothBoundaryGraphAtlas.toBoundaryHalfSpaceAtlas
#print axioms
  SelectedBoundaryTopologyInput.ofOrientedSmoothBoundaryGraphAtlas
#print axioms
  SelectedBoundaryTopologyInput.exists_closedBoundaryTrace_of_orientedSmoothBoundaryGraphAtlas
#print axioms UnitDisk.hasOrientedSmoothBoundaryGraphAtlas
#print axioms isConnected_open_horizontal_strip_of_ordConnected_sections
#print axioms isConnected_iInter_of_antitone
#print axioms SelectedBoundaryTopologyInput.occupiedHeights_eq_Ioo
#print axioms SelectedBoundaryTopologyInput.leftEndpoint_lt_rightEndpoint
#print axioms SelectedBoundaryTopologyInput.isConnected_lowerBand
#print axioms SelectedBoundaryTopologyInput.isConnected_upperBand
#print axioms SelectedBoundaryTopologyInput.tendsto_lowerCutoff
#print axioms SelectedBoundaryTopologyInput.tendsto_upperCutoff
#print axioms SelectedBoundaryTopologyInput.iInter_lowerClosedBand
#print axioms SelectedBoundaryTopologyInput.iInter_upperClosedBand
#print axioms SelectedBoundaryTopologyInput.horizontalSection_eq_Ioo_endpoints
#print axioms SelectedBoundaryTopologyInput.leftEndpoint_mem_frontier
#print axioms SelectedBoundaryTopologyInput.rightEndpoint_mem_frontier
#print axioms
  SelectedBoundaryTopologyInput.frontierSection_subset_endpoint_exteriors
#print axioms SelectedBoundaryTopologyInput.eventually_endpoints_straddle_of_mem
#print axioms SelectedBoundaryTopologyInput.upperSemicontinuousAt_leftEndpoint
#print axioms SelectedBoundaryTopologyInput.lowerSemicontinuousAt_rightEndpoint
#print axioms SelectedBoundaryTopologyInput.exists_leftEndpoint_limit_nhdsLT
#print axioms SelectedBoundaryTopologyInput.exists_leftEndpoint_limit_nhdsGT
#print axioms SelectedBoundaryTopologyInput.exists_rightEndpoint_limit_nhdsLT
#print axioms SelectedBoundaryTopologyInput.exists_rightEndpoint_limit_nhdsGT
#print axioms
  SelectedBoundaryTopologyInput.Icc_leftLim_leftEndpoint_subset_frontierSection
#print axioms
  SelectedBoundaryTopologyInput.Icc_rightEndpoint_leftLim_subset_frontierSection
#print axioms
  SelectedBoundaryTopologyInput.exists_leftEndpoint_limit_nhdsGT_lowerHeight
#print axioms
  SelectedBoundaryTopologyInput.exists_rightEndpoint_limit_nhdsGT_lowerHeight
#print axioms
  SelectedBoundaryTopologyInput.exists_leftEndpoint_limit_nhdsLT_upperHeight
#print axioms
  SelectedBoundaryTopologyInput.exists_rightEndpoint_limit_nhdsLT_upperHeight
#print axioms
  SelectedBoundaryTopologyInput.frontierSection_eq_endpointLimitIntervals
#print axioms
  SelectedBoundaryTopologyInput.lower_frontierSection_eq_Icc_endpointLimits
#print axioms
  SelectedBoundaryTopologyInput.upper_frontierSection_eq_Icc_endpointLimits
#print axioms SelectedBoundaryTopologyInput.leftLim_leftEndpoint_le
#print axioms SelectedBoundaryTopologyInput.rightLim_leftEndpoint_le
#print axioms SelectedBoundaryTopologyInput.rightEndpoint_le_leftLim
#print axioms SelectedBoundaryTopologyInput.rightEndpoint_le_rightLim
#print axioms SelectedBoundaryTopologyInput.max_leftEndpoint_limits_eq
#print axioms SelectedBoundaryTopologyInput.min_rightEndpoint_limits_eq
#print axioms
  SelectedBoundaryTopologyInput.frontierSection_eq_orientedEndpointSegments
#print axioms SelectedBoundaryTopologyInput.leftCompletedChain_subset_frontier
#print axioms SelectedBoundaryTopologyInput.rightCompletedChain_subset_frontier
#print axioms SelectedBoundaryTopologyInput.frontier_eq_union_completedChains
#print axioms SelectedBoundaryTopologyInput.completedChains_inter_eq
#print axioms SelectedBoundaryTopologyInput.lowerSplitPoint_ne_upperSplitPoint
#print axioms SelectedBoundaryTopologyInput.isClosed_leftCompletedChain
#print axioms SelectedBoundaryTopologyInput.isClosed_rightCompletedChain
#print axioms SelectedBoundaryTopologyInput.isCompact_leftCompletedChain
#print axioms SelectedBoundaryTopologyInput.isCompact_rightCompletedChain
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainLinearOrder
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainLinearOrder
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_mem_lower_iff
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_mem_upper_iff
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_mem_interior_iff
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_mem_lower_iff
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_mem_upper_iff
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_mem_interior_iff
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_exists_between_of_snd_lt
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_exists_between_of_same_snd
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_exists_between_of_snd_lt
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_exists_between_of_same_snd
#print axioms SelectedBoundaryTopologyInput.leftCompletedChain_denselyOrdered
#print axioms SelectedBoundaryTopologyInput.rightCompletedChain_denselyOrdered
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainBottom_le
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainBottom_le
#print axioms SelectedBoundaryTopologyInput.leftCompletedChain_le_top
#print axioms SelectedBoundaryTopologyInput.rightCompletedChain_le_top
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainOrderBot
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainOrderBot
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainOrderTop
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainOrderTop
#print axioms SelectedBoundaryTopologyInput.leftCompletedChain_le_iff
#print axioms SelectedBoundaryTopologyInput.rightCompletedChain_le_iff
#print axioms SelectedBoundaryTopologyInput.leftCompletedChain_separableSpace
#print axioms SelectedBoundaryTopologyInput.rightCompletedChain_separableSpace
#print axioms
  SelectedBoundaryTopologyInput.tendsto_rightLim_nhdsLT_of_tendsto
#print axioms
  SelectedBoundaryTopologyInput.tendsto_leftLim_nhdsGT_of_tendsto
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_limit_from_below
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_limit_from_above
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_limit_from_below
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_limit_from_above
#print axioms SelectedBoundaryTopologyInput.isClosed_leftCompletedChain_Iic
#print axioms SelectedBoundaryTopologyInput.isClosed_leftCompletedChain_Ici
#print axioms SelectedBoundaryTopologyInput.isClosed_rightCompletedChain_Iic
#print axioms SelectedBoundaryTopologyInput.isClosed_rightCompletedChain_Ici
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_topology_eq_orderTopology
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_topology_eq_orderTopology
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChainPlanarOrderTopology
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChainPlanarOrderTopology
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChainCompleteLinearOrder
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChainCompleteLinearOrder
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainNontrivial
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainNontrivial
#print axioms
  SeparableLinearContinuum.dedekindFactorEmbedding_surjective_of_denseRange
#print axioms SeparableLinearContinuum.dedekindOrderIsoOfDenseRange
#print axioms SeparableLinearContinuum.exists_orderIso_unitInterval
#print axioms SeparableLinearContinuum.orderIsoUnitInterval
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChainOrderIsoUnitInterval
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChainOrderIsoUnitInterval
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainHomeomorph
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainHomeomorph
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChainHomeomorph_zero
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChainHomeomorph_one
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChainHomeomorph_zero
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChainHomeomorph_one
#print axioms
  SelectedBoundaryTopologyInput.range_leftCompletedChainHomeomorph
#print axioms
  SelectedBoundaryTopologyInput.range_rightCompletedChainHomeomorph
#print axioms SelectedBoundaryTopologyInput.leftCompletedChainPath
#print axioms SelectedBoundaryTopologyInput.rightCompletedChainReversedPath
#print axioms SelectedBoundaryTopologyInput.completedBoundaryLoopOn
#print axioms SelectedBoundaryTopologyInput.completedBoundaryLoop
#print axioms SelectedBoundaryTopologyInput.continuous_completedBoundaryLoop
#print axioms SelectedBoundaryTopologyInput.completedBoundaryLoop_closed
#print axioms SelectedBoundaryTopologyInput.range_completedBoundaryLoopOn
#print axioms SelectedBoundaryTopologyInput.image_completedBoundaryLoop_Icc
#print axioms SelectedBoundaryTopologyInput.completedBoundaryLoop_injOn_Ico
#print axioms
  SelectedBoundaryTopologyInput.isConnected_frontier_aeOpenRepresentative
#print axioms SelectedBoundaryTopologyInput.closedBoundaryTrace
#print axioms SelectedBoundaryTopologyInput.continuous_closedBoundaryTrace
#print axioms
  SelectedBoundaryTopologyInput.closedBoundaryTrace_start_lt_finish
#print axioms SelectedBoundaryTopologyInput.closedBoundaryTrace_injOn_Ico
#print axioms
  SelectedBoundaryTopologyInput.selectedRepresentative_isMinimizer_of_source
#print axioms
  SelectedBoundaryTopologyInput.source_isMinimizer_of_selectedRepresentative
#print axioms
  SelectedBoundaryTopologyInput.toRegularFigureThreeBoundaryConfiguration
#print axioms SelectedBoundaryTopologyInput.figureThree_sourceRadius_eq_one
#print axioms SelectedBoundaryTopologyInput.leftCompletedChain_lt_of_snd_lt
#print axioms SelectedBoundaryTopologyInput.rightCompletedChain_lt_of_snd_lt
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_lt_of_same_snd_of_forward
#print axioms
  SelectedBoundaryTopologyInput.leftCompletedChain_lt_of_same_snd_of_backward
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_lt_of_same_snd_of_forward
#print axioms
  SelectedBoundaryTopologyInput.rightCompletedChain_lt_of_same_snd_of_backward
#print axioms SelectedBoundaryTopologyInput.exists_lowerHeightPoint
#print axioms SelectedBoundaryTopologyInput.exists_upperHeightPoint
#print axioms SelectedBoundaryTopologyInput.lower_frontierSection_nonempty_compact
#print axioms SelectedBoundaryTopologyInput.upper_frontierSection_nonempty_compact
#print axioms SelectedBoundaryTopologyInput.frontier_snd_mem_Icc
#print axioms SelectedBoundaryTopologyInput.isConnected_lower_frontierSection
#print axioms SelectedBoundaryTopologyInput.isConnected_upper_frontierSection
#print axioms SelectedBoundaryTopologyInput.lower_frontierSection_eq_Icc
#print axioms SelectedBoundaryTopologyInput.upper_frontierSection_eq_Icc

#print axioms UnitDisk.selectedBoundaryAtlas
#print axioms UnitDisk.selectedTopologyInput
#print axioms UnitDisk.occupiedHeights_eq
#print axioms UnitDisk.zero_endpoints_mem_frontier
#print axioms UnitDisk.endpointLimits_zero
#print axioms UnitDisk.extreme_frontierSections_eq_endpointLimits
#print axioms UnitDisk.frontier_eq_union_completedChains
#print axioms UnitDisk.completedChains_compact
#print axioms UnitDisk.completedChains_inter_eq_splitPoints
#print axioms UnitDisk.completedChain_splitPoints_distinct
#print axioms UnitDisk.completedChain_intrinsic_order_data
#print axioms UnitDisk.completedChain_order_extrema
#print axioms UnitDisk.completedChain_topology_agreement
#print axioms UnitDisk.leftCompletedChainCompleteOrder
#print axioms UnitDisk.rightCompletedChainCompleteOrder
#print axioms UnitDisk.leftCompletedChainParameterization
#print axioms UnitDisk.rightCompletedChainParameterization
#print axioms UnitDisk.completedChainParameterizations_endpoints
#print axioms UnitDisk.completedChainParameterizations_ranges
#print axioms UnitDisk.simpleBoundaryLoop
#print axioms UnitDisk.continuous_simpleBoundaryLoop
#print axioms UnitDisk.simpleBoundaryLoop_closed
#print axioms UnitDisk.simpleBoundaryLoop_injOn_Ico
#print axioms UnitDisk.simpleBoundaryLoop_image
#print axioms UnitDisk.frontier_connected_from_simpleBoundaryLoop

#print axioms StepPolygon.boundaryAtlas
#print axioms StepPolygon.selectedBoundaryAtlas
#print axioms StepPolygon.selectedTopologyInput
#print axioms StepPolygon.occupiedHeights_eq
#print axioms StepPolygon.tendsto_rightEndpoint_nhdsLT_one
#print axioms StepPolygon.tendsto_rightEndpoint_nhdsGT_one
#print axioms StepPolygon.rightEndpoint_leftLim_one
#print axioms StepPolygon.generic_right_jump_segment_one
#print axioms StepPolygon.frontierSection_one
#print axioms StepPolygon.lower_frontierSection
#print axioms StepPolygon.upper_frontierSection
#print axioms StepPolygon.rightEndpoint_rightLim_one
#print axioms StepPolygon.shelf_subset_rightCompletedChain
#print axioms StepPolygon.shelf_jump_order
#print axioms StepPolygon.frontier_eq_union_completedChains
#print axioms StepPolygon.completedChains_compact
#print axioms StepPolygon.completedChains_inter_eq_splitPoints
#print axioms StepPolygon.completedChain_splitPoints_distinct
#print axioms StepPolygon.completedChain_intrinsic_order_data
#print axioms StepPolygon.completedChain_order_extrema
#print axioms StepPolygon.completedChain_topology_agreement
#print axioms StepPolygon.leftCompletedChainCompleteOrder
#print axioms StepPolygon.rightCompletedChainCompleteOrder
#print axioms StepPolygon.leftCompletedChainParameterization
#print axioms StepPolygon.rightCompletedChainParameterization
#print axioms StepPolygon.completedChainParameterizations_endpoints
#print axioms StepPolygon.completedChainParameterizations_ranges
#print axioms StepPolygon.simpleBoundaryLoop
#print axioms StepPolygon.continuous_simpleBoundaryLoop
#print axioms StepPolygon.simpleBoundaryLoop_closed
#print axioms StepPolygon.simpleBoundaryLoop_injOn_Ico
#print axioms StepPolygon.simpleBoundaryLoop_image
#print axioms StepPolygon.frontier_connected_from_simpleBoundaryLoop
#print axioms UnboundedNullDisk.volume_unboundedNullLine
#print axioms UnboundedNullDisk.unboundedNullLine_not_bounded
#print axioms UnboundedNullDisk.sourceCarrier_ae_openUnitDisk
#print axioms UnboundedNullDisk.sourceCarrier_ne_openUnitDisk
#print axioms UnboundedNullDisk.sourceCarrier_not_bounded
#print axioms
  UnboundedNullDisk.hasAEIntervalHorizontalSections_sourceCarrier
#print axioms UnboundedNullDisk.aeOpenRepresentative_sourceCarrier
#print axioms UnboundedNullDisk.selectedTopologyInput
#print axioms UnboundedNullDisk.selectedTrace
#print axioms UnboundedNullDisk.continuous_selectedTrace
#print axioms UnboundedNullDisk.selectedTrace_start_lt_finish
#print axioms UnboundedNullDisk.selectedTrace_injOn_Ico
#print axioms
  UnboundedNullDisk.selectedRepresentative_isMinimizer_of_source
#print axioms UnboundedNullDisk.selectedTrace_unboundedSource_compiledContract

/-- Compiled generic contract: the unchanged source-topology input alone
produces intrinsic height bounds, exact nonempty section endpoints, actual
frontier incidence, local endpoint semicontinuity, and attained extreme slices. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    D.occupiedHeights = Ioo D.lowerHeight D.upperHeight ∧
      D.lowerHeight < D.upperHeight ∧
      (∀ y, y ∈ D.occupiedHeights →
        D.leftEndpoint y < D.rightEndpoint y ∧
        (D.leftEndpoint y, y) ∈
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        (D.rightEndpoint y, y) ∈
          frontier (CMVRelaxation.aeOpenRepresentative E)) ∧
      (D.frontierSection D.lowerHeight).Nonempty ∧
      (D.frontierSection D.upperHeight).Nonempty := by
  refine ⟨D.occupiedHeights_eq_Ioo, D.lowerHeight_lt_upperHeight, ?_,
    D.lower_frontierSection_nonempty_compact.1,
    D.upper_frontierSection_nonempty_compact.1⟩
  intro y hy
  exact ⟨D.leftEndpoint_lt_rightEndpoint hy,
    D.leftEndpoint_mem_frontier hy,
    D.rightEndpoint_mem_frontier hy⟩

/-- Compiled regulation contract: at each occupied height both intrinsic
section endpoints have finite limits from both sides. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    ∀ y, y ∈ D.occupiedHeights →
      (∃ L, Tendsto D.leftEndpoint (𝓝[<] y) (𝓝 L)) ∧
      (∃ L, Tendsto D.leftEndpoint (𝓝[>] y) (𝓝 L)) ∧
      (∃ R, Tendsto D.rightEndpoint (𝓝[<] y) (𝓝 R)) ∧
      (∃ R, Tendsto D.rightEndpoint (𝓝[>] y) (𝓝 R)) := by
  intro y hy
  exact ⟨D.exists_leftEndpoint_limit_nhdsLT hy,
    D.exists_leftEndpoint_limit_nhdsGT hy,
    D.exists_rightEndpoint_limit_nhdsLT hy,
    D.exists_rightEndpoint_limit_nhdsGT hy⟩

/-- Compiled endpoint-completion contract: inward limits exist at both extreme
heights, and all interior and extreme frontier slices have exact endpoint-limit
formulas. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    (∃ L, Tendsto D.leftEndpoint (𝓝[>] D.lowerHeight) (𝓝 L)) ∧
    (∃ R, Tendsto D.rightEndpoint (𝓝[>] D.lowerHeight) (𝓝 R)) ∧
    (∃ L, Tendsto D.leftEndpoint (𝓝[<] D.upperHeight) (𝓝 L)) ∧
    (∃ R, Tendsto D.rightEndpoint (𝓝[<] D.upperHeight) (𝓝 R)) ∧
    D.frontierSection D.lowerHeight =
      Icc (Function.rightLim D.leftEndpoint D.lowerHeight)
        (Function.rightLim D.rightEndpoint D.lowerHeight) ∧
    D.frontierSection D.upperHeight =
      Icc (Function.leftLim D.leftEndpoint D.upperHeight)
        (Function.leftLim D.rightEndpoint D.upperHeight) ∧
    (∀ y, y ∈ D.occupiedHeights →
      D.frontierSection y =
        Icc (min (Function.leftLim D.leftEndpoint y)
            (Function.rightLim D.leftEndpoint y))
          (D.leftEndpoint y) ∪
        Icc (D.rightEndpoint y)
          (max (Function.leftLim D.rightEndpoint y)
            (Function.rightLim D.rightEndpoint y))) := by
  exact ⟨D.exists_leftEndpoint_limit_nhdsGT_lowerHeight,
    D.exists_rightEndpoint_limit_nhdsGT_lowerHeight,
    D.exists_leftEndpoint_limit_nhdsLT_upperHeight,
    D.exists_rightEndpoint_limit_nhdsLT_upperHeight,
    D.lower_frontierSection_eq_Icc_endpointLimits,
    D.upper_frontierSection_eq_Icc_endpointLimits,
    fun _y hy => D.frontierSection_eq_endpointLimitIntervals hy⟩

/-- Compiled no-slit and chain-decomposition contract: every occupied endpoint
segment is oriented from its genuine lower-side limit to its upper-side limit;
the two resulting compact frontier subsets exhaust the frontier and meet only
at two distinct intrinsic extreme split points. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    (∀ y, y ∈ D.occupiedHeights →
      max (Function.leftLim D.leftEndpoint y)
          (Function.rightLim D.leftEndpoint y) = D.leftEndpoint y ∧
      min (Function.leftLim D.rightEndpoint y)
          (Function.rightLim D.rightEndpoint y) = D.rightEndpoint y ∧
      D.frontierSection y =
        uIcc (Function.leftLim D.leftEndpoint y)
            (Function.rightLim D.leftEndpoint y) ∪
        uIcc (Function.leftLim D.rightEndpoint y)
            (Function.rightLim D.rightEndpoint y)) ∧
    frontier (CMVRelaxation.aeOpenRepresentative E) =
      D.leftCompletedChain ∪ D.rightCompletedChain ∧
    D.leftCompletedChain ∩ D.rightCompletedChain =
      {D.lowerSplitPoint, D.upperSplitPoint} ∧
    D.lowerSplitPoint ≠ D.upperSplitPoint ∧
    IsCompact D.leftCompletedChain ∧ IsCompact D.rightCompletedChain := by
  refine ⟨?_, D.frontier_eq_union_completedChains,
    D.completedChains_inter_eq, D.lowerSplitPoint_ne_upperSplitPoint,
    D.isCompact_leftCompletedChain, D.isCompact_rightCompletedChain⟩
  intro y hy
  exact ⟨D.max_leftEndpoint_limits_eq hy,
    D.min_rightEndpoint_limits_eq hy,
    D.frontierSection_eq_orientedEndpointSegments hy⟩

/-- Both completed chain subtypes carry the explicit intrinsic traversal
orders audited above. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    LinearOrder D.leftCompletedChain :=
  D.leftCompletedChainLinearOrder

example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    LinearOrder D.rightCompletedChain :=
  D.rightCompletedChainLinearOrder

/-- Compiled intrinsic-order contract: each compact chain has no adjacent
points in the height-first traversal order and retains its separable planar
subspace topology. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    @DenselyOrdered D.leftCompletedChain
        D.leftCompletedChainLinearOrder.toLT ∧
      @DenselyOrdered D.rightCompletedChain
        D.rightCompletedChainLinearOrder.toLT ∧
      TopologicalSpace.SeparableSpace D.leftCompletedChain ∧
      TopologicalSpace.SeparableSpace D.rightCompletedChain := by
  exact ⟨D.leftCompletedChain_denselyOrdered,
    D.rightCompletedChain_denselyOrdered,
    D.leftCompletedChain_separableSpace,
    D.rightCompletedChain_separableSpace⟩

example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    @OrderBot D.leftCompletedChain
      D.leftCompletedChainLinearOrder.toLE :=
  D.leftCompletedChainOrderBot

example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    @OrderTop D.leftCompletedChain
      D.leftCompletedChainLinearOrder.toLE :=
  D.leftCompletedChainOrderTop

example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    @OrderBot D.rightCompletedChain
      D.rightCompletedChainLinearOrder.toLE :=
  D.rightCompletedChainOrderBot

example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    @OrderTop D.rightCompletedChain
      D.rightCompletedChainLinearOrder.toLE :=
  D.rightCompletedChainOrderTop

/-- The planar subtype topologies are exactly the intrinsic order topologies. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    (inferInstance : TopologicalSpace D.leftCompletedChain) =
        @Preorder.topology D.leftCompletedChain
          D.leftCompletedChainLinearOrder.toPreorder ∧
      (inferInstance : TopologicalSpace D.rightCompletedChain) =
        @Preorder.topology D.rightCompletedChain
          D.rightCompletedChainLinearOrder.toPreorder :=
  ⟨D.leftCompletedChain_topology_eq_orderTopology,
    D.rightCompletedChain_topology_eq_orderTopology⟩

/-- Both intrinsic traversal orders have all suprema and infima. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    CompleteLinearOrder D.leftCompletedChain :=
  D.leftCompletedChainCompleteLinearOrder

example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    CompleteLinearOrder D.rightCompletedChain :=
  D.rightCompletedChainCompleteLinearOrder

/-- Compiled closed-interval parameterization contract: the unchanged topology
input alone yields endpoint-preserving homeomorphisms onto both actual planar
completed chains. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    ∃ L : Set.Icc (0 : ℝ) 1 ≃ₜ D.leftCompletedChain,
      ∃ R : Set.Icc (0 : ℝ) 1 ≃ₜ D.rightCompletedChain,
        ((L ⟨0, by norm_num⟩ : D.leftCompletedChain) : PlanePoint) =
            D.lowerSplitPoint ∧
        ((L ⟨1, by norm_num⟩ : D.leftCompletedChain) : PlanePoint) =
            D.upperSplitPoint ∧
        ((R ⟨0, by norm_num⟩ : D.rightCompletedChain) : PlanePoint) =
            D.lowerSplitPoint ∧
        ((R ⟨1, by norm_num⟩ : D.rightCompletedChain) : PlanePoint) =
            D.upperSplitPoint ∧
        range (fun t => ((L t : D.leftCompletedChain) : PlanePoint)) =
            D.leftCompletedChain ∧
        range (fun t => ((R t : D.rightCompletedChain) : PlanePoint)) =
            D.rightCompletedChain := by
  exact ⟨D.leftCompletedChainHomeomorph,
    D.rightCompletedChainHomeomorph,
    D.leftCompletedChainHomeomorph_zero,
    D.leftCompletedChainHomeomorph_one,
    D.rightCompletedChainHomeomorph_zero,
    D.rightCompletedChainHomeomorph_one,
    D.range_leftCompletedChainHomeomorph,
    D.range_rightCompletedChainHomeomorph⟩

/-- Compiled simple-loop contract: the unchanged topology input yields one
positive-length closed parameter interval whose map is continuous, injective
before its terminal endpoint, and exactly exhausts the actual frontier. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    (0 : ℝ) < 2 ∧
      ContinuousOn D.completedBoundaryLoop (Icc (0 : ℝ) 2) ∧
      D.completedBoundaryLoop 0 = D.completedBoundaryLoop 2 ∧
      Set.InjOn D.completedBoundaryLoop (Ico (0 : ℝ) 2) ∧
      D.completedBoundaryLoop '' Icc (0 : ℝ) 2 =
        frontier (CMVRelaxation.aeOpenRepresentative E) ∧
      IsConnected (frontier (CMVRelaxation.aeOpenRepresentative E)) := by
  exact ⟨by norm_num, D.continuous_completedBoundaryLoop.continuousOn,
    D.completedBoundaryLoop_closed, D.completedBoundaryLoop_injOn_Ico,
    D.image_completedBoundaryLoop_Icc,
    D.isConnected_frontier_aeOpenRepresentative⟩

/-- Compiled unchanged-adapter contract: the simple loop inhabits exactly the
existing weak source trace on the selected representative; its stronger
topology is exported separately, and source minimality crosses the selection
only through planar-AE invariance of the relaxed semantics. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U)
    {lam : ℝ} (hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative E),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Ico boundary.start boundary.finish) ∧
        boundary.trace '' Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative E) := by
  exact ⟨D.closedBoundaryTrace, D.continuous_closedBoundaryTrace,
    D.closedBoundaryTrace_start_lt_finish, D.closedBoundaryTrace_injOn_Ico,
    D.closedBoundaryTrace.complete_image,
    D.selectedRepresentative_isMinimizer_of_source hlam hsource⟩

/-- Fully expanded dependency contract for the selected-representative loop and
AE minimizer transport.  The topology input is reconstructed here from exactly
one bounded open connected representative, source AE agreement, source interval
sections, and one pointwise half-space chart at every selected frontier point.
No finite chart traversal, endpoint regularity, connected frontier, or supplied
boundary curve appears among the premises. -/
example {E U : Set PlanePoint} {lam : ℝ}
    (representative_nonempty : U.Nonempty)
    (representative_open : IsOpen U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    (localCharts :
      ∀ p : {q : PlanePoint //
        q ∈ frontier (CMVRelaxation.aeOpenRepresentative E)},
        PointwiseHalfSpaceChart
          (CMVRelaxation.aeOpenRepresentative E) p)
    (hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative E),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Ico boundary.start boundary.finish) ∧
        boundary.trace '' Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        IsConnected
          (frontier (CMVRelaxation.aeOpenRepresentative E)) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative E) := by
  let D : SelectedBoundaryTopologyInput E U :=
    { representative_nonempty := representative_nonempty
      representative_open := representative_open
      representative_bounded := representative_bounded
      representative_connected := representative_connected
      carrier_ae := carrier_ae
      interval_sections := interval_sections
      local_atlas := ⟨localCharts⟩ }
  exact ⟨D.closedBoundaryTrace, D.continuous_closedBoundaryTrace,
    D.closedBoundaryTrace_start_lt_finish, D.closedBoundaryTrace_injOn_Ico,
    D.closedBoundaryTrace.complete_image,
    D.isConnected_frontier_aeOpenRepresentative,
    D.selectedRepresentative_isMinimizer_of_source hlam hsource⟩

/-- Source-regularity dependency contract: pointwise oriented smooth graph germs
on the supplied open representative now suffice in place of selected-set germs
or caller-supplied ambient half-space charts.  The complete simple loop and
selected-frontier connectedness remain derived, while representative, section,
and source-minimality premises stay explicit. -/
example {E U : Set PlanePoint} {lam : ℝ}
    (representative_nonempty : U.Nonempty)
    (representative_open : IsOpen U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    (localRegularity :
      SmoothGraphAtlas.HasOrientedSmoothBoundaryGraphAtlas U)
    (hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative E),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Ico boundary.start boundary.finish) ∧
        boundary.trace '' Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        IsConnected
          (frontier (CMVRelaxation.aeOpenRepresentative E)) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative E) :=
  SelectedBoundaryTopologyInput.exists_closedBoundaryTrace_of_orientedSmoothBoundaryGraphAtlas
      representative_nonempty representative_open representative_bounded
      representative_connected carrier_ae interval_sections localRegularity
      hlam hsource

/-- Literal smooth-domain dependency contract: the source relaxation's own
regular-boundary notion supplies both representative openness and every local
oriented graph germ.  No atlas, chart, frontier connectedness, or loop is an
input. -/
example {E U : Set PlanePoint} {lam : ℝ}
    (representative_nonempty : U.Nonempty)
    (representative_smooth : CMVRelaxation.IsSmoothDomain U)
    (representative_bounded : Bornology.IsBounded U)
    (representative_connected : IsConnected U)
    (carrier_ae : E =ᵐ[volume] U)
    (interval_sections : CMVRelaxation.HasAEIntervalHorizontalSections E)
    (hlam : 1 < lam)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer E) :
    ∃ boundary :
        CMVFigureThree.SourceBoundaryExtraction.ClosedBoundaryTrace
          (CMVRelaxation.aeOpenRepresentative E),
      Continuous boundary.trace ∧
        boundary.start < boundary.finish ∧
        Set.InjOn boundary.trace (Ico boundary.start boundary.finish) ∧
        boundary.trace '' Icc boundary.start boundary.finish =
          frontier (CMVRelaxation.aeOpenRepresentative E) ∧
        IsConnected
          (frontier (CMVRelaxation.aeOpenRepresentative E)) ∧
        (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
          (CMVRelaxation.aeOpenRepresentative E) :=
  SelectedBoundaryTopologyInput.exists_closedBoundaryTrace_of_smoothDomain
    representative_nonempty representative_smooth representative_bounded
    representative_connected carrier_ae interval_sections hlam hsource

/-- Compiled completion contract: shrinking connected truncations recover the
two complete extreme frontier slices, which are intrinsic compact intervals. -/
example {E U : Set PlanePoint} (D : SelectedBoundaryTopologyInput E U) :
    (⋂ n, D.lowerClosedBand n) =
        frontier (CMVRelaxation.aeOpenRepresentative E) ∩
          Prod.snd ⁻¹' ({D.lowerHeight} : Set ℝ) ∧
      (⋂ n, D.upperClosedBand n) =
        frontier (CMVRelaxation.aeOpenRepresentative E) ∩
          Prod.snd ⁻¹' ({D.upperHeight} : Set ℝ) ∧
      D.frontierSection D.lowerHeight =
        Icc (sInf (D.frontierSection D.lowerHeight))
          (sSup (D.frontierSection D.lowerHeight)) ∧
      D.frontierSection D.upperHeight =
        Icc (sInf (D.frontierSection D.upperHeight))
          (sSup (D.frontierSection D.upperHeight)) :=
  ⟨D.iInter_lowerClosedBand, D.iInter_upperClosedBand,
    D.lower_frontierSection_eq_Icc, D.upper_frontierSection_eq_Icc⟩

/-- Compiled shelf contract: the generic input retains the discontinuous shelf,
its distinct genuine one-sided limits, and both extreme compact intervals. -/
example :
    Tendsto StepPolygon.selectedTopologyInput.rightEndpoint
        (𝓝[<] (1 : ℝ)) (𝓝 2) ∧
      Tendsto StepPolygon.selectedTopologyInput.rightEndpoint
        (𝓝[>] (1 : ℝ)) (𝓝 1) ∧
      StepPolygon.selectedTopologyInput.frontierSection 1 =
        ({0} : Set ℝ) ∪ Icc 1 2 ∧
      StepPolygon.selectedTopologyInput.frontierSection
          StepPolygon.selectedTopologyInput.lowerHeight = Icc 0 2 ∧
      StepPolygon.selectedTopologyInput.frontierSection
          StepPolygon.selectedTopologyInput.upperHeight = Icc 0 1 :=
  ⟨StepPolygon.tendsto_rightEndpoint_nhdsLT_one,
    StepPolygon.tendsto_rightEndpoint_nhdsGT_one,
    StepPolygon.frontierSection_one,
    StepPolygon.lower_frontierSection,
    StepPolygon.upper_frontierSection⟩

end CMVBoundaryLocalAtlas
