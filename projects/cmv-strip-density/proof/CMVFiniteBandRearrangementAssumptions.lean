import CMVFiniteBandRearrangementExample
import CMVFiniteBandFrontier
import CMVFiniteBandCostAssembly
import CMVFiniteBandCostComparison
import CMVFiniteBandEqualityRigidityExample

open Set Filter MeasureTheory

namespace CMVRelaxation.FiniteBandRearrangement

#print axioms Region.mem_componentCarrier_iff
#print axioms Region.horizontalSection_componentCarrier
#print axioms Region.horizontalSection_bandCarrier
#print axioms Region.horizontalSection_carrier
#print axioms Region.horizontalSection_centeredBandCarrier
#print axioms Region.horizontalSection_centeredCarrier
#print axioms Region.mem_interior_componentCarrier_of_strict
#print axioms Region.frontier_componentCarrier_subset_componentFrontierTrace
#print axioms Region.componentFrontierTrace_subset_frontier_componentCarrier
#print axioms Region.frontier_componentCarrier
#print axioms Region.frontier_bandCarrier_subset_bandComponentFrontierTrace
#print axioms Region.frontier_carrier_subset_rawComponentFrontierTrace
#print axioms Region.frontier_fiber_subset_fiberEndpoints
#print axioms Region.symmDiff_subset_seamBoundaryFiber
#print axioms Region.seamBoundaryFiber_subset_symmDiff_union_endpoints
#print axioms Region.seamSymmDiff_subset_seamBoundaryTrace
#print axioms Region.seamBoundaryTrace_subset_symmDiff_union_endpoints
#print axioms Region.fiberEndpoints_finite
#print axioms Region.seamEndpointSet_finite
#print axioms Region.hausdorffMeasure_seamEndpointSet
#print axioms Region.componentInterval_eq_singleton_of_eq
#print axioms Region.isClosed_centeredBandCarrier
#print axioms Region.isClosed_centeredCarrier
#print axioms Region.isClosed_componentCarrier
#print axioms Region.isClosed_bandCarrier
#print axioms Region.isClosed_carrier

#print axioms Region.band_eq_of_height_mem_Ioo_mem_Icc
#print axioms Region.horizontalSection_carrier_of_mem_Ioo
#print axioms Region.leftGraphTrace_subset_frontier_carrier
#print axioms Region.rightGraphTrace_subset_frontier_carrier
#print axioms Region.lowerOuterTrace_subset_frontier_carrier
#print axioms Region.upperOuterTrace_subset_frontier_carrier
#print axioms Region.seamSymmDiff_subset_frontier_carrier
#print axioms Region.seamEndpointSet_subset_graphTrace
#print axioms Region.filledSeamCoreTrace_subset_interior_carrier
#print axioms Region.seamFrontierTrace_eq_symmDiff_union_endpointSet
#print axioms Region.frontier_carrier
#print axioms Region.totalWidth_pos
#print axioms Region.centeredLeftGraphTrace_subset_frontier_centeredCarrier
#print axioms Region.centeredRightGraphTrace_subset_frontier_centeredCarrier
#print axioms Region.centeredLowerOuterTrace_subset_frontier_centeredCarrier
#print axioms Region.centeredUpperOuterTrace_subset_frontier_centeredCarrier
#print axioms Region.centeredSeamSymmDiff_subset_frontier_centeredCarrier
#print axioms Region.centeredSeamEndpointSet_subset_centeredGraphTrace
#print axioms Region.mem_interior_centeredCarrier_of_common_strict
#print axioms Region.centeredSeamFrontierTrace_eq_symmDiff_union_endpointSet
#print axioms Region.centeredSeamEndpointSet_finite
#print axioms Region.hausdorffMeasure_centeredSeamEndpointSet
#print axioms Region.frontier_centeredCarrier

#print axioms hausdorffMeasure_verticalGraph_Icc_eq_setLIntegral
#print axioms hausdorffMeasure_verticalGraph_image_eq_setLIntegral
#print axioms weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals
#print axioms weightedTraceCost_horizontal_image
#print axioms Region.weightedTraceCost_leftGraphTrace
#print axioms Region.weightedTraceCost_rightGraphTrace
#print axioms Region.totalWidth_speed_integrable
#print axioms Region.continuous_totalWidth
#print axioms Region.totalWidth_contDiffOn
#print axioms Region.weightedTraceCost_centeredLeftGraphTrace
#print axioms Region.weightedTraceCost_centeredRightGraphTrace
#print axioms Region.integrableOn_carrier
#print axioms Region.integrableOn_centeredCarrier
#print axioms volume_horizontalSection_carrier_eq_centeredCarrier
#print axioms weightedArea_carrier_eq_centeredCarrier
#print axioms hausdorffMeasure_circularPoleGraph
#print axioms weightedTraceCost_circularPoleGraph
#print axioms neg_deriv_circularPoleGraph_tendsto_atTop

#print axioms weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite
#print axioms weightedTraceCost_union_eq_add_of_inter_finite
#print axioms Region.graphTrace_eq_iUnion_indexedGraphTrace
#print axioms Region.indexedGraphValue_injective
#print axioms Region.indexedGraphTrace_inter_finite
#print axioms Region.weightedTraceCost_indexedGraphTrace
#print axioms Region.weightedTraceCost_graphTrace
#print axioms Region.pairwise_aedisjoint_componentIntervals
#print axioms Region.volume_fiber_of_mem_Icc
#print axioms Region.weightedTraceCost_lowerOuterTrace
#print axioms Region.weightedTraceCost_upperOuterTrace
#print axioms Region.weightedTraceCost_seamSymmDiff
#print axioms Region.completeFrontierTrace_eq_graph_union_horizontal
#print axioms Region.graphTrace_inter_horizontalFrontierTrace_finite
#print axioms Region.weightedTraceCost_horizontalFrontierTrace
#print axioms Region.weightedTraceCost_completeFrontierTrace
#print axioms Region.centeredGraphTrace_eq_iUnion_indexedCenteredGraphTrace
#print axioms Region.indexedCenteredGraphTrace_inter_finite
#print axioms Region.weightedTraceCost_indexedCenteredGraphTrace
#print axioms Region.weightedTraceCost_centeredGraphTrace
#print axioms Region.completeCenteredFrontierTrace_eq_graph_union_horizontal
#print axioms
  Region.centeredGraphTrace_inter_centeredHorizontalFrontierTrace_finite
#print axioms Region.weightedTraceCost_centeredHorizontalFrontierTrace
#print axioms Region.weightedTraceCost_completeCenteredFrontierTrace
#print axioms Region.indexedGraphSpeedCost_ne_top
#print axioms Region.indexedCenteredGraphSpeedCost_ne_top
#print axioms Region.weightedTraceCost_completeFrontierTrace_ne_top
#print axioms Region.weightedTraceCost_completeCenteredFrontierTrace_ne_top
#print axioms Region.weightedTraceCost_frontier_carrier
#print axioms Region.weightedTraceCost_frontier_centeredCarrier
#print axioms Region.weightedTraceCost_frontier_carrier_ne_top
#print axioms Region.weightedTraceCost_frontier_centeredCarrier_ne_top
#print axioms twoComponentNonconstantCenter_graphSpeed_strict
#print axioms translatedCenteredSingleComponent_graphSpeed_eq
#print axioms Region.centeredBandGraphSpeed_le_originalBandGraphSpeed
#print axioms Region.centeredBandGraphSpeed_lt_originalBandGraphSpeed
#print axioms Region.centeredBandGraphCost_le_originalBandGraphCost
#print axioms Region.centeredBandGraphCost_lt_originalBandGraphCost
#print axioms Region.weightedTraceCost_centeredGraphTrace_le_graphTrace
#print axioms Region.weightedTraceCost_centeredGraphTrace_lt_graphTrace
#print axioms Region.volume_centeredSeamSymmDiff_eq_abs_totalWidth
#print axioms Region.volume_centeredSeamSymmDiff_le
#print axioms Region.weightedTraceCost_centeredHorizontalFrontierTrace_le
#print axioms Region.weightedTraceCost_completeCenteredFrontierTrace_le
#print axioms Region.weightedTraceCost_completeCenteredFrontierTrace_lt
#print axioms Region.weightedTraceCost_frontier_centeredCarrier_le
#print axioms Region.weightedTraceCost_frontier_centeredCarrier_lt
#print axioms centered_single_speed_eq_endpoint_speed_sum_iff
#print axioms centered_single_speed_lt_endpoint_speed_sum_iff
#print axioms Region.componentCount_eq_one_of_frontier_cost_eq
#print axioms
  Region.centeredBandGraphCost_lt_of_componentCount_eq_one_of_deriv_bandCenter_ne
#print axioms Region.deriv_bandCenter_eq_zero_of_frontier_cost_eq
#print axioms Region.exists_bandCenter_eq_on_Icc_of_frontier_cost_eq
#print axioms
  Region.weightedTraceCost_centeredGraphTrace_eq_of_frontier_cost_eq
#print axioms
  Region.weightedTraceCost_centeredHorizontalFrontierTrace_eq_of_frontier_cost_eq
#print axioms
  Region.centeredSeamCost_eq_originalSeamCost_of_frontier_cost_eq
#print axioms
  Region.volume_seamSymmDiff_eq_zero_of_frontier_cost_eq_of_width_eq
#print axioms Region.center_eq_of_equal_positive_width_interval_symmDiff_zero
#print axioms
  Region.bandCenter_seamLower_eq_seamUpper_of_frontier_cost_eq
#print axioms Region.exists_globalAxis_of_frontier_cost_eq
#print axioms Region.hasCenteredHorizontalIntervalSections_carrier
#print axioms Region.source_section_interfaces_of_frontier_cost_eq
#print axioms Region.frontier_cost_eq_of_minimizer_and_bounds
#print axioms
  Region.source_section_interfaces_of_minimizer_and_frontier_bounds
#print axioms
  Region.weightedTraceCost_frontier_carrier_le_smoothSequence_cost_of_projection_exhaustion
#print axioms
  Region.weightedTraceCost_frontier_carrier_le_relaxedPerimeter_of_projection_exhaustion
#print axioms Region.relaxedPerimeter_centeredCarrier_le_of_recovery
#print axioms
  Region.frontier_cost_eq_of_minimizer_and_projection_exhaustion_and_recovery
#print axioms
  Region.source_section_interfaces_of_projection_exhaustion_and_recovery
#print axioms TwoBandWidthJump.frontierCost_eq
#print axioms TwoBandWidthJump.oneSidedTotalWidths_continuous
#print axioms TwoBandWidthJump.equal_cost_but_width_jump_and_unequal_centers

/-- Compiled public dependency contract.  `R : Region` retains the finite-band
representation, continuous endpoint graphs, interior `C¹` regularity, finite
graph-speed integrals, and positive separated interior components.  Continuity
of each one-sided total width is derived from that data.  Literal frontier-cost
equality, positive matching widths at internal cuts, and planar AE source
agreement remain caller-visible; no relaxed-source minimizer premise is
accepted or inferred. -/
example (R : Region) {lam : ℝ} (hlam : 1 < lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (hwidth : ∀ i : Fin (R.bandCount - 1),
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : ∀ i : Fin (R.bandCount - 1), 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i))
    {E : Set PlanePoint} (hE : E =ᵐ[volume] R.carrier) :
    (∀ i, Continuous (R.totalWidth i)) ∧
      ∃ axis : ℝ,
        HasAEIntervalHorizontalSections E ∧
          CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E := by
  refine ⟨R.continuous_totalWidth, ?_⟩
  exact R.source_section_interfaces_of_frontier_cost_eq
    hlam.le heq hwidth hpos hE

/-- Compiled source-facing geometric bridge contract.  Minimality of the AE
source representative replaces literal frontier-cost equality once finite
disjoint projection families exhaust the original frontier and one concrete
smooth sequence recovers the centered frontier cost.  The projection error is
charged once per finite family and removed by characteristic convergence;
centered admissibility is constructed internally. -/
example (R : Region) {lam : ℝ} (hlam : 1 < lam)
    (hexhaust : ∀ {eta : ℝ}, 0 < eta →
      ∃ N : ℕ, ∃ P : Fin N → RigidProjectionPatch lam R.carrier,
        Set.Pairwise (Set.univ : Set (Fin N))
          (Function.onFun Disjoint fun i => (P i).window) ∧
        (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
        weightedTraceCost lam (frontier R.carrier) ≤
          (∑ i, (P i).payoff) + ENNReal.ofReal eta)
    (A : SmoothSequence) (hconv : A.ConvergesTo R.centeredCarrier)
    (hcost : A.cost lam ≤
      weightedTraceCost lam (frontier R.centeredCarrier))
    (hwidth : ∀ i : Fin (R.bandCount - 1),
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : ∀ i : Fin (R.bandCount - 1), 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i))
    {E : Set PlanePoint}
    (hmin : (relaxedSourceSemantics lam).IsMinimizer E)
    (hE : E =ᵐ[volume] R.carrier) :
    ∃ axis : ℝ,
      HasAEIntervalHorizontalSections E ∧
        CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E :=
  R.source_section_interfaces_of_projection_exhaustion_and_recovery
    hlam hexhaust A hconv hcost hwidth hpos hmin hE

namespace ThreeBandExample

#print axioms horizontalSection_carrier
#print axioms horizontalSection_carrier_neg_one
#print axioms horizontalSection_carrier_one
#print axioms lowerOverlap_mem_interior
#print axioms upperOverlap_mem_interior
#print axioms frontier_carrier_subset_completeTrace
#print axioms completeTrace_subset_frontier_carrier
#print axioms frontier_carrier
#print axioms lowerSeam_eq_symmDiff_union_endpoints
#print axioms upperSeam_eq_symmDiff_union_endpoints
#print axioms lowerSeamEndpoints_finite
#print axioms upperSeamEndpoints_finite
#print axioms hausdorffMeasure_lowerSeamEndpoints
#print axioms hausdorffMeasure_upperSeamEndpoints
#print axioms weightedTraceCost_two_lowerSeam
#print axioms weightedTraceCost_two_upperSeam

end ThreeBandExample
end CMVRelaxation.FiniteBandRearrangement
