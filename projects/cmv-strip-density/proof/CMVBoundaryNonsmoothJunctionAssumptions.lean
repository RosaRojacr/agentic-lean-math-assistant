import CMVBoundaryHeightCompletionSpecimen
import CMVFigureFourBoundaryRigidityExamples

#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.exists_joinedGraph_of_two_negative_vertical_germs
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.regularSublevel_has_negative_vertical_germ
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.exists_joinedGraph_of_two_positive_vertical_germs
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.continuousGraphGerm_of_two_positive_vertical_germs
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.regularSublevel_has_positive_vertical_germ
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.circleSublevel_has_positive_vertical_germ
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.mem_frontier_of_two_regular_sublevels
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.PointwiseHalfSpaceChart.nonempty_of_two_regular_sublevels
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.PointwiseHalfSpaceChart.nonempty_ofContinuousVerticalGraphGerm
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.PointwiseHalfSpaceChart.nonempty_selected_of_locallyOneSided_circle
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionCircleOccupancy.toJunctionGraphGerms
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionGraphGerms.selected_pointwiseChart_nonempty
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.BilateralJunctionGraphGerms.selectedBoundaryHalfSpaceAtlas
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.PointwiseHalfSpaceChart.exists_complete_local_frontier
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.ShelfApplication.eventually_carrier_iff_diagonal_arm_phases
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.ShelfApplication.transformed_shelf_arms_endpoint_and_tangent_separation
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.ShelfApplication.reentrantPoint_chart_nonempty_of_actual_regular_arms
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.ShelfApplication.reentrantPoint_complete_local_frontier
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.source_radius
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.actual_normal_separation
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.upperPhase_regular_germ
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.leftPhase_regular_germ
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.junction_mem_frontier
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.upperLeft_chart_of_actual_occupied_side
#print axioms CMVBoundaryLocalAtlas.NonsmoothJunction.RadiusTwoSourceApplication.upperLeft_complete_local_frontier_of_actual_occupied_side
#print axioms CMVSourceClassification.RawFourArcCoordinates.centered_upperLeft_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.centered_upperRight_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.centered_lowerLeft_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.centered_lowerRight_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.eventually_upperLeft_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.eventually_upperRight_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.eventually_lowerLeft_interiorModel
#print axioms CMVSourceClassification.RawFourArcCoordinates.eventually_lowerRight_interiorModel
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.bilateral_representative_nonempty
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.bilateral_representative_connected
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.bilateral_hasAEIntervalHorizontalSections
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.bilateral_junctionCircleOccupancy
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.ofBilateralJunctionCircleOccupancy
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.ofBilateralSource
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.exists_closedBoundaryTrace_of_bilateralJunctionCircleOccupancy
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.BilateralJunctionApplications.strictNegThree_completedBoundaryLoop_contract
#print axioms CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.BilateralJunctionApplications.endpointSeven_completedBoundaryLoop_contract

open Set Filter MeasureTheory Metric Bornology
open scoped Topology ContDiff ENNReal MeasureTheory

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace NonsmoothJunction

open CMVRelaxation.LocalChartPreservation

/-- Compiled local dependency contract.  The coordinate frame, two actual
regular defining functions, common endpoint, common transverse direction, and
literal occupied-side exhaustion are the complete inputs.  Frontier incidence,
the joined continuous graph, ambient half-space chart, and complete local
frontier parameterization are outputs. -/
example {U : Set PlanePoint} {p : PlanePoint}
    (H : PlanePoint ≃ₜ PlanePoint)
    (first second : PlanePoint → ℝ)
    (first_smooth : ContDiff ℝ ∞ first)
    (second_smooth : ContDiff ℝ ∞ second)
    (first_endpoint : first (H p) = 0)
    (second_endpoint : second (H p) = 0)
    (first_transverse : 0 < fderiv ℝ first (H p) (0, 1))
    (second_transverse : 0 < fderiv ℝ second (H p) (0, 1))
    (occupied : ∀ᶠ q in 𝓝 p,
      q ∈ U ↔ first (H q) < 0 ∨ second (H q) < 0) :
    ∃ hp : p ∈ frontier U,
      Nonempty (PointwiseHalfSpaceChart U ⟨p, hp⟩) ∧
        ∃ A : ActualFrontierIntervalChart U ⟨p, hp⟩,
          p ∈ A.window ∧
            ContinuousOn A.trace (Ioo (-A.radius) A.radius) ∧
            Set.InjOn A.trace (Ioo (-A.radius) A.radius) ∧
            frontier U ∩ A.window =
              A.trace '' Ioo (-A.radius) A.radius := by
  have hp : p ∈ frontier U :=
    mem_frontier_of_two_regular_sublevels H first second
      first_smooth second_smooth first_endpoint second_endpoint
      first_transverse second_transverse occupied
  have hchart : Nonempty (PointwiseHalfSpaceChart U ⟨p, hp⟩) :=
    PointwiseHalfSpaceChart.nonempty_of_two_regular_sublevels H first second
      first_smooth second_smooth first_endpoint second_endpoint
      first_transverse second_transverse occupied hp
  exact ⟨hp, hchart,
    PointwiseHalfSpaceChart.exists_complete_local_frontier hchart⟩

end NonsmoothJunction

namespace SelectedBoundaryTopologyInput

/-- Compiled source-applicability contract.  A literal density-two bilateral
incidence supplies bounded openness, connectedness, planar-AE agreement,
almost-everywhere interval sections, four local junction exhaustions, every
regular-point chart, and the unchanged complete selected loop.  No graph,
atlas, smooth-domain certificate, or boundary trace is an argument. -/
example (g : CMVFigureFour.BilateralSourceIncidence 2) :
    let D := ofBilateralSource g
    g.representative.Nonempty ∧
      IsOpen g.representative ∧
      Bornology.IsBounded g.representative ∧
      IsConnected g.representative ∧
      g.sourceCarrier =ᵐ[volume] g.representative ∧
      CMVRelaxation.HasAEIntervalHorizontalSections g.sourceCarrier ∧
      NonsmoothJunction.BilateralJunctionCircleOccupancy g ∧
      Continuous D.completedBoundaryLoop ∧
      D.completedBoundaryLoop 0 = D.completedBoundaryLoop 2 ∧
      Set.InjOn D.completedBoundaryLoop (Ico 0 2) ∧
      D.completedBoundaryLoop '' Icc 0 2 =
        frontier (CMVRelaxation.aeOpenRepresentative g.sourceCarrier) := by
  dsimp only
  exact ⟨bilateral_representative_nonempty g,
    g.sourceRepresentative.representative_open,
    g.sourceRepresentative.representative_bounded,
    bilateral_representative_connected g,
    g.sourceRepresentative.source_ae_representative,
    bilateral_hasAEIntervalHorizontalSections g,
    bilateral_junctionCircleOccupancy g,
    (ofBilateralSource g).continuous_completedBoundaryLoop,
    (ofBilateralSource g).completedBoundaryLoop_closed,
    (ofBilateralSource g).completedBoundaryLoop_injOn_Ico,
    (ofBilateralSource g).image_completedBoundaryLoop_Icc⟩

end SelectedBoundaryTopologyInput

#print axioms
  CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.BilateralJunctionApplications.strictNegThreeTopologyInput
#print axioms
  CMVBoundaryLocalAtlas.SelectedBoundaryTopologyInput.BilateralJunctionApplications.endpointSevenTopologyInput
#print axioms CMVBoundaryLocalAtlas.UnboundedNullDisk.selectedTrace_unboundedSource_compiledContract
#print axioms CMVFigureFour.Examples.strictBilateralSource_negThree_not_isMinimizer
#print axioms CMVFigureFour.Examples.endpointBilateralSource_seven_not_isMinimizer
#print axioms
  CMVFigureFour.Examples.strictBilateralSourceAt_negThree_union_horizontalNullLine_not_isMinimizer

end CMVBoundaryLocalAtlas
