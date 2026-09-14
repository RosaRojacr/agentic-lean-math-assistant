import CMVAELocalChartPreservation

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology ContDiff

noncomputable section

namespace CMVRelaxation

#print axioms mem_aeOpenRepresentative_congr_nhds
#print axioms eventually_mem_aeOpenRepresentative_congr_nhds
#print axioms strictHypograph_complement_volume_pos
#print axioms strictHypograph_graph_complement_volume_pos
#print axioms strictEpigraph_complement_volume_pos
#print axioms strictEpigraph_graph_complement_volume_pos
#print axioms aeOpenRepresentative_strictHypograph
#print axioms aeOpenRepresentative_strictEpigraph
#print axioms mem_aeOpenRepresentative_iff_of_eventually_strictHypograph
#print axioms mem_aeOpenRepresentative_iff_of_eventually_strictEpigraph
#print axioms strictLeftGraph_complement_volume_pos
#print axioms strictRightGraph_complement_volume_pos
#print axioms aeOpenRepresentative_strictLeftGraph
#print axioms aeOpenRepresentative_strictRightGraph
#print axioms mem_aeOpenRepresentative_iff_of_eventually_strictLeftGraph
#print axioms mem_aeOpenRepresentative_iff_of_eventually_strictRightGraph

namespace LocalChartPreservation

open FiniteJunctionRepair
open CMVFigureFour

#print axioms HasContinuousGraphGermOnSide
#print axioms HasContinuousGraphGermOnSide.exists_vertical_graph_eq_base
#print axioms HasContinuousGraphGermOnSide.eventually_mem_aeOpenRepresentative_iff
#print axioms HasContinuousGraphGermOnSide.selected
#print axioms HasContinuousGraphGermOnSide.mem_aeOpenRepresentative_iff
#print axioms continuousGraphGerm_of_orientedSmooth
#print axioms mem_aeOpenRepresentative_iff_of_orientedSmoothGraphGerm
#print axioms signedCircleValue
#print axioms contDiff_signedCircleValue
#print axioms fderiv_signedCircleValue_snd
#print axioms fderiv_signedCircleValue_fst
#print axioms exists_verticalOrientedSmoothGraphGerm_of_locallyOneSided_circle
#print axioms exists_horizontalOrientedSmoothGraphGerm_of_locallyOneSided_circle
#print axioms exists_verticalGraphGerm_of_locallyOneSided_circle
#print axioms exists_horizontalGraphGerm_of_locallyOneSided_circle
#print axioms exists_graphGerm_of_locallyOneSided_circle
#print axioms exists_verticalGraphGerm_at_horizontal_circle_tangency
#print axioms exists_horizontalGraphGerm_at_vertical_circle_tangency
#print axioms selectedSource_localChart_contract

namespace CircleChartExamples

open CMVFigureFour.FiniteCrossingExample

/-- An ordinary unit-circle point supports both valid coordinate graph charts. -/
theorem unitDisk_ordinary_has_both_orientations :
    (∃ side : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .vertical side openUnitDisk
        ((3 / 5 : ℝ), (4 / 5 : ℝ))) ∧
    (∃ side : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .horizontal side openUnitDisk
        ((3 / 5 : ℝ), (4 / 5 : ℝ))) := by
  have hcircle : circleValue (0, 0) 1
      ((3 / 5 : ℝ), (4 / 5 : ℝ)) = 0 := by
    norm_num [circleValue]
  constructor
  · exact exists_verticalGraphGerm_of_locallyOneSided_circle
      hcircle (by norm_num)
      (openUnitDisk_locallyOneSided ((3 / 5 : ℝ), (4 / 5 : ℝ)))
  · exact exists_horizontalGraphGerm_of_locallyOneSided_circle
      hcircle (by norm_num)
      (openUnitDisk_locallyOneSided ((3 / 5 : ℝ), (4 / 5 : ℝ)))

/-- At the top horizontal tangency, the graph over the first coordinate is the
valid chart; no nonexistent transverse first-coordinate derivative is used. -/
theorem unitDisk_top_tangency_has_vertical_chart :
    ∃ side : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .vertical side openUnitDisk (0, 1) := by
  exact exists_verticalGraphGerm_at_horizontal_circle_tangency
    (by norm_num) (by norm_num [circleValue]) (by norm_num)
    (openUnitDisk_locallyOneSided (0, 1))

/-- At the right vertical tangency, the graph over the second coordinate is the
valid chart. -/
theorem unitDisk_right_tangency_has_horizontal_chart :
    ∃ side : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .horizontal side openUnitDisk (1, 0) := by
  exact exists_horizontalGraphGerm_at_vertical_circle_tangency
    (by norm_num) (by norm_num [circleValue]) (by norm_num)
    (openUnitDisk_locallyOneSided (1, 0))

/-- The top-tangency chart is transported to the actual selected
representative, not merely recognized at its base point. -/
theorem unitDisk_top_tangency_selected_chart :
    ∃ side : SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .vertical side
        (aeOpenRepresentative openUnitDisk) (0, 1) := by
  obtain ⟨side, chart⟩ := unitDisk_top_tangency_has_vertical_chart
  exact ⟨side, chart.selected (Filter.EventuallyEq.rfl)⟩

end CircleChartExamples

/-- Compiled hypothesis contract.  Open-representative existence, AE interval
fibers, and every local chart remain explicit inputs. -/
example (lam : ℝ) {E U : Set PlanePoint}
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hEU : E =ᵐ[volume] U)
    (hsections : HasAEIntervalHorizontalSections E)
    {ι : Type*}
    (axis : ι → SpliceCutAxis)
    (side : ι → SpliceGraphOccupiedSide)
    (point : ι → PlanePoint)
    (charts : ∀ i, HasContinuousGraphGermOnSide
      (axis i) (side i) U (point i)) :
    let O := aeOpenRepresentative E
    IsOpen O ∧
      O =ᵐ[volume] E ∧
      _root_.WeightedArea lam O = _root_.WeightedArea lam E ∧
      relaxedPerimeter lam O = relaxedPerimeter lam E ∧
      ((relaxedSourceSemantics lam).IsAdmissible O ↔
        (relaxedSourceSemantics lam).IsAdmissible E) ∧
      ((relaxedSourceSemantics lam).IsMinimizer O ↔
        (relaxedSourceSemantics lam).IsMinimizer E) ∧
      (∀ y : ℝ,
        CMVSourceClassification.horizontalSection O y = ∅ ∨
          ∃ a b : ℝ, a < b ∧
            CMVSourceClassification.horizontalSection O y = Ioo a b) ∧
      ∀ i, HasContinuousGraphGermOnSide
        (axis i) (side i) O (point i) := by
  exact selectedSource_localChart_contract lam hUopen hUbounded hEU
    hsections axis side point charts

#print axioms CircleChartExamples.unitDisk_ordinary_has_both_orientations
#print axioms CircleChartExamples.unitDisk_top_tangency_has_vertical_chart
#print axioms CircleChartExamples.unitDisk_right_tangency_has_horizontal_chart
#print axioms CircleChartExamples.unitDisk_top_tangency_selected_chart

end LocalChartPreservation
end CMVRelaxation
