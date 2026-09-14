import CMVOrientedLoopEmbeddedness
import CMVFiniteBandCostAssembly

/-!
# Exact cost accounting for finite boundary arcs

The quotient-indexed compact arc paths cover each cropped frontier once, with
only finite endpoint overlap.  Since `smoothCost` is the literal weighted
Euclidean Hausdorff measure of the frontier, countable additivity modulo those
null endpoint intersections gives coefficient-one cost accounting.  No metric
claim about the topological path parameter is used.
-/

open Set Function MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace BoundaryHalfSpaceAtlas
namespace FiniteChartCutSystem
open CMVRelaxation.FiniteBandRearrangement

variable {O : Set PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- The image of every normalized compact boundary arc is compact. -/
theorem isCompact_range_finiteArcPathLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    IsCompact (Set.range (D.finiteArcPathLR e)) := by
  rw [D.finiteArcPathLR_range]
  have hcompact : IsCompact (D.finiteArcClosure e) := by
    rw [D.finiteArcClosure_eq_selectedClosedArc]
    exact D.isCompact_cutComponentClosedArc
      (D.finiteArcChart e) (D.arcRepresentative e)
  exact hcompact.image continuous_subtype_val

/-- Every normalized compact boundary arc has a measurable planar image. -/
theorem measurableSet_range_finiteArcPathLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    MeasurableSet (Set.range (D.finiteArcPathLR e)) :=
  (D.isCompact_range_finiteArcPathLR e).measurableSet

/-- Distinct normalized arc images have only finitely many common points. -/
theorem finite_range_finiteArcPathLR_inter
    (D : FiniteChartCutSystem A) {e f : D.ArcIndex} (hef : e ≠ f) :
    (Set.range (D.finiteArcPathLR e) ∩
      Set.range (D.finiteArcPathLR f)).Finite := by
  apply Set.Finite.subset
    (Set.toFinite
      ({(D.finiteArcLeftEndpoint e).1,
        (D.finiteArcRightEndpoint e).1} : Set PlanePoint))
  intro q hq
  exact (D.finiteArcPathLR_range_inter_subset_endpointValues hef hq).1

/-- Every selected geometric loop has compact image. -/
theorem isCompact_range_boundaryGeometricWalkLoop
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    IsCompact (Set.range (D.boundaryGeometricWalkLoop j).path) :=
  isCompact_range (D.boundaryGeometricWalkLoop j).path.continuous

/-- Every selected geometric loop has a measurable planar image. -/
theorem measurableSet_range_boundaryGeometricWalkLoop
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    MeasurableSet (Set.range (D.boundaryGeometricWalkLoop j).path) :=
  (D.isCompact_range_boundaryGeometricWalkLoop j).measurableSet

/-- Distinct selected loop images have zero Euclidean one-dimensional
Hausdorff overlap because their planar images are disjoint. -/
theorem hausdorffMeasure_one_euclidean_loop_inter_eq_zero
    (D : FiniteChartCutSystem A) {j k : D.BoundaryLoopIndex}
    (hjk : j ≠ k) :
    (μH[1] : Measure EuclideanPlane)
      ((planeEuclideanHomeomorph ''
          Set.range (D.boundaryGeometricWalkLoop j).path) ∩
        (planeEuclideanHomeomorph ''
          Set.range (D.boundaryGeometricWalkLoop k).path)) = 0 := by
  rw [← Set.image_inter planeEuclideanHomeomorph.injective,
    disjoint_iff_inter_eq_empty.mp
      (D.disjoint_range_boundaryGeometricWalkLoop hjk),
    Set.image_empty, measure_empty]
/-- The literal weighted Euclidean cost of one selected geometric loop is the
coefficient-one sum of the compact arcs that its minimal traversal visits.
Finite endpoint intersections are `H¹`-null. -/
theorem weightedTraceCost_boundaryGeometricWalkLoop_eq_sum_arcs
    (D : FiniteChartCutSystem A) (lam : ℝ)
    (j : D.BoundaryLoopIndex) :
    CMVRelaxation.weightedTraceCost lam
        (Set.range (D.boundaryGeometricWalkLoop j).path) =
      ∑' e : {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j},
        CMVRelaxation.weightedTraceCost lam
          (Set.range (D.finiteArcPathLR e.1)) := by
  let _ : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  let _ : Finite {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j} := by
    infer_instance
  rw [D.boundaryGeometricWalkLoop_path_range_eq_iUnion_arcs]
  apply weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite
    lam
    (fun e : {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j} =>
      Set.range (D.finiteArcPathLR e.1))
    (fun e => D.measurableSet_range_finiteArcPathLR e.1)
  intro e f hef
  apply D.finite_range_finiteArcPathLR_inter
  intro heq
  exact hef (Subtype.ext heq)

/-- Exact coefficient-one decomposition of the literal smooth cost into the
weighted Euclidean costs of the once-indexed compact arc images.  Endpoint
intersections are `H¹`-null; no arc is charged once per endpoint direction. -/
theorem smoothCost_eq_sum_finiteArcPathLR
    (D : FiniteChartCutSystem A) (lam : ℝ) :
    CMVRelaxation.smoothCost lam O =
      ∑' e : D.ArcIndex,
        CMVRelaxation.weightedTraceCost lam
          (Set.range (D.finiteArcPathLR e)) := by
  let _ : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  calc
    CMVRelaxation.smoothCost lam O =
        CMVRelaxation.weightedTraceCost lam (frontier O) :=
      CMVRelaxation.smoothCost_eq_weightedTraceCost_frontier lam O
    _ = CMVRelaxation.weightedTraceCost lam
          (⋃ e : D.ArcIndex, Set.range (D.finiteArcPathLR e)) :=
      congrArg (CMVRelaxation.weightedTraceCost lam)
        D.iUnion_finiteArcPathLR_range_eq_frontier.symm
    _ = ∑' e : D.ArcIndex,
          CMVRelaxation.weightedTraceCost lam
            (Set.range (D.finiteArcPathLR e)) :=
      weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite
          lam (fun e : D.ArcIndex => Set.range (D.finiteArcPathLR e))
          D.measurableSet_range_finiteArcPathLR
          (fun {_e _f} hef => D.finite_range_finiteArcPathLR_inter hef)

/-- Exact cost accounting regrouped by the finite nonduplicating unoriented
walk-orbit family.  The dependent fiber places every compact arc in exactly
one outer summand by construction. -/
theorem smoothCost_eq_sum_boundaryLoopArcs
    (D : FiniteChartCutSystem A) (lam : ℝ) :
    CMVRelaxation.smoothCost lam O =
      ∑' j : D.BoundaryLoopIndex,
        ∑' e : {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j},
          CMVRelaxation.weightedTraceCost lam
            (Set.range (D.finiteArcPathLR e.1)) := by
  rw [D.smoothCost_eq_sum_finiteArcPathLR]
  calc
    (∑' e : D.ArcIndex,
        CMVRelaxation.weightedTraceCost lam
          (Set.range (D.finiteArcPathLR e))) =
        ∑' p : Σ j : D.BoundaryLoopIndex,
            {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j},
          CMVRelaxation.weightedTraceCost lam
            (Set.range (D.finiteArcPathLR p.2.1)) := by
      symm
      exact
        (Equiv.sigmaFiberEquiv D.arcBoundaryLoopIndex).tsum_eq
          (fun e : D.ArcIndex =>
            CMVRelaxation.weightedTraceCost lam
              (Set.range (D.finiteArcPathLR e)))
    _ = ∑' j : D.BoundaryLoopIndex,
          ∑' e : {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j},
            CMVRelaxation.weightedTraceCost lam
              (Set.range (D.finiteArcPathLR e.1)) :=
      by
        simpa only using
        (ENNReal.tsum_sigma
          (fun (j : D.BoundaryLoopIndex)
              (e : {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j}) =>
            CMVRelaxation.weightedTraceCost lam
              (Set.range (D.finiteArcPathLR e.1))))

/-- Exact coefficient-one accounting by the actual selected closed paths.
Neither opposite directions nor endpoint joins introduce an extra charge. -/
theorem smoothCost_eq_sum_boundaryGeometricWalkLoops
    (D : FiniteChartCutSystem A) (lam : ℝ) :
    CMVRelaxation.smoothCost lam O =
      ∑' j : D.BoundaryLoopIndex,
        CMVRelaxation.weightedTraceCost lam
          (Set.range (D.boundaryGeometricWalkLoop j).path) := by
  let _ : Finite D.BoundaryLoopIndex := D.finite_boundaryLoopIndex
  calc
    CMVRelaxation.smoothCost lam O =
        CMVRelaxation.weightedTraceCost lam (frontier O) :=
      CMVRelaxation.smoothCost_eq_weightedTraceCost_frontier lam O
    _ = CMVRelaxation.weightedTraceCost lam
          (⋃ j : D.BoundaryLoopIndex,
            Set.range (D.boundaryGeometricWalkLoop j).path) :=
      congrArg (CMVRelaxation.weightedTraceCost lam)
        D.iUnion_boundaryGeometricWalkLoop_path_range_eq_frontier.symm
    _ = ∑' j : D.BoundaryLoopIndex,
          CMVRelaxation.weightedTraceCost lam
            (Set.range (D.boundaryGeometricWalkLoop j).path) :=
      weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite
        lam
        (fun j : D.BoundaryLoopIndex =>
          Set.range (D.boundaryGeometricWalkLoop j).path)
        D.measurableSet_range_boundaryGeometricWalkLoop
        (fun {_j _k} hjk => by
          rw [disjoint_iff_inter_eq_empty.mp
            (D.disjoint_range_boundaryGeometricWalkLoop hjk)]
          exact Set.finite_empty)

end FiniteChartCutSystem
end BoundaryHalfSpaceAtlas
end CMVBoundaryLocalAtlas
