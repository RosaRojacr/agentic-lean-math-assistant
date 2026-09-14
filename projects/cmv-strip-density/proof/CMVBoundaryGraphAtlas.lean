/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryGlobalTransition
import CMVAELocalChartPreservation

/-!
# Smooth graph germs as actual frontier atlases

This file turns the existing source-local oriented graph germs into the ambient
half-space charts used by the boundary topology producer.  The independent
open unit disk then exercises the same generic component machinery as the
literal polygon specimen.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology ContDiff

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SmoothGraphAtlas

open CMVRelaxation.FiniteJunctionRepair
open CMVRelaxation.LocalChartPreservation

/-- A continuous vertical graph, centered at a chosen base abscissa, is
flattened by a global triangular homeomorphism. -/
def verticalGraphFlattening (f : ℝ → ℝ) (hf : Continuous f) (x₀ : ℝ) :
    PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.1 - x₀, q.2 - f q.1)
  invFun q := (q.1 + x₀, q.2 + f (q.1 + x₀))
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem verticalGraphFlattening_apply
    (f : ℝ → ℝ) (hf : Continuous f) (x₀ : ℝ) (q : PlanePoint) :
    verticalGraphFlattening f hf x₀ q =
      (q.1 - x₀, q.2 - f q.1) := rfl

/-- The coordinate-swapped triangular homeomorphism flattens a graph over the
second coordinate. -/
def horizontalGraphFlattening (f : ℝ → ℝ) (hf : Continuous f) (y₀ : ℝ) :
    PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.2 - y₀, q.1 - f q.2)
  invFun q := (q.2 + f (q.1 + y₀), q.1 + y₀)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem horizontalGraphFlattening_apply
    (f : ℝ → ℝ) (hf : Continuous f) (y₀ : ℝ) (q : PlanePoint) :
    horizontalGraphFlattening f hf y₀ q =
      (q.2 - y₀, q.1 - f q.2) := rfl

/-- An oriented smooth graph germ produces an actual ambient half-space chart.
Only the neighborhood certified by the germ is used; no global boundary trace
or component ordering is introduced. -/
theorem PointwiseHalfSpaceChart.nonempty_ofOrientedSmoothGraphGerm
    {axis : SpliceCutAxis} {graphSide : SpliceGraphOccupiedSide}
    {O : Set PlanePoint} {p : FrontierSpace O}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide
      axis graphSide O p.1) :
    Nonempty (PointwiseHalfSpaceChart O p) := by
  cases axis with
  | vertical =>
      rcases germ.exists_eventually_occupiedGraphDomain with
        ⟨f, hf, hfp, hlocal⟩
      cases graphSide with
      | negative =>
          obtain ⟨W, hWsub, hWopen, hpW⟩ :=
            _root_.mem_nhds_iff.mp hlocal
          exact ⟨PointwiseHalfSpaceChart.ofHomeomorph .lower
            (verticalGraphFlattening f hf.continuous p.1.1) W hWopen hpW
            (by simp only [verticalGraphFlattening_apply, sub_self,
              hfp, Prod.mk_zero_zero])
            (by
              intro q hq
              have hqModel := hWsub hq
              simpa only [OccupiedHalfPlane.carrier, mem_prod, mem_univ,
                mem_Iio, true_and, verticalGraphFlattening_apply,
                sub_lt_zero] using hqModel.symm)⟩
      | positive =>
          obtain ⟨W, hWsub, hWopen, hpW⟩ :=
            _root_.mem_nhds_iff.mp hlocal
          exact ⟨PointwiseHalfSpaceChart.ofHomeomorph .upper
            (verticalGraphFlattening f hf.continuous p.1.1) W hWopen hpW
            (by simp only [verticalGraphFlattening_apply, sub_self,
              hfp, Prod.mk_zero_zero])
            (by
              intro q hq
              have hqModel := hWsub hq
              simpa only [OccupiedHalfPlane.carrier, mem_prod, mem_univ,
                mem_Ioi, true_and, verticalGraphFlattening_apply,
                sub_pos] using hqModel.symm)⟩
  | horizontal =>
      rcases germ.exists_eventually_occupiedGraphDomain with
        ⟨f, hf, hfp, hlocal⟩
      cases graphSide with
      | negative =>
          obtain ⟨W, hWsub, hWopen, hpW⟩ :=
            _root_.mem_nhds_iff.mp hlocal
          exact ⟨PointwiseHalfSpaceChart.ofHomeomorph .lower
            (horizontalGraphFlattening f hf.continuous p.1.2) W hWopen hpW
            (by simp only [horizontalGraphFlattening_apply, sub_self,
              hfp, Prod.mk_zero_zero])
            (by
              intro q hq
              have hqModel := hWsub hq
              simpa only [OccupiedHalfPlane.carrier, mem_prod, mem_univ,
                mem_Iio, true_and, horizontalGraphFlattening_apply,
                sub_lt_zero] using hqModel.symm)⟩
      | positive =>
          obtain ⟨W, hWsub, hWopen, hpW⟩ :=
            _root_.mem_nhds_iff.mp hlocal
          exact ⟨PointwiseHalfSpaceChart.ofHomeomorph .upper
            (horizontalGraphFlattening f hf.continuous p.1.2) W hWopen hpW
            (by simp only [horizontalGraphFlattening_apply, sub_self,
              hfp, Prod.mk_zero_zero])
            (by
              intro q hq
              have hqModel := hWsub hq
              simpa only [OccupiedHalfPlane.carrier, mem_prod, mem_univ,
                mem_Ioi, true_and, horizontalGraphFlattening_apply,
                sub_pos] using hqModel.symm)⟩

/-- Choice of the actual ambient chart certified by an oriented smooth graph
germ. -/
noncomputable def PointwiseHalfSpaceChart.ofOrientedSmoothGraphGerm
    {axis : SpliceCutAxis} {graphSide : SpliceGraphOccupiedSide}
    {O : Set PlanePoint} {p : FrontierSpace O}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide
      axis graphSide O p.1) :
    PointwiseHalfSpaceChart O p :=
  Classical.choice
    (PointwiseHalfSpaceChart.nonempty_ofOrientedSmoothGraphGerm germ)

/-- Source-local regularity sufficient for the topology producer: every actual
frontier point has an oriented smooth graph germ in one coordinate direction.
This is pointwise data only; it supplies no global trace, component order, or
finite geometric inventory. -/
def HasOrientedSmoothBoundaryGraphAtlas (O : Set PlanePoint) : Prop :=
  ∀ p : FrontierSpace O,
    ∃ axis : SpliceCutAxis, ∃ graphSide : SpliceGraphOccupiedSide,
      HasOrientedSmoothBoundaryGraphGermOnSide axis graphSide O p.1

namespace HasOrientedSmoothBoundaryGraphAtlas

/-- The relaxation's literal smooth-domain contract supplies every oriented
graph germ required by the topology producer.  Nonvanishing of the defining
functional selects a coordinate direction; its sign selects the occupied
graph side. -/
theorem of_isSmoothDomain {O : Set PlanePoint}
    (hO : CMVRelaxation.IsSmoothDomain O) :
    HasOrientedSmoothBoundaryGraphAtlas O := by
  intro p
  rcases hO.regular_boundary p.1 p.2 with
    ⟨V, g, D, hVopen, hpV, hg, hgp, hderiv, hD, hlocal⟩
  rcases CMVRelaxation.continuousLinearMap_ne_zero_has_coordinate D hD with
      hx | hy
  · have hregular :
        CMVRelaxation.IsHorizontalRegularBoundaryValue O {p.1} p.1.2 := by
      intro q hq
      have hqp : q = p.1 := by
        simpa only [Set.mem_singleton_iff] using hq.1.2
      subst q
      exact ⟨V, g, D, hVopen, hpV, hg, hgp, hderiv, hD, hx, hlocal⟩
    obtain ⟨g', phi, hg', htrans, hphi, hphip, hmodel⟩ :=
      CMVRelaxation.local_oriented_smooth_graph_of_horizontal_regular hregular
        (p := p.1) ⟨⟨p.2, Set.mem_singleton p.1⟩, rfl⟩
    rcases lt_or_gt_of_ne htrans with hneg | hpos
    · exact ⟨.horizontal, .positive, g', phi, hg', htrans, hphi,
        hphip, hmodel, hneg⟩
    · exact ⟨.horizontal, .negative, g', phi, hg', htrans, hphi,
        hphip, hmodel, hpos⟩
  · have hregular :
        CMVRelaxation.IsVerticalRegularBoundaryValue O {p.1} p.1.1 := by
      intro q hq
      have hqp : q = p.1 := by
        simpa only [Set.mem_singleton_iff] using hq.1.2
      subst q
      exact ⟨V, g, D, hVopen, hpV, hg, hgp, hderiv, hD, hy, hlocal⟩
    obtain ⟨g', phi, hg', htrans, hphi, hphip, hmodel⟩ :=
      CMVRelaxation.local_oriented_smooth_graph_of_vertical_regular hregular
        (p := p.1) ⟨⟨p.2, Set.mem_singleton p.1⟩, rfl⟩
    rcases lt_or_gt_of_ne htrans with hneg | hpos
    · exact ⟨.vertical, .positive, g', phi, hg', htrans, hphi,
        hphip, hmodel, hneg⟩
    · exact ⟨.vertical, .negative, g', phi, hg', htrans, hphi,
        hphip, hmodel, hpos⟩

/-- Source-local regularity on an open representative restricts to the selected
frontier and survives AE selection.  Null puncture frontiers may disappear, but
no selected-frontier point is new. -/
theorem selected {E U : Set PlanePoint}
    (h : HasOrientedSmoothBoundaryGraphAtlas U)
    (hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    HasOrientedSmoothBoundaryGraphAtlas
      (CMVRelaxation.aeOpenRepresentative E) := by
  intro p
  let pU : FrontierSpace U :=
    ⟨p.1, CMVRelaxation.frontier_aeOpenRepresentative_subset_frontier_open
      hU hEU p.2⟩
  obtain ⟨axis, graphSide, germU⟩ := h pU
  have germ :
      HasOrientedSmoothBoundaryGraphGermOnSide
        axis graphSide U p.1 := by
    simpa only [pU] using germU
  exact ⟨axis, graphSide,
    CMVRelaxation.LocalChartPreservation.HasOrientedSmoothBoundaryGraphGermOnSide.selected
      germ hEU⟩

/-- Assemble the actual half-space atlas from pointwise source-regular graph
germs. -/
noncomputable def toBoundaryHalfSpaceAtlas {O : Set PlanePoint}
    (h : HasOrientedSmoothBoundaryGraphAtlas O) :
    BoundaryHalfSpaceAtlas O := by
  classical
  choose axis graphSide germ using h
  exact {
    chart := fun p =>
      PointwiseHalfSpaceChart.ofOrientedSmoothGraphGerm (germ p)
  }

end HasOrientedSmoothBoundaryGraphAtlas

end SmoothGraphAtlas

namespace UnitDisk

open BoundaryHalfSpaceAtlas
open SmoothGraphAtlas
open CMVRelaxation.LocalChartPreservation
open CMVFigureFour
open CMVFigureFour.FiniteCrossingExample

/-- The independently defined disk is the literal smooth domain already used
by the source relaxation. -/
theorem isSmoothDomain_openUnitDisk :
    CMVRelaxation.IsSmoothDomain openUnitDisk := by
  change CMVRelaxation.IsSmoothDomain CMVRelaxation.unitDisk
  exact CMVRelaxation.isSmoothDomain_unitDisk

/-- Every actual frontier point of the independently defined open unit disk has
an oriented smooth source-local graph germ, obtained through the generic
smooth-domain producer rather than circle-specific case splitting. -/
theorem hasOrientedSmoothBoundaryGraphAtlas :
    HasOrientedSmoothBoundaryGraphAtlas openUnitDisk :=
  HasOrientedSmoothBoundaryGraphAtlas.of_isSmoothDomain
    isSmoothDomain_openUnitDisk

/-- Every disk germ yields the corresponding ambient half-space chart. -/
theorem pointwiseChart_nonempty (p : FrontierSpace openUnitDisk) :
    Nonempty (PointwiseHalfSpaceChart openUnitDisk p) := by
  obtain ⟨_axis, _graphSide, germ⟩ :=
    hasOrientedSmoothBoundaryGraphAtlas p
  exact ⟨PointwiseHalfSpaceChart.ofOrientedSmoothGraphGerm germ⟩

/-- Complete actual pointwise atlas for the independent disk, assembled by the
generic source-regularity producer. -/
noncomputable def boundaryAtlas : BoundaryHalfSpaceAtlas openUnitDisk :=
  HasOrientedSmoothBoundaryGraphAtlas.toBoundaryHalfSpaceAtlas
    hasOrientedSmoothBoundaryGraphAtlas

/-- The generic compactness producer, not a supplied circle parameterization,
derives the disk's finite frontier-component decomposition. -/
noncomputable def finiteComponentDecomposition :
    FiniteFrontierComponentDecomposition openUnitDisk :=
  boundaryAtlas.finiteFrontierComponentDecomposition isBounded_openUnitDisk

/-- The generic component family exhausts the disk's actual frontier. -/
theorem finiteComponentDecomposition_exhausts :
    (⋃ i : finiteComponentDecomposition.index,
        componentAt (finiteComponentDecomposition.center i)) =
      frontier openUnitDisk :=
  finiteComponentDecomposition.iUnion_componentAt_eq_frontier

/-- The generic atlas topology makes the independent disk frontier locally path
connected without using its familiar global circle trace. -/
theorem frontier_locallyPathConnected :
    LocallyPathConnectedSpace (FrontierSpace openUnitDisk) :=
  boundaryAtlas.frontierLocallyPathConnectedSpace

/-- Every component of the disk frontier is infinite, as derived from the
generic local interval atlas. -/
theorem componentAt_infinite (p : FrontierSpace openUnitDisk) :
    (componentAt p).Infinite :=
  boundaryAtlas.infinite_componentAt p

/-- The component through every disk-frontier point exits its selected local
interval chart.  No global circle parameterization is used. -/
theorem component_exits_intervalAt_window (p : FrontierSpace openUnitDisk) :
    ∃ q : PlanePoint, q ∈ componentAt p ∧
      q ∉ (boundaryAtlas.intervalAt p).window :=
  boundaryAtlas.exists_mem_componentAt_not_mem_window isBounded_openUnitDisk
    (boundaryAtlas.intervalAt p)

/-- Every selected disk chart has exactly two connected local arms, both
incident to the chart base, without using the circle parameterization. -/
theorem intervalAt_twoBranchLocalTopology
    (p : FrontierSpace openUnitDisk) :
    let A := boundaryAtlas.intervalAt p
    IsConnected A.negativeBranch ∧
      IsConnected A.positiveBranch ∧
      Disjoint A.negativeBranch A.positiveBranch ∧
      A.negativeBranch ∪ A.positiveBranch = {A.baseInLocalDomain}ᶜ ∧
      A.baseInLocalDomain ∈ closure A.negativeBranch ∧
      A.baseInLocalDomain ∈ closure A.positiveBranch :=
  (boundaryAtlas.intervalAt p).twoBranchLocalTopology

/-- The generic global transition theorem bounds the number of disk-frontier
components remaining after any one actual frontier point is deleted. -/
theorem puncturedComponentCount_le_two
    (p : FrontierSpace openUnitDisk) :
    Nat.card (ConnectedComponents (PuncturedFrontierComponent p)) ≤ 2 :=
  boundaryAtlas.punctured_connectedComponents_natCard_le_two
    (boundaryAtlas.intervalAt p)

end UnitDisk
end CMVBoundaryLocalAtlas
