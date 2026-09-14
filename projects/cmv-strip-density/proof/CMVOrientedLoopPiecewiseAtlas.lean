import CMVBoundaryGraphAtlas
import CMVBoundaryFiniteChartCuts
import CMVBoundaryLocalAtlasSpecimen
import CMVFiniteCornerRepair

/-!
# Finite-junction boundary atlases for rectangular localization

A regular rectangular crop is generally not a smooth domain: transverse face
crossings and occupied rectangle corners are genuine corners.  This module
keeps those points in one derived finite set and constructs the actual local
half-space atlas at every other frontier point from the original smooth-domain
certificates.  No boundary curves, component inventory, or loop decomposition
is supplied.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace CMVRelaxation.FiniteJunctionRepair

open CMVTwoPatchGraphVariation

/-- The affine sign frame whose coordinates are the two inward-oriented
rectangle-corner distances. -/
def orientedCornerCoordinate
    (horizontal vertical : OccupiedSide) (center : _root_.PlanePoint) :
    _root_.PlanePoint ≃ₜ _root_.PlanePoint where
  toFun q :=
    (orientedCornerX horizontal center q,
      orientedCornerY vertical center q)
  invFun q :=
    (center.1 + horizontal.areaSign * q.1,
      center.2 + vertical.areaSign * q.2)
  left_inv q := by
    cases horizontal <;> cases vertical <;>
      ext <;>
      simp [orientedCornerX, orientedCornerY]
  right_inv q := by
    cases horizontal <;> cases vertical <;>
      ext <;>
      simp [orientedCornerX, orientedCornerY]
  continuous_toFun := by
    unfold orientedCornerX orientedCornerY
    fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem orientedCornerCoordinate_apply
    (horizontal vertical : OccupiedSide) (center q : _root_.PlanePoint) :
    orientedCornerCoordinate horizontal vertical center q =
      (orientedCornerX horizontal center q,
        orientedCornerY vertical center q) := rfl

@[simp] theorem orientedCornerCoordinate_self
    (horizontal vertical : OccupiedSide) (center : _root_.PlanePoint) :
    orientedCornerCoordinate horizontal vertical center center = (0, 0) := by
  simp [orientedCornerX, orientedCornerY]

end CMVRelaxation.FiniteJunctionRepair

namespace CMVBoundaryLocalAtlas
namespace SmoothGraphAtlas

open CMVRelaxation.FiniteJunctionRepair

/-- An oriented smooth graph germ survives replacement of its carrier on a
neighborhood of the base point. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.congr_nhds
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U O : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side U p)
    (hUO : ∀ᶠ q in 𝓝 p, q ∈ O ↔ q ∈ U) :
    HasOrientedSmoothBoundaryGraphGermOnSide axis side O p := by
  cases axis with
  | vertical =>
      rcases germ with ⟨g, phi, hg, htransverse, hphi, hphip, hlocal, hside⟩
      refine ⟨g, phi, hg, htransverse, hphi, hphip, ?_, hside⟩
      filter_upwards [hUO, hlocal] with q hqUO hq
      exact ⟨hqUO.trans hq.1, hq.2⟩
  | horizontal =>
      rcases germ with ⟨g, phi, hg, htransverse, hphi, hphip, hlocal, hside⟩
      refine ⟨g, phi, hg, htransverse, hphi, hphip, ?_, hside⟩
      filter_upwards [hUO, hlocal] with q hqUO hq
      exact ⟨hqUO.trans hq.1, hq.2⟩

/-- If an actual frontier is locally equal to a literal smooth domain, its
pointwise half-space chart is derived from that smooth model. -/
theorem PointwiseHalfSpaceChart.nonempty_of_local_smooth_model
    {O M V : Set PlanePoint} {p : FrontierSpace O}
    (hM : CMVRelaxation.IsSmoothDomain M)
    (hVopen : IsOpen V) (hpV : p.1 ∈ V)
    (hlocal : O ∩ V = M ∩ V) :
    Nonempty (PointwiseHalfSpaceChart O p) := by
  have hfrontier : frontier O ∩ V = frontier M ∩ V :=
    CMVRelaxation.frontier_inter_eq_of_inter_open_eq hVopen hlocal
  have hpM : p.1 ∈ frontier M := by
    have hpPair : p.1 ∈ frontier O ∩ V := ⟨p.2, hpV⟩
    rw [hfrontier] at hpPair
    exact hpPair.1
  let pM : FrontierSpace M := ⟨p.1, hpM⟩
  let atlas : HasOrientedSmoothBoundaryGraphAtlas M :=
    HasOrientedSmoothBoundaryGraphAtlas.of_isSmoothDomain hM
  obtain ⟨axis, side, germ⟩ := atlas pM
  have hUO : ∀ᶠ q in 𝓝 p.1, q ∈ O ↔ q ∈ M := by
    filter_upwards [hVopen.mem_nhds hpV] with q hqV
    have hq := Set.ext_iff.mp hlocal q
    simpa only [Set.mem_inter_iff, hqV, and_true] using hq
  exact PointwiseHalfSpaceChart.nonempty_ofOrientedSmoothGraphGerm
    (HasOrientedSmoothBoundaryGraphGermOnSide.congr_nhds
      (axis := axis) (side := side) germ hUO)

/-- Sign convention shared by a selected cut face and an oriented graph germ. -/
def signedCoordinateOccupied
    (side : SpliceGraphOccupiedSide) (x : ℝ) : Prop :=
  match side with
  | .negative => x < 0
  | .positive => 0 < x

/-- Reflect the cut-distance and graph-distance coordinates so their occupied
sides are simultaneously the positive quadrant. -/
def graphCutFrame
    (cutSide graphSide : SpliceGraphOccupiedSide) :
    CMVBoundaryLocalAtlas.StepPolygon.Frame :=
  match cutSide, graphSide with
  | .negative, .negative => .reflectBoth
  | .negative, .positive => .reflectFirst
  | .positive, .negative => .reflectSecond
  | .positive, .positive => .identity

/-- A transverse coordinate cut of one oriented smooth graph germ is a genuine
corner of the occupied carrier, hence has an ambient half-space chart after
quadrant flattening.  The caller supplies only the actual local carrier
identity; the graph and chart are derived. -/
theorem PointwiseHalfSpaceChart.nonempty_of_orientedGraphCut
    {axis : SpliceCutAxis}
    {cutSide graphSide : SpliceGraphOccupiedSide}
    {O G : Set PlanePoint} {p : FrontierSpace O}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide
      axis graphSide G p.1)
    (hcut : ∀ᶠ q in 𝓝 p.1,
      q ∈ O ↔
        (match axis with
        | .vertical =>
            signedCoordinateOccupied cutSide (q.1 - p.1.1)
        | .horizontal =>
            signedCoordinateOccupied cutSide (q.2 - p.1.2)) ∧
          q ∈ G) :
    Nonempty (PointwiseHalfSpaceChart O p) := by
  cases axis with
  | vertical =>
      obtain ⟨phi, hphi, hphip, hgraph⟩ :=
        germ.exists_eventually_occupiedGraphDomain
      let frame := graphCutFrame cutSide graphSide
      cases cutSide <;> cases graphSide <;>
        simp only [signedCoordinateOccupied] at hcut hgraph ⊢
      all_goals
        obtain ⟨V, hVsub, hVopen, hpV⟩ :=
          _root_.mem_nhds_iff.mp (hcut.and hgraph)
        refine ⟨PointwiseHalfSpaceChart.ofHomeomorph .upper
          (((verticalGraphFlattening phi hphi.continuous p.1.1).trans
            (CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate
              frame (0, 0))).trans
                CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten)
          V hVopen hpV ?_ ?_⟩
        · simp [verticalGraphFlattening_apply,
            CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate_apply,
            CMVBoundaryLocalAtlas.StepPolygon.Frame.apply, frame,
            graphCutFrame, hphip]
        · intro q hqV
          have hmodels := hVsub hqV
          change CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten
            (CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate
              frame (0, 0)
                (verticalGraphFlattening phi hphi.continuous p.1.1 q)) ∈
              OccupiedHalfPlane.upper.carrier ↔ q ∈ O
          rw [CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten_mem_upper_iff]
          simpa [verticalGraphFlattening_apply,
            CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate_apply,
            CMVBoundaryLocalAtlas.StepPolygon.Frame.apply, frame,
            graphCutFrame] using
              (and_congr Iff.rfl hmodels.2.symm).trans hmodels.1.symm
  | horizontal =>
      obtain ⟨phi, hphi, hphip, hgraph⟩ :=
        germ.exists_eventually_occupiedGraphDomain
      let frame := graphCutFrame cutSide graphSide
      cases cutSide <;> cases graphSide <;>
        simp only [signedCoordinateOccupied] at hcut hgraph ⊢
      all_goals
        obtain ⟨V, hVsub, hVopen, hpV⟩ :=
          _root_.mem_nhds_iff.mp (hcut.and hgraph)
        refine ⟨PointwiseHalfSpaceChart.ofHomeomorph .upper
          (((horizontalGraphFlattening phi hphi.continuous p.1.2).trans
            (CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate
              frame (0, 0))).trans
                CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten)
          V hVopen hpV ?_ ?_⟩
        · simp [horizontalGraphFlattening_apply,
            CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate_apply,
            CMVBoundaryLocalAtlas.StepPolygon.Frame.apply, frame,
            graphCutFrame, hphip]
        · intro q hqV
          have hmodels := hVsub hqV
          change CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten
            (CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate
              frame (0, 0)
                (horizontalGraphFlattening phi hphi.continuous p.1.2 q)) ∈
              OccupiedHalfPlane.upper.carrier ↔ q ∈ O
          rw [CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten_mem_upper_iff]
          simpa [horizontalGraphFlattening_apply,
            CMVBoundaryLocalAtlas.StepPolygon.frameCoordinate_apply,
            CMVBoundaryLocalAtlas.StepPolygon.Frame.apply, frame,
            graphCutFrame] using
              (and_congr Iff.rfl hmodels.2.symm).trans hmodels.1.symm

end SmoothGraphAtlas
end CMVBoundaryLocalAtlas

namespace CMVRelaxation

open CMVBoundaryLocalAtlas
open CMVBoundaryLocalAtlas.SmoothGraphAtlas
open FiniteJunctionRepair

/-- Derived finite topology of one bounded actual frontier: a complete atlas,
one center per connected component, and a finite chart-cut system whose compact
arcs cover the frontier.  It deliberately contains no cyclic order or loop. -/
structure FiniteBoundaryTopology (O : Set _root_.PlanePoint) where
  atlas : CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas O
  components :
    CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteFrontierComponentDecomposition O
  chartCuts :
    CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem atlas

/-- Boundedness and the actual pointwise atlas derive all finite topology data
retained before the cyclic arc-assembly step. -/
noncomputable def finiteBoundaryTopologyOfAtlas
    {O : Set _root_.PlanePoint}
    (A : CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O) :
    FiniteBoundaryTopology O where
  atlas := A
  components :=
    CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finiteFrontierComponentDecomposition
      A hObounded
  chartCuts :=
    CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finiteChartCutSystem
      A hObounded

/-- Type-valued finite-junction smooth boundary data for a bounded crop.
Retaining the exceptional set as data lets crop-specific consumers keep its
geometric provenance. -/
structure FiniteJunctionBoundaryData (O : Set _root_.PlanePoint) where
  exceptionalPoints : Set _root_.PlanePoint
  exceptionalPoints_finite : exceptionalPoints.Finite
  smooth_away_exceptionalPoints :
    ∀ p : FrontierSpace O, p.1 ∉ exceptionalPoints →
      ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
        HasOrientedSmoothBoundaryGraphGermOnSide axis side O p.1

/-- A bounded crop has smooth oriented graph germs away from some finite
exceptional set. -/
def HasFiniteJunctionBoundaryAtlas (O : Set _root_.PlanePoint) : Prop :=
  ∃ J : Set _root_.PlanePoint, J.Finite ∧
    ∀ p : FrontierSpace O, p.1 ∉ J →
      ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
        HasOrientedSmoothBoundaryGraphGermOnSide axis side O p.1

/-- Finite topology whose global cut contains every exceptional junction.
The exceptional set remains explicit: every point outside it, including
artificial chart-cut endpoints, retains an actual oriented smooth graph germ.
Every resulting open arc is therefore smooth, while only exceptional compact
arc endpoints require a nonsmooth branch splice. -/
structure FinitePiecewiseRegularBoundaryTopology
    (O : Set _root_.PlanePoint) extends FiniteBoundaryTopology O where
  exceptionalPoints : Set _root_.PlanePoint
  exceptionalPoints_finite : exceptionalPoints.Finite
  exceptionalPoints_subset_cutPoints :
    ∀ p : FrontierSpace O, p.1 ∈ exceptionalPoints →
      p ∈ chartCuts.cutPoints
  smooth_away_exceptionalPoints :
    ∀ p : FrontierSpace O, p.1 ∉ exceptionalPoints →
      ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
        HasOrientedSmoothBoundaryGraphGermOnSide axis side O p.1

/-- Explicit finite-junction data for a smooth rectangular splice.  Its
exceptional set is definitionally the actual splice-junction set. -/
noncomputable def finiteJunctionBoundaryData_openSpliceIn
    {U G : Set _root_.PlanePoint}
    (hU : IsSmoothDomain U) (hG : IsSmoothDomain G)
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u)
    (hfinite : (spliceJunctionSet U G l r d u).Finite) :
    FiniteJunctionBoundaryData
      (openSpliceIn U G (closedCutRectangle l r d u)) where
  exceptionalPoints := spliceJunctionSet U G l r d u
  exceptionalPoints_finite := hfinite
  smooth_away_exceptionalPoints := by
    intro p hpJ
    obtain ⟨M, V, hM, hVopen, hpV, hlocal⟩ :=
      openSpliceIn_locally_smooth_away_from_spliceJunctionSet
        hU hG hlr hdu p.2 hpJ
    have hfrontier : frontier
        (openSpliceIn U G (closedCutRectangle l r d u)) ∩ V =
          frontier M ∩ V :=
      frontier_inter_eq_of_inter_open_eq hVopen hlocal
    have hpM : p.1 ∈ frontier M := by
      have hpPair :
          p.1 ∈ frontier
            (openSpliceIn U G (closedCutRectangle l r d u)) ∩ V :=
        ⟨p.2, hpV⟩
      rw [hfrontier] at hpPair
      exact hpPair.1
    let pM : FrontierSpace M := ⟨p.1, hpM⟩
    obtain ⟨axis, side, germ⟩ :=
      SmoothGraphAtlas.HasOrientedSmoothBoundaryGraphAtlas.of_isSmoothDomain
        hM pM
    have hMO : ∀ᶠ q in 𝓝 p.1,
        q ∈ openSpliceIn U G (closedCutRectangle l r d u) ↔ q ∈ M := by
      filter_upwards [hVopen.mem_nhds hpV] with q hqV
      have hq := Set.ext_iff.mp hlocal q
      simpa only [Set.mem_inter_iff, hqV, and_true] using hq
    exact ⟨axis, side,
      HasOrientedSmoothBoundaryGraphGermOnSide.congr_nhds germ hMO⟩

@[simp] theorem finiteJunctionBoundaryData_openSpliceIn_exceptionalPoints
    {U G : Set _root_.PlanePoint}
    (hU : IsSmoothDomain U) (hG : IsSmoothDomain G)
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u)
    (hfinite : (spliceJunctionSet U G l r d u).Finite) :
    (finiteJunctionBoundaryData_openSpliceIn
      hU hG hlr hdu hfinite).exceptionalPoints =
        spliceJunctionSet U G l r d u :=
  rfl

/-- Smooth inputs and a finite rectangular splice-junction set derive the
finite-junction smooth graph atlas of the canonical open crop. -/
theorem hasFiniteJunctionBoundaryAtlas_openSpliceIn
    {U G : Set _root_.PlanePoint}
    (hU : IsSmoothDomain U) (hG : IsSmoothDomain G)
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u)
    (hfinite : (spliceJunctionSet U G l r d u).Finite) :
    HasFiniteJunctionBoundaryAtlas
      (openSpliceIn U G (closedCutRectangle l r d u)) := by
  let D := finiteJunctionBoundaryData_openSpliceIn
    hU hG hlr hdu hfinite
  exact ⟨D.exceptionalPoints, D.exceptionalPoints_finite,
    D.smooth_away_exceptionalPoints⟩

/-- Build the finite piecewise-regular topology from explicit exceptional-set
data.  The resulting topology retains that exact set definitionally. -/
noncomputable def finitePiecewiseRegularBoundaryTopologyOfData
    {O : Set _root_.PlanePoint}
    (A : CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O)
    (data : FiniteJunctionBoundaryData O) :
    FinitePiecewiseRegularBoundaryTopology O := by
  classical
  let junctionSet : Set (FrontierSpace O) :=
    {p | p.1 ∈ data.exceptionalPoints}
  have hJunctionSet : junctionSet.Finite := by
    change
      ((fun p : FrontierSpace O => p.1) ⁻¹'
        data.exceptionalPoints).Finite
    exact Set.Finite.preimage Subtype.val_injective.injOn
      data.exceptionalPoints_finite
  let junctions : Finset (FrontierSpace O) := hJunctionSet.toFinset
  let D :=
    CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finiteChartCutSystemIncluding
      A hObounded junctions
  refine {
    atlas := A
    components :=
      CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finiteFrontierComponentDecomposition
        A hObounded
    chartCuts := D
    exceptionalPoints := data.exceptionalPoints
    exceptionalPoints_finite := data.exceptionalPoints_finite
    exceptionalPoints_subset_cutPoints := ?_
    smooth_away_exceptionalPoints := data.smooth_away_exceptionalPoints
  }
  intro p hpJ
  apply D.additionalCutPoint_mem_cutPoints
  have hpJunctions : p ∈ junctions := by
    change p ∈ hJunctionSet.toFinset
    rw [Set.Finite.mem_toFinset]
    exact hpJ
  simpa only [D,
    CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.finiteChartCutSystemIncluding_additionalCutPoints]
    using hpJunctions

@[simp] theorem finitePiecewiseRegularBoundaryTopologyOfData_exceptionalPoints
    {O : Set _root_.PlanePoint}
    (A : CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O)
    (data : FiniteJunctionBoundaryData O) :
    (finitePiecewiseRegularBoundaryTopologyOfData
      A hObounded data).exceptionalPoints = data.exceptionalPoints :=
  rfl

/-- Refine the compactness-selected chart cuts by every exceptional frontier
point of a finite-junction smooth atlas.  Consequently no open quotient arc
passes through a corner or transverse crop junction. -/
noncomputable def finitePiecewiseRegularBoundaryTopologyOfAtlas
    {O : Set _root_.PlanePoint}
    (A : CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas O)
    (hObounded : Bornology.IsBounded O)
    (hregular : HasFiniteJunctionBoundaryAtlas O) :
    FinitePiecewiseRegularBoundaryTopology O := by
  classical
  let data : FiniteJunctionBoundaryData O := {
    exceptionalPoints := Classical.choose hregular
    exceptionalPoints_finite := (Classical.choose_spec hregular).1
    smooth_away_exceptionalPoints := (Classical.choose_spec hregular).2
  }
  exact finitePiecewiseRegularBoundaryTopologyOfData A hObounded data

/-- Every non-cut point is nonexceptional, so the previous public smoothness
contract follows from the stronger retained exceptional-set data. -/
theorem FinitePiecewiseRegularBoundaryTopology.smooth_away_cutPoints
    {O : Set _root_.PlanePoint}
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (p : FrontierSpace O) (hp : p ∉ T.chartCuts.cutPoints) :
    ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
      HasOrientedSmoothBoundaryGraphGermOnSide axis side O p.1 := by
  apply T.smooth_away_exceptionalPoints p
  intro hpExceptional
  exact hp (T.exceptionalPoints_subset_cutPoints p hpExceptional)

/-- Every point in a refined open arc has an actual oriented smooth graph germ.
Only exceptional cut points can require a nonsmooth branch splice. -/
theorem FinitePiecewiseRegularBoundaryTopology.smooth_finiteArcInterior
    {O : Set _root_.PlanePoint}
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (e : T.chartCuts.ArcIndex) {p : FrontierSpace O}
    (hp : p ∈ T.chartCuts.finiteArcInterior e) :
    ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
      HasOrientedSmoothBoundaryGraphGermOnSide axis side O p.1 := by
  exact T.smooth_away_cutPoints p
    (T.chartCuts.finiteArcInterior_subset_cutSpaceCarrier e hp)

/-- A clean rectangle corner of the one-input crop is an actual half-space
chart point.  The sharp one- or three-sector model is flattened by the
retained quadrant homeomorphism; no smoothing or omitted-corner convention is
used. -/
theorem nonempty_pointwiseHalfSpaceChart_openSpliceIn_empty_cleanCorner
    {G : Set _root_.PlanePoint} (hGopen : IsOpen G)
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u)
    {p : _root_.PlanePoint}
    (hpCorner :
      p ∈ ({(l, d), (l, u), (r, d), (r, u)} :
        Set _root_.PlanePoint))
    (hpFront :
      p ∈ frontier (openSpliceIn ∅ G (closedCutRectangle l r d u)))
    (hpG : p ∉ frontier G) :
    Nonempty (PointwiseHalfSpaceChart
      (openSpliceIn ∅ G (closedCutRectangle l r d u))
      ⟨p, hpFront⟩) := by
  let Aseq : ℕ → Set _root_.PlanePoint := fun _ => ∅
  let Gseq : ℕ → Set _root_.PlanePoint := fun _ => G
  let lseq : ℕ → ℝ := fun _ => l
  let rseq : ℕ → ℝ := fun _ => r
  let dseq : ℕ → ℝ := fun _ => d
  let useq : ℕ → ℝ := fun _ => u
  obtain ⟨sector, horizontal, vertical, N, hNopen, hpN, hlocalRaw⟩ :=
    exists_selectedRawSplice_cleanCorner_local_model
      Aseq Gseq lseq rseq dseq useq
      (fun _ => isOpen_empty) (fun _ => hGopen)
      (fun _ => hlr) (fun _ => hdu)
      (n := 0)
      (by simpa only [lseq, rseq, dseq, useq] using hpCorner)
      (by
        simpa only [selectedRawSplice, Aseq, Gseq, lseq, rseq, dseq,
          useq] using hpFront)
      (by simp only [Aseq, frontier_empty, Set.mem_empty_iff_false,
        not_false_eq_true])
      (by simpa only [Gseq] using hpG)
  have hlocal :
      openSpliceIn ∅ G (closedCutRectangle l r d u) ∩ N =
        openCornerSector sector horizontal vertical p ∩ N := by
    simpa only [selectedRawSplice, Aseq, Gseq, lseq, rseq, dseq,
      useq] using hlocalRaw
  have hmem (q : _root_.PlanePoint) (hqN : q ∈ N) :
      q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
        q ∈ openCornerSector sector horizontal vertical p := by
    have hq := Set.ext_iff.mp hlocal q
    simpa only [Set.mem_inter_iff, hqN, and_true] using hq
  cases sector with
  | below =>
      refine ⟨PointwiseHalfSpaceChart.ofHomeomorph .upper
        ((orientedCornerCoordinate horizontal vertical p).trans
          CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten)
        N hNopen hpN ?_ ?_⟩
      · simp [orientedCornerX, orientedCornerY]
      · intro q hqN
        change CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten
          (orientedCornerCoordinate horizontal vertical p q) ∈
            OccupiedHalfPlane.upper.carrier ↔
          q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u)
        rw [CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten_mem_upper_iff]
        simp only [orientedCornerCoordinate_apply]
        rw [← openCornerSector_below_mem_iff]
        exact (hmem q hqN).symm
  | above =>
      refine ⟨PointwiseHalfSpaceChart.ofHomeomorph .lower
        ((orientedCornerCoordinate horizontal vertical p).trans
          CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten)
        N hNopen hpN ?_ ?_⟩
      · simp [orientedCornerX, orientedCornerY]
      · intro q hqN
        change CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten
          (orientedCornerCoordinate horizontal vertical p q) ∈
            OccupiedHalfPlane.lower.carrier ↔
          q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u)
        rw [CMVBoundaryLocalAtlas.StepPolygon.quadrantFlatten_mem_lower_iff]
        simp only [orientedCornerCoordinate_apply]
        rw [← openCornerSector_above_mem_iff]
        exact (hmem q hqN).symm

/-- Every noncorner junction of a regularly selected one-input crop is a
transverse graph/cut corner, and therefore carries an actual ambient
half-space chart. -/
theorem nonempty_pointwiseHalfSpaceChart_openSpliceIn_empty_noncornerJunction
    {G : Set _root_.PlanePoint} (hGopen : IsOpen G)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ l r d u : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : l ∈ Ioo a₀ a₁) (hr : r ∈ Ioo b₀ b₁)
    (hd : d ∈ Ioo c₀ c₁) (hu : u ∈ Ioo d₀ d₁)
    (hL : IsRegularFiniteVerticalSpliceCut ∅ G
      (closedCutRectangle a₀ a₁ c₀ d₁) l)
    (hR : IsRegularFiniteVerticalSpliceCut ∅ G
      (closedCutRectangle b₀ b₁ c₀ d₁) r)
    (hD : IsRegularFiniteHorizontalSpliceCut ∅ G
      (closedCutRectangle a₀ b₁ c₀ c₁) d)
    (hU : IsRegularFiniteHorizontalSpliceCut ∅ G
      (closedCutRectangle a₀ b₁ d₀ d₁) u)
    {p : _root_.PlanePoint}
    (hpJ : p ∈ spliceJunctionSet ∅ G l r d u)
    (hpCorner :
      p ∉ ({(l, d), (l, u), (r, d), (r, u)} :
        Set _root_.PlanePoint))
    (hpFront :
      p ∈ frontier (openSpliceIn ∅ G (closedCutRectangle l r d u))) :
    Nonempty (PointwiseHalfSpaceChart
      (openSpliceIn ∅ G (closedCutRectangle l r d u))
      ⟨p, hpFront⟩) := by
  have hlr : l < r := hl.2.trans (hab.trans hr.1)
  have hdu : d < u := hd.2.trans (hcd.trans hu.1)
  have hpCross :
      p ∈ frontier G ∩ frontier (closedCutRectangle l r d u) := by
    have hpCrossRaw := hpJ.resolve_right hpCorner
    simpa only [Set.mem_inter_iff, Set.mem_union, frontier_empty,
      Set.mem_empty_iff_false, false_or] using hpCrossRaw
  have hpG : p ∈ frontier G := hpCross.1
  have hpWindowFrontier :
      p ∈ frontier (closedCutRectangle l r d u) := hpCross.2
  have hpWindow : p ∈ closedCutRectangle l r d u :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset hpWindowFrontier
  have hcrop :
      openSpliceIn ∅ G (closedCutRectangle l r d u) =
        G ∩ interior (closedCutRectangle l r d u) := by
    simp [openSpliceIn, spliceIn, interior_inter, hGopen.interior_eq]
  have hwindowInterior :
      interior (closedCutRectangle l r d u) =
        Ioo l r ×ˢ Ioo d u := by
    rw [closedCutRectangle, interior_prod_eq]
    simp
  have verticalGerm
      (K : Set _root_.PlanePoint) (x : ℝ)
      (hreg : IsVerticalRegularBoundaryValue G K x)
      (hpK : p ∈ K) (hpLine : p ∈ verticalLine x) :
      ∃ side, HasOrientedSmoothBoundaryGraphGermOnSide
        .vertical side G p := by
    obtain ⟨g, phi, hg, htransverse, hphi, hphip, hlocal⟩ :=
      local_oriented_smooth_graph_of_vertical_regular
        hreg ⟨⟨hpG, hpK⟩, hpLine⟩
    rcases lt_or_gt_of_ne htransverse with hnegative | hpositive
    · exact ⟨.positive, g, phi, hg, htransverse, hphi, hphip,
        hlocal, hnegative⟩
    · exact ⟨.negative, g, phi, hg, htransverse, hphi, hphip,
        hlocal, hpositive⟩
  have horizontalGerm
      (K : Set _root_.PlanePoint) (y : ℝ)
      (hreg : IsHorizontalRegularBoundaryValue G K y)
      (hpK : p ∈ K) (hpLine : p ∈ horizontalLine y) :
      ∃ side, HasOrientedSmoothBoundaryGraphGermOnSide
        .horizontal side G p := by
    obtain ⟨g, phi, hg, htransverse, hphi, hphip, hlocal⟩ :=
      local_oriented_smooth_graph_of_horizontal_regular
        hreg ⟨⟨hpG, hpK⟩, hpLine⟩
    rcases lt_or_gt_of_ne htransverse with hnegative | hpositive
    · exact ⟨.positive, g, phi, hg, htransverse, hphi, hphip,
        hlocal, hnegative⟩
    · exact ⟨.negative, g, phi, hg, htransverse, hphi, hphip,
        hlocal, hpositive⟩
  have hfaces :=
    frontier_closedCutRectangle_subset_lines hlr hdu hpWindowFrontier
  rcases hfaces with ((hpLeft | hpRight) | hpLower) | hpUpper
  · have hpX : p.1 = l := hpLeft
    have hpNotLower : p.2 ≠ d := by
      intro hpY
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl (Prod.ext hpX hpY)
    have hpNotUpper : p.2 ≠ u := by
      intro hpY
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inl (Prod.ext hpX hpY))
    have hpY : p.2 ∈ Ioo d u :=
      ⟨lt_of_le_of_ne hpWindow.2.1 hpNotLower.symm,
        lt_of_le_of_ne hpWindow.2.2 hpNotUpper⟩
    have hpK : p ∈ closedCutRectangle a₀ a₁ c₀ d₁ := by
      exact ⟨⟨by simpa only [hpX] using hl.1.le,
          by simpa only [hpX] using hl.2.le⟩,
        ⟨(hd.1.trans_le hpWindow.2.1).le,
          hpWindow.2.2.trans hu.2.le⟩⟩
    obtain ⟨side, germ⟩ :=
      verticalGerm _ l hL.2.1 hpK hpLeft
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .positive (q.1 - p.1) ∧ q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Iio_mem_nhds (by simpa [hpX] using hlr)),
          continuousAt_snd.eventually
            (Ioo_mem_nhds hpY.1 hpY.2)] with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied]
      constructor
      · rintro ⟨hqG, ⟨hql, _hqr⟩, _hqd, _hqu⟩
        exact ⟨by simpa only [hpX, sub_pos] using hql, hqG⟩
      · rintro ⟨hql, hqG⟩
        exact ⟨hqG, ⟨⟨by simpa only [hpX, sub_pos] using hql, hqx⟩,
          hqy⟩⟩
    exact PointwiseHalfSpaceChart.nonempty_of_orientedGraphCut
      (cutSide := .positive) (graphSide := side) germ hcut
  · have hpX : p.1 = r := hpRight
    have hpNotLower : p.2 ≠ d := by
      intro hpY
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inl (Prod.ext hpX hpY)))
    have hpNotUpper : p.2 ≠ u := by
      intro hpY
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inr (Prod.ext hpX hpY)))
    have hpY : p.2 ∈ Ioo d u :=
      ⟨lt_of_le_of_ne hpWindow.2.1 hpNotLower.symm,
        lt_of_le_of_ne hpWindow.2.2 hpNotUpper⟩
    have hpK : p ∈ closedCutRectangle b₀ b₁ c₀ d₁ := by
      exact ⟨⟨by simpa only [hpX] using hr.1.le,
          by simpa only [hpX] using hr.2.le⟩,
        ⟨(hd.1.trans_le hpWindow.2.1).le,
          hpWindow.2.2.trans hu.2.le⟩⟩
    obtain ⟨side, germ⟩ :=
      verticalGerm _ r hR.2.1 hpK hpRight
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .negative (q.1 - p.1) ∧ q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Ioi_mem_nhds (by simpa [hpX] using hlr)),
          continuousAt_snd.eventually
            (Ioo_mem_nhds hpY.1 hpY.2)] with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied]
      constructor
      · rintro ⟨hqG, ⟨_hql, hqr⟩, _hqd, _hqu⟩
        exact ⟨by simpa only [hpX, sub_neg] using hqr, hqG⟩
      · rintro ⟨hqr, hqG⟩
        exact ⟨hqG, ⟨⟨hqx,
          by simpa only [hpX, sub_neg] using hqr⟩, hqy⟩⟩
    exact PointwiseHalfSpaceChart.nonempty_of_orientedGraphCut
      (cutSide := .negative) (graphSide := side) germ hcut
  · have hpY : p.2 = d := hpLower
    have hpNotLeft : p.1 ≠ l := by
      intro hpX
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inl (Prod.ext hpX hpY)
    have hpNotRight : p.1 ≠ r := by
      intro hpX
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inl (Prod.ext hpX hpY)))
    have hpX : p.1 ∈ Ioo l r :=
      ⟨lt_of_le_of_ne hpWindow.1.1 hpNotLeft.symm,
        lt_of_le_of_ne hpWindow.1.2 hpNotRight⟩
    have hpK : p ∈ closedCutRectangle a₀ b₁ c₀ c₁ := by
      exact ⟨⟨(hl.1.trans_le hpWindow.1.1).le,
          hpWindow.1.2.trans hr.2.le⟩,
        ⟨by simpa only [hpY] using hd.1.le,
          by simpa only [hpY] using hd.2.le⟩⟩
    obtain ⟨side, germ⟩ :=
      horizontalGerm _ d hD.2.1 hpK hpLower
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .positive (q.2 - p.2) ∧ q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Ioo_mem_nhds hpX.1 hpX.2),
          continuousAt_snd.eventually (Iio_mem_nhds (by simpa [hpY] using hdu))]
          with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied]
      constructor
      · rintro ⟨hqG, ⟨_hql, _hqr⟩, hqd, _hqu⟩
        exact ⟨by simpa only [hpY, sub_pos] using hqd, hqG⟩
      · rintro ⟨hqd, hqG⟩
        exact ⟨hqG, ⟨hqx, ⟨by simpa only [hpY, sub_pos] using hqd,
          hqy⟩⟩⟩
    exact PointwiseHalfSpaceChart.nonempty_of_orientedGraphCut
      (cutSide := .positive) (graphSide := side) germ hcut
  · have hpY : p.2 = u := hpUpper
    have hpNotLeft : p.1 ≠ l := by
      intro hpX
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inl (Prod.ext hpX hpY))
    have hpNotRight : p.1 ≠ r := by
      intro hpX
      apply hpCorner
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inr (Prod.ext hpX hpY)))
    have hpX : p.1 ∈ Ioo l r :=
      ⟨lt_of_le_of_ne hpWindow.1.1 hpNotLeft.symm,
        lt_of_le_of_ne hpWindow.1.2 hpNotRight⟩
    have hpK : p ∈ closedCutRectangle a₀ b₁ d₀ d₁ := by
      exact ⟨⟨(hl.1.trans_le hpWindow.1.1).le,
          hpWindow.1.2.trans hr.2.le⟩,
        ⟨by simpa only [hpY] using hu.1.le,
          by simpa only [hpY] using hu.2.le⟩⟩
    obtain ⟨side, germ⟩ :=
      horizontalGerm _ u hU.2.1 hpK hpUpper
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .negative (q.2 - p.2) ∧ q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Ioo_mem_nhds hpX.1 hpX.2),
          continuousAt_snd.eventually (Ioi_mem_nhds (by simpa [hpY] using hdu))]
          with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied]
      constructor
      · rintro ⟨hqG, ⟨_hql, _hqr⟩, _hqd, hqu⟩
        exact ⟨by simpa only [hpY, sub_neg] using hqu, hqG⟩
      · rintro ⟨hqu, hqG⟩
        exact ⟨hqG, ⟨hqx, ⟨hqy,
          by simpa only [hpY, sub_neg] using hqu⟩⟩⟩
    exact PointwiseHalfSpaceChart.nonempty_of_orientedGraphCut
      (cutSide := .negative) (graphSide := side) germ hcut

/-- The regular one-input rectangular crop has a complete actual boundary
half-space atlas.  Away from the finite junction set this is inherited from a
local smooth model; noncorner crossings use the transverse graph/cut chart;
clean rectangle corners use the exact one-sector or three-sector chart. -/
noncomputable def boundaryHalfSpaceAtlas_openSpliceIn_empty_of_regularFiniteCuts
    {G : Set _root_.PlanePoint} (hG : IsSmoothDomain G)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ l r d u : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : l ∈ Ioo a₀ a₁) (hr : r ∈ Ioo b₀ b₁)
    (hd : d ∈ Ioo c₀ c₁) (hu : u ∈ Ioo d₀ d₁)
    (hL : IsRegularFiniteVerticalSpliceCut ∅ G
      (closedCutRectangle a₀ a₁ c₀ d₁) l)
    (hR : IsRegularFiniteVerticalSpliceCut ∅ G
      (closedCutRectangle b₀ b₁ c₀ d₁) r)
    (hD : IsRegularFiniteHorizontalSpliceCut ∅ G
      (closedCutRectangle a₀ b₁ c₀ c₁) d)
    (hU : IsRegularFiniteHorizontalSpliceCut ∅ G
      (closedCutRectangle a₀ b₁ d₀ d₁) u)
    (hcorner : ∀ p ∈
      ({(l, d), (l, u), (r, d), (r, u)} :
        Set _root_.PlanePoint),
      p ∉ frontier G) :
    BoundaryHalfSpaceAtlas
      (openSpliceIn ∅ G (closedCutRectangle l r d u)) where
  chart := fun p => Classical.choice (by
    have hlr : l < r := hl.2.trans (hab.trans hr.1)
    have hdu : d < u := hd.2.trans (hcd.trans hu.1)
    by_cases hpJ : p.1 ∈ spliceJunctionSet ∅ G l r d u
    · by_cases hpCorner :
          p.1 ∈ ({(l, d), (l, u), (r, d), (r, u)} :
            Set _root_.PlanePoint)
      · exact
          nonempty_pointwiseHalfSpaceChart_openSpliceIn_empty_cleanCorner
            hG.isOpen hlr hdu hpCorner p.2 (hcorner p.1 hpCorner)
      · exact
          nonempty_pointwiseHalfSpaceChart_openSpliceIn_empty_noncornerJunction
            hG.isOpen hab hcd hl hr hd hu hL hR hD hU hpJ hpCorner p.2
    · have hEmpty : IsSmoothDomain (∅ : Set _root_.PlanePoint) := by
        constructor
        · exact isOpen_empty
        · simp
      obtain ⟨M, V, hM, hVopen, hpV, hlocal⟩ :=
        openSpliceIn_locally_smooth_away_from_spliceJunctionSet
          hEmpty hG hlr hdu p.2 hpJ
      exact PointwiseHalfSpaceChart.nonempty_of_local_smooth_model
        hM hVopen hpV hlocal)

end CMVRelaxation
