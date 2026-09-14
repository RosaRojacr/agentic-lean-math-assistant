import CMVOrientedLoopLocalization
import CMVFigureFiveSourceGeometry

/-!
# Figure-5 source localization for oriented-loop recovery

This adapter applies the generic rectangular localization theorem to the
bounded open representative carried by the actual Figure-5 source geometry.
The source carrier itself need not be literally bounded because the source
contract only identifies it with the representative almost everywhere.
-/

open Set Filter MeasureTheory
open scoped ENNReal MeasureTheory Topology symmDiff

noncomputable section

namespace CMVFigureFive
open CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem


/-- Every finite-cost smooth sequence converging to the actual Figure-5 source
has a regular-finite rectangular localization converging to its bounded open
representative, with the same liminf cost and vanishing complete cut cost. -/
theorem SourceGeometry.hasOpenRectangularLocalization
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    CMVRelaxation.HasOpenRectangularLocalization lam g.representative A := by
  apply CMVRelaxation.SmoothSequence.exists_open_rectangular_localization
    g.density_jump g.sourceRepresentative.representative_bounded A
  · exact (A.convergesTo_congr_ae
      g.sourceRepresentative.source_ae_representative).mp hconv
  · exact hcost

/-- The actual Figure-5 localization exposes a finite derived exception set on
every crop and an ambient half-space chart at every other actual frontier
point.  The retained junctions are precisely the remaining loop-extraction
work; no regularity at those points is assumed here. -/
theorem SourceGeometry.exists_localizedFiniteJunctionBoundaryAtlases
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, CMVRelaxation.HasFiniteJunctionBoundaryAtlas
        (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
          (CMVRelaxation.closedCutRectangle
            (l n) (r n) (d n) (u n))) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finiteJunctionBoundaryAtlases
      (g.hasOpenRectangularLocalization A hconv hcost)

/-- Every actual Figure-5 crop carries a complete derived boundary
half-space atlas, including transverse cut crossings and clean rectangle
corners. -/
theorem SourceGeometry.exists_localizedBoundaryHalfSpaceAtlases
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty (CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas
        (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
          (CMVRelaxation.closedCutRectangle
            (l n) (r n) (d n) (u n)))) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_boundaryHalfSpaceAtlases
      (g.hasOpenRectangularLocalization A hconv hcost)

/-- The actual Figure-5 recovery sequence therefore reaches the retained
finite-component decomposition and finite compact chart-arc cover on every
localized crop, without assuming either inventory. -/
theorem SourceGeometry.exists_localizedFiniteBoundaryTopologies
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty (CMVRelaxation.FiniteBoundaryTopology
        (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
          (CMVRelaxation.closedCutRectangle
            (l n) (r n) (d n) (u n)))) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finiteBoundaryTopologies
      (g.hasOpenRectangularLocalization A hconv hcost)

/-- The actual Figure-5 recovery crops refine their finite arc cuts by every
nonsmooth rectangle junction.  Every resulting open arc therefore retains a
source-derived oriented smooth graph germ at each of its points. -/
theorem SourceGeometry.exists_localizedFinitePiecewiseRegularBoundaryTopologies
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty (CMVRelaxation.FinitePiecewiseRegularBoundaryTopology
        (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
          (CMVRelaxation.closedCutRectangle
            (l n) (r n) (d n) (u n)))) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finitePiecewiseRegularBoundaryTopologies
      (g.hasOpenRectangularLocalization A hconv hcost)

/-- Every localized Figure-5 approximant carries one globally defined
occupied-left branch field on its finite open arcs and the induced reference
assignment on its half-edges. -/
theorem SourceGeometry.exists_localizedOccupiedLeftArcBranchAssignments
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty
        (Σ T : CMVRelaxation.FinitePiecewiseRegularBoundaryTopology
            (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
              (CMVRelaxation.closedCutRectangle
                (l n) (r n) (d n) (u n))),
          CMVRelaxation.OccupiedLeftArcBranchAssignment T) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_occupiedLeftArcBranchAssignments
      (g.hasOpenRectangularLocalization A hconv hcost)
/-- At every transverse source/rectangle crossing in the same Figure-5
localization, both the source graph and the straight cut face extend smoothly,
injectively, and nonstationarily through the endpoint with their actual
occupied sides on the left; their half-spaces reconstruct the crop locally. -/
theorem SourceGeometry.exists_localizedTransverseEndpointTraces
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n (p : PlanePoint),
        p ∈ CMVRelaxation.FiniteJunctionRepair.spliceJunctionSet
          ∅ (B.carrier n) (l n) (r n) (d n) (u n) →
        p ∉ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        Nonempty
          (CMVRelaxation.FiniteJunctionRepair.OccupiedLeftTransverseEndpointTraces
            (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
              (CMVRelaxation.closedCutRectangle
                (l n) (r n) (d n) (u n)))
            (B.carrier n) p) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_transverseEndpointTraces
      (g.hasOpenRectangularLocalization A hconv hcost)
/-- At each corner of the same Figure-5 localization, two explicit
perpendicular cut traces carry the occupied rectangle interior on their left
and reconstruct it locally as the intersection of their inward half-spaces. -/
theorem SourceGeometry.exists_localizedCleanCornerCutTraces
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n (p : PlanePoint),
        p ∈ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        ∃ verticalSide horizontalSide :
            CMVRelaxation.FiniteJunctionRepair.SpliceGraphOccupiedSide,
          ∀ᶠ q in 𝓝 p,
            q ∈ interior
                (CMVRelaxation.closedCutRectangle
                  (l n) (r n) (d n) (u n)) ↔
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  verticalSide
                  (CMVRelaxation.FiniteJunctionRepair.cutNormalCoordinate
                    .vertical p q) ∧
                CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  horizontalSide
                  (CMVRelaxation.FiniteJunctionRepair.cutNormalCoordinate
                    .horizontal p q) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_cleanCornerCutTraces
      (g.hasOpenRectangularLocalization A hconv hcost)



/-- The actual Figure-5 recovery crops carry exact degree-two incidence at
every cut vertex: the negative and positive chart germs are distinct, incident,
and exhaust all compact arcs there. -/
theorem SourceGeometry.exists_localizedFiniteBoundaryIncidences
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : CMVRelaxation.FiniteBoundaryTopology
          (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
            (CMVRelaxation.closedCutRectangle
              (l n) (r n) (d n) (u n))),
        ∀ v : T.chartCuts.cutPoints,
          ∃ N : CutPointCoreNeighborhood T.chartCuts v,
            Nat.card (T.chartCuts.IncidentArc v) = 2 ∧
            N.negativeArcIndex ≠ N.positiveArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.negativeArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.positiveArcIndex := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finiteBoundaryIncidences
      (g.hasOpenRectangularLocalization A hconv hcost)


/-- Every actual Figure-5 recovery crop carries the canonical periodic
half-edge traversal obtained by switching to the other local germ and crossing
that compact arc. -/
theorem SourceGeometry.exists_localizedFiniteBoundaryCyclicTraversals
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : CMVRelaxation.FiniteBoundaryTopology
          (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
            (CMVRelaxation.closedCutRectangle
              (l n) (r n) (d n) (u n))),
        (∀ v : T.chartCuts.cutPoints,
          ∃ N : CutPointCoreNeighborhood T.chartCuts v,
            Nat.card (T.chartCuts.IncidentArc v) = 2 ∧
            N.negativeArcIndex ≠ N.positiveArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.negativeArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.positiveArcIndex) ∧
        ∀ e : T.chartCuts.HalfEdge,
          ∃ k : ℕ, 0 < k ∧
            ((T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[k]) e = e := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finiteBoundaryCyclicTraversals
      (g.hasOpenRectangularLocalization A hconv hcost)

/-- Every actual Figure-5 recovery crop carries a positive finite cyclic
sequence of embedded boundary-arc paths.  Each piece is an actual compact arc
closure from the derived chart-cut system. -/
theorem SourceGeometry.exists_localizedFiniteBoundaryGeometricTraversals
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : CMVRelaxation.FiniteBoundaryTopology
          (CMVRelaxation.openSpliceIn ∅ (B.carrier n)
            (CMVRelaxation.closedCutRectangle
              (l n) (r n) (d n) (u n))),
        (∀ v : T.chartCuts.cutPoints,
          ∃ N : CutPointCoreNeighborhood T.chartCuts v,
            Nat.card (T.chartCuts.IncidentArc v) = 2 ∧
            N.negativeArcIndex ≠ N.positiveArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.negativeArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.positiveArcIndex) ∧
        ∀ e : T.chartCuts.HalfEdge,
          ∃ k : ℕ, 0 < k ∧
            ((T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[k]) e = e ∧
            ∀ i : Fin k,
              Function.Injective
                  (T.chartCuts.walkArcPath
                    (((T.chartCuts.walkStep :
                      T.chartCuts.HalfEdge →
                        T.chartCuts.HalfEdge)^[i.1]) e)) ∧
                Set.range
                    (T.chartCuts.walkArcPath
                      (((T.chartCuts.walkStep :
                        T.chartCuts.HalfEdge →
                          T.chartCuts.HalfEdge)^[i.1]) e)) =
                  Subtype.val ''
                    T.chartCuts.finiteArcClosure
                      (T.chartCuts.switchHalfEdge
                        (((T.chartCuts.walkStep :
                          T.chartCuts.HalfEdge →
                            T.chartCuts.HalfEdge)^[i.1]) e)).1.2 := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finiteBoundaryGeometricTraversals
      (g.hasOpenRectangularLocalization A hconv hcost)

/-- The actual Figure-5 localization exposes one minimal closed path per
unoriented walk orbit. These paths exactly cover the cropped frontier, their
compact measurable images realize the once-indexed arc fibers, and their
literal weighted Euclidean costs sum exactly to `smoothCost`; opposite
half-edge traversals remain disjoint. Every open-arc point has an occupied-left
smooth nonstationary trace. On the same crop witnesses, every transverse
source/cut endpoint has both regular occupied-left branch extensions with an
exact local crop model, and each clean rectangle corner has its two inward
straight extensions. -/
theorem SourceGeometry.exists_localizedFiniteBoundaryClosedWalkPaths
    {lam : ℝ} (g : SourceGeometry lam) (A : CMVRelaxation.SmoothSequence)
    (hconv : A.ConvergesTo g.sourceCarrier) (hcost : A.cost lam < ⊤) :
    ∃ (B : CMVRelaxation.SmoothSequence) (R : ℝ)
        (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      g.representative ⊆
        Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo g.representative ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => CMVRelaxation.smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      let W : ℕ → Set PlanePoint := fun n =>
        CMVRelaxation.closedCutRectangle (l n) (r n) (d n) (u n)
      let cropped : ℕ → Set PlanePoint := fun n =>
        CMVRelaxation.openSpliceIn ∅ (B.carrier n) (W n)
      let cutCost : ℕ → ENNReal := fun n =>
        CMVRelaxation.weightedTraceCost lam
          (CMVRelaxation.spliceCutTrace ∅ (B.carrier n) (W n))
      Tendsto cutCost atTop (𝓝 0) ∧
      Tendsto
        (fun n => CMVRelaxation.characteristicDistance
          (cropped n) g.representative) atTop (𝓝 0) ∧
      (∀ n, CMVRelaxation.smoothCost lam (cropped n) ≤
        CMVRelaxation.smoothCost lam (B.carrier n) + cutCost n) ∧
      (∀ n (p : PlanePoint),
        p ∈ CMVRelaxation.FiniteJunctionRepair.spliceJunctionSet
          ∅ (B.carrier n) (l n) (r n) (d n) (u n) →
        p ∉ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        Nonempty
          (CMVRelaxation.FiniteJunctionRepair.OccupiedLeftTransverseEndpointTraces
            (cropped n) (B.carrier n) p)) ∧
      (∀ n (p : PlanePoint),
        p ∈ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        ∃ verticalSide horizontalSide :
            CMVRelaxation.FiniteJunctionRepair.SpliceGraphOccupiedSide,
          ∀ᶠ q in 𝓝 p,
            q ∈ interior (W n) ↔
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  verticalSide
                  (CMVRelaxation.FiniteJunctionRepair.cutNormalCoordinate
                    .vertical p q) ∧
                CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  horizontalSide
                  (CMVRelaxation.FiniteJunctionRepair.cutNormalCoordinate
                    .horizontal p q)) ∧
      ∀ n, CMVRelaxation.HasFiniteBoundaryClosedWalkPaths lam
        (cropped n) := by
  exact
    CMVRelaxation.HasOpenRectangularLocalization.exists_finiteBoundaryClosedWalkPaths
      (g.hasOpenRectangularLocalization A hconv hcost)

end CMVFigureFive
