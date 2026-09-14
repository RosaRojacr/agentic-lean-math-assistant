import CMVOrientedLoopPiecewiseAtlas

/-!
# Occupied-side oriented local boundary traces

A retained smooth boundary graph germ determines more than a topological
frontier chart.  This module gives it an explicit regular parameterization and
chooses the direction for which the certified occupied coordinate side lies on
the left.  The construction is local; endpoint regularity is exposed exactly
when the topology retains a smooth germ there.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteJunctionRepair
open CMVBoundaryLocalAtlas.SmoothGraphAtlas

/-- The literal strict graph side certified by an oriented smooth boundary
germ. -/
def orientedGraphDomain (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (φ : ℝ → ℝ) : Set PlanePoint :=
  match axis, side with
  | .vertical, .negative => {q | q.2 < φ q.1}
  | .vertical, .positive => {q | φ q.1 < q.2}
  | .horizontal, .negative => {q | q.1 < φ q.2}
  | .horizontal, .positive => {q | φ q.2 < q.1}

/-- Parameterization of the graph directed so that its occupied coordinate
side is on the left.  Negative vertical and positive horizontal graph sides
require reversal. -/
def occupiedLeftGraphTrace (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (φ : ℝ → ℝ) (t : ℝ) : PlanePoint :=
  match axis, side with
  | .vertical, .negative => (-t, φ (-t))
  | .vertical, .positive => (t, φ t)
  | .horizontal, .negative => (φ t, t)
  | .horizontal, .positive => (φ (-t), -t)

/-- Velocity of `occupiedLeftGraphTrace`. -/
def occupiedLeftGraphVelocity (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (φ : ℝ → ℝ) (t : ℝ) : PlanePoint :=
  match axis, side with
  | .vertical, .negative => (-1, -deriv φ (-t))
  | .vertical, .positive => (1, deriv φ t)
  | .horizontal, .negative => (deriv φ t, 1)
  | .horizontal, .positive => (-deriv φ (-t), -1)

/-- Unit transverse direction pointing into the graph side certified as
occupied. -/
def occupiedGraphProbe (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) : PlanePoint :=
  match axis, side with
  | .vertical, .negative => (0, -1)
  | .vertical, .positive => (0, 1)
  | .horizontal, .negative => (-1, 0)
  | .horizontal, .positive => (1, 0)

/-- Signed planar determinant.  Positive means that the second vector points
to the left of the first. -/
def planarDet (v w : PlanePoint) : ℝ := v.1 * w.2 - v.2 * w.1
/-- Signed coordinate normal to a rectangular cut face through `p`. -/
def cutNormalCoordinate (axis : SpliceCutAxis)
    (p q : PlanePoint) : ℝ :=
  match axis with
  | .vertical => q.1 - p.1
  | .horizontal => q.2 - p.2

/-- Straight cut-face trace directed with the selected crop side on its left. -/
def occupiedLeftCutTrace (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (p : PlanePoint) (t : ℝ) :
    PlanePoint :=
  match axis, side with
  | .vertical, .negative => (p.1, p.2 + t)
  | .vertical, .positive => (p.1, p.2 - t)
  | .horizontal, .negative => (p.1 - t, p.2)
  | .horizontal, .positive => (p.1 + t, p.2)

/-- Constant velocity of the occupied-left cut-face trace. -/
def occupiedLeftCutVelocity (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) : PlanePoint :=
  match axis, side with
  | .vertical, .negative => (0, 1)
  | .vertical, .positive => (0, -1)
  | .horizontal, .negative => (-1, 0)
  | .horizontal, .positive => (1, 0)

/-- Unit normal pointing from the cut face into its selected crop side. -/
def occupiedCutProbe (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) : PlanePoint :=
  match axis, side with
  | .vertical, .negative => (-1, 0)
  | .vertical, .positive => (1, 0)
  | .horizontal, .negative => (0, -1)
  | .horizontal, .positive => (0, 1)

theorem occupiedLeftCutTrace_zero (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (p : PlanePoint) :
    occupiedLeftCutTrace axis side p 0 = p := by
  cases axis <;> cases side <;> simp [occupiedLeftCutTrace]

theorem cutNormalCoordinate_occupiedLeftCutTrace
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (p : PlanePoint) (t : ℝ) :
    cutNormalCoordinate axis p (occupiedLeftCutTrace axis side p t) = 0 := by
  cases axis <;> cases side <;>
    simp [cutNormalCoordinate, occupiedLeftCutTrace]

theorem occupiedLeftCutTrace_contDiff (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (p : PlanePoint) :
    ContDiff ℝ ∞ (occupiedLeftCutTrace axis side p) := by
  cases axis with
  | vertical =>
      cases side with
      | negative =>
          exact contDiff_const.prodMk (contDiff_const.add contDiff_id)
      | positive =>
          exact contDiff_const.prodMk (contDiff_const.sub contDiff_id)
  | horizontal =>
      cases side with
      | negative =>
          exact (contDiff_const.sub contDiff_id).prodMk contDiff_const
      | positive =>
          exact (contDiff_const.add contDiff_id).prodMk contDiff_const

theorem occupiedLeftCutTrace_hasDerivAt (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (p : PlanePoint) (t : ℝ) :
    HasDerivAt (occupiedLeftCutTrace axis side p)
      (occupiedLeftCutVelocity axis side) t := by
  cases axis with
  | vertical =>
      cases side with
      | negative =>
          change HasDerivAt (fun s : ℝ => ((p.1, p.2 + s) : PlanePoint))
            (0, 1) t
          convert (hasDerivAt_const t p.1).prodMk
            ((hasDerivAt_const t p.2).add (hasDerivAt_id t)) using 1 <;> simp
      | positive =>
          change HasDerivAt (fun s : ℝ => ((p.1, p.2 - s) : PlanePoint))
            (0, -1) t
          convert (hasDerivAt_const t p.1).prodMk
            ((hasDerivAt_const t p.2).sub (hasDerivAt_id t)) using 1 <;> simp
  | horizontal =>
      cases side with
      | negative =>
          change HasDerivAt (fun s : ℝ => ((p.1 - s, p.2) : PlanePoint))
            (-1, 0) t
          convert ((hasDerivAt_const t p.1).sub (hasDerivAt_id t)).prodMk
            (hasDerivAt_const t p.2) using 1 <;> simp
      | positive =>
          change HasDerivAt (fun s : ℝ => ((p.1 + s, p.2) : PlanePoint))
            (1, 0) t
          convert ((hasDerivAt_const t p.1).add (hasDerivAt_id t)).prodMk
            (hasDerivAt_const t p.2) using 1 <;> simp

theorem occupiedLeftCutVelocity_ne_zero (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) :
    occupiedLeftCutVelocity axis side ≠ 0 := by
  cases axis <;> cases side <;> simp [occupiedLeftCutVelocity]

theorem occupiedLeftCutTrace_injective (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (p : PlanePoint) :
    Function.Injective (occupiedLeftCutTrace axis side p) := by
  intro s t hst
  cases axis with
  | vertical =>
      cases side with
      | negative =>
          have h := congrArg Prod.snd hst
          simpa [occupiedLeftCutTrace] using h
      | positive =>
          have h := congrArg Prod.snd hst
          simpa [occupiedLeftCutTrace] using h
  | horizontal =>
      cases side with
      | negative =>
          have h := congrArg Prod.fst hst
          simpa [occupiedLeftCutTrace] using h
      | positive =>
          have h := congrArg Prod.fst hst
          simpa [occupiedLeftCutTrace] using h

theorem planarDet_occupiedLeftCutVelocity_probe
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide) :
    planarDet (occupiedLeftCutVelocity axis side)
      (occupiedCutProbe axis side) = 1 := by
  cases axis <;> cases side <;>
    simp [planarDet, occupiedLeftCutVelocity, occupiedCutProbe]

/-- A positive displacement along the certified probe is strictly inside the
selected coordinate half-space. -/
theorem signedCoordinateOccupied_cutProbe
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (p : PlanePoint) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    signedCoordinateOccupied side
      (cutNormalCoordinate axis p
        (p.1 + epsilon * (occupiedCutProbe axis side).1,
          p.2 + epsilon * (occupiedCutProbe axis side).2)) := by
  cases axis <;> cases side <;>
    simp [signedCoordinateOccupied, cutNormalCoordinate, occupiedCutProbe] <;>
    linarith
/-- At a clean rectangle corner, the two inward coordinate half-spaces are
selected explicitly. Their boundaries are the two perpendicular
`occupiedLeftCutTrace`s, and the rectangle interior is locally exactly their
intersection. -/
theorem exists_occupiedCutSides_at_closedCutRectangle_corner
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u)
    {p : PlanePoint}
    (hp : p ∈ ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint)) :
    ∃ verticalSide horizontalSide : SpliceGraphOccupiedSide,
      ∀ᶠ q in 𝓝 p,
        q ∈ interior (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied verticalSide
              (cutNormalCoordinate .vertical p q) ∧
            signedCoordinateOccupied horizontalSide
              (cutNormalCoordinate .horizontal p q) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with hp | hp | hp | hp
  · subst p
    refine ⟨.positive, .positive, ?_⟩
    filter_upwards
      [continuousAt_fst.eventually (Iio_mem_nhds hlr),
        continuousAt_snd.eventually (Iio_mem_nhds hdu)] with q hqr hqu
    rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
    simp only [Set.mem_prod, Set.mem_Ioo, signedCoordinateOccupied,
      cutNormalCoordinate]
    constructor
    · rintro ⟨⟨hql, _⟩, hqd, _⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hql, hqd⟩
      exact ⟨⟨by linarith, hqr⟩, ⟨by linarith, hqu⟩⟩
  · subst p
    refine ⟨.positive, .negative, ?_⟩
    filter_upwards
      [continuousAt_fst.eventually (Iio_mem_nhds hlr),
        continuousAt_snd.eventually (Ioi_mem_nhds hdu)] with q hqr hqd
    rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
    simp only [Set.mem_prod, Set.mem_Ioo, signedCoordinateOccupied,
      cutNormalCoordinate]
    constructor
    · rintro ⟨⟨hql, _⟩, _, hqu⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hql, hqu⟩
      exact ⟨⟨by linarith, hqr⟩, ⟨hqd, by linarith⟩⟩
  · subst p
    refine ⟨.negative, .positive, ?_⟩
    filter_upwards
      [continuousAt_fst.eventually (Ioi_mem_nhds hlr),
        continuousAt_snd.eventually (Iio_mem_nhds hdu)] with q hql hqu
    rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
    simp only [Set.mem_prod, Set.mem_Ioo, signedCoordinateOccupied,
      cutNormalCoordinate]
    constructor
    · rintro ⟨⟨_, hqr⟩, hqd, _⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hqr, hqd⟩
      exact ⟨⟨hql, by linarith⟩, ⟨by linarith, hqu⟩⟩
  · subst p
    refine ⟨.negative, .negative, ?_⟩
    filter_upwards
      [continuousAt_fst.eventually (Ioi_mem_nhds hlr),
        continuousAt_snd.eventually (Ioi_mem_nhds hdu)] with q hql hqd
    rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
    simp only [Set.mem_prod, Set.mem_Ioo, signedCoordinateOccupied,
      cutNormalCoordinate]
    constructor
    · rintro ⟨⟨_, hqr⟩, _, hqu⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hqr, hqu⟩
      exact ⟨⟨hql, by linarith⟩, ⟨hqd, by linarith⟩⟩



/-- Parameter value at which the occupied-left trace passes through its germ
base point. -/
def occupiedLeftBaseParameter (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (p : PlanePoint) : ℝ :=
  match axis, side with
  | .vertical, .negative => -p.1
  | .vertical, .positive => p.1
  | .horizontal, .negative => p.2
  | .horizontal, .positive => -p.2

/-- Endpoint-independent local regular trace extracted from one actual
oriented smooth boundary germ.  The exact local carrier model is retained, so
the direction is tied to the occupied source side rather than chosen from an
unoriented path. -/
structure OccupiedLeftRegularTrace (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (U : Set PlanePoint)
    (p : PlanePoint) where
  graph : ℝ → ℝ
  graph_contDiff : ContDiff ℝ ∞ graph
  trace_base :
    occupiedLeftGraphTrace axis side graph
      (occupiedLeftBaseParameter axis side p) = p
  carrier_eventually :
    ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ orientedGraphDomain axis side graph

namespace OccupiedLeftRegularTrace

variable {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}

/-- The extracted occupied-left graph trace is globally smooth. -/
theorem trace_contDiff (T : OccupiedLeftRegularTrace axis side U p) :
    ContDiff ℝ ∞ (occupiedLeftGraphTrace axis side T.graph) := by
  cases axis with
  | vertical =>
      cases side with
      | negative =>
          exact contDiff_id.neg.prodMk
            (T.graph_contDiff.comp contDiff_id.neg)
      | positive =>
          exact contDiff_id.prodMk T.graph_contDiff
  | horizontal =>
      cases side with
      | negative =>
          exact T.graph_contDiff.prodMk contDiff_id
      | positive =>
          exact (T.graph_contDiff.comp contDiff_id.neg).prodMk
            contDiff_id.neg

/-- Exact derivative of the extracted trace at every parameter. -/
theorem trace_hasDerivAt (T : OccupiedLeftRegularTrace axis side U p)
    (t : ℝ) :
    HasDerivAt (occupiedLeftGraphTrace axis side T.graph)
      (occupiedLeftGraphVelocity axis side T.graph t) t := by
  cases axis with
  | vertical =>
      cases side with
      | negative =>
          change HasDerivAt (fun s : ℝ => ((-s, T.graph (-s)) : PlanePoint))
            (-1, -deriv T.graph (-t)) t
          have hneg := (hasDerivAt_id t).neg
          have hgraph : HasDerivAt T.graph (deriv T.graph (-t)) (-t) :=
            (T.graph_contDiff.differentiable (by simp) (-t)).hasDerivAt
          convert hneg.prodMk (hgraph.comp t hneg) using 1 <;>
            simp [Pi.neg_apply, id_eq]
      | positive =>
          change HasDerivAt (fun s : ℝ => ((s, T.graph s) : PlanePoint))
            (1, deriv T.graph t) t
          simpa only [id_eq] using
            (hasDerivAt_id t).prodMk
              (T.graph_contDiff.differentiable (by simp) t).hasDerivAt
  | horizontal =>
      cases side with
      | negative =>
          change HasDerivAt (fun s : ℝ => ((T.graph s, s) : PlanePoint))
            (deriv T.graph t, 1) t
          simpa only [id_eq] using
            (T.graph_contDiff.differentiable (by simp) t).hasDerivAt.prodMk
              (hasDerivAt_id t)
      | positive =>
          change HasDerivAt (fun s : ℝ => ((T.graph (-s), -s) : PlanePoint))
            (-deriv T.graph (-t), -1) t
          have hneg := (hasDerivAt_id t).neg
          have hgraph : HasDerivAt T.graph (deriv T.graph (-t)) (-t) :=
            (T.graph_contDiff.differentiable (by simp) (-t)).hasDerivAt
          convert (hgraph.comp t hneg).prodMk hneg using 1 <;>
            simp [Pi.neg_apply, id_eq]

/-- The explicit trace velocity never vanishes, including at the germ base
parameter.  One coordinate is always exactly `1` or `-1`. -/
theorem velocity_ne_zero (T : OccupiedLeftRegularTrace axis side U p)
    (t : ℝ) :
    occupiedLeftGraphVelocity axis side T.graph t ≠ 0 := by
  cases axis <;> cases side <;>
    simp [occupiedLeftGraphVelocity]

/-- The occupied-side probe is strictly to the left of the chosen velocity.
The determinant is exactly one, independently of the graph slope. -/
theorem planarDet_velocity_probe (T : OccupiedLeftRegularTrace axis side U p)
    (t : ℝ) :
    planarDet (occupiedLeftGraphVelocity axis side T.graph t)
      (occupiedGraphProbe axis side) = 1 := by
  cases axis <;> cases side <;>
    simp [planarDet, occupiedLeftGraphVelocity, occupiedGraphProbe]
/-- Reversing a graph parameter never introduces multiplicity: one coordinate
of the occupied-left trace is `t` or `-t`. -/
theorem trace_injective (T : OccupiedLeftRegularTrace axis side U p) :
    Function.Injective (occupiedLeftGraphTrace axis side T.graph) := by
  intro s t hst
  cases axis with
  | vertical =>
      cases side with
      | negative =>
          have h := congrArg Prod.fst hst
          simpa only [occupiedLeftGraphTrace, neg_inj] using h
      | positive =>
          exact congrArg Prod.fst hst
  | horizontal =>
      cases side with
      | negative =>
          exact congrArg Prod.snd hst
      | positive =>
          have h := congrArg Prod.snd hst
          simpa only [occupiedLeftGraphTrace, neg_inj] using h


/-- Every parameter has a genuine nonzero derivative, packaged in the form
used by piecewise-regular trace consumers. -/
theorem trace_regular (T : OccupiedLeftRegularTrace axis side U p)
    (t : ℝ) :
    ∃ velocity : PlanePoint,
      HasDerivAt (occupiedLeftGraphTrace axis side T.graph) velocity t ∧
        velocity ≠ 0 :=
  ⟨occupiedLeftGraphVelocity axis side T.graph t,
    T.trace_hasDerivAt t, T.velocity_ne_zero t⟩

/-- On every compact parameter interval the extracted trace is `C¹`. -/
theorem trace_contDiffOn_Icc (T : OccupiedLeftRegularTrace axis side U p)
    (a b : ℝ) :
    ContDiffOn ℝ 1 (occupiedLeftGraphTrace axis side T.graph) (Icc a b) :=
  (T.trace_contDiff.of_le (by simp)).contDiffOn

/-- Each compact restriction has one finite Lipschitz constant. -/
theorem exists_lipschitzOnWith_Icc
    (T : OccupiedLeftRegularTrace axis side U p) (a b : ℝ) :
    ∃ K : NNReal,
      LipschitzOnWith K (occupiedLeftGraphTrace axis side T.graph) (Icc a b) := by
  exact (T.trace_contDiffOn_Icc a b).exists_lipschitzOnWith
    (by decide) (convex_Icc _ _) isCompact_Icc

end OccupiedLeftRegularTrace

/-- Construct the explicit occupied-left regular trace from the retained
source-local smooth graph germ. -/
theorem HasOrientedSmoothBoundaryGraphGermOnSide.toOccupiedLeftRegularTrace
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide axis side U p) :
    Nonempty (OccupiedLeftRegularTrace axis side U p) := by
  obtain ⟨φ, hφ, hdata⟩ := germ.exists_eventually_occupiedGraphDomain
  refine ⟨{
    graph := φ
    graph_contDiff := hφ
    trace_base := ?_
    carrier_eventually := ?_
  }⟩
  · cases axis <;> cases side <;>
      simp only [occupiedLeftGraphTrace, occupiedLeftBaseParameter] at hdata ⊢
    · rw [neg_neg, hdata.1]
    · rw [hdata.1]
    · rw [hdata.1]
    · rw [neg_neg, hdata.1]
  · cases axis <;> cases side <;>
      simp only [orientedGraphDomain, mem_ofPred_eq]
    · exact hdata.2
    · exact hdata.2
    · exact hdata.2
    · exact hdata.2
/-- Both regular branches at a transverse source/cut endpoint, with their
actual occupied sides fixed. The source graph and the straight cut face extend
through the endpoint; `crop_eventually` records that these are the two local
boundary branches of the cropped carrier rather than unrelated traces. -/
structure OccupiedLeftTransverseEndpointTraces
    (O G : Set PlanePoint) (p : PlanePoint) where
  axis : SpliceCutAxis
  cutSide : SpliceGraphOccupiedSide
  graphSide : SpliceGraphOccupiedSide
  sourceTrace : OccupiedLeftRegularTrace axis graphSide G p
  crop_eventually : ∀ᶠ q in 𝓝 p,
    q ∈ O ↔
      signedCoordinateOccupied cutSide
          (cutNormalCoordinate axis p q) ∧
        q ∈ G

namespace OccupiedLeftTransverseEndpointTraces

/-- The source extension is globally smooth. -/
theorem source_contDiff
    (T : OccupiedLeftTransverseEndpointTraces O G p) :
    ContDiff ℝ ∞
      (occupiedLeftGraphTrace T.axis T.graphSide T.sourceTrace.graph) :=
  T.sourceTrace.trace_contDiff

/-- The source extension has no repeated parameter values. -/
theorem source_injective
    (T : OccupiedLeftTransverseEndpointTraces O G p) :
    Function.Injective
      (occupiedLeftGraphTrace T.axis T.graphSide T.sourceTrace.graph) :=
  T.sourceTrace.trace_injective

/-- The straight cut extension is globally smooth. -/
theorem cut_contDiff
    (T : OccupiedLeftTransverseEndpointTraces O G p) :
    ContDiff ℝ ∞ (occupiedLeftCutTrace T.axis T.cutSide p) :=
  occupiedLeftCutTrace_contDiff _ _ _

/-- The straight cut extension has no repeated parameter values. -/
theorem cut_injective
    (T : OccupiedLeftTransverseEndpointTraces O G p) :
    Function.Injective (occupiedLeftCutTrace T.axis T.cutSide p) :=
  occupiedLeftCutTrace_injective _ _ _
/-- Near the endpoint, the cropped carrier is exactly the intersection of the
selected cut half-space and selected smooth graph side. -/
theorem crop_eventually_eq_oriented_domains
    (T : OccupiedLeftTransverseEndpointTraces O G p) :
    ∀ᶠ q in 𝓝 p,
      q ∈ O ↔
        signedCoordinateOccupied T.cutSide
            (cutNormalCoordinate T.axis p q) ∧
          q ∈ orientedGraphDomain
            T.axis T.graphSide T.sourceTrace.graph := by
  filter_upwards
    [T.crop_eventually, T.sourceTrace.carrier_eventually] with q hcrop hsource
  rw [hcrop, hsource]


/-- The source branch is a globally smooth injective extension through the
endpoint with nowhere-vanishing velocity. -/
theorem source_regular
    (T : OccupiedLeftTransverseEndpointTraces O G p) (t : ℝ) :
    ∃ velocity : PlanePoint,
      HasDerivAt
          (occupiedLeftGraphTrace T.axis T.graphSide T.sourceTrace.graph)
          velocity t ∧
        velocity ≠ 0 :=
  T.sourceTrace.trace_regular t

/-- The cut branch is a globally smooth injective straight extension through
the same endpoint. -/
theorem cut_regular
    (T : OccupiedLeftTransverseEndpointTraces O G p) (t : ℝ) :
    HasDerivAt (occupiedLeftCutTrace T.axis T.cutSide p)
        (occupiedLeftCutVelocity T.axis T.cutSide) t ∧
      occupiedLeftCutVelocity T.axis T.cutSide ≠ 0 :=
  ⟨occupiedLeftCutTrace_hasDerivAt _ _ _ _,
    occupiedLeftCutVelocity_ne_zero _ _⟩

/-- Both selected velocities put their corresponding occupied probes strictly
on the left. -/
theorem oriented_determinants
    (T : OccupiedLeftTransverseEndpointTraces O G p) (t : ℝ) :
    planarDet
        (occupiedLeftGraphVelocity
          T.axis T.graphSide T.sourceTrace.graph t)
        (occupiedGraphProbe T.axis T.graphSide) = 1 ∧
      planarDet (occupiedLeftCutVelocity T.axis T.cutSide)
        (occupiedCutProbe T.axis T.cutSide) = 1 :=
  ⟨T.sourceTrace.planarDet_velocity_probe t,
    planarDet_occupiedLeftCutVelocity_probe _ _⟩

end OccupiedLeftTransverseEndpointTraces


end FiniteJunctionRepair
end CMVRelaxation

namespace CMVRelaxation

open CMVBoundaryLocalAtlas
open CMVBoundaryLocalAtlas.SmoothGraphAtlas
open FiniteJunctionRepair
/-- At every transverse noncorner source/cut junction, both actual boundary
branches have explicit smooth embedded extensions through the endpoint.  The
cut side is fixed by the selected rectangle face, the graph side by the source
domain, and their intersection locally reconstructs the cropped carrier. -/
theorem exists_occupiedLeftTransverseEndpointTraces_of_noncornerJunction
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
        Set _root_.PlanePoint)) :
    Nonempty (OccupiedLeftTransverseEndpointTraces
      (openSpliceIn ∅ G (closedCutRectangle l r d u)) G p) := by
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
  have verticalTrace
      (K : Set _root_.PlanePoint) (x : ℝ)
      (hreg : IsVerticalRegularBoundaryValue G K x)
      (hpK : p ∈ K) (hpLine : p ∈ verticalLine x) :
      ∃ side : SpliceGraphOccupiedSide,
        Nonempty (OccupiedLeftRegularTrace .vertical side G p) := by
    obtain ⟨g, φ, hg, htransverse, hφ, hφp, hlocal⟩ :=
      local_oriented_smooth_graph_of_vertical_regular
        hreg ⟨⟨hpG, hpK⟩, hpLine⟩
    rcases lt_or_gt_of_ne htransverse with hnegative | hpositive
    · refine ⟨.positive, ?_⟩
      exact (show HasOrientedSmoothBoundaryGraphGermOnSide
          .vertical .positive G p from
        ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hnegative⟩
        ).toOccupiedLeftRegularTrace
    · refine ⟨.negative, ?_⟩
      exact (show HasOrientedSmoothBoundaryGraphGermOnSide
          .vertical .negative G p from
        ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hpositive⟩
        ).toOccupiedLeftRegularTrace
  have horizontalTrace
      (K : Set _root_.PlanePoint) (y : ℝ)
      (hreg : IsHorizontalRegularBoundaryValue G K y)
      (hpK : p ∈ K) (hpLine : p ∈ horizontalLine y) :
      ∃ side : SpliceGraphOccupiedSide,
        Nonempty (OccupiedLeftRegularTrace .horizontal side G p) := by
    obtain ⟨g, φ, hg, htransverse, hφ, hφp, hlocal⟩ :=
      local_oriented_smooth_graph_of_horizontal_regular
        hreg ⟨⟨hpG, hpK⟩, hpLine⟩
    rcases lt_or_gt_of_ne htransverse with hnegative | hpositive
    · refine ⟨.positive, ?_⟩
      exact (show HasOrientedSmoothBoundaryGraphGermOnSide
          .horizontal .positive G p from
        ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hnegative⟩
        ).toOccupiedLeftRegularTrace
    · refine ⟨.negative, ?_⟩
      exact (show HasOrientedSmoothBoundaryGraphGermOnSide
          .horizontal .negative G p from
        ⟨g, φ, hg, htransverse, hφ, hφp, hlocal, hpositive⟩
        ).toOccupiedLeftRegularTrace
  rcases frontier_closedCutRectangle_subset_lines hlr hdu hpWindowFrontier with
    ((hpLeft | hpRight) | hpLower) | hpUpper
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
    obtain ⟨side, ⟨sourceTrace⟩⟩ :=
      verticalTrace _ l hL.2.1 hpK hpLeft
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .positive
              (cutNormalCoordinate .vertical p q) ∧
            q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Iio_mem_nhds (by simpa [hpX] using hlr)),
          continuousAt_snd.eventually
            (Ioo_mem_nhds hpY.1 hpY.2)] with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied, cutNormalCoordinate]
      constructor
      · rintro ⟨hqG, ⟨hql, _hqr⟩, _hqd, _hqu⟩
        exact ⟨by simpa only [hpX, sub_pos] using hql, hqG⟩
      · rintro ⟨hql, hqG⟩
        exact ⟨hqG, ⟨⟨by simpa only [hpX, sub_pos] using hql, hqx⟩,
          hqy⟩⟩
    exact ⟨{
      axis := .vertical
      cutSide := .positive
      graphSide := side
      sourceTrace := sourceTrace
      crop_eventually := hcut
    }⟩
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
    obtain ⟨side, ⟨sourceTrace⟩⟩ :=
      verticalTrace _ r hR.2.1 hpK hpRight
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .negative
              (cutNormalCoordinate .vertical p q) ∧
            q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Ioi_mem_nhds (by simpa [hpX] using hlr)),
          continuousAt_snd.eventually
            (Ioo_mem_nhds hpY.1 hpY.2)] with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied, cutNormalCoordinate]
      constructor
      · rintro ⟨hqG, ⟨_hql, hqr⟩, _hqd, _hqu⟩
        exact ⟨by simpa only [hpX, sub_neg] using hqr, hqG⟩
      · rintro ⟨hqr, hqG⟩
        exact ⟨hqG, ⟨⟨hqx,
          by simpa only [hpX, sub_neg] using hqr⟩, hqy⟩⟩
    exact ⟨{
      axis := .vertical
      cutSide := .negative
      graphSide := side
      sourceTrace := sourceTrace
      crop_eventually := hcut
    }⟩
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
    obtain ⟨side, ⟨sourceTrace⟩⟩ :=
      horizontalTrace _ d hD.2.1 hpK hpLower
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .positive
              (cutNormalCoordinate .horizontal p q) ∧
            q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Ioo_mem_nhds hpX.1 hpX.2),
          continuousAt_snd.eventually
            (Iio_mem_nhds (by simpa [hpY] using hdu))] with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied, cutNormalCoordinate]
      constructor
      · rintro ⟨hqG, ⟨_hql, _hqr⟩, hqd, _hqu⟩
        exact ⟨by simpa only [hpY, sub_pos] using hqd, hqG⟩
      · rintro ⟨hqd, hqG⟩
        exact ⟨hqG, ⟨hqx, ⟨by simpa only [hpY, sub_pos] using hqd,
          hqy⟩⟩⟩
    exact ⟨{
      axis := .horizontal
      cutSide := .positive
      graphSide := side
      sourceTrace := sourceTrace
      crop_eventually := hcut
    }⟩
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
    obtain ⟨side, ⟨sourceTrace⟩⟩ :=
      horizontalTrace _ u hU.2.1 hpK hpUpper
    have hcut : ∀ᶠ q in 𝓝 p,
        q ∈ openSpliceIn ∅ G (closedCutRectangle l r d u) ↔
          signedCoordinateOccupied .negative
              (cutNormalCoordinate .horizontal p q) ∧
            q ∈ G := by
      filter_upwards
        [continuousAt_fst.eventually (Ioo_mem_nhds hpX.1 hpX.2),
          continuousAt_snd.eventually
            (Ioi_mem_nhds (by simpa [hpY] using hdu))] with q hqx hqy
      rw [hcrop, hwindowInterior]
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo,
        signedCoordinateOccupied, cutNormalCoordinate]
      constructor
      · rintro ⟨hqG, ⟨_hql, _hqr⟩, _hqd, hqu⟩
        exact ⟨by simpa only [hpY, sub_neg] using hqu, hqG⟩
      · rintro ⟨hqu, hqG⟩
        exact ⟨hqG, ⟨hqx, ⟨hqy,
          by simpa only [hpY, sub_neg] using hqu⟩⟩⟩
    exact ⟨{
      axis := .horizontal
      cutSide := .negative
      graphSide := side
      sourceTrace := sourceTrace
      crop_eventually := hcut
    }⟩


variable {O : Set _root_.PlanePoint}

/-- Every ordinary frontier point outside the retained finite exceptional set
has an explicit occupied-left regular trace. This includes artificial
chart-cut endpoints, not only points in open quotient arcs. -/
theorem FinitePiecewiseRegularBoundaryTopology.exists_regularTrace_away_exceptionalPoints
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (p : FrontierSpace O) (hp : p.1 ∉ T.exceptionalPoints) :
    ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
      Nonempty (OccupiedLeftRegularTrace axis side O p.1) := by
  obtain ⟨axis, side, germ⟩ :=
    T.smooth_away_exceptionalPoints p hp
  exact ⟨axis, side, germ.toOccupiedLeftRegularTrace⟩

/-- Every actual interior point of every refined compact arc inherits the
ordinary-point occupied-left trace. Exceptional points are cuts and therefore
cannot lie in an open quotient arc. -/
theorem FinitePiecewiseRegularBoundaryTopology.exists_occupiedLeftRegularTrace
    (T : FinitePiecewiseRegularBoundaryTopology O)
    (e : T.chartCuts.ArcIndex) {p : FrontierSpace O}
    (hp : p ∈ T.chartCuts.finiteArcInterior e) :
    ∃ axis : SpliceCutAxis, ∃ side : SpliceGraphOccupiedSide,
      Nonempty (OccupiedLeftRegularTrace axis side O p.1) := by
  apply T.exists_regularTrace_away_exceptionalPoints p
  intro hpExceptional
  exact (T.chartCuts.finiteArcInterior_subset_cutSpaceCarrier e hp)
    (T.exceptionalPoints_subset_cutPoints p hpExceptional)

end CMVRelaxation
