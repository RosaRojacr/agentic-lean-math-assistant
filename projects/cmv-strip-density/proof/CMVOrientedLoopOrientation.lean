import CMVOrientedLoopSmoothTrace
import CMVOrientedLoopPathRealization

/-!
# Occupied-left orientation coherence

Occupied-left smooth germs at one frontier point determine the same oriented
tangent ray.  Positive local transition parameters make their direction in a
fixed finite-arc coordinate locally constant; connectedness propagates that
direction across the complete open arc.  Endpoint switching remains an
explicit separate condition because exceptional cut vertices need not retain
a smooth germ in the generic topology.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteJunctionRepair

/-- The graph retained by an occupied-left trace passes through its base point,
in either coordinate chart and for either occupied-side convention. -/
theorem OccupiedLeftRegularTrace.graph_eq_base
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p) :
    match axis with
    | .vertical => T.graph p.1 = p.2
    | .horizontal => T.graph p.2 = p.1 := by
  cases axis <;> cases side <;>
    have h := congrArg Prod.snd T.trace_base <;>
    try { simpa [occupiedLeftGraphTrace, occupiedLeftBaseParameter] using h }
  all_goals
    have h := congrArg Prod.fst T.trace_base
    simpa [occupiedLeftGraphTrace, occupiedLeftBaseParameter] using h

/-- The complete frontier of a strict oriented graph domain is its graph.
This exact equality, rather than only `frontier_lt_subset_eq`, is needed to
transport a trace through a second local carrier model. -/
theorem frontier_orientedGraphDomain
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (φ : ℝ → ℝ) (hφ : Continuous φ) :
    frontier (orientedGraphDomain axis side φ) =
      match axis with
      | .vertical => {q : PlanePoint | φ q.1 = q.2}
      | .horizontal => {q : PlanePoint | φ q.2 = q.1} := by
  cases axis with
  | vertical =>
      let H :=
        CMVBoundaryLocalAtlas.SmoothGraphAtlas.verticalGraphFlattening φ hφ 0
      cases side with
      | negative =>
          have hdomain :
              orientedGraphDomain .vertical .negative φ =
                H ⁻¹' CMVBoundaryLocalAtlas.OccupiedHalfPlane.lower.carrier := by
            ext q
            simp [orientedGraphDomain, H,
              CMVBoundaryLocalAtlas.OccupiedHalfPlane.carrier,
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.verticalGraphFlattening_apply]
          rw [hdomain, ← H.preimage_frontier,
            CMVBoundaryLocalAtlas.OccupiedHalfPlane.frontier_carrier]
          ext q
          simp [CMVBoundaryLocalAtlas.OccupiedHalfPlane.axis, H,
            CMVBoundaryLocalAtlas.SmoothGraphAtlas.verticalGraphFlattening_apply,
            sub_eq_zero, eq_comm]
      | positive =>
          have hdomain :
              orientedGraphDomain .vertical .positive φ =
                H ⁻¹' CMVBoundaryLocalAtlas.OccupiedHalfPlane.upper.carrier := by
            ext q
            simp [orientedGraphDomain, H,
              CMVBoundaryLocalAtlas.OccupiedHalfPlane.carrier,
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.verticalGraphFlattening_apply]
          rw [hdomain, ← H.preimage_frontier,
            CMVBoundaryLocalAtlas.OccupiedHalfPlane.frontier_carrier]
          ext q
          simp [CMVBoundaryLocalAtlas.OccupiedHalfPlane.axis, H,
            CMVBoundaryLocalAtlas.SmoothGraphAtlas.verticalGraphFlattening_apply,
            sub_eq_zero, eq_comm]
  | horizontal =>
      let H :=
        CMVBoundaryLocalAtlas.SmoothGraphAtlas.horizontalGraphFlattening φ hφ 0
      cases side with
      | negative =>
          have hdomain :
              orientedGraphDomain .horizontal .negative φ =
                H ⁻¹' CMVBoundaryLocalAtlas.OccupiedHalfPlane.lower.carrier := by
            ext q
            simp [orientedGraphDomain, H,
              CMVBoundaryLocalAtlas.OccupiedHalfPlane.carrier,
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.horizontalGraphFlattening_apply]
          rw [hdomain, ← H.preimage_frontier,
            CMVBoundaryLocalAtlas.OccupiedHalfPlane.frontier_carrier]
          ext q
          simp [CMVBoundaryLocalAtlas.OccupiedHalfPlane.axis, H,
            CMVBoundaryLocalAtlas.SmoothGraphAtlas.horizontalGraphFlattening_apply,
            sub_eq_zero, eq_comm]
      | positive =>
          have hdomain :
              orientedGraphDomain .horizontal .positive φ =
                H ⁻¹' CMVBoundaryLocalAtlas.OccupiedHalfPlane.upper.carrier := by
            ext q
            simp [orientedGraphDomain, H,
              CMVBoundaryLocalAtlas.OccupiedHalfPlane.carrier,
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.horizontalGraphFlattening_apply]
          rw [hdomain, ← H.preimage_frontier,
            CMVBoundaryLocalAtlas.OccupiedHalfPlane.frontier_carrier]
          ext q
          simp [CMVBoundaryLocalAtlas.OccupiedHalfPlane.axis, H,
            CMVBoundaryLocalAtlas.SmoothGraphAtlas.horizontalGraphFlattening_apply,
            sub_eq_zero, eq_comm]

/-- On one neighborhood of the base point, the actual frontier and the graph
frontier retained by an occupied-left trace agree pointwise. -/
theorem OccupiedLeftRegularTrace.frontier_eventually
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p) :
    ∀ᶠ q in 𝓝 p,
      q ∈ frontier U ↔ q ∈ frontier (orientedGraphDomain axis side T.graph) := by
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp T.carrier_eventually
  have hlocal :
      U ∩ W = orientedGraphDomain axis side T.graph ∩ W := by
    ext q
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hqU, hqW⟩
      exact ⟨(hWsub hqW).mp hqU, hqW⟩
    · rintro ⟨hqModel, hqW⟩
      exact ⟨(hWsub hqW).mpr hqModel, hqW⟩
  have hfrontier :=
    frontier_inter_eq_of_inter_open_eq hWopen hlocal
  filter_upwards [hWopen.mem_nhds hpW] with q hqW
  have hq := Set.ext_iff.mp hfrontier q
  simpa only [mem_inter_iff, hqW, and_true] using hq

/-- A vertical and a horizontal occupied-left germ at the same actual frontier
point are local inverse graph parametrizations. -/
theorem OccupiedLeftRegularTrace.crossAxis_inverse_eventually
    {sideV sideH : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace .vertical sideV U p)
    (S : OccupiedLeftRegularTrace .horizontal sideH U p) :
    (fun x => S.graph (T.graph x)) =ᶠ[𝓝 p.1] fun x => x := by
  let q : ℝ → PlanePoint := fun x => (x, T.graph x)
  have hqp : q p.1 = p := by
    apply Prod.ext
    · rfl
    · exact T.graph_eq_base
  have hqTendsto : Tendsto q (𝓝 p.1) (𝓝 p) := by
    rw [← hqp]
    exact continuousAt_id.prodMk T.graph_contDiff.continuous.continuousAt
  have hTfrontier := hqTendsto.eventually T.frontier_eventually
  have hSfrontier := hqTendsto.eventually S.frontier_eventually
  filter_upwards [hTfrontier, hSfrontier] with x hT hS
  have hqTmodel :
      q x ∈ frontier (orientedGraphDomain .vertical sideV T.graph) := by
    rw [frontier_orientedGraphDomain _ _ _ T.graph_contDiff.continuous]
    exact rfl
  have hqU : q x ∈ frontier U := hT.mpr hqTmodel
  have hqSmodel :
      q x ∈ frontier (orientedGraphDomain .horizontal sideH S.graph) :=
    hS.mp hqU
  rw [frontier_orientedGraphDomain _ _ _ S.graph_contDiff.continuous] at hqSmodel
  exact hqSmodel

/-- Transition derivatives between vertical and horizontal boundary charts are
reciprocal.  In particular, neither chart can be singular at the overlap. -/
theorem OccupiedLeftRegularTrace.crossAxis_deriv_mul
    {sideV sideH : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace .vertical sideV U p)
    (S : OccupiedLeftRegularTrace .horizontal sideH U p) :
    deriv S.graph p.2 * deriv T.graph p.1 = 1 := by
  have hT :
      HasDerivAt T.graph (deriv T.graph p.1) p.1 :=
    (T.graph_contDiff.differentiable (by simp) p.1).hasDerivAt
  have hS :
      HasDerivAt S.graph (deriv S.graph p.2) p.2 :=
    (S.graph_contDiff.differentiable (by simp) p.2).hasDerivAt
  have hS' :
      HasDerivAt S.graph (deriv S.graph p.2) (T.graph p.1) := by
    rw [T.graph_eq_base]
    exact hS
  have hcomp :
      HasDerivAt (fun x => S.graph (T.graph x))
        (deriv S.graph p.2 * deriv T.graph p.1) p.1 :=
    hS'.comp p.1 hT
  calc
    deriv S.graph p.2 * deriv T.graph p.1 =
        deriv (fun x => S.graph (T.graph x)) p.1 := hcomp.deriv.symm
    _ = deriv id p.1 := (T.crossAxis_inverse_eventually S).deriv_eq
    _ = 1 := (hasDerivAt_id p.1).deriv

private theorem deriv_nonneg_of_eventually_ge_right
    {f : ℝ → ℝ} {x f' : ℝ} (hf : HasDerivAt f f' x)
    (hmono : ∀ᶠ y in 𝓝[>] x, f x ≤ f y) :
    0 ≤ f' := by
  apply ge_of_tendsto
    (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
  filter_upwards [self_mem_nhdsWithin, hmono] with y hy hfy
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr hfy) (sub_nonneg.mpr hy.le)

private theorem deriv_nonpos_of_eventually_le_right
    {f : ℝ → ℝ} {x f' : ℝ} (hf : HasDerivAt f f' x)
    (hmono : ∀ᶠ y in 𝓝[>] x, f y ≤ f x) :
    f' ≤ 0 := by
  apply le_of_tendsto
    (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
  filter_upwards [self_mem_nhdsWithin, hmono] with y hy hfy
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hfy) (sub_nonneg.mpr hy.le)

/-- The side labels determine the one-sided monotonicity of a horizontal graph
when it overlaps a vertical graph for the same actual occupied set. -/
theorem OccupiedLeftRegularTrace.crossAxis_horizontal_graph_right
    {sideV sideH : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace .vertical sideV U p)
    (S : OccupiedLeftRegularTrace .horizontal sideH U p) :
    ∀ᶠ y in 𝓝[>] p.2,
      match sideV, sideH with
      | .negative, .negative => S.graph y ≤ S.graph p.2
      | .negative, .positive => S.graph p.2 ≤ S.graph y
      | .positive, .negative => S.graph p.2 ≤ S.graph y
      | .positive, .positive => S.graph y ≤ S.graph p.2 := by
  cases sideV <;> cases sideH <;>
    let q : ℝ → PlanePoint := fun y => (p.1, y)
  all_goals
    have hqTendsto : Tendsto q (𝓝 p.2) (𝓝 p) := by
      have hqp : q p.2 = p := rfl
      rw [← hqp]
      exact continuousAt_const.prodMk continuousAt_id
    have hmodels := hqTendsto.eventually
      (T.carrier_eventually.and S.carrier_eventually)
    have hmodelsRight :
        ∀ᶠ y in 𝓝[>] p.2,
          (q y ∈ U ↔ q y ∈
            orientedGraphDomain .vertical _ T.graph) ∧
          (q y ∈ U ↔ q y ∈
            orientedGraphDomain .horizontal _ S.graph) :=
      hmodels.filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hmodelsRight] with y hy hmodelsAt
  · have hiff : y < p.2 ↔ p.1 < S.graph y := by
      simpa [q, orientedGraphDomain, T.graph_eq_base] using
        hmodelsAt.1.symm.trans hmodelsAt.2
    rw [S.graph_eq_base]
    exact le_of_not_gt fun h =>
      (not_lt_of_ge hy.le) (hiff.mpr h)
  · have hiff : y < p.2 ↔ S.graph y < p.1 := by
      simpa [q, orientedGraphDomain, T.graph_eq_base] using
        hmodelsAt.1.symm.trans hmodelsAt.2
    rw [S.graph_eq_base]
    exact le_of_not_gt fun h =>
      (not_lt_of_ge hy.le) (hiff.mpr h)
  · have hiff : p.2 < y ↔ p.1 < S.graph y := by
      simpa [q, orientedGraphDomain, T.graph_eq_base] using
        hmodelsAt.1.symm.trans hmodelsAt.2
    rw [S.graph_eq_base]
    exact (hiff.mp hy).le
  · have hiff : p.2 < y ↔ S.graph y < p.1 := by
      simpa [q, orientedGraphDomain, T.graph_eq_base] using
        hmodelsAt.1.symm.trans hmodelsAt.2
    rw [S.graph_eq_base]
    exact (hiff.mp hy).le

/-- Cross-axis occupied-left charts have the derivative sign forced by their
two occupied-side labels.  Strictness follows from reciprocal derivatives. -/
theorem OccupiedLeftRegularTrace.crossAxis_horizontal_deriv_sign
    {sideV sideH : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace .vertical sideV U p)
    (S : OccupiedLeftRegularTrace .horizontal sideH U p) :
    match sideV, sideH with
    | .negative, .negative => deriv S.graph p.2 < 0
    | .negative, .positive => 0 < deriv S.graph p.2
    | .positive, .negative => 0 < deriv S.graph p.2
    | .positive, .positive => deriv S.graph p.2 < 0 := by
  have hS :
      HasDerivAt S.graph (deriv S.graph p.2) p.2 :=
    (S.graph_contDiff.differentiable (by simp) p.2).hasDerivAt
  have hne : deriv S.graph p.2 ≠ 0 := by
    intro hzero
    have hmul := T.crossAxis_deriv_mul S
    rw [hzero, zero_mul] at hmul
    exact zero_ne_one hmul
  cases sideV <;> cases sideH
  · exact lt_of_le_of_ne
      (deriv_nonpos_of_eventually_le_right hS
        (T.crossAxis_horizontal_graph_right S)) hne
  · exact lt_of_le_of_ne
      (deriv_nonneg_of_eventually_ge_right hS
        (T.crossAxis_horizontal_graph_right S)) hne.symm
  · exact lt_of_le_of_ne
      (deriv_nonneg_of_eventually_ge_right hS
        (T.crossAxis_horizontal_graph_right S)) hne.symm
  · exact lt_of_le_of_ne
      (deriv_nonpos_of_eventually_le_right hS
        (T.crossAxis_horizontal_graph_right S)) hne

/-- Any vertical and horizontal occupied-left velocities for the same frontier
germ differ by a positive scalar.  Thus the occupied-left orientation is
independent of both chart axis and side encoding. -/
theorem OccupiedLeftRegularTrace.crossAxis_velocity_positive_smul
    {sideV sideH : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace .vertical sideV U p)
    (S : OccupiedLeftRegularTrace .horizontal sideH U p) :
    ∃ c : ℝ, 0 < c ∧
      occupiedLeftGraphVelocity .horizontal sideH S.graph
          (occupiedLeftBaseParameter .horizontal sideH p) =
        c • occupiedLeftGraphVelocity .vertical sideV T.graph
          (occupiedLeftBaseParameter .vertical sideV p) := by
  have hmul := T.crossAxis_deriv_mul S
  have hsign := T.crossAxis_horizontal_deriv_sign S
  cases sideV <;> cases sideH
  · refine ⟨-deriv S.graph p.2, neg_pos.mpr hsign, ?_⟩
    ext <;> simp [occupiedLeftGraphVelocity, occupiedLeftBaseParameter]
    nlinarith
  · refine ⟨deriv S.graph p.2, hsign, ?_⟩
    ext <;> simp [occupiedLeftGraphVelocity, occupiedLeftBaseParameter]
    nlinarith
  · refine ⟨deriv S.graph p.2, hsign, ?_⟩
    ext <;> simp [occupiedLeftGraphVelocity, occupiedLeftBaseParameter]
    nlinarith
  · refine ⟨-deriv S.graph p.2, neg_pos.mpr hsign, ?_⟩
    ext <;> simp [occupiedLeftGraphVelocity, occupiedLeftBaseParameter]
    nlinarith

/-- Two occupied-left germs with the same axis and side have the same graph on
one neighborhood of the base coordinate.  This is derived from their two
literal local carrier identities by testing the midpoint of the graph values. -/
theorem OccupiedLeftRegularTrace.eventuallyEq_graph
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T S : OccupiedLeftRegularTrace axis side U p) :
    match axis with
    | .vertical => T.graph =ᶠ[𝓝 p.1] S.graph
    | .horizontal => T.graph =ᶠ[𝓝 p.2] S.graph := by
  cases axis with
  | vertical =>
      have hTp : T.graph p.1 = p.2 := T.graph_eq_base
      have hSp : S.graph p.1 = p.2 := S.graph_eq_base
      let q : ℝ → PlanePoint := fun x =>
        (x, (T.graph x + S.graph x) / 2)
      have hqContinuous : Continuous q := by
        exact continuous_id.prodMk
          ((T.graph_contDiff.continuous.add S.graph_contDiff.continuous).div_const 2)
      have hqp : q p.1 = p := by
        apply Prod.ext
        · rfl
        · dsimp only [q]
          rw [hTp, hSp]
          ring
      have hqTendsto : Tendsto q (𝓝 p.1) (𝓝 p) := by
        rw [← hqp]
        exact hqContinuous.continuousAt
      have hmodels := hqTendsto.eventually
        (T.carrier_eventually.and S.carrier_eventually)
      filter_upwards [hmodels] with x hx
      have hdomain :
          q x ∈ orientedGraphDomain .vertical side T.graph ↔
            q x ∈ orientedGraphDomain .vertical side S.graph :=
        hx.1.symm.trans hx.2
      cases side with
      | negative =>
          simp only [q, orientedGraphDomain, mem_ofPred_eq] at hdomain
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hmidS :
                (T.graph x + S.graph x) / 2 < S.graph x := by linarith
            have hmidT := hdomain.mpr hmidS
            linarith
          · have hmidT :
                (T.graph x + S.graph x) / 2 < T.graph x := by linarith
            have hmidS := hdomain.mp hmidT
            linarith
      | positive =>
          simp only [q, orientedGraphDomain, mem_ofPred_eq] at hdomain
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hTmid :
                T.graph x < (T.graph x + S.graph x) / 2 := by linarith
            have hSmid := hdomain.mp hTmid
            linarith
          · have hSmid :
                S.graph x < (T.graph x + S.graph x) / 2 := by linarith
            have hTmid := hdomain.mpr hSmid
            linarith
  | horizontal =>
      have hTp : T.graph p.2 = p.1 := T.graph_eq_base
      have hSp : S.graph p.2 = p.1 := S.graph_eq_base
      let q : ℝ → PlanePoint := fun y =>
        ((T.graph y + S.graph y) / 2, y)
      have hqContinuous : Continuous q := by
        exact
          ((T.graph_contDiff.continuous.add S.graph_contDiff.continuous).div_const 2).prodMk
            continuous_id
      have hqp : q p.2 = p := by
        apply Prod.ext
        · dsimp only [q]
          rw [hTp, hSp]
          ring
        · rfl
      have hqTendsto : Tendsto q (𝓝 p.2) (𝓝 p) := by
        rw [← hqp]
        exact hqContinuous.continuousAt
      have hmodels := hqTendsto.eventually
        (T.carrier_eventually.and S.carrier_eventually)
      filter_upwards [hmodels] with y hy
      have hdomain :
          q y ∈ orientedGraphDomain .horizontal side T.graph ↔
            q y ∈ orientedGraphDomain .horizontal side S.graph :=
        hy.1.symm.trans hy.2
      cases side with
      | negative =>
          simp only [q, orientedGraphDomain, mem_ofPred_eq] at hdomain
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hmidS :
                (T.graph y + S.graph y) / 2 < S.graph y := by linarith
            have hmidT := hdomain.mpr hmidS
            linarith
          · have hmidT :
                (T.graph y + S.graph y) / 2 < T.graph y := by linarith
            have hmidS := hdomain.mp hmidT
            linarith
      | positive =>
          simp only [q, orientedGraphDomain, mem_ofPred_eq] at hdomain
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have hTmid :
                T.graph y < (T.graph y + S.graph y) / 2 := by linarith
            have hSmid := hdomain.mp hTmid
            linarith
          · have hSmid :
                S.graph y < (T.graph y + S.graph y) / 2 := by linarith
            have hTmid := hdomain.mpr hSmid
            linarith

/-- Same-axis, same-side occupied-left germs induce exactly the same tangent
velocity at their common base point. -/
theorem OccupiedLeftRegularTrace.velocity_eq
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T S : OccupiedLeftRegularTrace axis side U p) :
    occupiedLeftGraphVelocity axis side T.graph
        (occupiedLeftBaseParameter axis side p) =
      occupiedLeftGraphVelocity axis side S.graph
        (occupiedLeftBaseParameter axis side p) := by
  have hgraph := T.eventuallyEq_graph S
  cases axis <;> cases side <;>
    simp only [occupiedLeftGraphVelocity, occupiedLeftBaseParameter,
      neg_neg]
  all_goals
    rw [hgraph.deriv_eq]

/-- Two truthful graph germs for the same carrier and base point cannot assign
opposite occupied sides while using the same coordinate axis. -/
theorem OccupiedLeftRegularTrace.side_eq
    {axis : SpliceCutAxis} {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis side' U p) :
    side = side' := by
  cases axis with
  | vertical =>
      have hTp : T.graph p.1 = p.2 := T.graph_eq_base
      have hSp : S.graph p.1 = p.2 := S.graph_eq_base
      let q : ℝ → PlanePoint := fun y => (p.1, y)
      have hqTendsto : Tendsto q (𝓝 p.2) (𝓝 p) := by
        have hq : q p.2 = p := rfl
        rw [← hq]
        exact (continuous_const.prodMk continuous_id).continuousAt
      have hmodels := hqTendsto.eventually
        (T.carrier_eventually.and S.carrier_eventually)
      cases side <;> cases side'
      · rfl
      · exfalso
        have hright : ∀ᶠ y in 𝓝[Ioi p.2] p.2,
            y ∈ Ioi p.2 ∧
              ((q y ∈ orientedGraphDomain .vertical .negative T.graph) ↔
                q y ∈ orientedGraphDomain .vertical .positive S.graph) := by
          filter_upwards
            [self_mem_nhdsWithin,
              hmodels.filter_mono nhdsWithin_le_nhds] with y hy hmodel
          exact ⟨hy, hmodel.1.symm.trans hmodel.2⟩
        obtain ⟨y, hy, hdomain⟩ := hright.exists
        simp only [mem_Ioi] at hy
        simp only [q, orientedGraphDomain, mem_ofPred_eq, hTp, hSp] at hdomain
        exact (not_lt_of_ge hy.le) (hdomain.mpr hy)
      · exfalso
        have hright : ∀ᶠ y in 𝓝[Ioi p.2] p.2,
            y ∈ Ioi p.2 ∧
              ((q y ∈ orientedGraphDomain .vertical .positive T.graph) ↔
                q y ∈ orientedGraphDomain .vertical .negative S.graph) := by
          filter_upwards
            [self_mem_nhdsWithin,
              hmodels.filter_mono nhdsWithin_le_nhds] with y hy hmodel
          exact ⟨hy, hmodel.1.symm.trans hmodel.2⟩
        obtain ⟨y, hy, hdomain⟩ := hright.exists
        simp only [mem_Ioi] at hy
        simp only [q, orientedGraphDomain, mem_ofPred_eq, hTp, hSp] at hdomain
        exact (not_lt_of_ge hy.le) (hdomain.mp hy)
      · rfl
  | horizontal =>
      have hTp : T.graph p.2 = p.1 := T.graph_eq_base
      have hSp : S.graph p.2 = p.1 := S.graph_eq_base
      let q : ℝ → PlanePoint := fun x => (x, p.2)
      have hqTendsto : Tendsto q (𝓝 p.1) (𝓝 p) := by
        have hq : q p.1 = p := rfl
        rw [← hq]
        exact (continuous_id.prodMk continuous_const).continuousAt
      have hmodels := hqTendsto.eventually
        (T.carrier_eventually.and S.carrier_eventually)
      cases side <;> cases side'
      · rfl
      · exfalso
        have hright : ∀ᶠ x in 𝓝[Ioi p.1] p.1,
            x ∈ Ioi p.1 ∧
              ((q x ∈ orientedGraphDomain .horizontal .negative T.graph) ↔
                q x ∈ orientedGraphDomain .horizontal .positive S.graph) := by
          filter_upwards
            [self_mem_nhdsWithin,
              hmodels.filter_mono nhdsWithin_le_nhds] with x hx hmodel
          exact ⟨hx, hmodel.1.symm.trans hmodel.2⟩
        obtain ⟨x, hx, hdomain⟩ := hright.exists
        simp only [mem_Ioi] at hx
        simp only [q, orientedGraphDomain, mem_ofPred_eq, hTp, hSp] at hdomain
        exact (not_lt_of_ge hx.le) (hdomain.mpr hx)
      · exfalso
        have hright : ∀ᶠ x in 𝓝[Ioi p.1] p.1,
            x ∈ Ioi p.1 ∧
              ((q x ∈ orientedGraphDomain .horizontal .positive T.graph) ↔
                q x ∈ orientedGraphDomain .horizontal .negative S.graph) := by
          filter_upwards
            [self_mem_nhdsWithin,
              hmodels.filter_mono nhdsWithin_le_nhds] with x hx hmodel
          exact ⟨hx, hmodel.1.symm.trans hmodel.2⟩
        obtain ⟨x, hx, hdomain⟩ := hright.exists
        simp only [mem_Ioi] at hx
        simp only [q, orientedGraphDomain, mem_ofPred_eq, hTp, hSp] at hdomain
        exact (not_lt_of_ge hx.le) (hdomain.mp hx)
      · rfl

/-- Consequently the same-axis occupied-left velocity is independent of every
choice made when extracting the local graph germ. -/
theorem OccupiedLeftRegularTrace.velocity_eq_of_same_axis
    {axis : SpliceCutAxis} {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis side' U p) :
    occupiedLeftGraphVelocity axis side T.graph
        (occupiedLeftBaseParameter axis side p) =
      occupiedLeftGraphVelocity axis side' S.graph
        (occupiedLeftBaseParameter axis side' p) := by
  have hside := T.side_eq S
  subst side'
  exact T.velocity_eq S


/-- Occupied-left velocities from arbitrary graph-axis choices at one actual
frontier point determine the same oriented tangent ray. -/
theorem OccupiedLeftRegularTrace.velocity_positive_smul
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) :
    ∃ c : ℝ, 0 < c ∧
      occupiedLeftGraphVelocity axis' side' S.graph
          (occupiedLeftBaseParameter axis' side' p) =
        c • occupiedLeftGraphVelocity axis side T.graph
          (occupiedLeftBaseParameter axis side p) := by
  cases axis with
  | vertical =>
      cases axis' with
      | vertical =>
          refine ⟨1, zero_lt_one, ?_⟩
          simpa only [one_smul] using (T.velocity_eq_of_same_axis S).symm
      | horizontal =>
          exact T.crossAxis_velocity_positive_smul S
  | horizontal =>
      cases axis' with
      | vertical =>
          obtain ⟨c, hc, hvelocity⟩ :=
            S.crossAxis_velocity_positive_smul T
          refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
          rw [hvelocity, ← mul_smul]
          simp only [inv_mul_cancel₀ hc.ne', one_smul]
      | horizontal =>
          refine ⟨1, zero_lt_one, ?_⟩
          simpa only [one_smul] using (T.velocity_eq_of_same_axis S).symm


/-- Signed free-coordinate linear map for an occupied-left graph chart. -/
@[simp] def occupiedLeftParameterCLM (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) : PlanePoint →L[ℝ] ℝ :=
  match axis, side with
  | .vertical, .negative => -(ContinuousLinearMap.fst ℝ ℝ ℝ)
  | .vertical, .positive => ContinuousLinearMap.fst ℝ ℝ ℝ
  | .horizontal, .negative => ContinuousLinearMap.snd ℝ ℝ ℝ
  | .horizontal, .positive => -(ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- The parameter read from a point in an occupied-left graph chart.  This is
the signed free coordinate used by `occupiedLeftGraphTrace`. -/
def occupiedLeftTraceParameter (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (q : PlanePoint) : ℝ :=
  occupiedLeftParameterCLM axis side q

/-- The corresponding signed coordinate on a tangent vector. -/
def occupiedLeftVelocityParameter (axis : SpliceCutAxis)
    (side : SpliceGraphOccupiedSide) (v : PlanePoint) : ℝ :=
  occupiedLeftParameterCLM axis side v

theorem continuous_occupiedLeftTraceParameter
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide) :
    Continuous (occupiedLeftTraceParameter axis side) :=
  (occupiedLeftParameterCLM axis side).continuous

@[simp] theorem occupiedLeftTraceParameter_base
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (q : PlanePoint) :
    occupiedLeftTraceParameter axis side q =
      occupiedLeftBaseParameter axis side q := by
  cases axis <;> cases side <;>
    rfl

/-- Rebase an unchanged occupied-left graph trace at another point of the
same local carrier model. -/
def OccupiedLeftRegularTrace.rebase
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p q : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (htrace :
      occupiedLeftGraphTrace axis side T.graph
        (occupiedLeftTraceParameter axis side q) = q)
    (hcarrier :
      ∀ᶠ z in 𝓝 q,
        z ∈ U ↔ z ∈ orientedGraphDomain axis side T.graph) :
    OccupiedLeftRegularTrace axis side U q where
  graph := T.graph
  graph_contDiff := T.graph_contDiff
  trace_base := by
    simpa only [occupiedLeftTraceParameter_base] using htrace
  carrier_eventually := hcarrier

@[simp] theorem occupiedLeftTraceParameter_trace
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (φ : ℝ → ℝ) (t : ℝ) :
    occupiedLeftTraceParameter axis side
        (occupiedLeftGraphTrace axis side φ t) = t := by
  cases axis <;> cases side <;>
    simp [occupiedLeftTraceParameter, occupiedLeftGraphTrace]

@[simp] theorem occupiedLeftVelocityParameter_velocity
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (φ : ℝ → ℝ) (t : ℝ) :
    occupiedLeftVelocityParameter axis side
        (occupiedLeftGraphVelocity axis side φ t) = 1 := by
  cases axis <;> cases side <;>
    simp [occupiedLeftVelocityParameter, occupiedLeftGraphVelocity]

@[simp] theorem occupiedLeftVelocityParameter_smul
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (c : ℝ) (v : PlanePoint) :
    occupiedLeftVelocityParameter axis side (c • v) =
      c * occupiedLeftVelocityParameter axis side v := by
  cases axis <;> cases side <;>
    simp [occupiedLeftVelocityParameter]

/-- Reading a graph's signed free coordinate and rebuilding that graph recovers
every point of its exact frontier. -/
theorem occupiedLeftGraphTrace_traceParameter_of_mem_frontier
    (axis : SpliceCutAxis) (side : SpliceGraphOccupiedSide)
    (φ : ℝ → ℝ) (hφ : Continuous φ) {q : PlanePoint}
    (hq : q ∈ frontier (orientedGraphDomain axis side φ)) :
    occupiedLeftGraphTrace axis side φ
        (occupiedLeftTraceParameter axis side q) = q := by
  rw [frontier_orientedGraphDomain axis side φ hφ] at hq
  cases axis <;> cases side <;>
    simp only [occupiedLeftGraphTrace, occupiedLeftTraceParameter,
      mem_ofPred_eq] at hq ⊢ <;>
    ext <;> simp_all

/-- Parameter transition from one occupied-left trace to another trace at the
same actual frontier point. -/
def OccupiedLeftRegularTrace.transitionParameter
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (_S : OccupiedLeftRegularTrace axis' side' U p) (t : ℝ) : ℝ :=
  occupiedLeftTraceParameter axis' side'
    (occupiedLeftGraphTrace axis side T.graph t)

theorem OccupiedLeftRegularTrace.transitionParameter_base
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) :
    T.transitionParameter S
        (occupiedLeftBaseParameter axis side p) =
      occupiedLeftBaseParameter axis' side' p := by
  unfold transitionParameter
  rw [T.trace_base]
  cases axis' <;> cases side' <;>
    simp [occupiedLeftTraceParameter, occupiedLeftBaseParameter]

theorem OccupiedLeftRegularTrace.transitionParameter_contDiff
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) :
    ContDiff ℝ ∞ (T.transitionParameter S) := by
  change ContDiff ℝ ∞ (fun t =>
    occupiedLeftParameterCLM axis' side'
      (occupiedLeftGraphTrace axis side T.graph t))
  exact (occupiedLeftParameterCLM axis' side').contDiff.comp T.trace_contDiff

theorem OccupiedLeftRegularTrace.transitionParameter_hasDerivAt
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) (t : ℝ) :
    HasDerivAt (T.transitionParameter S)
      (occupiedLeftVelocityParameter axis' side'
        (occupiedLeftGraphVelocity axis side T.graph t)) t := by
  change HasDerivAt
    (fun s => occupiedLeftParameterCLM axis' side'
      (occupiedLeftGraphTrace axis side T.graph s))
    (occupiedLeftParameterCLM axis' side'
      (occupiedLeftGraphVelocity axis side T.graph t)) t
  exact (occupiedLeftParameterCLM axis' side').hasFDerivAt.comp_hasDerivAt t
    (T.trace_hasDerivAt t)

/-- Transition between two occupied-left charts has positive derivative at
their common base point.  This is the infinitesimal orientation-coherence
statement; the finite-arc path itself is not differentiated. -/
theorem OccupiedLeftRegularTrace.transitionParameter_deriv_pos
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) :
    0 < deriv (T.transitionParameter S)
      (occupiedLeftBaseParameter axis side p) := by
  let t := occupiedLeftBaseParameter axis side p
  let u := occupiedLeftBaseParameter axis' side' p
  obtain ⟨c, hc, hvelocity⟩ := T.velocity_positive_smul S
  have hcoordinate :=
    congrArg (occupiedLeftVelocityParameter axis' side') hvelocity
  have hpositive :
      0 < occupiedLeftVelocityParameter axis' side'
        (occupiedLeftGraphVelocity axis side T.graph t) := by
    dsimp only [t, u] at hcoordinate ⊢
    rw [occupiedLeftVelocityParameter_velocity,
      occupiedLeftVelocityParameter_smul] at hcoordinate
    nlinarith
  rw [(T.transitionParameter_hasDerivAt S t).deriv]
  exact hpositive

/-- Two occupied-left charts at one frontier point induce an
orientation-preserving parameter transition on a genuine two-sided interval. -/
theorem OccupiedLeftRegularTrace.exists_radius_strictMonoOn_transitionParameter
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) :
    ∃ r : ℝ, 0 < r ∧
      StrictMonoOn (T.transitionParameter S)
        (Icc (occupiedLeftBaseParameter axis side p - r)
          (occupiedLeftBaseParameter axis side p + r)) := by
  let t := occupiedLeftBaseParameter axis side p
  have hderiv :
      0 < deriv (T.transitionParameter S) t :=
    T.transitionParameter_deriv_pos S
  have heventually :
      ∀ᶠ x in 𝓝 t, 0 < deriv (T.transitionParameter S) x :=
    (T.transitionParameter_contDiff S).continuous_deriv (by simp)
      |>.continuousAt.eventually (Ioi_mem_nhds hderiv)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp heventually
  let delta := r / 2
  refine ⟨delta, div_pos hr (by norm_num), ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (T.transitionParameter_contDiff S).continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [delta] at hx
    constructor <;> linarith [hx.1, hx.2, hr]

/-- Near their common base point, the transition parameter genuinely
reparametrizes one occupied-left trace by the other. -/
theorem OccupiedLeftRegularTrace.transitionParameter_trace_eventually
    {axis axis' : SpliceCutAxis}
    {side side' : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p)
    (S : OccupiedLeftRegularTrace axis' side' U p) :
    ∀ᶠ t in 𝓝 (occupiedLeftBaseParameter axis side p),
      occupiedLeftGraphTrace axis' side' S.graph
          (T.transitionParameter S t) =
        occupiedLeftGraphTrace axis side T.graph t := by
  let gamma : ℝ → PlanePoint :=
    occupiedLeftGraphTrace axis side T.graph
  let t₀ := occupiedLeftBaseParameter axis side p
  have hgammaBase : gamma t₀ = p := by
    simpa only [gamma, t₀] using T.trace_base
  have hgammaTendsto : Tendsto gamma (𝓝 t₀) (𝓝 p) := by
    rw [← hgammaBase]
    exact T.trace_contDiff.continuous.continuousAt
  have hTfrontier := hgammaTendsto.eventually T.frontier_eventually
  have hSfrontier := hgammaTendsto.eventually S.frontier_eventually
  filter_upwards [hTfrontier, hSfrontier] with t hT hS
  have hactual : gamma t ∈ frontier U := by
    apply hT.mpr
    rw [frontier_orientedGraphDomain axis side T.graph
      T.graph_contDiff.continuous]
    cases axis <;> cases side <;>
      simp [gamma, occupiedLeftGraphTrace]
  have hmodel :
      gamma t ∈ frontier (orientedGraphDomain axis' side' S.graph) :=
    hS.mp hactual
  simpa only [transitionParameter, gamma] using
    occupiedLeftGraphTrace_traceParameter_of_mem_frontier
      axis' side' S.graph S.graph_contDiff.continuous hmodel
/-- One chosen occupied-left smooth branch at an actual frontier point. -/
structure OccupiedLeftArcBranch (U : Set PlanePoint) (p : PlanePoint) where
  axis : SpliceCutAxis
  side : SpliceGraphOccupiedSide
  trace : OccupiedLeftRegularTrace axis side U p

namespace OccupiedLeftArcBranch

/-- Base velocity representing the branch's occupied-left tangent ray. -/
def velocity {U : Set PlanePoint} {p : PlanePoint}
    (B : OccupiedLeftArcBranch U p) : PlanePoint :=
  occupiedLeftGraphVelocity B.axis B.side B.trace.graph
    (occupiedLeftBaseParameter B.axis B.side p)

theorem velocity_ne_zero {U : Set PlanePoint} {p : PlanePoint}
    (B : OccupiedLeftArcBranch U p) :
    B.velocity ≠ 0 :=
  B.trace.velocity_ne_zero (occupiedLeftBaseParameter B.axis B.side p)

end OccupiedLeftArcBranch

end FiniteJunctionRepair

open FiniteJunctionRepair

theorem FinitePiecewiseRegularBoundaryTopology.arcRepresentative_mem_finiteArcInterior
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O)
    (e : T.chartCuts.ArcIndex) :
    (T.chartCuts.arcRepresentative e).1 ∈
      T.chartCuts.finiteArcInterior e := by
  refine ⟨T.chartCuts.arcRepresentative e, ?_, rfl⟩
  exact mem_connectedComponent

/-- Every actual point of every selected open finite arc has a smooth
occupied-left branch. -/
theorem FinitePiecewiseRegularBoundaryTopology.exists_occupiedLeftArcBranch
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O)
    (e : T.chartCuts.ArcIndex) (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e) :
    Nonempty (OccupiedLeftArcBranch O p.1) := by
  obtain ⟨axis, side, ⟨trace⟩⟩ :=
    T.exists_occupiedLeftRegularTrace e hp
  exact ⟨⟨axis, side, trace⟩⟩

/-- A genuine global branch assignment over every point of every actual open
finite arc.  Choices are allowed here; the coherence theorem below proves that
their occupied-left tangent rays do not depend on those choices. -/
structure OccupiedLeftArcBranchAssignment
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O) where
  branch :
    ∀ (e : T.chartCuts.ArcIndex)
      (p : CMVBoundaryLocalAtlas.FrontierSpace O),
      p ∈ T.chartCuts.finiteArcInterior e → OccupiedLeftArcBranch O p.1

/-- Canonical choice of the globally defined occupied-left branch field. -/
noncomputable def
    FinitePiecewiseRegularBoundaryTopology.occupiedLeftArcBranchAssignment
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O) :
    OccupiedLeftArcBranchAssignment T where
  branch e p hp := Classical.choice (T.exists_occupiedLeftArcBranch e p hp)

namespace OccupiedLeftArcBranchAssignment

/-- At every point of every actual arc, the assigned branch agrees with any
other local occupied-left chart up to a positive velocity rescaling. -/
theorem branch_chart_independent
    {O : Set PlanePoint} {T : FinitePiecewiseRegularBoundaryTopology O}
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e)
    (C : OccupiedLeftArcBranch O p.1) :
    ∃ c : ℝ, 0 < c ∧ C.velocity = c • (B.branch e p hp).velocity := by
  exact (B.branch e p hp).trace.velocity_positive_smul C.trace

/-- The reference branch attached to a half-edge is the globally assigned
branch at its arc's chosen interior representative. -/
noncomputable def branchAtHalfEdge
    {O : Set PlanePoint} {T : FinitePiecewiseRegularBoundaryTopology O}
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) :
    OccupiedLeftArcBranch O (T.chartCuts.arcRepresentative h.1.2).1.1 :=
  B.branch h.1.2 (T.chartCuts.arcRepresentative h.1.2).1
    (T.arcRepresentative_mem_finiteArcInterior h.1.2)

/-- The ordinary vector-valued reference field underlying the dependent branch
assignment on arc representatives. -/
noncomputable def arcReferenceVelocity
    {O : Set PlanePoint} {T : FinitePiecewiseRegularBoundaryTopology O}
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) : PlanePoint :=
  (B.branch e (T.chartCuts.arcRepresentative e).1
    (T.arcRepresentative_mem_finiteArcInterior e)).velocity

/-- The occupied-left reference velocity assigned to one actual half-edge. -/
noncomputable def branchVelocityAtHalfEdge
    {O : Set PlanePoint} {T : FinitePiecewiseRegularBoundaryTopology O}
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) : PlanePoint :=
  B.arcReferenceVelocity h.1.2

/-- Crossing an arc changes its endpoint but retains exactly the same assigned
interior reference velocity. -/
theorem branchAtHalfEdge_crossHalfEdge_velocity
    {O : Set PlanePoint} {T : FinitePiecewiseRegularBoundaryTopology O}
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) :
    B.branchVelocityAtHalfEdge (T.chartCuts.crossHalfEdge h) =
      B.branchVelocityAtHalfEdge h := by
  exact congrArg B.arcReferenceVelocity (T.chartCuts.crossHalfEdge_arc h)

end OccupiedLeftArcBranchAssignment

namespace FiniteJunctionRepair.OccupiedLeftRegularTrace

/-- Every point of an occupied-left graph trace lies on the exact frontier of
its strict graph model. -/
theorem trace_mem_model_frontier
    {axis : SpliceCutAxis} {side : SpliceGraphOccupiedSide}
    {U : Set PlanePoint} {p : PlanePoint}
    (T : OccupiedLeftRegularTrace axis side U p) (t : ℝ) :
    occupiedLeftGraphTrace axis side T.graph t ∈
      frontier (orientedGraphDomain axis side T.graph) := by
  rw [frontier_orientedGraphDomain axis side T.graph
    T.graph_contDiff.continuous]
  cases axis <;> cases side <;>
    simp [occupiedLeftGraphTrace]

end FiniteJunctionRepair.OccupiedLeftRegularTrace

/-- A genuine two-sided coordinate neighborhood of one point on a selected
open arc.  The parameter is the occupied-left smooth parameter; every point
in the retained interval lies on the same actual quotient arc. -/
structure OccupiedLeftArcCoordinateNeighborhood
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O)
    (e : T.chartCuts.ArcIndex)
    {p : CMVBoundaryLocalAtlas.FrontierSpace O}
    (_hp : p ∈ T.chartCuts.finiteArcInterior e)
    (B : OccupiedLeftArcBranch O p.1) where
  radius : ℝ
  radius_pos : 0 < radius
  frontier_mem :
    ∀ {t : ℝ},
      t ∈ Icc
          (occupiedLeftBaseParameter B.axis B.side p.1 - radius)
          (occupiedLeftBaseParameter B.axis B.side p.1 + radius) →
        occupiedLeftGraphTrace B.axis B.side B.trace.graph t ∈ frontier O
  arc_mem :
    ∀ {t : ℝ}
      (ht : t ∈ Icc
        (occupiedLeftBaseParameter B.axis B.side p.1 - radius)
        (occupiedLeftBaseParameter B.axis B.side p.1 + radius)),
      (⟨occupiedLeftGraphTrace B.axis B.side B.trace.graph t,
        frontier_mem ht⟩ :
          CMVBoundaryLocalAtlas.FrontierSpace O) ∈
        T.chartCuts.finiteArcInterior e

namespace OccupiedLeftArcCoordinateNeighborhood

variable {O : Set PlanePoint}
    {T : FinitePiecewiseRegularBoundaryTopology O}
    {e : T.chartCuts.ArcIndex}
    {p : CMVBoundaryLocalAtlas.FrontierSpace O}
    {hp : p ∈ T.chartCuts.finiteArcInterior e}
    {B : OccupiedLeftArcBranch O p.1}

/-- The compact occupied-left parameter interval retained by the
neighborhood. -/
abbrev ParameterInterval
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :=
  Icc
    (occupiedLeftBaseParameter B.axis B.side p.1 - N.radius)
    (occupiedLeftBaseParameter B.axis B.side p.1 + N.radius)

/-- The actual frontier point at one retained occupied-left parameter. -/
def point (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    CMVBoundaryLocalAtlas.FrontierSpace O :=
  ⟨occupiedLeftGraphTrace B.axis B.side B.trace.graph t.1,
    N.frontier_mem t.2⟩

theorem point_mem_arc
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    N.point t ∈ T.chartCuts.finiteArcInterior e :=
  N.arc_mem t.2

/-- Membership in the selected open arc puts the underlying planar point in
the selected finite-arc chart window. -/
theorem point_mem_chartWindow
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    (N.point t).1 ∈
      (T.chartCuts.arc (T.chartCuts.finiteArcChart e)).window := by
  have hcore :=
    T.chartCuts.cutComponentImage_subset_coreInterior
      (T.chartCuts.finiteArcChart e)
      (T.chartCuts.arcRepresentative e)
      (T.chartCuts.arcRepresentative_mem_finiteArcChart_coreInterior e)
      (N.point_mem_arc t)
  rcases hcore with ⟨q, _hq, hqPoint⟩
  rw [← hqPoint]
  exact q.2

/-- The same point lifted to the selected finite-arc chart. -/
def localPoint
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    (T.chartCuts.arc (T.chartCuts.finiteArcChart e)).localDomain :=
  ⟨N.point t, N.point_mem_chartWindow t⟩

@[simp] theorem localPoint_val
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    (N.localPoint t :
        CMVBoundaryLocalAtlas.FrontierSpace O) = N.point t :=
  rfl

/-- Selected finite-arc real coordinate of an occupied-left trace point. -/
noncomputable def coordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) : ℝ :=
  ((T.chartCuts.arc
      (T.chartCuts.finiteArcChart e)).parameterHomeomorph
        (N.localPoint t) : ℝ)

/-- Every retained occupied-left trace point has a parameter on the normalized
left-to-right finite-arc path. -/
theorem exists_unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    ∃ u : unitInterval,
      (u : ℝ) ∈ Ioo 0 1 ∧
        T.chartCuts.finiteArcPointLR e u = N.point t := by
  have hImage :
      N.point t ∈
        T.chartCuts.finiteArcPointLR e ''
          {u : unitInterval | (u : ℝ) ∈ Ioo 0 1} := by
    rw [T.chartCuts.image_finiteArcPointLR_openUnitInterval e]
    exact N.point_mem_arc t
  exact hImage

/-- Normalized left-to-right path parameter of one retained occupied-left
trace point. -/
noncomputable def unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) : unitInterval :=
  Classical.choose (N.exists_unitParameter t)

theorem unitParameter_mem_openUnitInterval
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    (N.unitParameter t : ℝ) ∈ Ioo 0 1 :=
  (Classical.choose_spec (N.exists_unitParameter t)).1

theorem finiteArcPointLR_unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    T.chartCuts.finiteArcPointLR e (N.unitParameter t) = N.point t :=
  (Classical.choose_spec (N.exists_unitParameter t)).2

/-- The normalized finite-arc path parameter is uniquely determined by its
frontier point. -/
theorem eq_unitParameter_of_finiteArcPointLR_eq
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) (u : unitInterval)
    (hu : T.chartCuts.finiteArcPointLR e u = N.point t) :
    u = N.unitParameter t :=
  T.chartCuts.finiteArcPointLR_injective e
    (hu.trans (N.finiteArcPointLR_unitParameter t).symm)

/-- The selected raw chart coordinate is the positive affine normalization of
the actual compact-arc path parameter. -/
theorem coordinate_eq_affine_unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    N.coordinate t =
      T.chartCuts.finiteArcLowerParameter e +
        (N.unitParameter t : ℝ) *
          (T.chartCuts.finiteArcUpperParameter e -
            T.chartCuts.finiteArcLowerParameter e) := by
  let C := T.chartCuts.arc (T.chartCuts.finiteArcChart e)
  let z := T.chartCuts.finiteArcUnitCoreParameter e (N.unitParameter t)
  have hlocal :
      C.parameterHomeomorph.symm
          (C.coreParameterToParameterInterval z) =
        N.localPoint t := by
    apply Subtype.ext
    change T.chartCuts.finiteArcPointLR e (N.unitParameter t) =
      (N.localPoint t :
        CMVBoundaryLocalAtlas.FrontierSpace O)
    rw [N.localPoint_val]
    exact N.finiteArcPointLR_unitParameter t
  have hparameter := congrArg C.parameterHomeomorph hlocal
  rw [C.parameterHomeomorph.apply_symm_apply] at hparameter
  have hvalue :=
    congrArg (fun u : C.parameterInterval => (u : ℝ)) hparameter
  exact hvalue.symm

/-- Explicit inverse-affine formula for the normalized compact-arc path
parameter of an occupied-left trace point. -/
theorem unitParameter_val_eq_normalizedCoordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (t : N.ParameterInterval) :
    (N.unitParameter t : ℝ) =
      (N.coordinate t - T.chartCuts.finiteArcLowerParameter e) /
        (T.chartCuts.finiteArcUpperParameter e -
          T.chartCuts.finiteArcLowerParameter e) := by
  have hne :
      T.chartCuts.finiteArcUpperParameter e -
          T.chartCuts.finiteArcLowerParameter e ≠ 0 :=
    (sub_pos.mpr
      (T.chartCuts.finiteArcLowerParameter_lt_upperParameter e)).ne'
  apply (eq_div_iff hne).2
  rw [N.coordinate_eq_affine_unitParameter t]
  ring

theorem continuous_point
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    Continuous N.point := by
  apply Continuous.subtype_mk
  exact B.trace.trace_contDiff.continuous.comp continuous_subtype_val

theorem continuous_localPoint
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    Continuous N.localPoint := by
  apply Continuous.subtype_mk
  exact N.continuous_point

theorem continuous_coordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    Continuous N.coordinate := by
  exact continuous_subtype_val.comp
    ((T.chartCuts.arc
      (T.chartCuts.finiteArcChart e)).parameterHomeomorph.continuous.comp
        N.continuous_localPoint)

theorem continuous_unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    Continuous N.unitParameter := by
  apply Continuous.subtype_mk
  change Continuous (fun t => (N.unitParameter t : ℝ))
  have hfun :
      (fun t => (N.unitParameter t : ℝ)) =
        fun t =>
          (N.coordinate t - T.chartCuts.finiteArcLowerParameter e) /
            (T.chartCuts.finiteArcUpperParameter e -
              T.chartCuts.finiteArcLowerParameter e) := by
    funext t
    exact N.unitParameter_val_eq_normalizedCoordinate t
  rw [hfun]
  exact (N.continuous_coordinate.sub continuous_const).div_const _

theorem injective_coordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    Function.Injective N.coordinate := by
  intro s t hst
  have hparameter :
      (T.chartCuts.arc
          (T.chartCuts.finiteArcChart e)).parameterHomeomorph
            (N.localPoint s) =
        (T.chartCuts.arc
          (T.chartCuts.finiteArcChart e)).parameterHomeomorph
            (N.localPoint t) :=
    Subtype.ext hst
  have hlocal : N.localPoint s = N.localPoint t :=
    (T.chartCuts.arc
      (T.chartCuts.finiteArcChart e)).parameterHomeomorph.injective hparameter
  have hpoint : N.point s = N.point t := by
    rw [← N.localPoint_val s, ← N.localPoint_val t, hlocal]
  have htrace :
      occupiedLeftGraphTrace B.axis B.side B.trace.graph s.1 =
        occupiedLeftGraphTrace B.axis B.side B.trace.graph t.1 :=
    congrArg Subtype.val hpoint
  exact Subtype.ext (B.trace.trace_injective htrace)

/-- Relative to any selected finite-arc chart, the occupied-left parameter
has one strict local orientation.  This is derived from continuity and
injectivity; no continuity of the global choice-valued branch field is used. -/
theorem strictMono_or_strictAnti_coordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    StrictMono N.coordinate ∨ StrictAnti N.coordinate := by
  letI : Fact
      (occupiedLeftBaseParameter B.axis B.side p.1 - N.radius ≤
        occupiedLeftBaseParameter B.axis B.side p.1 + N.radius) :=
    ⟨by linarith [N.radius_pos]⟩
  exact N.continuous_coordinate.strictMono_of_inj_boundedOrder'
    N.injective_coordinate

theorem strictMono_unitParameter_of_strictMono_coordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (h : StrictMono N.coordinate) :
    StrictMono N.unitParameter := by
  intro s t hst
  change (N.unitParameter s : ℝ) < (N.unitParameter t : ℝ)
  rw [N.unitParameter_val_eq_normalizedCoordinate,
    N.unitParameter_val_eq_normalizedCoordinate]
  apply (div_lt_div_iff_of_pos_right
    (sub_pos.mpr
      (T.chartCuts.finiteArcLowerParameter_lt_upperParameter e))).2
  exact sub_lt_sub_right (h hst) _

theorem strictAnti_unitParameter_of_strictAnti_coordinate
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (h : StrictAnti N.coordinate) :
    StrictAnti N.unitParameter := by
  intro s t hst
  change (N.unitParameter t : ℝ) < (N.unitParameter s : ℝ)
  rw [N.unitParameter_val_eq_normalizedCoordinate,
    N.unitParameter_val_eq_normalizedCoordinate]
  apply (div_lt_div_iff_of_pos_right
    (sub_pos.mpr
      (T.chartCuts.finiteArcLowerParameter_lt_upperParameter e))).2
  exact sub_lt_sub_right (h hst) _

/-- The local occupied-left trace has one strict direction in the actual
normalized left-to-right finite-arc path parameter. -/
theorem strictMono_or_strictAnti_unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    StrictMono N.unitParameter ∨ StrictAnti N.unitParameter := by
  rcases N.strictMono_or_strictAnti_coordinate with hincreases | hdecreases
  · exact Or.inl (N.strictMono_unitParameter_of_strictMono_coordinate hincreases)
  · exact Or.inr (N.strictAnti_unitParameter_of_strictAnti_coordinate hdecreases)

/-- Two occupied-left coordinate neighborhoods at the same arc point choose
the same orientation in the normalized finite-arc parameter.  The comparison
uses the positive smooth transition between the two local traces; the
topological finite-arc path is only evaluated, never differentiated. -/
theorem orientation_agrees
    {C : OccupiedLeftArcBranch O p.1}
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (M : OccupiedLeftArcCoordinateNeighborhood T e hp C) :
    StrictMono N.unitParameter ↔ StrictMono M.unitParameter := by
  let t₀ := occupiedLeftBaseParameter B.axis B.side p.1
  let u₀ := occupiedLeftBaseParameter C.axis C.side p.1
  let transition : ℝ → ℝ := B.trace.transitionParameter C.trace
  obtain ⟨r, hr, htransitionMono⟩ :=
    B.trace.exists_radius_strictMonoOn_transitionParameter C.trace
  have htransitionBase : transition t₀ = u₀ := by
    simpa only [transition, t₀, u₀] using
      B.trace.transitionParameter_base C.trace
  have hNdomain :
      Ioo (t₀ - N.radius) (t₀ + N.radius) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds (by linarith [N.radius_pos]) (by linarith [N.radius_pos])
  have htransitionDomain :
      Ioo (t₀ - r) (t₀ + r) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hMtarget :
      Ioo (u₀ - M.radius) (u₀ + M.radius) ∈ 𝓝 (transition t₀) := by
    rw [htransitionBase]
    exact Ioo_mem_nhds
      (by linarith [M.radius_pos]) (by linarith [M.radius_pos])
  have hMdomain :
      transition ⁻¹' Ioo (u₀ - M.radius) (u₀ + M.radius) ∈ 𝓝 t₀ :=
    (B.trace.transitionParameter_contDiff C.trace).continuous.continuousAt
      hMtarget
  have htrace :
      ∀ᶠ s in 𝓝 t₀,
        occupiedLeftGraphTrace C.axis C.side C.trace.graph (transition s) =
          occupiedLeftGraphTrace B.axis B.side B.trace.graph s := by
    simpa only [transition, t₀] using
      B.trace.transitionParameter_trace_eventually C.trace
  have hgood :
      {s : ℝ |
        s ∈ Ioo (t₀ - N.radius) (t₀ + N.radius) ∧
        s ∈ Ioo (t₀ - r) (t₀ + r) ∧
        transition s ∈ Ioo (u₀ - M.radius) (u₀ + M.radius) ∧
        occupiedLeftGraphTrace C.axis C.side C.trace.graph (transition s) =
          occupiedLeftGraphTrace B.axis B.side B.trace.graph s} ∈ 𝓝 t₀ := by
    filter_upwards [hNdomain, htransitionDomain, hMdomain, htrace] with s
      hsN hsTransition hsM hsTrace
    exact ⟨hsN, hsTransition, hsM, hsTrace⟩
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let delta := rho / 2
  let s := t₀ - delta
  let z := t₀ + delta
  have hdelta : 0 < delta := div_pos hrho (by norm_num)
  have hsBall : s ∈ Metric.ball t₀ rho := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [s, delta]
    constructor <;> linarith
  have hzBall : z ∈ Metric.ball t₀ rho := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [z, delta]
    constructor <;> linarith
  have hsGood := hball hsBall
  have hzGood := hball hzBall
  let sN : N.ParameterInterval :=
    ⟨s, hsGood.1.1.le, hsGood.1.2.le⟩
  let zN : N.ParameterInterval :=
    ⟨z, hzGood.1.1.le, hzGood.1.2.le⟩
  let sM : M.ParameterInterval :=
    ⟨transition s, hsGood.2.2.1.1.le, hsGood.2.2.1.2.le⟩
  let zM : M.ParameterInterval :=
    ⟨transition z, hzGood.2.2.1.1.le, hzGood.2.2.1.2.le⟩
  have hsz : sN < zN := by
    change s < z
    dsimp only [s, z]
    linarith
  have htransitionSZ : sM < zM := by
    change transition s < transition z
    apply htransitionMono
      ⟨hsGood.2.1.1.le, hsGood.2.1.2.le⟩
      ⟨hzGood.2.1.1.le, hzGood.2.1.2.le⟩
    change s < z
    dsimp only [s, z]
    linarith
  have hsPoint : N.point sN = M.point sM := by
    apply Subtype.ext
    exact hsGood.2.2.2.symm
  have hzPoint : N.point zN = M.point zM := by
    apply Subtype.ext
    exact hzGood.2.2.2.symm
  have hsUnit : N.unitParameter sN = M.unitParameter sM := by
    apply T.chartCuts.finiteArcPointLR_injective e
    rw [N.finiteArcPointLR_unitParameter,
      M.finiteArcPointLR_unitParameter, hsPoint]
  have hzUnit : N.unitParameter zN = M.unitParameter zM := by
    apply T.chartCuts.finiteArcPointLR_injective e
    rw [N.finiteArcPointLR_unitParameter,
      M.finiteArcPointLR_unitParameter, hzPoint]
  constructor
  · intro hN
    rcases M.strictMono_or_strictAnti_unitParameter with hM | hM
    · exact hM
    · exfalso
      have hforward := hN hsz
      have hbackward := hM htransitionSZ
      rw [hsUnit, hzUnit] at hforward
      exact (not_lt_of_ge hforward.le) hbackward
  · intro hM
    rcases N.strictMono_or_strictAnti_unitParameter with hN | hN
    · exact hN
    · exfalso
      have hforward := hM htransitionSZ
      have hbackward := hN hsz
      rw [hsUnit, hzUnit] at hbackward
      exact (not_lt_of_ge hforward.le) hbackward

/-- Two local neighborhoods based at different points have the same
orientation when they use a common raw parameter on their overlap.  This is
the re-centering lemma used to move one occupied-left trace along an arc. -/
theorem orientation_agrees_of_common_parameter
    {q : CMVBoundaryLocalAtlas.FrontierSpace O}
    {hq : q ∈ T.chartCuts.finiteArcInterior e}
    {C : OccupiedLeftArcBranch O q.1}
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (M : OccupiedLeftArcCoordinateNeighborhood T e hq C)
    (hbase :
      occupiedLeftBaseParameter C.axis C.side q.1 ∈
        Ioo
          (occupiedLeftBaseParameter B.axis B.side p.1 - N.radius)
          (occupiedLeftBaseParameter B.axis B.side p.1 + N.radius))
    (hpoint : ∀ (t : ℝ)
      (htN : t ∈ N.ParameterInterval)
      (htM : t ∈ M.ParameterInterval),
      N.point ⟨t, htN⟩ = M.point ⟨t, htM⟩) :
    StrictMono N.unitParameter ↔ StrictMono M.unitParameter := by
  let u := occupiedLeftBaseParameter C.axis C.side q.1
  have hMbase :
      u ∈ Ioo
        (occupiedLeftBaseParameter C.axis C.side q.1 - M.radius)
        (occupiedLeftBaseParameter C.axis C.side q.1 + M.radius) := by
    dsimp only [u]
    constructor <;> linarith [M.radius_pos]
  have hgood :
      Ioo
          (occupiedLeftBaseParameter B.axis B.side p.1 - N.radius)
          (occupiedLeftBaseParameter B.axis B.side p.1 + N.radius) ∩
        Ioo
          (occupiedLeftBaseParameter C.axis C.side q.1 - M.radius)
          (occupiedLeftBaseParameter C.axis C.side q.1 + M.radius) ∈
        𝓝 u :=
    inter_mem
      (Ioo_mem_nhds (show
        occupiedLeftBaseParameter B.axis B.side p.1 - N.radius < u from
          hbase.1) (show
        u < occupiedLeftBaseParameter B.axis B.side p.1 + N.radius from
          hbase.2))
      (Ioo_mem_nhds hMbase.1 hMbase.2)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let s := u - r / 2
  let z := u + r / 2
  have hsBall : s ∈ Metric.ball u r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [s]
    constructor <;> linarith [hr]
  have hzBall : z ∈ Metric.ball u r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [z]
    constructor <;> linarith [hr]
  have hsGood := hball hsBall
  have hzGood := hball hzBall
  have hsz : s < z := by
    dsimp only [s, z]
    linarith [hr]
  let sN : N.ParameterInterval :=
    ⟨s, hsGood.1.1.le, hsGood.1.2.le⟩
  let zN : N.ParameterInterval :=
    ⟨z, hzGood.1.1.le, hzGood.1.2.le⟩
  let sM : M.ParameterInterval :=
    ⟨s, hsGood.2.1.le, hsGood.2.2.le⟩
  let zM : M.ParameterInterval :=
    ⟨z, hzGood.2.1.le, hzGood.2.2.le⟩
  have hsNltzN : sN < zN := by
    change s < z
    exact hsz
  have hsMltzM : sM < zM := by
    change s < z
    exact hsz
  have hsPoint : N.point sN = M.point sM :=
    hpoint s sN.property sM.property
  have hzPoint : N.point zN = M.point zM :=
    hpoint z zN.property zM.property
  have hsUnit : N.unitParameter sN = M.unitParameter sM := by
    apply T.chartCuts.finiteArcPointLR_injective e
    rw [N.finiteArcPointLR_unitParameter,
      M.finiteArcPointLR_unitParameter, hsPoint]
  have hzUnit : N.unitParameter zN = M.unitParameter zM := by
    apply T.chartCuts.finiteArcPointLR_injective e
    rw [N.finiteArcPointLR_unitParameter,
      M.finiteArcPointLR_unitParameter, hzPoint]
  constructor
  · intro hN
    rcases M.strictMono_or_strictAnti_unitParameter with hM | hM
    · exact hM
    · have hforward := hN hsNltzN
      have hbackward := hM hsMltzM
      rw [hsUnit, hzUnit] at hforward
      exact (False.elim ((not_lt_of_ge hforward.le) hbackward))
  · intro hM
    rcases N.strictMono_or_strictAnti_unitParameter with hN | hN
    · exact hN
    · have hforward := hM hsMltzM
      have hbackward := hN hsNltzN
      rw [hsUnit, hzUnit] at hbackward
      exact (False.elim ((not_lt_of_ge hforward.le) hbackward))

/-- Strict increase in the selected finite-arc chart is equivalent to strict
increase in its positive affine unit normalization. -/
theorem strictMono_coordinate_iff_unitParameter
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    StrictMono N.coordinate ↔ StrictMono N.unitParameter := by
  constructor
  · exact N.strictMono_unitParameter_of_strictMono_coordinate
  · intro hunit
    rcases N.strictMono_or_strictAnti_coordinate with hmono | hanti
    · exact hmono
    · exfalso
      have hantiUnit :=
        N.strictAnti_unitParameter_of_strictAnti_coordinate hanti
      let a : N.ParameterInterval :=
        ⟨occupiedLeftBaseParameter B.axis B.side p.1 - N.radius,
          le_rfl, by linarith [N.radius_pos]⟩
      let b : N.ParameterInterval :=
        ⟨occupiedLeftBaseParameter B.axis B.side p.1 + N.radius,
          by linarith [N.radius_pos], le_rfl⟩
      have hab : a < b := by
        change occupiedLeftBaseParameter B.axis B.side p.1 - N.radius <
          occupiedLeftBaseParameter B.axis B.side p.1 + N.radius
        linarith [N.radius_pos]
      exact (not_lt_of_ge (hunit hab).le) (hantiUnit hab)

/-- Boolean orientation of one arbitrary occupied-left coordinate
neighborhood relative to the fixed left-to-right finite-arc parameter. -/
noncomputable def coordinateIncreases
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) : Bool := by
  classical
  exact if StrictMono N.coordinate then true else false

theorem coordinateIncreases_eq_true
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    N.coordinateIncreases = true → StrictMono N.unitParameter := by
  classical
  intro hincreases
  apply N.strictMono_coordinate_iff_unitParameter.mp
  by_contra hnot
  simp [coordinateIncreases, hnot] at hincreases

theorem coordinateIncreases_eq_false
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B) :
    N.coordinateIncreases = false → StrictAnti N.unitParameter := by
  classical
  intro hdecreases
  have hnot : ¬ StrictMono N.coordinate := by
    intro hmono
    simp [coordinateIncreases, hmono] at hdecreases
  exact N.strictMono_or_strictAnti_coordinate.resolve_left hnot
    |> N.strictAnti_unitParameter_of_strictAnti_coordinate

/-- The orientation Boolean is independent of the occupied-left branch and
coordinate neighborhood chosen at the same actual arc point. -/
theorem coordinateIncreases_eq
    {C : OccupiedLeftArcBranch O p.1}
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (M : OccupiedLeftArcCoordinateNeighborhood T e hp C) :
    N.coordinateIncreases = M.coordinateIncreases := by
  classical
  have hiff : StrictMono N.coordinate ↔ StrictMono M.coordinate :=
    N.strictMono_coordinate_iff_unitParameter.trans
      ((N.orientation_agrees M).trans
        M.strictMono_coordinate_iff_unitParameter.symm)
  unfold coordinateIncreases
  by_cases hN : StrictMono N.coordinate
  · rw [if_pos hN, if_pos (hiff.mp hN)]
  · rw [if_neg hN, if_neg (fun hM => hN (hiff.mpr hM))]

/-- Boolean form of orientation coherence for two recentered neighborhoods
that share a raw trace parameter on an overlap. -/
theorem coordinateIncreases_eq_of_common_parameter
    {q : CMVBoundaryLocalAtlas.FrontierSpace O}
    {hq : q ∈ T.chartCuts.finiteArcInterior e}
    {C : OccupiedLeftArcBranch O q.1}
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp B)
    (M : OccupiedLeftArcCoordinateNeighborhood T e hq C)
    (hbase :
      occupiedLeftBaseParameter C.axis C.side q.1 ∈
        Ioo
          (occupiedLeftBaseParameter B.axis B.side p.1 - N.radius)
          (occupiedLeftBaseParameter B.axis B.side p.1 + N.radius))
    (hpoint : ∀ (t : ℝ)
      (htN : t ∈ N.ParameterInterval)
      (htM : t ∈ M.ParameterInterval),
      N.point ⟨t, htN⟩ = M.point ⟨t, htM⟩) :
    N.coordinateIncreases = M.coordinateIncreases := by
  classical
  have hiffUnit :=
    N.orientation_agrees_of_common_parameter M hbase hpoint
  have hiff : StrictMono N.coordinate ↔ StrictMono M.coordinate :=
    N.strictMono_coordinate_iff_unitParameter.trans
      (hiffUnit.trans M.strictMono_coordinate_iff_unitParameter.symm)
  unfold coordinateIncreases
  by_cases hN : StrictMono N.coordinate
  · rw [if_pos hN, if_pos (hiff.mp hN)]
  · rw [if_neg hN, if_neg (fun hM => hN (hiff.mpr hM))]
end OccupiedLeftArcCoordinateNeighborhood

/-- Every assigned occupied-left branch on an actual open finite arc admits a
two-sided coordinate interval contained in that same arc.  On that interval
the occupied-left parameter is strictly monotone or strictly antitone in the
fixed finite-arc coordinate. -/
theorem FinitePiecewiseRegularBoundaryTopology.exists_occupiedLeftArcCoordinateNeighborhood
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e)
    (B : OccupiedLeftArcBranch O p.1) :
    Nonempty (OccupiedLeftArcCoordinateNeighborhood T e hp B) := by
  let gamma : ℝ → PlanePoint :=
    occupiedLeftGraphTrace B.axis B.side B.trace.graph
  let t0 : ℝ := occupiedLeftBaseParameter B.axis B.side p.1
  have hgamma0 : gamma t0 = p.1 := by
    simpa only [gamma, t0] using B.trace.trace_base
  have hgammaTendsto : Tendsto gamma (𝓝 t0) (𝓝 p.1) := by
    rw [← hgamma0]
    exact B.trace.trace_contDiff.continuous.continuousAt
  have hfrontier :
      ∀ᶠ t in 𝓝 t0, gamma t ∈ frontier O := by
    have hlocal := hgammaTendsto.eventually B.trace.frontier_eventually
    filter_upwards [hlocal] with t ht
    apply ht.mpr
    exact B.trace.trace_mem_model_frontier t
  have hopen : IsOpen (T.chartCuts.finiteArcInterior e) := by
    exact T.chartCuts.isOpen_cutComponentImage
      (T.chartCuts.arcRepresentative e)
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hopen
  have hpV : p.1 ∈ V := by
    have hpPreimage : p ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]
      exact hp
    exact hpPreimage
  have hV :
      ∀ᶠ t in 𝓝 t0, gamma t ∈ V :=
    hgammaTendsto.eventually (hVopen.mem_nhds hpV)
  have hgood :
      {t : ℝ | gamma t ∈ frontier O ∧ gamma t ∈ V} ∈ 𝓝 t0 := by
    filter_upwards [hfrontier, hV] with t htFrontier htV
    exact ⟨htFrontier, htV⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let delta : ℝ := r / 2
  have hdelta : 0 < delta := div_pos hr (by norm_num)
  have in_ball_of_mem_interval {t : ℝ}
      (ht : t ∈ Icc (t0 - delta) (t0 + delta)) :
      t ∈ Metric.ball t0 r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp only [delta] at ht
    constructor <;> linarith [ht.1, ht.2, hr]
  refine ⟨{
    radius := delta
    radius_pos := hdelta
    frontier_mem := ?_
    arc_mem := ?_
  }⟩
  · intro t ht
    have ht' : t ∈ Icc (t0 - delta) (t0 + delta) := by
      simpa only [t0] using ht
    exact (hball (in_ball_of_mem_interval ht')).1
  · intro t ht
    have ht' : t ∈ Icc (t0 - delta) (t0 + delta) := by
      simpa only [t0] using ht
    have hdata := hball (in_ball_of_mem_interval ht')
    have hpreimage :
        (⟨gamma t, hdata.1⟩ :
          CMVBoundaryLocalAtlas.FrontierSpace O) ∈ Subtype.val ⁻¹' V :=
      hdata.2
    rw [hVeq] at hpreimage
    simpa only [gamma] using hpreimage

namespace OccupiedLeftArcBranchAssignment

variable {O : Set PlanePoint}
    {T : FinitePiecewiseRegularBoundaryTopology O}

/-- A concrete two-sided occupied-left neighborhood at an arbitrary actual
point of a selected open arc. -/
noncomputable def pointCoordinateNeighborhood
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e) :
    OccupiedLeftArcCoordinateNeighborhood T e hp (B.branch e p hp) :=
  Classical.choice
    (T.exists_occupiedLeftArcCoordinateNeighborhood e p hp (B.branch e p hp))

/-- Branch-independent local orientation at an arbitrary open-arc point. -/
noncomputable def pointCoordinateIncreases
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e) : Bool :=
  (B.pointCoordinateNeighborhood e p hp).coordinateIncreases

/-- Every other occupied-left branch and coordinate neighborhood at the same
arc point computes the same orientation bit. -/
theorem pointCoordinateIncreases_eq
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e)
    (C : OccupiedLeftArcBranch O p.1)
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp C) :
    B.pointCoordinateIncreases e p hp = N.coordinateIncreases := by
  unfold pointCoordinateIncreases
  exact (B.pointCoordinateNeighborhood e p hp).coordinateIncreases_eq N

/-- The occupied-left direction is locally constant on every actual open
finite arc.  The proof rebases one unchanged graph trace and compares only
overlapping raw-parameter intervals. -/
theorem pointCoordinateIncreases_isLocallyConstant
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    IsLocallyConstant (fun p : T.chartCuts.finiteArcInterior e =>
      B.pointCoordinateIncreases e p.1 p.2) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro p
  let C : OccupiedLeftArcBranch O p.1.1 :=
    B.branch e p.1 p.2
  let N : OccupiedLeftArcCoordinateNeighborhood T e p.2 C :=
    B.pointCoordinateNeighborhood e p.1 p.2
  obtain ⟨W, hW, hWopen, hpW⟩ :=
    mem_nhds_iff.mp C.trace.carrier_eventually
  let t₀ := occupiedLeftBaseParameter C.axis C.side p.1.1
  let U : Set (T.chartCuts.finiteArcInterior e) :=
    {q | q.1.1 ∈ W ∧
      occupiedLeftTraceParameter C.axis C.side q.1.1 ∈
        Ioo (t₀ - N.radius) (t₀ + N.radius)}
  refine ⟨U, ?_, ?_, ?_⟩
  · change IsOpen
      ((fun q : T.chartCuts.finiteArcInterior e => q.1.1) ⁻¹' W ∩
        (fun q : T.chartCuts.finiteArcInterior e =>
          occupiedLeftTraceParameter C.axis C.side q.1.1) ⁻¹'
            Ioo (t₀ - N.radius) (t₀ + N.radius))
    have hval :
        Continuous (fun q : T.chartCuts.finiteArcInterior e => q.1.1) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (hWopen.preimage hval).inter
      (isOpen_Ioo.preimage
        ((continuous_occupiedLeftTraceParameter C.axis C.side).comp hval))
  · change p.1.1 ∈ W ∧
      occupiedLeftTraceParameter C.axis C.side p.1.1 ∈
        Ioo (t₀ - N.radius) (t₀ + N.radius)
    refine ⟨hpW, ?_⟩
    rw [occupiedLeftTraceParameter_base]
    dsimp only [t₀]
    constructor <;> linarith [N.radius_pos]
  · intro q hq
    change q.1.1 ∈ W ∧
      occupiedLeftTraceParameter C.axis C.side q.1.1 ∈
        Ioo (t₀ - N.radius) (t₀ + N.radius) at hq
    have hlocal :
        O ∩ W =
          orientedGraphDomain C.axis C.side C.trace.graph ∩ W := by
      ext z
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨hzO, hzW⟩
        exact ⟨(hW hzW).mp hzO, hzW⟩
      · rintro ⟨hzModel, hzW⟩
        exact ⟨(hW hzW).mpr hzModel, hzW⟩
    have hfrontier :=
      frontier_inter_eq_of_inter_open_eq hWopen hlocal
    have hqModelPair :
        q.1.1 ∈
          frontier (orientedGraphDomain C.axis C.side C.trace.graph) ∩ W := by
      rw [← hfrontier]
      exact ⟨q.1.2, hq.1⟩
    have htrace :
        occupiedLeftGraphTrace C.axis C.side C.trace.graph
          (occupiedLeftTraceParameter C.axis C.side q.1.1) = q.1.1 :=
      occupiedLeftGraphTrace_traceParameter_of_mem_frontier
        C.axis C.side C.trace.graph C.trace.graph_contDiff.continuous
        hqModelPair.1
    have hcarrier :
        ∀ᶠ z in 𝓝 q.1.1,
          z ∈ O ↔
            z ∈ orientedGraphDomain C.axis C.side C.trace.graph := by
      filter_upwards [hWopen.mem_nhds hq.1] with z hz
      exact hW hz
    let Cq : OccupiedLeftArcBranch O q.1.1 := {
      axis := C.axis
      side := C.side
      trace := C.trace.rebase htrace hcarrier
    }
    let M : OccupiedLeftArcCoordinateNeighborhood T e q.2 Cq :=
      Classical.choice
        (T.exists_occupiedLeftArcCoordinateNeighborhood e q.1 q.2 Cq)
    have hbase :
        occupiedLeftBaseParameter Cq.axis Cq.side q.1.1 ∈
          Ioo
            (occupiedLeftBaseParameter C.axis C.side p.1.1 - N.radius)
            (occupiedLeftBaseParameter C.axis C.side p.1.1 + N.radius) := by
      simpa only [Cq, occupiedLeftTraceParameter_base, t₀] using hq.2
    have hpoint : ∀ (t : ℝ)
        (htN : t ∈ N.ParameterInterval)
        (htM : t ∈ M.ParameterInterval),
        N.point ⟨t, htN⟩ = M.point ⟨t, htM⟩ := by
      intro t htN htM
      apply Subtype.ext
      rfl
    have hNM :
        N.coordinateIncreases = M.coordinateIncreases :=
      N.coordinateIncreases_eq_of_common_parameter M hbase hpoint
    calc
      B.pointCoordinateIncreases e q.1 q.2 =
          M.coordinateIncreases :=
        B.pointCoordinateIncreases_eq e q.1 q.2 Cq M
      _ = N.coordinateIncreases := hNM.symm
      _ = B.pointCoordinateIncreases e p.1 p.2 := rfl

/-- Connectedness of the finite open arc promotes local occupied-left
orientation coherence to one orientation on the entire arc. -/
theorem pointCoordinateIncreases_eq_on_arc
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p q : T.chartCuts.finiteArcInterior e) :
    B.pointCoordinateIncreases e p.1 p.2 =
      B.pointCoordinateIncreases e q.1 q.2 := by
  letI : ConnectedSpace (T.chartCuts.finiteArcInterior e) :=
    isConnected_iff_connectedSpace.mp
      (T.chartCuts.isConnected_cutComponentImage
        (T.chartCuts.arcRepresentative e))
  exact IsLocallyConstant.apply_eq_of_preconnectedSpace
    (B.pointCoordinateIncreases_isLocallyConstant e) p q

/-- Specialization of the pointwise neighborhood at the chosen arc
representative. -/
noncomputable def arcCoordinateNeighborhood
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    OccupiedLeftArcCoordinateNeighborhood T e
      (T.arcRepresentative_mem_finiteArcInterior e)
      (B.branch e (T.chartCuts.arcRepresentative e).1
        (T.arcRepresentative_mem_finiteArcInterior e)) :=
  B.pointCoordinateNeighborhood e (T.chartCuts.arcRepresentative e).1
    (T.arcRepresentative_mem_finiteArcInterior e)

/-- Orientation at the chosen arc representative. -/
noncomputable def arcCoordinateIncreases
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) : Bool :=
  B.pointCoordinateIncreases e (T.chartCuts.arcRepresentative e).1
    (T.arcRepresentative_mem_finiteArcInterior e)

/-- Every occupied-left neighborhood at every open-arc point has the
representative's orientation.  This is the whole-open-arc propagation bridge
used by endpoint and walk compatibility. -/
theorem pointCoordinateIncreases_eq_arcCoordinateIncreases
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e) :
    B.pointCoordinateIncreases e p hp = B.arcCoordinateIncreases e := by
  exact B.pointCoordinateIncreases_eq_on_arc e
    ⟨p, hp⟩
    ⟨(T.chartCuts.arcRepresentative e).1,
      T.arcRepresentative_mem_finiteArcInterior e⟩

theorem coordinateNeighborhood_increases_eq_arcCoordinateIncreases
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e)
    (C : OccupiedLeftArcBranch O p.1)
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp C) :
    N.coordinateIncreases = B.arcCoordinateIncreases e := by
  rw [← B.pointCoordinateIncreases_eq e p hp C N]
  exact B.pointCoordinateIncreases_eq_arcCoordinateIncreases e p hp

theorem coordinateNeighborhood_strictMono_unitParameter
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e)
    (C : OccupiedLeftArcBranch O p.1)
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp C)
    (hincreases : B.arcCoordinateIncreases e = true) :
    StrictMono N.unitParameter := by
  apply N.coordinateIncreases_eq_true
  exact
    (B.coordinateNeighborhood_increases_eq_arcCoordinateIncreases
      e p hp C N).trans hincreases

theorem coordinateNeighborhood_strictAnti_unitParameter
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (p : CMVBoundaryLocalAtlas.FrontierSpace O)
    (hp : p ∈ T.chartCuts.finiteArcInterior e)
    (C : OccupiedLeftArcBranch O p.1)
    (N : OccupiedLeftArcCoordinateNeighborhood T e hp C)
    (hdecreases : B.arcCoordinateIncreases e = false) :
    StrictAnti N.unitParameter := by
  apply N.coordinateIncreases_eq_false
  exact
    (B.coordinateNeighborhood_increases_eq_arcCoordinateIncreases
      e p hp C N).trans hdecreases

theorem arcCoordinateIncreases_eq_true
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    B.arcCoordinateIncreases e = true →
      StrictMono (B.arcCoordinateNeighborhood e).coordinate := by
  intro hincreases
  change (B.arcCoordinateNeighborhood e).coordinateIncreases = true at hincreases
  exact (B.arcCoordinateNeighborhood e).strictMono_coordinate_iff_unitParameter.mpr
    ((B.arcCoordinateNeighborhood e).coordinateIncreases_eq_true hincreases)

theorem arcCoordinateIncreases_eq_false
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    B.arcCoordinateIncreases e = false →
      StrictAnti (B.arcCoordinateNeighborhood e).coordinate := by
  classical
  intro hdecreases
  change (B.arcCoordinateNeighborhood e).coordinateIncreases = false at hdecreases
  have hnot :
      ¬ StrictMono (B.arcCoordinateNeighborhood e).coordinate := by
    intro hincreases
    have :
        (B.arcCoordinateNeighborhood e).coordinateIncreases = true := by
      simp [OccupiedLeftArcCoordinateNeighborhood.coordinateIncreases,
        hincreases]
    simp [this] at hdecreases
  exact
    (B.arcCoordinateNeighborhood e).strictMono_or_strictAnti_coordinate
      |>.resolve_left hnot

theorem arcCoordinateIncreases_eq_true_unitParameter
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (hincreases : B.arcCoordinateIncreases e = true) :
    StrictMono (B.arcCoordinateNeighborhood e).unitParameter :=
  (B.arcCoordinateNeighborhood e).strictMono_unitParameter_of_strictMono_coordinate
      (B.arcCoordinateIncreases_eq_true e hincreases)

theorem arcCoordinateIncreases_eq_false_unitParameter
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (hdecreases : B.arcCoordinateIncreases e = false) :
    StrictAnti (B.arcCoordinateNeighborhood e).unitParameter :=
  (B.arcCoordinateNeighborhood e).strictAnti_unitParameter_of_strictAnti_coordinate
      (B.arcCoordinateIncreases_eq_false e hdecreases)


/-- The selected-chart endpoint coordinate of a half-edge: `false` is the
left endpoint and `true` is the right endpoint. -/
noncomputable def halfEdgeEndpointSide
    (_B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) : Bool :=
  (T.chartCuts.endpointHalfEdgeEquiv.symm h).2

@[simp] theorem halfEdgeEndpointSide_endpointHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) (side : Bool) :
    B.halfEdgeEndpointSide (T.chartCuts.endpointHalfEdge (e, side)) =
      side := by
  simp only [halfEdgeEndpointSide,
    T.chartCuts.endpointHalfEdgeEquiv_symm_endpointHalfEdge]

/-- Crossing the same arc exchanges its selected-chart endpoint side. -/
theorem halfEdgeEndpointSide_crossHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) :
    B.halfEdgeEndpointSide (T.chartCuts.crossHalfEdge h) =
      !B.halfEdgeEndpointSide h := by
  obtain ⟨⟨e, side⟩, rfl⟩ :=
    T.chartCuts.endpointHalfEdge_surjective h
  cases side <;>
    simp only [halfEdgeEndpointSide,
      CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem.crossHalfEdge,
      Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.boolNot,
      T.chartCuts.endpointHalfEdgeEquiv_symm_endpointHalfEdge,
      T.chartCuts.endpointHalfEdgeEquiv_apply,
      Bool.not_false, Bool.not_true]
  all_goals rfl

/-- Endpoint-relative direction induced by the local occupied-left orientation
at the arc representative.  It is `true` when that representative direction
points away from this endpoint in the selected finite-arc order. -/
noncomputable def representativeOrientationPointsAway
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) : Bool :=
  B.arcCoordinateIncreases h.1.2 != B.halfEdgeEndpointSide h

/-- The endpoint-relative representative direction reverses when the same arc
is crossed. -/
theorem representativeOrientationPointsAway_crossHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (h : T.chartCuts.HalfEdge) :
    B.representativeOrientationPointsAway
        (T.chartCuts.crossHalfEdge h) =
      !B.representativeOrientationPointsAway h := by
  simp only [representativeOrientationPointsAway,
    T.chartCuts.crossHalfEdge_arc,
    B.halfEdgeEndpointSide_crossHalfEdge]
  generalize B.arcCoordinateIncreases h.1.2 = direction
  generalize B.halfEdgeEndpointSide h = side
  cases direction <;> cases side <;> rfl


/-- The sole endpoint condition still needed to orient the combinatorial
boundary walk: switching to the other incident arc reverses whether the
occupied-left direction points away from the common vertex. -/
def IsSwitchCompatible
    (B : OccupiedLeftArcBranchAssignment T) : Prop :=
  ∀ h : T.chartCuts.HalfEdge,
    B.representativeOrientationPointsAway
        (T.chartCuts.switchHalfEdge h) =
      !B.representativeOrientationPointsAway h

/-- Once endpoint switch compatibility is supplied, the switch followed by
crossing preserves the orientation state along every walk step. -/
theorem representativeOrientationPointsAway_walkStep
    (B : OccupiedLeftArcBranchAssignment T)
    (hB : B.IsSwitchCompatible)
    (h : T.chartCuts.HalfEdge) :
    B.representativeOrientationPointsAway (T.chartCuts.walkStep h) =
      B.representativeOrientationPointsAway h := by
  change B.representativeOrientationPointsAway
      (T.chartCuts.crossHalfEdge (T.chartCuts.switchHalfEdge h)) =
    B.representativeOrientationPointsAway h
  rw [B.representativeOrientationPointsAway_crossHalfEdge, hB]
  simp only [Bool.not_not]

theorem representativeOrientationPointsAway_iterate_walkStep
    (B : OccupiedLeftArcBranchAssignment T)
    (hB : B.IsSwitchCompatible)
    (h : T.chartCuts.HalfEdge) (n : ℕ) :
    B.representativeOrientationPointsAway
        (((T.chartCuts.walkStep :
          T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n]) h) =
      B.representativeOrientationPointsAway h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        B.representativeOrientationPointsAway_walkStep hB, ih]
/-- The unique half-edge of an arc from which its representative
occupied-left direction points away in the selected finite-arc order. -/
noncomputable def representativeOrientedHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) : T.chartCuts.HalfEdge :=
  T.chartCuts.endpointHalfEdge (e, !B.arcCoordinateIncreases e)

@[simp] theorem representativeOrientedHalfEdge_arc
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    (B.representativeOrientedHalfEdge e).1.2 = e :=
  T.chartCuts.endpointHalfEdge_arc _

@[simp] theorem representativeOrientationPointsAway_orientedHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    B.representativeOrientationPointsAway
        (B.representativeOrientedHalfEdge e) = true := by
  simp only [representativeOrientationPointsAway,
    representativeOrientedHalfEdge,
    T.chartCuts.endpointHalfEdge_arc,
    B.halfEdgeEndpointSide_endpointHalfEdge]
  generalize B.arcCoordinateIncreases e = direction
  cases direction <;> rfl

@[simp] theorem representativeOrientationPointsAway_cross_orientedHalfEdge
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex) :
    B.representativeOrientationPointsAway
        (T.chartCuts.crossHalfEdge
          (B.representativeOrientedHalfEdge e)) = false := by
  rw [B.representativeOrientationPointsAway_crossHalfEdge]
  simp only [B.representativeOrientationPointsAway_orientedHalfEdge,
    Bool.not_true]

theorem representativeOrientedHalfEdge_unique
    (B : OccupiedLeftArcBranchAssignment T)
    (e : T.chartCuts.ArcIndex)
    (h : T.chartCuts.HalfEdge)
    (harc : h.1.2 = e)
    (haway : B.representativeOrientationPointsAway h = true) :
    h = B.representativeOrientedHalfEdge e := by
  obtain ⟨⟨f, side⟩, rfl⟩ :=
    T.chartCuts.endpointHalfEdge_surjective h
  simp only [T.chartCuts.endpointHalfEdge_arc] at harc
  subst f
  simp only [representativeOrientationPointsAway,
    T.chartCuts.endpointHalfEdge_arc,
    B.halfEdgeEndpointSide_endpointHalfEdge] at haway
  have hside : side = !B.arcCoordinateIncreases e := by
    generalize B.arcCoordinateIncreases e = direction at haway ⊢
    cases direction <;> cases side <;> simp_all
  simp only [representativeOrientedHalfEdge, hside]
end OccupiedLeftArcBranchAssignment

/-- Every selected open finite arc has one occupied-left orientation in the
normalized left-to-right arc parameter.  Every local occupied-left chart at
every point computes that same direction, and endpoint-relative direction
reverses under `crossHalfEdge`.  Compatibility across a cut vertex is not
asserted by this topology-only contract. -/
def HasGloballyOrientedOpenArcs
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O) : Prop :=
  ∃ B : OccupiedLeftArcBranchAssignment T,
    (∀ e : T.chartCuts.ArcIndex,
      (B.arcCoordinateIncreases e = true ∧
          StrictMono (B.arcCoordinateNeighborhood e).unitParameter) ∨
        (B.arcCoordinateIncreases e = false ∧
          StrictAnti (B.arcCoordinateNeighborhood e).unitParameter)) ∧
    (∀ (e : T.chartCuts.ArcIndex)
      (p : CMVBoundaryLocalAtlas.FrontierSpace O)
      (hp : p ∈ T.chartCuts.finiteArcInterior e)
      (C : OccupiedLeftArcBranch O p.1)
      (N : OccupiedLeftArcCoordinateNeighborhood T e hp C),
      N.coordinateIncreases = B.arcCoordinateIncreases e) ∧
    ∀ h : T.chartCuts.HalfEdge,
      B.representativeOrientationPointsAway
          (T.chartCuts.crossHalfEdge h) =
        !B.representativeOrientationPointsAway h

theorem FinitePiecewiseRegularBoundaryTopology.hasGloballyOrientedOpenArcs
    {O : Set PlanePoint} (T : FinitePiecewiseRegularBoundaryTopology O) :
    HasGloballyOrientedOpenArcs T := by
  let B := T.occupiedLeftArcBranchAssignment
  refine ⟨B, ?_, ?_, B.representativeOrientationPointsAway_crossHalfEdge⟩
  · intro e
    cases hdirection : B.arcCoordinateIncreases e with
    | false =>
        refine Or.inr ⟨rfl, ?_⟩
        exact B.arcCoordinateIncreases_eq_false_unitParameter e hdirection
    | true =>
        refine Or.inl ⟨rfl, ?_⟩
        exact B.arcCoordinateIncreases_eq_true_unitParameter e hdirection
  · intro e p hp C N
    exact B.coordinateNeighborhood_increases_eq_arcCoordinateIncreases
      e p hp C N

end CMVRelaxation
