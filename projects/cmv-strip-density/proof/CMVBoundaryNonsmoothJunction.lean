/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryGraphAtlas
import CMVBoundaryLocalAtlasSpecimen
import CMVFigureFourBilateralExamples

/-!
# Ambient charts at nonsmooth two-arm junctions

Two source-local regular sublevel arms can meet at a genuine corner without the
union being a smooth domain.  This module joins their independently derived
implicit graphs and feeds the retained triangular graph flattening.  No joined
graph, ambient chart, global boundary trace, or normalized carrier is supplied.
-/

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace NonsmoothJunction

open CMVRelaxation.FiniteJunctionRepair
open CMVRelaxation.LocalChartPreservation
open SmoothGraphAtlas

/-- The actual joined graph derived from two regular negative-side vertical
sublevel germs.  The maximum is forced by union of the two occupied phases;
its value at the common endpoint is proved from the two implicit-function
outputs. -/
theorem exists_joinedGraph_of_two_negative_vertical_germs
    {A B U : Set PlanePoint} {p : PlanePoint}
    (first : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .negative A p)
    (second : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .negative B p)
    (occupied : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ A ∨ q ∈ B) :
    ∃ f : ℝ → ℝ, Continuous f ∧ f p.1 = p.2 ∧
      ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < f q.1 := by
  obtain ⟨f, hf, hfp, hA⟩ :=
    first.exists_vertical_graphDomain_germ
  obtain ⟨g, hg, hgp, hB⟩ :=
    second.exists_vertical_graphDomain_germ
  refine ⟨fun x => max (f x) (g x), hf.continuous.max hg.continuous, ?_, ?_⟩
  · change max (f p.1) (g p.1) = p.2
    rw [hfp, hgp, max_self]
  · filter_upwards [occupied, hA, hB] with q hU hqA hqB
    rw [hU, hqA, hqB]
    exact lt_max_iff.symm

/-- A local strict lower graph through its base point forces actual frontier
incidence.  The proof flattens the graph to a half-plane and transfers the
frontier back through the local set equality. -/
theorem mem_frontier_of_eventually_strictLowerGraph
    {U : Set PlanePoint} {p : PlanePoint} {f : ℝ → ℝ}
    (hf : Continuous f) (hfp : f p.1 = p.2)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q.2 < f q.1) :
    p ∈ frontier U := by
  let G : Set PlanePoint := {q | q.2 < f q.1}
  let K : PlanePoint ≃ₜ PlanePoint :=
    verticalGraphFlattening f hf p.1
  have hpreimage :
      K ⁻¹' OccupiedHalfPlane.lower.carrier = G := by
    ext q
    simp only [mem_preimage, OccupiedHalfPlane.carrier, mem_prod, mem_univ,
      mem_Iio, true_and, K, verticalGraphFlattening_apply, sub_lt_zero,
      G, mem_ofPred_eq]
  have hpG : p ∈ frontier G := by
    rw [← hpreimage, ← K.preimage_frontier,
      OccupiedHalfPlane.frontier_carrier]
    change verticalGraphFlattening f hf p.1 p ∈
      OccupiedHalfPlane.axis
    simp only [verticalGraphFlattening_apply, hfp, sub_self,
      OccupiedHalfPlane.axis, mem_prod, mem_univ, mem_singleton_iff,
      true_and]
  have hlocal' : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ G := by
    simpa only [G, mem_ofPred_eq] using hlocal
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hlocal'
  have hUW : U ∩ W = G ∩ W := by
    ext q
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hqU, hqW⟩
      exact ⟨(hWsub hqW).mp hqU, hqW⟩
    · rintro ⟨hqG, hqW⟩
      exact ⟨(hWsub hqW).mpr hqG, hqW⟩
  have hfrontier :
      frontier U ∩ W = frontier G ∩ W :=
    CMVRelaxation.frontier_inter_eq_of_inter_open_eq hWopen hUW
  have hpPair : p ∈ frontier G ∩ W := ⟨hpG, hpW⟩
  rw [← hfrontier] at hpPair
  exact hpPair.1

/-- The preceding frontier criterion is invariant under an ambient
homeomorphism, allowing the tangent-derived coordinate frame to be selected
before the implicit graph is constructed. -/
theorem mem_frontier_of_eventually_transformed_strictLowerGraph
    {U : Set PlanePoint} {p : PlanePoint} {f : ℝ → ℝ}
    (H : PlanePoint ≃ₜ PlanePoint)
    (hf : Continuous f) (hfp : f (H p).1 = (H p).2)
    (hlocal : ∀ᶠ q in 𝓝 p, q ∈ U ↔ (H q).2 < f (H q).1) :
    p ∈ frontier U := by
  let G : Set PlanePoint := {z | z.2 < f z.1}
  let M : Set PlanePoint := H ⁻¹' G
  have hpG : H p ∈ frontier G := by
    apply mem_frontier_of_eventually_strictLowerGraph hf hfp
    exact Filter.Eventually.of_forall (fun _ => Iff.rfl)
  have hpM : p ∈ frontier M := by
    change p ∈ frontier (H ⁻¹' G)
    rw [← H.preimage_frontier]
    exact hpG
  have hlocal' : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ M := by
    simpa only [M, G, mem_preimage, mem_ofPred_eq] using hlocal
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hlocal'
  have hUW : U ∩ W = M ∩ W := by
    ext q
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hqU, hqW⟩
      exact ⟨(hWsub hqW).mp hqU, hqW⟩
    · rintro ⟨hqM, hqW⟩
      exact ⟨(hWsub hqW).mpr hqM, hqW⟩
  have hfrontier :
      frontier U ∩ W = frontier M ∩ W :=
    CMVRelaxation.frontier_inter_eq_of_inter_open_eq hWopen hUW
  have hpPair : p ∈ frontier M ∩ W := ⟨hpM, hpW⟩
  rw [← hfrontier] at hpPair
  exact hpPair.1

/-- Forgetting the armwise smoothness only after the join gives the retained
continuous occupied-side graph germ. -/
theorem continuousGraphGerm_of_two_negative_vertical_germs
    {A B U : Set PlanePoint} {p : PlanePoint}
    (first : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .negative A p)
    (second : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .negative B p)
    (occupied : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ A ∨ q ∈ B) :
    HasContinuousGraphGermOnSide .vertical .negative U p := by
  obtain ⟨f, hf, _hfp, hlocal⟩ :=
    exists_joinedGraph_of_two_negative_vertical_germs first second occupied
  exact ⟨f, hf, hlocal⟩

/-- The epigraph analogue of `exists_joinedGraph_of_two_negative_vertical_germs`.
The minimum is forced by the union of two positive-side occupied phases. -/
theorem exists_joinedGraph_of_two_positive_vertical_germs
    {A B U : Set PlanePoint} {p : PlanePoint}
    (first : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .positive A p)
    (second : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .positive B p)
    (occupied : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ A ∨ q ∈ B) :
    ∃ f : ℝ → ℝ, Continuous f ∧ f p.1 = p.2 ∧
      ∀ᶠ q in 𝓝 p, q ∈ U ↔ f q.1 < q.2 := by
  obtain ⟨f, hf, hfp, hA⟩ :=
    first.exists_vertical_graphDomain_germ
  obtain ⟨g, hg, hgp, hB⟩ :=
    second.exists_vertical_graphDomain_germ
  refine ⟨fun x => min (f x) (g x), hf.continuous.min hg.continuous, ?_, ?_⟩
  · change min (f p.1) (g p.1) = p.2
    rw [hfp, hgp, min_self]
  · filter_upwards [occupied, hA, hB] with q hU hqA hqB
    rw [hU, hqA, hqB]
    exact min_lt_iff.symm

/-- Forgetting armwise smoothness after the positive-side join gives the
retained continuous epigraph germ. -/
theorem continuousGraphGerm_of_two_positive_vertical_germs
    {A B U : Set PlanePoint} {p : PlanePoint}
    (first : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .positive A p)
    (second : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .positive B p)
    (occupied : ∀ᶠ q in 𝓝 p, q ∈ U ↔ q ∈ A ∨ q ∈ B) :
    HasContinuousGraphGermOnSide .vertical .positive U p := by
  obtain ⟨f, hf, _hfp, hlocal⟩ :=
    exists_joinedGraph_of_two_positive_vertical_germs first second occupied
  exact ⟨f, hf, hlocal⟩

/-- Pull back a two-arm regular junction through an actual ambient coordinate
frame and construct the pointwise half-space chart.  The frame is applied only
to the two independently regular source arms; the nonlinear joined flattening
is derived here. -/
theorem PointwiseHalfSpaceChart.nonempty_of_two_negative_vertical_germs
    {A B U : Set PlanePoint} {p : PlanePoint}
    (H : PlanePoint ≃ₜ PlanePoint)
    (first : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .negative A (H p))
    (second : HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .negative B (H p))
    (occupied : ∀ᶠ q in 𝓝 p,
      q ∈ U ↔ H q ∈ A ∨ H q ∈ B)
    (hp : p ∈ frontier U) :
    Nonempty (PointwiseHalfSpaceChart U ⟨p, hp⟩) := by
  obtain ⟨f, hf, hfp, hjoined⟩ :=
    exists_joinedGraph_of_two_negative_vertical_germs first second
      (U := A ∪ B) (Filter.Eventually.of_forall fun q => by simp)
  have hjoinedPull : ∀ᶠ q in 𝓝 p,
      H q ∈ A ∪ B ↔ (H q).2 < f (H q).1 :=
    H.continuous.continuousAt.tendsto.eventually hjoined
  have hlocal : ∀ᶠ q in 𝓝 p,
      q ∈ U ↔ (H q).2 < f (H q).1 := by
    filter_upwards [occupied, hjoinedPull] with q hqU hqJoined
    exact hqU.trans (by simpa only [mem_union] using hqJoined)
  obtain ⟨W, hWsub, hWopen, hpW⟩ := _root_.mem_nhds_iff.mp hlocal
  let K : PlanePoint ≃ₜ PlanePoint :=
    H.trans (verticalGraphFlattening f hf (H p).1)
  exact ⟨PointwiseHalfSpaceChart.ofHomeomorph .lower K W hWopen hpW
    (by
      change verticalGraphFlattening f hf (H p).1 (H p) = (0, 0)
      simp only [verticalGraphFlattening_apply, sub_self, hfp,
        Prod.mk_zero_zero])
    (by
      intro q hq
      have hqModel := hWsub hq
      change verticalGraphFlattening f hf (H p).1 (H q) ∈
          OccupiedHalfPlane.lower.carrier ↔ q ∈ U
      simpa only [OccupiedHalfPlane.carrier, mem_prod, mem_univ, mem_Iio,
        true_and, verticalGraphFlattening_apply, sub_lt_zero] using
        hqModel.symm)⟩

/-- A continuous vertical graph germ at an actual frontier point supplies the
same ambient half-space chart as a smooth germ.  This is the junction-facing
adapter: no differentiability of the joined graph is required. -/
theorem PointwiseHalfSpaceChart.nonempty_ofContinuousVerticalGraphGerm
    {side : SpliceGraphOccupiedSide} {U : Set PlanePoint}
    {p : FrontierSpace U}
    (germ : HasContinuousGraphGermOnSide .vertical side U p.1) :
    Nonempty (PointwiseHalfSpaceChart U p) := by
  obtain ⟨f, hf, hfp, hlocal⟩ :=
    germ.exists_vertical_graph_eq_base p.2
  cases side with
  | negative =>
      obtain ⟨W, hWsub, hWopen, hpW⟩ :=
        _root_.mem_nhds_iff.mp hlocal
      exact ⟨PointwiseHalfSpaceChart.ofHomeomorph .lower
        (verticalGraphFlattening f hf p.1.1) W hWopen hpW
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
        (verticalGraphFlattening f hf p.1.1) W hWopen hpW
        (by simp only [verticalGraphFlattening_apply, sub_self,
          hfp, Prod.mk_zero_zero])
        (by
          intro q hq
          have hqModel := hWsub hq
          simpa only [OccupiedHalfPlane.carrier, mem_prod, mem_univ,
            mem_Ioi, true_and, verticalGraphFlattening_apply,
            sub_pos] using hqModel.symm)⟩

/-- A regular strict sublevel with positive transverse derivative supplies its
negative occupied-side implicit graph.  The graph is produced by the implicit
function theorem; it is not part of the input. -/
theorem regularSublevel_has_negative_vertical_germ
    (g : PlanePoint → ℝ) (p : PlanePoint)
    (hg : ContDiff ℝ ∞ g) (hgp : g p = 0)
    (htransverse : 0 < fderiv ℝ g p (0, 1)) :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      {q : PlanePoint | g q < 0} p := by
  obtain ⟨phi, hphi, hphip, hzero⟩ :=
    CMVRelaxation.exists_contDiff_infty_implicitGraph_of_contDiffOn
      isOpen_univ (mem_univ p) hg.contDiffOn htransverse.ne'
  refine ⟨g, phi, hg.contDiffAt, htransverse.ne', hphi, ?_, ?_,
    htransverse⟩
  · simpa only [hgp] using hphip
  · filter_upwards [hzero] with q hq
    exact ⟨Iff.rfl, by simpa only [hgp] using hq⟩

/-- A regular strict sublevel with negative transverse derivative supplies its
positive occupied-side implicit graph. -/
theorem regularSublevel_has_positive_vertical_germ
    (g : PlanePoint → ℝ) (p : PlanePoint)
    (hg : ContDiff ℝ ∞ g) (hgp : g p = 0)
    (htransverse : fderiv ℝ g p (0, 1) < 0) :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .positive
      {q : PlanePoint | g q < 0} p := by
  obtain ⟨phi, hphi, hphip, hzero⟩ :=
    CMVRelaxation.exists_contDiff_infty_implicitGraph_of_contDiffOn
      isOpen_univ (mem_univ p) hg.contDiffOn htransverse.ne
  refine ⟨g, phi, hg.contDiffAt, htransverse.ne, hphi, ?_, ?_,
    htransverse⟩
  · simpa only [hgp] using hphip
  · filter_upwards [hzero] with q hq
    exact ⟨Iff.rfl, by simpa only [hgp] using hq⟩

/-- Endpoint incidence is not a separate prerequisite: two regular sublevels
with a locally exhaustive occupied side force their common endpoint onto the
actual frontier. -/
theorem mem_frontier_of_two_regular_sublevels
    {U : Set PlanePoint} {p : PlanePoint}
    (H : PlanePoint ≃ₜ PlanePoint)
    (first second : PlanePoint → ℝ)
    (first_smooth : ContDiff ℝ ∞ first)
    (second_smooth : ContDiff ℝ ∞ second)
    (first_endpoint : first (H p) = 0)
    (second_endpoint : second (H p) = 0)
    (first_transverse :
      0 < fderiv ℝ first (H p) (0, 1))
    (second_transverse :
      0 < fderiv ℝ second (H p) (0, 1))
    (occupied : ∀ᶠ q in 𝓝 p,
      q ∈ U ↔ first (H q) < 0 ∨ second (H q) < 0) :
    p ∈ frontier U := by
  let A : Set PlanePoint := {z | first z < 0}
  let B : Set PlanePoint := {z | second z < 0}
  have firstGerm :
      HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
        A (H p) := by
    exact regularSublevel_has_negative_vertical_germ first (H p)
      first_smooth first_endpoint first_transverse
  have secondGerm :
      HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
        B (H p) := by
    exact regularSublevel_has_negative_vertical_germ second (H p)
      second_smooth second_endpoint second_transverse
  obtain ⟨f, hf, hfp, hjoined⟩ :=
    exists_joinedGraph_of_two_negative_vertical_germs firstGerm secondGerm
      (U := A ∪ B) (Filter.Eventually.of_forall fun q => by simp)
  have hjoinedPull : ∀ᶠ q in 𝓝 p,
      H q ∈ A ∪ B ↔ (H q).2 < f (H q).1 :=
    H.continuous.continuousAt.tendsto.eventually hjoined
  have hlocal : ∀ᶠ q in 𝓝 p,
      q ∈ U ↔ (H q).2 < f (H q).1 := by
    filter_upwards [occupied, hjoinedPull] with q hqU hqJoined
    exact hqU.trans (by simpa only [A, B, mem_union, mem_ofPred_eq]
      using hqJoined)
  exact mem_frontier_of_eventually_transformed_strictLowerGraph
    H hf hfp hlocal

/-- Complete nonsmooth-junction supplier from two actual regular defining
functions.  A coordinate frame, both defining functions, their endpoint
incidence and transverse regularity, local occupied-side exhaustion, and the
actual frontier incidence are the only inputs.  The two implicit graphs, their
continuous join, and the ambient half-space chart are all derived. -/
theorem PointwiseHalfSpaceChart.nonempty_of_two_regular_sublevels
    {U : Set PlanePoint} {p : PlanePoint}
    (H : PlanePoint ≃ₜ PlanePoint)
    (first second : PlanePoint → ℝ)
    (first_smooth : ContDiff ℝ ∞ first)
    (second_smooth : ContDiff ℝ ∞ second)
    (first_endpoint : first (H p) = 0)
    (second_endpoint : second (H p) = 0)
    (first_transverse :
      0 < fderiv ℝ first (H p) (0, 1))
    (second_transverse :
      0 < fderiv ℝ second (H p) (0, 1))
    (occupied : ∀ᶠ q in 𝓝 p,
      q ∈ U ↔ first (H q) < 0 ∨ second (H q) < 0)
    (hp : p ∈ frontier U) :
    Nonempty (PointwiseHalfSpaceChart U ⟨p, hp⟩) := by
  apply PointwiseHalfSpaceChart.nonempty_of_two_negative_vertical_germs
    H
    (regularSublevel_has_negative_vertical_germ first (H p)
      first_smooth first_endpoint first_transverse)
    (regularSublevel_has_negative_vertical_germ second (H p)
      second_smooth second_endpoint second_transverse)
    occupied

/-- Any chart produced by the nonsmooth supplier yields a genuine local
reparameterization of the complete actual frontier, with endpoint inclusion,
continuity, and no retracing. -/
theorem PointwiseHalfSpaceChart.exists_complete_local_frontier
    {U : Set PlanePoint} {p : {q : PlanePoint // q ∈ frontier U}}
    (hchart : Nonempty (PointwiseHalfSpaceChart U p)) :
    ∃ A : ActualFrontierIntervalChart U p,
      p.1 ∈ A.window ∧
      ContinuousOn A.trace (Ioo (-A.radius) A.radius) ∧
      Set.InjOn A.trace (Ioo (-A.radius) A.radius) ∧
      frontier U ∩ A.window =
        A.trace '' Ioo (-A.radius) A.radius := by
  rcases hchart with ⟨chart⟩
  rcases chart.exists_actualFrontierIntervalChart with ⟨A⟩
  exact ⟨A, A.base_mem_window, A.continuousOn_trace, A.injOn_trace,
    A.frontier_inter_window⟩

/-- The unsigned circle defining function is globally smooth. -/
theorem contDiff_circleValue (center : PlanePoint) (radius : ℝ) :
    ContDiff ℝ ∞ (CMVFigureFour.circleValue center radius) := by
  unfold CMVFigureFour.circleValue
  fun_prop

/-- The unsigned circle gradient in the upward transverse direction. -/
theorem fderiv_circleValue_snd
    (center p : PlanePoint) (radius : ℝ) :
    fderiv ℝ (CMVFigureFour.circleValue center radius) p (0, 1) =
      2 * (p.2 - center.2) := by
  have hfun : CMVFigureFour.circleValue center radius =
      CMVRelaxation.LocalChartPreservation.signedCircleValue
        CMVFigureFour.CircleSide.inside center radius := by
    funext q
    simp [CMVRelaxation.LocalChartPreservation.signedCircleValue,
      CMVFigureFour.CircleSide.sign]
  rw [hfun,
    CMVRelaxation.LocalChartPreservation.fderiv_signedCircleValue_snd]
  simp [CMVFigureFour.CircleSide.sign]

/-- A literal circle sublevel at a point above its center is a regular
negative-side vertical arm.  The transverse coordinate is selected from the
actual center-to-endpoint vector. -/
theorem circleSublevel_has_negative_vertical_germ
    (center p : PlanePoint) (radius : ℝ)
    (hcircle : CMVFigureFour.circleValue center radius p = 0)
    (habove : center.2 < p.2) :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      {q : PlanePoint |
        CMVFigureFour.circleValue center radius q < 0} p := by
  apply regularSublevel_has_negative_vertical_germ
  · have hfun : CMVFigureFour.circleValue center radius =
        CMVRelaxation.LocalChartPreservation.signedCircleValue
          CMVFigureFour.CircleSide.inside center radius := by
      funext q
      simp [CMVRelaxation.LocalChartPreservation.signedCircleValue,
        CMVFigureFour.CircleSide.sign]
    rw [hfun]
    exact CMVRelaxation.LocalChartPreservation.contDiff_signedCircleValue
      CMVFigureFour.CircleSide.inside center radius
  · exact hcircle
  · have hfun : CMVFigureFour.circleValue center radius =
        CMVRelaxation.LocalChartPreservation.signedCircleValue
          CMVFigureFour.CircleSide.inside center radius := by
      funext q
      simp [CMVRelaxation.LocalChartPreservation.signedCircleValue,
        CMVFigureFour.CircleSide.sign]
    rw [hfun,
      CMVRelaxation.LocalChartPreservation.fderiv_signedCircleValue_snd]
    simp only [CMVFigureFour.CircleSide.sign, one_mul]
    linarith

/-- A literal circle sublevel at a point below its center is a regular
positive-side vertical arm. -/
theorem circleSublevel_has_positive_vertical_germ
    (center p : PlanePoint) (radius : ℝ)
    (hcircle : CMVFigureFour.circleValue center radius p = 0)
    (hbelow : p.2 < center.2) :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .positive
      {q : PlanePoint |
        CMVFigureFour.circleValue center radius q < 0} p := by
  apply regularSublevel_has_positive_vertical_germ
  · exact contDiff_circleValue center radius
  · exact hcircle
  · rw [fderiv_circleValue_snd]
    linarith

/-- The affine defining function has unit derivative in its transverse
coordinate, independently of its tangent slope. -/
theorem fderiv_linearSublevel_snd
    (slope intercept : ℝ) (p : PlanePoint) :
    fderiv ℝ (fun q : PlanePoint =>
      q.2 + slope * q.1 - intercept) p (0, 1) = 1 := by
  let g : PlanePoint → ℝ := fun q => q.2 + slope * q.1 - intercept
  have hg : ContDiff ℝ ∞ g := by
    dsimp only [g]
    fun_prop
  have hdiff : DifferentiableAt ℝ g p := hg.differentiable (by simp) p
  have hline :
      HasDerivAt (fun y : ℝ => ((p.1, y) : PlanePoint)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt p.2 hline
  have heq : deriv (fun y : ℝ => g (p.1, y)) p.2 =
      fderiv ℝ g p (0, 1) := by
    simpa only [Function.comp_def] using hcomp.deriv
  rw [← heq]
  simp [g]

/-- A regular affine sublevel arm.  Its tangent, implicit graph, and occupied
side are all calculated from the literal affine defining function. -/
theorem linearSublevel_has_negative_vertical_germ
    (slope intercept : ℝ) {p : PlanePoint}
    (hp : p.2 + slope * p.1 = intercept) :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      {q : PlanePoint | q.2 + slope * q.1 < intercept} p := by
  let g : PlanePoint → ℝ := fun q => q.2 + slope * q.1 - intercept
  let phi : ℝ → ℝ := fun x => intercept - slope * x
  have hg : ContDiff ℝ ∞ g := by
    dsimp only [g]
    fun_prop
  have hphi : ContDiff ℝ ∞ phi := by
    dsimp only [phi]
    fun_prop
  have hderiv : fderiv ℝ g p (0, 1) = 1 := by
    exact fderiv_linearSublevel_snd slope intercept p
  refine ⟨g, phi, hg.contDiffAt, ?_, hphi, ?_, ?_, ?_⟩
  · rw [hderiv]
    norm_num
  · dsimp only [phi]
    linarith
  · filter_upwards [] with q
    constructor
    · change (q.2 + slope * q.1 < intercept) ↔
        q.2 + slope * q.1 - intercept < 0
      rw [sub_neg]
    · dsimp only [g, phi]
      constructor <;> intro h <;> linarith
  · rw [hderiv]
    norm_num

/-- Literal regular parameterization of the affine arm used above. -/
def linearBoundaryTrace (slope intercept : ℝ) (t : ℝ) : PlanePoint :=
  (t, intercept - slope * t)

/-- The affine arm has its calculated nonzero tangent everywhere. -/
theorem linearBoundaryTrace_hasDerivAt (slope intercept t : ℝ) :
    HasDerivAt (linearBoundaryTrace slope intercept) (1, -slope) t := by
  unfold linearBoundaryTrace
  convert (hasDerivAt_id t).prodMk
    ((hasDerivAt_const t intercept).sub
      ((hasDerivAt_const t slope).mul (hasDerivAt_id t))) using 1 <;> simp


/-- The diagonal tangent frame selected by the two outgoing shelf directions.
Its first coordinate separates the rays and its second coordinate is transverse
to both; no graph or chart is encoded in this frame. -/
def diagonalTangentFrame : PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.1 - q.2, (q.1 + q.2) / 2)
  invFun z := (z.2 + z.1 / 2, z.2 - z.1 / 2)
  left_inv q := by ext <;> dsimp <;> ring

  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop
/-- Endpoint-centered ambient frame.  Its transverse direction is the common
upward direction detected by the two actual center-to-junction normals. -/
def endpointTangentFrame (p : PlanePoint) : PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.1 - p.1, q.2 - p.2)
  invFun z := (z.1 + p.1, z.2 + p.2)
  left_inv q := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem endpointTangentFrame_apply (p q : PlanePoint) :
    endpointTangentFrame p q = (q.1 - p.1, q.2 - p.2) := rfl

@[simp] theorem endpointTangentFrame_self (p : PlanePoint) :
    endpointTangentFrame p p = (0, 0) := by
  simp [endpointTangentFrame]

/-- Circle values are preserved by translating both center and point into the
endpoint-selected tangent frame. -/
theorem circleValue_endpointTangentFrame
    (p center q : PlanePoint) (radius : ℝ) :
    CMVFigureFour.circleValue (endpointTangentFrame p center) radius
        (endpointTangentFrame p q) =
      CMVFigureFour.circleValue center radius q := by
  change ((q.1 - p.1 - (center.1 - p.1)) ^ 2 +
      (q.2 - p.2 - (center.2 - p.2)) ^ 2 - radius ^ 2) =
    (q.1 - center.1) ^ 2 + (q.2 - center.2) ^ 2 - radius ^ 2
  ring

@[simp] theorem diagonalTangentFrame_apply (q : PlanePoint) :
    diagonalTangentFrame q = (q.1 - q.2, (q.1 + q.2) / 2) := rfl


/-- A regular source-circle point away from the junction set supplies an
ambient chart on the AE-selected representative.  Horizontal circle tangencies
use the vertical graph; vertical tangencies use the horizontal graph. -/
theorem PointwiseHalfSpaceChart.nonempty_selected_of_locallyOneSided_circle
    {E U : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    (hEU : E =ᵐ[MeasureTheory.volume] U)
    (hradius : 0 < radius)
    (hcircle : CMVFigureFour.circleValue center radius p = 0)
    (hlocal : CMVFigureFour.LocallyOneSided U center radius p)
    (hp : p ∈ frontier (CMVRelaxation.aeOpenRepresentative E)) :
    Nonempty (PointwiseHalfSpaceChart
      (CMVRelaxation.aeOpenRepresentative E) ⟨p, hp⟩) := by
  by_cases hy : p.2 ≠ center.2
  · obtain ⟨side, germ⟩ :=
      exists_verticalOrientedSmoothGraphGerm_of_locallyOneSided_circle
        hcircle hy hlocal
    exact PointwiseHalfSpaceChart.nonempty_ofOrientedSmoothGraphGerm
      (HasOrientedSmoothBoundaryGraphGermOnSide.selected germ hEU)
  · have hyEq : p.2 = center.2 := not_ne_iff.mp hy
    have hx : p.1 ≠ center.1 := by
      intro hxEq
      have hsq : radius ^ 2 = 0 := by
        unfold CMVFigureFour.circleValue at hcircle
        rw [hxEq, hyEq] at hcircle
        simpa using hcircle.symm
      exact (sq_pos_of_pos hradius).ne' hsq
    obtain ⟨side, germ⟩ :=
      exists_horizontalOrientedSmoothGraphGerm_of_locallyOneSided_circle
        hcircle hx hlocal
    exact PointwiseHalfSpaceChart.nonempty_ofOrientedSmoothGraphGerm
      (HasOrientedSmoothBoundaryGraphGermOnSide.selected germ hEU)

/-- The only nonsmooth inputs needed to complete a bilateral four-circle
source atlas: one continuous vertical graph germ at each actual junction.
The graph side may differ pointwise, so upper and lower contacts and the
radius-one tangency branch share the same contract. -/
structure BilateralJunctionGraphGerms {lam : ℝ}
    (g : CMVFigureFour.BilateralSourceIncidence lam) : Prop where
  upperLeft : ∃ side : SpliceGraphOccupiedSide,
    HasContinuousGraphGermOnSide .vertical side
      g.representative g.upperLeft
  upperRight : ∃ side : SpliceGraphOccupiedSide,
    HasContinuousGraphGermOnSide .vertical side
      g.representative g.upperRight
  lowerLeft : ∃ side : SpliceGraphOccupiedSide,
    HasContinuousGraphGermOnSide .vertical side
      g.representative g.lowerLeft
  lowerRight : ∃ side : SpliceGraphOccupiedSide,
    HasContinuousGraphGermOnSide .vertical side
      g.representative g.lowerRight


/-- Literal occupied-side exhaustion at the four junctions.  Unlike
`BilateralJunctionGraphGerms`, this contains no graph or chart: each field
speaks only about the actual representative and its two incident circle
sublevels. -/
structure BilateralJunctionCircleOccupancy {lam : ℝ}
    (g : CMVFigureFour.BilateralSourceIncidence lam) : Prop where
  upperLeft : ∀ᶠ q in 𝓝 g.upperLeft,
    q ∈ g.representative ↔
      CMVFigureFour.circleValue g.upperCenter g.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue g.leftStripCenter g.sourceRadius q < 0
  upperRight : ∀ᶠ q in 𝓝 g.upperRight,
    q ∈ g.representative ↔
      CMVFigureFour.circleValue g.upperCenter g.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue g.rightStripCenter g.sourceRadius q < 0
  lowerLeft : ∀ᶠ q in 𝓝 g.lowerLeft,
    q ∈ g.representative ↔
      CMVFigureFour.circleValue g.lowerCenter g.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue g.leftStripCenter g.sourceRadius q < 0
  lowerRight : ∀ᶠ q in 𝓝 g.lowerRight,
    q ∈ g.representative ↔
      CMVFigureFour.circleValue g.lowerCenter g.sourceRadius q < 0 ∨
        CMVFigureFour.circleValue g.rightStripCenter g.sourceRadius q < 0

/-- The four literal circle-sublevel exhaustions derive all four continuous
junction graphs.  Upper contacts join two hypographs by `max`; lower contacts
join two epigraphs by `min`. -/
theorem BilateralJunctionCircleOccupancy.toJunctionGraphGerms
    {lam : ℝ} {g : CMVFigureFour.BilateralSourceIncidence lam}
    (occupied : BilateralJunctionCircleOccupancy g) :
    BilateralJunctionGraphGerms g := by
  have hcenters := g.toSourceGeometry.horizontal_center_symmetry
  have hleftY : g.leftStripCenter.2 = 0 := hcenters.1
  have hrightY : g.rightStripCenter.2 = 0 := hcenters.2.1
  have hUpperCenter : g.upperCenter.2 < 1 := by
    have hsnell := g.upper_left_signed_snell
    rw [hleftY] at hsnell
    field_simp [ne_of_gt g.sourceRadius_pos] at hsnell
    nlinarith [g.density_jump]
  have hLowerCenter : -1 < g.lowerCenter.2 := by
    have hsnell := g.lower_left_signed_snell
    rw [hleftY] at hsnell
    field_simp [ne_of_gt g.sourceRadius_pos] at hsnell
    nlinarith [g.density_jump]
  refine {
    upperLeft := ⟨.negative,
      continuousGraphGerm_of_two_negative_vertical_germs
        (circleSublevel_has_negative_vertical_germ
          g.upperCenter g.upperLeft g.sourceRadius
          g.upperLeft_mem_upper.1 (by
            rw [g.upperLeft_height]
            exact hUpperCenter))
        (circleSublevel_has_negative_vertical_germ
          g.leftStripCenter g.upperLeft g.sourceRadius
          g.upperLeft_mem_left.1 (by
            rw [g.upperLeft_height, hleftY]
            norm_num))
        occupied.upperLeft⟩
    upperRight := ⟨.negative,
      continuousGraphGerm_of_two_negative_vertical_germs
        (circleSublevel_has_negative_vertical_germ
          g.upperCenter g.upperRight g.sourceRadius
          g.upperRight_mem_upper.1 (by
            rw [g.upperRight_height]
            exact hUpperCenter))
        (circleSublevel_has_negative_vertical_germ
          g.rightStripCenter g.upperRight g.sourceRadius
          g.upperRight_mem_right.1 (by
            rw [g.upperRight_height, hrightY]
            norm_num))
        occupied.upperRight⟩
    lowerLeft := ⟨.positive,
      continuousGraphGerm_of_two_positive_vertical_germs
        (circleSublevel_has_positive_vertical_germ
          g.lowerCenter g.lowerLeft g.sourceRadius
          g.lowerLeft_mem_lower.1 (by
            rw [g.lowerLeft_height]
            exact hLowerCenter))
        (circleSublevel_has_positive_vertical_germ
          g.leftStripCenter g.lowerLeft g.sourceRadius
          g.lowerLeft_mem_left.1 (by
            rw [g.lowerLeft_height, hleftY]
            norm_num))
        occupied.lowerLeft⟩
    lowerRight := ⟨.positive,
      continuousGraphGerm_of_two_positive_vertical_germs
        (circleSublevel_has_positive_vertical_germ
          g.lowerCenter g.lowerRight g.sourceRadius
          g.lowerRight_mem_lower.1 (by
            rw [g.lowerRight_height]
            exact hLowerCenter))
        (circleSublevel_has_positive_vertical_germ
          g.rightStripCenter g.lowerRight g.sourceRadius
          g.lowerRight_mem_right.1 (by
            rw [g.lowerRight_height, hrightY]
            norm_num))
        occupied.lowerRight⟩
  }
/-- Regular circle points and the four derived junction germs together cover
every point of the complete selected frontier.  This is the source-facing
applicability bridge; it assumes neither global smoothness nor a boundary
curve, and coordinate tangencies are retained. -/
theorem BilateralJunctionGraphGerms.selected_pointwiseChart_nonempty
    {lam : ℝ} {E : Set PlanePoint}
    {g : CMVFigureFour.BilateralSourceIncidence lam}
    (J : BilateralJunctionGraphGerms g)
    (hEU : E =ᵐ[MeasureTheory.volume] g.representative)
    (p : FrontierSpace (CMVRelaxation.aeOpenRepresentative E)) :
    Nonempty (PointwiseHalfSpaceChart
      (CMVRelaxation.aeOpenRepresentative E) p) := by
  rcases p with ⟨p, hp⟩
  have hpRepresentative : p ∈ frontier g.representative :=
    CMVRelaxation.frontier_aeOpenRepresentative_subset_frontier_open
      g.sourceRepresentative.representative_open hEU hp
  by_cases hUpperLeft : p = g.upperLeft
  · subst p
    obtain ⟨side, germ⟩ := J.upperLeft
    exact PointwiseHalfSpaceChart.nonempty_ofContinuousVerticalGraphGerm
      (germ.selected hEU)
  by_cases hUpperRight : p = g.upperRight
  · subst p
    obtain ⟨side, germ⟩ := J.upperRight
    exact PointwiseHalfSpaceChart.nonempty_ofContinuousVerticalGraphGerm
      (germ.selected hEU)
  by_cases hLowerLeft : p = g.lowerLeft
  · subst p
    obtain ⟨side, germ⟩ := J.lowerLeft
    exact PointwiseHalfSpaceChart.nonempty_ofContinuousVerticalGraphGerm
      (germ.selected hEU)
  by_cases hLowerRight : p = g.lowerRight
  · subst p
    obtain ⟨side, germ⟩ := J.lowerRight
    exact PointwiseHalfSpaceChart.nonempty_ofContinuousVerticalGraphGerm
      (germ.selected hEU)
  rw [g.frontier_eq_four_circles] at hpRepresentative
  rcases hpRepresentative with hpABC | hpRight
  · rcases hpABC with hpAB | hpLeft
    · rcases hpAB with hpUpper | hpLower
      · exact PointwiseHalfSpaceChart.nonempty_selected_of_locallyOneSided_circle
          hEU g.sourceRadius_pos hpUpper.1
            (g.upper_one_sided p hpUpper hUpperLeft hUpperRight) hp
      · exact PointwiseHalfSpaceChart.nonempty_selected_of_locallyOneSided_circle
          hEU g.sourceRadius_pos hpLower.1
            (g.lower_one_sided p hpLower hLowerLeft hLowerRight) hp
    · exact PointwiseHalfSpaceChart.nonempty_selected_of_locallyOneSided_circle
        hEU g.sourceRadius_pos hpLeft.1
          (g.left_one_sided p hpLeft hUpperLeft hLowerLeft) hp
  · exact PointwiseHalfSpaceChart.nonempty_selected_of_locallyOneSided_circle
      hEU g.sourceRadius_pos hpRight.1
        (g.right_one_sided p hpRight hUpperRight hLowerRight) hp

/-- Choice-free hypotheses yield the actual selected pointwise atlas; the only
choice is the standard packaging of each already-proved nonempty chart. -/
noncomputable def BilateralJunctionGraphGerms.selectedBoundaryHalfSpaceAtlas
    {lam : ℝ} {E : Set PlanePoint}
    {g : CMVFigureFour.BilateralSourceIncidence lam}
    (J : BilateralJunctionGraphGerms g)
    (hEU : E =ᵐ[MeasureTheory.volume] g.representative) :
    BoundaryHalfSpaceAtlas (CMVRelaxation.aeOpenRepresentative E) where
  chart := fun p => Classical.choice (J.selected_pointwiseChart_nonempty hEU p)

namespace ShelfApplication

/-- In the tangent-derived diagonal frame, the vertical and horizontal shelf
arms are two independently regular negative sublevels. -/
def verticalArmPhase : Set PlanePoint :=
  {z | z.2 + (1 / 2 : ℝ) * z.1 < 1}

def horizontalArmPhase : Set PlanePoint :=
  {z | z.2 + (-1 / 2 : ℝ) * z.1 < 1}

/-- Local occupied-side exhaustion at the actual reentrant corner, derived by
unfolding the two literal open rectangles. -/
theorem eventually_carrier_iff_diagonal_arm_phases :
    ∀ᶠ q in 𝓝 ((1, 1) : PlanePoint),
      q ∈ CMVBoundaryLocalAtlas.StepPolygon.carrier ↔
        diagonalTangentFrame q ∈ verticalArmPhase ∨
          diagonalTangentFrame q ∈ horizontalArmPhase := by
  have hbox : Ioo (0 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 2 ∈
      𝓝 ((1, 1) : PlanePoint) :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds (by norm_num)
  filter_upwards [hbox] with q hq
  rcases hq with ⟨⟨hx0, hx2⟩, hy0, hy2⟩
  simp only [CMVBoundaryLocalAtlas.StepPolygon.mem_carrier,
    verticalArmPhase, horizontalArmPhase,
    diagonalTangentFrame_apply, mem_ofPred_eq]
  constructor
  · rintro (hlower | hleft)
    · right
      convert hlower.2.2.2 using 1
      ring
    · left
      convert hleft.2.1 using 1
      ring
  · rintro (hvertical | hhorizontal)
    · apply Or.inr
      refine ⟨hx0, ?_, hy0, hy2⟩
      convert hvertical using 1
      ring
    · apply Or.inl
      refine ⟨hx0, hx2, hy0, ?_⟩
      convert hhorizontal using 1
      ring

/-- First actual shelf arm regularity, including its calculated tangent, in the
separating diagonal frame. -/
theorem verticalArmPhase_regular_germ :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      verticalArmPhase (diagonalTangentFrame (1, 1)) := by
  apply linearSublevel_has_negative_vertical_germ (1 / 2) 1
  norm_num [diagonalTangentFrame]

/-- Second actual shelf arm regularity in the same derived frame. -/
theorem horizontalArmPhase_regular_germ :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      horizontalArmPhase (diagonalTangentFrame (1, 1)) := by
  apply linearSublevel_has_negative_vertical_germ (-1 / 2) 1
  norm_num [diagonalTangentFrame]

/-- Both actual outgoing shelf traces meet at the transformed reentrant
endpoint; their tangent rays are distinct. -/
theorem transformed_shelf_arms_endpoint_and_tangent_separation :
    linearBoundaryTrace (1 / 2) 1 0 =
        diagonalTangentFrame ((1, 1) : PlanePoint) ∧
      linearBoundaryTrace (-1 / 2) 1 0 =
        diagonalTangentFrame ((1, 1) : PlanePoint) ∧
      (1, -(1 / 2 : ℝ)) ≠ (1, -(-1 / 2 : ℝ)) := by
  constructor
  · norm_num [linearBoundaryTrace, diagonalTangentFrame]
  constructor
  · norm_num [linearBoundaryTrace, diagonalTangentFrame]
  · norm_num

/-- The common nonsmooth supplier constructs an ambient occupied-half-space
chart at the literal reentrant shelf corner.  This proof does not consume the
specimen's pre-existing `reentrantCornerChart` or `boundaryAtlas`. -/
theorem reentrantPoint_chart_nonempty_of_actual_regular_arms :
    Nonempty (PointwiseHalfSpaceChart
      CMVBoundaryLocalAtlas.StepPolygon.carrier
      CMVBoundaryLocalAtlas.StepPolygon.reentrantPoint) := by
  apply PointwiseHalfSpaceChart.nonempty_of_two_regular_sublevels
    diagonalTangentFrame
    (fun z : PlanePoint => z.2 + (1 / 2 : ℝ) * z.1 - 1)
    (fun z : PlanePoint => z.2 + (-1 / 2 : ℝ) * z.1 - 1)
  · fun_prop
  · fun_prop
  · norm_num [diagonalTangentFrame]
  · norm_num [diagonalTangentFrame]
  · rw [fderiv_linearSublevel_snd]
    norm_num
  · rw [fderiv_linearSublevel_snd]
    norm_num
  · simpa only [verticalArmPhase, horizontalArmPhase, mem_ofPred_eq,
      sub_neg] using eventually_carrier_iff_diagonal_arm_phases

/-- The derived shelf chart supplies a non-retracing parameterization of the
complete actual frontier in a neighborhood of the reentrant corner. -/
theorem reentrantPoint_complete_local_frontier :
    ∃ A : ActualFrontierIntervalChart
        CMVBoundaryLocalAtlas.StepPolygon.carrier
        CMVBoundaryLocalAtlas.StepPolygon.reentrantPoint,
      CMVBoundaryLocalAtlas.StepPolygon.reentrantPoint.1 ∈ A.window ∧
      ContinuousOn A.trace (Ioo (-A.radius) A.radius) ∧
      Set.InjOn A.trace (Ioo (-A.radius) A.radius) ∧
      frontier CMVBoundaryLocalAtlas.StepPolygon.carrier ∩ A.window =
        A.trace '' Ioo (-A.radius) A.radius :=
  PointwiseHalfSpaceChart.exists_complete_local_frontier
    reentrantPoint_chart_nonempty_of_actual_regular_arms

end ShelfApplication

namespace RadiusTwoSourceApplication

/-- The literal translated strict source used by the downstream placement
contract. -/
abbrev source : CMVFigureFour.BilateralSourceIncidence 2 :=
  CMVFigureFour.Examples.strictBilateralSourceAt (-3)

abbrev junction : PlanePoint := source.upperLeft

/-- Upper-cap and left-strip circle phases in the endpoint-centered frame. -/
def upperPhase (z : PlanePoint) : ℝ :=
  CMVFigureFour.circleValue
    (endpointTangentFrame junction source.upperCenter)
    source.sourceRadius z

def leftPhase (z : PlanePoint) : ℝ :=
  CMVFigureFour.circleValue
    (endpointTangentFrame junction source.leftStripCenter)
    source.sourceRadius z

@[simp] theorem source_radius : source.sourceRadius = 2 := by
  exact CMVFigureFour.Examples.strictBilateralSourceAt_sourceRadius (-3)

theorem leftStripCenter_y : source.leftStripCenter.2 = 0 := by
  simp [source, CMVFigureFour.Examples.strictBilateralSourceAt,
    CMVFigureFour.BilateralSourceIncidence.horizontalTranslate,
    CMVFigureFour.Examples.strictBilateralSource,
    CMVFigureFour.BilateralSourceIncidence.ofFourArcCandidate]

theorem junction_y : junction.2 = 1 :=
  source.upperLeft_height

/-- The strict lambda-two Snell incidence places the upper circle center
strictly below the junction; no graph orientation is assumed. -/
theorem upperCenter_y : source.upperCenter.2 = 1 / 2 := by
  have hsnell := source.upper_left_signed_snell
  rw [leftStripCenter_y, source_radius] at hsnell
  norm_num at hsnell ⊢
  linarith

theorem transformed_upperCenter_below :
    (endpointTangentFrame junction source.upperCenter).2 < 0 := by
  rw [endpointTangentFrame_apply]
  dsimp only
  rw [junction_y, upperCenter_y]
  norm_num

theorem transformed_leftStripCenter_below :
    (endpointTangentFrame junction source.leftStripCenter).2 < 0 := by
  rw [endpointTangentFrame_apply]
  dsimp only
  rw [junction_y, leftStripCenter_y]
  norm_num

/-- The two actual circle normals have distinct vertical components at the
junction, recording genuine tangent separation before graph construction. -/
theorem actual_normal_separation :
    junction.2 - source.upperCenter.2 ≠
      junction.2 - source.leftStripCenter.2 := by
  rw [junction_y, upperCenter_y, leftStripCenter_y]
  norm_num

theorem upperPhase_endpoint : upperPhase (0, 0) = 0 := by
  rw [show (0, 0) = endpointTangentFrame junction junction by
    symm; exact endpointTangentFrame_self junction]
  exact (circleValue_endpointTangentFrame junction source.upperCenter
    junction source.sourceRadius).trans source.upperLeft_mem_upper.1

theorem leftPhase_endpoint : leftPhase (0, 0) = 0 := by
  rw [show (0, 0) = endpointTangentFrame junction junction by
    symm; exact endpointTangentFrame_self junction]
  exact (circleValue_endpointTangentFrame junction source.leftStripCenter
    junction source.sourceRadius).trans source.upperLeft_mem_left.1

theorem upperPhase_smooth : ContDiff ℝ ∞ upperPhase :=
  contDiff_circleValue
    (endpointTangentFrame junction source.upperCenter) source.sourceRadius

theorem leftPhase_smooth : ContDiff ℝ ∞ leftPhase :=
  contDiff_circleValue
    (endpointTangentFrame junction source.leftStripCenter) source.sourceRadius

theorem upperPhase_transverse :
    0 < fderiv ℝ upperPhase (0, 0) (0, 1) := by
  unfold upperPhase
  rw [fderiv_circleValue_snd]
  linarith [transformed_upperCenter_below]

theorem leftPhase_transverse :
    0 < fderiv ℝ leftPhase (0, 0) (0, 1) := by
  unfold leftPhase
  rw [fderiv_circleValue_snd]
  linarith [transformed_leftStripCenter_below]

/-- Actual upper-cap regularity at the radius-two junction, derived from its
literal circle trace incidence and center-to-endpoint normal. -/
theorem upperPhase_regular_germ :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      {z : PlanePoint | upperPhase z < 0} (0, 0) := by
  exact circleSublevel_has_negative_vertical_germ
    (endpointTangentFrame junction source.upperCenter) (0, 0)
      source.sourceRadius upperPhase_endpoint transformed_upperCenter_below

/-- Actual left-strip regularity at the same radius-two junction. -/
theorem leftPhase_regular_germ :
    HasOrientedSmoothBoundaryGraphGermOnSide .vertical .negative
      {z : PlanePoint | leftPhase z < 0} (0, 0) := by
  exact circleSublevel_has_negative_vertical_germ
    (endpointTangentFrame junction source.leftStripCenter) (0, 0)
      source.sourceRadius leftPhase_endpoint transformed_leftStripCenter_below

/-- The occupied-side germ and actual regular circle incidences force the
source junction onto the frontier.  No global frontier trace is used. -/
theorem junction_mem_frontier
    (occupied : ∀ᶠ q in 𝓝 junction,
      q ∈ source.representative ↔
        upperPhase (endpointTangentFrame junction q) < 0 ∨
          leftPhase (endpointTangentFrame junction q) < 0) :
    junction ∈ frontier source.representative := by
  apply mem_frontier_of_two_regular_sublevels
    (endpointTangentFrame junction) upperPhase leftPhase
    upperPhase_smooth leftPhase_smooth
  · simpa only [endpointTangentFrame_self] using upperPhase_endpoint
  · simpa only [endpointTangentFrame_self] using leftPhase_endpoint
  · simpa only [endpointTangentFrame_self] using upperPhase_transverse
  · simpa only [endpointTangentFrame_self] using leftPhase_transverse
  · exact occupied

/-- Instantiation of the common ambient supplier at the literal lambda-two,
radius-two source junction.  The remaining premise is exactly the local
occupied-side datum: no junction graph, chart, normalized carrier, or global
trace is accepted. -/
theorem upperLeft_chart_of_actual_occupied_side
    (occupied : ∀ᶠ q in 𝓝 junction,
      q ∈ source.representative ↔
        upperPhase (endpointTangentFrame junction q) < 0 ∨
          leftPhase (endpointTangentFrame junction q) < 0) :
    Nonempty (PointwiseHalfSpaceChart source.representative
      ⟨junction, junction_mem_frontier occupied⟩) := by
  apply PointwiseHalfSpaceChart.nonempty_of_two_regular_sublevels
    (endpointTangentFrame junction) upperPhase leftPhase
    upperPhase_smooth leftPhase_smooth
  · simpa only [endpointTangentFrame_self] using upperPhase_endpoint
  · simpa only [endpointTangentFrame_self] using leftPhase_endpoint
  · simpa only [endpointTangentFrame_self] using upperPhase_transverse
  · simpa only [endpointTangentFrame_self] using leftPhase_transverse
  · exact occupied

/-- The source instantiation also returns a non-retracing local
reparameterization whose image exhausts the actual frontier in its window. -/
theorem upperLeft_complete_local_frontier_of_actual_occupied_side
    (occupied : ∀ᶠ q in 𝓝 junction,
      q ∈ source.representative ↔
        upperPhase (endpointTangentFrame junction q) < 0 ∨
          leftPhase (endpointTangentFrame junction q) < 0) :
    ∃ A : ActualFrontierIntervalChart source.representative
        ⟨junction, junction_mem_frontier occupied⟩,
      junction ∈ A.window ∧
      ContinuousOn A.trace (Ioo (-A.radius) A.radius) ∧
      Set.InjOn A.trace (Ioo (-A.radius) A.radius) ∧
      frontier source.representative ∩ A.window =
        A.trace '' Ioo (-A.radius) A.radius :=
  PointwiseHalfSpaceChart.exists_complete_local_frontier
    (upperLeft_chart_of_actual_occupied_side occupied)

end RadiusTwoSourceApplication

end NonsmoothJunction
end CMVBoundaryLocalAtlas
