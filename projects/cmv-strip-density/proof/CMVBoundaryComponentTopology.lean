/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryLocalAtlas
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Component topology from the local boundary atlas

The pointwise ambient half-space charts induce genuine one-dimensional charts
on the subtype of the actual frontier.  Consequently that frontier is locally
path connected.  For bounded carriers, its connected components are compact,
path connected, relatively clopen, and finite in number.  The finiteness is a
compactness consequence; no component list, global walk, or boundary ordering
is supplied.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

/-- The actual complete frontier, carrying its subspace topology. -/
abbrev FrontierSpace (O : Set PlanePoint) :=
  {q : PlanePoint // q ∈ frontier O}

namespace ActualFrontierIntervalChart

variable {O : Set PlanePoint} {p : FrontierSpace O}

/-- The portion of the frontier subtype lying in an actual interval chart. -/
def localDomain (A : ActualFrontierIntervalChart O p) : Set (FrontierSpace O) :=
  {q | q.1 ∈ A.window}

/-- The open parameter interval of an actual frontier chart. -/
def parameterInterval (A : ActualFrontierIntervalChart O p) : Set ℝ :=
  Ioo (-A.radius) A.radius

/-- The chart domain is open in the actual frontier. -/
theorem isOpen_localDomain (A : ActualFrontierIntervalChart O p) :
    IsOpen A.localDomain := by
  exact A.isOpen_window.preimage continuous_subtype_val

/-- The chart base lies in its frontier-subtype domain. -/
theorem base_mem_localDomain (A : ActualFrontierIntervalChart O p) :
    p ∈ A.localDomain :=
  A.base_mem_window

/-- The chart domain is nonempty, independently of any global component
assumption. -/
theorem localDomain_nonempty (A : ActualFrontierIntervalChart O p) :
    A.localDomain.Nonempty :=
  ⟨p, A.base_mem_localDomain⟩

/-- The parameter interval is nonempty because the selected chart radius is
strictly positive. -/
theorem parameterInterval_nonempty (A : ActualFrontierIntervalChart O p) :
    A.parameterInterval.Nonempty :=
  nonempty_Ioo.2 (neg_lt_self A.radius_pos)

private theorem coordFst_mem_parameterInterval
    (A : ActualFrontierIntervalChart O p) (q : A.localDomain) :
    (A.ambient.coord q.1.1).1 ∈ A.parameterInterval := by
  have hqWindow : q.1.1 ∈ A.window := q.2
  have hqBall : A.ambient.coord q.1.1 ∈ Metric.ball (0, 0) A.radius := hqWindow.2
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hqBall
  simpa only [parameterInterval, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hqBall.1

private theorem trace_mem_frontier_window
    (A : ActualFrontierIntervalChart O p) (t : A.parameterInterval) :
    A.trace t.1 ∈ frontier O ∩ A.window := by
  rw [A.frontier_inter_window]
  exact ⟨t.1, t.2, rfl⟩

/-- The local frontier portion is genuinely homeomorphic to an open real
interval.  This packages the no-retracing and no-branching content already
forced by the ambient half-space chart. -/
noncomputable def parameterHomeomorph
    (A : ActualFrontierIntervalChart O p) :
    A.localDomain ≃ₜ A.parameterInterval where
  toFun q := ⟨(A.ambient.coord q.1.1).1, A.coordFst_mem_parameterInterval q⟩
  invFun t :=
    ⟨⟨A.trace t.1, (A.trace_mem_frontier_window t).1⟩,
      (A.trace_mem_frontier_window t).2⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Subtype.ext
    change A.trace (A.ambient.coord q.1.1).1 = q.1.1
    have hqWindow : q.1.1 ∈ A.window := q.2
    have hqAxis : A.ambient.coord q.1.1 ∈ OccupiedHalfPlane.axis :=
      (A.ambient.frontier_image.apply_mem_iff hqWindow.1).2 q.1.2
    have hcoords :
        ((A.ambient.coord q.1.1).1, 0) = A.ambient.coord q.1.1 :=
      Prod.ext rfl hqAxis.2.symm
    unfold trace
    rw [hcoords]
    exact A.ambient.coord.left_inv hqWindow.1
  right_inv := by
    intro t
    apply Subtype.ext
    have htTarget : (t.1, 0) ∈ A.ambient.coord.target :=
      A.axisPoint_mem_target t.2
    exact congrArg Prod.fst (A.ambient.coord.right_inv htTarget)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_fst.comp
    exact A.ambient.coord.continuousOn_toFun.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun q => (show q.1.1 ∈ A.window from q.2).1)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact A.continuousOn_trace.comp_continuous continuous_subtype_val
      (fun t => t.2)

/-- The preceding local homeomorphism, extended only across its two open
subtypes, is an open partial homeomorphism from the complete frontier to `ℝ`. -/
noncomputable def frontierChart
    (A : ActualFrontierIntervalChart O p) :
    OpenPartialHomeomorph (FrontierSpace O) ℝ := by
  let S : TopologicalSpace.Opens (FrontierSpace O) :=
    ⟨A.localDomain, A.isOpen_localDomain⟩
  let T : TopologicalSpace.Opens ℝ :=
    ⟨A.parameterInterval, isOpen_Ioo⟩
  exact (S.openPartialHomeomorphSubtypeCoe
      (Set.nonempty_coe_sort.mpr A.localDomain_nonempty)).symm |>.trans
    (A.parameterHomeomorph.toOpenPartialHomeomorph.trans
      (T.openPartialHomeomorphSubtypeCoe
        (Set.nonempty_coe_sort.mpr A.parameterInterval_nonempty)))

/-- Each actual chart domain is connected.  This is a local consequence of
its homeomorphism with a nonempty open real interval, not a global component
assumption. -/
theorem isConnected_localDomain
    (A : ActualFrontierIntervalChart O p) :
    IsConnected A.localDomain := by
  rw [isConnected_iff_connectedSpace]
  exact A.parameterHomeomorph.connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp
      (isConnected_Ioo (neg_lt_self A.radius_pos)))

/-- The whole local interval lies in the actual frontier component through its
base point.  Thus a component cannot branch away inside a chart. -/
theorem localDomain_subset_connectedComponent
    (A : ActualFrontierIntervalChart O p) :
    A.localDomain ⊆ connectedComponent p :=
  A.isConnected_localDomain.subset_connectedComponent A.base_mem_localDomain

/-- The parameter interval of an actual chart is never compact. -/
theorem parameterInterval_not_isCompact
    (A : ActualFrontierIntervalChart O p) :
    ¬ IsCompact A.parameterInterval := by
  change ¬ IsCompact (Ioo (-A.radius) A.radius)
  rw [isCompact_Ioo_iff]
  exact not_le_of_gt (neg_lt_self A.radius_pos)

/-- The chart origin as a point of its open parameter interval. -/
def zeroParameter (A : ActualFrontierIntervalChart O p) :
    A.parameterInterval :=
  ⟨0, by exact ⟨neg_neg_of_pos A.radius_pos, A.radius_pos⟩⟩

/-- The actual frontier base, regarded as a point of the local chart domain. -/
def baseInLocalDomain (A : ActualFrontierIntervalChart O p) :
    A.localDomain :=
  ⟨p, A.base_mem_localDomain⟩

/-- The base maps to the chart origin. -/
@[simp] theorem parameterHomeomorph_base
    (A : ActualFrontierIntervalChart O p) :
    A.parameterHomeomorph A.baseInLocalDomain = A.zeroParameter := by
  apply Subtype.ext
  exact congrArg Prod.fst A.ambient.coord_base

/-- Unwrap the negative parameter branch to the ordinary real interval
`(-radius, 0)`. -/
def negativeParameterHomeomorph
    (A : ActualFrontierIntervalChart O p) :
    {t : A.parameterInterval // t < A.zeroParameter} ≃ₜ
      {t : ℝ // t ∈ Ioo (-A.radius) 0} where
  toFun t := ⟨t.1.1, t.1.2.1, t.2⟩
  invFun t :=
    ⟨⟨t.1, t.2.1, t.2.2.trans A.radius_pos⟩, t.2.2⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Unwrap the positive parameter branch to the ordinary real interval
`(0, radius)`. -/
def positiveParameterHomeomorph
    (A : ActualFrontierIntervalChart O p) :
    {t : A.parameterInterval // A.zeroParameter < t} ≃ₜ
      {t : ℝ // t ∈ Ioo 0 A.radius} where
  toFun t := ⟨t.1.1, t.2, t.1.2.2⟩
  invFun t :=
    ⟨⟨t.1, (neg_neg_of_pos A.radius_pos).trans t.2.1, t.2.2⟩, t.2.1⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The negative parameter branch is connected without requiring an order-
completeness instance on the open-interval subtype. -/
theorem isConnected_negativeParameterBranch
    (A : ActualFrontierIntervalChart O p) :
    IsConnected (Iio A.zeroParameter : Set A.parameterInterval) := by
  rw [isConnected_iff_connectedSpace]
  exact A.negativeParameterHomeomorph.connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp
      (isConnected_Ioo (neg_neg_of_pos A.radius_pos)))

/-- The positive parameter branch is connected. -/
theorem isConnected_positiveParameterBranch
    (A : ActualFrontierIntervalChart O p) :
    IsConnected (Ioi A.zeroParameter : Set A.parameterInterval) := by
  rw [isConnected_iff_connectedSpace]
  exact A.positiveParameterHomeomorph.connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp (isConnected_Ioo A.radius_pos))

/-- The negative local branch after deleting the chart base. -/
def negativeBranch (A : ActualFrontierIntervalChart O p) :
    Set A.localDomain :=
  A.parameterHomeomorph ⁻¹' Iio A.zeroParameter

/-- The positive local branch after deleting the chart base. -/
def positiveBranch (A : ActualFrontierIntervalChart O p) :
    Set A.localDomain :=
  A.parameterHomeomorph ⁻¹' Ioi A.zeroParameter

/-- The negative local branch is a genuine connected open interval. -/
theorem isConnected_negativeBranch
    (A : ActualFrontierIntervalChart O p) :
    IsConnected A.negativeBranch := by
  exact A.parameterHomeomorph.isConnected_preimage.mpr
    A.isConnected_negativeParameterBranch

/-- The positive local branch is a genuine connected open interval. -/
theorem isConnected_positiveBranch
    (A : ActualFrontierIntervalChart O p) :
    IsConnected A.positiveBranch := by
  exact A.parameterHomeomorph.isConnected_preimage.mpr
    A.isConnected_positiveParameterBranch

/-- The two punctured local branches are disjoint. -/
theorem disjoint_negativeBranch_positiveBranch
    (A : ActualFrontierIntervalChart O p) :
    Disjoint A.negativeBranch A.positiveBranch := by
  rw [Set.disjoint_left]
  intro q hnegative hpositive
  exact ((show A.parameterHomeomorph q < A.zeroParameter from hnegative).trans
    (show A.zeroParameter < A.parameterHomeomorph q from hpositive)).false

/-- The two connected local branches exhaust exactly the chart domain with its
base removed.  This is the precise local no-branching statement used by the
global loop construction. -/
theorem negativeBranch_union_positiveBranch
    (A : ActualFrontierIntervalChart O p) :
    A.negativeBranch ∪ A.positiveBranch = {A.baseInLocalDomain}ᶜ := by
  ext q
  simp only [negativeBranch, positiveBranch, mem_union, mem_preimage,
    mem_Iio, mem_Ioi, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro (hnegative | hpositive) hq
    · subst q
      simpa using hnegative
    · subst q
      simpa using hpositive
  · intro hq
    have hparameter : A.parameterHomeomorph q ≠ A.zeroParameter := by
      intro h
      exact hq (A.parameterHomeomorph.injective
        (h.trans A.parameterHomeomorph_base.symm))
    exact lt_or_gt_of_ne hparameter

/-- The deleted base remains in the closure of the negative local branch. -/
theorem base_mem_closure_negativeBranch
    (A : ActualFrontierIntervalChart O p) :
    A.baseInLocalDomain ∈ closure A.negativeBranch := by
  let s : ℕ → A.parameterInterval := fun n =>
    ⟨-A.radius / (n + 2 : ℝ), by
      have hn : (0 : ℝ) < n + 2 := by positivity
      constructor
      · field_simp
        nlinarith [A.radius_pos]
      · exact (div_neg_of_neg_of_pos (neg_neg_of_pos A.radius_pos) hn).trans A.radius_pos⟩
  have hsBranch (n : ℕ) : s n < A.zeroParameter := by
    change -A.radius / (n + 2 : ℝ) < 0
    exact div_neg_of_neg_of_pos (neg_neg_of_pos A.radius_pos) (by positivity)
  have hsLim : Tendsto s atTop (𝓝 A.zeroParameter) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (0 : ℝ))
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ => A.radius / (n + 2 : ℝ))
        atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
    simpa only [s, neg_div, neg_zero] using hdiv.neg
  rw [mem_closure_iff_seq_limit]
  refine ⟨A.parameterHomeomorph.symm ∘ s, ?_, ?_⟩
  · intro n
    change A.parameterHomeomorph
      (A.parameterHomeomorph.symm (s n)) < A.zeroParameter
    simpa using hsBranch n
  · have hlim := A.parameterHomeomorph.symm.continuous.continuousAt.tendsto.comp hsLim
    have hbase :
        A.parameterHomeomorph.symm A.zeroParameter = A.baseInLocalDomain := by
      rw [← A.parameterHomeomorph_base]
      exact A.parameterHomeomorph.symm_apply_apply A.baseInLocalDomain
    rw [hbase] at hlim
    exact hlim
/-- The deleted base remains in the closure of the positive local branch. -/
theorem base_mem_closure_positiveBranch
    (A : ActualFrontierIntervalChart O p) :
    A.baseInLocalDomain ∈ closure A.positiveBranch := by
  let s : ℕ → A.parameterInterval := fun n =>
    ⟨A.radius / (n + 2 : ℝ), by
      have hn : (0 : ℝ) < n + 2 := by positivity
      constructor
      · exact (neg_neg_of_pos A.radius_pos).trans (div_pos A.radius_pos hn)
      · field_simp
        nlinarith [A.radius_pos]⟩
  have hsBranch (n : ℕ) : A.zeroParameter < s n := by
    change 0 < A.radius / (n + 2 : ℝ)
    exact div_pos A.radius_pos (by positivity)
  have hsLim : Tendsto s atTop (𝓝 A.zeroParameter) := by
    rw [tendsto_subtype_rng]
    change Tendsto (fun n => (s n : ℝ)) atTop (𝓝 (0 : ℝ))
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
    simpa only [s, div_eq_mul_inv, mul_zero, Function.comp_apply] using
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hden)
  rw [mem_closure_iff_seq_limit]
  refine ⟨A.parameterHomeomorph.symm ∘ s, ?_, ?_⟩
  · intro n
    change A.zeroParameter < A.parameterHomeomorph
      (A.parameterHomeomorph.symm (s n))
    simpa using hsBranch n
  · have hlim := A.parameterHomeomorph.symm.continuous.continuousAt.tendsto.comp hsLim
    have hbase :
        A.parameterHomeomorph.symm A.zeroParameter = A.baseInLocalDomain := by
      rw [← A.parameterHomeomorph_base]
      exact A.parameterHomeomorph.symm_apply_apply A.baseInLocalDomain
    rw [hbase] at hlim
    exact hlim

/-- Complete two-arm local topology at a frontier point: deleting the base
leaves two connected disjoint branches, both incident to the deleted point. -/
theorem twoBranchLocalTopology
    (A : ActualFrontierIntervalChart O p) :
    IsConnected A.negativeBranch ∧
      IsConnected A.positiveBranch ∧
      Disjoint A.negativeBranch A.positiveBranch ∧
      A.negativeBranch ∪ A.positiveBranch = {A.baseInLocalDomain}ᶜ ∧
      A.baseInLocalDomain ∈ closure A.negativeBranch ∧
      A.baseInLocalDomain ∈ closure A.positiveBranch :=
  ⟨A.isConnected_negativeBranch, A.isConnected_positiveBranch,
    A.disjoint_negativeBranch_positiveBranch,
    A.negativeBranch_union_positiveBranch,
    A.base_mem_closure_negativeBranch,
    A.base_mem_closure_positiveBranch⟩
/-- The base point belongs to the source of its induced frontier chart. -/
theorem base_mem_frontierChart_source
    (A : ActualFrontierIntervalChart O p) :
    p ∈ A.frontierChart.source := by
  simp only [frontierChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  exact A.base_mem_localDomain

end ActualFrontierIntervalChart

namespace BoundaryHalfSpaceAtlas

variable {O : Set PlanePoint}

/-- The pointwise ambient atlas induces a charted-space structure on the actual
frontier subtype.  Only the chosen local interval charts enter the atlas. -/
@[instance_reducible]
noncomputable def frontierChartedSpace (A : BoundaryHalfSpaceAtlas O) :
    ChartedSpace ℝ (FrontierSpace O) where
  atlas := Set.range (fun p : FrontierSpace O => (A.intervalAt p).frontierChart)
  chartAt := fun p => (A.intervalAt p).frontierChart
  mem_chart_source := fun p => (A.intervalAt p).base_mem_frontierChart_source
  chart_mem_atlas := fun p => Set.mem_range_self p

/-- The actual frontier is locally path connected.  Thus connected components
are path components; this rules out local branching without assuming a global
trace. -/
theorem frontierLocallyPathConnectedSpace
    (A : BoundaryHalfSpaceAtlas O) : LocallyPathConnectedSpace (FrontierSpace O) := by
  letI : ChartedSpace ℝ (FrontierSpace O) := A.frontierChartedSpace
  exact ChartedSpace.locallyPathConnectedSpace ℝ (FrontierSpace O)

/-- The locally path-connected frontier is in particular locally connected. -/
theorem frontierLocallyConnectedSpace
    (A : BoundaryHalfSpaceAtlas O) : LocallyConnectedSpace (FrontierSpace O) := by
  letI : LocallyPathConnectedSpace (FrontierSpace O) :=
    A.frontierLocallyPathConnectedSpace
  infer_instance

/-- Boundedness of the planar carrier makes its actual frontier subtype
compact. -/
theorem frontierCompactSpace
    (_A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O) :
    CompactSpace (FrontierSpace O) := by
  apply isCompact_iff_compactSpace.mp
  exact isCompact_iff_isClosed_bounded.2
    ⟨isClosed_frontier, hObounded.closure.subset frontier_subset_closure⟩

/-- Every actual frontier component contains infinitely many points, already
witnessed in the local interval around any one of its points. -/
theorem infinite_connectedComponent
    (A : BoundaryHalfSpaceAtlas O) (p : FrontierSpace O) :
    (connectedComponent p).Infinite := by
  let C := A.intervalAt p
  have hparameter : C.parameterInterval.Infinite := by
    exact Set.Ioo_infinite (neg_lt_self C.radius_pos)
  haveI hparameterType : Infinite C.parameterInterval :=
    Set.infinite_coe_iff.mpr hparameter
  haveI hlocalType : Infinite C.localDomain :=
    C.parameterHomeomorph.toEquiv.infinite_iff.mpr hparameterType
  exact (Set.infinite_coe_iff.mp hlocalType).mono
    C.localDomain_subset_connectedComponent

/-- No compact frontier component can be contained in one actual open-interval
chart.  This is the first global-return obstruction: every local branch must
eventually leave its chart, since otherwise a compact component would be
homeomorphic to a noncompact open interval. -/
theorem connectedComponent_not_subset_localDomain
    (B : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O)
    {p : FrontierSpace O} (A : ActualFrontierIntervalChart O p) :
    ¬ connectedComponent p ⊆ A.localDomain := by
  intro hsubset
  have heq : connectedComponent p = A.localDomain :=
    Subset.antisymm hsubset A.localDomain_subset_connectedComponent
  letI : CompactSpace (FrontierSpace O) := B.frontierCompactSpace hObounded
  have hlocalCompact : IsCompact A.localDomain := by
    rw [← heq]
    exact isClosed_connectedComponent.isCompact
  letI : CompactSpace A.localDomain :=
    isCompact_iff_compactSpace.mp hlocalCompact
  letI : CompactSpace A.parameterInterval :=
    A.parameterHomeomorph.surjective.compactSpace
      A.parameterHomeomorph.continuous
  exact A.parameterInterval_not_isCompact
    (isCompact_iff_compactSpace.mpr inferInstance)

/-- Hence every actual chart has a point of the same complete frontier
component outside its local domain. -/
theorem exists_mem_connectedComponent_not_mem_localDomain
    (B : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O)
    {p : FrontierSpace O} (A : ActualFrontierIntervalChart O p) :
    ∃ q : FrontierSpace O,
      q ∈ connectedComponent p ∧ q ∉ A.localDomain :=
  Set.not_subset.mp
    (B.connectedComponent_not_subset_localDomain hObounded A)

/-- A bounded carrier with the pointwise atlas has only finitely many actual
frontier components.  This is obtained from compactness and local connectedness,
not from a supplied finite geometric inventory. -/
theorem finite_frontier_connectedComponents
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O) :
    Finite (ConnectedComponents (FrontierSpace O)) := by
  letI : LocallyConnectedSpace (FrontierSpace O) := A.frontierLocallyConnectedSpace
  letI : CompactSpace (FrontierSpace O) := A.frontierCompactSpace hObounded
  infer_instance

/-- The actual planar subset represented by the frontier component through
`p`. -/
def componentAt (p : FrontierSpace O) : Set PlanePoint :=
  Subtype.val '' connectedComponent p

/-- A component contains its indexing actual frontier point. -/
theorem mem_componentAt (p : FrontierSpace O) :
    p.1 ∈ componentAt p :=
  ⟨p, mem_connectedComponent, rfl⟩

/-- Every component consists only of actual frontier points. -/
theorem componentAt_subset_frontier (p : FrontierSpace O) :
    componentAt p ⊆ frontier O := by
  rintro _ ⟨q, -, rfl⟩
  exact q.2

/-- Every actual frontier component is connected as a planar set. -/
theorem isConnected_componentAt (p : FrontierSpace O) :
    IsConnected (componentAt p) :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

/-- Every actual frontier component is path connected; connectedness cannot hide
multiple path components. -/
theorem isPathConnected_componentAt
    (A : BoundaryHalfSpaceAtlas O) (p : FrontierSpace O) :
    IsPathConnected (componentAt p) := by
  letI : LocallyPathConnectedSpace (FrontierSpace O) :=
    A.frontierLocallyPathConnectedSpace
  letI : LocallyPathConnectedSpace (connectedComponent p) :=
    (isOpen_connectedComponent (x := p)).locallyPathConnectedSpace
  have hcomponent : IsPathConnected (connectedComponent p) := by
    rw [isPathConnected_iff_pathConnectedSpace]
    letI : ConnectedSpace (connectedComponent p) :=
      isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  exact hcomponent.image' continuous_subtype_val.continuousOn

/-- Every actual frontier component is compact for a bounded carrier.  Hence no
limit point of a component can be omitted by a later global parameterization. -/
theorem isCompact_componentAt
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O)
    (p : FrontierSpace O) : IsCompact (componentAt p) := by
  letI : CompactSpace (FrontierSpace O) := A.frontierCompactSpace hObounded
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- The planar realization of every actual frontier component is infinite. -/
theorem infinite_componentAt
    (A : BoundaryHalfSpaceAtlas O) (p : FrontierSpace O) :
    (componentAt p).Infinite := by
  exact (Set.infinite_image_iff Subtype.val_injective.injOn).2
    (A.infinite_connectedComponent p)

/-- In planar coordinates, every local interval chart omits an actual point of
the same compact component.  This is the concrete return point needed before
closing the two local branches into a loop. -/
theorem exists_mem_componentAt_not_mem_window
    (B : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O)
    {p : FrontierSpace O} (A : ActualFrontierIntervalChart O p) :
    ∃ q : PlanePoint, q ∈ componentAt p ∧ q ∉ A.window := by
  obtain ⟨q, hqComponent, hqOutside⟩ :=
    B.exists_mem_connectedComponent_not_mem_localDomain hObounded A
  exact ⟨q.1, ⟨q, hqComponent, rfl⟩, hqOutside⟩

/-- Every component is relatively open in the actual frontier.  Together with
closedness and the local interval charts, this isolates components without a
supplied component cover. -/
theorem isOpen_componentAt_preimage
    (A : BoundaryHalfSpaceAtlas O) (p : FrontierSpace O) :
    IsOpen ((fun q : FrontierSpace O => q.1) ⁻¹' componentAt p) := by
  letI : LocallyConnectedSpace (FrontierSpace O) := A.frontierLocallyConnectedSpace
  have hpreimage :
      (fun q : FrontierSpace O => q.1) ⁻¹' componentAt p =
        connectedComponent p := by
    ext q
    constructor
    · rintro ⟨r, hr, hqr⟩
      have : q = r := Subtype.ext hqr.symm
      simpa only [this] using hr
    · intro hq
      exact ⟨q, hq, rfl⟩
  rw [hpreimage]
  exact isOpen_connectedComponent

/-- Distinct indexed components are disjoint as actual planar subsets. -/
theorem componentAt_disjoint
    {p q : FrontierSpace O}
    (hneq : connectedComponent p ≠ connectedComponent q) :
    Disjoint (componentAt p) (componentAt q) := by
  exact Disjoint.image (connectedComponent_disjoint hneq)
    Subtype.val_injective.injOn (subset_univ _) (subset_univ _)

/-- A chosen actual frontier point representing a connected-component class. -/
noncomputable def componentRepresentative
    (c : ConnectedComponents (FrontierSpace O)) : FrontierSpace O :=
  Classical.choose (ConnectedComponents.surjective_coe c)

@[simp] theorem componentRepresentative_class
    (c : ConnectedComponents (FrontierSpace O)) :
    (componentRepresentative c : ConnectedComponents (FrontierSpace O)) = c :=
  Classical.choose_spec (ConnectedComponents.surjective_coe c)

/-- A finite family of actual frontier centers which indexes every component
exactly once.  The index finiteness is derived rather than accepted. -/
structure FiniteFrontierComponentDecomposition (O : Set PlanePoint) where
  index : Type
  finite_index : Finite index
  center : index → FrontierSpace O
  center_class_bijective :
    Function.Bijective
      (fun i => (center i : ConnectedComponents (FrontierSpace O)))

namespace FiniteFrontierComponentDecomposition

variable {O : Set PlanePoint}

/-- The component sets indexed by the finite decomposition exhaust the actual
frontier. -/
theorem iUnion_componentAt_eq_frontier
    (D : FiniteFrontierComponentDecomposition O) :
    (⋃ i : D.index, componentAt (D.center i)) = frontier O := by
  apply Subset.antisymm
  · exact iUnion_subset fun i => componentAt_subset_frontier (D.center i)
  · intro q hq
    let p : FrontierSpace O := ⟨q, hq⟩
    obtain ⟨i, hi⟩ := D.center_class_bijective.2
      (p : ConnectedComponents (FrontierSpace O))
    have hpComponent : p ∈ connectedComponent (D.center i) := by
      exact ConnectedComponents.coe_eq_coe'.mp hi.symm
    exact mem_iUnion.2 ⟨i, ⟨p, hpComponent, rfl⟩⟩

/-- Different finite indices give disjoint actual planar components. -/
theorem pairwise_disjoint_componentAt
    (D : FiniteFrontierComponentDecomposition O) :
    Pairwise fun i j : D.index =>
      Disjoint (componentAt (D.center i)) (componentAt (D.center j)) := by
  intro i j hij
  apply componentAt_disjoint
  intro hcomponent
  apply hij
  apply D.center_class_bijective.1
  exact ConnectedComponents.coe_eq_coe.mpr hcomponent

end FiniteFrontierComponentDecomposition

/-- Compactness and the induced one-dimensional atlas produce the finite
component decomposition with no supplied centers or component count. -/
noncomputable def finiteFrontierComponentDecomposition
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O) :
    FiniteFrontierComponentDecomposition O where
  index := ConnectedComponents (FrontierSpace O)
  finite_index := A.finite_frontier_connectedComponents hObounded
  center := componentRepresentative
  center_class_bijective := by
    constructor
    · intro c d hcd
      simpa only [componentRepresentative_class] using hcd
    · intro c
      exact ⟨c, componentRepresentative_class c⟩

end BoundaryHalfSpaceAtlas

end CMVBoundaryLocalAtlas
