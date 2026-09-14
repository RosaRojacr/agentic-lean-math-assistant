/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryGlobalTransition

/-!
# Finite compact subarcs and endpoint cuts

A bounded actual frontier with the pointwise half-space atlas admits a finite
cover by relative interiors of compact embedded chart subarcs.  Their actual
endpoints form a finite cut set.  The cut frontier has finitely many connected
pieces; each is homeomorphic to a nondegenerate open real interval, and its
actual closure is a compact embedded closed interval with two distinct
endpoints in the cut set.  Selected arcs remain indexed by chart centers, so
equal endpoint pairs do not identify distinct arcs.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

namespace ActualFrontierIntervalChart

variable {O : Set PlanePoint} {p : FrontierSpace O}

/-- Half the radius of the selected open interval chart. -/
def coreRadius (C : ActualFrontierIntervalChart O p) : ℝ := C.radius / 2

/-- The compact parameter interval strictly inside the original chart. -/
abbrev CoreParameter (C : ActualFrontierIntervalChart O p) :=
  Set.Icc (-C.coreRadius) C.coreRadius

/-- The open parameter interval which is the relative interior of the compact
core. -/
def coreInteriorParameter (C : ActualFrontierIntervalChart O p) :
    Set C.CoreParameter :=
  {t | (t : ℝ) ∈ Set.Ioo (-C.coreRadius) C.coreRadius}

theorem coreRadius_pos (C : ActualFrontierIntervalChart O p) :
    0 < C.coreRadius := by
  unfold coreRadius
  exact div_pos C.radius_pos (by norm_num)

/-- A compact-core parameter lies in the original open chart interval. -/
def coreParameterToParameterInterval
    (C : ActualFrontierIntervalChart O p) (t : C.CoreParameter) :
    C.parameterInterval :=
  ⟨t.1, by
    have ht := t.2
    change -C.radius < t.1 ∧ t.1 < C.radius
    change -(C.radius / 2) ≤ t.1 ∧ t.1 ≤ C.radius / 2 at ht
    constructor <;> linarith [C.radius_pos]⟩

/-- The actual frontier point at a compact-core parameter. -/
noncomputable def corePoint
    (C : ActualFrontierIntervalChart O p) (t : C.CoreParameter) :
    FrontierSpace O :=
  (C.parameterHomeomorph.symm (C.coreParameterToParameterInterval t)).1

/-- The compact closed subarc in the actual frontier subtype. -/
def closedCore (C : ActualFrontierIntervalChart O p) : Set (FrontierSpace O) :=
  Set.range C.corePoint

/-- The relative interior of the compact subarc, expressed through the actual
open chart so that its openness is explicit. -/
def coreInterior (C : ActualFrontierIntervalChart O p) : Set (FrontierSpace O) :=
  Subtype.val ''
    {q : C.localDomain |
      (C.parameterHomeomorph q : ℝ) ∈
        Set.Ioo (-C.coreRadius) C.coreRadius}

/-- Left endpoint of the compact core. -/
def leftCoreParameter (C : ActualFrontierIntervalChart O p) : C.CoreParameter :=
  ⟨-C.coreRadius, le_rfl, by linarith [C.coreRadius_pos]⟩

/-- Right endpoint of the compact core. -/
def rightCoreParameter (C : ActualFrontierIntervalChart O p) : C.CoreParameter :=
  ⟨C.coreRadius, by linarith [C.coreRadius_pos], le_rfl⟩

/-- Actual left endpoint of the compact chart subarc. -/
def leftEndpoint (C : ActualFrontierIntervalChart O p) : FrontierSpace O :=
  C.corePoint C.leftCoreParameter

/-- Actual right endpoint of the compact chart subarc. -/
def rightEndpoint (C : ActualFrontierIntervalChart O p) : FrontierSpace O :=
  C.corePoint C.rightCoreParameter

/-- The two actual endpoints of the selected compact subarc. -/
noncomputable def endpointFinset
    (C : ActualFrontierIntervalChart O p) : Finset (FrontierSpace O) :=
  {C.leftEndpoint, C.rightEndpoint}

/-- The inclusion of compact-core parameters into the original chart interval
is continuous. -/
theorem continuous_coreParameterToParameterInterval
    (C : ActualFrontierIntervalChart O p) :
    Continuous C.coreParameterToParameterInterval := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- The compact subarc parameterization is continuous. -/
theorem continuous_corePoint (C : ActualFrontierIntervalChart O p) :
    Continuous C.corePoint := by
  unfold corePoint
  exact continuous_subtype_val.comp
    (C.parameterHomeomorph.symm.continuous.comp
      C.continuous_coreParameterToParameterInterval)

/-- The compact subarc parameterization never retraces. -/
theorem injective_corePoint (C : ActualFrontierIntervalChart O p) :
    Function.Injective C.corePoint := by
  intro s t hst
  have hlocal :
      C.parameterHomeomorph.symm (C.coreParameterToParameterInterval s) =
        C.parameterHomeomorph.symm (C.coreParameterToParameterInterval t) := by
    apply Subtype.ext
    exact hst
  have hparameter :
      C.coreParameterToParameterInterval s =
        C.coreParameterToParameterInterval t :=
    C.parameterHomeomorph.symm.injective hlocal
  have hvalue : (s : ℝ) = (t : ℝ) :=
    congrArg (fun u : C.parameterInterval => (u : ℝ)) hparameter
  exact Subtype.ext hvalue

/-- Each selected compact core is an embedded closed interval in the actual
frontier. -/
theorem isClosedEmbedding_corePoint
    (C : ActualFrontierIntervalChart O p) :
    Topology.IsClosedEmbedding C.corePoint :=
  C.continuous_corePoint.isClosedEmbedding C.injective_corePoint

/-- The closed core is compact. -/
theorem isCompact_closedCore (C : ActualFrontierIntervalChart O p) :
    IsCompact C.closedCore := by
  rw [closedCore, ← Set.image_univ]
  exact isCompact_univ.image C.continuous_corePoint

/-- The closed core is closed in the actual frontier subtype. -/
theorem isClosed_closedCore (C : ActualFrontierIntervalChart O p) :
    IsClosed C.closedCore :=
  C.isCompact_closedCore.isClosed

/-- The relative interior of a compact core is open in the complete actual
frontier, not merely in its chart domain. -/
theorem isOpen_coreInterior (C : ActualFrontierIntervalChart O p) :
    IsOpen C.coreInterior := by
  apply C.isOpen_localDomain.isOpenMap_subtype_val
  exact isOpen_Ioo.preimage
    (continuous_subtype_val.comp C.parameterHomeomorph.continuous)

/-- The chart base belongs to the relative interior of its compact core. -/
theorem base_mem_coreInterior (C : ActualFrontierIntervalChart O p) :
    p ∈ C.coreInterior := by
  refine ⟨C.baseInLocalDomain, ?_, rfl⟩
  change (C.parameterHomeomorph C.baseInLocalDomain : ℝ) ∈
    Ioo (-C.coreRadius) C.coreRadius
  rw [C.parameterHomeomorph_base]
  exact ⟨neg_neg_of_pos C.coreRadius_pos, C.coreRadius_pos⟩

/-- The open core parameters are dense in the compact parameter interval. -/
theorem closure_coreInteriorParameter
    (C : ActualFrontierIntervalChart O p) :
    closure C.coreInteriorParameter = Set.univ := by
  have himage :
      ((fun t : C.CoreParameter => (t : ℝ)) '' C.coreInteriorParameter) =
        Ioo (-C.coreRadius) C.coreRadius := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, hx.1.le, hx.2.le⟩, hx, rfl⟩
  apply Dense.closure_eq
  apply (Topology.IsEmbedding.subtypeVal.isInducing.dense_iff).2
  intro t
  rw [himage, closure_Ioo (ne_of_lt (neg_lt_self C.coreRadius_pos))]
  exact t.2

/-- The open core is exactly the image of the open part of the compact
parameter interval. -/
theorem image_coreInteriorParameter
    (C : ActualFrontierIntervalChart O p) :
    C.corePoint '' C.coreInteriorParameter = C.coreInterior := by
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨C.parameterHomeomorph.symm
      (C.coreParameterToParameterInterval t), ?_, rfl⟩
    change
      (C.parameterHomeomorph
        (C.parameterHomeomorph.symm
          (C.coreParameterToParameterInterval t)) : ℝ) ∈
        Ioo (-C.coreRadius) C.coreRadius
    rw [C.parameterHomeomorph.apply_symm_apply]
    exact ht
  · rintro ⟨qLocal, hq, rfl⟩
    let t : C.CoreParameter :=
      ⟨(C.parameterHomeomorph qLocal : ℝ), hq.1.le, hq.2.le⟩
    refine ⟨t, hq, ?_⟩
    unfold corePoint
    have ht : C.coreParameterToParameterInterval t =
        C.parameterHomeomorph qLocal := by
      apply Subtype.ext
      rfl
    rw [ht, C.parameterHomeomorph.symm_apply_apply]

/-- Every relative-interior point belongs to the compact closed core. -/
theorem coreInterior_subset_closedCore
    (C : ActualFrontierIntervalChart O p) :
    C.coreInterior ⊆ C.closedCore := by
  rintro q ⟨qLocal, hq, rfl⟩
  let t : C.CoreParameter :=
    ⟨(C.parameterHomeomorph qLocal : ℝ), ⟨hq.1.le, hq.2.le⟩⟩
  refine ⟨t, ?_⟩
  unfold corePoint
  have ht : C.coreParameterToParameterInterval t =
      C.parameterHomeomorph qLocal := by
    apply Subtype.ext
    rfl
  rw [ht, C.parameterHomeomorph.symm_apply_apply]
/-- Away from its two endpoints, a point of the compact core lies in its
relative interior. -/
theorem mem_coreInterior_of_mem_closedCore_of_ne_endpoints
    (C : ActualFrontierIntervalChart O p) {q : FrontierSpace O}
    (hq : q ∈ C.closedCore)
    (hqLeft : q ≠ C.leftEndpoint) (hqRight : q ≠ C.rightEndpoint) :
    q ∈ C.coreInterior := by
  rcases hq with ⟨t, rfl⟩
  have htLeft : (t : ℝ) ≠ -C.coreRadius := by
    intro ht
    apply hqLeft
    unfold leftEndpoint
    apply congrArg C.corePoint
    apply Subtype.ext
    exact ht
  have htRight : (t : ℝ) ≠ C.coreRadius := by
    intro ht
    apply hqRight
    unfold rightEndpoint
    apply congrArg C.corePoint
    apply Subtype.ext
    exact ht
  have htInterior : (t : ℝ) ∈ Ioo (-C.coreRadius) C.coreRadius :=
    ⟨lt_of_le_of_ne t.2.1 (Ne.symm htLeft),
      lt_of_le_of_ne t.2.2 htRight⟩
  refine ⟨C.parameterHomeomorph.symm
      (C.coreParameterToParameterInterval t), ?_, rfl⟩
  change
    (C.parameterHomeomorph
      (C.parameterHomeomorph.symm
        (C.coreParameterToParameterInterval t)) : ℝ) ∈
      Ioo (-C.coreRadius) C.coreRadius
  rw [C.parameterHomeomorph.apply_symm_apply]
  exact htInterior

/-- Off the endpoint pair, membership in the open and closed versions of the
same selected subarc is equivalent. -/
theorem mem_coreInterior_iff_mem_closedCore_of_ne_endpoints
    (C : ActualFrontierIntervalChart O p) {q : FrontierSpace O}
    (hqLeft : q ≠ C.leftEndpoint) (hqRight : q ≠ C.rightEndpoint) :
    q ∈ C.coreInterior ↔ q ∈ C.closedCore :=
  ⟨fun hq => C.coreInterior_subset_closedCore hq,
    fun hq => C.mem_coreInterior_of_mem_closedCore_of_ne_endpoints
      hq hqLeft hqRight⟩

/-- The two endpoints of every selected compact subarc are distinct. -/
theorem leftEndpoint_ne_rightEndpoint
    (C : ActualFrontierIntervalChart O p) :
    C.leftEndpoint ≠ C.rightEndpoint := by
  intro h
  have hp := C.injective_corePoint h
  have hvalue := congrArg Subtype.val hp
  dsimp [leftCoreParameter, rightCoreParameter] at hvalue
  linarith [C.coreRadius_pos]
/-- The compact embedded core is exactly the closure of its relative
interior in the complete actual frontier. -/
theorem closure_coreInterior
    (C : ActualFrontierIntervalChart O p) :
    closure C.coreInterior = C.closedCore := by
  apply Subset.antisymm
  · exact closure_minimal C.coreInterior_subset_closedCore
      C.isClosed_closedCore
  · intro q hq
    rcases hq with ⟨t, rfl⟩
    rw [← C.image_coreInteriorParameter]
    apply image_closure_subset_closure_image C.continuous_corePoint
    refine ⟨t, ?_, rfl⟩
    rw [C.closure_coreInteriorParameter]
    exact mem_univ t

/-- The left endpoint is not in the relative interior. -/
theorem leftEndpoint_not_mem_coreInterior
    (C : ActualFrontierIntervalChart O p) :
    C.leftEndpoint ∉ C.coreInterior := by
  intro h
  rw [← C.image_coreInteriorParameter] at h
  rcases h with ⟨t, htInterior, ht⟩
  unfold leftEndpoint at ht
  have hparameter : t = C.leftCoreParameter :=
    C.injective_corePoint ht
  have hvalue := congrArg Subtype.val hparameter
  dsimp [leftCoreParameter] at hvalue
  change (t : ℝ) ∈ Ioo (-C.coreRadius) C.coreRadius at htInterior
  rw [hvalue] at htInterior
  exact (lt_irrefl _ htInterior.1)

/-- The right endpoint is not in the relative interior. -/
theorem rightEndpoint_not_mem_coreInterior
    (C : ActualFrontierIntervalChart O p) :
    C.rightEndpoint ∉ C.coreInterior := by
  intro h
  rw [← C.image_coreInteriorParameter] at h
  rcases h with ⟨t, htInterior, ht⟩
  unfold rightEndpoint at ht
  have hparameter : t = C.rightCoreParameter :=
    C.injective_corePoint ht
  have hvalue := congrArg Subtype.val hparameter
  dsimp [rightCoreParameter] at hvalue
  change (t : ℝ) ∈ Ioo (-C.coreRadius) C.coreRadius at htInterior
  rw [hvalue] at htInterior
  exact (lt_irrefl _ htInterior.2)

/-- The only points of the compact core outside its relative interior are its
two distinct actual endpoints. -/
theorem closedCore_sdiff_coreInterior
    (C : ActualFrontierIntervalChart O p) :
    C.closedCore \ C.coreInterior =
      ({C.leftEndpoint, C.rightEndpoint} : Set (FrontierSpace O)) := by
  ext q
  constructor
  · rintro ⟨hqCore, hqInterior⟩
    by_cases hqLeft : q = C.leftEndpoint
    · simp [hqLeft]
    by_cases hqRight : q = C.rightEndpoint
    · simp [hqRight]
    exact False.elim
      (hqInterior
        (C.mem_coreInterior_of_mem_closedCore_of_ne_endpoints
          hqCore hqLeft hqRight))
  · intro hq
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨C.leftCoreParameter, rfl⟩,
        C.leftEndpoint_not_mem_coreInterior⟩
    · exact ⟨⟨C.rightCoreParameter, rfl⟩,
        C.rightEndpoint_not_mem_coreInterior⟩

end ActualFrontierIntervalChart

/-- A nonempty bounded open connected subset of the real line is exactly the
open interval between its infimum and supremum. -/
theorem openConnectedRealSet_eq_Ioo_sInf_sSup
    {s : Set ℝ} (hsOpen : IsOpen s) (hsConnected : IsConnected s)
    (hsBelow : BddBelow s) (hsAbove : BddAbove s) :
    s = Ioo (sInf s) (sSup s) := by
  ext t
  constructor
  · intro ht
    obtain ⟨l, u, hltu, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hsOpen.mem_nhds ht)
    obtain ⟨y, hly, hyt⟩ := exists_between hltu.1
    obtain ⟨z, htz, hzu⟩ := exists_between hltu.2
    have hy : y ∈ s := hlu ⟨hly, hyt.trans hltu.2⟩
    have hz : z ∈ s := hlu ⟨hltu.1.trans htz, hzu⟩
    exact ⟨csInf_lt_of_lt hsBelow hy hyt,
      lt_csSup_of_lt hsAbove hz htz⟩
  · rintro ⟨hInf, hSup⟩
    obtain ⟨y, hy, hyt⟩ :=
      exists_lt_of_csInf_lt hsConnected.nonempty hInf
    obtain ⟨z, hz, htz⟩ :=
      exists_lt_of_lt_csSup hsConnected.nonempty hSup
    have hyz : y ≤ z := hyt.le.trans htz.le
    apply hsConnected.isPreconnected.ordConnected.uIcc_subset hy hz
    rw [uIcc_of_le hyz]
    exact ⟨hyt.le, htz.le⟩

namespace RealFiniteCuts

/-- The number of cuts strictly to the left of a point outside a finite real
cut set. -/
noncomputable def rank (cuts : Finset ℝ)
    (x : {t : ℝ // t ∉ cuts}) : Fin (cuts.card + 1) :=
  ⟨(cuts.filter fun c => c < x.1).card,
    Nat.lt_succ_of_le (Finset.card_filter_le _ _)⟩

/-- A connected subset of a finite real cut complement cannot cross a cut. -/
theorem cut_not_mem_uIcc_of_mem_connectedComponent
    (cuts : Finset ℝ) (x y : {t : ℝ // t ∉ cuts})
    (hy : y ∈ connectedComponent x) {c : ℝ} (hc : c ∈ cuts) :
    c ∉ uIcc x.1 y.1 := by
  intro hcInterval
  have hImage : IsConnected (Subtype.val '' connectedComponent x) :=
    isConnected_connectedComponent.image Subtype.val
      continuous_subtype_val.continuousOn
  have hxImage : x.1 ∈ Subtype.val '' connectedComponent x :=
    ⟨x, mem_connectedComponent, rfl⟩
  have hyImage : y.1 ∈ Subtype.val '' connectedComponent x :=
    ⟨y, hy, rfl⟩
  have hcImage :=
    hImage.isPreconnected.ordConnected.uIcc_subset
      hxImage hyImage hcInterval
  rcases hcImage with ⟨z, _hz, rfl⟩
  exact z.2 hc

/-- The finite-cut rank is constant on every connected component. -/
theorem rank_eq_of_mem_connectedComponent
    (cuts : Finset ℝ) (x y : {t : ℝ // t ∉ cuts})
    (hy : y ∈ connectedComponent x) :
    rank cuts x = rank cuts y := by
  apply Fin.ext
  change (cuts.filter fun c => c < x.1).card =
    (cuts.filter fun c => c < y.1).card
  congr 1
  apply Finset.ext
  intro c
  simp only [Finset.mem_filter]
  have hNoCut (hc : c ∈ cuts) : c ∉ uIcc x.1 y.1 :=
    cut_not_mem_uIcc_of_mem_connectedComponent cuts x y hy hc
  rcases le_total x.1 y.1 with hxy | hyx
  · constructor
    · rintro ⟨hc, hcx⟩
      exact ⟨hc, hcx.trans_le hxy⟩
    · rintro ⟨hc, hcy⟩
      refine ⟨hc, ?_⟩
      by_contra hcx
      exact hNoCut hc (by
        rw [uIcc_of_le hxy]
        exact ⟨le_of_not_gt hcx, hcy.le⟩)
  · constructor
    · rintro ⟨hc, hcx⟩
      refine ⟨hc, ?_⟩
      by_contra hcy
      exact hNoCut hc (by
        rw [uIcc_of_ge hyx]
        exact ⟨le_of_not_gt hcy, hcx.le⟩)
    · rintro ⟨hc, hcy⟩
      exact ⟨hc, hcy.trans_le hyx⟩

/-- Equal finite-cut ranks force two points into the same connected component
of the real cut complement. -/
theorem connectedComponent_eq_of_rank_eq
    (cuts : Finset ℝ) (x y : {t : ℝ // t ∉ cuts})
    (hRank : rank cuts x = rank cuts y) :
    connectedComponent x = connectedComponent y := by
  have hCard : (cuts.filter fun c => c < x.1).card =
      (cuts.filter fun c => c < y.1).card :=
    congrArg Fin.val hRank
  have hNoCut : ∀ c ∈ cuts, c ∉ uIcc x.1 y.1 := by
    intro c hc hcInterval
    rcases le_total x.1 y.1 with hxy | hyx
    · rw [uIcc_of_le hxy] at hcInterval
      have hSubset :
          cuts.filter (fun d => d < x.1) ⊆
            cuts.filter (fun d => d < y.1) := by
        intro d hd
        simp only [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.trans_le hxy⟩
      have hcLeft : c ∉ cuts.filter (fun d => d < x.1) := by
        simp only [Finset.mem_filter, hc, true_and]
        exact not_lt_of_ge hcInterval.1
      have hcRight : c ∈ cuts.filter (fun d => d < y.1) := by
        simp only [Finset.mem_filter, hc, true_and]
        exact lt_of_le_of_ne hcInterval.2 (fun h => y.2 (h ▸ hc))
      have hStrict :
          cuts.filter (fun d => d < x.1) ⊂
            cuts.filter (fun d => d < y.1) :=
        (Finset.ssubset_iff_of_subset hSubset).2
          ⟨c, hcRight, hcLeft⟩
      exact (Finset.card_lt_card hStrict).ne hCard
    · rw [uIcc_of_ge hyx] at hcInterval
      have hSubset :
          cuts.filter (fun d => d < y.1) ⊆
            cuts.filter (fun d => d < x.1) := by
        intro d hd
        simp only [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, hd.2.trans_le hyx⟩
      have hcRight : c ∉ cuts.filter (fun d => d < y.1) := by
        simp only [Finset.mem_filter, hc, true_and]
        exact not_lt_of_ge hcInterval.1
      have hcLeft : c ∈ cuts.filter (fun d => d < x.1) := by
        simp only [Finset.mem_filter, hc, true_and]
        exact lt_of_le_of_ne hcInterval.2 (fun h => x.2 (h ▸ hc))
      have hStrict :
          cuts.filter (fun d => d < y.1) ⊂
            cuts.filter (fun d => d < x.1) :=
        (Finset.ssubset_iff_of_subset hSubset).2
          ⟨c, hcLeft, hcRight⟩
      exact (Finset.card_lt_card hStrict).ne hCard.symm
  have hRange : uIcc x.1 y.1 ⊆
      Set.range (Subtype.val : {t : ℝ // t ∉ cuts} → ℝ) := by
    intro t ht
    refine ⟨⟨t, ?_⟩, rfl⟩
    intro htCut
    exact hNoCut t htCut ht
  have hOpen : IsOpen {t : ℝ | t ∉ cuts} := by
    change IsOpen ((cuts : Set ℝ)ᶜ)
    exact cuts.finite_toSet.isClosed.isOpen_compl
  have hConnected :
      IsConnected ((Subtype.val : {t : ℝ // t ∉ cuts} → ℝ) ⁻¹'
        uIcc x.1 y.1) :=
    IsConnected.preimage_of_isOpenMap
      ⟨⟨x.1, left_mem_uIcc⟩, isPreconnected_uIcc⟩
      Subtype.val_injective
      hOpen.isOpenMap_subtype_val hRange
  apply connectedComponent_eq
  exact hConnected.subset_connectedComponent left_mem_uIcc right_mem_uIcc

/-- Connected components of a finite real cut complement inject into their
finite left-cut ranks. -/
noncomputable def componentRank (cuts : Finset ℝ) :
    ConnectedComponents {t : ℝ // t ∉ cuts} → Fin (cuts.card + 1) :=
  Quotient.lift (rank cuts) fun x y hxy =>
    rank_eq_of_mem_connectedComponent cuts x y
      (hxy.symm ▸ mem_connectedComponent)

/-- The rank map on connected components is injective. -/
theorem componentRank_injective (cuts : Finset ℝ) :
    Function.Injective (componentRank cuts) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  apply ConnectedComponents.coe_eq_coe.mpr
  exact connectedComponent_eq_of_rank_eq cuts x y hcd

/-- Deleting finitely many points from the real line leaves finitely many
connected components. -/
theorem finite_connectedComponents_compl (cuts : Finset ℝ) :
    Finite (ConnectedComponents {t : ℝ // t ∉ cuts}) :=
  Finite.of_injective (componentRank cuts) (componentRank_injective cuts)

end RealFiniteCuts

/-- Homeomorphic spaces have the same finite connected-component property. -/
theorem finiteConnectedComponents_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Finite (ConnectedComponents Y)] (h : X ≃ₜ Y) :
    Finite (ConnectedComponents X) := by
  have hFiber (y : Y) : IsConnected (h ⁻¹' {y}) := by
    have heq : h ⁻¹' {y} = {h.symm y} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro hx
        apply h.injective
        rw [hx, h.apply_symm_apply]
      · rintro rfl
        exact h.apply_symm_apply y
    rw [heq]
    exact isConnected_singleton
  let e :=
    h.isQuotientMap.isCoinducing.connectedComponentsHomeomorph hFiber
  exact Finite.of_equiv (ConnectedComponents Y) e.symm.toEquiv

/-- A clopen subspace of a space with finitely many connected components again
has finitely many connected components. -/
theorem finiteConnectedComponents_clopenSubtype
    {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]
    {U : Set X} (hU : IsClopen U) :
    Finite (ConnectedComponents U) := by
  apply Finite.of_injective
    continuous_subtype_val.connectedComponentsMap
  intro c d hcd
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  apply ConnectedComponents.coe_eq_coe.mpr
  apply Subtype.val_injective.image_injective
  calc
    Subtype.val '' connectedComponent x =
        connectedComponentIn U x.1 :=
      (connectedComponentIn_eq_image x.2).symm
    _ = connectedComponent x.1 :=
      hU.connectedComponentIn_eq x.2
    _ = connectedComponent y.1 := by
      exact ConnectedComponents.coe_eq_coe.mp hcd
    _ = connectedComponentIn U y.1 :=
      (hU.connectedComponentIn_eq y.2).symm
    _ = Subtype.val '' connectedComponent y :=
      connectedComponentIn_eq_image y.2

/-- A finite cover by subspaces with finitely many connected components forces
the ambient space to have finitely many connected components. -/
theorem finiteConnectedComponents_of_finite_iUnion
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (U : ι → Set X)
    (hU : ∀ i, Finite (ConnectedComponents (U i)))
    (hcover : ⋃ i, U i = Set.univ) :
    Finite (ConnectedComponents X) := by
  letI (i : ι) : Finite (ConnectedComponents (U i)) := hU i
  let f : (Σ i, ConnectedComponents (U i)) →
      ConnectedComponents X :=
    fun z => continuous_subtype_val.connectedComponentsMap z.2
  apply Finite.of_surjective f
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hxCover : x ∈ ⋃ i, U i := by
    rw [hcover]
    exact mem_univ x
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxCover
  refine ⟨⟨i, ConnectedComponents.mk ⟨x, hi⟩⟩, ?_⟩
  rfl

namespace BoundaryHalfSpaceAtlas

open ActualFrontierIntervalChart

variable {O : Set PlanePoint}

/-- A finite compactness-selected family of actual chart subarcs.  The index is
the selected chart center, so the construction never identifies arcs merely
because their endpoint pairs happen to agree.  `additionalCutPoints` lets a
downstream geometric construction force a previously derived finite junction
set into the cut before connected arc components are formed. -/
structure FiniteChartCutSystem (A : BoundaryHalfSpaceAtlas O) where
  centers : Finset (FrontierSpace O)
  covers : Set.univ ⊆
    ⋃ i : centers, (A.intervalAt i.1).coreInterior
  additionalCutPoints : Finset (FrontierSpace O) := ∅
/-- Compactness selects finitely many relative interiors of compact chart cores
covering the complete actual frontier. -/
theorem exists_finiteChartCutSystem
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O) :
    Nonempty (FiniteChartCutSystem A) := by
  classical
  letI : CompactSpace (FrontierSpace O) := A.frontierCompactSpace hObounded
  have hcover : Set.univ ⊆
      ⋃ p : FrontierSpace O, (A.intervalAt p).coreInterior := by
    intro p _hp
    exact mem_iUnion.2 ⟨p, (A.intervalAt p).base_mem_coreInterior⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : FrontierSpace O => (A.intervalAt p).coreInterior)
    (fun p => (A.intervalAt p).isOpen_coreInterior) hcover
  exact ⟨{
    centers := t
    covers := by simpa only [Set.iUnion_subtype] using ht
    additionalCutPoints := ∅
  }⟩


/-- The actual frontier has no isolated points.  This is derived from either
local chart arm accumulating at its base, rather than assumed globally. -/
theorem frontier_punctured_nhds_neBot
    (A : BoundaryHalfSpaceAtlas O) (p : FrontierSpace O) :
    Filter.NeBot (𝓝[≠] p) := by
  let C := A.intervalAt p
  have hpImage :
      p ∈ closure (Subtype.val '' C.negativeBranch) := by
    have hpLocal :
        (C.baseInLocalDomain : FrontierSpace O) ∈
          Subtype.val '' closure C.negativeBranch :=
      ⟨C.baseInLocalDomain, C.base_mem_closure_negativeBranch, rfl⟩
    have hpClosure :=
      image_closure_subset_closure_image continuous_subtype_val hpLocal
    simpa only [ActualFrontierIntervalChart.baseInLocalDomain] using hpClosure
  have hBranch :
      Subtype.val '' C.negativeBranch ⊆ ({p} : Set (FrontierSpace O))ᶜ := by
    rintro q ⟨r, hr, rfl⟩
    intro hrp
    have hrpEq : (r : FrontierSpace O) = p :=
      Set.mem_singleton_iff.mp hrp
    have hrBase : r = C.baseInLocalDomain := by
      apply Subtype.ext
      simpa only [ActualFrontierIntervalChart.baseInLocalDomain] using hrpEq
    subst r
    have hBaseNot : C.baseInLocalDomain ∉ C.negativeBranch := by
      change ¬ C.parameterHomeomorph C.baseInLocalDomain < C.zeroParameter
      rw [C.parameterHomeomorph_base]
      exact lt_irrefl _
    exact hBaseNot hr
  exact mem_closure_iff_nhdsWithin_neBot.mp
    (closure_mono hBranch hpImage)

namespace FiniteChartCutSystem

variable {A : BoundaryHalfSpaceAtlas O}

/-- The selected actual chart attached to one retained center. -/
noncomputable def arc (D : FiniteChartCutSystem A) (i : D.centers) :
    ActualFrontierIntervalChart O i.1 :=
  A.intervalAt i.1

/-- The finite set of prescribed junctions and all actual endpoints of all
selected compact subarcs. -/
noncomputable def cutPoints (D : FiniteChartCutSystem A) :
    Finset (FrontierSpace O) :=
  D.additionalCutPoints ∪
    D.centers.biUnion fun p => (A.intervalAt p).endpointFinset

/-- Every prescribed geometric junction is retained by the global cut. -/
theorem additionalCutPoint_mem_cutPoints
    (D : FiniteChartCutSystem A) {p : FrontierSpace O}
    (hp : p ∈ D.additionalCutPoints) :
    p ∈ D.cutPoints := by
  exact Finset.mem_union_left _ hp

/-- Every selected left endpoint belongs to the global cut set. -/
theorem leftEndpoint_mem_cutPoints
    (D : FiniteChartCutSystem A) (i : D.centers) :
    (D.arc i).leftEndpoint ∈ D.cutPoints := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.2
    ⟨i.1, i.2, by simp [arc, ActualFrontierIntervalChart.endpointFinset]⟩

/-- Every selected right endpoint belongs to the global cut set. -/
theorem rightEndpoint_mem_cutPoints
    (D : FiniteChartCutSystem A) (i : D.centers) :
    (D.arc i).rightEndpoint ∈ D.cutPoints := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.2
    ⟨i.1, i.2, by simp [arc, ActualFrontierIntervalChart.endpointFinset]⟩

/-- The actual frontier after deleting the finite endpoint cut set. -/
abbrev CutSpace (D : FiniteChartCutSystem A) :=
  {q : FrontierSpace O // q ∉ D.cutPoints}

/-- Real parameters on a selected compact core whose actual images are global
cut points. -/
def coreCutParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) : Set ℝ :=
  Subtype.val '' ((D.arc i).corePoint ⁻¹'
    (D.cutPoints : Set (FrontierSpace O)))

/-- Only finitely many selected-core parameters map to global cut points. -/
theorem finite_coreCutParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) :
    (D.coreCutParameterSet i).Finite := by
  apply Set.Finite.image
  exact Set.Finite.preimage (D.arc i).injective_corePoint.injOn
    D.cutPoints.finite_toSet

/-- The finite set of cut parameters on one selected compact core. -/
noncomputable def coreCutParameters
    (D : FiniteChartCutSystem A) (i : D.centers) : Finset ℝ :=
  (D.finite_coreCutParameterSet i).toFinset

/-- Membership in the selected-core cut-parameter set is exactly membership of
the represented actual point in the global cut set. -/
theorem mem_coreCutParameters_iff
    (D : FiniteChartCutSystem A) (i : D.centers)
    (t : (D.arc i).CoreParameter) :
    (t : ℝ) ∈ D.coreCutParameters i ↔
      (D.arc i).corePoint t ∈ D.cutPoints := by
  classical
  rw [coreCutParameters, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨s, hs, hst⟩
    have hEq : s = t := Subtype.ext hst
    change (D.arc i).corePoint s ∈ D.cutPoints at hs
    simpa only [hEq] using hs
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- Compact-core parameters whose actual points survive the global cuts. -/
abbrev CoreCutParameterSpace
    (D : FiniteChartCutSystem A) (i : D.centers) :=
  {t : (D.arc i).CoreParameter //
    (D.arc i).corePoint t ∉ D.cutPoints}

/-- The compact core interval inside the real complement of its finite cut
parameters. -/
def coreIntervalInRealCut
    (D : FiniteChartCutSystem A) (i : D.centers) :
    Set {t : ℝ // t ∉ D.coreCutParameters i} :=
  {t | t.1 ∈ Icc (-(D.arc i).coreRadius) (D.arc i).coreRadius}

/-- The selected compact core interval is clopen after its endpoint parameters
and all other global cut parameters are removed. -/
theorem isClopen_coreIntervalInRealCut
    (D : FiniteChartCutSystem A) (i : D.centers) :
    IsClopen (D.coreIntervalInRealCut i) := by
  have hLeft :
      -(D.arc i).coreRadius ∈ D.coreCutParameters i := by
    have h :=
      (D.mem_coreCutParameters_iff i (D.arc i).leftCoreParameter).2
        (D.leftEndpoint_mem_cutPoints i)
    exact h
  have hRight :
      (D.arc i).coreRadius ∈ D.coreCutParameters i := by
    have h :=
      (D.mem_coreCutParameters_iff i (D.arc i).rightCoreParameter).2
        (D.rightEndpoint_mem_cutPoints i)
    exact h
  constructor
  · exact isClosed_Icc.preimage continuous_subtype_val
  · have heq : D.coreIntervalInRealCut i =
        {t : {t : ℝ // t ∉ D.coreCutParameters i} |
          t.1 ∈ Ioo (-(D.arc i).coreRadius) (D.arc i).coreRadius} := by
      ext t
      constructor
      · intro ht
        have hLeftNe : -(D.arc i).coreRadius ≠ t.1 := by
          intro h
          apply t.2
          rw [← h]
          exact hLeft
        have hRightNe : t.1 ≠ (D.arc i).coreRadius := by
          intro h
          apply t.2
          rw [h]
          exact hRight
        exact ⟨lt_of_le_of_ne ht.1 hLeftNe,
          lt_of_le_of_ne ht.2 hRightNe⟩
      · exact fun ht => ⟨ht.1.le, ht.2.le⟩
    rw [heq]
    exact isOpen_Ioo.preimage continuous_subtype_val

/-- Reassociating the two subtype conditions identifies surviving compact-core
parameters with the clopen core interval in the finite real cut complement. -/
noncomputable def coreCutParameterHomeomorph
    (D : FiniteChartCutSystem A) (i : D.centers) :
    D.CoreCutParameterSpace i ≃ₜ D.coreIntervalInRealCut i where
  toEquiv :=
    { toFun := fun t =>
        ⟨⟨t.1.1, fun ht =>
          t.2 ((D.mem_coreCutParameters_iff i t.1).1 ht)⟩, t.1.2⟩
      invFun := fun t =>
        ⟨⟨t.1.1, t.2⟩, fun ht =>
          t.1.2 ((D.mem_coreCutParameters_iff i ⟨t.1.1, t.2⟩).2 ht)⟩
      left_inv := by
        intro t
        rfl
      right_inv := by
        intro t
        rfl }
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- Each selected compact core has only finitely many connected pieces after
the global endpoint cuts. -/
theorem finite_coreCutParameter_connectedComponents
    (D : FiniteChartCutSystem A) (i : D.centers) :
    Finite (ConnectedComponents (D.CoreCutParameterSpace i)) := by
  letI : Finite
      (ConnectedComponents {t : ℝ // t ∉ D.coreCutParameters i}) :=
    RealFiniteCuts.finite_connectedComponents_compl (D.coreCutParameters i)
  letI : Finite
      (ConnectedComponents (D.coreIntervalInRealCut i)) :=
    finiteConnectedComponents_clopenSubtype
      (D.isClopen_coreIntervalInRealCut i)
  exact finiteConnectedComponents_of_homeomorph
    (D.coreCutParameterHomeomorph i)
/-- The complement of the finite actual endpoint set is open in the complete
frontier subtype. -/
theorem isOpen_cutSpaceCarrier (D : FiniteChartCutSystem A) :
    IsOpen {q : FrontierSpace O | q ∉ D.cutPoints} := by
  change IsOpen ((D.cutPoints : Set (FrontierSpace O))ᶜ)
  exact D.cutPoints.finite_toSet.isClosed.isOpen_compl

/-- The cut frontier remains locally connected. -/
theorem cutSpaceLocallyConnectedSpace
    (D : FiniteChartCutSystem A) : LocallyConnectedSpace D.CutSpace := by
  letI : LocallyConnectedSpace (FrontierSpace O) :=
    A.frontierLocallyConnectedSpace
  exact D.isOpen_cutSpaceCarrier.locallyConnectedSpace


/-- The realization in the complete actual frontier of one connected piece
remaining after the finite cuts. -/
def cutComponentImage (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    Set (FrontierSpace O) :=
  Subtype.val '' connectedComponent x

/-- One connected piece of the cut frontier, retained as its own subtype. -/
abbrev CutComponent (D : FiniteChartCutSystem A) (x : D.CutSpace) :=
  {y : D.CutSpace // y ∈ connectedComponent x}

/-- Every cut component has a nonempty actual realization. -/
theorem cutComponentImage_nonempty
    (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    (D.cutComponentImage x).Nonempty :=
  ⟨x.1, x, mem_connectedComponent, rfl⟩

/-- Every cut-component realization is connected. -/
theorem isConnected_cutComponentImage
    (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    IsConnected (D.cutComponentImage x) :=
  isConnected_connectedComponent.image Subtype.val
    continuous_subtype_val.continuousOn

/-- Every cut-component realization is open in the complete actual frontier. -/
theorem isOpen_cutComponentImage
    (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    IsOpen (D.cutComponentImage x) := by
  letI : LocallyConnectedSpace (FrontierSpace O) :=
    A.frontierLocallyConnectedSpace
  letI : LocallyConnectedSpace D.CutSpace :=
    D.cutSpaceLocallyConnectedSpace
  exact D.isOpen_cutSpaceCarrier.isOpenMap_subtype_val _
    (isOpen_connectedComponent (x := x))

/-- Distinct connected pieces remain disjoint after realization in the actual
frontier. -/
theorem disjoint_cutComponentImage
    (D : FiniteChartCutSystem A) (x y : D.CutSpace)
    (hxy : connectedComponent x ≠ connectedComponent y) :
    Disjoint (D.cutComponentImage x) (D.cutComponentImage y) :=
  Disjoint.image (connectedComponent_disjoint hxy)
    Subtype.val_injective.injOn (subset_univ _) (subset_univ _)

/-- The realized cut components exhaust exactly the actual frontier away from
the finite cut set. -/
theorem iUnion_cutComponentImage_eq_cutSpaceCarrier
    (D : FiniteChartCutSystem A) :
    (⋃ x : D.CutSpace, D.cutComponentImage x) =
      {q : FrontierSpace O | q ∉ D.cutPoints} := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨x, hx⟩ := mem_iUnion.1 hq
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro q hq
    let x : D.CutSpace := ⟨q, hq⟩
    exact mem_iUnion.2 ⟨x, x, mem_connectedComponent, rfl⟩

/-- The part of one selected compact core remaining in the cut space. -/
def closedCoreInCutSpace (D : FiniteChartCutSystem A) (i : D.centers) :
    Set D.CutSpace :=
  {q | q.1 ∈ (D.arc i).closedCore}

/-- A surviving compact-core parameter as a point of the selected core inside
the global cut space. -/
def coreCutPoint
    (D : FiniteChartCutSystem A) (i : D.centers)
    (t : D.CoreCutParameterSpace i) :
    D.closedCoreInCutSpace i :=
  ⟨⟨(D.arc i).corePoint t.1, t.2⟩, ⟨t.1, rfl⟩⟩

/-- The surviving parameters of one selected compact core are homeomorphic to
that core's actual points in the global cut space. -/
noncomputable def coreCutPointHomeomorph
    (D : FiniteChartCutSystem A) (i : D.centers) :
    D.CoreCutParameterSpace i ≃ₜ D.closedCoreInCutSpace i := by
  have hContinuous : Continuous (D.coreCutPoint i) := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (D.arc i).continuous_corePoint.comp continuous_subtype_val
  have hForget : Continuous
      (fun q : D.closedCoreInCutSpace i => q.1.1) := by
    fun_prop
  have hCoreEmbedding : Topology.IsEmbedding
      (fun t : D.CoreCutParameterSpace i =>
        (D.arc i).corePoint t.1) :=
    (D.arc i).isClosedEmbedding_corePoint.isEmbedding.comp
      Topology.IsEmbedding.subtypeVal
  have hEmbedding : Topology.IsEmbedding (D.coreCutPoint i) := by
    apply Topology.IsEmbedding.of_comp hContinuous hForget
    have hfun :
        (fun q : D.closedCoreInCutSpace i => q.1.1) ∘
            D.coreCutPoint i =
          (fun t : D.CoreCutParameterSpace i =>
            (D.arc i).corePoint t.1) := by
      funext t
      rfl
    rw [hfun]
    exact hCoreEmbedding
  apply hEmbedding.toHomeomorphOfSurjective
  intro q
  obtain ⟨t, ht⟩ := q.2
  let tCut : D.CoreCutParameterSpace i :=
    ⟨t, by
      intro htCut
      exact q.1.2 (ht ▸ htCut)⟩
  refine ⟨tCut, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact ht

/-- Every selected actual compact core has finitely many connected components
after the global cuts. -/
theorem finite_closedCoreInCutSpace_connectedComponents
    (D : FiniteChartCutSystem A) (i : D.centers) :
    Finite (ConnectedComponents (D.closedCoreInCutSpace i)) := by
  letI : Finite
      (ConnectedComponents (D.CoreCutParameterSpace i)) :=
    D.finite_coreCutParameter_connectedComponents i
  exact finiteConnectedComponents_of_homeomorph
    (D.coreCutPointHomeomorph i).symm

/-- On the cut complement, the closed core equals its open relative interior. -/
theorem mem_closedCoreInCutSpace_iff_mem_coreInterior
    (D : FiniteChartCutSystem A) (i : D.centers) (q : D.CutSpace) :
    q ∈ D.closedCoreInCutSpace i ↔ q.1 ∈ (D.arc i).coreInterior := by
  have hqLeft : q.1 ≠ (D.arc i).leftEndpoint := by
    intro h
    exact q.2 (h ▸ D.leftEndpoint_mem_cutPoints i)
  have hqRight : q.1 ≠ (D.arc i).rightEndpoint := by
    intro h
    exact q.2 (h ▸ D.rightEndpoint_mem_cutPoints i)
  exact ((D.arc i).mem_coreInterior_iff_mem_closedCore_of_ne_endpoints
    hqLeft hqRight).symm

/-- A selected compact core becomes clopen after all selected endpoints are
removed. -/
theorem isClopen_closedCoreInCutSpace
    (D : FiniteChartCutSystem A) (i : D.centers) :
    IsClopen (D.closedCoreInCutSpace i) := by
  constructor
  · exact (D.arc i).isClosed_closedCore.preimage continuous_subtype_val
  · have heq : D.closedCoreInCutSpace i =
        {q : D.CutSpace | q.1 ∈ (D.arc i).coreInterior} := by
      ext q
      exact D.mem_closedCoreInCutSpace_iff_mem_coreInterior i q
    rw [heq]
    exact (D.arc i).isOpen_coreInterior.preimage continuous_subtype_val

/-- The actual frontier cut by all selected chart endpoints has only finitely
many connected pieces. -/
theorem finite_cutSpace_connectedComponents
    (D : FiniteChartCutSystem A) :
    Finite (ConnectedComponents D.CutSpace) := by
  apply finiteConnectedComponents_of_finite_iUnion
    (fun i : D.centers => D.closedCoreInCutSpace i)
    (fun i => D.finite_closedCoreInCutSpace_connectedComponents i)
  apply Set.eq_univ_of_univ_subset
  intro q _hq
  have hqCover : q.1 ∈
      ⋃ i : D.centers, (A.intervalAt i.1).coreInterior :=
    D.covers (mem_univ q.1)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hqCover
  exact mem_iUnion.2
    ⟨i, (D.mem_closedCoreInCutSpace_iff_mem_coreInterior i q).2 hi⟩

/-- Any punctured connected component meeting a selected relative interior is
confined to that selected compact embedded interval. -/
theorem connectedComponent_subset_closedCore
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    connectedComponent x ⊆ D.closedCoreInCutSpace i := by
  apply (D.isClopen_closedCoreInCutSpace i).connectedComponent_subset
  exact (D.mem_closedCoreInCutSpace_iff_mem_coreInterior i x).2 hx

/-- Every component left after the finite endpoint cuts is confined to one of
the finitely many selected embedded compact intervals. -/
theorem exists_arc_containing_connectedComponent
    (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    ∃ i : D.centers,
      ∀ y ∈ connectedComponent x, y.1 ∈ (D.arc i).closedCore := by
  have hxCover : x.1 ∈
      ⋃ i : D.centers, (A.intervalAt i.1).coreInterior :=
    D.covers (mem_univ x.1)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxCover
  refine ⟨i, ?_⟩
  intro y hy
  exact D.connectedComponent_subset_closedCore i x hi hy

/-- The actual realization of a confined cut component lies in the relative
interior of the selected chart core. -/
theorem cutComponentImage_subset_coreInterior
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentImage x ⊆ (D.arc i).coreInterior := by
  rintro q ⟨y, hy, rfl⟩
  have hyCore :=
    D.connectedComponent_subset_closedCore i x hx hy
  exact (D.mem_closedCoreInCutSpace_iff_mem_coreInterior i y).1 hyCore

/-- A cut component lifted into the local-domain subtype of a selected chart. -/
def cutComponentLocal
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    Set (D.arc i).localDomain :=
  {q | q.1 ∈ D.cutComponentImage x}

/-- The local lift realizes exactly the actual cut component whenever that
component meets the selected core interior. -/
theorem image_cutComponentLocal
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    Subtype.val '' D.cutComponentLocal i x = D.cutComponentImage x := by
  apply Subset.antisymm
  · rintro q ⟨qLocal, hq, rfl⟩
    exact hq
  · intro q hq
    rcases D.cutComponentImage_subset_coreInterior i x hx hq with
      ⟨qLocal, _hqLocalInterior, hqLocal⟩
    refine ⟨qLocal, ?_, hqLocal⟩
    change qLocal.1 ∈ D.cutComponentImage x
    rw [hqLocal]
    exact hq

/-- The local lift of a cut component is open in the selected chart domain. -/
theorem isOpen_cutComponentLocal
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    IsOpen (D.cutComponentLocal i x) :=
  (D.isOpen_cutComponentImage x).preimage continuous_subtype_val

/-- The local lift of a confined cut component is connected. -/
theorem isConnected_cutComponentLocal
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    IsConnected (D.cutComponentLocal i x) := by
  constructor
  · obtain ⟨q, hq⟩ := D.cutComponentImage_nonempty x
    have hqImage : q ∈
        Subtype.val '' D.cutComponentLocal i x := by
      rw [D.image_cutComponentLocal i x hx]
      exact hq
    rcases hqImage with ⟨qLocal, hqLocal, _⟩
    exact ⟨qLocal, hqLocal⟩
  · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [D.image_cutComponentLocal i x hx]
    exact (D.isConnected_cutComponentImage x).isPreconnected

/-- Real chart parameters occupied by one cut component. -/
def cutComponentParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    Set (D.arc i).parameterInterval :=
  (D.arc i).parameterHomeomorph '' D.cutComponentLocal i x

/-- The parameter image of a cut component is open. -/
theorem isOpen_cutComponentParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    IsOpen (D.cutComponentParameterImage i x) :=
  (D.arc i).parameterHomeomorph.isOpenMap _
    (D.isOpen_cutComponentLocal i x)

/-- The parameter image of a confined cut component is connected. -/
theorem isConnected_cutComponentParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    IsConnected (D.cutComponentParameterImage i x) :=
  (D.isConnected_cutComponentLocal i x hx).image
    (D.arc i).parameterHomeomorph
    (D.arc i).parameterHomeomorph.continuous.continuousOn

/-- Ordinary real parameters occupied by one cut component. -/
def cutComponentRealParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    Set ℝ :=
  Subtype.val '' D.cutComponentParameterImage i x

/-- The real parameter image of a cut component is open in `ℝ`. -/
theorem isOpen_cutComponentRealParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    IsOpen (D.cutComponentRealParameterImage i x) := by
  apply (show IsOpen (D.arc i).parameterInterval from isOpen_Ioo).isOpenMap_subtype_val
  exact D.isOpen_cutComponentParameterImage i x

/-- The real parameter image of a confined cut component is connected. -/
theorem isConnected_cutComponentRealParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    IsConnected (D.cutComponentRealParameterImage i x) :=
  (D.isConnected_cutComponentParameterImage i x hx).image Subtype.val
    continuous_subtype_val.continuousOn

/-- Confined component parameters stay strictly between the two selected core
endpoints. -/
theorem cutComponentRealParameterImage_subset_core
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentRealParameterImage i x ⊆
      Ioo (-(D.arc i).coreRadius) (D.arc i).coreRadius := by
  rintro t ⟨tChart, ⟨qLocal, hqComponent, rfl⟩, rfl⟩
  have hqInterior :=
    D.cutComponentImage_subset_coreInterior i x hx hqComponent
  rcases hqInterior with ⟨rLocal, hrInterior, hrEq⟩
  have hlocalEq : qLocal = rLocal := Subtype.ext hrEq.symm
  change (↑((D.arc i).parameterHomeomorph rLocal) : ℝ) ∈
    Ioo (-(D.arc i).coreRadius) (D.arc i).coreRadius at hrInterior
  simpa only [hlocalEq] using hrInterior

/-- A confined cut component is homeomorphic to its ordinary real parameter
image, not merely in bijection with it. -/
noncomputable def cutComponentHomeomorphRealParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.CutComponent x ≃ₜ D.cutComponentRealParameterImage i x := by
  let componentToImage :
      D.CutComponent x ≃ₜ D.cutComponentImage x :=
    Topology.IsEmbedding.subtypeVal.homeomorphImage (connectedComponent x)
  let localToImage :
      D.cutComponentLocal i x ≃ₜ D.cutComponentImage x :=
    (Topology.IsEmbedding.subtypeVal.homeomorphImage
      (D.cutComponentLocal i x)).trans
        (Homeomorph.setCongr (D.image_cutComponentLocal i x hx))
  let f : (D.arc i).localDomain → ℝ :=
    fun q => ((D.arc i).parameterHomeomorph q : ℝ)
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp
      (D.arc i).parameterHomeomorph.isEmbedding
  have hImage : f '' D.cutComponentLocal i x =
      D.cutComponentRealParameterImage i x := by
    simp only [f, cutComponentRealParameterImage,
      cutComponentParameterImage, Set.image_image]
  let localToParameter :
      D.cutComponentLocal i x ≃ₜ
        D.cutComponentRealParameterImage i x :=
    (hf.homeomorphImage (D.cutComponentLocal i x)).trans
      (Homeomorph.setCongr hImage)
  exact componentToImage.trans (localToImage.symm.trans localToParameter)

/-- A confined cut component occupies exactly one bounded open real interval in
the selected chart coordinates. -/
theorem cutComponentRealParameterImage_eq_Ioo
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentRealParameterImage i x =
      Ioo (sInf (D.cutComponentRealParameterImage i x))
        (sSup (D.cutComponentRealParameterImage i x)) := by
  have hSubset :=
    D.cutComponentRealParameterImage_subset_core i x hx
  have hBelow : BddBelow (D.cutComponentRealParameterImage i x) := by
    refine ⟨-(D.arc i).coreRadius, ?_⟩
    intro t ht
    exact (hSubset ht).1.le
  have hAbove : BddAbove (D.cutComponentRealParameterImage i x) := by
    refine ⟨(D.arc i).coreRadius, ?_⟩
    intro t ht
    exact (hSubset ht).2.le
  exact openConnectedRealSet_eq_Ioo_sInf_sSup
    (D.isOpen_cutComponentRealParameterImage i x)
    (D.isConnected_cutComponentRealParameterImage i x hx)
    hBelow hAbove

/-- The two coordinate endpoints of a confined cut component are distinct. -/
theorem cutComponentRealParameter_sInf_lt_sSup
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    sInf (D.cutComponentRealParameterImage i x) <
      sSup (D.cutComponentRealParameterImage i x) := by
  have hsConnected :=
    D.isConnected_cutComponentRealParameterImage i x hx
  have hsEq :=
    D.cutComponentRealParameterImage_eq_Ioo i x hx
  obtain ⟨t, ht⟩ := hsConnected.nonempty
  rw [hsEq] at ht
  exact ht.1.trans ht.2

/-- Both coordinate closure endpoints remain inside the selected compact core. -/
theorem cutComponentRealParameter_endpoints_mem_core
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    sInf (D.cutComponentRealParameterImage i x) ∈
        Icc (-(D.arc i).coreRadius) (D.arc i).coreRadius ∧
      sSup (D.cutComponentRealParameterImage i x) ∈
        Icc (-(D.arc i).coreRadius) (D.arc i).coreRadius := by
  let s := D.cutComponentRealParameterImage i x
  have hSubset : s ⊆
      Ioo (-(D.arc i).coreRadius) (D.arc i).coreRadius :=
    D.cutComponentRealParameterImage_subset_core i x hx
  have hNonempty : s.Nonempty :=
    (D.isConnected_cutComponentRealParameterImage i x hx).nonempty
  obtain ⟨t, ht⟩ := hNonempty
  have hBelow : BddBelow s :=
    ⟨-(D.arc i).coreRadius, fun y hy => (hSubset hy).1.le⟩
  have hAbove : BddAbove s :=
    ⟨(D.arc i).coreRadius, fun y hy => (hSubset hy).2.le⟩
  constructor
  · exact ⟨le_csInf ⟨t, ht⟩ (fun y hy => (hSubset hy).1.le),
      (csInf_le hBelow ht).trans (hSubset ht).2.le⟩
  · exact ⟨(hSubset ht).1.le.trans (le_csSup hAbove ht),
      csSup_le ⟨t, ht⟩ (fun y hy => (hSubset hy).2.le)⟩

/-- The coordinate closure of a confined cut component is exactly the compact
closed interval between its two distinct endpoint parameters. -/
theorem closure_cutComponentRealParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    closure (D.cutComponentRealParameterImage i x) =
      Icc (sInf (D.cutComponentRealParameterImage i x))
        (sSup (D.cutComponentRealParameterImage i x)) := by
  calc
    closure (D.cutComponentRealParameterImage i x) =
        closure (Ioo (sInf (D.cutComponentRealParameterImage i x))
          (sSup (D.cutComponentRealParameterImage i x))) :=
      congrArg closure (D.cutComponentRealParameterImage_eq_Ioo i x hx)
    _ = Icc (sInf (D.cutComponentRealParameterImage i x))
          (sSup (D.cutComponentRealParameterImage i x)) :=
      closure_Ioo
        (D.cutComponentRealParameter_sInf_lt_sSup i x hx).ne

/-- The coordinate closure of every confined cut component is compact. -/
theorem isCompact_closure_cutComponentRealParameterImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    IsCompact (closure (D.cutComponentRealParameterImage i x)) := by
  rw [D.closure_cutComponentRealParameterImage i x hx]
  exact isCompact_Icc

/-- A compact-core parameter on the boundary of a confined component's real
parameter image must represent a global cut point. -/
theorem corePoint_mem_cutPoints_of_mem_parameterClosure
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) {e : ℝ}
    (heCore : e ∈ Icc (-(D.arc i).coreRadius) (D.arc i).coreRadius)
    (heClosure : e ∈ closure (D.cutComponentRealParameterImage i x))
    (heOutside : e ∉ D.cutComponentRealParameterImage i x) :
    (D.arc i).corePoint ⟨e, heCore⟩ ∈ D.cutPoints := by
  let eCore : (D.arc i).CoreParameter := ⟨e, heCore⟩
  let eChart : (D.arc i).parameterInterval :=
    (D.arc i).coreParameterToParameterInterval eCore
  let qLocal : (D.arc i).localDomain :=
    (D.arc i).parameterHomeomorph.symm eChart
  by_contra heNotCut
  let y : D.CutSpace :=
    ⟨qLocal.1, by
      simpa only [qLocal, eChart, eCore,
        ActualFrontierIntervalChart.corePoint] using heNotCut⟩
  have heChartClosure :
      eChart ∈ closure (D.cutComponentParameterImage i x) := by
    apply (closure_subtype).2
    change e ∈ closure (D.cutComponentRealParameterImage i x)
    exact heClosure
  have hqInverseImage :
      (D.arc i).parameterHomeomorph.symm eChart ∈
        (D.arc i).parameterHomeomorph.symm ''
          closure (D.cutComponentParameterImage i x) :=
    ⟨eChart, heChartClosure, rfl⟩
  rw [(D.arc i).parameterHomeomorph.symm.image_closure] at hqInverseImage
  have hBack :
      (D.arc i).parameterHomeomorph.symm ''
          D.cutComponentParameterImage i x =
        D.cutComponentLocal i x := by
    apply Subset.antisymm
    · rintro q ⟨t, ⟨r, hr, hrt⟩, htq⟩
      subst t
      have hrq : r = q := by
        simpa only [(D.arc i).parameterHomeomorph.symm_apply_apply] using htq
      exact hrq ▸ hr
    · intro q hq
      exact ⟨(D.arc i).parameterHomeomorph q,
        ⟨q, hq, rfl⟩,
        (D.arc i).parameterHomeomorph.symm_apply_apply q⟩
  rw [hBack] at hqInverseImage
  have hqClosure : qLocal ∈ closure (D.cutComponentLocal i x) := by
    exact hqInverseImage
  have hActualClosure :
      qLocal.1 ∈ closure (D.cutComponentImage x) := by
    have hImageClosure :=
      (image_closure_subset_closure_image continuous_subtype_val)
        (show qLocal.1 ∈
          Subtype.val '' closure (D.cutComponentLocal i x) from
            ⟨qLocal, hqClosure, rfl⟩)
    rw [D.image_cutComponentLocal i x hx] at hImageClosure
    exact hImageClosure
  have hyClosure : y ∈ closure (connectedComponent x) := by
    apply (closure_subtype).2
    simpa only [cutComponentImage] using hActualClosure
  have hyComponent : y ∈ connectedComponent x := by
    rw [closure_eq_iff_isClosed.mpr isClosed_connectedComponent] at hyClosure
    exact hyClosure
  have hqComponent : qLocal.1 ∈ D.cutComponentImage x :=
    ⟨y, hyComponent, rfl⟩
  have hqLocal : qLocal ∈ D.cutComponentLocal i x :=
    hqComponent
  apply heOutside
  refine ⟨(D.arc i).parameterHomeomorph qLocal,
    ⟨qLocal, hqLocal, rfl⟩, ?_⟩
  have hApply :
      (D.arc i).parameterHomeomorph qLocal = eChart := by
    exact (D.arc i).parameterHomeomorph.apply_symm_apply eChart
  exact congrArg Subtype.val hApply

/-- Left compact-core parameter of the closure of a confined cut component. -/
noncomputable def cutComponentLeftCoreParameter
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    (D.arc i).CoreParameter :=
  ⟨sInf (D.cutComponentRealParameterImage i x),
    (D.cutComponentRealParameter_endpoints_mem_core i x hx).1⟩

/-- Right compact-core parameter of the closure of a confined cut component. -/
noncomputable def cutComponentRightCoreParameter
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    (D.arc i).CoreParameter :=
  ⟨sSup (D.cutComponentRealParameterImage i x),
    (D.cutComponentRealParameter_endpoints_mem_core i x hx).2⟩

/-- Actual left endpoint of the closure of a confined cut component. -/
noncomputable def cutComponentLeftEndpoint
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) : FrontierSpace O :=
  (D.arc i).corePoint (D.cutComponentLeftCoreParameter i x hx)

/-- Actual right endpoint of the closure of a confined cut component. -/
noncomputable def cutComponentRightEndpoint
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) : FrontierSpace O :=
  (D.arc i).corePoint (D.cutComponentRightCoreParameter i x hx)

/-- The actual left closure endpoint is one of the finite global cut points. -/
theorem cutComponentLeftEndpoint_mem_cutPoints
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentLeftEndpoint i x hx ∈ D.cutPoints := by
  have hClosure :
      sInf (D.cutComponentRealParameterImage i x) ∈
        closure (D.cutComponentRealParameterImage i x) := by
    rw [D.closure_cutComponentRealParameterImage i x hx]
    exact left_mem_Icc.mpr
      (D.cutComponentRealParameter_sInf_lt_sSup i x hx).le
  have hOutside :
      sInf (D.cutComponentRealParameterImage i x) ∉
        D.cutComponentRealParameterImage i x := by
    intro h
    have hIoo :=
      (Set.ext_iff.mp
        (D.cutComponentRealParameterImage_eq_Ioo i x hx)
        (sInf (D.cutComponentRealParameterImage i x))).1 h
    exact lt_irrefl _ hIoo.1
  simpa only [cutComponentLeftEndpoint, cutComponentLeftCoreParameter] using
    D.corePoint_mem_cutPoints_of_mem_parameterClosure i x hx
      (D.cutComponentRealParameter_endpoints_mem_core i x hx).1
      hClosure hOutside

/-- The actual right closure endpoint is one of the finite global cut points. -/
theorem cutComponentRightEndpoint_mem_cutPoints
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentRightEndpoint i x hx ∈ D.cutPoints := by
  have hClosure :
      sSup (D.cutComponentRealParameterImage i x) ∈
        closure (D.cutComponentRealParameterImage i x) := by
    rw [D.closure_cutComponentRealParameterImage i x hx]
    exact right_mem_Icc.mpr
      (D.cutComponentRealParameter_sInf_lt_sSup i x hx).le
  have hOutside :
      sSup (D.cutComponentRealParameterImage i x) ∉
        D.cutComponentRealParameterImage i x := by
    intro h
    have hIoo :=
      (Set.ext_iff.mp
        (D.cutComponentRealParameterImage_eq_Ioo i x hx)
        (sSup (D.cutComponentRealParameterImage i x))).1 h
    exact lt_irrefl _ hIoo.2
  simpa only [cutComponentRightEndpoint, cutComponentRightCoreParameter] using
    D.corePoint_mem_cutPoints_of_mem_parameterClosure i x hx
      (D.cutComponentRealParameter_endpoints_mem_core i x hx).2
      hClosure hOutside

/-- The two actual closure endpoints of a cut component are distinct. -/
theorem cutComponentLeftEndpoint_ne_rightEndpoint
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentLeftEndpoint i x hx ≠
      D.cutComponentRightEndpoint i x hx := by
  intro hEndpoints
  have hParameters :=
    (D.arc i).injective_corePoint hEndpoints
  have hRealParameters := congrArg Subtype.val hParameters
  exact (D.cutComponentRealParameter_sInf_lt_sSup i x hx).ne
    hRealParameters

/-- Compact-core parameters occupied by the open cut component. -/
def cutComponentOpenCoreParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    Set (D.arc i).CoreParameter :=
  {t | (t : ℝ) ∈ D.cutComponentRealParameterImage i x}

/-- Compact-core parameters in the closed interval between the two component
endpoints. -/
def cutComponentClosedCoreParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    Set (D.arc i).CoreParameter :=
  {t | (t : ℝ) ∈
    Icc (sInf (D.cutComponentRealParameterImage i x))
      (sSup (D.cutComponentRealParameterImage i x))}

/-- Forgetting the compact-core subtype realizes exactly the component's open
real parameter image. -/
theorem image_cutComponentOpenCoreParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    Subtype.val '' D.cutComponentOpenCoreParameterSet i x =
      D.cutComponentRealParameterImage i x := by
  apply Subset.antisymm
  · rintro t ⟨s, hs, rfl⟩
    exact hs
  · intro t ht
    have htCore :=
      D.cutComponentRealParameterImage_subset_core i x hx ht
    let s : (D.arc i).CoreParameter :=
      ⟨t, htCore.1.le, htCore.2.le⟩
    exact ⟨s, ht, rfl⟩

/-- The compact-core parameterization realizes exactly the actual cut
component before taking closures. -/
theorem image_corePoint_cutComponentOpenCoreParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    (D.arc i).corePoint '' D.cutComponentOpenCoreParameterSet i x =
      D.cutComponentImage x := by
  apply Subset.antisymm
  · rintro q ⟨t, ht, rfl⟩
    change (t : ℝ) ∈ D.cutComponentRealParameterImage i x at ht
    rcases ht with ⟨tChart, ⟨qLocal, hqLocal, hqChart⟩, htReal⟩
    subst tChart
    have hParameter :
        (D.arc i).parameterHomeomorph qLocal =
          (D.arc i).coreParameterToParameterInterval t :=
      Subtype.ext htReal
    have hLocal :
        qLocal =
          (D.arc i).parameterHomeomorph.symm
            ((D.arc i).coreParameterToParameterInterval t) := by
      apply (D.arc i).parameterHomeomorph.injective
      rw [(D.arc i).parameterHomeomorph.apply_symm_apply]
      exact hParameter
    have hPoint : (D.arc i).corePoint t = qLocal.1 := by
      unfold ActualFrontierIntervalChart.corePoint
      rw [← hLocal]
    rw [hPoint]
    exact hqLocal
  · intro q hq
    have hqInterior :=
      D.cutComponentImage_subset_coreInterior i x hx hq
    rcases hqInterior with ⟨qLocal, hqParameter, hqPoint⟩
    let t : (D.arc i).CoreParameter :=
      ⟨((D.arc i).parameterHomeomorph qLocal : ℝ),
        hqParameter.1.le, hqParameter.2.le⟩
    have hqLocal : qLocal ∈ D.cutComponentLocal i x := by
      change qLocal.1 ∈ D.cutComponentImage x
      rw [hqPoint]
      exact hq
    have htOpen : t ∈ D.cutComponentOpenCoreParameterSet i x := by
      change (t : ℝ) ∈ D.cutComponentRealParameterImage i x
      exact ⟨(D.arc i).parameterHomeomorph qLocal,
        ⟨qLocal, hqLocal, rfl⟩, rfl⟩
    refine ⟨t, htOpen, ?_⟩
    have hParameter :
        (D.arc i).coreParameterToParameterInterval t =
          (D.arc i).parameterHomeomorph qLocal :=
      Subtype.ext rfl
    unfold ActualFrontierIntervalChart.corePoint
    rw [hParameter, (D.arc i).parameterHomeomorph.symm_apply_apply]
    exact hqPoint

/-- Closing the component's compact-core parameters adds exactly the two
endpoint parameters. -/
theorem closure_cutComponentOpenCoreParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    closure (D.cutComponentOpenCoreParameterSet i x) =
      D.cutComponentClosedCoreParameterSet i x := by
  ext t
  rw [closure_subtype]
  rw [D.image_cutComponentOpenCoreParameterSet i x hx]
  change (t : ℝ) ∈ closure (D.cutComponentRealParameterImage i x) ↔
    (t : ℝ) ∈
      Icc (sInf (D.cutComponentRealParameterImage i x))
        (sSup (D.cutComponentRealParameterImage i x))
  rw [D.closure_cutComponentRealParameterImage i x hx]

/-- The actual compact closed arc associated with a confined cut component. -/
def cutComponentClosedArc
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    Set (FrontierSpace O) :=
  (D.arc i).corePoint '' D.cutComponentClosedCoreParameterSet i x

/-- The closure of the actual cut component is exactly its selected embedded
closed arc. -/
theorem closure_cutComponentImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    closure (D.cutComponentImage x) =
      D.cutComponentClosedArc i x := by
  calc
    closure (D.cutComponentImage x) =
        closure ((D.arc i).corePoint ''
          D.cutComponentOpenCoreParameterSet i x) :=
      congrArg closure
        (D.image_corePoint_cutComponentOpenCoreParameterSet i x hx).symm
    _ = (D.arc i).corePoint ''
        closure (D.cutComponentOpenCoreParameterSet i x) :=
      (D.arc i).isClosedEmbedding_corePoint.closure_image_eq _
    _ = D.cutComponentClosedArc i x := by
      rw [D.closure_cutComponentOpenCoreParameterSet i x hx]
      rfl

/-- The closed component-parameter interval is compact. -/
theorem isCompact_cutComponentClosedCoreParameterSet
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    IsCompact (D.cutComponentClosedCoreParameterSet i x) := by
  letI : CompactSpace (D.arc i).CoreParameter :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  exact (isClosed_Icc.preimage continuous_subtype_val).isCompact

/-- Every actual cut-component closure is compact. -/
theorem isCompact_cutComponentClosedArc
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    IsCompact (D.cutComponentClosedArc i x) :=
  (D.isCompact_cutComponentClosedCoreParameterSet i x).image
    (D.arc i).continuous_corePoint

/-- The closed component-parameter interval embeds homeomorphically as the
actual closed component arc. -/
noncomputable def cutComponentClosedArcHomeomorph
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace) :
    D.cutComponentClosedCoreParameterSet i x ≃ₜ
      D.cutComponentClosedArc i x :=
  (D.arc i).isClosedEmbedding_corePoint.isEmbedding.homeomorphImage _

/-- Every component produced by the finite endpoint cuts has a selected chart
in which its parameter realization is an actual nondegenerate open interval. -/
theorem exists_arc_parameterizing_cutComponent_as_Ioo
    (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    ∃ i : D.centers, ∃ a b : ℝ, a < b ∧
      D.cutComponentRealParameterImage i x = Ioo a b := by
  have hxCover : x.1 ∈
      ⋃ i : D.centers, (A.intervalAt i.1).coreInterior :=
    D.covers (mem_univ x.1)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxCover
  let s := D.cutComponentRealParameterImage i x
  have hsConnected : IsConnected s :=
    D.isConnected_cutComponentRealParameterImage i x hi
  have hsEq : s = Ioo (sInf s) (sSup s) :=
    D.cutComponentRealParameterImage_eq_Ioo i x hi
  refine ⟨i, sInf s, sSup s, ?_, hsEq⟩
  obtain ⟨t, ht⟩ := hsConnected.nonempty
  rw [hsEq] at ht
  exact ht.1.trans ht.2

/-- Each connected piece left by the finite cuts is genuinely homeomorphic to
a nondegenerate open real interval. -/
theorem exists_cutComponent_homeomorph_Ioo
    (D : FiniteChartCutSystem A) (x : D.CutSpace) :
    ∃ a b : ℝ, a < b ∧
      Nonempty (D.CutComponent x ≃ₜ (Ioo a b : Set ℝ)) := by
  have hxCover : x.1 ∈
      ⋃ i : D.centers, (A.intervalAt i.1).coreInterior :=
    D.covers (mem_univ x.1)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hxCover
  let s := D.cutComponentRealParameterImage i x
  have hsConnected : IsConnected s :=
    D.isConnected_cutComponentRealParameterImage i x hi
  have hsEq : s = Ioo (sInf s) (sSup s) :=
    D.cutComponentRealParameterImage_eq_Ioo i x hi
  have hab : sInf s < sSup s := by
    obtain ⟨t, ht⟩ := hsConnected.nonempty
    rw [hsEq] at ht
    exact ht.1.trans ht.2
  refine ⟨sInf s, sSup s, hab, ?_⟩
  exact ⟨(D.cutComponentHomeomorphRealParameterImage i x hi).trans
    (Homeomorph.setCongr hsEq)⟩

/-- The selected closed cores exhaust the complete actual frontier. -/
theorem iUnion_closedCore_eq_univ (D : FiniteChartCutSystem A) :
    (⋃ i : D.centers, (D.arc i).closedCore) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  intro q _hq
  have hqCover := D.covers (mem_univ q)
  obtain ⟨i, hi⟩ := mem_iUnion.1 hqCover
  exact mem_iUnion.2 ⟨i, (D.arc i).coreInterior_subset_closedCore hi⟩


/-- The finite, quotient-level index of the actual open arcs left by the
endpoint cuts.  Unlike an arbitrary point index, this names each connected
piece exactly once. -/
abbrev ArcIndex (D : FiniteChartCutSystem A) :=
  ConnectedComponents D.CutSpace

/-- A chosen actual point on one quotient-indexed open arc. -/
noncomputable def arcRepresentative
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) : D.CutSpace :=
  Classical.choose (ConnectedComponents.surjective_coe e)

@[simp] theorem arcRepresentative_class
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    (D.arcRepresentative e : ConnectedComponents D.CutSpace) = e :=
  Classical.choose_spec (ConnectedComponents.surjective_coe e)

/-- The actual open frontier arc represented by one quotient index. -/
def finiteArcInterior
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Set (FrontierSpace O) :=
  D.cutComponentImage (D.arcRepresentative e)

/-- The actual compact closure of one quotient-indexed frontier arc. -/
def finiteArcClosure
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Set (FrontierSpace O) :=
  closure (D.finiteArcInterior e)

/-- Different quotient-level arc indices have disjoint actual interiors. -/
theorem disjoint_finiteArcInterior
    (D : FiniteChartCutSystem A) {e f : D.ArcIndex} (hef : e ≠ f) :
    Disjoint (D.finiteArcInterior e) (D.finiteArcInterior f) := by
  apply D.disjoint_cutComponentImage
  intro hcomponent
  apply hef
  rw [← D.arcRepresentative_class e, ← D.arcRepresentative_class f]
  exact ConnectedComponents.coe_eq_coe.mpr hcomponent

/-- The quotient-indexed actual open arcs exhaust exactly the frontier away
from the finite cut set. -/
theorem iUnion_finiteArcInterior_eq_cutSpaceCarrier
    (D : FiniteChartCutSystem A) :
    (⋃ e : D.ArcIndex, D.finiteArcInterior e) =
      {q : FrontierSpace O | q ∉ D.cutPoints} := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨e, hqe⟩ := mem_iUnion.1 hq
    rcases hqe with ⟨x, _hx, rfl⟩
    exact x.2
  · intro q hq
    let x : D.CutSpace := ⟨q, hq⟩
    let e : D.ArcIndex := (x : ConnectedComponents D.CutSpace)
    have hclass :
        (D.arcRepresentative e : ConnectedComponents D.CutSpace) =
          (x : ConnectedComponents D.CutSpace) := by
      simpa only [e] using D.arcRepresentative_class e
    have hcomponent :
        connectedComponent (D.arcRepresentative e) =
          connectedComponent x :=
      ConnectedComponents.coe_eq_coe.mp hclass
    refine mem_iUnion.2 ⟨e, x, ?_, rfl⟩
    rw [hcomponent]
    exact mem_connectedComponent

/-- Removing the finite cut set leaves a dense subset of the actual frontier.
The needed absence of isolated points comes from the local interval atlas. -/
theorem dense_cutSpaceCarrier (D : FiniteChartCutSystem A) :
    Dense {q : FrontierSpace O | q ∉ D.cutPoints} := by
  letI (q : FrontierSpace O) : Filter.NeBot (𝓝[≠] q) :=
    A.frontier_punctured_nhds_neBot q
  have hDense :
      Dense ((Set.univ : Set (FrontierSpace O)) \ D.cutPoints) :=
    (dense_univ : Dense (Set.univ : Set (FrontierSpace O))).sdiff_finset
      D.cutPoints
  have hSet :
      ((Set.univ : Set (FrontierSpace O)) \ D.cutPoints) =
        {q : FrontierSpace O | q ∉ D.cutPoints} := by
    ext q
    simp
  rw [← hSet]
  exact hDense

/-- The compact closures of the finitely many quotient-indexed actual arcs
exhaust the complete frontier, including every cut point and every limit
point. -/
theorem iUnion_finiteArcClosure_eq_univ
    (D : FiniteChartCutSystem A) :
    (⋃ e : D.ArcIndex, D.finiteArcClosure e) = Set.univ := by
  letI : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  calc
    (⋃ e : D.ArcIndex, D.finiteArcClosure e) =
        closure (⋃ e : D.ArcIndex, D.finiteArcInterior e) := by
      rw [closure_iUnion_of_finite]
      rfl
    _ = closure {q : FrontierSpace O | q ∉ D.cutPoints} := by
      rw [D.iUnion_finiteArcInterior_eq_cutSpaceCarrier]
    _ = Set.univ := D.dense_cutSpaceCarrier.closure_eq

/-- A compactness-selected chart which contains the representative of one
quotient-indexed arc in its relative interior. -/
noncomputable def finiteArcChart
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) : D.centers :=
  Classical.choose (D.exists_arc_containing_connectedComponent
    (D.arcRepresentative e))

/-- The selected arc representative lies in the chosen chart core interior. -/
theorem arcRepresentative_mem_finiteArcChart_coreInterior
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    (D.arcRepresentative e).1 ∈ (D.arc (D.finiteArcChart e)).coreInterior := by
  have hCore :=
    Classical.choose_spec (D.exists_arc_containing_connectedComponent
      (D.arcRepresentative e))
      (D.arcRepresentative e) mem_connectedComponent
  have hLeft : (D.arcRepresentative e).1 ≠
      (D.arc (D.finiteArcChart e)).leftEndpoint := by
    intro h
    exact (D.arcRepresentative e).2
      (h ▸ D.leftEndpoint_mem_cutPoints (D.finiteArcChart e))
  have hRight : (D.arcRepresentative e).1 ≠
      (D.arc (D.finiteArcChart e)).rightEndpoint := by
    intro h
    exact (D.arcRepresentative e).2
      (h ▸ D.rightEndpoint_mem_cutPoints (D.finiteArcChart e))
  exact (D.arc (D.finiteArcChart e)).mem_coreInterior_of_mem_closedCore_of_ne_endpoints
    hCore hLeft hRight

/-- First actual endpoint of the selected embedded closure of an indexed arc. -/
noncomputable def finiteArcLeftEndpoint
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) : FrontierSpace O :=
  D.cutComponentLeftEndpoint (D.finiteArcChart e) (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)

/-- Second actual endpoint of the selected embedded closure of an indexed arc. -/
noncomputable def finiteArcRightEndpoint
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) : FrontierSpace O :=
  D.cutComponentRightEndpoint (D.finiteArcChart e) (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)

/-- The selected compact embedded closure is the intrinsic closure of the
quotient-indexed actual arc, so it is independent of the representative and
selected chart as a set. -/
theorem finiteArcClosure_eq_selectedClosedArc
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcClosure e =
      D.cutComponentClosedArc (D.finiteArcChart e)
        (D.arcRepresentative e) := by
  exact D.closure_cutComponentImage (D.finiteArcChart e)
    (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)

/-- Both endpoints of every quotient-indexed actual arc are global cut
points. -/
theorem finiteArc_endpoints_mem_cutPoints
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcLeftEndpoint e ∈ D.cutPoints ∧
      D.finiteArcRightEndpoint e ∈ D.cutPoints :=
  ⟨D.cutComponentLeftEndpoint_mem_cutPoints (D.finiteArcChart e)
      (D.arcRepresentative e)
      (D.arcRepresentative_mem_finiteArcChart_coreInterior e),
    D.cutComponentRightEndpoint_mem_cutPoints (D.finiteArcChart e)
      (D.arcRepresentative e)
      (D.arcRepresentative_mem_finiteArcChart_coreInterior e)⟩

/-- The two endpoints of every quotient-indexed actual arc are distinct. -/
theorem finiteArcLeftEndpoint_ne_rightEndpoint
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcLeftEndpoint e ≠ D.finiteArcRightEndpoint e :=
  D.cutComponentLeftEndpoint_ne_rightEndpoint (D.finiteArcChart e)
    (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)


/-- A cut component's compact closure adds exactly its two distinct cut
endpoints; there are no hidden frontier or cut points on the closed arc. -/
theorem cutComponentClosedArc_sdiff_cutComponentImage
    (D : FiniteChartCutSystem A) (i : D.centers) (x : D.CutSpace)
    (hx : x.1 ∈ (D.arc i).coreInterior) :
    D.cutComponentClosedArc i x \ D.cutComponentImage x =
      ({D.cutComponentLeftEndpoint i x hx,
        D.cutComponentRightEndpoint i x hx} :
        Set (FrontierSpace O)) := by
  ext q
  constructor
  · rintro ⟨hqClosed, hqOpen⟩
    rcases hqClosed with ⟨t, ht, rfl⟩
    have htInterval :
        (t : ℝ) ∈
          Icc (sInf (D.cutComponentRealParameterImage i x))
            (sSup (D.cutComponentRealParameterImage i x)) :=
      ht
    have htNotInterior :
        (t : ℝ) ∉
          Ioo (sInf (D.cutComponentRealParameterImage i x))
            (sSup (D.cutComponentRealParameterImage i x)) := by
      intro htInterior
      apply hqOpen
      rw [← D.image_corePoint_cutComponentOpenCoreParameterSet i x hx]
      refine ⟨t, ?_, rfl⟩
      change (t : ℝ) ∈ D.cutComponentRealParameterImage i x
      rw [D.cutComponentRealParameterImage_eq_Ioo i x hx]
      exact htInterior
    simp only [mem_insert_iff, mem_singleton_iff]
    rcases eq_or_lt_of_le htInterval.1 with htLeft | htLeft
    · left
      apply congrArg (D.arc i).corePoint
      apply Subtype.ext
      simpa only [cutComponentLeftCoreParameter] using htLeft.symm
    · right
      apply congrArg (D.arc i).corePoint
      apply Subtype.ext
      simp only [cutComponentRightCoreParameter]
      exact le_antisymm htInterval.2
        (le_of_not_gt fun htRight => htNotInterior ⟨htLeft, htRight⟩)
  · intro hq
    simp only [mem_insert_iff, mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · constructor
      · refine ⟨D.cutComponentLeftCoreParameter i x hx, ?_, rfl⟩
        change sInf (D.cutComponentRealParameterImage i x) ∈
          Icc (sInf (D.cutComponentRealParameterImage i x))
            (sSup (D.cutComponentRealParameterImage i x))
        exact ⟨le_rfl,
          (D.cutComponentRealParameter_sInf_lt_sSup i x hx).le⟩
      · intro hOpen
        rw [← D.image_corePoint_cutComponentOpenCoreParameterSet i x hx] at hOpen
        rcases hOpen with ⟨t, htOpen, htPoint⟩
        have htParameter :
            t = D.cutComponentLeftCoreParameter i x hx :=
          (D.arc i).injective_corePoint htPoint
        have htReal :
            (t : ℝ) =
              sInf (D.cutComponentRealParameterImage i x) :=
          congrArg Subtype.val htParameter
        change (t : ℝ) ∈ D.cutComponentRealParameterImage i x at htOpen
        rw [D.cutComponentRealParameterImage_eq_Ioo i x hx, htReal] at htOpen
        exact (lt_irrefl _ htOpen.1)
    · constructor
      · refine ⟨D.cutComponentRightCoreParameter i x hx, ?_, rfl⟩
        change sSup (D.cutComponentRealParameterImage i x) ∈
          Icc (sInf (D.cutComponentRealParameterImage i x))
            (sSup (D.cutComponentRealParameterImage i x))
        exact ⟨(D.cutComponentRealParameter_sInf_lt_sSup i x hx).le,
          le_rfl⟩
      · intro hOpen
        rw [← D.image_corePoint_cutComponentOpenCoreParameterSet i x hx] at hOpen
        rcases hOpen with ⟨t, htOpen, htPoint⟩
        have htParameter :
            t = D.cutComponentRightCoreParameter i x hx :=
          (D.arc i).injective_corePoint htPoint
        have htReal :
            (t : ℝ) =
              sSup (D.cutComponentRealParameterImage i x) :=
          congrArg Subtype.val htParameter
        change (t : ℝ) ∈ D.cutComponentRealParameterImage i x at htOpen
        rw [D.cutComponentRealParameterImage_eq_Ioo i x hx, htReal] at htOpen
        exact (lt_irrefl _ htOpen.2)

/-- Intrinsically, each quotient-indexed compact arc differs from its open
interior by exactly the two named distinct cut endpoints. -/
theorem finiteArcClosure_sdiff_finiteArcInterior
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcClosure e \ D.finiteArcInterior e =
      ({D.finiteArcLeftEndpoint e, D.finiteArcRightEndpoint e} :
        Set (FrontierSpace O)) := by
  rw [D.finiteArcClosure_eq_selectedClosedArc]
  exact D.cutComponentClosedArc_sdiff_cutComponentImage
    (D.finiteArcChart e) (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)

/-- Every point in an indexed arc interior survives the global endpoint cuts. -/
theorem finiteArcInterior_subset_cutSpaceCarrier
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcInterior e ⊆
      {q : FrontierSpace O | q ∉ D.cutPoints} := by
  intro q hq
  rcases hq with ⟨x, _hx, rfl⟩
  exact x.2

/-- Incidence of a cut point with an indexed compact arc is exactly equality
with one of that arc's two named endpoints. -/
theorem cutPoint_mem_finiteArcClosure_iff_endpoint
    (D : FiniteChartCutSystem A) {v : FrontierSpace O}
    (hv : v ∈ D.cutPoints) (e : D.ArcIndex) :
    v ∈ D.finiteArcClosure e ↔
      v = D.finiteArcLeftEndpoint e ∨
        v = D.finiteArcRightEndpoint e := by
  have hvInterior : v ∉ D.finiteArcInterior e := by
    intro hvOpen
    exact (D.finiteArcInterior_subset_cutSpaceCarrier e hvOpen) hv
  have hBoundary :=
    Set.ext_iff.mp (D.finiteArcClosure_sdiff_finiteArcInterior e) v
  constructor
  · intro hvClosure
    have hvBoundary :
        v ∈ D.finiteArcClosure e \ D.finiteArcInterior e :=
      ⟨hvClosure, hvInterior⟩
    simpa only [mem_insert_iff, mem_singleton_iff] using
      hBoundary.mp hvBoundary
  · intro hvEndpoint
    have hvBoundary :
        v ∈ D.finiteArcClosure e \ D.finiteArcInterior e :=
      hBoundary.mpr (by
        simpa only [mem_insert_iff, mem_singleton_iff] using hvEndpoint)
    exact hvBoundary.1

/-- The finite type of actual compact arcs incident to one global cut point. -/
abbrev IncidentArc
    (D : FiniteChartCutSystem A) (v : D.cutPoints) :=
  {e : D.ArcIndex // v.1 ∈ D.finiteArcClosure e}

/-- Every actual cut point is incident to at least one quotient-indexed compact
arc.  This follows from closure exhaustion, not from a supplied adjacency
list. -/
theorem incidentArc_nonempty
    (D : FiniteChartCutSystem A) (v : D.cutPoints) :
    Nonempty (D.IncidentArc v) := by
  have hvUnion : v.1 ∈ ⋃ e : D.ArcIndex, D.finiteArcClosure e := by
    rw [D.iUnion_finiteArcClosure_eq_univ]
    exact mem_univ v.1
  obtain ⟨e, he⟩ := mem_iUnion.1 hvUnion
  exact ⟨⟨e, he⟩⟩

/-- Every indexed compact arc stays inside the complete frontier component of
any point in its interior. -/
theorem finiteArcClosure_subset_connectedComponent
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcClosure e ⊆
      connectedComponent (D.arcRepresentative e).1 := by
  apply closure_minimal
  · rintro q ⟨x, hx, rfl⟩
    have hPath : x.1 ∈
        connectedComponent (D.arcRepresentative e).1 := by
      apply isConnected_connectedComponent.image Subtype.val
        continuous_subtype_val.continuousOn |>.subset_connectedComponent
      · exact ⟨D.arcRepresentative e, mem_connectedComponent, rfl⟩
      · exact ⟨x, hx, rfl⟩
    exact hPath
  · exact isClosed_connectedComponent

/-- The compact closure of every indexed arc is connected. -/
theorem isConnected_finiteArcClosure
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    IsConnected (D.finiteArcClosure e) := by
  exact (D.isConnected_cutComponentImage
    (D.arcRepresentative e)).closure


/-- The finite cut set is exactly the union of the endpoint pairs of the
derived quotient-indexed arcs.  Thus the compactness construction creates no
orphan cut vertex, and every arc endpoint is an actual selected cut point. -/
theorem iUnion_finiteArcEndpointPair_eq_cutPoints
    (D : FiniteChartCutSystem A) :
    (⋃ e : D.ArcIndex,
      ({D.finiteArcLeftEndpoint e, D.finiteArcRightEndpoint e} :
        Set (FrontierSpace O))) =
      (D.cutPoints : Set (FrontierSpace O)) := by
  apply Subset.antisymm
  · intro v hv
    obtain ⟨e, he⟩ := mem_iUnion.1 hv
    simp only [mem_insert_iff, mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact (D.finiteArc_endpoints_mem_cutPoints e).1
    · exact (D.finiteArc_endpoints_mem_cutPoints e).2
  · intro v hv
    let vCut : D.cutPoints := ⟨v, hv⟩
    obtain ⟨incident⟩ := D.incidentArc_nonempty vCut
    have hEndpoint :=
      (D.cutPoint_mem_finiteArcClosure_iff_endpoint hv incident.1).mp
        incident.2
    exact mem_iUnion.2 ⟨incident.1, by
      simpa only [mem_insert_iff, mem_singleton_iff] using hEndpoint⟩


/-- The finite subtype of quotient-indexed arcs lying in one complete actual
frontier component. -/
abbrev ComponentArc
    (D : FiniteChartCutSystem A) (p : FrontierSpace O) :=
  {e : D.ArcIndex //
    (D.arcRepresentative e).1 ∈ connectedComponent p}

/-- The compact closure of a component-indexed arc stays in that complete
actual frontier component. -/
theorem componentArcClosure_subset
    (D : FiniteChartCutSystem A) (p : FrontierSpace O)
    (e : D.ComponentArc p) :
    D.finiteArcClosure e.1 ⊆ connectedComponent p := by
  have hcomponents :
      connectedComponent (D.arcRepresentative e.1).1 =
        connectedComponent p :=
    (connectedComponent_eq e.2).symm
  simpa only [hcomponents] using
    D.finiteArcClosure_subset_connectedComponent e.1

/-- For each complete actual frontier component, the closures of exactly its
derived finite arcs exhaust that component.  No component edge list is
supplied. -/
theorem iUnion_componentArcClosure_eq_connectedComponent
    (D : FiniteChartCutSystem A) (p : FrontierSpace O) :
    (⋃ e : D.ComponentArc p, D.finiteArcClosure e.1) =
      connectedComponent p := by
  apply Subset.antisymm
  · exact iUnion_subset fun e => D.componentArcClosure_subset p e
  · intro q hq
    have hqAll : q ∈ ⋃ e : D.ArcIndex, D.finiteArcClosure e := by
      rw [D.iUnion_finiteArcClosure_eq_univ]
      exact mem_univ q
    obtain ⟨e, hqe⟩ := mem_iUnion.1 hqAll
    have hqRepresentative :=
      D.finiteArcClosure_subset_connectedComponent e hqe
    have hcomponents :
        connectedComponent (D.arcRepresentative e).1 =
          connectedComponent p := by
      exact (connectedComponent_eq hqRepresentative).trans
        (connectedComponent_eq hq).symm
    let ep : D.ComponentArc p :=
      ⟨e, by
        rw [← hcomponents]
        exact mem_connectedComponent⟩
    exact mem_iUnion.2 ⟨ep, hqe⟩

/-- Every endpoint of a component-indexed arc lies in the same complete
frontier component. -/
theorem componentArc_endpoints_mem_connectedComponent
    (D : FiniteChartCutSystem A) (p : FrontierSpace O)
    (e : D.ComponentArc p) :
    D.finiteArcLeftEndpoint e.1 ∈ connectedComponent p ∧
      D.finiteArcRightEndpoint e.1 ∈ connectedComponent p := by
  have hBoundary :=
    Set.ext_iff.mp (D.finiteArcClosure_sdiff_finiteArcInterior e.1)
  constructor
  · apply D.componentArcClosure_subset p e
    exact ((hBoundary (D.finiteArcLeftEndpoint e.1)).mpr
      (by simp)).1
  · apply D.componentArcClosure_subset p e
    exact ((hBoundary (D.finiteArcRightEndpoint e.1)).mpr
      (by simp)).1

end FiniteChartCutSystem

/-- Canonical choice of the finite chart-cut system supplied by boundedness and
the actual pointwise atlas. -/
noncomputable def finiteChartCutSystem
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O) :
    FiniteChartCutSystem A :=
  Classical.choice (A.exists_finiteChartCutSystem hObounded)

/-- Canonical finite chart cuts refined by a caller-derived finite set of actual
frontier junctions.  The chart cover is unchanged; only the complement whose
connected components define the final compact arcs is refined. -/
noncomputable def finiteChartCutSystemIncluding
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O)
    (junctions : Finset (FrontierSpace O)) :
    FiniteChartCutSystem A := by
  let D := A.finiteChartCutSystem hObounded
  exact {
    centers := D.centers
    covers := D.covers
    additionalCutPoints := junctions
  }

@[simp] theorem finiteChartCutSystemIncluding_additionalCutPoints
    (A : BoundaryHalfSpaceAtlas O) (hObounded : Bornology.IsBounded O)
    (junctions : Finset (FrontierSpace O)) :
    (A.finiteChartCutSystemIncluding hObounded junctions).additionalCutPoints =
      junctions := by
  rfl

end BoundaryHalfSpaceAtlas

end CMVBoundaryLocalAtlas
