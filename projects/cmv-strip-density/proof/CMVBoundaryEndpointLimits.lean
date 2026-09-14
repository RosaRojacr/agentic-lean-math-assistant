/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryHeightCompletion

/-!
# One-sided intrinsic endpoint limits

The pointwise half-space atlas regulates the intrinsic section endpoints
without imposing a global boundary parametrization.  At every occupied height,
both endpoints have finite limits from both sides; both inward limits also
exist at each extreme occupied height.  Two putative cluster values create a
horizontal frontier segment, while the local frontier interval chart excludes
transverse accumulation.  The resulting limits describe every interior and
extreme horizontal frontier slice exactly, including shelf-jump segments.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

open CMVRelaxation
open CMVSourceClassification

variable {E U : Set PlanePoint}

private theorem exists_frontier_horizontal_window
    {O : Set PlanePoint} (A₀ : BoundaryHalfSpaceAtlas O)
    {a x b y : ℝ} (hx : x ∈ Ioo a b)
    (hsegment : ∀ t ∈ Ioo a b, (t, y) ∈ frontier O) :
    ∃ W : Set PlanePoint, IsOpen W ∧ (x, y) ∈ W ∧
      frontier O ∩ W ⊆ Prod.snd ⁻¹' ({y} : Set ℝ) := by
  let p : {q : PlanePoint // q ∈ frontier O} := ⟨(x, y), hsegment x hx⟩
  let A := A₀.intervalAt p
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp A.isOpen_window (x, y) A.base_mem_window
  have hgapLeft : 0 < x - a := sub_pos.mpr hx.1
  have hgapRight : 0 < b - x := sub_pos.mpr hx.2
  have hminPos : 0 < min ε (min (x - a) (b - x)) :=
    lt_min hε (lt_min hgapLeft hgapRight)
  let δ := min ε (min (x - a) (b - x)) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hδε : δ < ε := by
    dsimp [δ]
    have hmin : min ε (min (x - a) (b - x)) ≤ ε := min_le_left _ _
    nlinarith
  have hδLeft : δ < x - a := by
    dsimp [δ]
    have hmin : min ε (min (x - a) (b - x)) ≤ x - a :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [hminPos]
  have hδRight : δ < b - x := by
    dsimp [δ]
    have hmin : min ε (min (x - a) (b - x)) ≤ b - x :=
      (min_le_right _ _).trans (min_le_right _ _)
    nlinarith [hminPos]
  let c := x - δ
  let d := x + δ
  have hcd : c ≤ d := by dsimp [c, d]; linarith
  have hcx : c < x := by dsimp [c]; linarith
  have hxd : x < d := by dsimp [d]; linarith
  have hIccIoo : Icc c d ⊆ Ioo a b := by
    intro t ht
    dsimp [c, d] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hhorizontalWindow : ∀ t ∈ Icc c d, (t, y) ∈ A.window := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · change |t - x| < ε
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    · simpa using hε
  let f : ℝ → ℝ := fun t => (A.ambient.coord (t, y)).1
  have hfContinuous : ContinuousOn f (Icc c d) := by
    apply continuous_fst.comp_continuousOn
    exact A.ambient.coord.continuousOn_toFun.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => (hhorizontalWindow t ht).1)
  have hfInjective : InjOn f (Icc c d) := by
    intro s hs t ht hst
    have hsSource := (hhorizontalWindow s hs).1
    have htSource := (hhorizontalWindow t ht).1
    have hsFrontier := hsegment s (hIccIoo hs)
    have htFrontier := hsegment t (hIccIoo ht)
    have hsAxis := (A.ambient.frontier_image.apply_mem_iff hsSource).2 hsFrontier
    have htAxis := (A.ambient.frontier_image.apply_mem_iff htSource).2 htFrontier
    have hcoords : A.ambient.coord (s, y) = A.ambient.coord (t, y) :=
      Prod.ext hst (hsAxis.2.trans htAxis.2.symm)
    exact congrArg Prod.fst
      (A.ambient.coord.injOn hsSource htSource hcoords)
  rcases hfContinuous.strictMonoOn_of_injOn_Icc' hcd hfInjective with
      hfMono | hfAnti
  · let J := Ioo (f c) (f d)
    refine ⟨A.ambient.coord.source ∩ A.ambient.coord ⁻¹' (Prod.fst ⁻¹' J),
      A.ambient.coord.isOpen_inter_preimage
        (isOpen_Ioo.preimage continuous_fst),
      ?_, ?_⟩
    · refine ⟨(hhorizontalWindow x ⟨hcx.le, hxd.le⟩).1, ?_⟩
      exact ⟨hfMono ⟨le_rfl, hcd⟩ ⟨hcx.le, hxd.le⟩ hcx,
        hfMono ⟨hcx.le, hxd.le⟩ ⟨hcd, le_rfl⟩ hxd⟩
    · rintro q ⟨hqFrontier, hqSource, hqJ⟩
      have hqAxis :=
        (A.ambient.frontier_image.apply_mem_iff hqSource).2 hqFrontier
      have hqRange : (A.ambient.coord q).1 ∈ f '' Icc c d := by
        rw [hfContinuous.image_Icc_of_monotoneOn hcd hfMono.monotoneOn]
        exact ⟨hqJ.1.le, hqJ.2.le⟩
      obtain ⟨t, ht, hft⟩ := hqRange
      have htSource := (hhorizontalWindow t ht).1
      have htFrontier := hsegment t (hIccIoo ht)
      have htAxis :=
        (A.ambient.frontier_image.apply_mem_iff htSource).2 htFrontier
      have hcoords : A.ambient.coord (t, y) = A.ambient.coord q :=
        Prod.ext hft (htAxis.2.trans hqAxis.2.symm)
      have heq := A.ambient.coord.injOn htSource hqSource hcoords
      simpa only [mem_preimage, mem_singleton_iff] using congrArg Prod.snd heq.symm
  · let J := Ioo (f d) (f c)
    refine ⟨A.ambient.coord.source ∩ A.ambient.coord ⁻¹' (Prod.fst ⁻¹' J),
      A.ambient.coord.isOpen_inter_preimage
        (isOpen_Ioo.preimage continuous_fst),
      ?_, ?_⟩
    · refine ⟨(hhorizontalWindow x ⟨hcx.le, hxd.le⟩).1, ?_⟩
      exact ⟨hfAnti ⟨hcx.le, hxd.le⟩ ⟨hcd, le_rfl⟩ hxd,
        hfAnti ⟨le_rfl, hcd⟩ ⟨hcx.le, hxd.le⟩ hcx⟩
    · rintro q ⟨hqFrontier, hqSource, hqJ⟩
      have hqAxis :=
        (A.ambient.frontier_image.apply_mem_iff hqSource).2 hqFrontier
      have hqRange : (A.ambient.coord q).1 ∈ f '' Icc c d := by
        rw [hfContinuous.image_Icc_of_antitoneOn hcd hfAnti.antitoneOn]
        exact ⟨hqJ.1.le, hqJ.2.le⟩
      obtain ⟨t, ht, hft⟩ := hqRange
      have htSource := (hhorizontalWindow t ht).1
      have htFrontier := hsegment t (hIccIoo ht)
      have htAxis :=
        (A.ambient.frontier_image.apply_mem_iff htSource).2 htFrontier
      have hcoords : A.ambient.coord (t, y) = A.ambient.coord q :=
        Prod.ext hft (htAxis.2.trans hqAxis.2.symm)
      have heq := A.ambient.coord.injOn htSource hqSource hcoords
      simpa only [mem_preimage, mem_singleton_iff] using congrArg Prod.snd heq.symm

private theorem exists_frontier_vertical_between
    {O : Set PlanePoint} (hO : IsOpen O) {x s t : ℝ}
    (hs : (x, s) ∈ O) (ht : (x, t) ∉ O) :
    ∃ z ∈ uIcc s t, (x, z) ∈ frontier O := by
  let φ : ℝ → PlanePoint := fun z => (x, z)
  let C : Set PlanePoint := φ '' uIcc s t
  have hC : IsPreconnected C :=
    isPreconnected_uIcc.image φ (continuous_const.prodMk continuous_id).continuousOn
  have hsC : (x, s) ∈ C := by
    exact ⟨s, left_mem_uIcc, rfl⟩
  have htC : (x, t) ∈ C := by
    exact ⟨t, right_mem_uIcc, rfl⟩
  by_contra h
  simp only [not_exists, not_and] at h
  have hclosure : closure O ∩ C ⊆ O := by
    rintro q ⟨hqClosure, hqC⟩
    rcases hqC with ⟨z, hz, rfl⟩
    by_contra hzO
    have hzFrontier : (x, z) ∈ frontier O := by
      rw [hO.frontier_eq]
      exact ⟨hqClosure, hzO⟩
    exact h z hz hzFrontier
  have hCO : C ⊆ O :=
    hC.subset_of_closure_inter_subset hO ⟨(x, s), hsC, hs⟩ hclosure
  exact ht (hCO htC)

private theorem mapClusterPt_mem_frontierSection_general
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ}
    {f : ℝ → ℝ} {a x : ℝ}
    (ha : Tendsto id l (𝓝 a))
    (hfrontier : ∀ᶠ y in l,
      (f y, y) ∈ frontier (aeOpenRepresentative E))
    (hx : MapClusterPt x l f) :
    x ∈ D.frontierSection a := by
  have hpair : MapClusterPt (x, a) l (fun y => (f y, y)) := by
    rw [mapClusterPt_iff_frequently] at hx ⊢
    intro s hs
    rcases mem_nhds_prod_iff.mp hs with ⟨u, hu, v, hv, huv⟩
    exact ((hx u hu).and_eventually (ha hv)).mono fun y hy =>
      huv ⟨hy.1, hy.2⟩
  exact isClosed_frontier.mem_of_mapClusterPt hpair hfrontier

private theorem mapClusterPt_leftEndpoint_le_general
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y x : ℝ}
    (hy : y ∈ D.occupiedHeights) (hl : Tendsto id l (𝓝 y))
    (hx : MapClusterPt x l D.leftEndpoint) :
    x ≤ D.leftEndpoint y := by
  by_contra hle
  have hlt : D.leftEndpoint y < x := lt_of_not_ge hle
  obtain ⟨t, hleft, htx⟩ := exists_between hlt
  have hevent : ∀ᶠ z in l, D.leftEndpoint z < t := by
    change {z | D.leftEndpoint z < t} ∈ l
    simpa only [map_id] using
      hl (D.upperSemicontinuousAt_leftEndpoint hy t hleft)
  have hfreq : ∃ᶠ z in l, t < D.leftEndpoint z :=
    hx.frequently (Ioi_mem_nhds htx)
  obtain ⟨z, htz, hzt⟩ := (hfreq.and_eventually hevent).exists
  exact (htz.trans hzt).false

private theorem Icc_leftEndpoint_subset_frontierSection_of_mapClusterPt
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y x : ℝ}
    (hy : y ∈ D.occupiedHeights) (hl : Tendsto id l (𝓝 y))
    (hoccupied : ∀ᶠ z in l, z ∈ D.occupiedHeights)
    (hx : MapClusterPt x l D.leftEndpoint) :
    Icc x (D.leftEndpoint y) ⊆ D.frontierSection y := by
  intro u hu
  rcases hu.1.eq_or_lt with rfl | hxu
  · apply mapClusterPt_mem_frontierSection_general D hl _ hx
    filter_upwards [hoccupied] with z hz
    exact D.leftEndpoint_mem_frontier hz
  · have huyRight : u < D.rightEndpoint y :=
      hu.2.trans_lt (D.leftEndpoint_lt_rightEndpoint hy)
    have hright : ∀ᶠ z in l, u < D.rightEndpoint z := by
      change {z | u < D.rightEndpoint z} ∈ l
      simpa only [map_id] using
        hl (D.lowerSemicontinuousAt_rightEndpoint hy u huyRight)
    have hleft : ∃ᶠ z in l, D.leftEndpoint z < u :=
      hx.frequently (Iio_mem_nhds hxu)
    have hcarrier : ∃ᶠ z in l, (u, z) ∈ aeOpenRepresentative E := by
      exact (hleft.and_eventually (hright.and hoccupied)).mono fun z hz => by
        rw [show (u, z) ∈ aeOpenRepresentative E ↔
            u ∈ horizontalSection (aeOpenRepresentative E) z by rfl,
          D.horizontalSection_eq_Ioo_endpoints hz.2.2]
        exact ⟨hz.1, hz.2.1⟩
    have hpair : Tendsto (fun z : ℝ => ((u, z) : PlanePoint))
        l (𝓝 (u, y)) := by
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.prodMk hl
    have hclosure : (u, y) ∈ closure (aeOpenRepresentative E) :=
      mem_closure_of_frequently_of_tendsto hcarrier hpair
    have hnot : (u, y) ∉ aeOpenRepresentative E := by
      intro huCarrier
      have huSection : u ∈ horizontalSection (aeOpenRepresentative E) y :=
        huCarrier
      rw [D.horizontalSection_eq_Ioo_endpoints hy] at huSection
      exact (not_lt_of_ge hu.2) huSection.1
    change (u, y) ∈ frontier (aeOpenRepresentative E)
    rw [D.produce.selected_open.frontier_eq]
    exact ⟨hclosure, hnot⟩

private theorem horizontal_frontier_forbids_oneSided_vertical_oscillation
    {O : Set PlanePoint} (hO : IsOpen O) (A : BoundaryHalfSpaceAtlas O)
    {l : Filter ℝ} {a x b y : ℝ}
    (hl : Tendsto id l (𝓝 y))
    (hside : (∀ᶠ z in l, z < y) ∨ (∀ᶠ z in l, y < z))
    (hx : x ∈ Ioo a b)
    (hsegment : ∀ t ∈ Ioo a b, (t, y) ∈ frontier O)
    (hin : ∃ᶠ z in l, (x, z) ∈ O)
    (hout : ∃ᶠ z in l, (x, z) ∉ O) :
    False := by
  obtain ⟨W, hWopen, hxyW, hfrontierW⟩ :=
    exists_frontier_horizontal_window A hx hsegment
  obtain ⟨ε, hε, hballW⟩ :=
    Metric.isOpen_iff.mp hWopen (x, y) hxyW
  have hnear : ∀ᶠ z in l, dist z y < ε := by
    change Metric.ball y ε ∈ l
    simpa only [map_id] using hl (Metric.ball_mem_nhds y hε)
  have hcontradiction :
      ∀ {s t : ℝ}, (x, s) ∈ O → (x, t) ∉ O →
        dist s y < ε → dist t y < ε →
        ((s < y ∧ t < y) ∨ (y < s ∧ y < t)) → False := by
    intro s t hsCarrier htNotCarrier hsNear htNear hstrictSide
    obtain ⟨z, hzIcc, hzFrontier⟩ :=
      exists_frontier_vertical_between hO hsCarrier htNotCarrier
    have hsBounds : y - ε < s ∧ s < y + ε := by
      rw [Real.dist_eq, abs_lt] at hsNear
      constructor <;> linarith
    have htBounds : y - ε < t ∧ t < y + ε := by
      rw [Real.dist_eq, abs_lt] at htNear
      constructor <;> linarith
    have hzBounds : y - ε < z ∧ z < y + ε := by
      rcases le_total s t with hst | hts
      · rw [uIcc_of_le hst] at hzIcc
        exact ⟨hsBounds.1.trans_le hzIcc.1,
          hzIcc.2.trans_lt htBounds.2⟩
      · rw [uIcc_comm, uIcc_of_le hts] at hzIcc
        exact ⟨htBounds.1.trans_le hzIcc.1,
          hzIcc.2.trans_lt hsBounds.2⟩
    have hxzW : (x, z) ∈ W := by
      apply hballW
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · simpa using hε
      · rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hzBounds.1], by linarith [hzBounds.2]⟩
    have hzy : z = y :=
      hfrontierW ⟨hzFrontier, hxzW⟩
    rcases hstrictSide with ⟨hsy, hty⟩ | ⟨hys, hyt⟩
    · have hzBelow : z < y := by
        rcases le_total s t with hst | hts
        · rw [uIcc_of_le hst] at hzIcc
          exact hzIcc.2.trans_lt hty
        · rw [uIcc_comm, uIcc_of_le hts] at hzIcc
          exact hzIcc.2.trans_lt hsy
      exact hzy.not_lt hzBelow
    · have hzAbove : y < z := by
        rcases le_total s t with hst | hts
        · rw [uIcc_of_le hst] at hzIcc
          exact hys.trans_le hzIcc.1
        · rw [uIcc_comm, uIcc_of_le hts] at hzIcc
          exact hyt.trans_le hzIcc.1
      exact hzy.symm.not_lt hzAbove
  rcases hside with hbelow | habove
  · obtain ⟨s, hsCarrier, hsNear, hsy⟩ :=
      (hin.and_eventually (hnear.and hbelow)).exists
    obtain ⟨t, htNotCarrier, htNear, hty⟩ :=
      (hout.and_eventually (hnear.and hbelow)).exists
    exact hcontradiction hsCarrier htNotCarrier hsNear htNear
      (Or.inl ⟨hsy, hty⟩)
  · obtain ⟨s, hsCarrier, hsNear, hys⟩ :=
      (hin.and_eventually (hnear.and habove)).exists
    obtain ⟨t, htNotCarrier, htNear, hyt⟩ :=
      (hout.and_eventually (hnear.and habove)).exists
    exact hcontradiction hsCarrier htNotCarrier hsNear htNear
      (Or.inr ⟨hys, hyt⟩)

private theorem mapClusterPt_leftEndpoint_not_lt_of_oneSided
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y a b : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hl : Tendsto id l (𝓝 y))
    (hoccupied : ∀ᶠ z in l, z ∈ D.occupiedHeights)
    (hside : (∀ᶠ z in l, z < y) ∨ (∀ᶠ z in l, y < z))
    (ha : MapClusterPt a l D.leftEndpoint)
    (hb : MapClusterPt b l D.leftEndpoint)
    (hab : a < b) :
    False := by
  have hbLe := mapClusterPt_leftEndpoint_le_general D hy hl hb
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have hsegment : ∀ t ∈ Ioo a b,
      (t, y) ∈ frontier (aeOpenRepresentative E) := by
    intro t ht
    exact Icc_leftEndpoint_subset_frontierSection_of_mapClusterPt
      D hy hl hoccupied ha ⟨ht.1.le, ht.2.le.trans hbLe⟩
  have hright : ∀ᶠ z in l, x < D.rightEndpoint z := by
    change {z | x < D.rightEndpoint z} ∈ l
    simpa only [map_id] using hl
      (D.lowerSemicontinuousAt_rightEndpoint hy x
        ((hxb.trans_le hbLe).trans (D.leftEndpoint_lt_rightEndpoint hy)))
  have hinLeft : ∃ᶠ z in l, D.leftEndpoint z < x :=
    ha.frequently (Iio_mem_nhds hax)
  have houtLeft : ∃ᶠ z in l, x < D.leftEndpoint z :=
    hb.frequently (Ioi_mem_nhds hxb)
  have hin : ∃ᶠ z in l, (x, z) ∈ aeOpenRepresentative E := by
    exact (hinLeft.and_eventually (hright.and hoccupied)).mono fun z hz => by
      rw [show (x, z) ∈ aeOpenRepresentative E ↔
          x ∈ horizontalSection (aeOpenRepresentative E) z by rfl,
        D.horizontalSection_eq_Ioo_endpoints hz.2.2]
      exact ⟨hz.1, hz.2.1⟩
  have hout : ∃ᶠ z in l, (x, z) ∉ aeOpenRepresentative E := by
    exact (houtLeft.and_eventually hoccupied).mono fun z hz => by
      intro hzCarrier
      have hxSection : x ∈ horizontalSection (aeOpenRepresentative E) z :=
        hzCarrier
      rw [D.horizontalSection_eq_Ioo_endpoints hz.2] at hxSection
      exact (not_lt_of_ge hz.1.le) hxSection.1
  exact horizontal_frontier_forbids_oneSided_vertical_oscillation
    D.produce.selected_open D.local_atlas hl hside ⟨hax, hxb⟩
      hsegment hin hout

private theorem mapClusterPt_leftEndpoint_unique_of_oneSided
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y a b : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hl : Tendsto id l (𝓝 y))
    (hoccupied : ∀ᶠ z in l, z ∈ D.occupiedHeights)
    (hside : (∀ᶠ z in l, z < y) ∨ (∀ᶠ z in l, y < z))
    (ha : MapClusterPt a l D.leftEndpoint)
    (hb : MapClusterPt b l D.leftEndpoint) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (mapClusterPt_leftEndpoint_not_lt_of_oneSided
      D hy hl hoccupied hside ha hb hab).elim
  · exact hab
  · exact (mapClusterPt_leftEndpoint_not_lt_of_oneSided
      D hy hl hoccupied hside hb ha hba).elim

private theorem isCompact_endpointRange
    (D : SelectedBoundaryTopologyInput E U) :
    IsCompact (Prod.fst '' closure (aeOpenRepresentative E)) :=
  D.produce.selected_bounded.isCompact_closure.image continuous_fst

private theorem eventually_leftEndpoint_mem_endpointRange
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ}
    (hoccupied : ∀ᶠ y in l, y ∈ D.occupiedHeights) :
    ∀ᶠ y in l,
      D.leftEndpoint y ∈ Prod.fst '' closure (aeOpenRepresentative E) := by
  filter_upwards [hoccupied] with y hy
  exact ⟨(D.leftEndpoint y, y),
    frontier_subset_closure (D.leftEndpoint_mem_frontier hy), rfl⟩

/-- The left section endpoint has a finite limit from below at every occupied
height. -/
theorem exists_leftEndpoint_limit_nhdsLT
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    ∃ L : ℝ, Tendsto D.leftEndpoint (𝓝[<] y) (𝓝 L) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hl : Tendsto id (𝓝[<] y) (𝓝 y) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hoccupied : ∀ᶠ z in 𝓝[<] y, z ∈ D.occupiedHeights :=
    (D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ z in 𝓝[<] y, D.leftEndpoint z ∈ K :=
    D.eventually_leftEndpoint_mem_endpointRange hoccupied
  obtain ⟨L, hLK, hL⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨L, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact mapClusterPt_leftEndpoint_unique_of_oneSided
    D hy hl hoccupied (Or.inl self_mem_nhdsWithin) hx hL

/-- The left section endpoint has a finite limit from above at every occupied
height. -/
theorem exists_leftEndpoint_limit_nhdsGT
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    ∃ L : ℝ, Tendsto D.leftEndpoint (𝓝[>] y) (𝓝 L) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hl : Tendsto id (𝓝[>] y) (𝓝 y) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hoccupied : ∀ᶠ z in 𝓝[>] y, z ∈ D.occupiedHeights :=
    (D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ z in 𝓝[>] y, D.leftEndpoint z ∈ K :=
    D.eventually_leftEndpoint_mem_endpointRange hoccupied
  obtain ⟨L, hLK, hL⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨L, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact mapClusterPt_leftEndpoint_unique_of_oneSided
    D hy hl hoccupied (Or.inr self_mem_nhdsWithin) hx hL

private theorem mapClusterPt_rightEndpoint_ge_general
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y x : ℝ}
    (hy : y ∈ D.occupiedHeights) (hl : Tendsto id l (𝓝 y))
    (hx : MapClusterPt x l D.rightEndpoint) :
    D.rightEndpoint y ≤ x := by
  by_contra hle
  have hlt : x < D.rightEndpoint y := lt_of_not_ge hle
  obtain ⟨t, hxt, hright⟩ := exists_between hlt
  have hevent : ∀ᶠ z in l, t < D.rightEndpoint z := by
    change {z | t < D.rightEndpoint z} ∈ l
    simpa only [map_id] using
      hl (D.lowerSemicontinuousAt_rightEndpoint hy t hright)
  have hfreq : ∃ᶠ z in l, D.rightEndpoint z < t :=
    hx.frequently (Iio_mem_nhds hxt)
  obtain ⟨z, hzt, htz⟩ := (hfreq.and_eventually hevent).exists
  exact (hzt.trans htz).false

private theorem Icc_rightEndpoint_subset_frontierSection_of_mapClusterPt
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y x : ℝ}
    (hy : y ∈ D.occupiedHeights) (hl : Tendsto id l (𝓝 y))
    (hoccupied : ∀ᶠ z in l, z ∈ D.occupiedHeights)
    (hx : MapClusterPt x l D.rightEndpoint) :
    Icc (D.rightEndpoint y) x ⊆ D.frontierSection y := by
  intro u hu
  rcases hu.2.eq_or_lt with rfl | hux
  · apply mapClusterPt_mem_frontierSection_general D hl _ hx
    filter_upwards [hoccupied] with z hz
    exact D.rightEndpoint_mem_frontier hz
  · have hleftU : D.leftEndpoint y < u :=
      (D.leftEndpoint_lt_rightEndpoint hy).trans_le hu.1
    have hleft : ∀ᶠ z in l, D.leftEndpoint z < u := by
      change {z | D.leftEndpoint z < u} ∈ l
      simpa only [map_id] using
        hl (D.upperSemicontinuousAt_leftEndpoint hy u hleftU)
    have hright : ∃ᶠ z in l, u < D.rightEndpoint z :=
      hx.frequently (Ioi_mem_nhds hux)
    have hcarrier : ∃ᶠ z in l, (u, z) ∈ aeOpenRepresentative E := by
      exact (hright.and_eventually (hleft.and hoccupied)).mono fun z hz => by
        rw [show (u, z) ∈ aeOpenRepresentative E ↔
            u ∈ horizontalSection (aeOpenRepresentative E) z by rfl,
          D.horizontalSection_eq_Ioo_endpoints hz.2.2]
        exact ⟨hz.2.1, hz.1⟩
    have hpair : Tendsto (fun z : ℝ => ((u, z) : PlanePoint))
        l (𝓝 (u, y)) := by
      rw [nhds_prod_eq]
      exact tendsto_const_nhds.prodMk hl
    have hclosure : (u, y) ∈ closure (aeOpenRepresentative E) :=
      mem_closure_of_frequently_of_tendsto hcarrier hpair
    have hnot : (u, y) ∉ aeOpenRepresentative E := by
      intro huCarrier
      have huSection : u ∈ horizontalSection (aeOpenRepresentative E) y :=
        huCarrier
      rw [D.horizontalSection_eq_Ioo_endpoints hy] at huSection
      exact (not_lt_of_ge hu.1) huSection.2
    change (u, y) ∈ frontier (aeOpenRepresentative E)
    rw [D.produce.selected_open.frontier_eq]
    exact ⟨hclosure, hnot⟩


private theorem mapClusterPt_rightEndpoint_not_lt_of_oneSided
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y a b : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hl : Tendsto id l (𝓝 y))
    (hoccupied : ∀ᶠ z in l, z ∈ D.occupiedHeights)
    (hside : (∀ᶠ z in l, z < y) ∨ (∀ᶠ z in l, y < z))
    (ha : MapClusterPt a l D.rightEndpoint)
    (hb : MapClusterPt b l D.rightEndpoint)
    (hab : a < b) :
    False := by
  have haGe := mapClusterPt_rightEndpoint_ge_general D hy hl ha
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have hsegment : ∀ t ∈ Ioo a b,
      (t, y) ∈ frontier (aeOpenRepresentative E) := by
    intro t ht
    exact Icc_rightEndpoint_subset_frontierSection_of_mapClusterPt
      D hy hl hoccupied hb ⟨haGe.trans ht.1.le, ht.2.le⟩
  have hleft : ∀ᶠ z in l, D.leftEndpoint z < x := by
    change {z | D.leftEndpoint z < x} ∈ l
    simpa only [map_id] using hl
      (D.upperSemicontinuousAt_leftEndpoint hy x
        ((D.leftEndpoint_lt_rightEndpoint hy).trans_le
          (haGe.trans hax.le)))
  have hinRight : ∃ᶠ z in l, x < D.rightEndpoint z :=
    hb.frequently (Ioi_mem_nhds hxb)
  have houtRight : ∃ᶠ z in l, D.rightEndpoint z < x :=
    ha.frequently (Iio_mem_nhds hax)
  have hin : ∃ᶠ z in l, (x, z) ∈ aeOpenRepresentative E := by
    exact (hinRight.and_eventually (hleft.and hoccupied)).mono fun z hz => by
      rw [show (x, z) ∈ aeOpenRepresentative E ↔
          x ∈ horizontalSection (aeOpenRepresentative E) z by rfl,
        D.horizontalSection_eq_Ioo_endpoints hz.2.2]
      exact ⟨hz.2.1, hz.1⟩
  have hout : ∃ᶠ z in l, (x, z) ∉ aeOpenRepresentative E := by
    exact (houtRight.and_eventually hoccupied).mono fun z hz => by
      intro hzCarrier
      have hxSection : x ∈ horizontalSection (aeOpenRepresentative E) z :=
        hzCarrier
      rw [D.horizontalSection_eq_Ioo_endpoints hz.2] at hxSection
      exact (not_lt_of_ge hz.1.le) hxSection.2
  exact horizontal_frontier_forbids_oneSided_vertical_oscillation
    D.produce.selected_open D.local_atlas hl hside ⟨hax, hxb⟩
      hsegment hin hout

private theorem mapClusterPt_rightEndpoint_unique_of_oneSided
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ} {y a b : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hl : Tendsto id l (𝓝 y))
    (hoccupied : ∀ᶠ z in l, z ∈ D.occupiedHeights)
    (hside : (∀ᶠ z in l, z < y) ∨ (∀ᶠ z in l, y < z))
    (ha : MapClusterPt a l D.rightEndpoint)
    (hb : MapClusterPt b l D.rightEndpoint) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (mapClusterPt_rightEndpoint_not_lt_of_oneSided
      D hy hl hoccupied hside ha hb hab).elim
  · exact hab
  · exact (mapClusterPt_rightEndpoint_not_lt_of_oneSided
      D hy hl hoccupied hside hb ha hba).elim

private theorem eventually_rightEndpoint_mem_endpointRange
    (D : SelectedBoundaryTopologyInput E U) {l : Filter ℝ}
    (hoccupied : ∀ᶠ y in l, y ∈ D.occupiedHeights) :
    ∀ᶠ y in l,
      D.rightEndpoint y ∈ Prod.fst '' closure (aeOpenRepresentative E) := by
  filter_upwards [hoccupied] with y hy
  exact ⟨(D.rightEndpoint y, y),
    frontier_subset_closure (D.rightEndpoint_mem_frontier hy), rfl⟩

/-- The right section endpoint has a finite limit from below at every occupied
height. -/
theorem exists_rightEndpoint_limit_nhdsLT
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    ∃ R : ℝ, Tendsto D.rightEndpoint (𝓝[<] y) (𝓝 R) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hl : Tendsto id (𝓝[<] y) (𝓝 y) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hoccupied : ∀ᶠ z in 𝓝[<] y, z ∈ D.occupiedHeights :=
    (D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ z in 𝓝[<] y, D.rightEndpoint z ∈ K :=
    D.eventually_rightEndpoint_mem_endpointRange hoccupied
  obtain ⟨R, hRK, hR⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨R, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact mapClusterPt_rightEndpoint_unique_of_oneSided
    D hy hl hoccupied (Or.inl self_mem_nhdsWithin) hx hR

/-- The right section endpoint has a finite limit from above at every occupied
height. -/
theorem exists_rightEndpoint_limit_nhdsGT
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    ∃ R : ℝ, Tendsto D.rightEndpoint (𝓝[>] y) (𝓝 R) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hl : Tendsto id (𝓝[>] y) (𝓝 y) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hoccupied : ∀ᶠ z in 𝓝[>] y, z ∈ D.occupiedHeights :=
    (D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds
  have hmem : ∀ᶠ z in 𝓝[>] y, D.rightEndpoint z ∈ K :=
    D.eventually_rightEndpoint_mem_endpointRange hoccupied
  obtain ⟨R, hRK, hR⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨R, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact mapClusterPt_rightEndpoint_unique_of_oneSided
    D hy hl hoccupied (Or.inr self_mem_nhdsWithin) hx hR

/-- Canonical form of the left endpoint's limit from below. -/
theorem tendsto_leftEndpoint_nhdsLT_leftLim
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Tendsto D.leftEndpoint (𝓝[<] y)
      (𝓝 (Function.leftLim D.leftEndpoint y)) :=
  tendsto_leftLim_of_tendsto (D.exists_leftEndpoint_limit_nhdsLT hy)

/-- Canonical form of the left endpoint's limit from above. -/
theorem tendsto_leftEndpoint_nhdsGT_rightLim
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Tendsto D.leftEndpoint (𝓝[>] y)
      (𝓝 (Function.rightLim D.leftEndpoint y)) :=
  tendsto_rightLim_of_tendsto (D.exists_leftEndpoint_limit_nhdsGT hy)

/-- Canonical form of the right endpoint's limit from below. -/
theorem tendsto_rightEndpoint_nhdsLT_leftLim
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Tendsto D.rightEndpoint (𝓝[<] y)
      (𝓝 (Function.leftLim D.rightEndpoint y)) :=
  tendsto_leftLim_of_tendsto (D.exists_rightEndpoint_limit_nhdsLT hy)

/-- Canonical form of the right endpoint's limit from above. -/
theorem tendsto_rightEndpoint_nhdsGT_rightLim
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Tendsto D.rightEndpoint (𝓝[>] y)
      (𝓝 (Function.rightLim D.rightEndpoint y)) :=
  tendsto_rightLim_of_tendsto (D.exists_rightEndpoint_limit_nhdsGT hy)

/-- A downward left-endpoint jump fills the complete intervening horizontal
frontier segment. -/
theorem Icc_leftLim_leftEndpoint_subset_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Icc (Function.leftLim D.leftEndpoint y) (D.leftEndpoint y) ⊆
      D.frontierSection y := by
  apply Icc_leftEndpoint_subset_frontierSection_of_mapClusterPt D hy
    (tendsto_id.mono_left nhdsWithin_le_nhds)
    ((D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds)
  exact (D.tendsto_leftEndpoint_nhdsLT_leftLim hy).mapClusterPt

/-- An upward left-endpoint jump fills the complete intervening horizontal
frontier segment. -/
theorem Icc_rightLim_leftEndpoint_subset_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Icc (Function.rightLim D.leftEndpoint y) (D.leftEndpoint y) ⊆
      D.frontierSection y := by
  apply Icc_leftEndpoint_subset_frontierSection_of_mapClusterPt D hy
    (tendsto_id.mono_left nhdsWithin_le_nhds)
    ((D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds)
  exact (D.tendsto_leftEndpoint_nhdsGT_rightLim hy).mapClusterPt

/-- A downward right-endpoint jump fills the complete intervening horizontal
frontier segment. -/
theorem Icc_rightEndpoint_leftLim_subset_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Icc (D.rightEndpoint y) (Function.leftLim D.rightEndpoint y) ⊆
      D.frontierSection y := by
  apply Icc_rightEndpoint_subset_frontierSection_of_mapClusterPt D hy
    (tendsto_id.mono_left nhdsWithin_le_nhds)
    ((D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds)
  exact (D.tendsto_rightEndpoint_nhdsLT_leftLim hy).mapClusterPt

/-- An upward right-endpoint jump fills the complete intervening horizontal
frontier segment. -/
theorem Icc_rightEndpoint_rightLim_subset_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Icc (D.rightEndpoint y) (Function.rightLim D.rightEndpoint y) ⊆
      D.frontierSection y := by
  apply Icc_rightEndpoint_subset_frontierSection_of_mapClusterPt D hy
    (tendsto_id.mono_left nhdsWithin_le_nhds)
    ((D.eventually_mem_occupiedHeights hy).filter_mono nhdsWithin_le_nhds)
  exact (D.tendsto_rightEndpoint_nhdsGT_rightLim hy).mapClusterPt


private theorem eventually_occupied_nhdsGT_lowerHeight
    (D : SelectedBoundaryTopologyInput E U) :
    ∀ᶠ y in 𝓝[>] D.lowerHeight, y ∈ D.occupiedHeights := by
  have hupper : ∀ᶠ y in 𝓝[>] D.lowerHeight, y < D.upperHeight :=
    (eventually_lt_nhds D.lowerHeight_lt_upperHeight).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hupper] with y hyLower hyUpper
  exact D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hyLower, hyUpper⟩

private theorem frequently_fixed_abscissa_lower_of_leftEndpoint_clusters
    (D : SelectedBoundaryTopologyInput E U) {a x b : ℝ}
    (ha : MapClusterPt a (𝓝[>] D.lowerHeight) D.leftEndpoint)
    (hb : MapClusterPt b (𝓝[>] D.lowerHeight) D.leftEndpoint)
    (hax : a < x) (hxb : x < b) :
    ∃ᶠ y in 𝓝[>] D.lowerHeight,
      (x, y) ∈ aeOpenRepresentative E := by
  rw [(nhdsGT_basis D.lowerHeight).frequently_iff]
  intro c hc
  let m := (D.lowerHeight + D.upperHeight) / 2
  let d := min c m
  have hLowerM : D.lowerHeight < m := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hMUpper : m < D.upperHeight := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hLowerD : D.lowerHeight < d := lt_min hc hLowerM
  have hDUpper : d < D.upperHeight := (min_le_right c m).trans_lt hMUpper
  have hdOccupied : d ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hLowerD, hDUpper⟩
  have hband : Ioo D.lowerHeight d ∈ 𝓝[>] D.lowerHeight :=
    Ioo_mem_nhdsGT hLowerD
  obtain ⟨ya, hleftA, hyaBand⟩ :=
    ((ha.frequently (Iio_mem_nhds hax)).and_eventually hband).exists
  obtain ⟨yb, hleftB, hybBand⟩ :=
    ((hb.frequently (Ioi_mem_nhds hxb)).and_eventually hband).exists
  have hyaOccupied : ya ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hyaBand.1, hyaBand.2.trans hDUpper⟩
  have hybOccupied : yb ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hybBand.1, hybBand.2.trans hDUpper⟩
  obtain ⟨xa, hleftXa, hxaMin⟩ :=
    exists_between (lt_min hleftA (D.leftEndpoint_lt_rightEndpoint hyaOccupied))
  have hxaX : xa < x := hxaMin.trans_le (min_le_left _ _)
  have hxaRight : xa < D.rightEndpoint ya :=
    hxaMin.trans_le (min_le_right _ _)
  obtain ⟨xb, hleftXb, hxbRight⟩ :=
    exists_between (D.leftEndpoint_lt_rightEndpoint hybOccupied)
  have hxXb : x < xb := hleftB.trans hleftXb
  have hxaBand : (xa, ya) ∈ D.lowerBand d := by
    constructor
    · change xa ∈ horizontalSection (aeOpenRepresentative E) ya
      rw [D.horizontalSection_eq_Ioo_endpoints hyaOccupied]
      exact ⟨hleftXa, hxaRight⟩
    · exact hyaBand
  have hxbBand : (xb, yb) ∈ D.lowerBand d := by
    constructor
    · change xb ∈ horizontalSection (aeOpenRepresentative E) yb
      rw [D.horizontalSection_eq_Ioo_endpoints hybOccupied]
      exact ⟨hleftXb, hxbRight⟩
    · exact hybBand
  have hprojection :
      IsConnected (Prod.fst '' D.lowerBand d) :=
    (D.isConnected_lowerBand hdOccupied).image Prod.fst
      continuous_fst.continuousOn
  have hxaProjection : xa ∈ Prod.fst '' D.lowerBand d :=
    ⟨(xa, ya), hxaBand, rfl⟩
  have hxbProjection : xb ∈ Prod.fst '' D.lowerBand d :=
    ⟨(xb, yb), hxbBand, rfl⟩
  obtain ⟨p, hpBand, hpX⟩ :=
    hprojection.Icc_subset hxaProjection hxbProjection
      ⟨hxaX.le, hxXb.le⟩
  refine ⟨p.2, ⟨hpBand.2.1, hpBand.2.2.trans_le (min_le_left c m)⟩, ?_⟩
  rw [← hpX]
  exact hpBand.1

private theorem frequently_fixed_abscissa_lower_of_rightEndpoint_clusters
    (D : SelectedBoundaryTopologyInput E U) {a x b : ℝ}
    (ha : MapClusterPt a (𝓝[>] D.lowerHeight) D.rightEndpoint)
    (hb : MapClusterPt b (𝓝[>] D.lowerHeight) D.rightEndpoint)
    (hax : a < x) (hxb : x < b) :
    ∃ᶠ y in 𝓝[>] D.lowerHeight,
      (x, y) ∈ aeOpenRepresentative E := by
  rw [(nhdsGT_basis D.lowerHeight).frequently_iff]
  intro c hc
  let m := (D.lowerHeight + D.upperHeight) / 2
  let d := min c m
  have hLowerM : D.lowerHeight < m := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hMUpper : m < D.upperHeight := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hLowerD : D.lowerHeight < d := lt_min hc hLowerM
  have hDUpper : d < D.upperHeight := (min_le_right c m).trans_lt hMUpper
  have hdOccupied : d ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hLowerD, hDUpper⟩
  have hband : Ioo D.lowerHeight d ∈ 𝓝[>] D.lowerHeight :=
    Ioo_mem_nhdsGT hLowerD
  obtain ⟨ya, hrightA, hyaBand⟩ :=
    ((ha.frequently (Iio_mem_nhds hax)).and_eventually hband).exists
  obtain ⟨yb, hrightB, hybBand⟩ :=
    ((hb.frequently (Ioi_mem_nhds hxb)).and_eventually hband).exists
  have hyaOccupied : ya ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hyaBand.1, hyaBand.2.trans hDUpper⟩
  have hybOccupied : yb ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hybBand.1, hybBand.2.trans hDUpper⟩
  obtain ⟨xa, hleftXa, hxaRight⟩ :=
    exists_between (D.leftEndpoint_lt_rightEndpoint hyaOccupied)
  have hxaX : xa < x := hxaRight.trans hrightA
  have hmaxRight :
      max x (D.leftEndpoint yb) < D.rightEndpoint yb := by
    rw [max_lt_iff]
    exact ⟨hrightB, D.leftEndpoint_lt_rightEndpoint hybOccupied⟩
  obtain ⟨xb, hmaxXb, hxbRight⟩ := exists_between hmaxRight
  have hxXb : x < xb := (le_max_left _ _).trans_lt hmaxXb
  have hleftXb : D.leftEndpoint yb < xb :=
    (le_max_right _ _).trans_lt hmaxXb
  have hxaBand : (xa, ya) ∈ D.lowerBand d := by
    constructor
    · change xa ∈ horizontalSection (aeOpenRepresentative E) ya
      rw [D.horizontalSection_eq_Ioo_endpoints hyaOccupied]
      exact ⟨hleftXa, hxaRight⟩
    · exact hyaBand
  have hxbBand : (xb, yb) ∈ D.lowerBand d := by
    constructor
    · change xb ∈ horizontalSection (aeOpenRepresentative E) yb
      rw [D.horizontalSection_eq_Ioo_endpoints hybOccupied]
      exact ⟨hleftXb, hxbRight⟩
    · exact hybBand
  have hprojection :
      IsConnected (Prod.fst '' D.lowerBand d) :=
    (D.isConnected_lowerBand hdOccupied).image Prod.fst
      continuous_fst.continuousOn
  have hxaProjection : xa ∈ Prod.fst '' D.lowerBand d :=
    ⟨(xa, ya), hxaBand, rfl⟩
  have hxbProjection : xb ∈ Prod.fst '' D.lowerBand d :=
    ⟨(xb, yb), hxbBand, rfl⟩
  obtain ⟨p, hpBand, hpX⟩ :=
    hprojection.Icc_subset hxaProjection hxbProjection
      ⟨hxaX.le, hxXb.le⟩
  refine ⟨p.2, ⟨hpBand.2.1, hpBand.2.2.trans_le (min_le_left c m)⟩, ?_⟩
  rw [← hpX]
  exact hpBand.1
private theorem mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : MapClusterPt x (𝓝[>] D.lowerHeight) D.leftEndpoint) :
    x ∈ D.frontierSection D.lowerHeight := by
  apply mapClusterPt_mem_frontierSection_general D
    (tendsto_id.mono_left nhdsWithin_le_nhds) _ hx
  filter_upwards [D.eventually_occupied_nhdsGT_lowerHeight] with y hy
  exact D.leftEndpoint_mem_frontier hy

private theorem mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_not_lt
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[>] D.lowerHeight) D.leftEndpoint)
    (hb : MapClusterPt b (𝓝[>] D.lowerHeight) D.leftEndpoint)
    (hab : a < b) :
    False := by
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have haFrontier :=
    D.mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_mem_frontierSection ha
  have hbFrontier :=
    D.mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_mem_frontierSection hb
  have hsegment : ∀ t ∈ Ioo a b,
      (t, D.lowerHeight) ∈ frontier (aeOpenRepresentative E) := by
    intro t ht
    exact D.isConnected_lower_frontierSection.Icc_subset
      haFrontier hbFrontier ⟨ht.1.le, ht.2.le⟩
  have hin : ∃ᶠ y in 𝓝[>] D.lowerHeight,
      (x, y) ∈ aeOpenRepresentative E :=
    D.frequently_fixed_abscissa_lower_of_leftEndpoint_clusters
      ha hb hax hxb
  have houtLeft : ∃ᶠ y in 𝓝[>] D.lowerHeight, x < D.leftEndpoint y :=
    hb.frequently (Ioi_mem_nhds hxb)
  have hout : ∃ᶠ y in 𝓝[>] D.lowerHeight,
      (x, y) ∉ aeOpenRepresentative E := by
    exact (houtLeft.and_eventually
      D.eventually_occupied_nhdsGT_lowerHeight).mono fun y hy => by
        intro hyCarrier
        have hxSection : x ∈ horizontalSection (aeOpenRepresentative E) y :=
          hyCarrier
        rw [D.horizontalSection_eq_Ioo_endpoints hy.2] at hxSection
        exact (not_lt_of_ge hy.1.le) hxSection.1
  exact horizontal_frontier_forbids_oneSided_vertical_oscillation
    D.produce.selected_open D.local_atlas
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (Or.inr self_mem_nhdsWithin) ⟨hax, hxb⟩ hsegment hin hout

private theorem mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_unique
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[>] D.lowerHeight) D.leftEndpoint)
    (hb : MapClusterPt b (𝓝[>] D.lowerHeight) D.leftEndpoint) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (D.mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_not_lt
      ha hb hab).elim
  · exact hab
  · exact (D.mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_not_lt
      hb ha hba).elim

/-- The left endpoint has a finite inward limit at the lower extreme height. -/
theorem exists_leftEndpoint_limit_nhdsGT_lowerHeight
    (D : SelectedBoundaryTopologyInput E U) :
    ∃ L : ℝ, Tendsto D.leftEndpoint (𝓝[>] D.lowerHeight) (𝓝 L) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hmem : ∀ᶠ y in 𝓝[>] D.lowerHeight, D.leftEndpoint y ∈ K :=
    D.eventually_leftEndpoint_mem_endpointRange
      D.eventually_occupied_nhdsGT_lowerHeight
  obtain ⟨L, hLK, hL⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨L, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact D.mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_unique hx hL

private theorem mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : MapClusterPt x (𝓝[>] D.lowerHeight) D.rightEndpoint) :
    x ∈ D.frontierSection D.lowerHeight := by
  apply mapClusterPt_mem_frontierSection_general D
    (tendsto_id.mono_left nhdsWithin_le_nhds) _ hx
  filter_upwards [D.eventually_occupied_nhdsGT_lowerHeight] with y hy
  exact D.rightEndpoint_mem_frontier hy

private theorem mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_not_lt
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[>] D.lowerHeight) D.rightEndpoint)
    (hb : MapClusterPt b (𝓝[>] D.lowerHeight) D.rightEndpoint)
    (hab : a < b) :
    False := by
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have haFrontier :=
    D.mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_mem_frontierSection ha
  have hbFrontier :=
    D.mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_mem_frontierSection hb
  have hsegment : ∀ t ∈ Ioo a b,
      (t, D.lowerHeight) ∈ frontier (aeOpenRepresentative E) := by
    intro t ht
    exact D.isConnected_lower_frontierSection.Icc_subset
      haFrontier hbFrontier ⟨ht.1.le, ht.2.le⟩
  have hin : ∃ᶠ y in 𝓝[>] D.lowerHeight,
      (x, y) ∈ aeOpenRepresentative E :=
    D.frequently_fixed_abscissa_lower_of_rightEndpoint_clusters
      ha hb hax hxb
  have houtRight : ∃ᶠ y in 𝓝[>] D.lowerHeight, D.rightEndpoint y < x :=
    ha.frequently (Iio_mem_nhds hax)
  have hout : ∃ᶠ y in 𝓝[>] D.lowerHeight,
      (x, y) ∉ aeOpenRepresentative E := by
    exact (houtRight.and_eventually
      D.eventually_occupied_nhdsGT_lowerHeight).mono fun y hy => by
        intro hyCarrier
        have hxSection : x ∈ horizontalSection (aeOpenRepresentative E) y :=
          hyCarrier
        rw [D.horizontalSection_eq_Ioo_endpoints hy.2] at hxSection
        exact (not_lt_of_ge hy.1.le) hxSection.2
  exact horizontal_frontier_forbids_oneSided_vertical_oscillation
    D.produce.selected_open D.local_atlas
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (Or.inr self_mem_nhdsWithin) ⟨hax, hxb⟩ hsegment hin hout

private theorem mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_unique
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[>] D.lowerHeight) D.rightEndpoint)
    (hb : MapClusterPt b (𝓝[>] D.lowerHeight) D.rightEndpoint) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (D.mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_not_lt
      ha hb hab).elim
  · exact hab
  · exact (D.mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_not_lt
      hb ha hba).elim

/-- The right endpoint has a finite inward limit at the lower extreme height. -/
theorem exists_rightEndpoint_limit_nhdsGT_lowerHeight
    (D : SelectedBoundaryTopologyInput E U) :
    ∃ R : ℝ, Tendsto D.rightEndpoint (𝓝[>] D.lowerHeight) (𝓝 R) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hmem : ∀ᶠ y in 𝓝[>] D.lowerHeight, D.rightEndpoint y ∈ K :=
    D.eventually_rightEndpoint_mem_endpointRange
      D.eventually_occupied_nhdsGT_lowerHeight
  obtain ⟨R, hRK, hR⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨R, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact D.mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_unique hx hR

private theorem eventually_occupied_nhdsLT_upperHeight
    (D : SelectedBoundaryTopologyInput E U) :
    ∀ᶠ y in 𝓝[<] D.upperHeight, y ∈ D.occupiedHeights := by
  have hlower : ∀ᶠ y in 𝓝[<] D.upperHeight, D.lowerHeight < y :=
    (eventually_gt_nhds D.lowerHeight_lt_upperHeight).filter_mono inf_le_left
  filter_upwards [self_mem_nhdsWithin, hlower] with y hyUpper hyLower
  exact D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hyLower, hyUpper⟩

private theorem frequently_fixed_abscissa_upper_of_leftEndpoint_clusters
    (D : SelectedBoundaryTopologyInput E U) {a x b : ℝ}
    (ha : MapClusterPt a (𝓝[<] D.upperHeight) D.leftEndpoint)
    (hb : MapClusterPt b (𝓝[<] D.upperHeight) D.leftEndpoint)
    (hax : a < x) (hxb : x < b) :
    ∃ᶠ y in 𝓝[<] D.upperHeight,
      (x, y) ∈ aeOpenRepresentative E := by
  rw [(nhdsLT_basis D.upperHeight).frequently_iff]
  intro c hc
  let m := (D.lowerHeight + D.upperHeight) / 2
  let d := max c m
  have hLowerM : D.lowerHeight < m := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hMUpper : m < D.upperHeight := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hLowerD : D.lowerHeight < d := hLowerM.trans_le (le_max_right c m)
  have hDUpper : d < D.upperHeight := by
    rw [max_lt_iff]
    exact ⟨hc, hMUpper⟩
  have hdOccupied : d ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hLowerD, hDUpper⟩
  have hband : Ioo d D.upperHeight ∈ 𝓝[<] D.upperHeight :=
    Ioo_mem_nhdsLT hDUpper
  obtain ⟨ya, hleftA, hyaBand⟩ :=
    ((ha.frequently (Iio_mem_nhds hax)).and_eventually hband).exists
  obtain ⟨yb, hleftB, hybBand⟩ :=
    ((hb.frequently (Ioi_mem_nhds hxb)).and_eventually hband).exists
  have hyaOccupied : ya ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hLowerD.trans hyaBand.1, hyaBand.2⟩
  have hybOccupied : yb ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hLowerD.trans hybBand.1, hybBand.2⟩
  obtain ⟨xa, hleftXa, hxaMin⟩ :=
    exists_between (lt_min hleftA (D.leftEndpoint_lt_rightEndpoint hyaOccupied))
  have hxaX : xa < x := hxaMin.trans_le (min_le_left _ _)
  have hxaRight : xa < D.rightEndpoint ya :=
    hxaMin.trans_le (min_le_right _ _)
  obtain ⟨xb, hleftXb, hxbRight⟩ :=
    exists_between (D.leftEndpoint_lt_rightEndpoint hybOccupied)
  have hxXb : x < xb := hleftB.trans hleftXb
  have hxaBand : (xa, ya) ∈ D.upperBand d := by
    constructor
    · change xa ∈ horizontalSection (aeOpenRepresentative E) ya
      rw [D.horizontalSection_eq_Ioo_endpoints hyaOccupied]
      exact ⟨hleftXa, hxaRight⟩
    · exact hyaBand
  have hxbBand : (xb, yb) ∈ D.upperBand d := by
    constructor
    · change xb ∈ horizontalSection (aeOpenRepresentative E) yb
      rw [D.horizontalSection_eq_Ioo_endpoints hybOccupied]
      exact ⟨hleftXb, hxbRight⟩
    · exact hybBand
  have hprojection :
      IsConnected (Prod.fst '' D.upperBand d) :=
    (D.isConnected_upperBand hdOccupied).image Prod.fst
      continuous_fst.continuousOn
  have hxaProjection : xa ∈ Prod.fst '' D.upperBand d :=
    ⟨(xa, ya), hxaBand, rfl⟩
  have hxbProjection : xb ∈ Prod.fst '' D.upperBand d :=
    ⟨(xb, yb), hxbBand, rfl⟩
  obtain ⟨p, hpBand, hpX⟩ :=
    hprojection.Icc_subset hxaProjection hxbProjection
      ⟨hxaX.le, hxXb.le⟩
  refine ⟨p.2, ⟨(le_max_left c m).trans_lt hpBand.2.1, hpBand.2.2⟩, ?_⟩
  rw [← hpX]
  exact hpBand.1

private theorem frequently_fixed_abscissa_upper_of_rightEndpoint_clusters
    (D : SelectedBoundaryTopologyInput E U) {a x b : ℝ}
    (ha : MapClusterPt a (𝓝[<] D.upperHeight) D.rightEndpoint)
    (hb : MapClusterPt b (𝓝[<] D.upperHeight) D.rightEndpoint)
    (hax : a < x) (hxb : x < b) :
    ∃ᶠ y in 𝓝[<] D.upperHeight,
      (x, y) ∈ aeOpenRepresentative E := by
  rw [(nhdsLT_basis D.upperHeight).frequently_iff]
  intro c hc
  let m := (D.lowerHeight + D.upperHeight) / 2
  let d := max c m
  have hLowerM : D.lowerHeight < m := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hMUpper : m < D.upperHeight := by
    dsimp [m]
    linarith [D.lowerHeight_lt_upperHeight]
  have hLowerD : D.lowerHeight < d := hLowerM.trans_le (le_max_right c m)
  have hDUpper : d < D.upperHeight := by
    rw [max_lt_iff]
    exact ⟨hc, hMUpper⟩
  have hdOccupied : d ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hLowerD, hDUpper⟩
  have hband : Ioo d D.upperHeight ∈ 𝓝[<] D.upperHeight :=
    Ioo_mem_nhdsLT hDUpper
  obtain ⟨ya, hrightA, hyaBand⟩ :=
    ((ha.frequently (Iio_mem_nhds hax)).and_eventually hband).exists
  obtain ⟨yb, hrightB, hybBand⟩ :=
    ((hb.frequently (Ioi_mem_nhds hxb)).and_eventually hband).exists
  have hyaOccupied : ya ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hLowerD.trans hyaBand.1, hyaBand.2⟩
  have hybOccupied : yb ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hLowerD.trans hybBand.1, hybBand.2⟩
  obtain ⟨xa, hleftXa, hxaRight⟩ :=
    exists_between (D.leftEndpoint_lt_rightEndpoint hyaOccupied)
  have hxaX : xa < x := hxaRight.trans hrightA
  have hmaxRight :
      max x (D.leftEndpoint yb) < D.rightEndpoint yb := by
    rw [max_lt_iff]
    exact ⟨hrightB, D.leftEndpoint_lt_rightEndpoint hybOccupied⟩
  obtain ⟨xb, hmaxXb, hxbRight⟩ := exists_between hmaxRight
  have hxXb : x < xb := (le_max_left _ _).trans_lt hmaxXb
  have hleftXb : D.leftEndpoint yb < xb :=
    (le_max_right _ _).trans_lt hmaxXb
  have hxaBand : (xa, ya) ∈ D.upperBand d := by
    constructor
    · change xa ∈ horizontalSection (aeOpenRepresentative E) ya
      rw [D.horizontalSection_eq_Ioo_endpoints hyaOccupied]
      exact ⟨hleftXa, hxaRight⟩
    · exact hyaBand
  have hxbBand : (xb, yb) ∈ D.upperBand d := by
    constructor
    · change xb ∈ horizontalSection (aeOpenRepresentative E) yb
      rw [D.horizontalSection_eq_Ioo_endpoints hybOccupied]
      exact ⟨hleftXb, hxbRight⟩
    · exact hybBand
  have hprojection :
      IsConnected (Prod.fst '' D.upperBand d) :=
    (D.isConnected_upperBand hdOccupied).image Prod.fst
      continuous_fst.continuousOn
  have hxaProjection : xa ∈ Prod.fst '' D.upperBand d :=
    ⟨(xa, ya), hxaBand, rfl⟩
  have hxbProjection : xb ∈ Prod.fst '' D.upperBand d :=
    ⟨(xb, yb), hxbBand, rfl⟩
  obtain ⟨p, hpBand, hpX⟩ :=
    hprojection.Icc_subset hxaProjection hxbProjection
      ⟨hxaX.le, hxXb.le⟩
  refine ⟨p.2, ⟨(le_max_left c m).trans_lt hpBand.2.1, hpBand.2.2⟩, ?_⟩
  rw [← hpX]
  exact hpBand.1

private theorem mapClusterPt_leftEndpoint_nhdsLT_upperHeight_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : MapClusterPt x (𝓝[<] D.upperHeight) D.leftEndpoint) :
    x ∈ D.frontierSection D.upperHeight := by
  apply mapClusterPt_mem_frontierSection_general D
    (tendsto_id.mono_left nhdsWithin_le_nhds) _ hx
  filter_upwards [D.eventually_occupied_nhdsLT_upperHeight] with y hy
  exact D.leftEndpoint_mem_frontier hy

private theorem mapClusterPt_leftEndpoint_nhdsLT_upperHeight_not_lt
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[<] D.upperHeight) D.leftEndpoint)
    (hb : MapClusterPt b (𝓝[<] D.upperHeight) D.leftEndpoint)
    (hab : a < b) :
    False := by
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have haFrontier :=
    D.mapClusterPt_leftEndpoint_nhdsLT_upperHeight_mem_frontierSection ha
  have hbFrontier :=
    D.mapClusterPt_leftEndpoint_nhdsLT_upperHeight_mem_frontierSection hb
  have hsegment : ∀ t ∈ Ioo a b,
      (t, D.upperHeight) ∈ frontier (aeOpenRepresentative E) := by
    intro t ht
    exact D.isConnected_upper_frontierSection.Icc_subset
      haFrontier hbFrontier ⟨ht.1.le, ht.2.le⟩
  have hin : ∃ᶠ y in 𝓝[<] D.upperHeight,
      (x, y) ∈ aeOpenRepresentative E :=
    D.frequently_fixed_abscissa_upper_of_leftEndpoint_clusters
      ha hb hax hxb
  have houtLeft : ∃ᶠ y in 𝓝[<] D.upperHeight, x < D.leftEndpoint y :=
    hb.frequently (Ioi_mem_nhds hxb)
  have hout : ∃ᶠ y in 𝓝[<] D.upperHeight,
      (x, y) ∉ aeOpenRepresentative E := by
    exact (houtLeft.and_eventually
      D.eventually_occupied_nhdsLT_upperHeight).mono fun y hy => by
        intro hyCarrier
        have hxSection : x ∈ horizontalSection (aeOpenRepresentative E) y :=
          hyCarrier
        rw [D.horizontalSection_eq_Ioo_endpoints hy.2] at hxSection
        exact (not_lt_of_ge hy.1.le) hxSection.1
  exact horizontal_frontier_forbids_oneSided_vertical_oscillation
    D.produce.selected_open D.local_atlas
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (Or.inl self_mem_nhdsWithin) ⟨hax, hxb⟩ hsegment hin hout

private theorem mapClusterPt_leftEndpoint_nhdsLT_upperHeight_unique
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[<] D.upperHeight) D.leftEndpoint)
    (hb : MapClusterPt b (𝓝[<] D.upperHeight) D.leftEndpoint) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (D.mapClusterPt_leftEndpoint_nhdsLT_upperHeight_not_lt
      ha hb hab).elim
  · exact hab
  · exact (D.mapClusterPt_leftEndpoint_nhdsLT_upperHeight_not_lt
      hb ha hba).elim

/-- The left endpoint has a finite inward limit at the upper extreme height. -/
theorem exists_leftEndpoint_limit_nhdsLT_upperHeight
    (D : SelectedBoundaryTopologyInput E U) :
    ∃ L : ℝ, Tendsto D.leftEndpoint (𝓝[<] D.upperHeight) (𝓝 L) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hmem : ∀ᶠ y in 𝓝[<] D.upperHeight, D.leftEndpoint y ∈ K :=
    D.eventually_leftEndpoint_mem_endpointRange
      D.eventually_occupied_nhdsLT_upperHeight
  obtain ⟨L, hLK, hL⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨L, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact D.mapClusterPt_leftEndpoint_nhdsLT_upperHeight_unique hx hL

private theorem mapClusterPt_rightEndpoint_nhdsLT_upperHeight_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : MapClusterPt x (𝓝[<] D.upperHeight) D.rightEndpoint) :
    x ∈ D.frontierSection D.upperHeight := by
  apply mapClusterPt_mem_frontierSection_general D
    (tendsto_id.mono_left nhdsWithin_le_nhds) _ hx
  filter_upwards [D.eventually_occupied_nhdsLT_upperHeight] with y hy
  exact D.rightEndpoint_mem_frontier hy

private theorem mapClusterPt_rightEndpoint_nhdsLT_upperHeight_not_lt
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[<] D.upperHeight) D.rightEndpoint)
    (hb : MapClusterPt b (𝓝[<] D.upperHeight) D.rightEndpoint)
    (hab : a < b) :
    False := by
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have haFrontier :=
    D.mapClusterPt_rightEndpoint_nhdsLT_upperHeight_mem_frontierSection ha
  have hbFrontier :=
    D.mapClusterPt_rightEndpoint_nhdsLT_upperHeight_mem_frontierSection hb
  have hsegment : ∀ t ∈ Ioo a b,
      (t, D.upperHeight) ∈ frontier (aeOpenRepresentative E) := by
    intro t ht
    exact D.isConnected_upper_frontierSection.Icc_subset
      haFrontier hbFrontier ⟨ht.1.le, ht.2.le⟩
  have hin : ∃ᶠ y in 𝓝[<] D.upperHeight,
      (x, y) ∈ aeOpenRepresentative E :=
    D.frequently_fixed_abscissa_upper_of_rightEndpoint_clusters
      ha hb hax hxb
  have houtRight : ∃ᶠ y in 𝓝[<] D.upperHeight, D.rightEndpoint y < x :=
    ha.frequently (Iio_mem_nhds hax)
  have hout : ∃ᶠ y in 𝓝[<] D.upperHeight,
      (x, y) ∉ aeOpenRepresentative E := by
    exact (houtRight.and_eventually
      D.eventually_occupied_nhdsLT_upperHeight).mono fun y hy => by
        intro hyCarrier
        have hxSection : x ∈ horizontalSection (aeOpenRepresentative E) y :=
          hyCarrier
        rw [D.horizontalSection_eq_Ioo_endpoints hy.2] at hxSection
        exact (not_lt_of_ge hy.1.le) hxSection.2
  exact horizontal_frontier_forbids_oneSided_vertical_oscillation
    D.produce.selected_open D.local_atlas
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (Or.inl self_mem_nhdsWithin) ⟨hax, hxb⟩ hsegment hin hout

private theorem mapClusterPt_rightEndpoint_nhdsLT_upperHeight_unique
    (D : SelectedBoundaryTopologyInput E U) {a b : ℝ}
    (ha : MapClusterPt a (𝓝[<] D.upperHeight) D.rightEndpoint)
    (hb : MapClusterPt b (𝓝[<] D.upperHeight) D.rightEndpoint) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact (D.mapClusterPt_rightEndpoint_nhdsLT_upperHeight_not_lt
      ha hb hab).elim
  · exact hab
  · exact (D.mapClusterPt_rightEndpoint_nhdsLT_upperHeight_not_lt
      hb ha hba).elim

/-- The right endpoint has a finite inward limit at the upper extreme height. -/
theorem exists_rightEndpoint_limit_nhdsLT_upperHeight
    (D : SelectedBoundaryTopologyInput E U) :
    ∃ R : ℝ, Tendsto D.rightEndpoint (𝓝[<] D.upperHeight) (𝓝 R) := by
  let K := Prod.fst '' closure (aeOpenRepresentative E)
  have hmem : ∀ᶠ y in 𝓝[<] D.upperHeight, D.rightEndpoint y ∈ K :=
    D.eventually_rightEndpoint_mem_endpointRange
      D.eventually_occupied_nhdsLT_upperHeight
  obtain ⟨R, hRK, hR⟩ :=
    D.isCompact_endpointRange.exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  refine ⟨R, D.isCompact_endpointRange.tendsto_nhds_of_unique_mapClusterPt
    hmem ?_⟩
  intro x _hxK hx
  exact D.mapClusterPt_rightEndpoint_nhdsLT_upperHeight_unique hx hR

/-- Canonical left-endpoint limit at the lower extreme. -/
theorem tendsto_leftEndpoint_nhdsGT_lowerHeight_rightLim
    (D : SelectedBoundaryTopologyInput E U) :
    Tendsto D.leftEndpoint (𝓝[>] D.lowerHeight)
      (𝓝 (Function.rightLim D.leftEndpoint D.lowerHeight)) :=
  tendsto_rightLim_of_tendsto D.exists_leftEndpoint_limit_nhdsGT_lowerHeight

/-- Canonical right-endpoint limit at the lower extreme. -/
theorem tendsto_rightEndpoint_nhdsGT_lowerHeight_rightLim
    (D : SelectedBoundaryTopologyInput E U) :
    Tendsto D.rightEndpoint (𝓝[>] D.lowerHeight)
      (𝓝 (Function.rightLim D.rightEndpoint D.lowerHeight)) :=
  tendsto_rightLim_of_tendsto D.exists_rightEndpoint_limit_nhdsGT_lowerHeight

/-- Canonical left-endpoint limit at the upper extreme. -/
theorem tendsto_leftEndpoint_nhdsLT_upperHeight_leftLim
    (D : SelectedBoundaryTopologyInput E U) :
    Tendsto D.leftEndpoint (𝓝[<] D.upperHeight)
      (𝓝 (Function.leftLim D.leftEndpoint D.upperHeight)) :=
  tendsto_leftLim_of_tendsto D.exists_leftEndpoint_limit_nhdsLT_upperHeight

/-- Canonical right-endpoint limit at the upper extreme. -/
theorem tendsto_rightEndpoint_nhdsLT_upperHeight_leftLim
    (D : SelectedBoundaryTopologyInput E U) :
    Tendsto D.rightEndpoint (𝓝[<] D.upperHeight)
      (𝓝 (Function.leftLim D.rightEndpoint D.upperHeight)) :=
  tendsto_leftLim_of_tendsto D.exists_rightEndpoint_limit_nhdsLT_upperHeight

/-- The two inward endpoint limits remain ordered at the lower extreme. -/
theorem rightLim_leftEndpoint_le_rightLim_rightEndpoint_lowerHeight
    (D : SelectedBoundaryTopologyInput E U) :
    Function.rightLim D.leftEndpoint D.lowerHeight ≤
      Function.rightLim D.rightEndpoint D.lowerHeight := by
  exact le_of_tendsto_of_tendsto
    D.tendsto_leftEndpoint_nhdsGT_lowerHeight_rightLim
    D.tendsto_rightEndpoint_nhdsGT_lowerHeight_rightLim
    (D.eventually_occupied_nhdsGT_lowerHeight.mono fun y hy =>
      (D.leftEndpoint_lt_rightEndpoint hy).le)

/-- The two inward endpoint limits remain ordered at the upper extreme. -/
theorem leftLim_leftEndpoint_le_leftLim_rightEndpoint_upperHeight
    (D : SelectedBoundaryTopologyInput E U) :
    Function.leftLim D.leftEndpoint D.upperHeight ≤
      Function.leftLim D.rightEndpoint D.upperHeight := by
  exact le_of_tendsto_of_tendsto
    D.tendsto_leftEndpoint_nhdsLT_upperHeight_leftLim
    D.tendsto_rightEndpoint_nhdsLT_upperHeight_leftLim
    (D.eventually_occupied_nhdsLT_upperHeight.mono fun y hy =>
      (D.leftEndpoint_lt_rightEndpoint hy).le)

private theorem rightLim_leftEndpoint_lowerHeight_le_of_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : x ∈ D.frontierSection D.lowerHeight) :
    Function.rightLim D.leftEndpoint D.lowerHeight ≤ x := by
  by_contra hle
  have hxLimit : x < Function.rightLim D.leftEndpoint D.lowerHeight :=
    lt_of_not_ge hle
  obtain ⟨t, hxt, htLimit⟩ := exists_between hxLimit
  have hevent : ∀ᶠ y in 𝓝[>] D.lowerHeight, t < D.leftEndpoint y :=
    D.tendsto_leftEndpoint_nhdsGT_lowerHeight_rightLim
      (Ioi_mem_nhds htLimit)
  obtain ⟨c, hcLower, hcEndpoint⟩ :=
    (nhdsGT_basis D.lowerHeight).eventually_iff.mp hevent
  let W : Set PlanePoint := Iio t ×ˢ Iio c
  have hWopen : IsOpen W := isOpen_Iio.prod isOpen_Iio
  have hpointW : (x, D.lowerHeight) ∈ W := ⟨hxt, hcLower⟩
  have hclosure :
      (x, D.lowerHeight) ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hx
  obtain ⟨q, hqW, hqCarrier⟩ :=
    mem_closure_iff.mp hclosure W hWopen hpointW
  have hqOccupied : q.2 ∈ D.occupiedHeights := ⟨q, hqCarrier, rfl⟩
  have hqBounds := D.mem_occupiedHeights_iff_height_bounds.mp hqOccupied
  have hqEndpoint : t < D.leftEndpoint q.2 :=
    hcEndpoint ⟨hqBounds.1, hqW.2⟩
  have hqSection : q.1 ∈ horizontalSection (aeOpenRepresentative E) q.2 :=
    hqCarrier
  rw [D.horizontalSection_eq_Ioo_endpoints hqOccupied] at hqSection
  exact (not_lt_of_ge hqSection.1.le) (hqW.1.trans hqEndpoint)

private theorem mem_frontierSection_lowerHeight_le_rightLim_rightEndpoint
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : x ∈ D.frontierSection D.lowerHeight) :
    x ≤ Function.rightLim D.rightEndpoint D.lowerHeight := by
  by_contra hle
  have hLimitX : Function.rightLim D.rightEndpoint D.lowerHeight < x :=
    lt_of_not_ge hle
  obtain ⟨t, hLimitT, htx⟩ := exists_between hLimitX
  have hevent : ∀ᶠ y in 𝓝[>] D.lowerHeight, D.rightEndpoint y < t :=
    D.tendsto_rightEndpoint_nhdsGT_lowerHeight_rightLim
      (Iio_mem_nhds hLimitT)
  obtain ⟨c, hcLower, hcEndpoint⟩ :=
    (nhdsGT_basis D.lowerHeight).eventually_iff.mp hevent
  let W : Set PlanePoint := Ioi t ×ˢ Iio c
  have hWopen : IsOpen W := isOpen_Ioi.prod isOpen_Iio
  have hpointW : (x, D.lowerHeight) ∈ W := ⟨htx, hcLower⟩
  have hclosure :
      (x, D.lowerHeight) ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hx
  obtain ⟨q, hqW, hqCarrier⟩ :=
    mem_closure_iff.mp hclosure W hWopen hpointW
  have hqOccupied : q.2 ∈ D.occupiedHeights := ⟨q, hqCarrier, rfl⟩
  have hqBounds := D.mem_occupiedHeights_iff_height_bounds.mp hqOccupied
  have hqEndpoint : D.rightEndpoint q.2 < t :=
    hcEndpoint ⟨hqBounds.1, hqW.2⟩
  have hqSection : q.1 ∈ horizontalSection (aeOpenRepresentative E) q.2 :=
    hqCarrier
  rw [D.horizontalSection_eq_Ioo_endpoints hqOccupied] at hqSection
  exact (not_lt_of_ge hqW.1.le) (hqSection.2.trans hqEndpoint)

/-- The complete lower extreme frontier slice is exactly the interval between
the two inward endpoint limits. -/
theorem lower_frontierSection_eq_Icc_endpointLimits
    (D : SelectedBoundaryTopologyInput E U) :
    D.frontierSection D.lowerHeight =
      Icc (Function.rightLim D.leftEndpoint D.lowerHeight)
        (Function.rightLim D.rightEndpoint D.lowerHeight) := by
  apply subset_antisymm
  · intro x hx
    exact ⟨D.rightLim_leftEndpoint_lowerHeight_le_of_mem_frontierSection hx,
      D.mem_frontierSection_lowerHeight_le_rightLim_rightEndpoint hx⟩
  · have hleft :
        Function.rightLim D.leftEndpoint D.lowerHeight ∈
          D.frontierSection D.lowerHeight :=
      D.mapClusterPt_leftEndpoint_nhdsGT_lowerHeight_mem_frontierSection
        D.tendsto_leftEndpoint_nhdsGT_lowerHeight_rightLim.mapClusterPt
    have hright :
        Function.rightLim D.rightEndpoint D.lowerHeight ∈
          D.frontierSection D.lowerHeight :=
      D.mapClusterPt_rightEndpoint_nhdsGT_lowerHeight_mem_frontierSection
        D.tendsto_rightEndpoint_nhdsGT_lowerHeight_rightLim.mapClusterPt
    exact D.isConnected_lower_frontierSection.Icc_subset hleft hright

private theorem leftLim_leftEndpoint_upperHeight_le_of_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : x ∈ D.frontierSection D.upperHeight) :
    Function.leftLim D.leftEndpoint D.upperHeight ≤ x := by
  by_contra hle
  have hxLimit : x < Function.leftLim D.leftEndpoint D.upperHeight :=
    lt_of_not_ge hle
  obtain ⟨t, hxt, htLimit⟩ := exists_between hxLimit
  have hevent : ∀ᶠ y in 𝓝[<] D.upperHeight, t < D.leftEndpoint y :=
    D.tendsto_leftEndpoint_nhdsLT_upperHeight_leftLim
      (Ioi_mem_nhds htLimit)
  obtain ⟨c, hcUpper, hcEndpoint⟩ :=
    (nhdsLT_basis D.upperHeight).eventually_iff.mp hevent
  let W : Set PlanePoint := Iio t ×ˢ Ioi c
  have hWopen : IsOpen W := isOpen_Iio.prod isOpen_Ioi
  have hpointW : (x, D.upperHeight) ∈ W := ⟨hxt, hcUpper⟩
  have hclosure :
      (x, D.upperHeight) ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hx
  obtain ⟨q, hqW, hqCarrier⟩ :=
    mem_closure_iff.mp hclosure W hWopen hpointW
  have hqOccupied : q.2 ∈ D.occupiedHeights := ⟨q, hqCarrier, rfl⟩
  have hqBounds := D.mem_occupiedHeights_iff_height_bounds.mp hqOccupied
  have hqEndpoint : t < D.leftEndpoint q.2 :=
    hcEndpoint ⟨hqW.2, hqBounds.2⟩
  have hqSection : q.1 ∈ horizontalSection (aeOpenRepresentative E) q.2 :=
    hqCarrier
  rw [D.horizontalSection_eq_Ioo_endpoints hqOccupied] at hqSection
  exact (not_lt_of_ge hqSection.1.le) (hqW.1.trans hqEndpoint)

private theorem mem_frontierSection_upperHeight_le_leftLim_rightEndpoint
    (D : SelectedBoundaryTopologyInput E U) {x : ℝ}
    (hx : x ∈ D.frontierSection D.upperHeight) :
    x ≤ Function.leftLim D.rightEndpoint D.upperHeight := by
  by_contra hle
  have hLimitX : Function.leftLim D.rightEndpoint D.upperHeight < x :=
    lt_of_not_ge hle
  obtain ⟨t, hLimitT, htx⟩ := exists_between hLimitX
  have hevent : ∀ᶠ y in 𝓝[<] D.upperHeight, D.rightEndpoint y < t :=
    D.tendsto_rightEndpoint_nhdsLT_upperHeight_leftLim
      (Iio_mem_nhds hLimitT)
  obtain ⟨c, hcUpper, hcEndpoint⟩ :=
    (nhdsLT_basis D.upperHeight).eventually_iff.mp hevent
  let W : Set PlanePoint := Ioi t ×ˢ Ioi c
  have hWopen : IsOpen W := isOpen_Ioi.prod isOpen_Ioi
  have hpointW : (x, D.upperHeight) ∈ W := ⟨htx, hcUpper⟩
  have hclosure :
      (x, D.upperHeight) ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hx
  obtain ⟨q, hqW, hqCarrier⟩ :=
    mem_closure_iff.mp hclosure W hWopen hpointW
  have hqOccupied : q.2 ∈ D.occupiedHeights := ⟨q, hqCarrier, rfl⟩
  have hqBounds := D.mem_occupiedHeights_iff_height_bounds.mp hqOccupied
  have hqEndpoint : D.rightEndpoint q.2 < t :=
    hcEndpoint ⟨hqW.2, hqBounds.2⟩
  have hqSection : q.1 ∈ horizontalSection (aeOpenRepresentative E) q.2 :=
    hqCarrier
  rw [D.horizontalSection_eq_Ioo_endpoints hqOccupied] at hqSection
  exact (not_lt_of_ge hqW.1.le) (hqSection.2.trans hqEndpoint)

/-- The complete upper extreme frontier slice is exactly the interval between
the two inward endpoint limits. -/
theorem upper_frontierSection_eq_Icc_endpointLimits
    (D : SelectedBoundaryTopologyInput E U) :
    D.frontierSection D.upperHeight =
      Icc (Function.leftLim D.leftEndpoint D.upperHeight)
        (Function.leftLim D.rightEndpoint D.upperHeight) := by
  apply subset_antisymm
  · intro x hx
    exact ⟨D.leftLim_leftEndpoint_upperHeight_le_of_mem_frontierSection hx,
      D.mem_frontierSection_upperHeight_le_leftLim_rightEndpoint hx⟩
  · have hleft :
        Function.leftLim D.leftEndpoint D.upperHeight ∈
          D.frontierSection D.upperHeight :=
      D.mapClusterPt_leftEndpoint_nhdsLT_upperHeight_mem_frontierSection
        D.tendsto_leftEndpoint_nhdsLT_upperHeight_leftLim.mapClusterPt
    have hright :
        Function.leftLim D.rightEndpoint D.upperHeight ∈
          D.frontierSection D.upperHeight :=
      D.mapClusterPt_rightEndpoint_nhdsLT_upperHeight_mem_frontierSection
        D.tendsto_rightEndpoint_nhdsLT_upperHeight_leftLim.mapClusterPt
    exact D.isConnected_upper_frontierSection.Icc_subset hleft hright

private theorem min_leftEndpoint_limits_le_of_mem_frontierSection
    (D : SelectedBoundaryTopologyInput E U) {y x : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hx : x ∈ D.frontierSection y) :
    min (Function.leftLim D.leftEndpoint y)
        (Function.rightLim D.leftEndpoint y) ≤ x := by
  by_contra hle
  have hxMin : x < min (Function.leftLim D.leftEndpoint y)
      (Function.rightLim D.leftEndpoint y) := lt_of_not_ge hle
  obtain ⟨t, hxt, htMin⟩ := exists_between hxMin
  have htLeftLim : t < Function.leftLim D.leftEndpoint y :=
    htMin.trans_le (min_le_left _ _)
  have htRightLim : t < Function.rightLim D.leftEndpoint y :=
    htMin.trans_le (min_le_right _ _)
  have heventBelow : ∀ᶠ z in 𝓝[<] y, t < D.leftEndpoint z :=
    D.tendsto_leftEndpoint_nhdsLT_leftLim hy (Ioi_mem_nhds htLeftLim)
  have heventAbove : ∀ᶠ z in 𝓝[>] y, t < D.leftEndpoint z :=
    D.tendsto_leftEndpoint_nhdsGT_rightLim hy (Ioi_mem_nhds htRightLim)
  obtain ⟨c, hcY, hcEndpoint⟩ :=
    (nhdsLT_basis y).eventually_iff.mp heventBelow
  obtain ⟨d, hyD, hdEndpoint⟩ :=
    (nhdsGT_basis y).eventually_iff.mp heventAbove
  have hleftLimLe : Function.leftLim D.leftEndpoint y ≤ D.leftEndpoint y :=
    mapClusterPt_leftEndpoint_le_general D hy
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (D.tendsto_leftEndpoint_nhdsLT_leftLim hy).mapClusterPt
  have htValue : t < D.leftEndpoint y := htLeftLim.trans_le hleftLimLe
  let W : Set PlanePoint := Iio t ×ˢ Ioo c d
  have hWopen : IsOpen W := isOpen_Iio.prod isOpen_Ioo
  have hpointW : (x, y) ∈ W := ⟨hxt, hcY, hyD⟩
  have hclosure : (x, y) ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hx
  obtain ⟨q, hqW, hqCarrier⟩ :=
    mem_closure_iff.mp hclosure W hWopen hpointW
  have hqOccupied : q.2 ∈ D.occupiedHeights := ⟨q, hqCarrier, rfl⟩
  have hqEndpoint : t < D.leftEndpoint q.2 := by
    rcases lt_trichotomy q.2 y with hqy | hqy | hyq
    · exact hcEndpoint ⟨hqW.2.1, hqy⟩
    · simpa only [hqy] using htValue
    · exact hdEndpoint ⟨hyq, hqW.2.2⟩
  have hqSection : q.1 ∈ horizontalSection (aeOpenRepresentative E) q.2 :=
    hqCarrier
  rw [D.horizontalSection_eq_Ioo_endpoints hqOccupied] at hqSection
  exact (not_lt_of_ge hqSection.1.le) (hqW.1.trans hqEndpoint)

private theorem mem_frontierSection_le_max_rightEndpoint_limits
    (D : SelectedBoundaryTopologyInput E U) {y x : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hx : x ∈ D.frontierSection y) :
    x ≤ max (Function.leftLim D.rightEndpoint y)
      (Function.rightLim D.rightEndpoint y) := by
  by_contra hle
  have hMaxX : max (Function.leftLim D.rightEndpoint y)
      (Function.rightLim D.rightEndpoint y) < x := lt_of_not_ge hle
  obtain ⟨t, hMaxT, htx⟩ := exists_between hMaxX
  have hLeftLimT : Function.leftLim D.rightEndpoint y < t :=
    (le_max_left _ _).trans_lt hMaxT
  have hRightLimT : Function.rightLim D.rightEndpoint y < t :=
    (le_max_right _ _).trans_lt hMaxT
  have heventBelow : ∀ᶠ z in 𝓝[<] y, D.rightEndpoint z < t :=
    D.tendsto_rightEndpoint_nhdsLT_leftLim hy (Iio_mem_nhds hLeftLimT)
  have heventAbove : ∀ᶠ z in 𝓝[>] y, D.rightEndpoint z < t :=
    D.tendsto_rightEndpoint_nhdsGT_rightLim hy (Iio_mem_nhds hRightLimT)
  obtain ⟨c, hcY, hcEndpoint⟩ :=
    (nhdsLT_basis y).eventually_iff.mp heventBelow
  obtain ⟨d, hyD, hdEndpoint⟩ :=
    (nhdsGT_basis y).eventually_iff.mp heventAbove
  have hvalueLeLeftLim : D.rightEndpoint y ≤
      Function.leftLim D.rightEndpoint y :=
    mapClusterPt_rightEndpoint_ge_general D hy
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (D.tendsto_rightEndpoint_nhdsLT_leftLim hy).mapClusterPt
  have hValueT : D.rightEndpoint y < t :=
    hvalueLeLeftLim.trans_lt hLeftLimT
  let W : Set PlanePoint := Ioi t ×ˢ Ioo c d
  have hWopen : IsOpen W := isOpen_Ioi.prod isOpen_Ioo
  have hpointW : (x, y) ∈ W := ⟨htx, hcY, hyD⟩
  have hclosure : (x, y) ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hx
  obtain ⟨q, hqW, hqCarrier⟩ :=
    mem_closure_iff.mp hclosure W hWopen hpointW
  have hqOccupied : q.2 ∈ D.occupiedHeights := ⟨q, hqCarrier, rfl⟩
  have hqEndpoint : D.rightEndpoint q.2 < t := by
    rcases lt_trichotomy q.2 y with hqy | hqy | hyq
    · exact hcEndpoint ⟨hqW.2.1, hqy⟩
    · simpa only [hqy] using hValueT
    · exact hdEndpoint ⟨hyq, hqW.2.2⟩
  have hqSection : q.1 ∈ horizontalSection (aeOpenRepresentative E) q.2 :=
    hqCarrier
  rw [D.horizontalSection_eq_Ioo_endpoints hqOccupied] at hqSection
  exact (not_lt_of_ge hqW.1.le) (hqSection.2.trans hqEndpoint)

/-- Every occupied frontier slice is exactly the union of its left and right
endpoint-jump segments.  The segment extents are the two genuine one-sided
limits of the corresponding endpoint function. -/
theorem frontierSection_eq_endpointLimitIntervals
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    D.frontierSection y =
      Icc (min (Function.leftLim D.leftEndpoint y)
          (Function.rightLim D.leftEndpoint y))
        (D.leftEndpoint y) ∪
      Icc (D.rightEndpoint y)
        (max (Function.leftLim D.rightEndpoint y)
          (Function.rightLim D.rightEndpoint y)) := by
  apply subset_antisymm
  · intro x hx
    rcases D.frontierSection_subset_endpoint_exteriors hy hx with
        hxLeft | hxRight
    · exact Or.inl
        ⟨D.min_leftEndpoint_limits_le_of_mem_frontierSection hy hx,
          hxLeft⟩
    · exact Or.inr
        ⟨hxRight,
          D.mem_frontierSection_le_max_rightEndpoint_limits hy hx⟩
  · rintro x (hxLeft | hxRight)
    · by_cases hlimits :
          Function.leftLim D.leftEndpoint y ≤
            Function.rightLim D.leftEndpoint y
      · rw [min_eq_left hlimits] at hxLeft
        exact D.Icc_leftLim_leftEndpoint_subset_frontierSection hy hxLeft
      · rw [min_eq_right (le_of_not_ge hlimits)] at hxLeft
        exact D.Icc_rightLim_leftEndpoint_subset_frontierSection hy hxLeft
    · by_cases hlimits :
          Function.leftLim D.rightEndpoint y ≤
            Function.rightLim D.rightEndpoint y
      · rw [max_eq_right hlimits] at hxRight
        exact D.Icc_rightEndpoint_rightLim_subset_frontierSection hy hxRight
      · rw [max_eq_left (le_of_not_ge hlimits)] at hxRight
        exact D.Icc_rightEndpoint_leftLim_subset_frontierSection hy hxRight
end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
