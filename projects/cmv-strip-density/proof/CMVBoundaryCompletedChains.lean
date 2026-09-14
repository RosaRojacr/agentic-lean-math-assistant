/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryEndpointLimits

/-!
# Intrinsic completed boundary chains

The genuine one-sided section-endpoint limits cannot terminate in a slit.  A
local half-space chart forces each completed endpoint segment to run from its
lower-side limit to its upper-side limit.  This module records that no-slit
fact before constructing the two height-directed boundary chains.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

open CMVRelaxation
open CMVSourceClassification

variable {E U : Set PlanePoint}

private def occupiedRectangle (side : OccupiedHalfPlane) (δ : ℝ) :
    Set PlanePoint :=
  match side with
  | .lower => Ioo (-δ) δ ×ˢ Ioo (-δ) 0
  | .upper => Ioo (-δ) δ ×ˢ Ioo 0 δ

private theorem isConnected_occupiedRectangle
    (side : OccupiedHalfPlane) {δ : ℝ} (hδ : 0 < δ) :
    IsConnected (occupiedRectangle side δ) := by
  cases side
  · exact (isConnected_Ioo (neg_lt_self hδ)).prod
      (isConnected_Ioo (neg_neg_of_pos hδ))
  · exact (isConnected_Ioo (neg_lt_self hδ)).prod
      (isConnected_Ioo hδ)

private theorem occupiedRectangle_subset_ball
    (side : OccupiedHalfPlane) {δ : ℝ} :
    occupiedRectangle side δ ⊆ Metric.ball ((0, 0) : PlanePoint) δ := by
  intro q hq
  cases side with
  | lower =>
      rcases hq with ⟨hx, hy⟩
      change -δ < q.1 ∧ q.1 < δ at hx
      change -δ < q.2 ∧ q.2 < 0 at hy
      have hδ : 0 < δ := by linarith [hx.1, hx.2]
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · simpa only [Real.dist_eq, sub_zero, abs_lt] using hx
      · rw [Real.dist_eq, sub_zero, abs_lt]
        exact ⟨hy.1, hy.2.trans hδ⟩
  | upper =>
      rcases hq with ⟨hx, hy⟩
      change -δ < q.1 ∧ q.1 < δ at hx
      change 0 < q.2 ∧ q.2 < δ at hy
      have hδ : 0 < δ := by linarith [hx.1, hx.2]
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · simpa only [Real.dist_eq, sub_zero, abs_lt] using hx
      · rw [Real.dist_eq, sub_zero, abs_lt]
        exact ⟨(neg_neg_of_pos hδ).trans hy.1, hy.2⟩

private theorem occupiedRectangle_subset_carrier
    (side : OccupiedHalfPlane) {δ : ℝ} :
    occupiedRectangle side δ ⊆ side.carrier := by
  intro q hq
  cases side with
  | lower => exact ⟨Set.mem_univ _, hq.2.2⟩
  | upper => exact ⟨Set.mem_univ _, hq.2.1⟩

private theorem mem_occupiedRectangle_of_mem_ball_carrier
    (side : OccupiedHalfPlane) {δ : ℝ} {q : PlanePoint}
    (hqBall : q ∈ Metric.ball ((0, 0) : PlanePoint) δ)
    (hqSide : q ∈ side.carrier) :
    q ∈ occupiedRectangle side δ := by
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hqBall
  have hx' : -δ < q.1 ∧ q.1 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_lt] using hqBall.1
  have hy' : -δ < q.2 ∧ q.2 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_lt] using hqBall.2
  have hx : q.1 ∈ Ioo (-δ) δ := hx'
  have hy : q.2 ∈ Ioo (-δ) δ := hy'
  cases side with
  | lower => exact ⟨hx, hy.1, hqSide.2⟩
  | upper => exact ⟨hx, hqSide.2, hy.2⟩

/-- A horizontal open frontier segment cannot be the end of a slit whose two
vertical sides are both occupied.  The proof uses one actual half-space chart:
a small occupied coordinate half-rectangle is connected, while its physical
height projection would have to cross the horizontal frontier segment. -/
private theorem horizontal_frontier_forbids_occupied_both_vertical_sides
    {O : Set PlanePoint} (hO : IsOpen O) (A₀ : BoundaryHalfSpaceAtlas O)
    {a x b y : ℝ} (hx : x ∈ Ioo a b)
    (hsegment : ∀ t ∈ Ioo a b, (t, y) ∈ frontier O)
    (hbelow : ∀ᶠ z in 𝓝[<] y, (x, z) ∈ O)
    (habove : ∀ᶠ z in 𝓝[>] y, (x, z) ∈ O) :
    False := by
  let p : {q : PlanePoint // q ∈ frontier O} := ⟨(x, y), hsegment x hx⟩
  let A := A₀.intervalAt p
  let P : Set PlanePoint := Ioo a b ×ˢ Set.univ
  let N : Set PlanePoint :=
    A.ambient.coord.target ∩ A.ambient.coord.symm ⁻¹' P
  have hPopen : IsOpen P := isOpen_Ioo.prod isOpen_univ
  have hNopen : IsOpen N :=
    A.ambient.coord.symm.isOpen_inter_preimage hPopen
  have hzeroTarget : ((0, 0) : PlanePoint) ∈ A.ambient.coord.target :=
    A.ambient.zero_mem_target
  have hsymmZero : A.ambient.coord.symm (0, 0) = (x, y) := by
    rw [← A.ambient.coord_base]
    exact A.ambient.coord.left_inv A.ambient.base_mem_source
  have hzeroN : ((0, 0) : PlanePoint) ∈ N := by
    refine ⟨hzeroTarget, ?_⟩
    change A.ambient.coord.symm (0, 0) ∈ P
    rw [hsymmZero]
    exact ⟨hx, Set.mem_univ _⟩
  obtain ⟨ε, hε, hballN⟩ :=
    Metric.isOpen_iff.mp hNopen (0, 0) hzeroN
  let δ := min A.radius ε / 2
  have hmin : 0 < min A.radius ε := lt_min A.radius_pos hε
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδRadius : δ < A.radius := by
    dsimp [δ]
    have hle := min_le_left A.radius ε
    linarith
  have hδEpsilon : δ < ε := by
    dsimp [δ]
    have hle := min_le_right A.radius ε
    linarith
  let T : Set PlanePoint := occupiedRectangle A.ambient.side δ
  have hTconnected : IsConnected T :=
    isConnected_occupiedRectangle A.ambient.side hδ
  have hTtarget : T ⊆ A.ambient.coord.target := by
    intro q hq
    apply A.ball_subset_target
    have hqδ := occupiedRectangle_subset_ball A.ambient.side hq
    rw [Metric.mem_ball] at hqδ ⊢
    exact hqδ.trans hδRadius
  have hTside : T ⊆ A.ambient.side.carrier :=
    occupiedRectangle_subset_carrier A.ambient.side
  have hTphysical : A.ambient.coord.symm '' T ⊆ P := by
    rintro q ⟨z, hzT, rfl⟩
    have hzδ := occupiedRectangle_subset_ball A.ambient.side hzT
    have hzε : z ∈ Metric.ball ((0, 0) : PlanePoint) ε := by
      rw [Metric.mem_ball] at hzδ ⊢
      exact hzδ.trans hδEpsilon
    exact (hballN hzε).2
  have hToccupied : A.ambient.coord.symm '' T ⊆ O := by
    rintro q ⟨z, hzT, rfl⟩
    have hzTarget := hTtarget hzT
    have hqSource := A.ambient.coord.map_target hzTarget
    apply (A.ambient.carrier_image.apply_mem_iff hqSource).mp
    rw [A.ambient.coord.right_inv hzTarget]
    exact hTside hzT
  have hphysicalConnected : IsConnected (A.ambient.coord.symm '' T) :=
    hTconnected.image _
      (A.ambient.coord.continuousOn_symm.mono hTtarget)
  let V : Set PlanePoint :=
    A.ambient.coord.source ∩
      A.ambient.coord ⁻¹' Metric.ball ((0, 0) : PlanePoint) δ
  have hVopen : IsOpen V :=
    A.ambient.coord.isOpen_inter_preimage Metric.isOpen_ball
  have hpV : (x, y) ∈ V := by
    refine ⟨A.ambient.base_mem_source, ?_⟩
    change A.ambient.coord (x, y) ∈ Metric.ball ((0, 0) : PlanePoint) δ
    rw [show A.ambient.coord (x, y) = (0, 0) from A.ambient.coord_base]
    exact Metric.mem_ball_self hδ
  have hvertical : Tendsto (fun z : ℝ => (x, z)) (𝓝 y) (𝓝 (x, y)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hVnhds : V ∈ 𝓝 (x, y) := hVopen.mem_nhds hpV
  have hVbelow : ∀ᶠ z in 𝓝[<] y, (x, z) ∈ V :=
    (hvertical.mono_left inf_le_left) hVnhds
  have hVabove : ∀ᶠ z in 𝓝[>] y, (x, z) ∈ V :=
    (hvertical.mono_left inf_le_left) hVnhds
  obtain ⟨s, hsO, hsV, hsy⟩ :=
    (hbelow.and (hVbelow.and self_mem_nhdsWithin)).exists
  obtain ⟨t, htO, htV, hyt⟩ :=
    (habove.and (hVabove.and self_mem_nhdsWithin)).exists
  have hsCoordSide : A.ambient.coord (x, s) ∈ A.ambient.side.carrier :=
    (A.ambient.carrier_image.apply_mem_iff hsV.1).mpr hsO
  have htCoordSide : A.ambient.coord (x, t) ∈ A.ambient.side.carrier :=
    (A.ambient.carrier_image.apply_mem_iff htV.1).mpr htO
  have hsCoordT : A.ambient.coord (x, s) ∈ T :=
    mem_occupiedRectangle_of_mem_ball_carrier A.ambient.side hsV.2 hsCoordSide
  have htCoordT : A.ambient.coord (x, t) ∈ T :=
    mem_occupiedRectangle_of_mem_ball_carrier A.ambient.side htV.2 htCoordSide
  have hsPhysical : (x, s) ∈ A.ambient.coord.symm '' T := by
    refine ⟨A.ambient.coord (x, s), hsCoordT, ?_⟩
    exact A.ambient.coord.left_inv hsV.1
  have htPhysical : (x, t) ∈ A.ambient.coord.symm '' T := by
    refine ⟨A.ambient.coord (x, t), htCoordT, ?_⟩
    exact A.ambient.coord.left_inv htV.1
  have hheightConnected : IsConnected
      (Prod.snd '' (A.ambient.coord.symm '' T)) :=
    hphysicalConnected.image Prod.snd continuous_snd.continuousOn
  have hsHeight : s ∈ Prod.snd '' (A.ambient.coord.symm '' T) :=
    ⟨(x, s), hsPhysical, rfl⟩
  have htHeight : t ∈ Prod.snd '' (A.ambient.coord.symm '' T) :=
    ⟨(x, t), htPhysical, rfl⟩
  have hyHeight : y ∈ Prod.snd '' (A.ambient.coord.symm '' T) :=
    hheightConnected.Icc_subset hsHeight htHeight ⟨hsy.le, hyt.le⟩
  obtain ⟨q, hqPhysical, hqy⟩ := hyHeight
  have hqP := hTphysical hqPhysical
  have hqO := hToccupied hqPhysical
  have hqFrontier : q ∈ frontier O := by
    have := hsegment q.1 hqP.1
    rwa [← hqy] at this
  have hqEmpty : q ∈ O ∩ frontier O := ⟨hqO, hqFrontier⟩
  rw [hO.inter_frontier_eq] at hqEmpty
  exact hqEmpty.elim

/-- The lower-side left-endpoint limit cannot exceed the endpoint value. -/
theorem leftLim_leftEndpoint_le
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Function.leftLim D.leftEndpoint y ≤ D.leftEndpoint y := by
  by_contra hle
  have hvalueLimit : D.leftEndpoint y <
      Function.leftLim D.leftEndpoint y := lt_of_not_ge hle
  obtain ⟨c, hvalueC, hcLimit⟩ := exists_between hvalueLimit
  have hgt : ∀ᶠ z in 𝓝[<] y, c < D.leftEndpoint z :=
    (tendsto_order.mp (D.tendsto_leftEndpoint_nhdsLT_leftLim hy)).1 c hcLimit
  have hlt : ∀ᶠ z in 𝓝[<] y, D.leftEndpoint z < c :=
    (D.upperSemicontinuousAt_leftEndpoint hy c hvalueC).filter_mono inf_le_left
  obtain ⟨z, hzgt, hzlt⟩ := (hgt.and hlt).exists
  exact (hzgt.trans hzlt).false

/-- The upper-side left-endpoint limit cannot exceed the endpoint value. -/
theorem rightLim_leftEndpoint_le
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    Function.rightLim D.leftEndpoint y ≤ D.leftEndpoint y := by
  by_contra hle
  have hvalueLimit : D.leftEndpoint y <
      Function.rightLim D.leftEndpoint y := lt_of_not_ge hle
  obtain ⟨c, hvalueC, hcLimit⟩ := exists_between hvalueLimit
  have hgt : ∀ᶠ z in 𝓝[>] y, c < D.leftEndpoint z :=
    (tendsto_order.mp (D.tendsto_leftEndpoint_nhdsGT_rightLim hy)).1 c hcLimit
  have hlt : ∀ᶠ z in 𝓝[>] y, D.leftEndpoint z < c :=
    (D.upperSemicontinuousAt_leftEndpoint hy c hvalueC).filter_mono inf_le_left
  obtain ⟨z, hzgt, hzlt⟩ := (hgt.and hlt).exists
  exact (hzgt.trans hzlt).false

/-- The endpoint value cannot exceed the lower-side right-endpoint limit. -/
theorem rightEndpoint_le_leftLim
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    D.rightEndpoint y ≤ Function.leftLim D.rightEndpoint y := by
  by_contra hle
  have hlimitValue : Function.leftLim D.rightEndpoint y <
      D.rightEndpoint y := lt_of_not_ge hle
  obtain ⟨c, hlimitC, hcValue⟩ := exists_between hlimitValue
  have hlt : ∀ᶠ z in 𝓝[<] y, D.rightEndpoint z < c :=
    (tendsto_order.mp (D.tendsto_rightEndpoint_nhdsLT_leftLim hy)).2 c hlimitC
  have hgt : ∀ᶠ z in 𝓝[<] y, c < D.rightEndpoint z :=
    (D.lowerSemicontinuousAt_rightEndpoint hy c hcValue).filter_mono inf_le_left
  obtain ⟨z, hzlt, hzgt⟩ := (hlt.and hgt).exists
  exact (hzgt.trans hzlt).false

/-- The endpoint value cannot exceed the upper-side right-endpoint limit. -/
theorem rightEndpoint_le_rightLim
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    D.rightEndpoint y ≤ Function.rightLim D.rightEndpoint y := by
  by_contra hle
  have hlimitValue : Function.rightLim D.rightEndpoint y <
      D.rightEndpoint y := lt_of_not_ge hle
  obtain ⟨c, hlimitC, hcValue⟩ := exists_between hlimitValue
  have hlt : ∀ᶠ z in 𝓝[>] y, D.rightEndpoint z < c :=
    (tendsto_order.mp (D.tendsto_rightEndpoint_nhdsGT_rightLim hy)).2 c hlimitC
  have hgt : ∀ᶠ z in 𝓝[>] y, c < D.rightEndpoint z :=
    (D.lowerSemicontinuousAt_rightEndpoint hy c hcValue).filter_mono inf_le_left
  obtain ⟨z, hzlt, hzgt⟩ := (hlt.and hgt).exists
  exact (hzgt.trans hzlt).false
/-- No-slit completion for the left boundary: the actual endpoint value is one
of the two one-sided limits, hence their maximum. -/
theorem max_leftEndpoint_limits_eq
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    max (Function.leftLim D.leftEndpoint y)
        (Function.rightLim D.leftEndpoint y) =
      D.leftEndpoint y := by
  apply le_antisymm
  · exact max_le (D.leftLim_leftEndpoint_le hy)
      (D.rightLim_leftEndpoint_le hy)
  · by_contra hle
    have hgap : max (Function.leftLim D.leftEndpoint y)
        (Function.rightLim D.leftEndpoint y) < D.leftEndpoint y :=
      lt_of_not_ge hle
    obtain ⟨x, hmaxX, hxValue⟩ := exists_between hgap
    have hleftLimitX : Function.leftLim D.leftEndpoint y < x :=
      (le_max_left _ _).trans_lt hmaxX
    have hrightLimitX : Function.rightLim D.leftEndpoint y < x :=
      (le_max_right _ _).trans_lt hmaxX
    obtain ⟨w, hvalueW, hwRight⟩ :=
      exists_between (D.leftEndpoint_lt_rightEndpoint hy)
    have hxW : x < w := hxValue.trans hvalueW
    have hwSection :
        w ∈ horizontalSection (aeOpenRepresentative E) y := by
      rw [D.horizontalSection_eq_Ioo_endpoints hy]
      exact ⟨hvalueW, hwRight⟩
    have hcore := D.eventually_endpoints_straddle_of_mem hwSection
    have hoccupied := D.eventually_mem_occupiedHeights hy
    have hleftBelow : ∀ᶠ z in 𝓝[<] y, D.leftEndpoint z < x :=
      (tendsto_order.mp
        (D.tendsto_leftEndpoint_nhdsLT_leftLim hy)).2 x hleftLimitX
    have hleftAbove : ∀ᶠ z in 𝓝[>] y, D.leftEndpoint z < x :=
      (tendsto_order.mp
        (D.tendsto_leftEndpoint_nhdsGT_rightLim hy)).2 x hrightLimitX
    have hbelow : ∀ᶠ z in 𝓝[<] y,
        (x, z) ∈ aeOpenRepresentative E := by
      filter_upwards [hleftBelow, hcore.filter_mono inf_le_left,
        hoccupied.filter_mono inf_le_left] with z hzLeft hzCore hzOccupied
      change x ∈ horizontalSection (aeOpenRepresentative E) z
      rw [D.horizontalSection_eq_Ioo_endpoints hzOccupied]
      exact ⟨hzLeft, hxW.trans hzCore.2⟩
    have habove : ∀ᶠ z in 𝓝[>] y,
        (x, z) ∈ aeOpenRepresentative E := by
      filter_upwards [hleftAbove, hcore.filter_mono inf_le_left,
        hoccupied.filter_mono inf_le_left] with z hzLeft hzCore hzOccupied
      change x ∈ horizontalSection (aeOpenRepresentative E) z
      rw [D.horizontalSection_eq_Ioo_endpoints hzOccupied]
      exact ⟨hzLeft, hxW.trans hzCore.2⟩
    have hsegment : ∀ t ∈ Ioo
        (max (Function.leftLim D.leftEndpoint y)
          (Function.rightLim D.leftEndpoint y))
        (D.leftEndpoint y),
        (t, y) ∈ frontier (aeOpenRepresentative E) := by
      intro t ht
      apply D.Icc_leftLim_leftEndpoint_subset_frontierSection hy
      exact ⟨(le_max_left _ _).trans ht.1.le, ht.2.le⟩
    exact horizontal_frontier_forbids_occupied_both_vertical_sides
      D.produce.selected_open D.local_atlas
      ⟨hmaxX, hxValue⟩ hsegment hbelow habove

/-- No-slit completion for the right boundary: the actual endpoint value is
one of the two one-sided limits, hence their minimum. -/
theorem min_rightEndpoint_limits_eq
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    min (Function.leftLim D.rightEndpoint y)
        (Function.rightLim D.rightEndpoint y) =
      D.rightEndpoint y := by
  apply le_antisymm
  · by_contra hle
    have hgap : D.rightEndpoint y <
        min (Function.leftLim D.rightEndpoint y)
          (Function.rightLim D.rightEndpoint y) :=
      lt_of_not_ge hle
    obtain ⟨x, hvalueX, hxMin⟩ := exists_between hgap
    have hxLeftLimit : x < Function.leftLim D.rightEndpoint y :=
      hxMin.trans_le (min_le_left _ _)
    have hxRightLimit : x < Function.rightLim D.rightEndpoint y :=
      hxMin.trans_le (min_le_right _ _)
    obtain ⟨w, hleftW, hwValue⟩ :=
      exists_between (D.leftEndpoint_lt_rightEndpoint hy)
    have hwX : w < x := hwValue.trans hvalueX
    have hwSection :
        w ∈ horizontalSection (aeOpenRepresentative E) y := by
      rw [D.horizontalSection_eq_Ioo_endpoints hy]
      exact ⟨hleftW, hwValue⟩
    have hcore := D.eventually_endpoints_straddle_of_mem hwSection
    have hoccupied := D.eventually_mem_occupiedHeights hy
    have hrightBelow : ∀ᶠ z in 𝓝[<] y, x < D.rightEndpoint z :=
      (tendsto_order.mp
        (D.tendsto_rightEndpoint_nhdsLT_leftLim hy)).1 x hxLeftLimit
    have hrightAbove : ∀ᶠ z in 𝓝[>] y, x < D.rightEndpoint z :=
      (tendsto_order.mp
        (D.tendsto_rightEndpoint_nhdsGT_rightLim hy)).1 x hxRightLimit
    have hbelow : ∀ᶠ z in 𝓝[<] y,
        (x, z) ∈ aeOpenRepresentative E := by
      filter_upwards [hrightBelow, hcore.filter_mono inf_le_left,
        hoccupied.filter_mono inf_le_left] with z hzRight hzCore hzOccupied
      change x ∈ horizontalSection (aeOpenRepresentative E) z
      rw [D.horizontalSection_eq_Ioo_endpoints hzOccupied]
      exact ⟨hzCore.1.trans hwX, hzRight⟩
    have habove : ∀ᶠ z in 𝓝[>] y,
        (x, z) ∈ aeOpenRepresentative E := by
      filter_upwards [hrightAbove, hcore.filter_mono inf_le_left,
        hoccupied.filter_mono inf_le_left] with z hzRight hzCore hzOccupied
      change x ∈ horizontalSection (aeOpenRepresentative E) z
      rw [D.horizontalSection_eq_Ioo_endpoints hzOccupied]
      exact ⟨hzCore.1.trans hwX, hzRight⟩
    have hsegment : ∀ t ∈ Ioo (D.rightEndpoint y)
        (min (Function.leftLim D.rightEndpoint y)
          (Function.rightLim D.rightEndpoint y)),
        (t, y) ∈ frontier (aeOpenRepresentative E) := by
      intro t ht
      apply D.Icc_rightEndpoint_leftLim_subset_frontierSection hy
      exact ⟨ht.1.le, ht.2.le.trans (min_le_left _ _)⟩
    exact horizontal_frontier_forbids_occupied_both_vertical_sides
      D.produce.selected_open D.local_atlas
      ⟨hvalueX, hxMin⟩ hsegment hbelow habove
  · exact le_min (D.rightEndpoint_le_leftLim hy)
      (D.rightEndpoint_le_rightLim hy)

/-- Every interior frontier slice is the disjoint union of the two oriented
completed endpoint segments.  Their endpoints are the genuine lower- and
upper-side limits, so this formula retains the direction of every jump. -/
theorem frontierSection_eq_orientedEndpointSegments
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    D.frontierSection y =
      uIcc (Function.leftLim D.leftEndpoint y)
          (Function.rightLim D.leftEndpoint y) ∪
      uIcc (Function.leftLim D.rightEndpoint y)
          (Function.rightLim D.rightEndpoint y) := by
  rw [D.frontierSection_eq_endpointLimitIntervals hy,
    ← D.max_leftEndpoint_limits_eq hy,
    ← D.min_rightEndpoint_limits_eq hy]
  rfl


/-- Left and right abscissae of the completed lower extreme slice. -/
def lowerLeft (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  Function.rightLim D.leftEndpoint D.lowerHeight

def lowerRight (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  Function.rightLim D.rightEndpoint D.lowerHeight

/-- Left and right abscissae of the completed upper extreme slice. -/
def upperLeft (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  Function.leftLim D.leftEndpoint D.upperHeight

def upperRight (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  Function.leftLim D.rightEndpoint D.upperHeight

/-- Intrinsic split abscissae of the two extreme frontier intervals.  A
singleton extreme slice is allowed, in which case its split is that point. -/
def lowerSplit (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  (D.lowerLeft + D.lowerRight) / 2

def upperSplit (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  (D.upperLeft + D.upperRight) / 2

/-- The two actual points at which the completed chains meet. -/
def lowerSplitPoint (D : SelectedBoundaryTopologyInput E U) : PlanePoint :=
  (D.lowerSplit, D.lowerHeight)

def upperSplitPoint (D : SelectedBoundaryTopologyInput E U) : PlanePoint :=
  (D.upperSplit, D.upperHeight)

theorem lowerLeft_le_lowerSplit
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerLeft ≤ D.lowerSplit := by
  have h := D.rightLim_leftEndpoint_le_rightLim_rightEndpoint_lowerHeight
  dsimp [lowerLeft, lowerRight, lowerSplit]
  linarith

theorem lowerSplit_le_lowerRight
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerSplit ≤ D.lowerRight := by
  have h := D.rightLim_leftEndpoint_le_rightLim_rightEndpoint_lowerHeight
  dsimp [lowerLeft, lowerRight, lowerSplit]
  linarith

theorem upperLeft_le_upperSplit
    (D : SelectedBoundaryTopologyInput E U) :
    D.upperLeft ≤ D.upperSplit := by
  have h := D.leftLim_leftEndpoint_le_leftLim_rightEndpoint_upperHeight
  dsimp [upperLeft, upperRight, upperSplit]
  linarith

theorem upperSplit_le_upperRight
    (D : SelectedBoundaryTopologyInput E U) :
    D.upperSplit ≤ D.upperRight := by
  have h := D.leftLim_leftEndpoint_le_leftLim_rightEndpoint_upperHeight
  dsimp [upperLeft, upperRight, upperSplit]
  linarith

/-- The left height-completed boundary chain.  Its interior fibers are the
oriented completed left-endpoint segments; its extreme fibers stop at the
intrinsic split points. -/
def leftCompletedChain (D : SelectedBoundaryTopologyInput E U) :
    Set PlanePoint :=
  {p |
    (p.2 = D.lowerHeight ∧ p.1 ∈ Icc D.lowerLeft D.lowerSplit) ∨
    (p.2 ∈ D.occupiedHeights ∧
      p.1 ∈ uIcc (Function.leftLim D.leftEndpoint p.2)
        (Function.rightLim D.leftEndpoint p.2)) ∨
    (p.2 = D.upperHeight ∧ p.1 ∈ Icc D.upperLeft D.upperSplit)}

/-- The right height-completed boundary chain, with the complementary halves
of both extreme fibers. -/
def rightCompletedChain (D : SelectedBoundaryTopologyInput E U) :
    Set PlanePoint :=
  {p |
    (p.2 = D.lowerHeight ∧ p.1 ∈ Icc D.lowerSplit D.lowerRight) ∨
    (p.2 ∈ D.occupiedHeights ∧
      p.1 ∈ uIcc (Function.leftLim D.rightEndpoint p.2)
        (Function.rightLim D.rightEndpoint p.2)) ∨
    (p.2 = D.upperHeight ∧ p.1 ∈ Icc D.upperSplit D.upperRight)}

theorem orientedLeftSegment_le_leftEndpoint
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hx : x ∈ uIcc (Function.leftLim D.leftEndpoint y)
      (Function.rightLim D.leftEndpoint y)) :
    x ≤ D.leftEndpoint y := by
  rw [← D.max_leftEndpoint_limits_eq hy]
  exact hx.2

theorem rightEndpoint_le_orientedRightSegment
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ}
    (hy : y ∈ D.occupiedHeights)
    (hx : x ∈ uIcc (Function.leftLim D.rightEndpoint y)
      (Function.rightLim D.rightEndpoint y)) :
    D.rightEndpoint y ≤ x := by
  rw [← D.min_rightEndpoint_limits_eq hy]
  exact hx.1

/-- Every point of the left completed chain lies on the actual complete
frontier. -/
theorem leftCompletedChain_subset_frontier
    (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChain ⊆ frontier (aeOpenRepresentative E) := by
  intro p hp
  rcases hp with hpLower | hpInterior | hpUpper
  · change p.1 ∈ D.frontierSection p.2
    rw [hpLower.1, D.lower_frontierSection_eq_Icc_endpointLimits]
    change p.1 ∈ Icc D.lowerLeft D.lowerRight
    exact ⟨hpLower.2.1,
      hpLower.2.2.trans D.lowerSplit_le_lowerRight⟩
  · change p.1 ∈ D.frontierSection p.2
    rw [D.frontierSection_eq_orientedEndpointSegments hpInterior.1]
    exact Or.inl hpInterior.2
  · change p.1 ∈ D.frontierSection p.2
    rw [hpUpper.1, D.upper_frontierSection_eq_Icc_endpointLimits]
    change p.1 ∈ Icc D.upperLeft D.upperRight
    exact ⟨hpUpper.2.1,
      hpUpper.2.2.trans D.upperSplit_le_upperRight⟩

/-- Every point of the right completed chain lies on the actual complete
frontier. -/
theorem rightCompletedChain_subset_frontier
    (D : SelectedBoundaryTopologyInput E U) :
    D.rightCompletedChain ⊆ frontier (aeOpenRepresentative E) := by
  intro p hp
  rcases hp with hpLower | hpInterior | hpUpper
  · change p.1 ∈ D.frontierSection p.2
    rw [hpLower.1, D.lower_frontierSection_eq_Icc_endpointLimits]
    change p.1 ∈ Icc D.lowerLeft D.lowerRight
    exact ⟨D.lowerLeft_le_lowerSplit.trans hpLower.2.1,
      hpLower.2.2⟩
  · change p.1 ∈ D.frontierSection p.2
    rw [D.frontierSection_eq_orientedEndpointSegments hpInterior.1]
    exact Or.inr hpInterior.2
  · change p.1 ∈ D.frontierSection p.2
    rw [hpUpper.1, D.upper_frontierSection_eq_Icc_endpointLimits]
    change p.1 ∈ Icc D.upperLeft D.upperRight
    exact ⟨D.upperLeft_le_upperSplit.trans hpUpper.2.1,
      hpUpper.2.2⟩

/-- The two intrinsic completed chains exhaust the actual frontier. -/
theorem frontier_eq_union_completedChains
    (D : SelectedBoundaryTopologyInput E U) :
    frontier (aeOpenRepresentative E) =
      D.leftCompletedChain ∪ D.rightCompletedChain := by
  apply subset_antisymm
  · intro p hp
    have hpHeight := D.frontier_snd_mem_Icc hp
    rcases hpHeight.1.eq_or_lt with hpLower | hpLower
    · have hpLower' : p.2 = D.lowerHeight := hpLower.symm
      have hpSection : p.1 ∈ D.frontierSection D.lowerHeight := by
        change (p.1, D.lowerHeight) ∈ frontier (aeOpenRepresentative E)
        rwa [← hpLower']
      rw [D.lower_frontierSection_eq_Icc_endpointLimits] at hpSection
      change p.1 ∈ Icc D.lowerLeft D.lowerRight at hpSection
      rcases le_total p.1 D.lowerSplit with hpSplit | hsplitP
      · exact Or.inl (Or.inl
          ⟨hpLower', hpSection.1, hpSplit⟩)
      · exact Or.inr (Or.inl
          ⟨hpLower', hsplitP, hpSection.2⟩)
    · rcases hpHeight.2.eq_or_lt with hpUpper | hpUpper
      · have hpSection : p.1 ∈ D.frontierSection D.upperHeight := by
          change (p.1, D.upperHeight) ∈ frontier (aeOpenRepresentative E)
          rwa [← hpUpper]
        rw [D.upper_frontierSection_eq_Icc_endpointLimits] at hpSection
        change p.1 ∈ Icc D.upperLeft D.upperRight at hpSection
        rcases le_total p.1 D.upperSplit with hpSplit | hsplitP
        · exact Or.inl (Or.inr (Or.inr
            ⟨hpUpper, hpSection.1, hpSplit⟩))
        · exact Or.inr (Or.inr (Or.inr
            ⟨hpUpper, hsplitP, hpSection.2⟩))
      · have hpOccupied : p.2 ∈ D.occupiedHeights :=
          D.mem_occupiedHeights_iff_height_bounds.mpr
            ⟨hpLower, hpUpper⟩
        have hpSection : p.1 ∈ D.frontierSection p.2 := hp
        rw [D.frontierSection_eq_orientedEndpointSegments hpOccupied] at hpSection
        rcases hpSection with hpLeft | hpRight
        · exact Or.inl (Or.inr (Or.inl ⟨hpOccupied, hpLeft⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨hpOccupied, hpRight⟩))
  · exact union_subset D.leftCompletedChain_subset_frontier
      D.rightCompletedChain_subset_frontier

/-- The lower and upper split points are distinct, even when either extreme
frontier slice is a singleton. -/
theorem lowerSplitPoint_ne_upperSplitPoint
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerSplitPoint ≠ D.upperSplitPoint := by
  intro h
  have hheight := congrArg Prod.snd h
  exact D.lowerHeight_lt_upperHeight.ne hheight

/-- The completed chains meet at exactly the two intrinsic extreme split
points.  In particular, their interior fibers are disjoint. -/
theorem completedChains_inter_eq
    (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChain ∩ D.rightCompletedChain =
      {D.lowerSplitPoint, D.upperSplitPoint} := by
  ext p
  constructor
  · rintro ⟨hpLeft, hpRight⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hpLeft with hLeftLower | hLeftInterior | hLeftUpper
    · rcases hpRight with hRightLower | hRightInterior | hRightUpper
      · left
        change p = (D.lowerSplit, D.lowerHeight)
        apply Prod.ext
        · exact le_antisymm hLeftLower.2.2 hRightLower.2.1
        · exact hLeftLower.1
      · have hbounds :=
          D.mem_occupiedHeights_iff_height_bounds.mp hRightInterior.1
        rw [hLeftLower.1] at hbounds
        exact (lt_irrefl D.lowerHeight hbounds.1).elim
      · have hheight : D.lowerHeight = D.upperHeight :=
          hLeftLower.1.symm.trans hRightUpper.1
        exact (D.lowerHeight_lt_upperHeight.ne hheight).elim
    · rcases hpRight with hRightLower | hRightInterior | hRightUpper
      · have hbounds :=
          D.mem_occupiedHeights_iff_height_bounds.mp hLeftInterior.1
        rw [hRightLower.1] at hbounds
        exact (lt_irrefl D.lowerHeight hbounds.1).elim
      · have hxLeft :=
          D.orientedLeftSegment_le_leftEndpoint
            hLeftInterior.1 hLeftInterior.2
        have hxRight :=
          D.rightEndpoint_le_orientedRightSegment
            hRightInterior.1 hRightInterior.2
        have hwrong : D.rightEndpoint p.2 ≤ D.leftEndpoint p.2 :=
          hxRight.trans hxLeft
        exact ((not_le_of_gt
          (D.leftEndpoint_lt_rightEndpoint hLeftInterior.1)) hwrong).elim
      · have hbounds :=
          D.mem_occupiedHeights_iff_height_bounds.mp hLeftInterior.1
        rw [hRightUpper.1] at hbounds
        exact (lt_irrefl D.upperHeight hbounds.2).elim
    · rcases hpRight with hRightLower | hRightInterior | hRightUpper
      · have hheight : D.upperHeight = D.lowerHeight :=
          hLeftUpper.1.symm.trans hRightLower.1
        exact (D.lowerHeight_lt_upperHeight.ne hheight.symm).elim
      · have hbounds :=
          D.mem_occupiedHeights_iff_height_bounds.mp hRightInterior.1
        rw [hLeftUpper.1] at hbounds
        exact (lt_irrefl D.upperHeight hbounds.2).elim
      · right
        change p = (D.upperSplit, D.upperHeight)
        apply Prod.ext
        · exact le_antisymm hLeftUpper.2.2 hRightUpper.2.1
        · exact hLeftUpper.1
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · constructor
      · exact Or.inl ⟨rfl, D.lowerLeft_le_lowerSplit, le_rfl⟩
      · exact Or.inl ⟨rfl, le_rfl, D.lowerSplit_le_lowerRight⟩
    · constructor
      · exact Or.inr (Or.inr
          ⟨rfl, D.upperLeft_le_upperSplit, le_rfl⟩)
      · exact Or.inr (Or.inr
          ⟨rfl, le_rfl, D.upperSplit_le_upperRight⟩)
/-- The left completed boundary chain is closed. -/
theorem isClosed_leftCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    IsClosed D.leftCompletedChain := by
  apply IsSeqClosed.isClosed
  intro q p hq hqp
  have hpFrontier : p ∈ frontier (aeOpenRepresentative E) := by
    apply isClosed_frontier.mem_of_tendsto hqp
    exact Filter.Eventually.of_forall fun n =>
      D.leftCompletedChain_subset_frontier (hq n)
  have hpHeight := D.frontier_snd_mem_Icc hpFrontier
  rcases hpHeight.1.eq_or_lt with hpLower | hpLower
  · have hpLower' : p.2 = D.lowerHeight := hpLower.symm
    have hpSection : p.1 ∈ D.frontierSection D.lowerHeight := by
      change (p.1, D.lowerHeight) ∈ frontier (aeOpenRepresentative E)
      rwa [← hpLower']
    rw [D.lower_frontierSection_eq_Icc_endpointLimits] at hpSection
    change p.1 ∈ Icc D.lowerLeft D.lowerRight at hpSection
    have hpSplit : p.1 ≤ D.lowerSplit := by
      by_contra hle
      have hsplitP : D.lowerSplit < p.1 := lt_of_not_ge hle
      have hxEventually : ∀ᶠ n in atTop, D.lowerSplit < (q n).1 :=
        hqp.fst_nhds (Ioi_mem_nhds hsplitP)
      have hpBelowUpper : p.2 < D.upperHeight := by
        rw [hpLower']
        exact D.lowerHeight_lt_upperHeight
      have hyEventually : ∀ᶠ n in atTop, (q n).2 < D.upperHeight :=
        hqp.snd_nhds (Iio_mem_nhds hpBelowUpper)
      have hInterior : ∀ᶠ n in atTop,
          (q n).2 ∈ D.occupiedHeights ∧
            (q n).1 ≤ D.leftEndpoint (q n).2 := by
        filter_upwards [hxEventually, hyEventually] with n hsplitX hyUpper
        rcases hq n with hLower | hMiddle | hUpper
        · exact (not_lt_of_ge hLower.2.2 hsplitX).elim
        · exact ⟨hMiddle.1,
            D.orientedLeftSegment_le_leftEndpoint hMiddle.1 hMiddle.2⟩
        · rw [hUpper.1] at hyUpper
          exact (lt_irrefl D.upperHeight hyUpper).elim
      have hyAbove : ∀ᶠ n in atTop, D.lowerHeight < (q n).2 :=
        hInterior.mono fun n hn =>
          (D.mem_occupiedHeights_iff_height_bounds.mp hn.1).1
      have hEndpoint : Tendsto (fun n => D.leftEndpoint (q n).2) atTop
          (𝓝 D.lowerLeft) := by
        change Tendsto (fun n => D.leftEndpoint (q n).2) atTop
          (𝓝 (Function.rightLim D.leftEndpoint D.lowerHeight))
        have hyTendsto : Tendsto (fun n => (q n).2) atTop
            (𝓝 D.lowerHeight) := by
          simpa only [hpLower'] using hqp.snd_nhds
        exact D.tendsto_leftEndpoint_nhdsGT_lowerHeight_rightLim.comp
          (tendsto_nhdsWithin_iff.mpr ⟨hyTendsto, hyAbove⟩)
      have hpLeLowerLeft : p.1 ≤ D.lowerLeft :=
        le_of_tendsto_of_tendsto hqp.fst_nhds hEndpoint
          (hInterior.mono fun _ hn => hn.2)
      exact (not_le_of_gt hsplitP)
        (hpLeLowerLeft.trans D.lowerLeft_le_lowerSplit)
    exact Or.inl ⟨hpLower', hpSection.1, hpSplit⟩
  · rcases hpHeight.2.eq_or_lt with hpUpper | hpUpper
    · have hpSection : p.1 ∈ D.frontierSection D.upperHeight := by
        change (p.1, D.upperHeight) ∈ frontier (aeOpenRepresentative E)
        rwa [← hpUpper]
      rw [D.upper_frontierSection_eq_Icc_endpointLimits] at hpSection
      change p.1 ∈ Icc D.upperLeft D.upperRight at hpSection
      have hpSplit : p.1 ≤ D.upperSplit := by
        by_contra hle
        have hsplitP : D.upperSplit < p.1 := lt_of_not_ge hle
        have hxEventually : ∀ᶠ n in atTop, D.upperSplit < (q n).1 :=
          hqp.fst_nhds (Ioi_mem_nhds hsplitP)
        have hpAboveLower : D.lowerHeight < p.2 := by
          rw [hpUpper]
          exact D.lowerHeight_lt_upperHeight
        have hyEventually : ∀ᶠ n in atTop, D.lowerHeight < (q n).2 :=
          hqp.snd_nhds (Ioi_mem_nhds hpAboveLower)
        have hInterior : ∀ᶠ n in atTop,
            (q n).2 ∈ D.occupiedHeights ∧
              (q n).1 ≤ D.leftEndpoint (q n).2 := by
          filter_upwards [hxEventually, hyEventually] with n hsplitX hyLower
          rcases hq n with hLower | hMiddle | hUpper'
          · rw [hLower.1] at hyLower
            exact (lt_irrefl D.lowerHeight hyLower).elim
          · exact ⟨hMiddle.1,
              D.orientedLeftSegment_le_leftEndpoint hMiddle.1 hMiddle.2⟩
          · exact (not_lt_of_ge hUpper'.2.2 hsplitX).elim
        have hyBelow : ∀ᶠ n in atTop, (q n).2 < D.upperHeight :=
          hInterior.mono fun n hn =>
            (D.mem_occupiedHeights_iff_height_bounds.mp hn.1).2
        have hEndpoint : Tendsto (fun n => D.leftEndpoint (q n).2) atTop
            (𝓝 D.upperLeft) := by
          change Tendsto (fun n => D.leftEndpoint (q n).2) atTop
            (𝓝 (Function.leftLim D.leftEndpoint D.upperHeight))
          have hyTendsto : Tendsto (fun n => (q n).2) atTop
              (𝓝 D.upperHeight) := by
            simpa only [hpUpper] using hqp.snd_nhds
          exact D.tendsto_leftEndpoint_nhdsLT_upperHeight_leftLim.comp
            (tendsto_nhdsWithin_iff.mpr ⟨hyTendsto, hyBelow⟩)
        have hpLeUpperLeft : p.1 ≤ D.upperLeft :=
          le_of_tendsto_of_tendsto hqp.fst_nhds hEndpoint
            (hInterior.mono fun _ hn => hn.2)
        exact (not_le_of_gt hsplitP)
          (hpLeUpperLeft.trans D.upperLeft_le_upperSplit)
      exact Or.inr (Or.inr ⟨hpUpper, hpSection.1, hpSplit⟩)
    · have hpOccupied : p.2 ∈ D.occupiedHeights :=
        D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hpLower, hpUpper⟩
      have hyEventually : ∀ᶠ n in atTop, (q n).2 ∈ D.occupiedHeights := by
        have hyLower : ∀ᶠ n in atTop, D.lowerHeight < (q n).2 :=
          hqp.snd_nhds (Ioi_mem_nhds hpLower)
        have hyUpper : ∀ᶠ n in atTop, (q n).2 < D.upperHeight :=
          hqp.snd_nhds (Iio_mem_nhds hpUpper)
        filter_upwards [hyLower, hyUpper] with n hnLower hnUpper
        exact D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hnLower, hnUpper⟩
      have hInterior : ∀ᶠ n in atTop,
          (q n).1 ≤ D.leftEndpoint (q n).2 := by
        filter_upwards [hyEventually] with n hn
        rcases hq n with hLower | hMiddle | hUpper'
        · have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hn
          rw [hLower.1] at hbounds
          exact (lt_irrefl D.lowerHeight hbounds.1).elim
        · exact D.orientedLeftSegment_le_leftEndpoint hMiddle.1 hMiddle.2
        · have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hn
          rw [hUpper'.1] at hbounds
          exact (lt_irrefl D.upperHeight hbounds.2).elim
      have hpLeEndpoint : p.1 ≤ D.leftEndpoint p.2 := by
        by_contra hle
        have hEndpointP : D.leftEndpoint p.2 < p.1 := lt_of_not_ge hle
        obtain ⟨t, hEndpointT, htP⟩ := exists_between hEndpointP
        have hxEventually : ∀ᶠ n in atTop, t < (q n).1 :=
          hqp.fst_nhds (Ioi_mem_nhds htP)
        have hEndpointEventually : ∀ᶠ n in atTop,
            D.leftEndpoint (q n).2 < t :=
          hqp.snd_nhds
            (D.upperSemicontinuousAt_leftEndpoint hpOccupied t hEndpointT)
        obtain ⟨n, hnx, hnEndpoint, hnLe⟩ :=
          (hxEventually.and (hEndpointEventually.and hInterior)).exists
        exact ((hnx.trans_le hnLe).trans hnEndpoint).false
      have hpSection : p.1 ∈ D.frontierSection p.2 := hpFrontier
      rw [D.frontierSection_eq_orientedEndpointSegments hpOccupied] at hpSection
      rcases hpSection with hpLeft | hpRight
      · exact Or.inr (Or.inl ⟨hpOccupied, hpLeft⟩)
      · have hrightLe :=
          D.rightEndpoint_le_orientedRightSegment hpOccupied hpRight
        have hwrong : D.rightEndpoint p.2 ≤ D.leftEndpoint p.2 :=
          hrightLe.trans hpLeEndpoint
        exact ((not_le_of_gt
          (D.leftEndpoint_lt_rightEndpoint hpOccupied)) hwrong).elim

/-- The right completed boundary chain is closed. -/
theorem isClosed_rightCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    IsClosed D.rightCompletedChain := by
  apply IsSeqClosed.isClosed
  intro q p hq hqp
  have hpFrontier : p ∈ frontier (aeOpenRepresentative E) := by
    apply isClosed_frontier.mem_of_tendsto hqp
    exact Filter.Eventually.of_forall fun n =>
      D.rightCompletedChain_subset_frontier (hq n)
  have hpHeight := D.frontier_snd_mem_Icc hpFrontier
  rcases hpHeight.1.eq_or_lt with hpLower | hpLower
  · have hpLower' : p.2 = D.lowerHeight := hpLower.symm
    have hpSection : p.1 ∈ D.frontierSection D.lowerHeight := by
      change (p.1, D.lowerHeight) ∈ frontier (aeOpenRepresentative E)
      rwa [← hpLower']
    rw [D.lower_frontierSection_eq_Icc_endpointLimits] at hpSection
    change p.1 ∈ Icc D.lowerLeft D.lowerRight at hpSection
    have hpSplit : D.lowerSplit ≤ p.1 := by
      by_contra hle
      have hpSplit' : p.1 < D.lowerSplit := lt_of_not_ge hle
      have hxEventually : ∀ᶠ n in atTop, (q n).1 < D.lowerSplit :=
        hqp.fst_nhds (Iio_mem_nhds hpSplit')
      have hpBelowUpper : p.2 < D.upperHeight := by
        rw [hpLower']
        exact D.lowerHeight_lt_upperHeight
      have hyEventually : ∀ᶠ n in atTop, (q n).2 < D.upperHeight :=
        hqp.snd_nhds (Iio_mem_nhds hpBelowUpper)
      have hInterior : ∀ᶠ n in atTop,
          (q n).2 ∈ D.occupiedHeights ∧
            D.rightEndpoint (q n).2 ≤ (q n).1 := by
        filter_upwards [hxEventually, hyEventually] with n hxSplit hyUpper
        rcases hq n with hLower | hMiddle | hUpper
        · exact (not_lt_of_ge hLower.2.1 hxSplit).elim
        · exact ⟨hMiddle.1,
            D.rightEndpoint_le_orientedRightSegment hMiddle.1 hMiddle.2⟩
        · rw [hUpper.1] at hyUpper
          exact (lt_irrefl D.upperHeight hyUpper).elim
      have hyAbove : ∀ᶠ n in atTop, D.lowerHeight < (q n).2 :=
        hInterior.mono fun n hn =>
          (D.mem_occupiedHeights_iff_height_bounds.mp hn.1).1
      have hEndpoint : Tendsto (fun n => D.rightEndpoint (q n).2) atTop
          (𝓝 D.lowerRight) := by
        change Tendsto (fun n => D.rightEndpoint (q n).2) atTop
          (𝓝 (Function.rightLim D.rightEndpoint D.lowerHeight))
        have hyTendsto : Tendsto (fun n => (q n).2) atTop
            (𝓝 D.lowerHeight) := by
          simpa only [hpLower'] using hqp.snd_nhds
        exact D.tendsto_rightEndpoint_nhdsGT_lowerHeight_rightLim.comp
          (tendsto_nhdsWithin_iff.mpr ⟨hyTendsto, hyAbove⟩)
      have hLowerRightLeP : D.lowerRight ≤ p.1 :=
        le_of_tendsto_of_tendsto hEndpoint hqp.fst_nhds
          (hInterior.mono fun _ hn => hn.2)
      exact (not_le_of_gt hpSplit')
        (D.lowerSplit_le_lowerRight.trans hLowerRightLeP)
    exact Or.inl ⟨hpLower', hpSplit, hpSection.2⟩
  · rcases hpHeight.2.eq_or_lt with hpUpper | hpUpper
    · have hpSection : p.1 ∈ D.frontierSection D.upperHeight := by
        change (p.1, D.upperHeight) ∈ frontier (aeOpenRepresentative E)
        rwa [← hpUpper]
      rw [D.upper_frontierSection_eq_Icc_endpointLimits] at hpSection
      change p.1 ∈ Icc D.upperLeft D.upperRight at hpSection
      have hpSplit : D.upperSplit ≤ p.1 := by
        by_contra hle
        have hpSplit' : p.1 < D.upperSplit := lt_of_not_ge hle
        have hxEventually : ∀ᶠ n in atTop, (q n).1 < D.upperSplit :=
          hqp.fst_nhds (Iio_mem_nhds hpSplit')
        have hpAboveLower : D.lowerHeight < p.2 := by
          rw [hpUpper]
          exact D.lowerHeight_lt_upperHeight
        have hyEventually : ∀ᶠ n in atTop, D.lowerHeight < (q n).2 :=
          hqp.snd_nhds (Ioi_mem_nhds hpAboveLower)
        have hInterior : ∀ᶠ n in atTop,
            (q n).2 ∈ D.occupiedHeights ∧
              D.rightEndpoint (q n).2 ≤ (q n).1 := by
          filter_upwards [hxEventually, hyEventually] with n hxSplit hyLower
          rcases hq n with hLower | hMiddle | hUpper'
          · rw [hLower.1] at hyLower
            exact (lt_irrefl D.lowerHeight hyLower).elim
          · exact ⟨hMiddle.1,
              D.rightEndpoint_le_orientedRightSegment hMiddle.1 hMiddle.2⟩
          · exact (not_lt_of_ge hUpper'.2.1 hxSplit).elim
        have hyBelow : ∀ᶠ n in atTop, (q n).2 < D.upperHeight :=
          hInterior.mono fun n hn =>
            (D.mem_occupiedHeights_iff_height_bounds.mp hn.1).2
        have hEndpoint : Tendsto (fun n => D.rightEndpoint (q n).2) atTop
            (𝓝 D.upperRight) := by
          change Tendsto (fun n => D.rightEndpoint (q n).2) atTop
            (𝓝 (Function.leftLim D.rightEndpoint D.upperHeight))
          have hyTendsto : Tendsto (fun n => (q n).2) atTop
              (𝓝 D.upperHeight) := by
            simpa only [hpUpper] using hqp.snd_nhds
          exact D.tendsto_rightEndpoint_nhdsLT_upperHeight_leftLim.comp
            (tendsto_nhdsWithin_iff.mpr ⟨hyTendsto, hyBelow⟩)
        have hUpperRightLeP : D.upperRight ≤ p.1 :=
          le_of_tendsto_of_tendsto hEndpoint hqp.fst_nhds
            (hInterior.mono fun _ hn => hn.2)
        exact (not_le_of_gt hpSplit')
          (D.upperSplit_le_upperRight.trans hUpperRightLeP)
      exact Or.inr (Or.inr ⟨hpUpper, hpSplit, hpSection.2⟩)
    · have hpOccupied : p.2 ∈ D.occupiedHeights :=
        D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hpLower, hpUpper⟩
      have hyEventually : ∀ᶠ n in atTop, (q n).2 ∈ D.occupiedHeights := by
        have hyLower : ∀ᶠ n in atTop, D.lowerHeight < (q n).2 :=
          hqp.snd_nhds (Ioi_mem_nhds hpLower)
        have hyUpper : ∀ᶠ n in atTop, (q n).2 < D.upperHeight :=
          hqp.snd_nhds (Iio_mem_nhds hpUpper)
        filter_upwards [hyLower, hyUpper] with n hnLower hnUpper
        exact D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hnLower, hnUpper⟩
      have hInterior : ∀ᶠ n in atTop,
          D.rightEndpoint (q n).2 ≤ (q n).1 := by
        filter_upwards [hyEventually] with n hn
        rcases hq n with hLower | hMiddle | hUpper'
        · have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hn
          rw [hLower.1] at hbounds
          exact (lt_irrefl D.lowerHeight hbounds.1).elim
        · exact D.rightEndpoint_le_orientedRightSegment hMiddle.1 hMiddle.2
        · have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hn
          rw [hUpper'.1] at hbounds
          exact (lt_irrefl D.upperHeight hbounds.2).elim
      have hEndpointLeP : D.rightEndpoint p.2 ≤ p.1 := by
        by_contra hle
        have hpEndpoint : p.1 < D.rightEndpoint p.2 := lt_of_not_ge hle
        obtain ⟨t, hpT, htEndpoint⟩ := exists_between hpEndpoint
        have hxEventually : ∀ᶠ n in atTop, (q n).1 < t :=
          hqp.fst_nhds (Iio_mem_nhds hpT)
        have hEndpointEventually : ∀ᶠ n in atTop,
            t < D.rightEndpoint (q n).2 :=
          hqp.snd_nhds
            (D.lowerSemicontinuousAt_rightEndpoint hpOccupied t htEndpoint)
        obtain ⟨n, hnx, hnEndpoint, hnLe⟩ :=
          (hxEventually.and (hEndpointEventually.and hInterior)).exists
        exact ((hnEndpoint.trans_le hnLe).trans hnx).false
      have hpSection : p.1 ∈ D.frontierSection p.2 := hpFrontier
      rw [D.frontierSection_eq_orientedEndpointSegments hpOccupied] at hpSection
      rcases hpSection with hpLeft | hpRight
      · have hpLeLeft :=
          D.orientedLeftSegment_le_leftEndpoint hpOccupied hpLeft
        have hwrong : D.rightEndpoint p.2 ≤ D.leftEndpoint p.2 :=
          hEndpointLeP.trans hpLeLeft
        exact ((not_le_of_gt
          (D.leftEndpoint_lt_rightEndpoint hpOccupied)) hwrong).elim
      · exact Or.inr (Or.inl ⟨hpOccupied, hpRight⟩)

/-- The left completed boundary chain is compact. -/
theorem isCompact_leftCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    IsCompact D.leftCompletedChain :=
  D.produce.selected_bounded.isCompact_closure.of_isClosed_subset
    D.isClosed_leftCompletedChain
    (D.leftCompletedChain_subset_frontier.trans frontier_subset_closure)

/-- The right completed boundary chain is compact. -/
theorem isCompact_rightCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    IsCompact D.rightCompletedChain :=
  D.produce.selected_bounded.isCompact_closure.of_isClosed_subset
    D.isClosed_rightCompletedChain
    (D.rightCompletedChain_subset_frontier.trans frontier_subset_closure)

/-- Secondary traversal coordinate on a horizontal fiber of the left chain.
The lower extreme is traversed leftward, each interior jump is traversed from
its lower-side limit to its upper-side limit, and the upper extreme is
traversed rightward. -/
def leftOrderSecondary (D : SelectedBoundaryTopologyInput E U)
    (p : PlanePoint) : ℝ :=
  if p.2 = D.lowerHeight then -p.1
  else if p.2 = D.upperHeight then p.1
  else if Function.leftLim D.leftEndpoint p.2 ≤
      Function.rightLim D.leftEndpoint p.2 then p.1 else -p.1

/-- Secondary traversal coordinate on a horizontal fiber of the right chain.
Its extreme-fiber directions are complementary to those of the left chain. -/
def rightOrderSecondary (D : SelectedBoundaryTopologyInput E U)
    (p : PlanePoint) : ℝ :=
  if p.2 = D.lowerHeight then p.1
  else if p.2 = D.upperHeight then -p.1
  else if Function.leftLim D.rightEndpoint p.2 ≤
      Function.rightLim D.rightEndpoint p.2 then p.1 else -p.1

/-- Intrinsic height-first traversal coordinate for the left completed chain. -/
def leftOrderKey (D : SelectedBoundaryTopologyInput E U)
    (p : PlanePoint) : Lex (ℝ × ℝ) :=
  toLex (p.2, D.leftOrderSecondary p)

/-- Intrinsic height-first traversal coordinate for the right completed chain. -/
def rightOrderKey (D : SelectedBoundaryTopologyInput E U)
    (p : PlanePoint) : Lex (ℝ × ℝ) :=
  toLex (p.2, D.rightOrderSecondary p)

private theorem leftOrderKey_injective
    (D : SelectedBoundaryTopologyInput E U) :
    Function.Injective D.leftOrderKey := by
  intro p q hpq
  have hpq' : (p.2, D.leftOrderSecondary p) =
      (q.2, D.leftOrderSecondary q) := toLex.injective hpq
  have hy : p.2 = q.2 := congrArg Prod.fst hpq'
  have hxSecondary := congrArg Prod.snd hpq'
  dsimp only [leftOrderSecondary] at hxSecondary
  rw [← hy] at hxSecondary
  have hx : p.1 = q.1 := by
    split_ifs at hxSecondary <;> linarith
  exact Prod.ext hx hy

private theorem rightOrderKey_injective
    (D : SelectedBoundaryTopologyInput E U) :
    Function.Injective D.rightOrderKey := by
  intro p q hpq
  have hpq' : (p.2, D.rightOrderSecondary p) =
      (q.2, D.rightOrderSecondary q) := toLex.injective hpq
  have hy : p.2 = q.2 := congrArg Prod.fst hpq'
  have hxSecondary := congrArg Prod.snd hpq'
  dsimp only [rightOrderSecondary] at hxSecondary
  rw [← hy] at hxSecondary
  have hx : p.1 = q.1 := by
    split_ifs at hxSecondary <;> linarith
  exact Prod.ext hx hy

/-- The left chain's intrinsic linear order.  It is explicit rather than a
global instance because the planar subtype already carries an unrelated
coordinatewise order. -/
noncomputable abbrev leftCompletedChainLinearOrder
    (D : SelectedBoundaryTopologyInput E U) :
    LinearOrder D.leftCompletedChain :=
  LinearOrder.lift' (fun p => D.leftOrderKey p.1)
    (D.leftOrderKey_injective.comp Subtype.val_injective)

/-- The right chain's intrinsic linear order. -/
noncomputable abbrev rightCompletedChainLinearOrder
    (D : SelectedBoundaryTopologyInput E U) :
    LinearOrder D.rightCompletedChain :=
  LinearOrder.lift' (fun p => D.rightOrderKey p.1)
    (D.rightOrderKey_injective.comp Subtype.val_injective)

/-- Strictly increasing height is strictly increasing in the left traversal
order, independently of horizontal jump direction. -/
theorem leftCompletedChain_lt_of_snd_lt
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain) (h : p.1.2 < q.1.2) :
    @LT.lt _ D.leftCompletedChainLinearOrder.toLT p q := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- Strictly increasing height is strictly increasing in the right traversal
order, independently of horizontal jump direction. -/
theorem rightCompletedChain_lt_of_snd_lt
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.rightCompletedChain) (h : p.1.2 < q.1.2) :
    @LT.lt _ D.rightCompletedChainLinearOrder.toLT p q := by
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

/-- On an upward-oriented interior left jump, increasing abscissa is
increasing in the left traversal order. -/
theorem leftCompletedChain_lt_of_same_snd_of_forward
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain)
    (hy : p.1.2 = q.1.2) (hoccupied : p.1.2 ∈ D.occupiedHeights)
    (horiented : Function.leftLim D.leftEndpoint p.1.2 ≤
      Function.rightLim D.leftEndpoint p.1.2)
    (hx : p.1.1 < q.1.1) :
    @LT.lt _ D.leftCompletedChainLinearOrder.toLT p q := by
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hy, ?_⟩
  have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hoccupied
  have hlower : p.1.2 ≠ D.lowerHeight := hbounds.1.ne'
  have hupper : p.1.2 ≠ D.upperHeight := hbounds.2.ne
  rw [leftOrderSecondary, leftOrderSecondary]
  rw [← hy]
  simp only [hlower, hupper, if_false, horiented, if_true]
  exact hx

/-- On a downward-oriented interior left jump, decreasing abscissa is
increasing in the left traversal order. -/
theorem leftCompletedChain_lt_of_same_snd_of_backward
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain)
    (hy : p.1.2 = q.1.2) (hoccupied : p.1.2 ∈ D.occupiedHeights)
    (horiented : ¬ Function.leftLim D.leftEndpoint p.1.2 ≤
      Function.rightLim D.leftEndpoint p.1.2)
    (hx : q.1.1 < p.1.1) :
    @LT.lt _ D.leftCompletedChainLinearOrder.toLT p q := by
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hy, ?_⟩
  have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hoccupied
  have hlower : p.1.2 ≠ D.lowerHeight := hbounds.1.ne'
  have hupper : p.1.2 ≠ D.upperHeight := hbounds.2.ne
  rw [leftOrderSecondary, leftOrderSecondary]
  rw [← hy]
  simp only [hlower, hupper, if_false, horiented]
  linarith

/-- On an upward-oriented interior right jump, increasing abscissa is
increasing in the right traversal order. -/
theorem rightCompletedChain_lt_of_same_snd_of_forward
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.rightCompletedChain)
    (hy : p.1.2 = q.1.2) (hoccupied : p.1.2 ∈ D.occupiedHeights)
    (horiented : Function.leftLim D.rightEndpoint p.1.2 ≤
      Function.rightLim D.rightEndpoint p.1.2)
    (hx : p.1.1 < q.1.1) :
    @LT.lt _ D.rightCompletedChainLinearOrder.toLT p q := by
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hy, ?_⟩
  have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hoccupied
  have hlower : p.1.2 ≠ D.lowerHeight := hbounds.1.ne'
  have hupper : p.1.2 ≠ D.upperHeight := hbounds.2.ne
  rw [rightOrderSecondary, rightOrderSecondary]
  rw [← hy]
  simp only [hlower, hupper, if_false, horiented, if_true]
  exact hx

/-- On a downward-oriented interior right jump, decreasing abscissa is
increasing in the right traversal order. -/
theorem rightCompletedChain_lt_of_same_snd_of_backward
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.rightCompletedChain)
    (hy : p.1.2 = q.1.2) (hoccupied : p.1.2 ∈ D.occupiedHeights)
    (horiented : ¬ Function.leftLim D.rightEndpoint p.1.2 ≤
      Function.rightLim D.rightEndpoint p.1.2)
    (hx : q.1.1 < p.1.1) :
    @LT.lt _ D.rightCompletedChainLinearOrder.toLT p q := by
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  refine ⟨hy, ?_⟩
  have hbounds := D.mem_occupiedHeights_iff_height_bounds.mp hoccupied
  have hlower : p.1.2 ≠ D.lowerHeight := hbounds.1.ne'
  have hupper : p.1.2 ≠ D.upperHeight := hbounds.2.ne
  rw [rightOrderSecondary, rightOrderSecondary]
  rw [← hy]
  simp only [hlower, hupper, if_false, horiented]
  linarith

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
