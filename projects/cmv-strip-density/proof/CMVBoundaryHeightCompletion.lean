/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryLocalAtlas

/-!
# Height support and actual section endpoints

This module starts from the unchanged `SelectedBoundaryTopologyInput`.  It
identifies the occupied heights of the selected representative as one bounded
open interval, defines every nonempty section by its own infimum and supremum,
and places those two actual endpoints on the complete planar frontier.  No
continuity, one-sided limit, finite-jump, boundary order, or global trace is
assumed here.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

open Function Topology
open CMVSourceClassification

private theorem isConnected_of_isOpenQuotientMap_restrict
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {S : Set X}
    (hq : IsOpenQuotientMap
      ((mapsTo_image f S).restrict f S (f '' S)))
    (himage : IsConnected (f '' S))
    (hfiber : ∀ y ∈ f '' S, IsConnected (S ∩ f ⁻¹' {y})) :
    IsConnected S := by
  let g : S → (f '' S) :=
    (mapsTo_image f S).restrict f S (f '' S)
  have hg : IsOpenQuotientMap g := hq
  have hgfiber : ∀ y : (f '' S), IsConnected (g ⁻¹' {y}) := by
    intro y
    let F : ↥(S ∩ f ⁻¹' {(y : Y)}) → S :=
      fun x => ⟨x.1, x.2.1⟩
    have hF : Continuous F :=
      continuous_subtype_val.subtype_mk (fun x => x.2.1)
    let _ : ConnectedSpace ↥(S ∩ f ⁻¹' {(y : Y)}) :=
      Subtype.connectedSpace (hfiber y y.2)
    have hRange : IsConnected (Set.range F) := isConnected_range hF
    convert hRange using 1
    ext x
    constructor
    · intro hx
      refine ⟨⟨x.1, ⟨x.2, Set.mem_singleton_iff.mpr ?_⟩⟩, ?_⟩
      · exact congrArg Subtype.val hx
      · exact Subtype.ext (by rfl)
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp a.2.2
  let _ : ConnectedSpace ↥(f '' S) := Subtype.connectedSpace himage
  have hDomain : IsConnected (Set.univ : Set S) := by
    simpa using
      hg.isQuotientMap.isCoinducing.isConnected_preimage_of_isClosed
        hgfiber isClosed_univ
        (isConnected_univ : IsConnected (Set.univ : Set (f '' S)))
  exact isConnected_iff_connectedSpace.mpr
    (connectedSpace_iff_univ.mpr hDomain)

/-- An open planar set remains connected after restriction to a horizontal
strip when all horizontal sections are intervals and the occupied heights in
the strip form one nonempty interval. -/
theorem isConnected_open_horizontal_strip_of_ordConnected_sections
    {O : Set PlanePoint} {a b c d : ℝ}
    (hO : IsOpen O)
    (hsections : ∀ y : ℝ, (horizontalSection O y).OrdConnected)
    (hoccupied : Prod.snd '' O ∩ Ioo a b = Ioo c d)
    (hcd : c < d) :
    IsConnected (O ∩ Prod.snd ⁻¹' Ioo a b) := by
  let S : Set PlanePoint := O ∩ Prod.snd ⁻¹' Ioo a b
  have hSopen : IsOpen S :=
    hO.inter (isOpen_Ioo.preimage continuous_snd)
  let g : S → (Prod.snd '' S) :=
    (mapsTo_image Prod.snd S).restrict Prod.snd S (Prod.snd '' S)
  have hg : IsOpenQuotientMap g := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
    · exact continuous_snd.continuousOn.mapsToRestrict
        (mapsTo_image Prod.snd S)
    · exact (isOpenMap_snd.domRestrict hSopen).codRestrict _
  have himage : IsConnected (Prod.snd '' S) := by
    rw [show Prod.snd '' S = Prod.snd '' O ∩ Ioo a b by
      simpa [S] using image_inter_preimage Prod.snd O (Ioo a b)]
    rw [hoccupied]
    exact isConnected_Ioo hcd
  apply isConnected_of_isOpenQuotientMap_restrict hg himage
  intro y hy
  obtain ⟨p, hpS, hpY⟩ := hy
  have hyIoo : y ∈ Ioo a b := by
    rw [← hpY]
    exact hpS.2
  have hsectionNonempty : (horizontalSection O y).Nonempty := by
    refine ⟨p.1, ?_⟩
    change (p.1, y) ∈ O
    rw [← hpY]
    exact hpS.1
  have hsectionConnected : IsConnected (horizontalSection O y) :=
    ⟨hsectionNonempty, (hsections y).isPreconnected⟩
  have hsectionImageConnected :
      IsConnected ((fun x : ℝ => (x, y)) '' horizontalSection O y) :=
    hsectionConnected.image (fun x : ℝ => (x, y))
      (continuous_id.prodMk continuous_const).continuousOn
  convert hsectionImageConnected using 1
  ext q
  constructor
  · rintro ⟨hqS, hqy⟩
    have hqY : q.2 = y := Set.mem_singleton_iff.mp hqy
    refine ⟨q.1, ?_, ?_⟩
    · change (q.1, y) ∈ O
      rw [← hqY]
      exact hqS.1
    · exact Prod.ext rfl hqY.symm
  · rintro ⟨x, hxO, rfl⟩
    exact ⟨⟨hxO, hyIoo⟩, Set.mem_singleton_iff.mpr rfl⟩

/-- A decreasing intersection of nonempty compact connected sets remains
connected. -/
theorem isConnected_iInter_of_antitone
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (K : ℕ → Set X) (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hconnected : ∀ n, IsConnected (K n)) :
    IsConnected (⋂ n, K n) := by
  let I : Set X := ⋂ n, K n
  have hclosed : ∀ n, IsClosed (K n) :=
    fun n => (hcompact n).isClosed
  have hIclosed : IsClosed I := isClosed_iInter hclosed
  have hIcompact : IsCompact I :=
    (hcompact 0).of_isClosed_subset hIclosed (iInter_subset K 0)
  have hInonempty : I.Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
      (fun n => hanti (Nat.le_succ n))
      (fun n => (hconnected n).nonempty) (hcompact 0) hclosed
  refine ⟨hInonempty, ?_⟩
  rintro u v hu hv hIuv hIu hIv
  by_contra hIinter
  let A : Set X := I \ v
  let B : Set X := I \ u
  have hAcompact : IsCompact A := hIcompact.diff hv
  have hBcompact : IsCompact B := hIcompact.diff hu
  have hBclosed : IsClosed B := hIclosed.sdiff hu
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact (hIuv hxA.1).elim hxB.2 hxA.2
  obtain ⟨W, V, hW, hV, hAW, hBV, hWV⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed
      hAcompact hBcompact hBclosed hAB
  have hAI : A.Nonempty := by
    rcases hIu with ⟨x, hxI, hxu⟩
    refine ⟨x, hxI, ?_⟩
    intro hxv
    exact hIinter ⟨x, hxI, hxu, hxv⟩
  have hBI : B.Nonempty := by
    rcases hIv with ⟨x, hxI, hxv⟩
    refine ⟨x, hxI, ?_⟩
    intro hxu
    exact hIinter ⟨x, hxI, hxu, hxv⟩
  have hIWV : I ⊆ W ∪ V := by
    intro x hxI
    rcases hIuv hxI with hxu | hxv
    · exact Or.inl (hAW ⟨hxI,
        fun hxv => hIinter ⟨x, hxI, hxu, hxv⟩⟩)
    · exact Or.inr (hBV ⟨hxI,
        fun hxu => hIinter ⟨x, hxI, hxu, hxv⟩⟩)
  have hEventually : ∃ n, K n ⊆ W ∪ V := by
    by_contra h
    push Not at h
    let C : ℕ → Set X := fun n => K n ∩ (W ∪ V)ᶜ
    have hCnonempty : ∀ n, (C n).Nonempty := by
      intro n
      rcases Set.not_subset.mp (h n) with ⟨x, hxK, hxWV⟩
      exact ⟨x, hxK, hxWV⟩
    have hCclosed : ∀ n, IsClosed (C n) :=
      fun n => (hclosed n).inter (hW.union hV).isClosed_compl
    have hC0compact : IsCompact (C 0) :=
      (hcompact 0).inter_right (hW.union hV).isClosed_compl
    have hCanti : ∀ n, C (n + 1) ⊆ C n := by
      intro n x hx
      exact ⟨hanti (Nat.le_succ n) hx.1, hx.2⟩
    rcases
        IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
          C hCanti hCnonempty hC0compact hCclosed with ⟨x, hxC⟩
    have hxI : x ∈ I := by
      apply mem_iInter.2
      intro m
      exact ((mem_iInter.mp hxC) m).1
    exact (mem_iInter.mp hxC 0).2 (hIWV hxI)
  rcases hEventually with ⟨n, hn⟩
  rcases (hconnected n).isPreconnected.subset_or_subset
      hW hV hWV hn with hnW | hnV
  · rcases hBI with ⟨x, hxI, hxB⟩
    exact Set.disjoint_left.mp hWV
      (hnW (iInter_subset K n hxI)) (hBV ⟨hxI, hxB⟩)
  · rcases hAI with ⟨x, hxI, hxA⟩
    exact Set.disjoint_left.mp hWV
      (hAW ⟨hxI, hxA⟩) (hnV (iInter_subset K n hxI))

namespace SelectedBoundaryTopologyInput

open CMVRelaxation
open CMVSourceClassification

variable {E U : Set PlanePoint}

/-- Heights of the nonempty horizontal sections of the selected representative. -/
def occupiedHeights (_D : SelectedBoundaryTopologyInput E U) : Set ℝ :=
  Prod.snd '' aeOpenRepresentative E

/-- Lower endpoint of the occupied-height interval. -/
def lowerHeight (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  sInf D.occupiedHeights

/-- Upper endpoint of the occupied-height interval. -/
def upperHeight (D : SelectedBoundaryTopologyInput E U) : ℝ :=
  sSup D.occupiedHeights

/-- The actual left endpoint of the selected horizontal section.  Its geometric
properties are used only at occupied heights. -/
def leftEndpoint (_D : SelectedBoundaryTopologyInput E U) (y : ℝ) : ℝ :=
  sInf (horizontalSection (aeOpenRepresentative E) y)

/-- The actual right endpoint of the selected horizontal section. -/
def rightEndpoint (_D : SelectedBoundaryTopologyInput E U) (y : ℝ) : ℝ :=
  sSup (horizontalSection (aeOpenRepresentative E) y)

/-- Horizontal slice of the complete selected frontier. -/
def frontierSection (_D : SelectedBoundaryTopologyInput E U) (y : ℝ) : Set ℝ :=
  {x | (x, y) ∈ frontier (aeOpenRepresentative E)}

@[simp] theorem mem_occupiedHeights_iff
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ} :
    y ∈ D.occupiedHeights ↔
      (horizontalSection (aeOpenRepresentative E) y).Nonempty := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp⟩
  · rintro ⟨x, hx⟩
    exact ⟨(x, y), hx, rfl⟩

@[simp] theorem mem_frontierSection_iff
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ} :
    x ∈ D.frontierSection y ↔
      (x, y) ∈ frontier (aeOpenRepresentative E) :=
  Iff.rfl

/-- The occupied-height set is nonempty. -/
theorem occupiedHeights_nonempty (D : SelectedBoundaryTopologyInput E U) :
    D.occupiedHeights.Nonempty :=
  D.produce.selected_nonempty.image Prod.snd

/-- Projection along horizontal lines preserves openness. -/
theorem isOpen_occupiedHeights (D : SelectedBoundaryTopologyInput E U) :
    IsOpen D.occupiedHeights :=
  isOpenMap_snd _ D.produce.selected_open

/-- Boundedness of the selected representative uniformly bounds its occupied
heights. -/
theorem isBounded_occupiedHeights (D : SelectedBoundaryTopologyInput E U) :
    Bornology.IsBounded D.occupiedHeights :=
  D.produce.selected_bounded.image_snd

/-- Connectedness of the selected representative makes its occupied-height
projection connected. -/
theorem isConnected_occupiedHeights (D : SelectedBoundaryTopologyInput E U) :
    IsConnected D.occupiedHeights :=
  D.produce.selected_connected.image Prod.snd continuous_snd.continuousOn

/-- The occupied heights are exactly one open interval with intrinsic
endpoints. -/
theorem occupiedHeights_eq_Ioo (D : SelectedBoundaryTopologyInput E U) :
    D.occupiedHeights = Ioo D.lowerHeight D.upperHeight := by
  exact CMVRelaxation.IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
    D.isOpen_occupiedHeights D.occupiedHeights_nonempty
    D.isBounded_occupiedHeights
    D.isConnected_occupiedHeights.isPreconnected.ordConnected

/-- The two intrinsic extreme heights are strictly ordered. -/
theorem lowerHeight_lt_upperHeight (D : SelectedBoundaryTopologyInput E U) :
    D.lowerHeight < D.upperHeight := by
  obtain ⟨y, hy⟩ := D.occupiedHeights_nonempty
  rw [D.occupiedHeights_eq_Ioo] at hy
  exact hy.1.trans hy.2

@[simp] theorem mem_occupiedHeights_iff_height_bounds
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ} :
    y ∈ D.occupiedHeights ↔ D.lowerHeight < y ∧ y < D.upperHeight := by
  rw [D.occupiedHeights_eq_Ioo]
  rfl

/-- Portion of the selected representative strictly between its lower extreme
height and an occupied cutoff. -/
def lowerBand (D : SelectedBoundaryTopologyInput E U) (t : ℝ) :
    Set PlanePoint :=
  aeOpenRepresentative E ∩ Prod.snd ⁻¹' Ioo D.lowerHeight t

/-- Portion of the selected representative strictly between an occupied
cutoff and its upper extreme height. -/
def upperBand (D : SelectedBoundaryTopologyInput E U) (t : ℝ) :
    Set PlanePoint :=
  aeOpenRepresentative E ∩ Prod.snd ⁻¹' Ioo t D.upperHeight

/-- Canonical occupied cutoffs decreasing to the lower extreme height. -/
def lowerCutoff (D : SelectedBoundaryTopologyInput E U) (n : ℕ) : ℝ :=
  D.lowerHeight +
    (D.upperHeight - D.lowerHeight) / ((n : ℝ) + 2)

/-- Canonical occupied cutoffs increasing to the upper extreme height. -/
def upperCutoff (D : SelectedBoundaryTopologyInput E U) (n : ℕ) : ℝ :=
  D.upperHeight -
    (D.upperHeight - D.lowerHeight) / ((n : ℝ) + 2)

/-- Compact connected lower truncations used to recover the completed bottom
frontier as a nested intersection. -/
def lowerClosedBand (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    Set PlanePoint :=
  closure (D.lowerBand (D.lowerCutoff n))

/-- Compact connected upper truncations used to recover the completed top
frontier as a nested intersection. -/
def upperClosedBand (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    Set PlanePoint :=
  closure (D.upperBand (D.upperCutoff n))

/-- Every lower truncation at an occupied height remains connected.  This is
derived from projection openness and connected interval fibers, not assumed
from a global boundary trace. -/
theorem isConnected_lowerBand
    (D : SelectedBoundaryTopologyInput E U) {t : ℝ}
    (ht : t ∈ D.occupiedHeights) :
    IsConnected (D.lowerBand t) := by
  have htBounds := D.mem_occupiedHeights_iff_height_bounds.mp ht
  have hsections : ∀ y : ℝ,
      (horizontalSection (aeOpenRepresentative E) y).OrdConnected :=
    fun y => ordConnected_horizontalSection_aeOpenRepresentative
      D.representative_open D.carrier_ae D.interval_sections y
  unfold lowerBand
  apply isConnected_open_horizontal_strip_of_ordConnected_sections
    D.produce.selected_open hsections
  · change D.occupiedHeights ∩ Ioo D.lowerHeight t =
      Ioo D.lowerHeight t
    rw [D.occupiedHeights_eq_Ioo]
    ext y
    constructor
    · exact fun hy => hy.2
    · intro hy
      exact ⟨⟨hy.1, hy.2.trans htBounds.2⟩, hy⟩
  · exact htBounds.1

/-- Every upper truncation at an occupied height remains connected. -/
theorem isConnected_upperBand
    (D : SelectedBoundaryTopologyInput E U) {t : ℝ}
    (ht : t ∈ D.occupiedHeights) :
    IsConnected (D.upperBand t) := by
  have htBounds := D.mem_occupiedHeights_iff_height_bounds.mp ht
  have hsections : ∀ y : ℝ,
      (horizontalSection (aeOpenRepresentative E) y).OrdConnected :=
    fun y => ordConnected_horizontalSection_aeOpenRepresentative
      D.representative_open D.carrier_ae D.interval_sections y
  unfold upperBand
  apply isConnected_open_horizontal_strip_of_ordConnected_sections
    D.produce.selected_open hsections
  · change D.occupiedHeights ∩ Ioo t D.upperHeight =
      Ioo t D.upperHeight
    rw [D.occupiedHeights_eq_Ioo]
    ext y
    constructor
    · exact fun hy => hy.2
    · intro hy
      exact ⟨⟨htBounds.1.trans hy.1, hy.2⟩, hy⟩
  · exact htBounds.2

theorem lowerCutoff_mem_occupiedHeights
    (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    D.lowerCutoff n ∈ D.occupiedHeights := by
  rw [D.mem_occupiedHeights_iff_height_bounds]
  have hgap : 0 < D.upperHeight - D.lowerHeight :=
    sub_pos.mpr D.lowerHeight_lt_upperHeight
  have hden0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hden1 : (1 : ℝ) < (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hpos := div_pos hgap hden0
  have hlt := div_lt_self hgap hden1
  unfold lowerCutoff
  constructor <;> linarith

theorem upperCutoff_mem_occupiedHeights
    (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    D.upperCutoff n ∈ D.occupiedHeights := by
  rw [D.mem_occupiedHeights_iff_height_bounds]
  have hgap : 0 < D.upperHeight - D.lowerHeight :=
    sub_pos.mpr D.lowerHeight_lt_upperHeight
  have hden0 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hden1 : (1 : ℝ) < (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hpos := div_pos hgap hden0
  have hlt := div_lt_self hgap hden1
  unfold upperCutoff
  constructor <;> linarith

theorem antitone_lowerCutoff
    (D : SelectedBoundaryTopologyInput E U) :
    Antitone D.lowerCutoff := by
  intro m n hmn
  unfold lowerCutoff
  have hgap : 0 ≤ D.upperHeight - D.lowerHeight :=
    (sub_pos.mpr D.lowerHeight_lt_upperHeight).le
  have hden : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    simpa using (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ))
  simpa [add_comm] using add_le_add_left
    (div_le_div_of_nonneg_left hgap (by positivity) hden) D.lowerHeight

theorem monotone_upperCutoff
    (D : SelectedBoundaryTopologyInput E U) :
    Monotone D.upperCutoff := by
  intro m n hmn
  unfold upperCutoff
  have hgap : 0 ≤ D.upperHeight - D.lowerHeight :=
    (sub_pos.mpr D.lowerHeight_lt_upperHeight).le
  have hden : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    simpa using (Nat.cast_le.mpr hmn : (m : ℝ) ≤ (n : ℝ))
  exact sub_le_sub_left
    (div_le_div_of_nonneg_left hgap (by positivity) hden) _

theorem tendsto_lowerCutoff
    (D : SelectedBoundaryTopologyInput E U) :
    Tendsto D.lowerCutoff atTop (𝓝 D.lowerHeight) := by
  change Tendsto (fun n : ℕ => D.lowerHeight +
    (D.upperHeight - D.lowerHeight) / ((n : ℝ) + 2)) atTop
      (𝓝 D.lowerHeight)
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hquot :=
    hden.const_div_atTop (D.upperHeight - D.lowerHeight)
  simpa using hquot.const_add D.lowerHeight

theorem tendsto_upperCutoff
    (D : SelectedBoundaryTopologyInput E U) :
    Tendsto D.upperCutoff atTop (𝓝 D.upperHeight) := by
  change Tendsto (fun n : ℕ => D.upperHeight -
    (D.upperHeight - D.lowerHeight) / ((n : ℝ) + 2)) atTop
      (𝓝 D.upperHeight)
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hquot :=
    hden.const_div_atTop (D.upperHeight - D.lowerHeight)
  simpa using hquot.const_sub D.upperHeight

theorem isCompact_lowerClosedBand
    (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    IsCompact (D.lowerClosedBand n) := by
  unfold lowerClosedBand
  exact
    (D.produce.selected_bounded.subset inter_subset_left).isCompact_closure

theorem isConnected_lowerClosedBand
    (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    IsConnected (D.lowerClosedBand n) := by
  unfold lowerClosedBand
  exact
    (D.isConnected_lowerBand
      (D.lowerCutoff_mem_occupiedHeights n)).closure

theorem antitone_lowerClosedBand
    (D : SelectedBoundaryTopologyInput E U) :
    Antitone D.lowerClosedBand := by
  intro m n hmn
  apply closure_mono
  rintro p ⟨hpO, hpLow, hpCut⟩
  exact
    ⟨hpO, hpLow, hpCut.trans_le (D.antitone_lowerCutoff hmn)⟩

theorem isCompact_upperClosedBand
    (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    IsCompact (D.upperClosedBand n) := by
  unfold upperClosedBand
  exact
    (D.produce.selected_bounded.subset inter_subset_left).isCompact_closure

theorem isConnected_upperClosedBand
    (D : SelectedBoundaryTopologyInput E U) (n : ℕ) :
    IsConnected (D.upperClosedBand n) := by
  unfold upperClosedBand
  exact
    (D.isConnected_upperBand
      (D.upperCutoff_mem_occupiedHeights n)).closure

theorem antitone_upperClosedBand
    (D : SelectedBoundaryTopologyInput E U) :
    Antitone D.upperClosedBand := by
  intro m n hmn
  apply closure_mono
  rintro p ⟨hpO, hpCut, hpHigh⟩
  exact
    ⟨hpO, (D.monotone_upperCutoff hmn).trans_lt hpCut, hpHigh⟩

/-- The nested lower truncations complete exactly to the bottom planar
frontier slice. -/
theorem iInter_lowerClosedBand
    (D : SelectedBoundaryTopologyInput E U) :
    ⋂ n, D.lowerClosedBand n =
      frontier (aeOpenRepresentative E) ∩
        Prod.snd ⁻¹' ({D.lowerHeight} : Set ℝ) := by
  let O : Set PlanePoint := aeOpenRepresentative E
  ext p
  constructor
  · intro hp
    have hpK : ∀ n, p ∈ D.lowerClosedBand n := mem_iInter.mp hp
    have hpClosure : p ∈ closure O :=
      closure_mono inter_subset_left (hpK 0)
    have hpSlab : ∀ n,
        p ∈ Prod.snd ⁻¹' Icc D.lowerHeight (D.lowerCutoff n) := by
      intro n
      apply closure_minimal _
        (isClosed_Icc.preimage continuous_snd) (hpK n)
      rintro q ⟨hqO, hqLow, hqCut⟩
      exact ⟨hqLow.le, hqCut.le⟩
    have hpLower : D.lowerHeight ≤ p.2 := (hpSlab 0).1
    have hpUpper : p.2 ≤ D.lowerHeight := by
      by_contra h
      have hlt : D.lowerHeight < p.2 := lt_of_not_ge h
      have hevent : ∀ᶠ n in atTop, D.lowerCutoff n < p.2 :=
        (tendsto_order.mp D.tendsto_lowerCutoff).2 p.2 hlt
      rcases hevent.exists with ⟨n, hn⟩
      exact (not_lt_of_ge (hpSlab n).2) hn
    have hpHeight : p.2 = D.lowerHeight :=
      le_antisymm hpUpper hpLower
    have hpNotO : p ∉ O := by
      intro hpO
      have hy : p.2 ∈ D.occupiedHeights := ⟨p, hpO, rfl⟩
      have hlt :=
        (D.mem_occupiedHeights_iff_height_bounds.mp hy).1
      linarith
    refine ⟨?_, Set.mem_singleton_iff.mpr hpHeight⟩
    rw [D.produce.selected_open.frontier_eq]
    exact ⟨hpClosure, hpNotO⟩
  · rintro ⟨hpFrontier, hpHeight⟩
    have hpHeight' : p.2 = D.lowerHeight :=
      Set.mem_singleton_iff.mp hpHeight
    have hpClosure : p ∈ closure O :=
      frontier_subset_closure hpFrontier
    apply mem_iInter.2
    intro n
    apply _root_.mem_closure_iff.2
    intro V hV hpV
    let W : Set PlanePoint :=
      V ∩ Prod.snd ⁻¹' Iio (D.lowerCutoff n)
    have hW : IsOpen W :=
      hV.inter (isOpen_Iio.preimage continuous_snd)
    have hpW : p ∈ W := by
      refine ⟨hpV, ?_⟩
      change p.2 < D.lowerCutoff n
      rw [hpHeight']
      exact (D.mem_occupiedHeights_iff_height_bounds.mp
        (D.lowerCutoff_mem_occupiedHeights n)).1
    rcases (_root_.mem_closure_iff.mp hpClosure W hW hpW) with
      ⟨q, hqW, hqO⟩
    have hqOccupied : q.2 ∈ D.occupiedHeights :=
      ⟨q, hqO, rfl⟩
    exact ⟨q, hqW.1, hqO,
      (D.mem_occupiedHeights_iff_height_bounds.mp hqOccupied).1,
      hqW.2⟩

/-- The nested upper truncations complete exactly to the top planar frontier
slice. -/
theorem iInter_upperClosedBand
    (D : SelectedBoundaryTopologyInput E U) :
    ⋂ n, D.upperClosedBand n =
      frontier (aeOpenRepresentative E) ∩
        Prod.snd ⁻¹' ({D.upperHeight} : Set ℝ) := by
  let O : Set PlanePoint := aeOpenRepresentative E
  ext p
  constructor
  · intro hp
    have hpK : ∀ n, p ∈ D.upperClosedBand n := mem_iInter.mp hp
    have hpClosure : p ∈ closure O :=
      closure_mono inter_subset_left (hpK 0)
    have hpSlab : ∀ n,
        p ∈ Prod.snd ⁻¹' Icc (D.upperCutoff n) D.upperHeight := by
      intro n
      apply closure_minimal _
        (isClosed_Icc.preimage continuous_snd) (hpK n)
      rintro q ⟨hqO, hqCut, hqHigh⟩
      exact ⟨hqCut.le, hqHigh.le⟩
    have hpUpper : p.2 ≤ D.upperHeight := (hpSlab 0).2
    have hpLower : D.upperHeight ≤ p.2 := by
      by_contra h
      have hlt : p.2 < D.upperHeight := lt_of_not_ge h
      have hevent : ∀ᶠ n in atTop, p.2 < D.upperCutoff n :=
        (tendsto_order.mp D.tendsto_upperCutoff).1 p.2 hlt
      rcases hevent.exists with ⟨n, hn⟩
      exact (not_lt_of_ge (hpSlab n).1) hn
    have hpHeight : p.2 = D.upperHeight :=
      le_antisymm hpUpper hpLower
    have hpNotO : p ∉ O := by
      intro hpO
      have hy : p.2 ∈ D.occupiedHeights := ⟨p, hpO, rfl⟩
      have hlt :=
        (D.mem_occupiedHeights_iff_height_bounds.mp hy).2
      linarith
    refine ⟨?_, Set.mem_singleton_iff.mpr hpHeight⟩
    rw [D.produce.selected_open.frontier_eq]
    exact ⟨hpClosure, hpNotO⟩
  · rintro ⟨hpFrontier, hpHeight⟩
    have hpHeight' : p.2 = D.upperHeight :=
      Set.mem_singleton_iff.mp hpHeight
    have hpClosure : p ∈ closure O :=
      frontier_subset_closure hpFrontier
    apply mem_iInter.2
    intro n
    apply _root_.mem_closure_iff.2
    intro V hV hpV
    let W : Set PlanePoint :=
      V ∩ Prod.snd ⁻¹' Ioi (D.upperCutoff n)
    have hW : IsOpen W :=
      hV.inter (isOpen_Ioi.preimage continuous_snd)
    have hpW : p ∈ W := by
      refine ⟨hpV, ?_⟩
      change D.upperCutoff n < p.2
      rw [hpHeight']
      exact (D.mem_occupiedHeights_iff_height_bounds.mp
        (D.upperCutoff_mem_occupiedHeights n)).2
    rcases (_root_.mem_closure_iff.mp hpClosure W hW hpW) with
      ⟨q, hqW, hqO⟩
    have hqOccupied : q.2 ∈ D.occupiedHeights :=
      ⟨q, hqO, rfl⟩
    exact ⟨q, hqW.1, hqO, hqW.2,
      (D.mem_occupiedHeights_iff_height_bounds.mp hqOccupied).2⟩

/-- At every occupied height, the section's intrinsic endpoints are strictly
ordered. -/
theorem leftEndpoint_lt_rightEndpoint
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    D.leftEndpoint y < D.rightEndpoint y := by
  exact (horizontalSection_eq_Ioo_selfEndpoints_aeOpenRepresentative
    D.representative_open D.carrier_ae D.representative_bounded
    D.interval_sections y (D.mem_occupiedHeights_iff.mp hy)).1

/-- Every occupied section is exactly the open interval between its actual
infimum and supremum. -/
theorem horizontalSection_eq_Ioo_endpoints
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    horizontalSection (aeOpenRepresentative E) y =
      Ioo (D.leftEndpoint y) (D.rightEndpoint y) := by
  exact (horizontalSection_eq_Ioo_selfEndpoints_aeOpenRepresentative
    D.representative_open D.carrier_ae D.representative_bounded
    D.interval_sections y (D.mem_occupiedHeights_iff.mp hy)).2

/-- The intrinsic left section endpoint is an actual point of the complete
planar frontier. -/
theorem leftEndpoint_mem_frontier
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    (D.leftEndpoint y, y) ∈ frontier (aeOpenRepresentative E) := by
  apply frontier_horizontalSection_subset
  rw [D.horizontalSection_eq_Ioo_endpoints hy,
    frontier_Ioo (D.leftEndpoint_lt_rightEndpoint hy)]
  simp

/-- The intrinsic right section endpoint is an actual point of the complete
planar frontier. -/
theorem rightEndpoint_mem_frontier
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    (D.rightEndpoint y, y) ∈ frontier (aeOpenRepresentative E) := by
  apply frontier_horizontalSection_subset
  rw [D.horizontalSection_eq_Ioo_endpoints hy,
    frontier_Ioo (D.leftEndpoint_lt_rightEndpoint hy)]
  simp

/-- At an occupied height, no additional frontier point can lie inside the
actual open section.  Any horizontal jump contribution is therefore confined
to the two exterior sides of the endpoint pair. -/
theorem frontierSection_subset_endpoint_exteriors
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    D.frontierSection y ⊆
      Iic (D.leftEndpoint y) ∪ Ici (D.rightEndpoint y) := by
  intro x hx
  by_cases hleft : x ≤ D.leftEndpoint y
  · exact Or.inl hleft
  by_cases hright : D.rightEndpoint y ≤ x
  · exact Or.inr hright
  exfalso
  have hxCarrier :
      x ∈ horizontalSection (aeOpenRepresentative E) y := by
    rw [D.horizontalSection_eq_Ioo_endpoints hy]
    exact ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
  have hxNotCarrier : (x, y) ∉ aeOpenRepresentative E := by
    change (x, y) ∈ frontier (aeOpenRepresentative E) at hx
    rw [D.produce.selected_open.frontier_eq] at hx
    exact hx.2
  exact hxNotCarrier hxCarrier

/-- Any actual interior point of one section remains in the same horizontal
coordinate on all sufficiently nearby sections. -/
theorem eventually_mem_horizontalSection_of_mem
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ}
    (hxy : x ∈ horizontalSection (aeOpenRepresentative E) y) :
    ∀ᶠ z in 𝓝 y,
      x ∈ horizontalSection (aeOpenRepresentative E) z := by
  exact (D.produce.selected_open.preimage
    (continuous_const.prodMk continuous_id)).mem_nhds hxy

/-- A fixed interior core point gives simultaneous strict local bounds on both
actual endpoint functions. -/
theorem eventually_endpoints_straddle_of_mem
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ}
    (hxy : x ∈ horizontalSection (aeOpenRepresentative E) y) :
    ∀ᶠ z in 𝓝 y, D.leftEndpoint z < x ∧ x < D.rightEndpoint z := by
  filter_upwards [D.eventually_mem_horizontalSection_of_mem hxy] with z hxz
  have hz : z ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff.mpr ⟨x, hxz⟩
  rw [D.horizontalSection_eq_Ioo_endpoints hz] at hxz
  exact hxz

/-- Openness of the selected carrier makes the actual left endpoint upper
semicontinuous at every occupied height. -/
theorem upperSemicontinuousAt_leftEndpoint
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    UpperSemicontinuousAt D.leftEndpoint y := by
  intro t hleft
  have horder := D.leftEndpoint_lt_rightEndpoint hy
  obtain ⟨x, hleftx, hxupper⟩ :=
    exists_between (lt_min hleft horder)
  have hxright : x < D.rightEndpoint y :=
    hxupper.trans_le (min_le_right _ _)
  have hxsection :
      x ∈ horizontalSection (aeOpenRepresentative E) y := by
    rw [D.horizontalSection_eq_Ioo_endpoints hy]
    exact ⟨hleftx, hxright⟩
  filter_upwards [D.eventually_endpoints_straddle_of_mem hxsection] with z hz
  exact hz.1.trans (hxupper.trans_le (min_le_left _ _))

/-- Openness of the selected carrier makes the actual right endpoint lower
semicontinuous at every occupied height. -/
theorem lowerSemicontinuousAt_rightEndpoint
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    LowerSemicontinuousAt D.rightEndpoint y := by
  intro t hright
  have horder := D.leftEndpoint_lt_rightEndpoint hy
  obtain ⟨x, hlowerx, hxright⟩ :=
    exists_between (max_lt horder hright)
  have hleftx : D.leftEndpoint y < x :=
    (le_max_left _ _).trans_lt hlowerx
  have hxsection :
      x ∈ horizontalSection (aeOpenRepresentative E) y := by
    rw [D.horizontalSection_eq_Ioo_endpoints hy]
    exact ⟨hleftx, hxright⟩
  filter_upwards [D.eventually_endpoints_straddle_of_mem hxsection] with z hz
  exact ((le_max_right _ _).trans_lt hlowerx).trans hz.2

/-- Every occupied height has a neighborhood on which all sections remain
occupied. -/
theorem eventually_mem_occupiedHeights
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    ∀ᶠ z in 𝓝 y, z ∈ D.occupiedHeights :=
  D.isOpen_occupiedHeights.mem_nhds hy

private theorem exists_frontier_point_at_height_of_mem_closure_not_mem
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hyClosure : y ∈ closure D.occupiedHeights)
    (hyNot : y ∉ D.occupiedHeights) :
    ∃ p : PlanePoint,
      p ∈ frontier (aeOpenRepresentative E) ∧ p.2 = y := by
  let O : Set PlanePoint := aeOpenRepresentative E
  have hK : IsCompact (closure O) :=
    isCompact_iff_isClosed_bounded.2
      ⟨isClosed_closure, D.produce.selected_bounded.closure⟩
  have hclosed : IsClosed (Prod.snd '' closure O) :=
    (hK.image continuous_snd).isClosed
  have hyProjected : y ∈ Prod.snd '' closure O :=
    closure_minimal (image_mono subset_closure) hclosed hyClosure
  obtain ⟨p, hpClosure, hpHeight⟩ := hyProjected
  refine ⟨p, ?_, hpHeight⟩
  rw [D.produce.selected_open.frontier_eq]
  exact ⟨hpClosure, fun hpO => hyNot ⟨p, hpO, hpHeight⟩⟩

/-- The lower extreme height is attained by the complete selected frontier. -/
theorem exists_lowerHeightPoint (D : SelectedBoundaryTopologyInput E U) :
    ∃ p : PlanePoint,
      p ∈ frontier (aeOpenRepresentative E) ∧ p.2 = D.lowerHeight := by
  apply D.exists_frontier_point_at_height_of_mem_closure_not_mem
  · rw [D.occupiedHeights_eq_Ioo,
      closure_Ioo D.lowerHeight_lt_upperHeight.ne]
    exact ⟨le_rfl, D.lowerHeight_lt_upperHeight.le⟩
  · rw [D.occupiedHeights_eq_Ioo]
    exact fun h => (lt_irrefl D.lowerHeight) h.1

/-- The upper extreme height is attained by the complete selected frontier. -/
theorem exists_upperHeightPoint (D : SelectedBoundaryTopologyInput E U) :
    ∃ p : PlanePoint,
      p ∈ frontier (aeOpenRepresentative E) ∧ p.2 = D.upperHeight := by
  apply D.exists_frontier_point_at_height_of_mem_closure_not_mem
  · rw [D.occupiedHeights_eq_Ioo,
      closure_Ioo D.lowerHeight_lt_upperHeight.ne]
    exact ⟨D.lowerHeight_lt_upperHeight.le, le_rfl⟩
  · rw [D.occupiedHeights_eq_Ioo]
    exact fun h => (lt_irrefl D.upperHeight) h.2

/-- Every point of the complete selected frontier has height in the closed
occupied-height band. -/
theorem frontier_snd_mem_Icc
    (D : SelectedBoundaryTopologyInput E U) {p : PlanePoint}
    (hp : p ∈ frontier (aeOpenRepresentative E)) :
    p.2 ∈ Icc D.lowerHeight D.upperHeight := by
  have hpClosure : p ∈ closure (aeOpenRepresentative E) :=
    frontier_subset_closure hp
  have hpHeight : p.2 ∈ closure D.occupiedHeights :=
    map_mem_closure continuous_snd hpClosure
      (mapsTo_image Prod.snd (aeOpenRepresentative E))
  rw [D.occupiedHeights_eq_Ioo,
    closure_Ioo D.lowerHeight_lt_upperHeight.ne] at hpHeight
  exact hpHeight

/-- No selected-frontier points occur below the intrinsic lower height. -/
theorem frontierSection_eq_empty_of_lt_lowerHeight
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : y < D.lowerHeight) :
    D.frontierSection y = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  exact (not_le_of_gt hy) (D.frontier_snd_mem_Icc hx).1

/-- No selected-frontier points occur above the intrinsic upper height. -/
theorem frontierSection_eq_empty_of_upperHeight_lt
    (D : SelectedBoundaryTopologyInput E U) {y : ℝ}
    (hy : D.upperHeight < y) :
    D.frontierSection y = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  exact (not_le_of_gt hy) (D.frontier_snd_mem_Icc hx).2

/-- A chosen actual frontier point at the lower extreme height. -/
noncomputable def lowerHeightPoint
    (D : SelectedBoundaryTopologyInput E U) : PlanePoint :=
  Classical.choose D.exists_lowerHeightPoint

/-- A chosen actual frontier point at the upper extreme height. -/
noncomputable def upperHeightPoint
    (D : SelectedBoundaryTopologyInput E U) : PlanePoint :=
  Classical.choose D.exists_upperHeightPoint

theorem lowerHeightPoint_mem_frontier
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerHeightPoint ∈ frontier (aeOpenRepresentative E) :=
  (Classical.choose_spec D.exists_lowerHeightPoint).1

@[simp] theorem lowerHeightPoint_snd
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerHeightPoint.2 = D.lowerHeight :=
  (Classical.choose_spec D.exists_lowerHeightPoint).2

theorem upperHeightPoint_mem_frontier
    (D : SelectedBoundaryTopologyInput E U) :
    D.upperHeightPoint ∈ frontier (aeOpenRepresentative E) :=
  (Classical.choose_spec D.exists_upperHeightPoint).1

@[simp] theorem upperHeightPoint_snd
    (D : SelectedBoundaryTopologyInput E U) :
    D.upperHeightPoint.2 = D.upperHeight :=
  (Classical.choose_spec D.exists_upperHeightPoint).2

/-- Every selected-frontier horizontal slice is closed. -/
theorem isClosed_frontierSection
    (D : SelectedBoundaryTopologyInput E U) (y : ℝ) :
    IsClosed (D.frontierSection y) :=
  isClosed_frontier.preimage (continuous_id.prodMk continuous_const)

/-- Every selected-frontier horizontal slice is bounded. -/
theorem isBounded_frontierSection
    (D : SelectedBoundaryTopologyInput E U) (y : ℝ) :
    Bornology.IsBounded (D.frontierSection y) := by
  apply (D.produce.selected_bounded.closure.subset
    frontier_subset_closure).image_fst.subset
  intro x hx
  exact ⟨(x, y), hx, rfl⟩

/-- Every complete-frontier horizontal slice is compact. -/
theorem isCompact_frontierSection
    (D : SelectedBoundaryTopologyInput E U) (y : ℝ) :
    IsCompact (D.frontierSection y) :=
  isCompact_iff_isClosed_bounded.2
    ⟨D.isClosed_frontierSection y, D.isBounded_frontierSection y⟩

/-- The lower extreme frontier slice is a nonempty compact set. -/
theorem lower_frontierSection_nonempty_compact
    (D : SelectedBoundaryTopologyInput E U) :
    (D.frontierSection D.lowerHeight).Nonempty ∧
      IsCompact (D.frontierSection D.lowerHeight) := by
  obtain ⟨p, hp, hpy⟩ := D.exists_lowerHeightPoint
  refine ⟨⟨p.1, ?_⟩, D.isCompact_frontierSection D.lowerHeight⟩
  change (p.1, D.lowerHeight) ∈ frontier (aeOpenRepresentative E)
  rw [← hpy]
  exact hp

/-- The upper extreme frontier slice is a nonempty compact set. -/
theorem upper_frontierSection_nonempty_compact
    (D : SelectedBoundaryTopologyInput E U) :
    (D.frontierSection D.upperHeight).Nonempty ∧
      IsCompact (D.frontierSection D.upperHeight) := by
  obtain ⟨p, hp, hpy⟩ := D.exists_upperHeightPoint
  refine ⟨⟨p.1, ?_⟩, D.isCompact_frontierSection D.upperHeight⟩
  change (p.1, D.upperHeight) ∈ frontier (aeOpenRepresentative E)
  rw [← hpy]
  exact hp

/-- The completed lower extreme frontier slice is connected. -/
theorem isConnected_lower_frontierSection
    (D : SelectedBoundaryTopologyInput E U) :
    IsConnected (D.frontierSection D.lowerHeight) := by
  have hplanar : IsConnected
      (frontier (aeOpenRepresentative E) ∩
        Prod.snd ⁻¹' ({D.lowerHeight} : Set ℝ)) := by
    rw [← D.iInter_lowerClosedBand]
    exact isConnected_iInter_of_antitone D.lowerClosedBand
      D.antitone_lowerClosedBand D.isCompact_lowerClosedBand
      D.isConnected_lowerClosedBand
  have himage : Prod.fst ''
      (frontier (aeOpenRepresentative E) ∩
        Prod.snd ⁻¹' ({D.lowerHeight} : Set ℝ)) =
      D.frontierSection D.lowerHeight := by
    ext x
    constructor
    · rintro ⟨p, ⟨hpFrontier, hpHeight⟩, rfl⟩
      have hpHeight' : p.2 = D.lowerHeight :=
        Set.mem_singleton_iff.mp hpHeight
      change
        (p.1, D.lowerHeight) ∈ frontier (aeOpenRepresentative E)
      rwa [← hpHeight']
    · intro hx
      exact ⟨(x, D.lowerHeight),
        ⟨hx, Set.mem_singleton_iff.mpr rfl⟩, rfl⟩
  rw [← himage]
  exact hplanar.image Prod.fst continuous_fst.continuousOn

/-- The completed upper extreme frontier slice is connected. -/
theorem isConnected_upper_frontierSection
    (D : SelectedBoundaryTopologyInput E U) :
    IsConnected (D.frontierSection D.upperHeight) := by
  have hplanar : IsConnected
      (frontier (aeOpenRepresentative E) ∩
        Prod.snd ⁻¹' ({D.upperHeight} : Set ℝ)) := by
    rw [← D.iInter_upperClosedBand]
    exact isConnected_iInter_of_antitone D.upperClosedBand
      D.antitone_upperClosedBand D.isCompact_upperClosedBand
      D.isConnected_upperClosedBand
  have himage : Prod.fst ''
      (frontier (aeOpenRepresentative E) ∩
        Prod.snd ⁻¹' ({D.upperHeight} : Set ℝ)) =
      D.frontierSection D.upperHeight := by
    ext x
    constructor
    · rintro ⟨p, ⟨hpFrontier, hpHeight⟩, rfl⟩
      have hpHeight' : p.2 = D.upperHeight :=
        Set.mem_singleton_iff.mp hpHeight
      change
        (p.1, D.upperHeight) ∈ frontier (aeOpenRepresentative E)
      rwa [← hpHeight']
    · intro hx
      exact ⟨(x, D.upperHeight),
        ⟨hx, Set.mem_singleton_iff.mpr rfl⟩, rfl⟩
  rw [← himage]
  exact hplanar.image Prod.fst continuous_fst.continuousOn

/-- The complete lower extreme frontier slice is its intrinsic closed
interval. -/
theorem lower_frontierSection_eq_Icc
    (D : SelectedBoundaryTopologyInput E U) :
    D.frontierSection D.lowerHeight =
      Icc (sInf (D.frontierSection D.lowerHeight))
        (sSup (D.frontierSection D.lowerHeight)) := by
  apply eq_Icc_csInf_csSup_of_connected_bdd_closed
    D.isConnected_lower_frontierSection
  · exact D.isBounded_frontierSection D.lowerHeight |>.bddBelow
  · exact D.isBounded_frontierSection D.lowerHeight |>.bddAbove
  · exact D.isClosed_frontierSection D.lowerHeight

/-- The complete upper extreme frontier slice is its intrinsic closed
interval. -/
theorem upper_frontierSection_eq_Icc
    (D : SelectedBoundaryTopologyInput E U) :
    D.frontierSection D.upperHeight =
      Icc (sInf (D.frontierSection D.upperHeight))
        (sSup (D.frontierSection D.upperHeight)) := by
  apply eq_Icc_csInf_csSup_of_connected_bdd_closed
    D.isConnected_upper_frontierSection
  · exact D.isBounded_frontierSection D.upperHeight |>.bddBelow
  · exact D.isBounded_frontierSection D.upperHeight |>.bddAbove
  · exact D.isClosed_frontierSection D.upperHeight

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
