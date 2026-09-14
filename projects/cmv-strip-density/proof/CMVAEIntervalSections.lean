/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVAEOpenRepresentative
import CMVSourceSectionClassification

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology symmDiff

noncomputable section

namespace CMVRelaxation

open CMVSourceClassification

/-- Almost every horizontal section agrees modulo one-dimensional volume with
an order-connected set. The interval may vary existentially with the height. -/
def HasAEIntervalHorizontalSections (E : Set PlanePoint) : Prop :=
  ∀ᵐ y ∂(volume : Measure ℝ), ∃ I : Set ℝ,
    I.OrdConnected ∧ horizontalSection E y =ᵐ[volume] I

/-- Planar almost-everywhere equality descends to horizontal sections at almost
every height. This is the Fubini bridge used before pointwise saturation. -/
theorem ae_horizontalSection_congr_ae {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      horizontalSection E y =ᵐ[volume] horizontalSection F y := by
  rw [Measure.volume_eq_prod] at hEF
  have hswap :
      Filter.Tendsto Prod.swap (ae (volume.prod volume))
        (ae (volume.prod volume)) :=
    (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae
  have hEFswap :
      (fun p : ℝ × ℝ => E p.swap) =ᵐ[volume.prod volume]
        (fun p : ℝ × ℝ => F p.swap) :=
    hEF.comp_tendsto hswap
  filter_upwards [Measure.ae_ae_eq_curry_of_prod hEFswap] with y hy
  filter_upwards [hy] with x hx
  change E (x, y) = F (x, y)
  simpa only [Function.curry_apply, Prod.swap_prod_mk] using hx

private theorem middle_mem_aeOpenRepresentative
    {E : Set PlanePoint}
    (hsections : HasAEIntervalHorizontalSections (aeOpenRepresentative E))
    {y x₁ x x₂ : ℝ}
    (hx₁ : x₁ ∈ horizontalSection (aeOpenRepresentative E) y)
    (hx₂ : x₂ ∈ horizontalSection (aeOpenRepresentative E) y)
    (h₁x : x₁ < x) (hx₂' : x < x₂) :
    x ∈ horizontalSection (aeOpenRepresentative E) y := by
  let O : Set PlanePoint := aeOpenRepresentative E
  have hOopen : IsOpen O := isOpen_aeOpenRepresentative E
  have hx₁O : (x₁, y) ∈ O := hx₁
  have hx₂O : (x₂, y) ∈ O := hx₂
  obtain ⟨r₁, hr₁, hball₁⟩ :=
    Metric.mem_nhds_iff.mp (hOopen.mem_nhds hx₁O)
  obtain ⟨r₂, hr₂, hball₂⟩ :=
    Metric.mem_nhds_iff.mp (hOopen.mem_nhds hx₂O)
  let m : ℝ := min (min r₁ r₂) (min (x - x₁) (x₂ - x))
  let d : ℝ := m / 8
  have hm : 0 < m := by
    dsimp [m]
    exact lt_min (lt_min hr₁ hr₂) (lt_min (sub_pos.mpr h₁x) (sub_pos.mpr hx₂'))
  have hd : 0 < d := div_pos hm (by norm_num)
  have hdm : d * 2 < m := by
    dsimp [d]
    nlinarith
  have hmr₁ : m ≤ r₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hmr₂ : m ≤ r₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hmgap₁ : m ≤ x - x₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hmgap₂ : m ≤ x₂ - x := (min_le_right _ _).trans (min_le_right _ _)
  have hdr₁ : d < r₁ := lt_of_lt_of_le (by nlinarith) hmr₁
  have hdr₂ : d < r₂ := lt_of_lt_of_le (by nlinarith) hmr₂
  have hdgap₁ : d * 2 < x - x₁ := hdm.trans_le hmgap₁
  have hdgap₂ : d * 2 < x₂ - x := hdm.trans_le hmgap₂
  let A : Set ℝ := Metric.ball x₁ d
  let B : Set ℝ := Metric.ball x₂ d
  let C : Set ℝ := Metric.ball x d
  let Y : Set ℝ := Metric.ball y d
  have hAY : A ×ˢ Y ⊆ O := by
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    apply hball₁
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(show dist u x₁ < d from hu).trans hdr₁,
      (show dist z y < d from hz).trans hdr₁⟩
  have hBY : B ×ˢ Y ⊆ O := by
    rintro ⟨u, z⟩ ⟨hu, hz⟩
    apply hball₂
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(show dist u x₂ < d from hu).trans hdr₂,
      (show dist z y < d from hz).trans hdr₂⟩
  have hsliceZero : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Y →
      volume (C \ horizontalSection O z) = 0 := by
    filter_upwards [hsections] with z hzgood hzY
    rcases hzgood with ⟨I, hIord, hOI⟩
    have hAsection : A ⊆ horizontalSection O z := by
      intro u hu
      exact hAY ⟨hu, hzY⟩
    have hBsection : B ⊆ horizontalSection O z := by
      intro u hu
      exact hBY ⟨hu, hzY⟩
    have hAI : (A ∩ I).Nonempty := by
      by_contra hnone
      have hsub : A ⊆ horizontalSection O z \ I := by
        intro u hu
        refine ⟨hAsection hu, ?_⟩
        intro huI
        exact hnone ⟨u, hu, huI⟩
      have hzero := measure_mono_null hsub (ae_eq_set.mp hOI).1
      have hpos : 0 < volume A :=
        Metric.isOpen_ball.measure_pos volume
          ⟨x₁, Metric.mem_ball_self hd⟩
      exact hpos.ne' hzero
    have hBI : (B ∩ I).Nonempty := by
      by_contra hnone
      have hsub : B ⊆ horizontalSection O z \ I := by
        intro u hu
        refine ⟨hBsection hu, ?_⟩
        intro huI
        exact hnone ⟨u, hu, huI⟩
      have hzero := measure_mono_null hsub (ae_eq_set.mp hOI).1
      have hpos : 0 < volume B :=
        Metric.isOpen_ball.measure_pos volume
          ⟨x₂, Metric.mem_ball_self hd⟩
      exact hpos.ne' hzero
    rcases hAI with ⟨a, haA, haI⟩
    rcases hBI with ⟨b, hbB, hbI⟩
    change a ∈ Metric.ball x₁ d at haA
    change b ∈ Metric.ball x₂ d at hbB
    rw [Real.ball_eq_Ioo] at haA hbB
    have ha : a < x - d := by nlinarith [haA.2, hdgap₁]
    have hb : x + d < b := by nlinarith [hbB.1, hdgap₂]
    have hCsubI : C ⊆ I := by
      intro c hc
      change c ∈ Metric.ball x d at hc
      rw [Real.ball_eq_Ioo] at hc
      exact hIord.out haI hbI ⟨le_of_lt (ha.trans hc.1),
        le_of_lt (hc.2.trans hb)⟩
    apply measure_mono_null (t := I \ horizontalSection O z)
    · intro u hu
      exact ⟨hCsubI hu.1, hu.2⟩
    · exact (ae_eq_set.mp hOI).2
  let S : Set PlanePoint := (C ×ˢ Y) \ O
  have hSmeasurable : MeasurableSet S :=
    (Metric.isOpen_ball.prod Metric.isOpen_ball).measurableSet.diff
      hOopen.measurableSet
  have hSzero : volume S = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hSmeasurable]
    calc
      (∫⁻ z : ℝ, volume ((fun u : ℝ => (u, z)) ⁻¹' S)) =
          ∫⁻ _z : ℝ, 0 := by
        apply lintegral_congr_ae
        filter_upwards [hsliceZero] with z hz
        by_cases hzY : z ∈ Y
        · have hpre : (fun u : ℝ => (u, z)) ⁻¹' S =
              C \ horizontalSection O z := by
            ext u
            change (((u ∈ C ∧ z ∈ Y) ∧ (u, z) ∉ O) ↔
              (u ∈ C ∧ (u, z) ∉ O))
            simp only [hzY, and_true]
          rw [hpre, hz hzY]
        · have hpre : (fun u : ℝ => (u, z)) ⁻¹' S = ∅ := by
            ext u
            change (((u ∈ C ∧ z ∈ Y) ∧ (u, z) ∉ O) ↔ False)
            simp only [hzY, and_false, false_and]
          rw [hpre, measure_empty]
      _ = 0 := lintegral_zero
  have hballSub : Metric.ball ((x, y) : PlanePoint) d \ O ⊆ S := by
    rintro ⟨u, z⟩ ⟨hball, hnotO⟩
    change dist (u, z) (x, y) < d at hball
    rw [Prod.dist_eq, max_lt_iff] at hball
    refine ⟨⟨hball.1, hball.2⟩, hnotO⟩
  have hballZero : volume (Metric.ball ((x, y) : PlanePoint) d \ O) = 0 :=
    measure_mono_null hballSub hSzero
  have hmem : (x, y) ∈ aeOpenRepresentative O := ⟨d, hd, hballZero⟩
  rw [show aeOpenRepresentative O = O by
    dsimp [O]
    exact aeOpenRepresentative_idempotent E] at hmem
  exact hmem

/-- Saturation upgrades almost-everywhere interval fibers to order-connected
fibers at every height, including exceptional and interface heights. -/
theorem ordConnected_horizontalSection_aeOpenRepresentative
    {E U : Set PlanePoint} (hU : IsOpen U) (hEU : E =ᵐ[volume] U)
    (hsections : HasAEIntervalHorizontalSections E) (y : ℝ) :
    (horizontalSection (aeOpenRepresentative E) y).OrdConnected := by
  have hOE : aeOpenRepresentative E =ᵐ[volume] E :=
    aeOpenRepresentative_ae_eq hU hEU
  have hsectionsOE := ae_horizontalSection_congr_ae hOE
  have hsectionsO : HasAEIntervalHorizontalSections (aeOpenRepresentative E) := by
    filter_upwards [hsectionsOE, hsections] with z hOEz hEz
    rcases hEz with ⟨I, hI, hEI⟩
    exact ⟨I, hI, hOEz.trans hEI⟩
  rw [Set.ordConnected_iff_uIcc_subset]
  intro x₁ hx₁ x₂ hx₂ x hx
  rcases (Set.mem_uIcc.mp hx) with hxorder | hxorder
  · rcases hxorder.1.eq_or_lt with rfl | h₁x
    · exact hx₁
    rcases hxorder.2.eq_or_lt with rfl | hx₂'
    · exact hx₂
    exact middle_mem_aeOpenRepresentative hsectionsO hx₁ hx₂ h₁x hx₂'
  · rcases hxorder.1.eq_or_lt with rfl | h₂x
    · exact hx₂
    rcases hxorder.2.eq_or_lt with rfl | hx₁'
    · exact hx₁
    exact middle_mem_aeOpenRepresentative hsectionsO hx₂ hx₁ h₂x hx₁'

/-- A nonempty bounded open order-connected subset of the line is the actual
open interval between the infimum and supremum derived from the set itself. -/
theorem IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
    {S : Set ℝ} (hSopen : IsOpen S) (hSne : S.Nonempty)
    (hSbounded : Bornology.IsBounded S) (hSord : S.OrdConnected) :
    S = Ioo (sInf S) (sSup S) := by
  have hbddBelow : BddBelow S := hSbounded.bddBelow
  have hbddAbove : BddAbove S := hSbounded.bddAbove
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨r, hr, hball⟩ :=
      Metric.mem_nhds_iff.mp (hSopen.mem_nhds hx)
    have hleft : x - r / 2 ∈ S := by
      apply hball
      rw [Real.ball_eq_Ioo]
      constructor <;> nlinarith
    have hright : x + r / 2 ∈ S := by
      apply hball
      rw [Real.ball_eq_Ioo]
      constructor <;> nlinarith
    exact ⟨lt_of_le_of_lt (csInf_le hbddBelow hleft) (by nlinarith),
      lt_of_lt_of_le (by nlinarith) (le_csSup hbddAbove hright)⟩
  · intro x hx
    obtain ⟨a, haS, hax⟩ := exists_lt_of_csInf_lt hSne hx.1
    obtain ⟨b, hbS, hxb⟩ := exists_lt_of_lt_csSup hSne hx.2
    exact hSord.out haS hbS ⟨hax.le, hxb.le⟩

/-- A nonempty selected section is the interval between its own infimum and
supremum, and those two derived endpoints are strictly ordered. -/
theorem horizontalSection_eq_Ioo_selfEndpoints_aeOpenRepresentative
    {E U : Set PlanePoint} (hU : IsOpen U) (hEU : E =ᵐ[volume] U)
    (hUbounded : Bornology.IsBounded U)
    (hsections : HasAEIntervalHorizontalSections E) (y : ℝ)
    (hne : (horizontalSection (aeOpenRepresentative E) y).Nonempty) :
    sInf (horizontalSection (aeOpenRepresentative E) y) <
        sSup (horizontalSection (aeOpenRepresentative E) y) ∧
      horizontalSection (aeOpenRepresentative E) y =
        Ioo (sInf (horizontalSection (aeOpenRepresentative E) y))
          (sSup (horizontalSection (aeOpenRepresentative E) y)) := by
  let S := horizontalSection (aeOpenRepresentative E) y
  have hSopen : IsOpen S :=
    CMVSourceClassification.isOpen_horizontalSection
      (isOpen_aeOpenRepresentative E) y
  have hSbounded : Bornology.IsBounded S :=
    CMVSourceClassification.isBounded_horizontalSection
      (isBounded_aeOpenRepresentative_of_ae hEU hUbounded) y
  have hSord : S.OrdConnected :=
    ordConnected_horizontalSection_aeOpenRepresentative hU hEU hsections y
  have hSeq : S = Ioo (sInf S) (sSup S) :=
    IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
      hSopen hne hSbounded hSord
  obtain ⟨x, hxS⟩ := hne
  have hxI : x ∈ Ioo (sInf S) (sSup S) := hSeq ▸ hxS
  exact ⟨hxI.1.trans hxI.2, hSeq⟩

/-- Every selected horizontal section is empty or an actual bounded open
interval. Its endpoints are `sInf` and `sSup` of the selected section itself. -/
theorem horizontalSection_empty_or_Ioo_aeOpenRepresentative
    {E U : Set PlanePoint} (hU : IsOpen U) (hEU : E =ᵐ[volume] U)
    (hUbounded : Bornology.IsBounded U)
    (hsections : HasAEIntervalHorizontalSections E) (y : ℝ) :
    horizontalSection (aeOpenRepresentative E) y = ∅ ∨
      ∃ a b : ℝ, a < b ∧
        horizontalSection (aeOpenRepresentative E) y = Ioo a b := by
  let S := horizontalSection (aeOpenRepresentative E) y
  by_cases hSne : S.Nonempty
  · right
    have hself :=
      horizontalSection_eq_Ioo_selfEndpoints_aeOpenRepresentative
        hU hEU hUbounded hsections y hSne
    exact ⟨sInf S, sSup S, hself.1, hself.2⟩
  · left
    exact not_nonempty_iff_eq_empty.mp hSne


/-! ## A separately supplied common horizontal center -/

/-- Reflection in the vertical line with abscissa `axis`. -/
def reflectAcrossVerticalAxis (axis : ℝ) (p : PlanePoint) : PlanePoint :=
  (2 * axis - p.1, p.2)

@[simp] theorem reflectAcrossVerticalAxis_involutive
    (axis : ℝ) (p : PlanePoint) :
    reflectAcrossVerticalAxis axis (reflectAcrossVerticalAxis axis p) = p := by
  ext <;> simp [reflectAcrossVerticalAxis]

private theorem measurePreserving_reflectReal (axis : ℝ) :
    MeasurePreserving (fun x : ℝ => 2 * axis - x) volume volume := by
  have h :=
    (measurePreserving_add_left (volume : Measure ℝ) (2 * axis)).comp
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  convert h using 1
  funext x
  simp only [Function.comp_apply]
  ring

theorem measurePreserving_reflectAcrossVerticalAxis (axis : ℝ) :
    MeasurePreserving (reflectAcrossVerticalAxis axis) volume volume := by
  change MeasurePreserving (reflectAcrossVerticalAxis axis)
    ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume)
  have h :=
    (measurePreserving_reflectReal axis).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  convert h using 1
  funext p
  rfl

private theorem ae_reflection_invariant_of_centered_sections
    {E U : Set PlanePoint} (axis : ℝ) (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U)
    (hcentered :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E) :
    E =ᵐ[volume] reflectAcrossVerticalAxis axis ⁻¹' E := by
  let R : PlanePoint → PlanePoint := reflectAcrossVerticalAxis axis
  let F : Set PlanePoint := R ⁻¹' E
  let V : Set PlanePoint := R ⁻¹' U
  have hRcontinuous : Continuous R := by
    dsimp [R, reflectAcrossVerticalAxis]
    exact (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hRae :
      Filter.Tendsto R (ae (volume : Measure PlanePoint))
        (ae (volume : Measure PlanePoint)) :=
    (measurePreserving_reflectAcrossVerticalAxis axis).quasiMeasurePreserving.tendsto_ae
  have hFV : F =ᵐ[volume] V := by
    have hcomp := hEU.comp_tendsto hRae
    filter_upwards [hcomp] with p hp
    exact hp
  have hVopen : IsOpen V := hU.preimage hRcontinuous
  have hEnull : NullMeasurableSet E volume :=
    hU.nullMeasurableSet.congr hEU.symm
  have hFnull : NullMeasurableSet F volume :=
    hVopen.nullMeasurableSet.congr hFV.symm
  apply CMVSourceClassification.ae_eq_of_ae_horizontalSection_eq hEnull hFnull
  filter_upwards [hcentered] with y hy
  rcases hy with ⟨length, hlength, hEI⟩
  let I : Set ℝ :=
    Icc (axis - length / 2) (axis + length / 2)
  have hrealAe :
      Filter.Tendsto (fun x : ℝ => 2 * axis - x)
        (ae (volume : Measure ℝ)) (ae (volume : Measure ℝ)) :=
    (measurePreserving_reflectReal axis).quasiMeasurePreserving.tendsto_ae
  have hcomp := hEI.comp_tendsto hrealAe
  have hFI : horizontalSection F y =ᵐ[volume] I := by
    filter_upwards [hcomp] with x hx
    change ((2 * axis - x, y) ∈ E) = (x ∈ I)
    change ((2 * axis - x, y) ∈ E) =
      (2 * axis - x ∈ I) at hx
    calc
      ((2 * axis - x, y) ∈ E) = (2 * axis - x ∈ I) := hx
      _ = (x ∈ I) := by
        apply propext
        dsimp [I]
        simp only [Set.mem_Icc]
        constructor <;> intro h <;> constructor <;> linarith
  exact hEI.trans hFI.symm

/-- A common center supplied only almost everywhere becomes an exact reflection
symmetry of the selected representative. -/
theorem aeOpenRepresentative_reflection_mem_iff
    {E U : Set PlanePoint} (axis : ℝ) (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U)
    (hcentered :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E)
    (p : PlanePoint) :
    reflectAcrossVerticalAxis axis p ∈ aeOpenRepresentative E ↔
      p ∈ aeOpenRepresentative E := by
  let O : Set PlanePoint := aeOpenRepresentative E
  let R : PlanePoint → PlanePoint := reflectAcrossVerticalAxis axis
  let V : Set PlanePoint := R ⁻¹' O
  have hRcontinuous : Continuous R := by
    dsimp [R, reflectAcrossVerticalAxis]
    exact (continuous_const.sub continuous_fst).prodMk continuous_snd
  have hRae :
      Filter.Tendsto R (ae (volume : Measure PlanePoint))
        (ae (volume : Measure PlanePoint)) :=
    (measurePreserving_reflectAcrossVerticalAxis axis).quasiMeasurePreserving.tendsto_ae
  have hOE : O =ᵐ[volume] E := aeOpenRepresentative_ae_eq hU hEU
  have hFE :
      (reflectAcrossVerticalAxis axis ⁻¹' E) =ᵐ[volume] E :=
    (ae_reflection_invariant_of_centered_sections axis hU hEU hcentered).symm
  have hVE : V =ᵐ[volume] E := by
    have hcomp := hOE.comp_tendsto hRae
    have hVF :
        V =ᵐ[volume] reflectAcrossVerticalAxis axis ⁻¹' E := by
      filter_upwards [hcomp] with p hp
      exact hp
    exact hVF.trans hFE
  have hVopen : IsOpen V :=
    (isOpen_aeOpenRepresentative E).preimage hRcontinuous
  have hVsubO : V ⊆ O :=
    open_subset_aeOpenRepresentative hVopen hVE.symm
  constructor
  · intro hp
    change R p ∈ O at hp
    have hpV : p ∈ V := by
      change R p ∈ O
      exact hp
    exact hVsubO hpV
  · intro hp
    change p ∈ O at hp
    have hRpV : R p ∈ V := by
      change R (R p) ∈ O
      simpa only [R, reflectAcrossVerticalAxis_involutive] using hp
    exact hVsubO hRpV

/-- Under the separately explicit AE-centered-section premise, every nonempty
selected section is an actual open interval with that same center. -/
theorem horizontalSection_empty_or_centered_Ioo_aeOpenRepresentative
    {E U : Set PlanePoint} (axis : ℝ) (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) (hUbounded : Bornology.IsBounded U)
    (hcentered :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E)
    (y : ℝ) :
    horizontalSection (aeOpenRepresentative E) y = ∅ ∨
      ∃ radius : ℝ, 0 < radius ∧
        horizontalSection (aeOpenRepresentative E) y =
          Ioo (axis - radius) (axis + radius) := by
  have hintervals : HasAEIntervalHorizontalSections E := by
    filter_upwards [hcentered] with z hz
    rcases hz with ⟨length, hlength, hsection⟩
    exact ⟨Icc (axis - length / 2) (axis + length / 2),
      Set.ordConnected_Icc, hsection⟩
  rcases horizontalSection_empty_or_Ioo_aeOpenRepresentative
      hU hEU hUbounded hintervals y with hempty | ⟨a, b, hab, hsection⟩
  · exact Or.inl hempty
  · right
    have hsymm : ∀ x : ℝ,
        x ∈ Ioo a b ↔ 2 * axis - x ∈ Ioo a b := by
      intro x
      rw [← hsection]
      change (x, y) ∈ aeOpenRepresentative E ↔
        (2 * axis - x, y) ∈ aeOpenRepresentative E
      exact (aeOpenRepresentative_reflection_mem_iff
        axis hU hEU hcentered (x, y)).symm
    have hleft : 2 * axis - b ≤ a := by
      by_contra h
      have hlt : a < 2 * axis - b := lt_of_not_ge h
      let x := (a + min b (2 * axis - b)) / 2
      have hamin : a < min b (2 * axis - b) := lt_min hab hlt
      have hx : x ∈ Ioo a b := by
        dsimp [x]
        constructor
        · nlinarith [min_le_left b (2 * axis - b)]
        · nlinarith [min_le_left b (2 * axis - b)]
      have hRx := (hsymm x).1 hx
      dsimp [x] at hRx
      have hminle : min b (2 * axis - b) ≤ 2 * axis - b :=
        min_le_right _ _
      nlinarith [hRx.2]
    have hright : a ≤ 2 * axis - b := by
      by_contra h
      have hlt : 2 * axis - b < a := lt_of_not_ge h
      have hdual : 2 * axis - a < b := by linarith
      let x := (max a (2 * axis - a) + b) / 2
      have hmaxb : max a (2 * axis - a) < b := max_lt hab hdual
      have hx : x ∈ Ioo a b := by
        dsimp [x]
        constructor
        · nlinarith [le_max_left a (2 * axis - a)]
        · nlinarith
      have hRx := (hsymm x).1 hx
      dsimp [x] at hRx
      have hlemax : 2 * axis - a ≤ max a (2 * axis - a) :=
        le_max_right _ _
      nlinarith [hRx.1]
    have hmid : a + b = 2 * axis := by
      linarith [le_antisymm hleft hright]
    let radius := b - axis
    have hradius : 0 < radius := by
      dsimp [radius]
      nlinarith
    refine ⟨radius, hradius, ?_⟩
    rw [hsection]
    congr 1 <;> dsimp [radius] <;> linarith
end CMVRelaxation
