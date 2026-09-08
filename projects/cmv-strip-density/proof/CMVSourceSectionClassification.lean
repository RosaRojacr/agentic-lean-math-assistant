/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSourceClassification
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Sectionwise reconstruction of a source type-(iv) carrier

Cañete--Miranda--Vittone obtain the type-(iv) geometry by analyzing the
one-dimensional slices of a symmetrized finite-perimeter region (Lemma 3.8,
printed pages 15--17).  This module isolates the measure-theoretic reconstruction
step: almost-everywhere equality of almost every horizontal slice implies planar
almost-everywhere equality, including for null-measurable representatives.

The final predicate is strictly sectionwise.  It does not assume planar equality
with `RawFourArcCoordinates.carrier`.  Proving that every source minimizer has
these slices still requires the unresolved regularity, symmetrization, and
boundary classification argument.
-/

open Set
open MeasureTheory

noncomputable section

namespace CMVSourceClassification

/-- The horizontal section of a planar carrier at height `y`, matching the
interval slices used in CMV Proposition 3.6 and Lemma 3.8. -/
def horizontalSection (carrier : Set PlanePoint) (y : ℝ) : Set ℝ :=
  {x | (x, y) ∈ carrier}

/-- Horizontal sections of an open planar set are open. -/
theorem isOpen_horizontalSection
    {U : Set PlanePoint} (hU : IsOpen U) (y : ℝ) :
    IsOpen (horizontalSection U y) := by
  exact hU.preimage (continuous_id.prodMk continuous_const)

/-- Horizontal sections of a bounded planar set are bounded. -/
theorem isBounded_horizontalSection
    {U : Set PlanePoint} (hU : Bornology.IsBounded U) (y : ℝ) :
    Bornology.IsBounded (horizontalSection U y) := by
  apply hU.image_fst.subset
  intro x hx
  exact ⟨(x, y), hx, rfl⟩

/-- Every boundary point of a horizontal section lifts to a boundary point of
the planar set.  This is the forward half of finite-crossing reconstruction;
the reverse half requires source-local transversality. -/
theorem frontier_horizontalSection_subset
    (U : Set PlanePoint) (y : ℝ) :
    frontier (horizontalSection U y) ⊆
      {x : ℝ | (x, y) ∈ frontier U} := by
  exact (continuous_id.prodMk continuous_const).frontier_preimage_subset U

/-- A bounded open subset of the real line whose complete frontier consists of
two ordered points is the open interval between them.  Boundedness rules out
the two exterior components; connectedness of the three complementary
intervals then determines membership. -/
theorem IsOpen.eq_Ioo_of_isBounded_frontier_eq_pair
    {S : Set ℝ} (hSopen : IsOpen S) (hSbounded : Bornology.IsBounded S)
    {a b : ℝ} (hab : a < b) (hfrontier : frontier S = {a, b}) :
    S = Ioo a b := by
  have component_subset
      (C : Set ℝ) (hC : IsPreconnected C)
      (hCpair : Disjoint C ({a, b} : Set ℝ))
      (hne : (C ∩ S).Nonempty) :
      C ⊆ S := by
    apply hC.subset_of_closure_inter_subset hSopen hne
    rintro x ⟨hxClosure, hxC⟩
    by_contra hxS
    have hxFrontier : x ∈ frontier S := by
      rw [hSopen.frontier_eq]
      exact ⟨hxClosure, hxS⟩
    have hxPair : x ∈ ({a, b} : Set ℝ) := by
      rwa [hfrontier] at hxFrontier
    exact (Set.disjoint_left.mp hCpair) hxC hxPair
  have hleftPair : Disjoint (Iio a) ({a, b} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hxa hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hxaEq | hxbEq
    · subst x
      exact (lt_irrefl a) hxa
    · subst x
      exact (not_lt_of_ge hab.le) hxa
  have hrightPair : Disjoint (Ioi b) ({a, b} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hbx hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hxaEq | hxbEq
    · subst x
      exact (not_lt_of_ge hab.le) hbx
    · subst x
      exact (lt_irrefl b) hbx
  have hmiddlePair : Disjoint (Ioo a b) ({a, b} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx hxPair
    simp only [mem_insert_iff, mem_singleton_iff] at hxPair
    rcases hxPair with hxaEq | hxbEq
    · subst x
      exact (lt_irrefl a) hx.1
    · subst x
      exact (lt_irrefl b) hx.2
  have hleft : Disjoint (Iio a) S := by
    rw [Set.disjoint_left]
    intro x hxa hxS
    have hsub : Iio a ⊆ S :=
      component_subset (Iio a) isPreconnected_Iio hleftPair
        ⟨x, hxa, hxS⟩
    obtain ⟨lower, hlower⟩ := hSbounded.bddBelow
    have hzIio : min a lower - 1 ∈ Iio a := by
      change min a lower - 1 < a
      linarith [min_le_left a lower]
    have hzLower := hlower (hsub hzIio)
    linarith [min_le_right a lower]
  have hright : Disjoint (Ioi b) S := by
    rw [Set.disjoint_left]
    intro x hbx hxS
    have hsub : Ioi b ⊆ S :=
      component_subset (Ioi b) isPreconnected_Ioi hrightPair
        ⟨x, hbx, hxS⟩
    obtain ⟨upper, hupper⟩ := hSbounded.bddAbove
    have hzIoi : max b upper + 1 ∈ Ioi b := by
      change b < max b upper + 1
      linarith [le_max_left b upper]
    have hzUpper := hupper (hsub hzIoi)
    linarith [le_max_right b upper]
  have haFrontier : a ∈ frontier S := by
    rw [hfrontier]
    simp
  have hbFrontier : b ∈ frontier S := by
    rw [hfrontier]
    simp
  have hSfrontier : Disjoint S (frontier S) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    exact hSopen.inter_frontier_eq
  have haNotMem : a ∉ S := fun haS =>
    (Set.disjoint_left.mp hSfrontier) haS haFrontier
  have hbNotMem : b ∉ S := fun hbS =>
    (Set.disjoint_left.mp hSfrontier) hbS hbFrontier
  have hSne : S.Nonempty :=
    closure_nonempty_iff.mp ⟨a, frontier_subset_closure haFrontier⟩
  obtain ⟨x, hxS⟩ := hSne
  have hax : a < x := by
    apply lt_of_not_ge
    intro hxa
    rcases hxa.eq_or_lt with hxa | hxa
    · exact haNotMem (hxa ▸ hxS)
    · exact (Set.disjoint_left.mp hleft) hxa hxS
  have hxb : x < b := by
    apply lt_of_not_ge
    intro hbx
    rcases hbx.eq_or_lt with hbx | hbx
    · exact hbNotMem (hbx ▸ hxS)
    · exact (Set.disjoint_left.mp hright) hbx hxS
  have hmiddle : Ioo a b ⊆ S :=
    component_subset (Ioo a b) isPreconnected_Ioo hmiddlePair
      ⟨x, ⟨hax, hxb⟩, hxS⟩
  apply Set.Subset.antisymm
  · intro z hzS
    constructor
    · apply lt_of_not_ge
      intro hza
      rcases hza.eq_or_lt with hza | hza
      · exact haNotMem (hza ▸ hzS)
      · exact (Set.disjoint_left.mp hleft) hza hzS
    · apply lt_of_not_ge
      intro hbz
      rcases hbz.eq_or_lt with hbz | hbz
      · exact hbNotMem (hbz ▸ hzS)
      · exact (Set.disjoint_left.mp hright) hbz hzS
  · exact hmiddle

/-- Fubini reconstruction for null-measurable planar representatives.  The
measurable-representative detour is essential: reverse Fubini is false for an
arbitrary nonmeasurable subset of a product. -/
theorem ae_eq_of_ae_horizontalSection_eq
    {E F : Set PlanePoint}
    (hE : NullMeasurableSet E volume)
    (hF : NullMeasurableSet F volume)
    (hsections : ∀ᵐ y ∂(volume : Measure ℝ),
      horizontalSection E y =ᵐ[volume] horizontalSection F y) :
    E =ᵐ[volume] F := by
  rw [Measure.volume_eq_prod] at hE hF ⊢
  let Em : Set (ℝ × ℝ) := toMeasurable (volume.prod volume) E
  let Fm : Set (ℝ × ℝ) := toMeasurable (volume.prod volume) F
  have hEm : Em =ᵐ[volume.prod volume] E := by
    exact hE.toMeasurable_ae_eq
  have hFm : Fm =ᵐ[volume.prod volume] F := by
    exact hF.toMeasurable_ae_eq
  have hswap :
      Filter.Tendsto Prod.swap (ae (volume.prod volume))
        (ae (volume.prod volume)) :=
    (Measure.measurePreserving_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.tendsto_ae
  have hEm_sections : ∀ᵐ y ∂(volume : Measure ℝ),
      horizontalSection Em y =ᵐ[volume] horizontalSection E y := by
    have hEm_swap :
        (fun p : ℝ × ℝ => Em p.swap) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => E p.swap) :=
      hEm.comp_tendsto hswap
    filter_upwards [Measure.ae_ae_eq_curry_of_prod hEm_swap] with y hy
    filter_upwards [hy] with x hx
    change Em (x, y) = E (x, y)
    simpa only [Function.curry_apply, Prod.swap_prod_mk] using hx
  have hFm_sections : ∀ᵐ y ∂(volume : Measure ℝ),
      horizontalSection Fm y =ᵐ[volume] horizontalSection F y := by
    have hFm_swap :
        (fun p : ℝ × ℝ => Fm p.swap) =ᵐ[volume.prod volume]
          (fun p : ℝ × ℝ => F p.swap) :=
      hFm.comp_tendsto hswap
    filter_upwards [Measure.ae_ae_eq_curry_of_prod hFm_swap] with y hy
    filter_upwards [hy] with x hx
    change Fm (x, y) = F (x, y)
    simpa only [Function.curry_apply, Prod.swap_prod_mk] using hx
  have hmeasurable : MeasurableSet
      {p : ℝ × ℝ | (p ∈ Em ↔ p ∈ Fm)} := by
    have hset : {p : ℝ × ℝ | (p ∈ Em ↔ p ∈ Fm)} =
        (Em ∩ Fm) ∪ (Emᶜ ∩ Fmᶜ) := by
      ext p
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [hset]
    exact ((measurableSet_toMeasurable _ _).inter
      (measurableSet_toMeasurable _ _)).union
        ((measurableSet_toMeasurable _ _).compl.inter
          (measurableSet_toMeasurable _ _).compl)
  have hEmFm : Em =ᵐ[volume.prod volume] Fm := by
    have hmemYX :
        ∀ᵐ y ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure ℝ),
          ((x, y) ∈ Em ↔ (x, y) ∈ Fm) := by
      filter_upwards [hEm_sections, hsections, hFm_sections] with y hEy hEF hFy
      have hs := hEy.trans (hEF.trans hFy.symm)
      filter_upwards [hs] with x hx
      exact Iff.of_eq hx
    have hmemXY :
        ∀ᵐ x ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure ℝ),
          ((x, y) ∈ Em ↔ (x, y) ∈ Fm) :=
      (Measure.ae_ae_comm
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        hmeasurable).2 hmemYX
    have hmem : ∀ᵐ p ∂volume.prod volume, p ∈ Em ↔ p ∈ Fm :=
      (Measure.ae_prod_iff_ae_ae
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        hmeasurable).2 hmemXY
    filter_upwards [hmem] with p hp
    exact propext hp
  filter_upwards [hEm, hEmFm, hFm] with p hpE hpEF hpF
  exact hpE.symm.trans (hpEF.trans hpF)

namespace RawFourArcCoordinates

variable (raw : RawFourArcCoordinates)

private theorem isClosed_disk (center : PlanePoint) (radius : ℝ) :
    IsClosed {p : PlanePoint |
      (p.1 - center.1) ^ 2 + (p.2 - center.2) ^ 2 ≤ radius ^ 2} := by
  exact isClosed_le
    (((continuous_fst.sub continuous_const).pow 2).add
      ((continuous_snd.sub continuous_const).pow 2))
    continuous_const

theorem isClosed_rectangleCarrier : IsClosed raw.rectangleCarrier := by
  unfold rectangleCarrier
  have hxLower : IsClosed {p : PlanePoint | -raw.outerHalfWidth ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hxUpper : IsClosed {p : PlanePoint | p.1 ≤ raw.outerHalfWidth} :=
    isClosed_le continuous_fst continuous_const
  have hy : IsClosed {p : PlanePoint | |p.2| ≤ (1 : ℝ)} :=
    isClosed_le continuous_snd.abs continuous_const
  exact hxLower.inter (hxUpper.inter hy)

theorem isClosed_leftSegmentCarrier : IsClosed raw.leftSegmentCarrier := by
  unfold leftSegmentCarrier
  have hx : IsClosed {p : PlanePoint | p.1 ≤ -raw.outerHalfWidth} :=
    isClosed_le continuous_fst continuous_const
  have hy : IsClosed {p : PlanePoint | |p.2| ≤ (1 : ℝ)} :=
    isClosed_le continuous_snd.abs continuous_const
  exact (isClosed_disk raw.leftCenter raw.sourceRadius).inter (hx.inter hy)

theorem isClosed_rightSegmentCarrier : IsClosed raw.rightSegmentCarrier := by
  unfold rightSegmentCarrier
  have hx : IsClosed {p : PlanePoint | raw.outerHalfWidth ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hy : IsClosed {p : PlanePoint | |p.2| ≤ (1 : ℝ)} :=
    isClosed_le continuous_snd.abs continuous_const
  exact (isClosed_disk raw.rightCenter raw.sourceRadius).inter (hx.inter hy)

theorem isClosed_upperCapCarrier : IsClosed raw.upperCapCarrier := by
  unfold upperCapCarrier
  exact (isClosed_disk raw.upperCenter raw.sourceRadius).inter
    (isClosed_le continuous_const continuous_snd)

theorem isClosed_lowerCapCarrier : IsClosed raw.lowerCapCarrier := by
  unfold lowerCapCarrier
  exact (isClosed_disk raw.lowerCenter raw.sourceRadius).inter
    (isClosed_le continuous_snd continuous_const)

theorem isClosed_centeredCarrier : IsClosed raw.centeredCarrier := by
  unfold centeredCarrier
  exact (((raw.isClosed_rectangleCarrier.union
    raw.isClosed_leftSegmentCarrier).union
      raw.isClosed_rightSegmentCarrier).union
        raw.isClosed_upperCapCarrier).union raw.isClosed_lowerCapCarrier

/-- The independently defined raw source carrier is Borel measurable, without
using the later identification with a modeled candidate. -/
theorem isClosed_carrier : IsClosed raw.carrier := by
  unfold carrier
  exact (horizontalTranslation raw.horizontalPlacement).isClosedMap
    raw.centeredCarrier raw.isClosed_centeredCarrier

theorem measurableSet_carrier : MeasurableSet raw.carrier :=
  raw.isClosed_carrier.measurableSet

/-- Half-width of a regular type-(iv) horizontal slice inside the strip.
The attachment estimate below proves that the two side disks and central
rectangle form one interval rather than three disconnected pieces. -/
def stripSectionHalfWidth (y : ℝ) : ℝ :=
  raw.sideCenterOffset + √(raw.sourceRadius ^ 2 - y ^ 2)

private theorem innerRadial_mul_radius_sq
    (h : raw.SatisfiesClosedGeometry) :
    (raw.sourceRadius * raw.innerRadial) ^ 2 =
      raw.sourceRadius ^ 2 - 1 := by
  have hR : 0 < raw.sourceRadius :=
    lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hcurv : raw.curvature = 1 / raw.sourceRadius := rfl
  have hrad : 0 ≤ 1 - raw.curvature ^ 2 := by
    rw [hcurv]
    have hdiv : 1 / raw.sourceRadius ≤ 1 :=
      (div_le_one hR).2 h.radius_ge_one
    have hdiv0 : 0 ≤ 1 / raw.sourceRadius := (one_div_pos.mpr hR).le
    nlinarith
  rw [innerRadial, mul_pow, Real.sq_sqrt hrad, hcurv]
  field_simp [ne_of_gt hR]

private theorem bridge_le_stripSqrt
    {y : ℝ} (h : raw.SatisfiesClosedGeometry) (hy : |y| < 1) :
    raw.sourceRadius * raw.innerRadial ≤
      √(raw.sourceRadius ^ 2 - y ^ 2) := by
  have hR : 0 < raw.sourceRadius :=
    lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hR1 := h.radius_ge_one
  have hyBounds := abs_lt.mp hy
  have hy' : y ^ 2 < 1 := by nlinarith
  have hrad : 0 ≤ raw.sourceRadius ^ 2 - y ^ 2 := by
    nlinarith [sq_nonneg (raw.sourceRadius - 1)]
  have hsqrt0 : 0 ≤ √(raw.sourceRadius ^ 2 - y ^ 2) := Real.sqrt_nonneg _
  have hinner0 : 0 ≤ raw.sourceRadius * raw.innerRadial :=
    mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hsqrt_sq :
      (√(raw.sourceRadius ^ 2 - y ^ 2)) ^ 2 =
        raw.sourceRadius ^ 2 - y ^ 2 := by
    exact Real.sq_sqrt hrad
  have hinner_sq := raw.innerRadial_mul_radius_sq h
  nlinarith

private theorem mem_carrier_iff_centered (x y : ℝ) :
    (x, y) ∈ raw.carrier ↔
      (x - raw.horizontalPlacement, y) ∈ raw.centeredCarrier := by
  unfold carrier
  constructor
  · rintro ⟨p, hp, heq⟩
    have hx : p.1 = x - raw.horizontalPlacement := by
      have := congrArg Prod.fst heq
      simp only [horizontalTranslation_apply] at this
      linarith
    have hy : p.2 = y := by
      have := congrArg Prod.snd heq
      simpa only [horizontalTranslation_apply] using this
    have hpEq : p = (x - raw.horizontalPlacement, y) :=
      Prod.ext hx hy
    rw [← hpEq]
    exact hp
  · intro hp
    refine ⟨(x - raw.horizontalPlacement, y), hp, ?_⟩
    rw [horizontalTranslation_apply]
    apply Prod.ext <;> simp

/-- On every strict interior height, the independently defined five-piece
carrier in the closed geometric domain has exactly one centered interval slice.
This includes the radius-one endpoint and is the coordinate counterpart of the
interval-slice geometry used before CMV Lemma 3.8 (printed page 15). -/
theorem horizontalSection_eq_Icc_of_abs_lt_one
    {y : ℝ} (h : raw.SatisfiesClosedGeometry) (hy : |y| < 1) :
    horizontalSection raw.carrier y =
      Icc (raw.horizontalPlacement - raw.stripSectionHalfWidth y)
        (raw.horizontalPlacement + raw.stripSectionHalfWidth y) := by
  have hR : 0 < raw.sourceRadius :=
    lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hsqrt0 :
      0 ≤ √(raw.sourceRadius ^ 2 - y ^ 2) := Real.sqrt_nonneg _
  have hR1 := h.radius_ge_one
  have hrad : 0 ≤ raw.sourceRadius ^ 2 - y ^ 2 := by
    have hyBounds := abs_lt.mp hy
    have hy' : y ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (raw.sourceRadius - 1)]
  have hsqrt_sq :
      (√(raw.sourceRadius ^ 2 - y ^ 2)) ^ 2 =
        raw.sourceRadius ^ 2 - y ^ 2 := Real.sq_sqrt hrad
  have hbridge := raw.bridge_le_stripSqrt h hy
  have hRinner0 : 0 ≤ raw.sourceRadius * raw.innerRadial :=
    mul_nonneg hR.le (Real.sqrt_nonneg _)
  have hsin0 : 0 ≤ Real.sin raw.exteriorHalfAngle := by
    exact (Real.sin_pos_of_pos_of_lt_pi h.exteriorHalfAngle_pos
      (lt_trans h.exteriorHalfAngle_lt_pi_div_two
        (by linarith [Real.pi_pos]))).le
  have hW0 : 0 ≤ raw.outerHalfWidth := by
    unfold outerHalfWidth
    exact mul_nonneg hR.le hsin0
  have hleft :
      -raw.stripSectionHalfWidth y ≤ -raw.outerHalfWidth := by
    unfold stripSectionHalfWidth sideCenterOffset outerHalfWidth
    linarith
  have hright :
      raw.outerHalfWidth ≤ raw.stripSectionHalfWidth y := by
    unfold stripSectionHalfWidth sideCenterOffset outerHalfWidth
    linarith
  have hB0 : 0 ≤ raw.stripSectionHalfWidth y :=
    hW0.trans hright
  ext x
  rw [show x ∈ horizontalSection raw.carrier y ↔
      (x, y) ∈ raw.carrier from Iff.rfl]
  rw [raw.mem_carrier_iff_centered]
  simp only [centeredCarrier, rectangleCarrier, leftSegmentCarrier,
    rightSegmentCarrier, upperCapCarrier, lowerCapCarrier, leftCenter,
    rightCenter, upperCenter, lowerCenter, Set.mem_union, Set.mem_ofPred_eq,
    sub_zero, Set.mem_Icc]
  have hnotUpper : ¬(1 ≤ y) := not_le.mpr (abs_lt.mp hy).2
  have hnotLower : ¬(y ≤ -1) := not_le.mpr (abs_lt.mp hy).1
  simp only [hnotUpper, hnotLower, and_false, or_false]
  constructor
  · intro hx
    rcases hx with (hrect | hleftSeg) | hrightSeg
    · constructor <;>
        unfold stripSectionHalfWidth at hleft hright ⊢ <;> linarith
    · rcases hleftSeg with ⟨hdisk, hxside, _⟩
      constructor
      · unfold stripSectionHalfWidth sideCenterOffset at *
        nlinarith
      · unfold stripSectionHalfWidth at hright hB0 ⊢
        unfold outerHalfWidth at hxside hW0
        linarith
    · rcases hrightSeg with ⟨hdisk, hxside, _⟩
      constructor
      · unfold stripSectionHalfWidth at hleft hB0 ⊢
        unfold outerHalfWidth at hxside hW0
        linarith
      · unfold stripSectionHalfWidth sideCenterOffset at *
        nlinarith
  · rintro ⟨hxlo, hxhi⟩
    by_cases hxLeft : x - raw.horizontalPlacement ≤ -raw.outerHalfWidth
    · left; right
      refine ⟨?_, hxLeft, (le_of_lt hy)⟩
      unfold stripSectionHalfWidth sideCenterOffset at hxlo
      unfold sideCenterOffset at ⊢
      unfold outerHalfWidth at hxLeft
      nlinarith
    · by_cases hxRight : raw.outerHalfWidth ≤ x - raw.horizontalPlacement
      · right
        refine ⟨?_, hxRight, (le_of_lt hy)⟩
        unfold stripSectionHalfWidth sideCenterOffset at hxhi
        unfold sideCenterOffset at ⊢
        unfold outerHalfWidth at hxRight
        nlinarith
      · left; left
        exact ⟨le_of_not_ge hxLeft, le_of_not_ge hxRight, le_of_lt hy⟩

/-- A slice shape allowing the empty exterior slices as well as a centered
closed interval. The exact endpoint convention is immaterial in the later
almost-everywhere source comparison. -/
def IsEmptyOrCenteredClosedInterval (center : ℝ) (slice : Set ℝ) : Prop :=
  slice = ∅ ∨
    ∃ radius : ℝ, 0 ≤ radius ∧
      slice = Icc (center - radius) (center + radius)

private theorem stripSectionHalfWidth_nonneg
    {y : ℝ} (h : raw.SatisfiesClosedGeometry) (hy : |y| < 1) :
    0 ≤ raw.stripSectionHalfWidth y := by
  have hR : 0 < raw.sourceRadius :=
    lt_of_lt_of_le zero_lt_one h.radius_ge_one
  have hbridge := raw.bridge_le_stripSqrt h hy
  have hsin0 : 0 ≤ Real.sin raw.exteriorHalfAngle :=
    (Real.sin_pos_of_pos_of_lt_pi h.exteriorHalfAngle_pos
      (lt_trans h.exteriorHalfAngle_lt_pi_div_two
        (by linarith [Real.pi_pos]))).le
  unfold stripSectionHalfWidth sideCenterOffset
  nlinarith [mul_nonneg hR.le hsin0]

private theorem horizontalSection_cap
    (y centerY : ℝ)
    (hsection :
      horizontalSection raw.carrier y =
        {x : ℝ | (x - raw.horizontalPlacement) ^ 2 +
          (y - centerY) ^ 2 ≤ raw.sourceRadius ^ 2}) :
    IsEmptyOrCenteredClosedInterval raw.horizontalPlacement
      (horizontalSection raw.carrier y) := by
  let q := raw.sourceRadius ^ 2 - (y - centerY) ^ 2
  by_cases hq : 0 ≤ q
  · right
    refine ⟨√q, Real.sqrt_nonneg _, ?_⟩
    rw [hsection]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    have hsqrt0 : 0 ≤ √q := Real.sqrt_nonneg _
    have hsqrt_sq : (√q) ^ 2 = q := Real.sq_sqrt hq
    dsimp only [q] at hsqrt_sq
    constructor
    · intro hx
      constructor <;> nlinarith
    · rintro ⟨hxlo, hxhi⟩
      nlinarith
  · left
    rw [hsection]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    have hqneg : q < 0 := lt_of_not_ge hq
    dsimp only [q] at hqneg
    nlinarith [sq_nonneg (x - raw.horizontalPlacement)]

private theorem horizontalSection_eq_upperCap_of_one_lt
    {y : ℝ} (hy : 1 < y) :
    horizontalSection raw.carrier y =
      {x : ℝ | (x - raw.horizontalPlacement) ^ 2 +
        (y - raw.upperCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2} := by
  ext x
  rw [show x ∈ horizontalSection raw.carrier y ↔
      (x, y) ∈ raw.carrier from Iff.rfl]
  rw [raw.mem_carrier_iff_centered]
  simp only [centeredCarrier, rectangleCarrier, leftSegmentCarrier,
    rightSegmentCarrier, upperCapCarrier, lowerCapCarrier, leftCenter,
    rightCenter, upperCenter, Set.mem_union, Set.mem_ofPred_eq, sub_zero]
  have habs : ¬(|y| ≤ 1) := by
    rw [not_le]
    exact hy.trans_le (le_abs_self y)
  have hnotLower : ¬(y ≤ -1) := by linarith
  simp only [habs, and_false, or_false, false_or, hnotLower, hy.le, and_true]

private theorem horizontalSection_eq_lowerCap_of_lt_neg_one
    {y : ℝ} (hy : y < -1) :
    horizontalSection raw.carrier y =
      {x : ℝ | (x - raw.horizontalPlacement) ^ 2 +
        (y - raw.lowerCenter.2) ^ 2 ≤ raw.sourceRadius ^ 2} := by
  ext x
  rw [show x ∈ horizontalSection raw.carrier y ↔
      (x, y) ∈ raw.carrier from Iff.rfl]
  rw [raw.mem_carrier_iff_centered]
  simp only [centeredCarrier, rectangleCarrier, leftSegmentCarrier,
    rightSegmentCarrier, upperCapCarrier, lowerCapCarrier, leftCenter,
    rightCenter, lowerCenter, Set.mem_union, Set.mem_ofPred_eq, sub_zero]
  have habs : ¬(|y| ≤ 1) := by
    rw [not_le]
    have : 1 < -y := by linarith
    exact this.trans_le (neg_le_abs y)
  have hnotUpper : ¬(1 ≤ y) := by linarith
  simp only [habs, and_false, or_false, false_or, hnotUpper, hy.le, and_true]

/-- Every horizontal slice of a raw closed-geometric type-(iv) carrier, except
the two null interface heights, is either empty or one closed interval centered
on its vertical reflection axis.  The proof includes `sourceRadius = 1` and
uses no density or contact law. -/
theorem ae_horizontalSection_empty_or_centered_interval
    (h : raw.SatisfiesClosedGeometry) :
    ∀ᵐ y ∂(volume : Measure ℝ),
      IsEmptyOrCenteredClosedInterval raw.horizontalPlacement
        (horizontalSection raw.carrier y) := by
  filter_upwards [(volume : Measure ℝ).ae_ne (-1),
    (volume : Measure ℝ).ae_ne 1] with y hyNeg hyPos
  rcases lt_or_gt_of_ne hyNeg with hyLt | hyGt
  · exact raw.horizontalSection_cap y raw.lowerCenter.2
      (raw.horizontalSection_eq_lowerCap_of_lt_neg_one hyLt)
  · rcases lt_or_gt_of_ne hyPos with hyMid | hyUpper
    · right
      have hyAbs : |y| < 1 := (abs_lt).2 ⟨hyGt, hyMid⟩
      exact ⟨raw.stripSectionHalfWidth y,
        raw.stripSectionHalfWidth_nonneg h hyAbs,
        raw.horizontalSection_eq_Icc_of_abs_lt_one h hyAbs⟩
    · exact raw.horizontalSection_cap y raw.upperCenter.2
        (raw.horizontalSection_eq_upperCap_of_one_lt hyUpper)

end RawFourArcCoordinates

/-- Almost every horizontal section is, modulo one-dimensional null sets, an
interval of nonnegative length centered on one fixed vertical axis. Proposition
3.6 and Proposition 3.9 (printed pages 14 and 18) supply exactly these two
source-side facts for a planar isoperimetric region after the still-unformalized
regularity and equality-case arguments. -/
def HasCenteredHorizontalIntervalSections
    (axis : ℝ) (carrier : Set PlanePoint) : Prop :=
  ∀ᵐ y ∂(volume : Measure ℝ),
    ∃ length : ℝ, 0 ≤ length ∧
      horizontalSection carrier y =ᵐ[volume]
        Icc (axis - length / 2) (axis + length / 2)

/-- The raw five-piece type-(iv) carrier satisfies the centered-interval side
of the source classification interface throughout the closed geometric domain.
Empty exterior slices are represented modulo null sets by a zero-length
interval. -/
theorem RawFourArcCoordinates.hasCenteredHorizontalIntervalSections
    (raw : RawFourArcCoordinates) (h : raw.SatisfiesClosedGeometry) :
    HasCenteredHorizontalIntervalSections
      raw.horizontalPlacement raw.carrier := by
  filter_upwards [raw.ae_horizontalSection_empty_or_centered_interval h]
    with y hy
  rcases hy with hempty | ⟨radius, hradius, hslice⟩
  · refine ⟨0, le_rfl, ?_⟩
    rw [hempty]
    simp only [zero_div, sub_zero, add_zero, Set.Icc_self]
    exact (ae_eq_empty.mpr (measure_singleton raw.horizontalPlacement)).symm
  · refine ⟨2 * radius, mul_nonneg (by norm_num) hradius, ?_⟩
    rw [hslice]
    apply Filter.EventuallyEq.of_eq
    congr 1 <;> ring

/-- The output expected from CMV's interval-slice classification: almost every
horizontal slice of the source representative agrees almost everywhere with
the corresponding interval slice of the explicit five-piece source carrier. -/
def HasTypeIVHorizontalSections
    (sourceCarrier : Set PlanePoint) (raw : RawFourArcCoordinates) : Prop :=
  ∀ᵐ y ∂(volume : Measure ℝ),
    horizontalSection sourceCarrier y =ᵐ[volume]
      horizontalSection raw.carrier y

/-- The equality-case output of Schwarz symmetrization determines the original
type-(iv) carrier sectionwise. The hypotheses separate the two source facts:
Proposition 3.6 and Proposition 3.9 give intervals centered on one vertical
axis, while equation (21) and the definition of Schwarz symmetrization
(printed page 14) preserve each horizontal slice measure. The raw interval
geometry is proved above from the five independent coordinate pieces.

This theorem assumes neither planar almost-everywhere equality, horizontal
congruence, density, nor a contact law. Deriving its two source hypotheses from
every admissible regular type-(iv) minimizer remains the GMT equality-case
obligation. -/
theorem hasTypeIVHorizontalSections_of_centeredIntervals_of_measure_eq
    {sourceCarrier : Set PlanePoint}
    (raw : RawFourArcCoordinates)
    (hgeometry : raw.SatisfiesClosedGeometry)
    (hsource : HasCenteredHorizontalIntervalSections
      raw.horizontalPlacement sourceCarrier)
    (hmeasure : ∀ᵐ y ∂(volume : Measure ℝ),
      volume (horizontalSection sourceCarrier y) =
        volume (horizontalSection raw.carrier y)) :
    HasTypeIVHorizontalSections sourceCarrier raw := by
  have hraw :=
    raw.hasCenteredHorizontalIntervalSections hgeometry
  filter_upwards [hsource, hraw, hmeasure] with
    y hsource_y hraw_y hmeasure_y
  rcases hsource_y with
    ⟨sourceLength, hsourceLength, hsourceSection⟩
  rcases hraw_y with
    ⟨rawLength, hrawLength, hrawSection⟩
  have hlength : sourceLength = rawLength := by
    have hinterval :
        volume (Icc
          (raw.horizontalPlacement - sourceLength / 2)
          (raw.horizontalPlacement + sourceLength / 2)) =
        volume (Icc
          (raw.horizontalPlacement - rawLength / 2)
          (raw.horizontalPlacement + rawLength / 2)) := by
      rw [← measure_congr hsourceSection, ← measure_congr hrawSection]
      exact hmeasure_y
    simp only [Real.volume_Icc] at hinterval
    rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)]
      at hinterval
    linarith
  exact hsourceSection.trans (hlength ▸ hrawSection.symm)

/-- Sectionwise type-(iv) classification reconstructs the planar source
representative up to the null sets intrinsic to finite-perimeter semantics. -/
theorem sourceCarrier_ae_rawCarrier_of_horizontalSections
    {sourceCarrier : Set PlanePoint} (raw : RawFourArcCoordinates)
    (hsource : NullMeasurableSet sourceCarrier volume)
    (hsections : HasTypeIVHorizontalSections sourceCarrier raw) :
    sourceCarrier =ᵐ[volume] raw.carrier :=
  ae_eq_of_ae_horizontalSection_eq hsource
    raw.measurableSet_carrier.nullMeasurableSet hsections

/-- The checked scalar/source reduction consumes sectionwise classification,
not a caller-supplied planar congruence theorem. -/
theorem almostEverywhereHorizontallyCongruent_profile_of_horizontalSections
    {lam : ℝ} {sourceCarrier : Set PlanePoint}
    (raw : RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsource : NullMeasurableSet sourceCarrier volume)
    (hsections : HasTypeIVHorizontalSections sourceCarrier raw) :
    AlmostEverywhereHorizontallyCongruent sourceCarrier
      (raw.toCanonicalProfile hregular).carrier :=
  raw.almostEverywhereHorizontallyCongruent_profile_of_ae hregular
    (sourceCarrier_ae_rawCarrier_of_horizontalSections raw hsource hsections)

end CMVSourceClassification
