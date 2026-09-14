import CMVFiniteBandCosts

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement

/-- `weightedTraceCost` is additive over a countable measurable trace family
whose pairwise intersections are finite.  This is the form needed for closed
graphs: adjacent traces may share endpoints, but those endpoints carry no
Euclidean `H¹` measure. -/
theorem weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite
    {ι : Type*} [Countable ι] (lam : ℝ) (S : ι → Set PlanePoint)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hfinite : ∀ ⦃i j⦄, i ≠ j → (S i ∩ S j).Finite) :
    weightedTraceCost lam (⋃ i, S i) = ∑' i, weightedTraceCost lam (S i) := by
  have himageMeas (i : ι) : MeasurableSet
      (planeEuclideanHomeomorph '' S i) :=
    (planeEuclideanHomeomorph.continuous.measurableEmbedding
      planeEuclideanHomeomorph.injective).measurableSet_image' (hmeas i)
  have himagePair : Pairwise (AEDisjoint (μH[1] : Measure EuclideanPlane) on
      fun i : ι => planeEuclideanHomeomorph '' S i) := by
    intro i j hij
    change (μH[1] : Measure EuclideanPlane)
      ((planeEuclideanHomeomorph '' S i) ∩
        (planeEuclideanHomeomorph '' S j)) = 0
    let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
      Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
    rw [← Set.image_inter planeEuclideanHomeomorph.injective]
    exact ((hfinite hij).image planeEuclideanHomeomorph).measure_zero
      (μH[1] : Measure EuclideanPlane)
  unfold weightedTraceCost
  rw [image_iUnion, lintegral_iUnion₀
    (fun i => (himageMeas i).nullMeasurableSet) himagePair]

/-- Binary additivity when two measurable traces overlap in only finitely many
points. -/
theorem weightedTraceCost_union_eq_add_of_inter_finite (lam : ℝ)
    {S T : Set PlanePoint} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hfinite : (S ∩ T).Finite) :
    weightedTraceCost lam (S ∪ T) =
      weightedTraceCost lam S + weightedTraceCost lam T := by
  rw [union_eq_iUnion,
    weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite lam]
  · rw [tsum_fintype, Fintype.sum_bool]
    simp
  · intro b
    cases b <;> assumption
  · intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [cond_false, cond_true, inter_comm] using hfinite
    · simpa only [cond_false, cond_true] using hfinite
    · exact (hbc rfl).elim

/-- Finite index of every left or right endpoint graph in a region.  `false`
denotes a left graph and `true` a right graph. -/
abbrev GraphIndex (R : Region) :=
  Σ i : Fin R.bandCount, Fin (R.componentCount i) × Bool

/-- Endpoint value selected by a `GraphIndex`. -/
def Region.indexedGraphValue (R : Region) (q : GraphIndex R) (y : ℝ) : ℝ :=
  if q.2.2 then R.right q.1 q.2.1 y else R.left q.1 q.2.1 y

/-- Closed endpoint graph selected by a `GraphIndex`. -/
def Region.indexedGraphTrace (R : Region) (q : GraphIndex R) : Set PlanePoint :=
  (fun y => (R.indexedGraphValue q y, y)) ''
    Icc (R.cuts q.1.castSucc) (R.cuts q.1.succ)

@[simp] theorem Region.indexedGraphValue_left (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.indexedGraphValue ⟨i, j, false⟩ = R.left i j := rfl

@[simp] theorem Region.indexedGraphValue_right (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.indexedGraphValue ⟨i, j, true⟩ = R.right i j := rfl

@[simp] theorem Region.indexedGraphTrace_left (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.indexedGraphTrace ⟨i, j, false⟩ = R.leftGraphTrace i j := rfl

@[simp] theorem Region.indexedGraphTrace_right (R : Region)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    R.indexedGraphTrace ⟨i, j, true⟩ = R.rightGraphTrace i j := rfl

/-- The literal graph trace is exactly the finite union indexed by
`GraphIndex`. -/
theorem Region.graphTrace_eq_iUnion_indexedGraphTrace (R : Region) :
    R.graphTrace = ⋃ q : GraphIndex R, R.indexedGraphTrace q := by
  ext p
  constructor
  · intro hp
    rw [Region.graphTrace, mem_iUnion] at hp
    rcases hp with ⟨i, hp⟩
    rw [mem_iUnion] at hp
    rcases hp with ⟨j, hp | hp⟩
    · rw [mem_iUnion]
      refine ⟨⟨i, j, false⟩, ?_⟩
      simpa only [Region.indexedGraphTrace_left] using hp
    · rw [mem_iUnion]
      refine ⟨⟨i, j, true⟩, ?_⟩
      simpa only [Region.indexedGraphTrace_right] using hp
  · intro hp
    rw [mem_iUnion] at hp
    rcases hp with ⟨⟨i, j, side⟩, hp⟩
    rw [Region.graphTrace, mem_iUnion]
    refine ⟨i, ?_⟩
    rw [mem_iUnion]
    refine ⟨j, ?_⟩
    cases side with
    | false =>
        left
        simpa only [Region.indexedGraphTrace_left] using hp
    | true =>
        right
        simpa only [Region.indexedGraphTrace_right] using hp

/-- At an interior height, all selected endpoint values in one band are
distinct.  This packages component separation and positive component width. -/
theorem Region.indexedGraphValue_injective (R : Region)
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    Function.Injective (fun q : Fin (R.componentCount i) × Bool =>
      R.indexedGraphValue ⟨i, q⟩ y) := by
  rintro ⟨j, sj⟩ ⟨k, sk⟩ hvalue
  cases sj <;> cases sk
  · simp only [Region.indexedGraphValue, Bool.false_eq_true, ↓reduceIte] at hvalue
    have hjk : j = k := by
      by_contra hjk
      rcases lt_or_gt_of_ne hjk with hjk | hkj
      · have hsep := R.components_strict i hjk y hy
        have hw := R.width_pos i j y hy
        linarith
      · have hsep := R.components_strict i hkj y hy
        have hw := R.width_pos i k y hy
        linarith
    subst k
    rfl
  · simp only [Region.indexedGraphValue, Bool.false_eq_true, ↓reduceIte] at hvalue
    by_cases hjk : j = k
    · subst k
      linarith [R.width_pos i j y hy]
    · rcases lt_or_gt_of_ne hjk with hjk | hkj
      · have hsep := R.components_strict i hjk y hy
        have hwj := R.width_pos i j y hy
        have hwk := R.width_pos i k y hy
        linarith
      · linarith [R.components_strict i hkj y hy]
  · simp only [Region.indexedGraphValue, Bool.false_eq_true, ↓reduceIte] at hvalue
    by_cases hjk : j = k
    · subst k
      linarith [R.width_pos i j y hy]
    · rcases lt_or_gt_of_ne hjk with hjk | hkj
      · linarith [R.components_strict i hjk y hy]
      · have hsep := R.components_strict i hkj y hy
        have hwj := R.width_pos i j y hy
        have hwk := R.width_pos i k y hy
        linarith
  · simp only [Region.indexedGraphValue, ↓reduceIte] at hvalue
    have hjk : j = k := by
      by_contra hjk
      rcases lt_or_gt_of_ne hjk with hjk | hkj
      · have hsep := R.components_strict i hjk y hy
        have hw := R.width_pos i k y hy
        linarith
      · have hsep := R.components_strict i hkj y hy
        have hw := R.width_pos i j y hy
        linarith
    subst k
    rfl

/-- Two distinct closed endpoint graphs meet only at finitely many cut
endpoints. -/
theorem Region.indexedGraphTrace_inter_finite (R : Region)
    {q r : GraphIndex R} (hqr : q ≠ r) :
    (R.indexedGraphTrace q ∩ R.indexedGraphTrace r).Finite := by
  rcases q with ⟨i, q⟩
  rcases r with ⟨k, r⟩
  have hendFinite :
      ((fun y => (R.indexedGraphValue ⟨i, q⟩ y, y)) ''
        ({R.cuts i.castSucc, R.cuts i.succ} : Set ℝ)).Finite :=
    ((Set.finite_singleton _).insert _).image _
  apply hendFinite.subset
  rintro p ⟨hpq, hpr⟩
  rcases hpq with ⟨y, hy, rfl⟩
  rcases hpr with ⟨z, hz, heq⟩
  have hyz : y = z := by
    simpa using (congrArg Prod.snd heq).symm
  subst z
  by_cases hyleft : y = R.cuts i.castSucc
  · subst y
    exact ⟨R.cuts i.castSucc, by simp, rfl⟩
  by_cases hyright : y = R.cuts i.succ
  · subst y
    exact ⟨R.cuts i.succ, by simp, rfl⟩
  exfalso
  have hyOpen : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) :=
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hyleft),
      lt_of_le_of_ne hy.2 hyright⟩
  have hki : k = i := R.band_eq_of_height_mem_Ioo_mem_Icc i k hyOpen hz
  subst k
  have hvalue : R.indexedGraphValue ⟨i, q⟩ y =
      R.indexedGraphValue ⟨i, r⟩ y := (congrArg Prod.fst heq).symm
  have hqreq : q = r := R.indexedGraphValue_injective i hyOpen hvalue
  subst r
  exact hqr rfl

/-- Every indexed graph trace is measurable. -/
theorem Region.measurableSet_indexedGraphTrace (R : Region)
    (q : GraphIndex R) : MeasurableSet (R.indexedGraphTrace q) := by
  rcases q with ⟨i, j, side⟩
  apply measurableSet_verticalGraph_image
  · cases side with
    | false =>
        change Continuous (R.left i j)
        exact R.left_continuous i j
    | true =>
        change Continuous (R.right i j)
        exact R.right_continuous i j
  · exact measurableSet_Icc

/-- Exact density-weighted graph-speed term selected by one graph index. -/
def Region.indexedGraphSpeedCost (R : Region) (lam : ℝ)
    (q : GraphIndex R) : ENNReal :=
  (∫⁻ y in Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ) ∩
      {y : ℝ | |y| ≤ 1},
    ENNReal.ofReal (Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2))) +
  ENNReal.ofReal lam *
    ∫⁻ y in Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ) \
        {y : ℝ | |y| ≤ 1},
      ENNReal.ofReal (Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2))

/-- One indexed closed graph has exactly its displayed density-zone speed
cost. -/
theorem Region.weightedTraceCost_indexedGraphTrace (R : Region) (lam : ℝ)
    (q : GraphIndex R) :
    weightedTraceCost lam (R.indexedGraphTrace q) =
      R.indexedGraphSpeedCost lam q := by
  rcases q with ⟨i, j, side⟩
  cases side with
  | false =>
      simpa only [Region.indexedGraphTrace_left, Region.indexedGraphSpeedCost,
        Region.indexedGraphValue_left] using R.weightedTraceCost_leftGraphTrace lam i j
  | true =>
      simpa only [Region.indexedGraphTrace_right, Region.indexedGraphSpeedCost,
        Region.indexedGraphValue_right] using R.weightedTraceCost_rightGraphTrace lam i j

/-- Exact finite sum of all density-weighted endpoint graph-speed integrals. -/
theorem Region.weightedTraceCost_graphTrace (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.graphTrace =
      ∑ q : GraphIndex R, R.indexedGraphSpeedCost lam q := by
  rw [R.graphTrace_eq_iUnion_indexedGraphTrace,
    weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite lam
      R.indexedGraphTrace R.measurableSet_indexedGraphTrace
      (by
        intro q r hqr
        exact R.indexedGraphTrace_inter_finite hqr),
    tsum_fintype]
  exact Finset.sum_congr rfl fun q _ => R.weightedTraceCost_indexedGraphTrace lam q

/-- Closed component intervals are pairwise disjoint modulo at most one common
endpoint, including at band cuts where strict separation may degenerate. -/
theorem Region.pairwise_aedisjoint_componentIntervals (R : Region)
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    Pairwise (AEDisjoint volume on fun j : Fin (R.componentCount i) =>
      Icc (R.left i j y) (R.right i j y)) := by
  intro j k hjk
  change volume
    (Icc (R.left i j y) (R.right i j y) ∩
      Icc (R.left i k y) (R.right i k y)) = 0
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · apply measure_mono_null ?_ (measure_singleton (R.right i j y))
    intro x hx
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff] at hx ⊢
    exact le_antisymm hx.1.2
      ((R.components_ordered i hjk y hy).trans hx.2.1)
  · apply measure_mono_null ?_ (measure_singleton (R.right i k y))
    intro x hx
    simp only [mem_inter_iff, mem_Icc, mem_singleton_iff] at hx ⊢
    exact le_antisymm hx.2.2
      ((R.components_ordered i hkj y hy).trans hx.1.1)

/-- Exact one-dimensional measure of an actual one-sided fiber, including
degenerate components and non-strict contacts at either band endpoint. -/
theorem Region.volume_fiber_of_mem_Icc (R : Region) (i : Fin R.bandCount)
    {y : ℝ} (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    volume (R.fiber i y) = ENNReal.ofReal (R.totalWidth i y) := by
  rw [Region.fiber, measure_iUnion₀
    (R.pairwise_aedisjoint_componentIntervals i hy)
    (fun _ => measurableSet_Icc.nullMeasurableSet), tsum_fintype]
  simp_rw [Real.volume_Icc]
  rw [Region.totalWidth, ENNReal.ofReal_sum_of_nonneg]
  intro j _
  exact sub_nonneg.mpr (R.width_nonneg i j y hy)

/-- Horizontal traces are measurable whenever their one-dimensional source is. -/
lemma measurableSet_horizontal_image (h : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    MeasurableSet ((fun x : ℝ => (x, h)) '' s) :=
  ((continuous_id.prodMk continuous_const).measurableEmbedding fun x y hxy => by
    simpa using congrArg Prod.fst hxy).measurableSet_image' hs

theorem Region.lowerOuterTrace_eq_horizontal_image (R : Region) :
    R.lowerOuterTrace =
      (fun x : ℝ => (x, R.cuts R.firstBand.castSucc)) ''
        R.fiber R.firstBand (R.cuts R.firstBand.castSucc) := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩

theorem Region.upperOuterTrace_eq_horizontal_image (R : Region) :
    R.upperOuterTrace =
      (fun x : ℝ => (x, R.cuts R.lastBand.succ)) ''
        R.fiber R.lastBand (R.cuts R.lastBand.succ) := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩

theorem Region.seamSymmDiff_eq_horizontal_image (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamSymmDiff i =
      (fun x : ℝ => (x, R.seamHeight i)) ''
        (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.fiber (R.seamUpperBand i) (R.seamHeight i)) := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩

theorem Region.measurableSet_lowerOuterTrace (R : Region) :
    MeasurableSet R.lowerOuterTrace := by
  rw [R.lowerOuterTrace_eq_horizontal_image]
  exact measurableSet_horizontal_image _
    (R.isClosed_fiber R.firstBand _).measurableSet

theorem Region.measurableSet_upperOuterTrace (R : Region) :
    MeasurableSet R.upperOuterTrace := by
  rw [R.upperOuterTrace_eq_horizontal_image]
  exact measurableSet_horizontal_image _
    (R.isClosed_fiber R.lastBand _).measurableSet

theorem Region.measurableSet_seamSymmDiff (R : Region)
    (i : Fin (R.bandCount - 1)) :
    MeasurableSet (R.seamSymmDiff i) := by
  rw [R.seamSymmDiff_eq_horizontal_image]
  apply measurableSet_horizontal_image
  exact ((R.isClosed_fiber (R.seamLowerBand i) _).measurableSet.symmDiff
    (R.isClosed_fiber (R.seamUpperBand i) _).measurableSet)

/-- Exact lower outer-end cost at its actual strip density. -/
theorem Region.weightedTraceCost_lowerOuterTrace (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.lowerOuterTrace =
      ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
        volume (R.fiber R.firstBand (R.cuts R.firstBand.castSucc)) := by
  rw [R.lowerOuterTrace_eq_horizontal_image]
  exact weightedTraceCost_horizontal_image lam _
    (R.isClosed_fiber R.firstBand _).measurableSet

/-- Exact upper outer-end cost at its actual strip density. -/
theorem Region.weightedTraceCost_upperOuterTrace (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.upperOuterTrace =
      ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.lastBand.succ)) *
        volume (R.fiber R.lastBand (R.cuts R.lastBand.succ)) := by
  rw [R.upperOuterTrace_eq_horizontal_image]
  exact weightedTraceCost_horizontal_image lam _
    (R.isClosed_fiber R.lastBand _).measurableSet

/-- Exact cost of one original symmetric-difference seam.  In particular,
interfaces at `y = ±1` retain weight one through the literal `StripDensity`. -/
theorem Region.weightedTraceCost_seamSymmDiff (R : Region) (lam : ℝ)
    (i : Fin (R.bandCount - 1)) :
    weightedTraceCost lam (R.seamSymmDiff i) =
      ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
        volume
          (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
            R.fiber (R.seamUpperBand i) (R.seamHeight i)) := by
  rw [R.seamSymmDiff_eq_horizontal_image]
  exact weightedTraceCost_horizontal_image lam _
    ((R.isClosed_fiber (R.seamLowerBand i) _).measurableSet.symmDiff
      (R.isClosed_fiber (R.seamUpperBand i) _).measurableSet)

/-- All positive-length horizontal pieces of the original complete frontier.
Finite seam endpoint corrections are already present in `graphTrace`. -/
def Region.horizontalFrontierTrace (R : Region) : Set PlanePoint :=
  (R.lowerOuterTrace ∪ R.upperOuterTrace) ∪
    ⋃ i : Fin (R.bandCount - 1), R.seamSymmDiff i

lemma Region.lowerOuterHeight_lt_upperOuterHeight (R : Region) :
    R.cuts R.firstBand.castSucc < R.cuts R.lastBand.succ := by
  apply R.cuts_strict
  apply Fin.mk_lt_mk.mpr
  simp only [Region.firstBand_val]
  have hn := R.bandCount_pos
  omega

lemma Region.lowerOuterHeight_lt_seamHeight (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.cuts R.firstBand.castSucc < R.seamHeight i := by
  apply R.cuts_strict
  apply Fin.mk_lt_mk.mpr
  change 0 < i.val + 1
  omega

lemma Region.seamHeight_lt_upperOuterHeight (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.seamHeight i < R.cuts R.lastBand.succ := by
  apply R.cuts_strict
  apply Fin.mk_lt_mk.mpr
  simp only [Region.seamUpperBand_val]
  have hi := i.isLt
  have hn := R.bandCount_pos
  omega

lemma Region.seamHeight_injective (R : Region) :
    Function.Injective R.seamHeight := by
  intro i j hij
  apply Fin.ext
  have hcuts :
      (R.seamUpperBand i).castSucc = (R.seamUpperBand j).castSucc :=
    R.cuts_strict.injective hij
  have hvals := congrArg Fin.val hcuts
  simp only [Fin.val_castSucc, Region.seamUpperBand_val] at hvals
  omega

theorem Region.pairwise_disjoint_seamSymmDiff (R : Region) :
    Pairwise (Disjoint on R.seamSymmDiff) := by
  intro i j hij
  change Disjoint (R.seamSymmDiff i) (R.seamSymmDiff j)
  rw [Set.disjoint_left]
  intro p hpi hpj
  apply hij
  apply R.seamHeight_injective
  exact hpi.1.symm.trans hpj.1

theorem Region.disjoint_lowerOuterTrace_upperOuterTrace (R : Region) :
    Disjoint R.lowerOuterTrace R.upperOuterTrace := by
  rw [Set.disjoint_left]
  intro p hp hq
  linarith [R.lowerOuterHeight_lt_upperOuterHeight, hp.1, hq.1]

theorem Region.disjoint_lowerOuterTrace_seamSymmDiff (R : Region)
    (i : Fin (R.bandCount - 1)) :
    Disjoint R.lowerOuterTrace (R.seamSymmDiff i) := by
  rw [Set.disjoint_left]
  intro p hp hq
  linarith [R.lowerOuterHeight_lt_seamHeight i, hp.1, hq.1]

theorem Region.disjoint_upperOuterTrace_seamSymmDiff (R : Region)
    (i : Fin (R.bandCount - 1)) :
    Disjoint R.upperOuterTrace (R.seamSymmDiff i) := by
  rw [Set.disjoint_left]
  intro p hp hq
  linarith [R.seamHeight_lt_upperOuterHeight i, hp.1, hq.1]

theorem Region.measurableSet_horizontalFrontierTrace (R : Region) :
    MeasurableSet R.horizontalFrontierTrace := by
  unfold horizontalFrontierTrace
  exact (R.measurableSet_lowerOuterTrace.union
    R.measurableSet_upperOuterTrace).union
      (MeasurableSet.iUnion R.measurableSet_seamSymmDiff)

/-- The complete original trace is the graph union plus every positive-length
horizontal outer or seam trace.  Endpoint corrections disappear only because
they were proved to be contained in the closed graph trace. -/
theorem Region.completeFrontierTrace_eq_graph_union_horizontal (R : Region) :
    R.completeFrontierTrace = R.graphTrace ∪ R.horizontalFrontierTrace := by
  ext p
  constructor
  · rintro (((hp | hp) | hp) | hp)
    · exact Or.inl hp
    · exact Or.inr (Or.inl (Or.inl hp))
    · exact Or.inr (Or.inl (Or.inr hp))
    · rw [mem_iUnion] at hp
      rcases hp with ⟨i, hp⟩
      rw [R.seamFrontierTrace_eq_symmDiff_union_endpointSet i] at hp
      rcases hp with hp | hp
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i, hp⟩))
      · exact Or.inl (R.seamEndpointSet_subset_graphTrace i hp)
  · rintro (hp | (hp | hp) | hp)
    · exact Or.inl (Or.inl (Or.inl hp))
    · exact Or.inl (Or.inl (Or.inr hp))
    · exact Or.inl (Or.inr hp)
    · rw [mem_iUnion] at hp
      rcases hp with ⟨i, hp⟩
      exact Or.inr (mem_iUnion.mpr ⟨i, by
        rw [R.seamFrontierTrace_eq_symmDiff_union_endpointSet i]
        exact Or.inl hp⟩)

/-- A closed graph trace meets an arbitrary horizontal line in only finitely
many points. -/
theorem Region.graphTrace_inter_horizontalLine_finite (R : Region)
    (h : ℝ) (S : Set ℝ) :
    (R.graphTrace ∩ {p | p.2 = h ∧ p.1 ∈ S}).Finite := by
  apply (Set.finite_range
    (fun q : GraphIndex R => (R.indexedGraphValue q h, h))).subset
  rintro p ⟨hpGraph, hpLine⟩
  rw [R.graphTrace_eq_iUnion_indexedGraphTrace, mem_iUnion] at hpGraph
  rcases hpGraph with ⟨q, hpGraph⟩
  rcases hpGraph with ⟨y, _hy, rfl⟩
  have hyh := hpLine.1
  subst h
  exact ⟨q, rfl⟩

theorem Region.graphTrace_inter_horizontalFrontierTrace_finite (R : Region) :
    (R.graphTrace ∩ R.horizontalFrontierTrace).Finite := by
  let heights : Set ℝ := Set.range R.cuts
  have hsub :
      R.graphTrace ∩ R.horizontalFrontierTrace ⊆
        R.graphTrace ∩ {p | p.2 ∈ heights} := by
    rintro p ⟨hpGraph, hpHorizontal⟩
    refine ⟨hpGraph, ?_⟩
    change p ∈ (R.lowerOuterTrace ∪ R.upperOuterTrace) ∪
      ⋃ i : Fin (R.bandCount - 1), R.seamSymmDiff i at hpHorizontal
    rcases hpHorizontal with (hp | hp) | hp
    · exact ⟨R.firstBand.castSucc, hp.1.symm⟩
    · exact ⟨R.lastBand.succ, hp.1.symm⟩
    · rw [mem_iUnion] at hp
      rcases hp with ⟨i, hp⟩
      exact ⟨(R.seamUpperBand i).castSucc, hp.1.symm⟩
  apply (Set.finite_range
    (fun qk : GraphIndex R × Fin (R.bandCount + 1) =>
      (R.indexedGraphValue qk.1 (R.cuts qk.2), R.cuts qk.2))).subset
  intro p hp
  have hp' := hsub hp
  rcases hp' with ⟨hpGraph, k, hk⟩
  rw [R.graphTrace_eq_iUnion_indexedGraphTrace, mem_iUnion] at hpGraph
  rcases hpGraph with ⟨q, y, _hy, hqy⟩
  refine ⟨(q, k), ?_⟩
  have hyk : y = R.cuts k := (congrArg Prod.snd hqy).trans hk.symm
  subst y
  exact hqy

/-- Exact finite sum of all positive-length original horizontal traces. -/
theorem Region.weightedTraceCost_horizontalFrontierTrace (R : Region)
    (lam : ℝ) :
    weightedTraceCost lam R.horizontalFrontierTrace =
      (ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
        volume (R.fiber R.firstBand (R.cuts R.firstBand.castSucc)) +
       ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.lastBand.succ)) *
        volume (R.fiber R.lastBand (R.cuts R.lastBand.succ))) +
      ∑ i : Fin (R.bandCount - 1),
        ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
          volume
            (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
              R.fiber (R.seamUpperBand i) (R.seamHeight i)) := by
  have houter :
      weightedTraceCost lam (R.lowerOuterTrace ∪ R.upperOuterTrace) =
        weightedTraceCost lam R.lowerOuterTrace +
          weightedTraceCost lam R.upperOuterTrace :=
    weightedTraceCost_union_eq lam R.measurableSet_upperOuterTrace
      R.disjoint_lowerOuterTrace_upperOuterTrace
  have hseams :
      weightedTraceCost lam (⋃ i : Fin (R.bandCount - 1), R.seamSymmDiff i) =
        ∑ i : Fin (R.bandCount - 1), weightedTraceCost lam (R.seamSymmDiff i) := by
    rw [weightedTraceCost_iUnion_eq_tsum lam R.seamSymmDiff
      R.measurableSet_seamSymmDiff R.pairwise_disjoint_seamSymmDiff,
      tsum_fintype]
  have hdisjoint :
      Disjoint (R.lowerOuterTrace ∪ R.upperOuterTrace)
        (⋃ i : Fin (R.bandCount - 1), R.seamSymmDiff i) := by
    rw [Set.disjoint_left]
    rintro p (hp | hp) hseam
    · rw [mem_iUnion] at hseam
      rcases hseam with ⟨i, hpi⟩
      exact Set.disjoint_left.mp (R.disjoint_lowerOuterTrace_seamSymmDiff i) hp hpi
    · rw [mem_iUnion] at hseam
      rcases hseam with ⟨i, hpi⟩
      exact Set.disjoint_left.mp (R.disjoint_upperOuterTrace_seamSymmDiff i) hp hpi
  rw [Region.horizontalFrontierTrace,
    weightedTraceCost_union_eq lam
      (MeasurableSet.iUnion R.measurableSet_seamSymmDiff) hdisjoint,
    houter, hseams, R.weightedTraceCost_lowerOuterTrace,
    R.weightedTraceCost_upperOuterTrace]
  apply congrArg₂ (· + ·) rfl
  exact Finset.sum_congr rfl fun i _ => R.weightedTraceCost_seamSymmDiff lam i

/-- Complete exact original-frontier cost formula: a finite sum of actual
density-zone graph-speed integrals plus the two outer traces and every
one-sided symmetric-difference seam, each evaluated at its literal density. -/
theorem Region.weightedTraceCost_completeFrontierTrace (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeFrontierTrace =
      (∑ q : GraphIndex R, R.indexedGraphSpeedCost lam q) +
        ((ENNReal.ofReal
            (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
          volume (R.fiber R.firstBand (R.cuts R.firstBand.castSucc)) +
         ENNReal.ofReal
            (StripDensity lam (0, R.cuts R.lastBand.succ)) *
          volume (R.fiber R.lastBand (R.cuts R.lastBand.succ))) +
        ∑ i : Fin (R.bandCount - 1),
          ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
            volume
              (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
                R.fiber (R.seamUpperBand i) (R.seamHeight i))) := by
  rw [R.completeFrontierTrace_eq_graph_union_horizontal,
    weightedTraceCost_union_eq_add_of_inter_finite lam
      (by
        rw [R.graphTrace_eq_iUnion_indexedGraphTrace]
        exact MeasurableSet.iUnion R.measurableSet_indexedGraphTrace)
      R.measurableSet_horizontalFrontierTrace
      R.graphTrace_inter_horizontalFrontierTrace_finite,
    R.weightedTraceCost_graphTrace,
    R.weightedTraceCost_horizontalFrontierTrace]


/-- Finite index of the two centered endpoint graphs in each band. -/
abbrev CenteredGraphIndex (R : Region) := Fin R.bandCount × Bool

def Region.indexedCenteredGraphValue (R : Region)
    (q : CenteredGraphIndex R) (y : ℝ) : ℝ :=
  if q.2 then R.totalWidth q.1 y / 2 else -R.totalWidth q.1 y / 2

def Region.indexedCenteredGraphTrace (R : Region)
    (q : CenteredGraphIndex R) : Set PlanePoint :=
  (fun y => (R.indexedCenteredGraphValue q y, y)) ''
    Icc (R.cuts q.1.castSucc) (R.cuts q.1.succ)

@[simp] theorem Region.indexedCenteredGraphValue_left (R : Region)
    (i : Fin R.bandCount) :
    R.indexedCenteredGraphValue (i, false) =
      fun y => -R.totalWidth i y / 2 := rfl

@[simp] theorem Region.indexedCenteredGraphValue_right (R : Region)
    (i : Fin R.bandCount) :
    R.indexedCenteredGraphValue (i, true) =
      fun y => R.totalWidth i y / 2 := rfl

@[simp] theorem Region.indexedCenteredGraphTrace_left (R : Region)
    (i : Fin R.bandCount) :
    R.indexedCenteredGraphTrace (i, false) = R.centeredLeftGraphTrace i := rfl

@[simp] theorem Region.indexedCenteredGraphTrace_right (R : Region)
    (i : Fin R.bandCount) :
    R.indexedCenteredGraphTrace (i, true) = R.centeredRightGraphTrace i := rfl

theorem Region.centeredGraphTrace_eq_iUnion_indexedCenteredGraphTrace
    (R : Region) :
    R.centeredGraphTrace =
      ⋃ q : CenteredGraphIndex R, R.indexedCenteredGraphTrace q := by
  ext p
  constructor
  · intro hp
    rw [Region.centeredGraphTrace, mem_iUnion] at hp
    rcases hp with ⟨i, hp | hp⟩
    · rw [mem_iUnion]
      exact ⟨(i, false), by
        simpa only [R.indexedCenteredGraphTrace_left] using hp⟩
    · rw [mem_iUnion]
      exact ⟨(i, true), by
        simpa only [R.indexedCenteredGraphTrace_right] using hp⟩
  · intro hp
    rw [mem_iUnion] at hp
    rcases hp with ⟨⟨i, side⟩, hp⟩
    rw [Region.centeredGraphTrace, mem_iUnion]
    refine ⟨i, ?_⟩
    cases side with
    | false =>
        left
        simpa only [R.indexedCenteredGraphTrace_left] using hp
    | true =>
        right
        simpa only [R.indexedCenteredGraphTrace_right] using hp

theorem Region.indexedCenteredGraphTrace_inter_finite (R : Region)
    {q r : CenteredGraphIndex R} (hqr : q ≠ r) :
    (R.indexedCenteredGraphTrace q ∩
      R.indexedCenteredGraphTrace r).Finite := by
  rcases q with ⟨i, side⟩
  rcases r with ⟨k, other⟩
  have hendFinite :
      ((fun y => (R.indexedCenteredGraphValue (i, side) y, y)) ''
        ({R.cuts i.castSucc, R.cuts i.succ} : Set ℝ)).Finite :=
    ((Set.finite_singleton _).insert _).image _
  apply hendFinite.subset
  rintro p ⟨hpq, hpr⟩
  rcases hpq with ⟨y, hy, rfl⟩
  rcases hpr with ⟨z, hz, heq⟩
  have hyz : y = z := by
    simpa using (congrArg Prod.snd heq).symm
  subst z
  by_cases hyleft : y = R.cuts i.castSucc
  · subst y
    exact ⟨R.cuts i.castSucc, by simp, rfl⟩
  by_cases hyright : y = R.cuts i.succ
  · subst y
    exact ⟨R.cuts i.succ, by simp, rfl⟩
  exfalso
  have hyOpen : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) :=
    ⟨lt_of_le_of_ne hy.1 (Ne.symm hyleft),
      lt_of_le_of_ne hy.2 hyright⟩
  have hki : k = i := R.band_eq_of_height_mem_Ioo_mem_Icc i k hyOpen hz
  subst k
  have hvalue : R.indexedCenteredGraphValue (i, side) y =
      R.indexedCenteredGraphValue (i, other) y :=
    (congrArg Prod.fst heq).symm
  have hside : side = other := by
    cases side <;> cases other
    · rfl
    · simp only [Region.indexedCenteredGraphValue, Bool.false_eq_true,
        ↓reduceIte] at hvalue
      linarith [R.totalWidth_pos i hyOpen]
    · simp only [Region.indexedCenteredGraphValue, Bool.false_eq_true,
        ↓reduceIte] at hvalue
      linarith [R.totalWidth_pos i hyOpen]
    · rfl
  subst other
  exact hqr rfl

theorem Region.measurableSet_indexedCenteredGraphTrace (R : Region)
    (q : CenteredGraphIndex R) :
    MeasurableSet (R.indexedCenteredGraphTrace q) := by
  rcases q with ⟨i, side⟩
  apply measurableSet_verticalGraph_image
  · cases side with
    | false =>
        change Continuous (fun y => -R.totalWidth i y / 2)
        exact (R.continuous_totalWidth i).neg.div_const 2
    | true =>
        change Continuous (fun y => R.totalWidth i y / 2)
        exact (R.continuous_totalWidth i).div_const 2
  · exact measurableSet_Icc

def Region.indexedCenteredGraphSpeedCost (R : Region) (lam : ℝ)
    (q : CenteredGraphIndex R) : ENNReal :=
  (∫⁻ y in Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ) ∩
      {y : ℝ | |y| ≤ 1},
    ENNReal.ofReal
      (Real.sqrt (1 + deriv (R.indexedCenteredGraphValue q) y ^ 2))) +
  ENNReal.ofReal lam *
    ∫⁻ y in Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ) \
        {y : ℝ | |y| ≤ 1},
      ENNReal.ofReal
        (Real.sqrt (1 + deriv (R.indexedCenteredGraphValue q) y ^ 2))

theorem Region.weightedTraceCost_indexedCenteredGraphTrace
    (R : Region) (lam : ℝ) (q : CenteredGraphIndex R) :
    weightedTraceCost lam (R.indexedCenteredGraphTrace q) =
      R.indexedCenteredGraphSpeedCost lam q := by
  rcases q with ⟨i, side⟩
  cases side with
  | false =>
      simpa only [R.indexedCenteredGraphTrace_left,
        Region.indexedCenteredGraphSpeedCost,
        R.indexedCenteredGraphValue_left] using
          R.weightedTraceCost_centeredLeftGraphTrace lam i
  | true =>
      simpa only [R.indexedCenteredGraphTrace_right,
        Region.indexedCenteredGraphSpeedCost,
        R.indexedCenteredGraphValue_right] using
          R.weightedTraceCost_centeredRightGraphTrace lam i

theorem Region.weightedTraceCost_centeredGraphTrace (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.centeredGraphTrace =
      ∑ q : CenteredGraphIndex R, R.indexedCenteredGraphSpeedCost lam q := by
  rw [R.centeredGraphTrace_eq_iUnion_indexedCenteredGraphTrace,
    weightedTraceCost_iUnion_eq_tsum_of_pairwise_inter_finite lam
      R.indexedCenteredGraphTrace R.measurableSet_indexedCenteredGraphTrace
      (by
        intro q r hqr
        exact R.indexedCenteredGraphTrace_inter_finite hqr),
    tsum_fintype]
  exact Finset.sum_congr rfl fun q _ =>
    R.weightedTraceCost_indexedCenteredGraphTrace lam q

/-- Positive-length part of the centered frontier at one internal cut. -/
def Region.centeredSeamSymmDiffTrace (R : Region)
    (i : Fin (R.bandCount - 1)) : Set PlanePoint :=
  {p | p.2 = R.seamHeight i ∧
    p.1 ∈ R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
      R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)}

theorem Region.centeredLowerOuterTrace_eq_horizontal_image (R : Region) :
    R.centeredLowerOuterTrace =
      (fun x : ℝ => (x, R.cuts R.firstBand.castSucc)) ''
        R.centeredFiber R.firstBand (R.cuts R.firstBand.castSucc) := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩

theorem Region.centeredUpperOuterTrace_eq_horizontal_image (R : Region) :
    R.centeredUpperOuterTrace =
      (fun x : ℝ => (x, R.cuts R.lastBand.succ)) ''
        R.centeredFiber R.lastBand (R.cuts R.lastBand.succ) := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩

theorem Region.centeredSeamSymmDiffTrace_eq_horizontal_image (R : Region)
    (i : Fin (R.bandCount - 1)) :
    R.centeredSeamSymmDiffTrace i =
      (fun x : ℝ => (x, R.seamHeight i)) ''
        (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) := by
  ext p
  constructor
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩

theorem Region.measurableSet_centeredLowerOuterTrace (R : Region) :
    MeasurableSet R.centeredLowerOuterTrace := by
  rw [R.centeredLowerOuterTrace_eq_horizontal_image]
  exact measurableSet_horizontal_image _ measurableSet_Icc

theorem Region.measurableSet_centeredUpperOuterTrace (R : Region) :
    MeasurableSet R.centeredUpperOuterTrace := by
  rw [R.centeredUpperOuterTrace_eq_horizontal_image]
  exact measurableSet_horizontal_image _ measurableSet_Icc

theorem Region.measurableSet_centeredSeamSymmDiffTrace (R : Region)
    (i : Fin (R.bandCount - 1)) :
    MeasurableSet (R.centeredSeamSymmDiffTrace i) := by
  rw [R.centeredSeamSymmDiffTrace_eq_horizontal_image]
  exact measurableSet_horizontal_image _
    (measurableSet_Icc.symmDiff measurableSet_Icc)

theorem Region.weightedTraceCost_centeredLowerOuterTrace
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.centeredLowerOuterTrace =
      ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
        volume
          (R.centeredFiber R.firstBand (R.cuts R.firstBand.castSucc)) := by
  rw [R.centeredLowerOuterTrace_eq_horizontal_image]
  exact weightedTraceCost_horizontal_image lam _ measurableSet_Icc

theorem Region.weightedTraceCost_centeredUpperOuterTrace
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.centeredUpperOuterTrace =
      ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.lastBand.succ)) *
        volume
          (R.centeredFiber R.lastBand (R.cuts R.lastBand.succ)) := by
  rw [R.centeredUpperOuterTrace_eq_horizontal_image]
  exact weightedTraceCost_horizontal_image lam _ measurableSet_Icc

theorem Region.weightedTraceCost_centeredSeamSymmDiffTrace
    (R : Region) (lam : ℝ) (i : Fin (R.bandCount - 1)) :
    weightedTraceCost lam (R.centeredSeamSymmDiffTrace i) =
      ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
        volume
          (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
            R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) := by
  rw [R.centeredSeamSymmDiffTrace_eq_horizontal_image]
  exact weightedTraceCost_horizontal_image lam _
    (measurableSet_Icc.symmDiff measurableSet_Icc)

def Region.centeredHorizontalFrontierTrace (R : Region) : Set PlanePoint :=
  (R.centeredLowerOuterTrace ∪ R.centeredUpperOuterTrace) ∪
    ⋃ i : Fin (R.bandCount - 1), R.centeredSeamSymmDiffTrace i

theorem Region.pairwise_disjoint_centeredSeamSymmDiffTrace (R : Region) :
    Pairwise (Disjoint on R.centeredSeamSymmDiffTrace) := by
  intro i j hij
  change Disjoint (R.centeredSeamSymmDiffTrace i)
    (R.centeredSeamSymmDiffTrace j)
  rw [Set.disjoint_left]
  intro p hpi hpj
  apply hij
  apply R.seamHeight_injective
  exact hpi.1.symm.trans hpj.1

theorem Region.disjoint_centeredLowerOuterTrace_centeredUpperOuterTrace
    (R : Region) :
    Disjoint R.centeredLowerOuterTrace R.centeredUpperOuterTrace := by
  rw [Set.disjoint_left]
  intro p hp hq
  linarith [R.lowerOuterHeight_lt_upperOuterHeight, hp.1, hq.1]

theorem Region.disjoint_centeredLowerOuterTrace_centeredSeamSymmDiffTrace
    (R : Region) (i : Fin (R.bandCount - 1)) :
    Disjoint R.centeredLowerOuterTrace (R.centeredSeamSymmDiffTrace i) := by
  rw [Set.disjoint_left]
  intro p hp hq
  linarith [R.lowerOuterHeight_lt_seamHeight i, hp.1, hq.1]

theorem Region.disjoint_centeredUpperOuterTrace_centeredSeamSymmDiffTrace
    (R : Region) (i : Fin (R.bandCount - 1)) :
    Disjoint R.centeredUpperOuterTrace (R.centeredSeamSymmDiffTrace i) := by
  rw [Set.disjoint_left]
  intro p hp hq
  linarith [R.seamHeight_lt_upperOuterHeight i, hp.1, hq.1]

theorem Region.measurableSet_centeredHorizontalFrontierTrace (R : Region) :
    MeasurableSet R.centeredHorizontalFrontierTrace := by
  unfold centeredHorizontalFrontierTrace
  exact (R.measurableSet_centeredLowerOuterTrace.union
    R.measurableSet_centeredUpperOuterTrace).union
      (MeasurableSet.iUnion R.measurableSet_centeredSeamSymmDiffTrace)

theorem Region.completeCenteredFrontierTrace_eq_graph_union_horizontal
    (R : Region) :
    R.completeCenteredFrontierTrace =
      R.centeredGraphTrace ∪ R.centeredHorizontalFrontierTrace := by
  ext p
  constructor
  · rintro (((hp | hp) | hp) | hp)
    · exact Or.inl hp
    · exact Or.inr (Or.inl (Or.inl hp))
    · exact Or.inr (Or.inl (Or.inr hp))
    · rw [mem_iUnion] at hp
      rcases hp with ⟨i, hp⟩
      rw [R.centeredSeamFrontierTrace_eq_symmDiff_union_endpointSet i] at hp
      rcases hp with hp | hp
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨i, hp⟩))
      · exact Or.inl (R.centeredSeamEndpointSet_subset_centeredGraphTrace i hp)
  · rintro (hp | (hp | hp) | hp)
    · exact Or.inl (Or.inl (Or.inl hp))
    · exact Or.inl (Or.inl (Or.inr hp))
    · exact Or.inl (Or.inr hp)
    · rw [mem_iUnion] at hp
      rcases hp with ⟨i, hp⟩
      exact Or.inr (mem_iUnion.mpr ⟨i, by
        rw [R.centeredSeamFrontierTrace_eq_symmDiff_union_endpointSet i]
        exact Or.inl hp⟩)

theorem Region.centeredGraphTrace_inter_centeredHorizontalFrontierTrace_finite
    (R : Region) :
    (R.centeredGraphTrace ∩ R.centeredHorizontalFrontierTrace).Finite := by
  let heights : Set ℝ := Set.range R.cuts
  have hsub :
      R.centeredGraphTrace ∩ R.centeredHorizontalFrontierTrace ⊆
        R.centeredGraphTrace ∩ {p | p.2 ∈ heights} := by
    rintro p ⟨hpGraph, hpHorizontal⟩
    refine ⟨hpGraph, ?_⟩
    change p ∈
      (R.centeredLowerOuterTrace ∪ R.centeredUpperOuterTrace) ∪
        ⋃ i : Fin (R.bandCount - 1), R.centeredSeamSymmDiffTrace i
      at hpHorizontal
    rcases hpHorizontal with (hp | hp) | hp
    · exact ⟨R.firstBand.castSucc, hp.1.symm⟩
    · exact ⟨R.lastBand.succ, hp.1.symm⟩
    · rw [mem_iUnion] at hp
      rcases hp with ⟨i, hp⟩
      exact ⟨(R.seamUpperBand i).castSucc, hp.1.symm⟩
  apply (Set.finite_range
    (fun qk : CenteredGraphIndex R × Fin (R.bandCount + 1) =>
      (R.indexedCenteredGraphValue qk.1 (R.cuts qk.2), R.cuts qk.2))).subset
  intro p hp
  have hp' := hsub hp
  rcases hp' with ⟨hpGraph, k, hk⟩
  rw [R.centeredGraphTrace_eq_iUnion_indexedCenteredGraphTrace,
    mem_iUnion] at hpGraph
  rcases hpGraph with ⟨q, y, _hy, hqy⟩
  refine ⟨(q, k), ?_⟩
  have hyk : y = R.cuts k := (congrArg Prod.snd hqy).trans hk.symm
  subst y
  exact hqy

theorem Region.weightedTraceCost_centeredHorizontalFrontierTrace
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.centeredHorizontalFrontierTrace =
      (ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
        volume
          (R.centeredFiber R.firstBand (R.cuts R.firstBand.castSucc)) +
       ENNReal.ofReal
          (StripDensity lam (0, R.cuts R.lastBand.succ)) *
        volume
          (R.centeredFiber R.lastBand (R.cuts R.lastBand.succ))) +
      ∑ i : Fin (R.bandCount - 1),
        ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
          volume
            (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
              R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) := by
  have houter :
      weightedTraceCost lam
          (R.centeredLowerOuterTrace ∪ R.centeredUpperOuterTrace) =
        weightedTraceCost lam R.centeredLowerOuterTrace +
          weightedTraceCost lam R.centeredUpperOuterTrace :=
    weightedTraceCost_union_eq lam R.measurableSet_centeredUpperOuterTrace
      R.disjoint_centeredLowerOuterTrace_centeredUpperOuterTrace
  have hseams :
      weightedTraceCost lam
          (⋃ i : Fin (R.bandCount - 1), R.centeredSeamSymmDiffTrace i) =
        ∑ i : Fin (R.bandCount - 1),
          weightedTraceCost lam (R.centeredSeamSymmDiffTrace i) := by
    rw [weightedTraceCost_iUnion_eq_tsum lam R.centeredSeamSymmDiffTrace
      R.measurableSet_centeredSeamSymmDiffTrace
      R.pairwise_disjoint_centeredSeamSymmDiffTrace, tsum_fintype]
  have hdisjoint :
      Disjoint
        (R.centeredLowerOuterTrace ∪ R.centeredUpperOuterTrace)
        (⋃ i : Fin (R.bandCount - 1), R.centeredSeamSymmDiffTrace i) := by
    rw [Set.disjoint_left]
    rintro p (hp | hp) hseam
    · rw [mem_iUnion] at hseam
      rcases hseam with ⟨i, hpi⟩
      exact Set.disjoint_left.mp
        (R.disjoint_centeredLowerOuterTrace_centeredSeamSymmDiffTrace i) hp hpi
    · rw [mem_iUnion] at hseam
      rcases hseam with ⟨i, hpi⟩
      exact Set.disjoint_left.mp
        (R.disjoint_centeredUpperOuterTrace_centeredSeamSymmDiffTrace i) hp hpi
  rw [Region.centeredHorizontalFrontierTrace,
    weightedTraceCost_union_eq lam
      (MeasurableSet.iUnion R.measurableSet_centeredSeamSymmDiffTrace)
      hdisjoint,
    houter, hseams, R.weightedTraceCost_centeredLowerOuterTrace,
    R.weightedTraceCost_centeredUpperOuterTrace]
  apply congrArg₂ (· + ·) rfl
  exact Finset.sum_congr rfl fun i _ =>
    R.weightedTraceCost_centeredSeamSymmDiffTrace lam i

/-- Complete exact centered-frontier cost formula, with no topological
frontier identification inferred from planar almost-everywhere equality. -/
theorem Region.weightedTraceCost_completeCenteredFrontierTrace
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeCenteredFrontierTrace =
      (∑ q : CenteredGraphIndex R,
        R.indexedCenteredGraphSpeedCost lam q) +
        ((ENNReal.ofReal
            (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
          volume
            (R.centeredFiber R.firstBand (R.cuts R.firstBand.castSucc)) +
         ENNReal.ofReal
            (StripDensity lam (0, R.cuts R.lastBand.succ)) *
          volume
            (R.centeredFiber R.lastBand (R.cuts R.lastBand.succ))) +
        ∑ i : Fin (R.bandCount - 1),
          ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
            volume
              (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
                R.centeredFiber (R.seamUpperBand i) (R.seamHeight i))) := by
  rw [R.completeCenteredFrontierTrace_eq_graph_union_horizontal,
    weightedTraceCost_union_eq_add_of_inter_finite lam
      (by
        rw [R.centeredGraphTrace_eq_iUnion_indexedCenteredGraphTrace]
        exact MeasurableSet.iUnion R.measurableSet_indexedCenteredGraphTrace)
      R.measurableSet_centeredHorizontalFrontierTrace
      R.centeredGraphTrace_inter_centeredHorizontalFrontierTrace_finite,
    R.weightedTraceCost_centeredGraphTrace,
    R.weightedTraceCost_centeredHorizontalFrontierTrace]

/-- Integrable graph speed remains integrable after division by two. -/
lemma integrableOn_speed_div_two {g : ℝ → ℝ} {a b : ℝ}
    (hgC1 : ContDiffOn ℝ 1 g (Ioo a b))
    (hspeed : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2))
      (Ioo a b)) :
    IntegrableOn
      (fun y => Real.sqrt (1 + deriv (fun z => g z / 2) y ^ 2))
      (Ioo a b) := by
  apply hspeed.mono'
  · exact (by fun_prop : Measurable
      (fun y => Real.sqrt (1 + deriv (fun z => g z / 2) y ^ 2)))
      |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hdiff :=
      (hgC1.differentiableOn (by norm_num) y hy).differentiableAt
        (isOpen_Ioo.mem_nhds hy)
    have hscaled : HasDerivAt (fun z => g z / 2) (deriv g y / 2) y :=
      hdiff.hasDerivAt.div_const 2
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hscaled.deriv]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (deriv g y)]

/-- Integrable graph speed remains integrable after negation and division by
two. -/
lemma integrableOn_speed_neg_div_two {g : ℝ → ℝ} {a b : ℝ}
    (hgC1 : ContDiffOn ℝ 1 g (Ioo a b))
    (hspeed : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2))
      (Ioo a b)) :
    IntegrableOn
      (fun y => Real.sqrt (1 + deriv (fun z => -g z / 2) y ^ 2))
      (Ioo a b) := by
  apply hspeed.mono'
  · exact (by fun_prop : Measurable
      (fun y => Real.sqrt (1 + deriv (fun z => -g z / 2) y ^ 2)))
      |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hdiff :=
      (hgC1.differentiableOn (by norm_num) y hy).differentiableAt
        (isOpen_Ioo.mem_nhds hy)
    have hscaled : HasDerivAt (fun z => -g z / 2) (-deriv g y / 2) y :=
      hdiff.hasDerivAt.neg.div_const 2
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hscaled.deriv]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (deriv g y)]

lemma lintegral_ofReal_speed_ne_top {g : ℝ → ℝ} {s : Set ℝ}
    (hspeed : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) s) :
    (∫⁻ y in s, ENNReal.ofReal
      (Real.sqrt (1 + deriv g y ^ 2))) ≠ ⊤ := by
  have hfinite := hspeed.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at hfinite
  exact ne_of_lt (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
      hfinite)

theorem Region.indexedGraphSpeed_integrable (R : Region) (q : GraphIndex R) :
    IntegrableOn
      (fun y => Real.sqrt (1 + deriv (R.indexedGraphValue q) y ^ 2))
      (Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ)) := by
  rcases q with ⟨i, j, side⟩
  cases side with
  | false =>
      simpa only [R.indexedGraphValue_left] using R.left_speed_integrable i j
  | true =>
      simpa only [R.indexedGraphValue_right] using R.right_speed_integrable i j

theorem Region.indexedCenteredGraphSpeed_integrable
    (R : Region) (q : CenteredGraphIndex R) :
    IntegrableOn
      (fun y => Real.sqrt
        (1 + deriv (R.indexedCenteredGraphValue q) y ^ 2))
      (Ioo (R.cuts q.1.castSucc) (R.cuts q.1.succ)) := by
  rcases q with ⟨i, side⟩
  cases side with
  | false =>
      simpa only [R.indexedCenteredGraphValue_left] using
        integrableOn_speed_neg_div_two (R.totalWidth_contDiffOn i)
          (R.totalWidth_speed_integrable i)
  | true =>
      simpa only [R.indexedCenteredGraphValue_right] using
        integrableOn_speed_div_two (R.totalWidth_contDiffOn i)
          (R.totalWidth_speed_integrable i)

theorem Region.indexedGraphSpeedCost_ne_top (R : Region) (lam : ℝ)
    (q : GraphIndex R) : R.indexedGraphSpeedCost lam q ≠ ⊤ := by
  unfold indexedGraphSpeedCost
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply lintegral_ofReal_speed_ne_top
    exact (R.indexedGraphSpeed_integrable q).mono_set inter_subset_left
  · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply lintegral_ofReal_speed_ne_top
    exact (R.indexedGraphSpeed_integrable q).mono_set Set.sdiff_subset

theorem Region.indexedCenteredGraphSpeedCost_ne_top
    (R : Region) (lam : ℝ) (q : CenteredGraphIndex R) :
    R.indexedCenteredGraphSpeedCost lam q ≠ ⊤ := by
  unfold indexedCenteredGraphSpeedCost
  apply ENNReal.add_ne_top.mpr
  constructor
  · apply lintegral_ofReal_speed_ne_top
    exact (R.indexedCenteredGraphSpeed_integrable q).mono_set inter_subset_left
  · apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply lintegral_ofReal_speed_ne_top
    exact (R.indexedCenteredGraphSpeed_integrable q).mono_set Set.sdiff_subset

theorem Region.volume_fiber_ne_top_of_mem_Icc (R : Region)
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    volume (R.fiber i y) ≠ ⊤ := by
  rw [R.volume_fiber_of_mem_Icc i hy]
  exact ENNReal.ofReal_ne_top

theorem Region.volume_centeredFiber_ne_top (R : Region)
    (i : Fin R.bandCount) (y : ℝ) :
    volume (R.centeredFiber i y) ≠ ⊤ := by
  rw [Region.centeredFiber, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

lemma volume_symmDiff_ne_top_of_ne_top {S T : Set ℝ}
    (hS : volume S ≠ ⊤) (hT : volume T ≠ ⊤) :
    volume (S ∆ T) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (measure_union_ne_top hS hT)
  apply measure_mono
  rintro x (hx | hx)
  · exact Or.inl hx.1
  · exact Or.inr hx.1

theorem Region.volume_lowerOuterFiber_ne_top (R : Region) :
    volume (R.fiber R.firstBand (R.cuts R.firstBand.castSucc)) ≠ ⊤ :=
  R.volume_fiber_ne_top_of_mem_Icc R.firstBand
    ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩

theorem Region.volume_upperOuterFiber_ne_top (R : Region) :
    volume (R.fiber R.lastBand (R.cuts R.lastBand.succ)) ≠ ⊤ :=
  R.volume_fiber_ne_top_of_mem_Icc R.lastBand
    ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩

theorem Region.volume_seamSymmDiffFiber_ne_top (R : Region)
    (i : Fin (R.bandCount - 1)) :
    volume
      (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.fiber (R.seamUpperBand i) (R.seamHeight i)) ≠ ⊤ := by
  apply volume_symmDiff_ne_top_of_ne_top
  · apply R.volume_fiber_ne_top_of_mem_Icc
    rw [R.cuts_seamLower_succ i]
    exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
  · apply R.volume_fiber_ne_top_of_mem_Icc
    exact ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩

theorem Region.volume_centeredSeamSymmDiffFiber_ne_top (R : Region)
    (i : Fin (R.bandCount - 1)) :
    volume
      (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) ≠ ⊤ :=
  volume_symmDiff_ne_top_of_ne_top
    (R.volume_centeredFiber_ne_top _ _) (R.volume_centeredFiber_ne_top _ _)

/-- The exact original complete-frontier formula is finite before any
conversion to a real-valued perimeter. -/
theorem Region.weightedTraceCost_completeFrontierTrace_ne_top
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeFrontierTrace ≠ ⊤ := by
  rw [R.weightedTraceCost_completeFrontierTrace]
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.sum_ne_top.mpr fun q _ => R.indexedGraphSpeedCost_ne_top lam q
  · apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          R.volume_lowerOuterFiber_ne_top
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          R.volume_upperOuterFiber_ne_top
    · exact ENNReal.sum_ne_top.mpr fun i _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (R.volume_seamSymmDiffFiber_ne_top i)

/-- The exact centered complete-frontier formula is finite before any
conversion to a real-valued perimeter. -/
theorem Region.weightedTraceCost_completeCenteredFrontierTrace_ne_top
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeCenteredFrontierTrace ≠ ⊤ := by
  rw [R.weightedTraceCost_completeCenteredFrontierTrace]
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.sum_ne_top.mpr fun q _ =>
      R.indexedCenteredGraphSpeedCost_ne_top lam q
  · apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.add_ne_top.mpr
      constructor
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (R.volume_centeredFiber_ne_top _ _)
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (R.volume_centeredFiber_ne_top _ _)
    · exact ENNReal.sum_ne_top.mpr fun i _ =>
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (R.volume_centeredSeamSymmDiffFiber_ne_top i)

/-- Literal topological-frontier cost of the original carrier, identified with
the exact finite-sum formula without using any almost-everywhere carrier
relation. -/
theorem Region.weightedTraceCost_frontier_carrier (R : Region) (lam : ℝ) :
    weightedTraceCost lam (frontier R.carrier) =
      weightedTraceCost lam R.completeFrontierTrace := by
  rw [R.frontier_carrier]

/-- Literal topological-frontier cost of the centered carrier, identified with
its independently derived exact finite-sum formula. -/
theorem Region.weightedTraceCost_frontier_centeredCarrier
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam R.completeCenteredFrontierTrace := by
  rw [R.frontier_centeredCarrier]

theorem Region.weightedTraceCost_frontier_carrier_ne_top
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam (frontier R.carrier) ≠ ⊤ := by
  rw [R.weightedTraceCost_frontier_carrier]
  exact R.weightedTraceCost_completeFrontierTrace_ne_top lam

theorem Region.weightedTraceCost_frontier_centeredCarrier_ne_top
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam (frontier R.centeredCarrier) ≠ ⊤ := by
  rw [R.weightedTraceCost_frontier_centeredCarrier]
  exact R.weightedTraceCost_completeCenteredFrontierTrace_ne_top lam
end FiniteBandRearrangement
end CMVRelaxation
