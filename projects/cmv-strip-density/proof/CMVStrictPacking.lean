import CMVGeometry
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Strict horizontal packing counts

This module specializes mathlib's strict `Metric.packingNumber` to horizontal
fibers of compact subsets of the Euclidean realization of the CMV plane.  The
strict convention is preserved: distinct selected points have distance strictly
greater than the requested separation.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace CMVRelaxation
namespace StrictPacking

/-- First coordinate in the Euclidean realization. -/
def first (z : EuclideanPlane) : ℝ := (WithLp.ofLp z).1

/-- Second coordinate in the Euclidean realization. -/
def second (z : EuclideanPlane) : ℝ := (WithLp.ofLp z).2

lemma continuous_first : Continuous first := by
  change Continuous (Prod.fst ∘ (WithLp.ofLp : EuclideanPlane → ℝ × ℝ))
  fun_prop

lemma continuous_second : Continuous second := by
  change Continuous (Prod.snd ∘ (WithLp.ofLp : EuclideanPlane → ℝ × ℝ))
  fun_prop

@[simp] lemma first_toLp (x y : ℝ) : first (WithLp.toLp 2 (x, y)) = x := rfl

@[simp] lemma second_toLp (x y : ℝ) : second (WithLp.toLp 2 (x, y)) = y := rfl

/-- The horizontal fiber of a Euclidean set at height `y`. -/
def horizontalFiber (K : Set EuclideanPlane) (y : ℝ) : Set ℝ :=
  {x | WithLp.toLp 2 (x, y) ∈ K}

/-- Mathlib's strict packing number of a horizontal fiber. -/
def count (delta : ℝ≥0) (K : Set EuclideanPlane) (y : ℝ) : ℕ∞ :=
  Metric.packingNumber delta (horizontalFiber K y)

/-- Horizontal projection of a Euclidean set. -/
def horizontalProjection (K : Set EuclideanPlane) : Set ℝ := first '' K

lemma horizontalFiber_subset_projection (K : Set EuclideanPlane) (y : ℝ) :
    horizontalFiber K y ⊆ horizontalProjection K := by
  intro x hx
  exact ⟨WithLp.toLp 2 (x, y), hx, by simp⟩

lemma isCompact_horizontalProjection {K : Set EuclideanPlane} (hK : IsCompact K) :
    IsCompact (horizontalProjection K) :=
  hK.image continuous_first

/-- Packing number is monotone in its carrier set. -/
lemma packingNumber_mono_set {X : Type*} [PseudoEMetricSpace X]
    {A B : Set X} {delta : ℝ≥0} (hAB : A ⊆ B) :
    Metric.packingNumber delta A ≤ Metric.packingNumber delta B := by
  simp only [Metric.packingNumber, iSup_le_iff]
  intro C hCA hsep
  exact le_iSup₂_of_le C (hCA.trans hAB) (le_iSup_of_le hsep le_rfl)

/-- Compactness gives one finite bound for all horizontal strict packing counts. -/
theorem exists_uniform_finite_bound {K : Set EuclideanPlane} (hK : IsCompact K)
    {delta : ℝ≥0} (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ y : ℝ, count delta K y ≤ N := by
  let P := horizontalProjection K
  have hP : IsCompact P := isCompact_horizontalProjection hK
  obtain ⟨C, _hCP, hCfinite, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (show delta / 2 ≠ 0 by positivity) hP
  refine ⟨hCfinite.toFinset.card, fun y ↦ ?_⟩
  have hpacking :
      Metric.packingNumber delta (horizontalFiber K y) ≤ C.encard := by
    calc
      Metric.packingNumber delta (horizontalFiber K y) =
          Metric.packingNumber (2 * (delta / 2)) (horizontalFiber K y) := by
            congr 2
            exact ((two_mul (delta / 2)).trans (add_halves delta)).symm
      _ ≤ Metric.externalCoveringNumber (delta / 2) (horizontalFiber K y) :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ Metric.externalCoveringNumber (delta / 2) P :=
        Metric.externalCoveringNumber_mono_set
          (horizontalFiber_subset_projection K y)
      _ ≤ C.encard := hCcover.externalCoveringNumber_le_encard
  simpa [count, hCfinite.encard_eq_coe_toFinset_card] using hpacking

@[simp] theorem count_empty (delta : ℝ≥0) (y : ℝ) :
    count delta (∅ : Set EuclideanPlane) y = 0 := by
  simp [count, horizontalFiber]

/-- Compact tuples with a common height and a prescribed positive separation
margin for every ordered pair. -/
def marginTuples (K : Set EuclideanPlane) (delta : ℝ≥0) (n : ℕ)
    (marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ) :
    Set (Fin (n + 1) → EuclideanPlane) :=
  Set.pi Set.univ (fun _ ↦ K) ∩
    {p | ∀ i, second (p i) = second (p 0)} ∩
    {p | ∀ i j, i ≠ j →
      (delta : ℝ) + 1 / (marginIndex i j + 1 : ℝ) ≤
        dist (first (p i)) (first (p j))}

lemma isCompact_marginTuples {K : Set EuclideanPlane} (hK : IsCompact K)
    (delta : ℝ≥0) (n : ℕ) (marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ) :
    IsCompact (marginTuples K delta n marginIndex) := by
  have hbase :
      IsCompact (Set.pi Set.univ (fun _ : Fin (n + 1) ↦ K)) :=
    isCompact_univ_pi fun _ ↦ hK
  rw [marginTuples]
  have heq : IsClosed {p : Fin (n + 1) → EuclideanPlane |
      ∀ i, second (p i) = second (p 0)} := by
    rw [show {p : Fin (n + 1) → EuclideanPlane |
        ∀ i, second (p i) = second (p 0)} =
      ⋂ i, {p | second (p i) = second (p 0)} by ext; simp]
    exact isClosed_iInter fun i ↦
      isClosed_eq
        (continuous_second.comp (continuous_apply i))
        (continuous_second.comp (continuous_apply 0))
  have hsep : IsClosed {p : Fin (n + 1) → EuclideanPlane |
      ∀ i j, i ≠ j →
        (delta : ℝ) + 1 / (marginIndex i j + 1 : ℝ) ≤
          dist (first (p i)) (first (p j))} := by
    rw [show {p : Fin (n + 1) → EuclideanPlane |
        ∀ i j, i ≠ j →
          (delta : ℝ) + 1 / (marginIndex i j + 1 : ℝ) ≤
            dist (first (p i)) (first (p j))} =
      ⋂ i, ⋂ j, {p | i ≠ j →
        (delta : ℝ) + 1 / (marginIndex i j + 1 : ℝ) ≤
          dist (first (p i)) (first (p j))} by ext; simp]
    refine isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ ?_
    by_cases hij : i = j
    · simp [hij]
    · have hconst : Continuous (fun _ : Fin (n + 1) → EuclideanPlane ↦
          (delta : ℝ) + 1 / (marginIndex i j + 1 : ℝ)) :=
        continuous_const
      have hi : Continuous (fun p : Fin (n + 1) → EuclideanPlane ↦
          first (p i)) := continuous_first.comp (continuous_apply i)
      have hj : Continuous (fun p : Fin (n + 1) → EuclideanPlane ↦
          first (p j)) := continuous_first.comp (continuous_apply j)
      have hdist : Continuous (fun p : Fin (n + 1) → EuclideanPlane ↦
          dist (first (p i)) (first (p j))) := hi.dist hj
      simpa [hij] using isClosed_le hconst hdist
  exact (hbase.inter_right heq).inter_right hsep
/-- Heights represented by one compact positive-margin tuple family. -/
def marginHeights (K : Set EuclideanPlane) (delta : ℝ≥0) (n : ℕ)
    (marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ) : Set ℝ :=
  (fun p ↦ second (p 0)) '' marginTuples K delta n marginIndex

lemma isCompact_marginHeights {K : Set EuclideanPlane} (hK : IsCompact K)
    (delta : ℝ≥0) (n : ℕ) (marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ) :
    IsCompact (marginHeights K delta n marginIndex) :=
  (isCompact_marginTuples hK delta n marginIndex).image
    (continuous_second.comp (continuous_apply 0))

lemma measurableSet_iUnion_marginHeights {K : Set EuclideanPlane} (hK : IsCompact K)
    (delta : ℝ≥0) (n : ℕ) :
    MeasurableSet
      (⋃ marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ,
        marginHeights K delta n marginIndex) :=
  MeasurableSet.iUnion fun marginIndex ↦
    (isCompact_marginHeights hK delta n marginIndex).measurableSet

/-- A labeled strictly separated family in one horizontal fiber. -/
def IsStrictTuple (K : Set EuclideanPlane) (delta : ℝ≥0) (y : ℝ)
    (n : ℕ) (x : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, x i ∈ horizontalFiber K y) ∧
    ∀ i j, i ≠ j → (delta : ℝ≥0∞) < edist (x i) (x j)

lemma count_ge_iff_exists_strictTuple {K : Set EuclideanPlane} (hK : IsCompact K)
    {delta : ℝ≥0} (hdelta : 0 < delta) (n : ℕ) (y : ℝ) :
    (n + 1 : ℕ∞) ≤ count delta K y ↔
      ∃ x : Fin (n + 1) → ℝ, IsStrictTuple K delta y n x := by
  obtain ⟨bound, hbound⟩ := exists_uniform_finite_bound hK hdelta
  have htop : count delta K y ≠ ⊤ :=
    ne_of_lt ((hbound y).trans_lt (ENat.natCast_lt_top bound))
  let C := Metric.maximalSeparatedSet delta (horizontalFiber K y)
  constructor
  · intro hn
    have hnC : (n + 1 : ℕ∞) ≤ C.encard := by
      rwa [Metric.encard_maximalSeparatedSet htop]
    obtain ⟨D, hDC, hDcard⟩ :=
      Set.exists_subset_encard_eq (s := C) hnC
    have hDfinite : D.Finite := Set.finite_of_encard_eq_coe hDcard
    letI : Fintype D := hDfinite.fintype
    have hcard : Fintype.card D = n + 1 := by
      apply ENat.natCast_inj.mp
      rw [Set.coe_fintypeCard]
      exact hDcard
    let e : D ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcard
    let x : Fin (n + 1) → ℝ := fun i ↦ (e.symm i : D).1
    refine ⟨x, ?_, ?_⟩
    · intro i
      exact Metric.maximalSeparatedSet_subset
        (hDC (e.symm i).2)
    · intro i j hij
      apply Metric.isSeparated_maximalSeparatedSet
        (hDC (e.symm i).2) (hDC (e.symm j).2)
      exact fun hvalue ↦ hij (e.symm.injective (Subtype.ext hvalue))
  · rintro ⟨x, hxmem, hxsep⟩
    have hxinj : Function.Injective x := by
      intro i j hvalue
      by_contra hij
      have hstrict := hxsep i j hij
      simp [hvalue] at hstrict
    have hrange_subset : Set.range x ⊆ horizontalFiber K y := by
      rintro _ ⟨i, rfl⟩
      exact hxmem i
    have hrange_sep : Metric.IsSeparated delta (Set.range x) := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hvalue
      exact hxsep i j fun hij ↦ hvalue (congrArg x hij)
    have hrange_card : (Set.range x).encard = (n + 1 : ℕ∞) := by
      rw [← Set.image_univ, hxinj.encard_image]
      simp
    rw [← hrange_card]
    exact hrange_sep.encard_le_packingNumber hrange_subset

theorem superlevel_eq_iUnion_marginHeights {K : Set EuclideanPlane}
    (hK : IsCompact K) {delta : ℝ≥0} (hdelta : 0 < delta) (n : ℕ) :
    {y | (n + 1 : ℕ∞) ≤ count delta K y} =
      ⋃ marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ,
        marginHeights K delta n marginIndex := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hxmem, hxsep⟩ :=
      (count_ge_iff_exists_strictTuple hK hdelta n y).mp hy
    have hreal : ∀ i j, i ≠ j →
        (delta : ℝ) < dist (x i) (x j) := by
      intro i j hij
      have hstrict := hxsep i j hij
      rw [edist_nndist, ENNReal.coe_lt_coe] at hstrict
      exact_mod_cast hstrict
    have hgap : ∀ i j, i ≠ j →
        0 < dist (x i) (x j) - (delta : ℝ) := by
      intro i j hij
      linarith [hreal i j hij]
    let marginIndex : Fin (n + 1) → Fin (n + 1) → ℕ :=
      fun i j ↦ if hij : i ≠ j then
        Classical.choose (exists_nat_one_div_lt (hgap i j hij))
      else 0
    have hmargin : ∀ i j, i ≠ j →
        (delta : ℝ) + 1 / (marginIndex i j + 1 : ℝ) ≤
          dist (x i) (x j) := by
      intro i j hij
      have hchoice :=
        Classical.choose_spec (exists_nat_one_div_lt (hgap i j hij))
      rw [show marginIndex i j =
          Classical.choose (exists_nat_one_div_lt (hgap i j hij)) by
        simp [marginIndex, hij]]
      linarith
    let p : Fin (n + 1) → EuclideanPlane :=
      fun i ↦ WithLp.toLp 2 (x i, y)
    apply Set.mem_iUnion.2
    refine ⟨marginIndex, ⟨p, ?_, rfl⟩⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i _hi
      exact hxmem i
    · intro i
      simp [p]
    · intro i j hij
      simpa [p] using hmargin i j hij
  · intro hy
    obtain ⟨marginIndex, hy⟩ := Set.mem_iUnion.1 hy
    obtain ⟨p, hp, rfl⟩ := hy
    rcases hp with ⟨⟨hpK, hheight⟩, hmargin⟩
    apply (count_ge_iff_exists_strictTuple hK hdelta n _).mpr
    let x : Fin (n + 1) → ℝ := fun i ↦ first (p i)
    refine ⟨x, ?_, ?_⟩
    · intro i
      have hpi : p i ∈ K := hpK i (Set.mem_univ i)
      change WithLp.toLp 2 (first (p i), second (p 0)) ∈ K
      rw [← hheight i]
      change WithLp.toLp 2 (WithLp.ofLp (p i)) ∈ K
      simpa using hpi
    · intro i j hij
      have hm := hmargin i j hij
      have hpos : 0 < 1 / (marginIndex i j + 1 : ℝ) := by positivity
      have hreal :
          (delta : ℝ) < dist (first (p i)) (first (p j)) := by
        linarith
      rw [edist_nndist, ENNReal.coe_lt_coe]
      exact_mod_cast hreal

lemma measurableSet_count_superlevel {K : Set EuclideanPlane}
    (hK : IsCompact K) {delta : ℝ≥0} (hdelta : 0 < delta) (n : ℕ) :
    MeasurableSet {y | (n + 1 : ℕ∞) ≤ count delta K y} := by
  rw [superlevel_eq_iUnion_marginHeights hK hdelta n]
  exact measurableSet_iUnion_marginHeights hK delta n

/-- The strict horizontal packing count of a compact Euclidean set is Borel
measurable. -/
theorem measurable_count {K : Set EuclideanPlane} (hK : IsCompact K)
    {delta : ℝ≥0} (hdelta : 0 < delta) :
    Measurable (count delta K) := by
  apply ENat.measurable_iff.mpr
  intro n
  cases n with
  | zero =>
      change MeasurableSet {y | count delta K y = (0 : ℕ∞)}
      rw [show {y | count delta K y = (0 : ℕ∞)} =
          {y | (1 : ℕ∞) ≤ count delta K y}ᶜ by
        ext y
        simp]
      exact (measurableSet_count_superlevel hK hdelta 0).compl
  | succ n =>
      change MeasurableSet {y | count delta K y = (Nat.succ n : ℕ∞)}
      rw [show {y | count delta K y = (Nat.succ n : ℕ∞)} =
          {y | (n + 1 : ℕ∞) ≤ count delta K y} ∩
            {y | (n + 2 : ℕ∞) ≤ count delta K y}ᶜ by
        ext y
        change count delta K y = (n + 1 : ℕ∞) ↔
          (n + 1 : ℕ∞) ≤ count delta K y ∧
            ¬(n + 2 : ℕ∞) ≤ count delta K y
        constructor
        · intro heq
          rw [heq]
          simp
        · rintro ⟨hlower, hupper⟩
          apply le_antisymm _ hlower
          apply (ENat.lt_add_one_iff (ENat.natCast_ne_top (n + 1))).mp
          have hlt : count delta K y < (n + 2 : ℕ∞) :=
            lt_of_not_ge hupper
          have htwo : (2 : ℕ∞) = 1 + 1 := by norm_num
          rw [htwo, ← add_assoc] at hlt
          exact hlt]
      exact (measurableSet_count_superlevel hK hdelta n).inter
        (measurableSet_count_superlevel hK hdelta (n + 1)).compl

lemma packingNumber_pair_eq_two {u v : ℝ} (huv : u ≠ v) {delta : ℝ≥0}
    (hdelta : (delta : ℝ≥0∞) < edist u v) :
    Metric.packingNumber delta ({u, v} : Set ℝ) = 2 := by
  apply le_antisymm
  · calc
      Metric.packingNumber delta ({u, v} : Set ℝ) ≤
          ({u, v} : Set ℝ).encard :=
        Metric.packingNumber_le_encard_self _
      _ = 2 := Set.encard_pair huv
  · have hsep : Metric.IsSeparated delta ({u, v} : Set ℝ) := by
      rw [Metric.isSeparated_insert]
      refine ⟨Metric.IsSeparated.singleton, ?_⟩
      intro y hy _huy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hdelta
    calc
      (2 : ℕ∞) = ({u, v} : Set ℝ).encard := (Set.encard_pair huv).symm
      _ ≤ Metric.packingNumber delta ({u, v} : Set ℝ) :=
        hsep.encard_le_packingNumber Subset.rfl

lemma packingNumber_pair_eq_one {u v : ℝ} (huv : u ≠ v) {delta : ℝ≥0}
    (hdelta : ¬(delta : ℝ≥0∞) < edist u v) :
    Metric.packingNumber delta ({u, v} : Set ℝ) = 1 := by
  apply le_antisymm
  · simp only [Metric.packingNumber, iSup_le_iff]
    intro C hC hsep
    apply Set.encard_le_one_iff_subsingleton.mpr
    intro x hx y hy
    have hx' := hC hx
    have hy' := hC hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx' hy'
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · rfl
    · exfalso
      exact hdelta (hsep hx hy huv)
    · exfalso
      exact hdelta (by simpa [edist_comm] using hsep hx hy huv.symm)
    · rfl
  · have hsingle : Metric.IsSeparated delta ({u} : Set ℝ) :=
      Metric.IsSeparated.singleton
    simpa using hsingle.encard_le_packingNumber
      (A := ({u, v} : Set ℝ)) (by simp)

/-- Two closed vertical segments at horizontal coordinates `-a` and `a`. -/
def twoVerticalSegments (a : ℝ) : Set EuclideanPlane :=
  planeEuclideanHomeomorph ''
    (({-a, a} : Set ℝ) ×ˢ Set.Icc (-1 : ℝ) 1)

lemma isCompact_twoVerticalSegments (a : ℝ) :
    IsCompact (twoVerticalSegments a) := by
  have hpair : IsCompact ({-a, a} : Set ℝ) :=
    isCompact_singleton.union isCompact_singleton
  exact (hpair.prod isCompact_Icc).image planeEuclideanHomeomorph.continuous

lemma horizontalFiber_twoVerticalSegments (a y : ℝ) :
    horizontalFiber (twoVerticalSegments a) y =
      if y ∈ Set.Icc (-1 : ℝ) 1 then ({-a, a} : Set ℝ) else ∅ := by
  ext x
  change (planeEuclideanHomeomorph (x, y) ∈ twoVerticalSegments a) ↔ _
  simp [twoVerticalSegments, and_comm]

theorem count_twoVerticalSegments_of_mem {a y : ℝ} (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    {delta : ℝ≥0} :
    count delta (twoVerticalSegments a) y =
      Metric.packingNumber delta ({-a, a} : Set ℝ) := by
  simp [count, horizontalFiber_twoVerticalSegments, hy]

theorem count_twoVerticalSegments_of_notMem {a y : ℝ}
    (hy : y ∉ Set.Icc (-1 : ℝ) 1) (delta : ℝ≥0) :
    count delta (twoVerticalSegments a) y = 0 := by
  simp [count, horizontalFiber_twoVerticalSegments, hy]

/-- Strict separation below the segment spacing counts both points. -/
theorem count_twoVerticalSegments_eq_two {a y : ℝ} (ha : 0 < a)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) {delta : ℝ≥0}
    (hdelta : (delta : ℝ≥0∞) < edist (-a) a) :
    count delta (twoVerticalSegments a) y = 2 := by
  rw [count_twoVerticalSegments_of_mem hy]
  exact packingNumber_pair_eq_two (by linarith) hdelta
/-- Coordinate form of the strict-separation contract: the spacing is `2*a`. -/
theorem count_twoVerticalSegments_eq_two_of_lt_two_mul {a y : ℝ} (ha : 0 < a)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) {delta : ℝ≥0}
    (hdelta : (delta : ℝ) < 2 * a) :
    count delta (twoVerticalSegments a) y = 2 := by
  apply count_twoVerticalSegments_eq_two ha hy
  rw [edist_nndist, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
  change (delta : ℝ) < dist (-a) a
  rw [Real.dist_eq, abs_of_neg]
  · linarith
  · linarith


/-- At separation exactly equal to the segment spacing, strict packing counts
only one point. -/
theorem count_twoVerticalSegments_eq_one_at_spacing {a y : ℝ} (ha : 0 < a)
    (hy : y ∈ Set.Icc (-1 : ℝ) 1) :
    count (nndist (-a) a) (twoVerticalSegments a) y = 1 := by
  rw [count_twoVerticalSegments_of_mem hy]
  apply packingNumber_pair_eq_one (by linarith)
  rw [edist_nndist]
  exact lt_irrefl _

end StrictPacking
end CMVRelaxation
