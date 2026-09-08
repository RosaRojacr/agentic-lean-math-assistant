/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFiveSourceGeometry
import CMVRigidProjection

/-!
# Flat-interface projection patches for CMV Figure 5

The complete source frontier and bounded openness determine the occupied side
of every nondegenerate exposed interface piece.  The resulting literal collars
are packaged directly as `CMVRelaxation.RigidProjectionPatch` values.
-/

open Set Real
open scoped Topology

noncomputable section

namespace CMVFigureFive

private def verticalSection (U : Set PlanePoint) (x : ℝ) : Set ℝ :=
  {y | (x, y) ∈ U}

private lemma isOpen_verticalSection {U : Set PlanePoint} (hU : IsOpen U) (x : ℝ) :
    IsOpen (verticalSection U x) := by
  exact hU.preimage (continuous_const.prodMk continuous_id)

private lemma isBounded_verticalSection {U : Set PlanePoint}
    (hU : Bornology.IsBounded U) (x : ℝ) :
    Bornology.IsBounded (verticalSection U x) := by
  apply hU.image_snd.subset
  intro y hy
  exact ⟨(x, y), hy, rfl⟩

private lemma frontier_verticalSection_subset (U : Set PlanePoint) (x : ℝ) :
    frontier (verticalSection U x) ⊆ {y : ℝ | (x, y) ∈ frontier U} := by
  exact (continuous_const.prodMk continuous_id).frontier_preimage_subset U

private lemma preconnected_subset_open_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {U C : Set X}
    (hU : IsOpen U) (hC : IsPreconnected C)
    (hdis : Disjoint C (frontier U)) (hne : (C ∩ U).Nonempty) : C ⊆ U := by
  apply hC.subset_of_closure_inter_subset hU hne
  rintro x ⟨hxClosure, hxC⟩
  by_contra hxU
  have hxFrontier : x ∈ frontier U := by
    rw [hU.frontier_eq]
    exact ⟨hxClosure, hxU⟩
  exact (Set.disjoint_left.mp hdis) hxC hxFrontier

private lemma outward_Ioi_disjoint
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U) {x y₀ : ℝ}
    (hfrontier_free : ∀ y, y₀ < y → (x, y) ∉ frontier U) :
    Disjoint (Ioi y₀) (verticalSection U x) := by
  let S := verticalSection U x
  have hSopen : IsOpen S := isOpen_verticalSection hUopen x
  have hSbounded : Bornology.IsBounded S := isBounded_verticalSection hUbounded x
  have hdisFrontier : Disjoint (Ioi y₀) (frontier S) := by
    rw [Set.disjoint_left]
    intro y hy hyFrontier
    exact hfrontier_free y hy
      (frontier_verticalSection_subset U x hyFrontier)
  rw [Set.disjoint_left]
  intro y hy hyS
  have hsub : Ioi y₀ ⊆ S :=
    preconnected_subset_open_of_disjoint_frontier hSopen isPreconnected_Ioi
      hdisFrontier ⟨y, hy, hyS⟩
  obtain ⟨upper, hupper⟩ := hSbounded.bddAbove
  have hz : max y₀ upper + 1 ∈ Ioi y₀ := by
    change y₀ < max y₀ upper + 1
    linarith [le_max_left y₀ upper]
  have := hupper (hsub hz)
  linarith [le_max_right y₀ upper]

private lemma outward_Iio_disjoint
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U) {x y₀ : ℝ}
    (hfrontier_free : ∀ y, y < y₀ → (x, y) ∉ frontier U) :
    Disjoint (Iio y₀) (verticalSection U x) := by
  let S := verticalSection U x
  have hSopen : IsOpen S := isOpen_verticalSection hUopen x
  have hSbounded : Bornology.IsBounded S := isBounded_verticalSection hUbounded x
  have hdisFrontier : Disjoint (Iio y₀) (frontier S) := by
    rw [Set.disjoint_left]
    intro y hy hyFrontier
    exact hfrontier_free y hy
      (frontier_verticalSection_subset U x hyFrontier)
  rw [Set.disjoint_left]
  intro y hy hyS
  have hsub : Iio y₀ ⊆ S :=
    preconnected_subset_open_of_disjoint_frontier hSopen isPreconnected_Iio
      hdisFrontier ⟨y, hy, hyS⟩
  obtain ⟨lower, hlower⟩ := hSbounded.bddBelow
  have hz : min y₀ lower - 1 ∈ Iio y₀ := by
    change min y₀ lower - 1 < y₀
    linarith [min_le_left y₀ lower]
  have := hlower (hsub hz)
  linarith [min_le_right y₀ lower]

private lemma upper_rectangle_eq
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U)
    {l r low high y₀ : ℝ} (hlr : l < r) (hlow : low < y₀)
    (hhigh : y₀ < high)
    (hray : ∀ x ∈ Ioo l r, ∀ y, y₀ < y → (x, y) ∉ frontier U)
    (hline : ∀ x ∈ Ioo l r, (x, y₀) ∈ frontier U)
    (hlowerFree : ∀ q ∈ frontier U, q.1 ∈ Ioo l r →
      q.2 ∈ Ioo low y₀ → False) :
    U ∩ (Ioo l r ×ˢ Ioo low high) =
      (Ioo l r ×ˢ Ioo low high) ∩ {q : PlanePoint | q.2 < y₀} := by
  let N : Set PlanePoint := Ioo l r ×ˢ Ioo low high
  let C : Set PlanePoint := Ioo l r ×ˢ Ioo low y₀
  have hupperOutside : ∀ q ∈ N, y₀ < q.2 → q ∉ U := by
    intro q hq hy hqU
    exact (Set.disjoint_left.mp
      (outward_Ioi_disjoint hUopen hUbounded (hray q.1 hq.1))) hy hqU
  have hCdis : Disjoint C (frontier U) := by
    rw [Set.disjoint_left]
    intro q hq hqFrontier
    exact hlowerFree q hqFrontier hq.1 hq.2
  have hCpre : IsPreconnected C := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hCnonempty : (C ∩ U).Nonempty := by
    let x₀ : ℝ := (l + r) / 2
    have hx₀ : x₀ ∈ Ioo l r := by
      dsimp [x₀]
      constructor <;> linarith
    have hpFrontier : (x₀, y₀) ∈ frontier U := hline x₀ hx₀
    have hpN : (x₀, y₀) ∈ N := ⟨hx₀, hlow, hhigh⟩
    have hNopen : IsOpen N := isOpen_Ioo.prod isOpen_Ioo
    obtain ⟨q, hqN, hqU⟩ :=
      (mem_closure_iff.1 (frontier_subset_closure hpFrontier)) N hNopen hpN
    have hqy : q.2 < y₀ := by
      apply lt_of_not_ge
      intro hy
      rcases hy.eq_or_lt with heq | hgt
      · have hqFrontier : q ∈ frontier U := by
          rw [show q = (q.1, q.2) from Prod.eta q, ← heq]
          exact hline q.1 hqN.1
        have hcontra : q ∈ U ∩ frontier U := ⟨hqU, hqFrontier⟩
        rw [hUopen.inter_frontier_eq] at hcontra
        exact hcontra
      · exact hupperOutside q hqN hgt hqU
    exact ⟨q, ⟨hqN.1, hqN.2.1, hqy⟩, hqU⟩
  have hCsub : C ⊆ U :=
    preconnected_subset_open_of_disjoint_frontier hUopen hCpre hCdis hCnonempty
  ext q
  constructor
  · rintro ⟨hqU, hqN⟩
    refine ⟨hqN, ?_⟩
    change q.2 < y₀
    apply lt_of_not_ge
    intro hy
    rcases hy.eq_or_lt with heq | hgt
    · have hqFrontier : q ∈ frontier U := by
        rw [show q = (q.1, q.2) from Prod.eta q, ← heq]
        exact hline q.1 hqN.1
      have hcontra : q ∈ U ∩ frontier U := ⟨hqU, hqFrontier⟩
      rw [hUopen.inter_frontier_eq] at hcontra
      exact hcontra
    · exact hupperOutside q hqN hgt hqU
  · rintro ⟨hqN, hqy⟩
    exact ⟨hCsub ⟨hqN.1, hqN.2.1, hqy⟩, hqN⟩

private lemma lower_rectangle_eq
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hUbounded : Bornology.IsBounded U)
    {l r low high y₀ : ℝ} (hlr : l < r) (hlow : low < y₀)
    (hhigh : y₀ < high)
    (hray : ∀ x ∈ Ioo l r, ∀ y, y < y₀ → (x, y) ∉ frontier U)
    (hline : ∀ x ∈ Ioo l r, (x, y₀) ∈ frontier U)
    (hupperFree : ∀ q ∈ frontier U, q.1 ∈ Ioo l r →
      q.2 ∈ Ioo y₀ high → False) :
    U ∩ (Ioo l r ×ˢ Ioo low high) =
      (Ioo l r ×ˢ Ioo low high) ∩ {q : PlanePoint | y₀ < q.2} := by
  let N : Set PlanePoint := Ioo l r ×ˢ Ioo low high
  let C : Set PlanePoint := Ioo l r ×ˢ Ioo y₀ high
  have hlowerOutside : ∀ q ∈ N, q.2 < y₀ → q ∉ U := by
    intro q hq hy hqU
    exact (Set.disjoint_left.mp
      (outward_Iio_disjoint hUopen hUbounded (hray q.1 hq.1))) hy hqU
  have hCdis : Disjoint C (frontier U) := by
    rw [Set.disjoint_left]
    intro q hq hqFrontier
    exact hupperFree q hqFrontier hq.1 hq.2
  have hCpre : IsPreconnected C := isPreconnected_Ioo.prod isPreconnected_Ioo
  have hCnonempty : (C ∩ U).Nonempty := by
    let x₀ : ℝ := (l + r) / 2
    have hx₀ : x₀ ∈ Ioo l r := by
      dsimp [x₀]
      constructor <;> linarith
    have hpFrontier : (x₀, y₀) ∈ frontier U := hline x₀ hx₀
    have hpN : (x₀, y₀) ∈ N := ⟨hx₀, hlow, hhigh⟩
    have hNopen : IsOpen N := isOpen_Ioo.prod isOpen_Ioo
    obtain ⟨q, hqN, hqU⟩ :=
      (mem_closure_iff.1 (frontier_subset_closure hpFrontier)) N hNopen hpN
    have hqy : y₀ < q.2 := by
      apply lt_of_not_ge
      intro hy
      rcases hy.eq_or_lt with heq | hlt
      · have hqFrontier : q ∈ frontier U := by
          rw [show q = (q.1, q.2) from Prod.eta q, heq]
          exact hline q.1 hqN.1
        have hcontra : q ∈ U ∩ frontier U := ⟨hqU, hqFrontier⟩
        rw [hUopen.inter_frontier_eq] at hcontra
        exact hcontra
      · exact hlowerOutside q hqN hlt hqU
    exact ⟨q, ⟨hqN.1, hqy, hqN.2.2⟩, hqU⟩
  have hCsub : C ⊆ U :=
    preconnected_subset_open_of_disjoint_frontier hUopen hCpre hCdis hCnonempty
  ext q
  constructor
  · rintro ⟨hqU, hqN⟩
    refine ⟨hqN, ?_⟩
    change y₀ < q.2
    apply lt_of_not_ge
    intro hy
    rcases hy.eq_or_lt with heq | hlt
    · have hqFrontier : q ∈ frontier U := by
        rw [show q = (q.1, q.2) from Prod.eta q, heq]
        exact hline q.1 hqN.1
      have hcontra : q ∈ U ∩ frontier U := ⟨hqU, hqFrontier⟩
      rw [hUopen.inter_frontier_eq] at hcontra
      exact hcontra
    · exact hlowerOutside q hqN hlt hqU
  · rintro ⟨hqN, hqy⟩
    exact ⟨hCsub ⟨hqN.1, hqy, hqN.2.2⟩, hqN⟩

namespace CappedInterface

variable {lam sourceRadius leftTangentX rightTangentX : ℝ} {side : CapSide}

lemma cap_cos_pos (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) : 0 < cos b.cap.theta := by
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  nlinarith [b.signed_contact_law]

lemma arcTrace_fst_between
    (b : CappedInterface lam sourceRadius leftTangentX rightTangentX side)
    (hlam : 1 < lam) {p : PlanePoint} (hp : p ∈ b.cap.arcTrace) :
    b.cap.leftEndpoint.1 ≤ p.1 ∧ p.1 ≤ b.cap.rightEndpoint.1 := by
  have hR := b.cap.radius_pos
  have hcos := b.cap_cos_pos hlam
  have htrig := Real.sin_sq_add_cos_sq b.cap.theta
  have hsin := b.cap.radius_mul_sin
  have hrcos : 0 ≤ b.cap.radius * cos b.cap.theta :=
    (mul_pos hR hcos).le
  have hdecomp :
      b.cap.radius ^ 2 =
        (b.cap.radius * sin b.cap.theta) ^ 2 +
          (b.cap.radius * cos b.cap.theta) ^ 2 := by
    calc
      b.cap.radius ^ 2 = b.cap.radius ^ 2 * 1 := by ring
      _ = b.cap.radius ^ 2 *
          (sin b.cap.theta ^ 2 + cos b.cap.theta ^ 2) := by rw [htrig]
      _ = _ := by ring
  cases hside : b.cap.side with
  | upper =>
      have hcircle := hp.1
      have hy := hp.2
      simp only [OneSidedCircularCap.radiusSquaredAt,
        OneSidedCircularCap.center, hside] at hcircle
      simp only [hside] at hy
      have hvertical :
          b.cap.radius * cos b.cap.theta ≤
            p.2 - (b.cap.baseY - b.cap.radius * cos b.cap.theta) := by
        linarith
      have hsum_nonneg :
          0 ≤ (p.2 - (b.cap.baseY - b.cap.radius * cos b.cap.theta) -
              b.cap.radius * cos b.cap.theta) *
            (p.2 - (b.cap.baseY - b.cap.radius * cos b.cap.theta) +
              b.cap.radius * cos b.cap.theta) := by
        apply mul_nonneg
        · linarith
        · linarith
      have hxSq :
          (p.1 - b.cap.midpointX) ^ 2 ≤
            (b.cap.radius * sin b.cap.theta) ^ 2 := by
        nlinarith
      have hxChord :
          (p.1 - b.cap.midpointX) ^ 2 ≤ (b.cap.chord / 2) ^ 2 := by
        rw [← hsin]
        exact hxSq
      have hchord : 0 < b.cap.chord / 2 := half_pos b.cap.chord_pos
      simp only [OneSidedCircularCap.leftEndpoint,
        OneSidedCircularCap.rightEndpoint]
      constructor <;> nlinarith
  | lower =>
      have hcircle := hp.1
      have hy := hp.2
      simp only [OneSidedCircularCap.radiusSquaredAt,
        OneSidedCircularCap.center, hside] at hcircle
      simp only [hside] at hy
      have hvertical :
          b.cap.radius * cos b.cap.theta ≤
            (b.cap.baseY + b.cap.radius * cos b.cap.theta) - p.2 := by
        linarith
      have hsum_nonneg :
          0 ≤ ((b.cap.baseY + b.cap.radius * cos b.cap.theta) - p.2 -
              b.cap.radius * cos b.cap.theta) *
            ((b.cap.baseY + b.cap.radius * cos b.cap.theta) - p.2 +
              b.cap.radius * cos b.cap.theta) := by
        apply mul_nonneg
        · linarith
        · linarith
      have hxSq :
          (p.1 - b.cap.midpointX) ^ 2 ≤
            (b.cap.radius * sin b.cap.theta) ^ 2 := by
        nlinarith
      have hxChord :
          (p.1 - b.cap.midpointX) ^ 2 ≤ (b.cap.chord / 2) ^ 2 := by
        rw [← hsin]
        exact hxSq
      have hchord : 0 < b.cap.chord / 2 := half_pos b.cap.chord_pos
      simp only [OneSidedCircularCap.leftEndpoint,
        OneSidedCircularCap.rightEndpoint]
      constructor <;> nlinarith

end CappedInterface


end CMVFigureFive
