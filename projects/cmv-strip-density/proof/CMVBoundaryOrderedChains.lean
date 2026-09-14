/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryCompletedChains
import Mathlib.Topology.Bases

/-!
# Intrinsic order structure on completed boundary chains

The completed left and right frontier chains carry height-first traversal orders.
This module proves the intrinsic fiber descriptions, explicit extrema, and the
absence of adjacent points without assuming endpoint continuity, bounded
variation, a finite jump inventory, or a supplied parameterization.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

open CMVRelaxation
open CMVSourceClassification

variable {E U : Set PlanePoint}

@[simp] theorem leftCompletedChain_mem_lower_iff
    (D : SelectedBoundaryTopologyInput E U) (x : ℝ) :
    (x, D.lowerHeight) ∈ D.leftCompletedChain ↔
      x ∈ Icc D.lowerLeft D.lowerSplit := by
  change ((D.lowerHeight = D.lowerHeight ∧
      x ∈ Icc D.lowerLeft D.lowerSplit) ∨
    (D.lowerHeight ∈ D.occupiedHeights ∧
      x ∈ uIcc (Function.leftLim D.leftEndpoint D.lowerHeight)
        (Function.rightLim D.leftEndpoint D.lowerHeight)) ∨
    (D.lowerHeight = D.upperHeight ∧
      x ∈ Icc D.upperLeft D.upperSplit)) ↔ _
  have hnotOccupied : D.lowerHeight ∉ D.occupiedHeights := by
    rw [D.mem_occupiedHeights_iff_height_bounds]
    exact fun h => (lt_irrefl D.lowerHeight h.1)
  simp only [hnotOccupied, false_and, D.lowerHeight_lt_upperHeight.ne,
    true_and, or_false]

@[simp] theorem leftCompletedChain_mem_upper_iff
    (D : SelectedBoundaryTopologyInput E U) (x : ℝ) :
    (x, D.upperHeight) ∈ D.leftCompletedChain ↔
      x ∈ Icc D.upperLeft D.upperSplit := by
  change ((D.upperHeight = D.lowerHeight ∧
      x ∈ Icc D.lowerLeft D.lowerSplit) ∨
    (D.upperHeight ∈ D.occupiedHeights ∧
      x ∈ uIcc (Function.leftLim D.leftEndpoint D.upperHeight)
        (Function.rightLim D.leftEndpoint D.upperHeight)) ∨
    (D.upperHeight = D.upperHeight ∧
      x ∈ Icc D.upperLeft D.upperSplit)) ↔ _
  have hnotOccupied : D.upperHeight ∉ D.occupiedHeights := by
    rw [D.mem_occupiedHeights_iff_height_bounds]
    exact fun h => (lt_irrefl D.upperHeight h.2)
  simp only [hnotOccupied, false_and, D.lowerHeight_lt_upperHeight.ne.symm,
    true_and, false_or]

@[simp] theorem leftCompletedChain_mem_interior_iff
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    (x, y) ∈ D.leftCompletedChain ↔
      x ∈ uIcc (Function.leftLim D.leftEndpoint y)
        (Function.rightLim D.leftEndpoint y) := by
  have hb := D.mem_occupiedHeights_iff_height_bounds.mp hy
  change ((y = D.lowerHeight ∧ x ∈ Icc D.lowerLeft D.lowerSplit) ∨
    (y ∈ D.occupiedHeights ∧
      x ∈ uIcc (Function.leftLim D.leftEndpoint y)
        (Function.rightLim D.leftEndpoint y)) ∨
    (y = D.upperHeight ∧ x ∈ Icc D.upperLeft D.upperSplit)) ↔ _
  simp only [hb.1.ne', false_and, hy, true_and, hb.2.ne, or_false,
    false_or]

theorem leftCompletedChain_snd_mem_Icc
    (D : SelectedBoundaryTopologyInput E U)
    (p : D.leftCompletedChain) :
    p.1.2 ∈ Icc D.lowerHeight D.upperHeight := by
  rcases p.property with hp | hp | hp
  · rw [hp.1]
    exact ⟨le_rfl, D.lowerHeight_lt_upperHeight.le⟩
  · exact (D.mem_occupiedHeights_iff_height_bounds.mp hp.1).imp
      LT.lt.le LT.lt.le
  · rw [hp.1]
    exact ⟨D.lowerHeight_lt_upperHeight.le, le_rfl⟩

theorem leftCompletedChain_exists_between_of_snd_lt
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain) (hpq : p.1.2 < q.1.2) :
    ∃ r : D.leftCompletedChain,
      @LT.lt _ D.leftCompletedChainLinearOrder.toLT p r ∧
      @LT.lt _ D.leftCompletedChainLinearOrder.toLT r q := by
  let y : ℝ := (p.1.2 + q.1.2) / 2
  have hpy : p.1.2 < y := by dsimp [y]; linarith
  have hyq : y < q.1.2 := by dsimp [y]; linarith
  have hpBounds := D.leftCompletedChain_snd_mem_Icc p
  have hqBounds := D.leftCompletedChain_snd_mem_Icc q
  have hyOccupied : y ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hpBounds.1.trans_lt hpy, hyq.trans_le hqBounds.2⟩
  let r : D.leftCompletedChain :=
    ⟨(Function.leftLim D.leftEndpoint y, y),
      (D.leftCompletedChain_mem_interior_iff hyOccupied).mpr left_mem_uIcc⟩
  exact ⟨r, D.leftCompletedChain_lt_of_snd_lt p r hpy,
    D.leftCompletedChain_lt_of_snd_lt r q hyq⟩

theorem leftCompletedChain_exists_between_of_same_snd
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain) (hy : p.1.2 = q.1.2)
    (hpq : @LT.lt _ D.leftCompletedChainLinearOrder.toLT p q) :
    ∃ r : D.leftCompletedChain,
      @LT.lt _ D.leftCompletedChainLinearOrder.toLT p r ∧
      @LT.lt _ D.leftCompletedChainLinearOrder.toLT r q := by
  have hsecondary : D.leftOrderSecondary p.1 < D.leftOrderSecondary q.1 := by
    rcases Prod.Lex.toLex_lt_toLex.mp hpq with hheight | hsecondary
    · exact (lt_irrefl q.1.2 (hy ▸ hheight)).elim
    · exact hsecondary.2
  dsimp only [leftOrderSecondary] at hsecondary
  rw [← hy] at hsecondary
  let m : ℝ := (p.1.1 + q.1.1) / 2
  have hm : m ∈ uIcc p.1.1 q.1.1 := by
    rcases le_total p.1.1 q.1.1 with hpqX | hqpX
    · exact mem_uIcc_of_le (by dsimp [m]; linarith)
        (by dsimp [m]; linarith)
    · exact mem_uIcc_of_ge (by dsimp [m]; linarith)
        (by dsimp [m]; linarith)
  have hrMem : (m, p.1.2) ∈ D.leftCompletedChain := by
    by_cases hlower : p.1.2 = D.lowerHeight
    · rw [hlower]
      apply (D.leftCompletedChain_mem_lower_iff m).mpr
      have hpIcc : p.1.1 ∈ Icc D.lowerLeft D.lowerSplit := by
        apply (D.leftCompletedChain_mem_lower_iff p.1.1).mp
        rw [← hlower]
        exact p.property
      have hqIcc : q.1.1 ∈ Icc D.lowerLeft D.lowerSplit := by
        apply (D.leftCompletedChain_mem_lower_iff q.1.1).mp
        rw [← hlower, hy]
        exact q.property
      exact uIcc_subset_Icc hpIcc hqIcc hm
    · by_cases hupper : p.1.2 = D.upperHeight
      · rw [hupper]
        apply (D.leftCompletedChain_mem_upper_iff m).mpr
        have hpIcc : p.1.1 ∈ Icc D.upperLeft D.upperSplit := by
          apply (D.leftCompletedChain_mem_upper_iff p.1.1).mp
          rw [← hupper]
          exact p.property
        have hqIcc : q.1.1 ∈ Icc D.upperLeft D.upperSplit := by
          apply (D.leftCompletedChain_mem_upper_iff q.1.1).mp
          rw [← hupper, hy]
          exact q.property
        exact uIcc_subset_Icc hpIcc hqIcc hm
      · have hoccupied : p.1.2 ∈ D.occupiedHeights := by
          rcases p.property with hp | hp | hp
          · exact (hlower hp.1).elim
          · exact hp.1
          · exact (hupper hp.1).elim
        apply (D.leftCompletedChain_mem_interior_iff hoccupied).mpr
        have hpUIcc :=
          (D.leftCompletedChain_mem_interior_iff hoccupied).mp p.property
        have hqAtHeight : (q.1.1, p.1.2) ∈ D.leftCompletedChain := by
          rw [hy]
          exact q.property
        have hqUIcc :=
          (D.leftCompletedChain_mem_interior_iff hoccupied).mp hqAtHeight
        exact uIcc_subset_uIcc hpUIcc hqUIcc hm
  let r : D.leftCompletedChain := ⟨(m, p.1.2), hrMem⟩
  refine ⟨r, ?_, ?_⟩
  · apply Prod.Lex.toLex_lt_toLex.mpr
    right
    refine ⟨rfl, ?_⟩
    dsimp [r, m]
    dsimp only [leftOrderSecondary]
    split_ifs at hsecondary ⊢ <;> linarith
  · apply Prod.Lex.toLex_lt_toLex.mpr
    right
    refine ⟨hy, ?_⟩
    dsimp [r, m]
    dsimp only [leftOrderSecondary] at hsecondary ⊢
    rw [← hy]
    split_ifs at hsecondary ⊢ <;> linarith


@[simp] theorem rightCompletedChain_mem_lower_iff
    (D : SelectedBoundaryTopologyInput E U) (x : ℝ) :
    (x, D.lowerHeight) ∈ D.rightCompletedChain ↔
      x ∈ Icc D.lowerSplit D.lowerRight := by
  change ((D.lowerHeight = D.lowerHeight ∧
      x ∈ Icc D.lowerSplit D.lowerRight) ∨
    (D.lowerHeight ∈ D.occupiedHeights ∧
      x ∈ uIcc (Function.leftLim D.rightEndpoint D.lowerHeight)
        (Function.rightLim D.rightEndpoint D.lowerHeight)) ∨
    (D.lowerHeight = D.upperHeight ∧
      x ∈ Icc D.upperSplit D.upperRight)) ↔ _
  have hnotOccupied : D.lowerHeight ∉ D.occupiedHeights := by
    rw [D.mem_occupiedHeights_iff_height_bounds]
    exact fun h => (lt_irrefl D.lowerHeight h.1)
  simp only [hnotOccupied, false_and, D.lowerHeight_lt_upperHeight.ne,
    true_and, or_false]

@[simp] theorem rightCompletedChain_mem_upper_iff
    (D : SelectedBoundaryTopologyInput E U) (x : ℝ) :
    (x, D.upperHeight) ∈ D.rightCompletedChain ↔
      x ∈ Icc D.upperSplit D.upperRight := by
  change ((D.upperHeight = D.lowerHeight ∧
      x ∈ Icc D.lowerSplit D.lowerRight) ∨
    (D.upperHeight ∈ D.occupiedHeights ∧
      x ∈ uIcc (Function.leftLim D.rightEndpoint D.upperHeight)
        (Function.rightLim D.rightEndpoint D.upperHeight)) ∨
    (D.upperHeight = D.upperHeight ∧
      x ∈ Icc D.upperSplit D.upperRight)) ↔ _
  have hnotOccupied : D.upperHeight ∉ D.occupiedHeights := by
    rw [D.mem_occupiedHeights_iff_height_bounds]
    exact fun h => (lt_irrefl D.upperHeight h.2)
  simp only [hnotOccupied, false_and, D.lowerHeight_lt_upperHeight.ne.symm,
    true_and, false_or]

@[simp] theorem rightCompletedChain_mem_interior_iff
    (D : SelectedBoundaryTopologyInput E U) {x y : ℝ}
    (hy : y ∈ D.occupiedHeights) :
    (x, y) ∈ D.rightCompletedChain ↔
      x ∈ uIcc (Function.leftLim D.rightEndpoint y)
        (Function.rightLim D.rightEndpoint y) := by
  have hb := D.mem_occupiedHeights_iff_height_bounds.mp hy
  change ((y = D.lowerHeight ∧ x ∈ Icc D.lowerSplit D.lowerRight) ∨
    (y ∈ D.occupiedHeights ∧
      x ∈ uIcc (Function.leftLim D.rightEndpoint y)
        (Function.rightLim D.rightEndpoint y)) ∨
    (y = D.upperHeight ∧ x ∈ Icc D.upperSplit D.upperRight)) ↔ _
  simp only [hb.1.ne', false_and, hy, true_and, hb.2.ne, or_false,
    false_or]

theorem rightCompletedChain_snd_mem_Icc
    (D : SelectedBoundaryTopologyInput E U)
    (p : D.rightCompletedChain) :
    p.1.2 ∈ Icc D.lowerHeight D.upperHeight := by
  rcases p.property with hp | hp | hp
  · rw [hp.1]
    exact ⟨le_rfl, D.lowerHeight_lt_upperHeight.le⟩
  · exact (D.mem_occupiedHeights_iff_height_bounds.mp hp.1).imp
      LT.lt.le LT.lt.le
  · rw [hp.1]
    exact ⟨D.lowerHeight_lt_upperHeight.le, le_rfl⟩

theorem rightCompletedChain_exists_between_of_snd_lt
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.rightCompletedChain) (hpq : p.1.2 < q.1.2) :
    ∃ r : D.rightCompletedChain,
      @LT.lt _ D.rightCompletedChainLinearOrder.toLT p r ∧
      @LT.lt _ D.rightCompletedChainLinearOrder.toLT r q := by
  let y : ℝ := (p.1.2 + q.1.2) / 2
  have hpy : p.1.2 < y := by dsimp [y]; linarith
  have hyq : y < q.1.2 := by dsimp [y]; linarith
  have hpBounds := D.rightCompletedChain_snd_mem_Icc p
  have hqBounds := D.rightCompletedChain_snd_mem_Icc q
  have hyOccupied : y ∈ D.occupiedHeights :=
    D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hpBounds.1.trans_lt hpy, hyq.trans_le hqBounds.2⟩
  let r : D.rightCompletedChain :=
    ⟨(Function.leftLim D.rightEndpoint y, y),
      (D.rightCompletedChain_mem_interior_iff hyOccupied).mpr left_mem_uIcc⟩
  exact ⟨r, D.rightCompletedChain_lt_of_snd_lt p r hpy,
    D.rightCompletedChain_lt_of_snd_lt r q hyq⟩

theorem rightCompletedChain_exists_between_of_same_snd
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.rightCompletedChain) (hy : p.1.2 = q.1.2)
    (hpq : @LT.lt _ D.rightCompletedChainLinearOrder.toLT p q) :
    ∃ r : D.rightCompletedChain,
      @LT.lt _ D.rightCompletedChainLinearOrder.toLT p r ∧
      @LT.lt _ D.rightCompletedChainLinearOrder.toLT r q := by
  have hsecondary : D.rightOrderSecondary p.1 < D.rightOrderSecondary q.1 := by
    rcases Prod.Lex.toLex_lt_toLex.mp hpq with hheight | hsecondary
    · exact (lt_irrefl q.1.2 (hy ▸ hheight)).elim
    · exact hsecondary.2
  dsimp only [rightOrderSecondary] at hsecondary
  rw [← hy] at hsecondary
  let m : ℝ := (p.1.1 + q.1.1) / 2
  have hm : m ∈ uIcc p.1.1 q.1.1 := by
    rcases le_total p.1.1 q.1.1 with hpqX | hqpX
    · exact mem_uIcc_of_le (by dsimp [m]; linarith)
        (by dsimp [m]; linarith)
    · exact mem_uIcc_of_ge (by dsimp [m]; linarith)
        (by dsimp [m]; linarith)
  have hrMem : (m, p.1.2) ∈ D.rightCompletedChain := by
    by_cases hlower : p.1.2 = D.lowerHeight
    · rw [hlower]
      apply (D.rightCompletedChain_mem_lower_iff m).mpr
      have hpIcc : p.1.1 ∈ Icc D.lowerSplit D.lowerRight := by
        apply (D.rightCompletedChain_mem_lower_iff p.1.1).mp
        rw [← hlower]
        exact p.property
      have hqIcc : q.1.1 ∈ Icc D.lowerSplit D.lowerRight := by
        apply (D.rightCompletedChain_mem_lower_iff q.1.1).mp
        rw [← hlower, hy]
        exact q.property
      exact uIcc_subset_Icc hpIcc hqIcc hm
    · by_cases hupper : p.1.2 = D.upperHeight
      · rw [hupper]
        apply (D.rightCompletedChain_mem_upper_iff m).mpr
        have hpIcc : p.1.1 ∈ Icc D.upperSplit D.upperRight := by
          apply (D.rightCompletedChain_mem_upper_iff p.1.1).mp
          rw [← hupper]
          exact p.property
        have hqIcc : q.1.1 ∈ Icc D.upperSplit D.upperRight := by
          apply (D.rightCompletedChain_mem_upper_iff q.1.1).mp
          rw [← hupper, hy]
          exact q.property
        exact uIcc_subset_Icc hpIcc hqIcc hm
      · have hoccupied : p.1.2 ∈ D.occupiedHeights := by
          rcases p.property with hp | hp | hp
          · exact (hlower hp.1).elim
          · exact hp.1
          · exact (hupper hp.1).elim
        apply (D.rightCompletedChain_mem_interior_iff hoccupied).mpr
        have hpUIcc :=
          (D.rightCompletedChain_mem_interior_iff hoccupied).mp p.property
        have hqAtHeight : (q.1.1, p.1.2) ∈ D.rightCompletedChain := by
          rw [hy]
          exact q.property
        have hqUIcc :=
          (D.rightCompletedChain_mem_interior_iff hoccupied).mp hqAtHeight
        exact uIcc_subset_uIcc hpUIcc hqUIcc hm
  let r : D.rightCompletedChain := ⟨(m, p.1.2), hrMem⟩
  refine ⟨r, ?_, ?_⟩
  · apply Prod.Lex.toLex_lt_toLex.mpr
    right
    refine ⟨rfl, ?_⟩
    dsimp [r, m]
    dsimp only [rightOrderSecondary]
    split_ifs at hsecondary ⊢ <;> linarith
  · apply Prod.Lex.toLex_lt_toLex.mpr
    right
    refine ⟨hy, ?_⟩
    dsimp [r, m]
    dsimp only [rightOrderSecondary] at hsecondary ⊢
    rw [← hy]
    split_ifs at hsecondary ⊢ <;> linarith


theorem leftCompletedChain_denselyOrdered
    (D : SelectedBoundaryTopologyInput E U) :
    @DenselyOrdered D.leftCompletedChain
      D.leftCompletedChainLinearOrder.toLT := by
  apply @DenselyOrdered.mk _ D.leftCompletedChainLinearOrder.toLT
  intro p q hpq
  rcases Prod.Lex.toLex_lt_toLex.mp hpq with hheight | hsame
  · exact D.leftCompletedChain_exists_between_of_snd_lt p q hheight
  · exact D.leftCompletedChain_exists_between_of_same_snd p q hsame.1 hpq

theorem rightCompletedChain_denselyOrdered
    (D : SelectedBoundaryTopologyInput E U) :
    @DenselyOrdered D.rightCompletedChain
      D.rightCompletedChainLinearOrder.toLT := by
  apply @DenselyOrdered.mk _ D.rightCompletedChainLinearOrder.toLT
  intro p q hpq
  rcases Prod.Lex.toLex_lt_toLex.mp hpq with hheight | hsame
  · exact D.rightCompletedChain_exists_between_of_snd_lt p q hheight
  · exact D.rightCompletedChain_exists_between_of_same_snd p q hsame.1 hpq

/-- The common lower split point belongs to the left completed chain. -/
theorem lowerSplitPoint_mem_leftCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerSplitPoint ∈ D.leftCompletedChain := by
  exact Or.inl ⟨rfl, D.lowerLeft_le_lowerSplit, le_rfl⟩

/-- The common lower split point belongs to the right completed chain. -/
theorem lowerSplitPoint_mem_rightCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    D.lowerSplitPoint ∈ D.rightCompletedChain := by
  exact Or.inl ⟨rfl, le_rfl, D.lowerSplit_le_lowerRight⟩

/-- The common upper split point belongs to the left completed chain. -/
theorem upperSplitPoint_mem_leftCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    D.upperSplitPoint ∈ D.leftCompletedChain := by
  exact Or.inr (Or.inr ⟨rfl, D.upperLeft_le_upperSplit, le_rfl⟩)

/-- The common upper split point belongs to the right completed chain. -/
theorem upperSplitPoint_mem_rightCompletedChain
    (D : SelectedBoundaryTopologyInput E U) :
    D.upperSplitPoint ∈ D.rightCompletedChain := by
  exact Or.inr (Or.inr ⟨rfl, le_rfl, D.upperSplit_le_upperRight⟩)

/-- The bottom element of the left intrinsic traversal. -/
def leftCompletedChainBottom (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChain :=
  ⟨D.lowerSplitPoint, D.lowerSplitPoint_mem_leftCompletedChain⟩

/-- The bottom element of the right intrinsic traversal. -/
def rightCompletedChainBottom (D : SelectedBoundaryTopologyInput E U) :
    D.rightCompletedChain :=
  ⟨D.lowerSplitPoint, D.lowerSplitPoint_mem_rightCompletedChain⟩

/-- The top element of the left intrinsic traversal. -/
def leftCompletedChainTop (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChain :=
  ⟨D.upperSplitPoint, D.upperSplitPoint_mem_leftCompletedChain⟩

/-- The top element of the right intrinsic traversal. -/
def rightCompletedChainTop (D : SelectedBoundaryTopologyInput E U) :
    D.rightCompletedChain :=
  ⟨D.upperSplitPoint, D.upperSplitPoint_mem_rightCompletedChain⟩

/-- The common lower split point is least in the left traversal order. -/
theorem leftCompletedChainBottom_le
    (D : SelectedBoundaryTopologyInput E U) (p : D.leftCompletedChain) :
    @LE.le _ D.leftCompletedChainLinearOrder.toLE D.leftCompletedChainBottom p := by
  change D.leftOrderKey D.lowerSplitPoint ≤ D.leftOrderKey p.1
  simp only [leftOrderKey]
  rw [Prod.Lex.toLex_le_toLex]
  rcases p.2 with hpLower | hpInterior | hpUpper
  · right
    refine ⟨hpLower.1.symm, ?_⟩
    simpa [leftOrderSecondary, lowerSplitPoint, hpLower.1] using
      (neg_le_neg hpLower.2.2)
  · exact Or.inl
      (D.mem_occupiedHeights_iff_height_bounds.mp hpInterior.1).1
  · exact Or.inl (by simpa [lowerSplitPoint, hpUpper.1] using
    D.lowerHeight_lt_upperHeight)

/-- The common lower split point is least in the right traversal order. -/
theorem rightCompletedChainBottom_le
    (D : SelectedBoundaryTopologyInput E U) (p : D.rightCompletedChain) :
    @LE.le _ D.rightCompletedChainLinearOrder.toLE D.rightCompletedChainBottom p := by
  change D.rightOrderKey D.lowerSplitPoint ≤ D.rightOrderKey p.1
  simp only [rightOrderKey]
  rw [Prod.Lex.toLex_le_toLex]
  rcases p.2 with hpLower | hpInterior | hpUpper
  · right
    refine ⟨hpLower.1.symm, ?_⟩
    simpa [rightOrderSecondary, lowerSplitPoint, hpLower.1] using hpLower.2.1
  · exact Or.inl
      (D.mem_occupiedHeights_iff_height_bounds.mp hpInterior.1).1
  · exact Or.inl (by simpa [lowerSplitPoint, hpUpper.1] using
    D.lowerHeight_lt_upperHeight)

/-- The common upper split point is greatest in the left traversal order. -/
theorem leftCompletedChain_le_top
    (D : SelectedBoundaryTopologyInput E U) (p : D.leftCompletedChain) :
    @LE.le _ D.leftCompletedChainLinearOrder.toLE p D.leftCompletedChainTop := by
  change D.leftOrderKey p.1 ≤ D.leftOrderKey D.upperSplitPoint
  simp only [leftOrderKey]
  rw [Prod.Lex.toLex_le_toLex]
  rcases p.2 with hpLower | hpInterior | hpUpper
  · exact Or.inl (hpLower.1.le.trans_lt D.lowerHeight_lt_upperHeight)
  · exact Or.inl
      (D.mem_occupiedHeights_iff_height_bounds.mp hpInterior.1).2
  · right
    refine ⟨hpUpper.1, ?_⟩
    simpa [leftOrderSecondary, upperSplitPoint, hpUpper.1,
      D.lowerHeight_lt_upperHeight.ne' ] using hpUpper.2.2

/-- The common upper split point is greatest in the right traversal order. -/
theorem rightCompletedChain_le_top
    (D : SelectedBoundaryTopologyInput E U) (p : D.rightCompletedChain) :
    @LE.le _ D.rightCompletedChainLinearOrder.toLE p D.rightCompletedChainTop := by
  change D.rightOrderKey p.1 ≤ D.rightOrderKey D.upperSplitPoint
  simp only [rightOrderKey]
  rw [Prod.Lex.toLex_le_toLex]
  rcases p.2 with hpLower | hpInterior | hpUpper
  · exact Or.inl (hpLower.1.le.trans_lt D.lowerHeight_lt_upperHeight)
  · exact Or.inl
      (D.mem_occupiedHeights_iff_height_bounds.mp hpInterior.1).2
  · right
    refine ⟨hpUpper.1, ?_⟩
    simpa [rightOrderSecondary, upperSplitPoint, hpUpper.1,
      D.lowerHeight_lt_upperHeight.ne' ] using
      (neg_le_neg hpUpper.2.1)

/-- The left traversal's explicit order-bottom structure. -/
noncomputable abbrev leftCompletedChainOrderBot
    (D : SelectedBoundaryTopologyInput E U) :
    @OrderBot D.leftCompletedChain D.leftCompletedChainLinearOrder.toLE := by
  refine @OrderBot.mk _ D.leftCompletedChainLinearOrder.toLE
    ⟨D.leftCompletedChainBottom⟩ ?_
  exact D.leftCompletedChainBottom_le

/-- The right traversal's explicit order-bottom structure. -/
noncomputable abbrev rightCompletedChainOrderBot
    (D : SelectedBoundaryTopologyInput E U) :
    @OrderBot D.rightCompletedChain D.rightCompletedChainLinearOrder.toLE := by
  refine @OrderBot.mk _ D.rightCompletedChainLinearOrder.toLE
    ⟨D.rightCompletedChainBottom⟩ ?_
  exact D.rightCompletedChainBottom_le

/-- The left traversal's explicit order-top structure. -/
noncomputable abbrev leftCompletedChainOrderTop
    (D : SelectedBoundaryTopologyInput E U) :
    @OrderTop D.leftCompletedChain D.leftCompletedChainLinearOrder.toLE := by
  refine @OrderTop.mk _ D.leftCompletedChainLinearOrder.toLE
    ⟨D.leftCompletedChainTop⟩ ?_
  exact D.leftCompletedChain_le_top

/-- The right traversal's explicit order-top structure. -/
noncomputable abbrev rightCompletedChainOrderTop
    (D : SelectedBoundaryTopologyInput E U) :
    @OrderTop D.rightCompletedChain D.rightCompletedChainLinearOrder.toLE := by
  refine @OrderTop.mk _ D.rightCompletedChainLinearOrder.toLE
    ⟨D.rightCompletedChainTop⟩ ?_
  exact D.rightCompletedChain_le_top

/-- The explicit left traversal order compares height first and its oriented
fiber coordinate second. -/
theorem leftCompletedChain_le_iff
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain) :
    @LE.le _ D.leftCompletedChainLinearOrder.toLE p q ↔
      p.1.2 < q.1.2 ∨
        (p.1.2 = q.1.2 ∧
          D.leftOrderSecondary p.1 ≤ D.leftOrderSecondary q.1) := by
  change D.leftOrderKey p.1 ≤ D.leftOrderKey q.1 ↔ _
  exact Prod.Lex.toLex_le_toLex

/-- The explicit right traversal order compares height first and its oriented
fiber coordinate second. -/
theorem rightCompletedChain_le_iff
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.rightCompletedChain) :
    @LE.le _ D.rightCompletedChainLinearOrder.toLE p q ↔
      p.1.2 < q.1.2 ∨
        (p.1.2 = q.1.2 ∧
          D.rightOrderSecondary p.1 ≤ D.rightOrderSecondary q.1) := by
  change D.rightOrderKey p.1 ≤ D.rightOrderKey q.1 ↔ _
  exact Prod.Lex.toLex_le_toLex

/-- The planar subtype topology on the left completed chain is separable. -/
theorem leftCompletedChain_separableSpace
    (D : SelectedBoundaryTopologyInput E U) :
    TopologicalSpace.SeparableSpace D.leftCompletedChain := by
  infer_instance

/-- The planar subtype topology on the right completed chain is separable. -/
theorem rightCompletedChain_separableSpace
    (D : SelectedBoundaryTopologyInput E U) :
    TopologicalSpace.SeparableSpace D.rightCompletedChain := by
  infer_instance


end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
