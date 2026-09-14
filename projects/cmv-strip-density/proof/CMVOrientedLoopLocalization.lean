import CMVOrientedLoopRegularCuts
import CMVOrientedLoopEmbeddedness
import CMVOrientedLoopCostAccounting
import CMVOrientedLoopSmoothTrace
import CMVOrientedLoopOrientation

/-!
# Localization for oriented-loop extraction

This module performs the finite-liminf and rectangular-cut stage needed before
extracting oriented boundary loops from arbitrary smooth approximants.  The
original approximants may be unbounded and globally disconnected.  Cropping is
used only for boundary accounting: the resulting cornered open sets are not
asserted to satisfy `IsSmoothDomain` and are not inserted back into the smooth
approximation class.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology symmDiff

noncomputable section

namespace CMVRelaxation
open CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas.FiniteChartCutSystem

/-- The empty exterior domain is a literal smooth domain; its regular-boundary
condition is vacuous. -/
theorem isSmoothDomain_empty : IsSmoothDomain (∅ : Set PlanePoint) := by
  constructor
  · exact isOpen_empty
  · simp


/-- Cropping against the empty exterior is exactly intersection with the
interior of the selected window. -/
theorem openSpliceIn_empty_eq_inter_interior
    {G W : Set PlanePoint} (hG : IsOpen G) :
    openSpliceIn ∅ G W = G ∩ interior W := by
  simp [openSpliceIn, spliceIn, interior_inter, hG.interior_eq]

/-- Every bounded planar target lies strictly inside a symmetric coordinate
rectangle.  The coordinate bound is derived from the ambient product norm. -/
theorem exists_nonneg_strict_coordinate_bound
    {E : Set PlanePoint} (hE : Bornology.IsBounded E) :
    ∃ R : ℝ, 0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hE
  let R : ℝ := max M 0
  refine ⟨R, le_max_right _ _, ?_⟩
  intro p hp
  have hpNorm : ‖p‖ ≤ M := hM p hp
  have hxM : |p.1| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans hpNorm
  have hyM : |p.2| ≤ M := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le p).trans hpNorm
  have hMR : M ≤ R := le_max_left _ _
  have hxR : |p.1| ≤ R := hxM.trans hMR
  have hyR : |p.2| ≤ R := hyM.trans hMR
  exact ⟨⟨by linarith [neg_le_of_abs_le hxR], by linarith [le_of_abs_le hxR]⟩,
    ⟨by linarith [neg_le_of_abs_le hyR], by linarith [le_of_abs_le hyR]⟩⟩
/-- A finite-liminf recovery sequence has a literal strict subsequence whose
term costs are finite and converge to the original liminf. -/
theorem SmoothSequence.exists_strictMono_finiteCost_reindex_of_cost_lt_top
    {lam : ℝ} {E : Set PlanePoint} (A : SmoothSequence)
    (hconv : A.ConvergesTo E) (hcost : A.cost lam < ⊤) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (A.reindex φ).ConvergesTo E ∧
      Tendsto (fun n => smoothCost lam (A.carrier (φ n)))
        atTop (𝓝 (A.cost lam)) ∧
      (A.reindex φ).cost lam = A.cost lam ∧
      ∀ n, smoothCost lam (A.carrier (φ n)) < ⊤ := by
  obtain ⟨u, huStrict, huCostRaw⟩ :=
    (MapClusterPt.liminf
      (u := fun n => smoothCost lam (A.carrier n))
      (f := atTop)).tendsto_subseq
  have huCost :
      Tendsto (fun n => smoothCost lam (A.carrier (u n))) atTop
        (𝓝 (A.cost lam)) := by
    change Tendsto (fun n => smoothCost lam (A.carrier (u n))) atTop
      (𝓝 (liminf (fun n => smoothCost lam (A.carrier n)) atTop)) at huCostRaw
    simpa only [SmoothSequence.cost] using huCostRaw
  have heventually :
      ∀ᶠ n in atTop, smoothCost lam (A.carrier (u n)) < ⊤ :=
    huCost.eventually (Iio_mem_nhds hcost)
  obtain ⟨chi, hchi, hfinite⟩ :=
    extraction_of_eventually_atTop heventually
  let φ : ℕ → ℕ := u ∘ chi
  have hφ : StrictMono φ := huStrict.comp hchi
  have hφCost :
      Tendsto (fun n => smoothCost lam (A.carrier (φ n))) atTop
        (𝓝 (A.cost lam)) := by
    change Tendsto
      ((fun n => smoothCost lam (A.carrier (u n))) ∘ chi) atTop
        (𝓝 (A.cost lam))
    exact huCost.comp hchi.tendsto_atTop
  refine ⟨φ, hφ, A.convergesTo_reindex φ hconv hφ.tendsto_atTop,
    hφCost, A.cost_reindex_eq_of_tendsto φ hφCost, ?_⟩
  intro n
  simpa only [φ, Function.comp_apply] using hfinite n

/-- Kernel-visible package for rectangular localization of an approximating
sequence.  The selected cuts are regular for both the empty exterior and the
actual smooth approximant, with finite face crossings and corner avoidance. -/
def HasOpenRectangularLocalization
    (lam : ℝ) (E : Set PlanePoint) (A : SmoothSequence) : Prop :=
  ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
    0 ≤ R ∧
    E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
    B.ConvergesTo E ∧
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ B = A.reindex φ) ∧
    Tendsto (fun n => smoothCost lam (B.carrier n))
      atTop (𝓝 (A.cost lam)) ∧
    B.cost lam = A.cost lam ∧
    (∀ n, smoothCost lam (B.carrier n) < ⊤) ∧
    (∀ n, l n ∈ Ioo (-R - 2) (-R - 1)) ∧
    (∀ n, r n ∈ Ioo (R + 1) (R + 2)) ∧
    (∀ n, d n ∈ Ioo (-R - 2) (-R - 1)) ∧
    (∀ n, u n ∈ Ioo (R + 1) (R + 2)) ∧
    (∀ n, IsRegularFiniteVerticalSpliceCut ∅ (B.carrier n)
      (closedCutRectangle (-R - 2) (-R - 1) (-R - 2) (R + 2)) (l n)) ∧
    (∀ n, IsRegularFiniteVerticalSpliceCut ∅ (B.carrier n)
      (closedCutRectangle (R + 1) (R + 2) (-R - 2) (R + 2)) (r n)) ∧
    (∀ n, IsRegularFiniteHorizontalSpliceCut ∅ (B.carrier n)
      (closedCutRectangle (-R - 2) (R + 2) (-R - 2) (-R - 1)) (d n)) ∧
    (∀ n, IsRegularFiniteHorizontalSpliceCut ∅ (B.carrier n)
      (closedCutRectangle (-R - 2) (R + 2) (R + 1) (R + 2)) (u n)) ∧
    (∀ n, ∀ p ∈
      ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
        Set PlanePoint),
      p ∉ frontier (∅ : Set PlanePoint) ∧
        p ∉ frontier (B.carrier n)) ∧
    (∀ n, HasFiniteJunctionBoundaryAtlas
      (openSpliceIn ∅ (B.carrier n)
        (closedCutRectangle (l n) (r n) (d n) (u n)))) ∧
    (∀ n, Nonempty (CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas
      (openSpliceIn ∅ (B.carrier n)
        (closedCutRectangle (l n) (r n) (d n) (u n))))) ∧
    (∀ n, Nonempty (FiniteBoundaryTopology
      (openSpliceIn ∅ (B.carrier n)
        (closedCutRectangle (l n) (r n) (d n) (u n))))) ∧
    let W : ℕ → Set PlanePoint := fun n =>
      closedCutRectangle (l n) (r n) (d n) (u n)
    let cropped : ℕ → Set PlanePoint := fun n =>
      openSpliceIn ∅ (B.carrier n) (W n)
    let cutCost : ℕ → ENNReal := fun n =>
      weightedTraceCost lam (spliceCutTrace ∅ (B.carrier n) (W n))
    (∀ n, E ⊆ interior (W n)) ∧
    (∀ n, IsOpen (cropped n)) ∧
    (∀ n, Bornology.IsBounded (cropped n)) ∧
    (∀ n, cropped n = B.carrier n ∩ interior (W n)) ∧
    (∀ᶠ n : ℕ in atTop, cutCost n < ⊤) ∧
    (∀ᶠ n : ℕ in atTop, smoothCost lam (cropped n) < ⊤) ∧
    Tendsto cutCost atTop (𝓝 0) ∧
    Tendsto (fun n => characteristicDistance (cropped n) E)
      atTop (𝓝 0) ∧
    ∀ n, smoothCost lam (cropped n) ≤
      smoothCost lam (B.carrier n) + cutCost n


/-- Finite-liminf localization of an arbitrary actual smooth sequence.

A cofinal reindexing first realizes the original liminf by finite term costs.
Four regular coordinate cuts are then selected in a target-free collar.  The
complete artificial cut trace has vanishing literal weighted cost.  The
canonical cropped representatives are open, bounded, converge globally to the
original target, and their complete-frontier cost is bounded by the selected
original cost plus the cut error.

The cropped representatives can have corners where an approximant meets a cut;
accordingly this theorem deliberately proves only `IsOpen`, not
`IsSmoothDomain`, for them. -/
theorem SmoothSequence.exists_open_rectangular_localization
    {lam : ℝ} (hlam : 1 < lam) {E : Set PlanePoint}
    (hEbounded : Bornology.IsBounded E) (A : SmoothSequence)
    (hconv : A.ConvergesTo E) (hcost : A.cost lam < ⊤) :
    HasOpenRectangularLocalization lam E A := by
  unfold HasOpenRectangularLocalization
  obtain ⟨R, hR, hEcore⟩ :=
    exists_nonneg_strict_coordinate_bound hEbounded
  obtain ⟨φ, hφ, hBconv, hBcostTendstoRaw, hBcost, hBfiniteRaw⟩ :=
    A.exists_strictMono_finiteCost_reindex_of_cost_lt_top hconv hcost
  let B : SmoothSequence := A.reindex φ
  have hBcostTendsto :
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) := by
    simpa only [B, SmoothSequence.reindex_carrier] using hBcostTendstoRaw
  have hBfinite : ∀ n, smoothCost lam (B.carrier n) < ⊤ := by
    intro n
    simpa only [B, SmoothSequence.reindex_carrier] using hBfiniteRaw n
  have hBreindex : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ B = A.reindex ψ :=
    ⟨φ, hφ, rfl⟩
  let emptySeq : ℕ → Set PlanePoint := fun _ => ∅
  let insideSeq : ℕ → Set PlanePoint := fun n => B.carrier n
  have hemptyConv : Tendsto
      (fun n => characteristicDistance (emptySeq n) (∅ : Set PlanePoint))
      atTop (𝓝 0) := by
    simp [emptySeq, characteristicDistance]
  have hinsideConv : Tendsto
      (fun n => characteristicDistance (insideSeq n) E) atTop (𝓝 0) := by
    simpa only [insideSeq, SmoothSequence.ConvergesTo] using hBconv
  have houterMeas : MeasurableSet
      (closedCutRectangle (-R - 2) (R + 2) (-R - 2) (R + 2)) :=
    measurableSet_closedCutRectangle _ _ _ _
  have hemptyFinite : ∀ n,
      FrontierMeasure (emptySeq n)
        (closedCutRectangle (-R - 2) (R + 2) (-R - 2) (R + 2)) ≠ ⊤ := by
    intro n
    simp [emptySeq, FrontierMeasure]
  have hinsideFinite : ∀ n,
      FrontierMeasure (insideSeq n)
        (closedCutRectangle (-R - 2) (R + 2) (-R - 2) (R + 2)) ≠ ⊤ := by
    intro n
    apply frontierMeasure_ne_top_of_smoothCost_ne_top hlam
      (insideSeq n)
      (closedCutRectangle (-R - 2) (R + 2) (-R - 2) (R + 2))
      houterMeas
    exact (hBfinite n).ne
  let KL := closedCutRectangle (-R - 2) (-R - 1) (-R - 2) (R + 2)
  let KR := closedCutRectangle (R + 1) (R + 2) (-R - 2) (R + 2)
  let KD := closedCutRectangle (-R - 2) (R + 2) (-R - 2) (-R - 1)
  let KU := closedCutRectangle (-R - 2) (R + 2) (R + 1) (R + 2)
  let C : Set PlanePoint :=
    Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1)
  have htargetCore : (∅ : Set PlanePoint) ∆ E ⊆ C := by
    intro p hp
    apply hEcore
    simp only [Set.mem_symmDiff, Set.mem_empty_iff_false, false_and,
      not_false_eq_true, and_true] at hp
    exact hp.resolve_left id
  have hagree : ∀ K : Set PlanePoint, Disjoint K C →
      (∅ : Set PlanePoint) ∩ K = E ∩ K := by
    intro K hKC
    ext p
    constructor
    · rintro ⟨hp, _⟩
      exact hp.elim
    · rintro ⟨hpE, hpK⟩
      have hpDiff : p ∈ (∅ : Set PlanePoint) ∆ E := by
        simp only [Set.mem_symmDiff, Set.mem_empty_iff_false, false_and,
          not_false_eq_true, and_true]
        exact Or.inr hpE
      exact ((Set.disjoint_left.1 hKC hpK) (htargetCore hpDiff)).elim
  have hKLC : Disjoint KL C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpx.2) hpxC.1)
  have hKRC : Disjoint KR C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpx.1) hpxC.2)
  have hKDC : Disjoint KD C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpy.2) hpyC.1)
  have hKUC : Disjoint KU C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpy.1) hpyC.2)
  have hleft := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KL) hemptyConv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KL) hinsideConv)
    (hagree KL hKLC)
  have hright := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KR) hemptyConv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KR) hinsideConv)
    (hagree KR hKRC)
  have hlower := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KD) hemptyConv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KD) hinsideConv)
    (hagree KD hKDC)
  have hupper := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KU) hemptyConv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KU) hinsideConv)
    (hagree KU hKUC)
  obtain ⟨l, r, d, u, hl, hr, hd, hu, hregL, hregR, hregD, hregU,
      hcorner, hcut⟩ :=
    exists_regularFinite_closedCutRectangle_spliceCutTrace_tendsto_zero
      (a₀ := -R - 2) (a₁ := -R - 1) (b₀ := R + 1) (b₁ := R + 2)
      (c₀ := -R - 2) (c₁ := -R - 1) (d₀ := R + 1) (d₁ := R + 2)
      hlam emptySeq insideSeq
      (fun _ => isSmoothDomain_empty) (fun n => B.smooth n)
      (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith)
      hemptyFinite hinsideFinite
      (by simpa only [KL] using hleft)
      (by simpa only [KR] using hright)
      (by simpa only [KD] using hlower)
      (by simpa only [KU] using hupper)
  let W : ℕ → Set PlanePoint := fun n =>
    closedCutRectangle (l n) (r n) (d n) (u n)
  let cropped : ℕ → Set PlanePoint := fun n =>
    openSpliceIn ∅ (B.carrier n) (W n)
  let cutCost : ℕ → ENNReal := fun n =>
    weightedTraceCost lam (spliceCutTrace ∅ (B.carrier n) (W n))
  have htargetInterior : ∀ n, E ⊆ interior (W n) := by
    intro n p hp
    have hpCore := hEcore hp
    change p ∈ interior (closedCutRectangle (l n) (r n) (d n) (u n))
    rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by linarith [(hl n).2, hpCore.1.1],
      by linarith [(hr n).1, hpCore.1.2]⟩,
      ⟨by linarith [(hd n).2, hpCore.2.1],
        by linarith [(hu n).1, hpCore.2.2]⟩⟩
  have htargetWindow : ∀ n, (∅ : Set PlanePoint) ∆ E ⊆ W n := by
    intro n p hp
    apply interior_subset (htargetInterior n ?_)
    simp only [Set.mem_symmDiff, Set.mem_empty_iff_false, false_and,
      not_false_eq_true, and_true] at hp
    exact hp.resolve_left id
  have hrawConv : Tendsto (fun n =>
      characteristicDistance
        (spliceIn (emptySeq n) (insideSeq n) (W n)) E)
      atTop (𝓝 0) := by
    have hdist_le : ∀ n,
        characteristicDistance
            (spliceIn (emptySeq n) (insideSeq n) (W n)) E ≤
          characteristicDistance (emptySeq n) (∅ : Set PlanePoint) +
            characteristicDistance (insideSeq n) E := by
      intro n
      refine (characteristicDistance_spliceIn_le (htargetWindow n)).trans ?_
      apply add_le_add le_rfl
      unfold characteristicDistance
      exact measure_mono inter_subset_left
    have hdist_sum : Tendsto (fun n =>
        characteristicDistance (emptySeq n) (∅ : Set PlanePoint) +
          characteristicDistance (insideSeq n) E) atTop (𝓝 0) := by
      simpa using hemptyConv.add hinsideConv
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hdist_sum (fun _ => bot_le) hdist_le
  have hcroppedOpen : ∀ n, IsOpen (cropped n) := by
    intro n
    exact isOpen_openSpliceIn _ _ _
  have hcroppedBounded : ∀ n, Bornology.IsBounded (cropped n) := by
    intro n
    have hWbounded : Bornology.IsBounded (W n) := by
      exact (Metric.isBounded_Icc (l n) (r n)).prod
        (Metric.isBounded_Icc (d n) (u n))
    apply hWbounded.subset
    intro p hp
    have hpRaw := openSpliceIn_subset_spliceIn ∅ (B.carrier n) (W n) hp
    rcases hpRaw with hpEmpty | hpInside
    · exact hpEmpty.1.elim
    · exact hpInside.2
  have hcroppedEq : ∀ n, cropped n = B.carrier n ∩ interior (W n) := by
    intro n
    exact openSpliceIn_empty_eq_inter_interior (B.smooth n).isOpen
  have hcutTendsto : Tendsto cutCost atTop (𝓝 0) := by
    simpa only [cutCost, emptySeq, insideSeq, W] using hcut
  have hcutFinite : ∀ᶠ n : ℕ in atTop, cutCost n < ⊤ :=
    hcutTendsto.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  have hcroppedConv : Tendsto
      (fun n => characteristicDistance (cropped n) E) atTop (𝓝 0) := by
    have heq : (fun n => characteristicDistance (cropped n) E) =
        fun n => characteristicDistance
          (spliceIn (emptySeq n) (insideSeq n) (W n)) E := by
      funext n
      apply characteristicDistance_openSpliceIn_eq_spliceIn
      · exact isOpen_empty
      · exact (B.smooth n).isOpen
      · apply volume_frontier_closedCutRectangle
        · linarith [(hl n).2, (hr n).1]
        · linarith [(hd n).2, (hu n).1]
    rw [heq]
    simpa only [emptySeq, insideSeq, W] using hrawConv
  have hcostBound : ∀ n, smoothCost lam (cropped n) ≤
      smoothCost lam (B.carrier n) + cutCost n := by
    intro n
    have hlr : l n < r n := by linarith [(hl n).2, (hr n).1]
    have hdu : d n < u n := by linarith [(hd n).2, (hu n).1]
    have hopenCost : smoothCost lam (cropped n) =
        smoothCost lam (spliceIn ∅ (B.carrier n) (W n)) := by
      apply smoothCost_openSpliceIn_eq_smoothCost_spliceIn
      · exact isOpen_empty
      · exact (B.smooth n).isOpen
      · exact isClosed_Icc.prod isClosed_Icc
      · exact closure_interior_closedCutRectangle hlr hdu
    have hlocalGlobal : smoothCostOn lam (B.carrier n) (interior (W n)) ≤
        smoothCost lam (B.carrier n) := by
      calc
        smoothCostOn lam (B.carrier n) (interior (W n)) ≤
            smoothCostOn lam (B.carrier n) univ :=
          smoothCostOn_mono lam (B.carrier n) (subset_univ _)
        _ = smoothCost lam (B.carrier n) := by
          simp [smoothCostOn, smoothCost]
    rw [hopenCost]
    calc
      smoothCost lam (spliceIn ∅ (B.carrier n) (W n)) ≤
          smoothCostOn lam ∅ (interior (W n)ᶜ) +
            smoothCostOn lam (B.carrier n) (interior (W n)) +
              cutCost n := by
          simpa only [cutCost] using
            smoothCost_spliceIn_le_outside_add_inside_add_cutTrace
              lam ∅ (B.carrier n) (W n)
      _ = smoothCostOn lam (B.carrier n) (interior (W n)) +
            cutCost n := by
          simp [smoothCostOn, FrontierMeasure]
      _ ≤ smoothCost lam (B.carrier n) + cutCost n :=
        add_le_add hlocalGlobal le_rfl
  have hcroppedFinite :
      ∀ᶠ n : ℕ in atTop, smoothCost lam (cropped n) < ⊤ := by
    filter_upwards [hcutFinite] with n hn
    exact (hcostBound n).trans_lt
      (ENNReal.add_lt_top.2 ⟨hBfinite n, hn⟩)
  have hboundaryTopology :
      ∀ n,
        HasFiniteJunctionBoundaryAtlas
          (openSpliceIn ∅ (B.carrier n)
            (closedCutRectangle (l n) (r n) (d n) (u n))) ∧
        Nonempty (CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas
          (openSpliceIn ∅ (B.carrier n)
            (closedCutRectangle (l n) (r n) (d n) (u n)))) := by
    intro n
    have hlr : l n < r n := by linarith [(hl n).2, (hr n).1]
    have hdu : d n < u n := by linarith [(hd n).2, (hu n).1]
    have hL : IsRegularFiniteVerticalSpliceCut ∅ (B.carrier n)
        (closedCutRectangle (-R - 2) (-R - 1) (-R - 2) (R + 2))
          (l n) := by
      simpa only [emptySeq, insideSeq] using hregL n
    have hRcut : IsRegularFiniteVerticalSpliceCut ∅ (B.carrier n)
        (closedCutRectangle (R + 1) (R + 2) (-R - 2) (R + 2))
          (r n) := by
      simpa only [emptySeq, insideSeq] using hregR n
    have hD : IsRegularFiniteHorizontalSpliceCut ∅ (B.carrier n)
        (closedCutRectangle (-R - 2) (R + 2) (-R - 2) (-R - 1))
          (d n) := by
      simpa only [emptySeq, insideSeq] using hregD n
    have hU : IsRegularFiniteHorizontalSpliceCut ∅ (B.carrier n)
        (closedCutRectangle (-R - 2) (R + 2) (R + 1) (R + 2))
          (u n) := by
      simpa only [emptySeq, insideSeq] using hregU n
    have hfinite :
        (FiniteJunctionRepair.spliceJunctionSet
          ∅ (B.carrier n) (l n) (r n) (d n) (u n)).Finite := by
      exact
        FiniteJunctionRepair.finite_spliceJunctionSet_of_selected_regularFinite_closedCutRectangle
            (A := ∅) (B := B.carrier n)
            (a₀ := -R - 2) (a₁ := -R - 1)
            (b₀ := R + 1) (b₁ := R + 2)
            (c₀ := -R - 2) (c₁ := -R - 1)
            (d₀ := R + 1) (d₁ := R + 2)
            (l := l n) (r := r n) (d := d n) (u := u n)
            (by linarith) (by linarith)
            (hl n) (hr n) (hd n) (hu n) hL hRcut hD hU
    have hcornerG : ∀ p ∈
        ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint),
        p ∉ frontier (B.carrier n) := by
      intro p hp
      simpa only [insideSeq] using (hcorner n p hp).2
    refine ⟨hasFiniteJunctionBoundaryAtlas_openSpliceIn
      isSmoothDomain_empty (B.smooth n) hlr hdu hfinite, ?_⟩
    exact ⟨boundaryHalfSpaceAtlas_openSpliceIn_empty_of_regularFiniteCuts
      (B.smooth n) (by linarith) (by linarith)
      (hl n) (hr n) (hd n) (hu n) hL hRcut hD hU hcornerG⟩
  have hpiecewise := fun n => (hboundaryTopology n).1
  have hfullAtlas := fun n => (hboundaryTopology n).2
  have hfiniteTopology :
      ∀ n, Nonempty (FiniteBoundaryTopology
        (openSpliceIn ∅ (B.carrier n)
          (closedCutRectangle (l n) (r n) (d n) (u n)))) := by
    intro n
    rcases hfullAtlas n with ⟨atlas⟩
    exact ⟨finiteBoundaryTopologyOfAtlas atlas (hcroppedBounded n)⟩
  refine ⟨B, R, l, r, d, u, hR, hEcore, hBconv, hBreindex,
    hBcostTendsto, hBcost, hBfinite, hl, hr, hd, hu,
    ?_, ?_, ?_, ?_, ?_, hpiecewise, hfullAtlas, hfiniteTopology, ?_⟩
  · simpa only [emptySeq, insideSeq] using hregL
  · simpa only [emptySeq, insideSeq] using hregR
  · simpa only [emptySeq, insideSeq] using hregD
  · simpa only [emptySeq, insideSeq] using hregU
  · simpa only [emptySeq, insideSeq] using hcorner
  · dsimp only
    exact ⟨htargetInterior, hcroppedOpen, hcroppedBounded, hcroppedEq,
      hcutFinite, hcroppedFinite, hcutTendsto, hcroppedConv, hcostBound⟩

/-- The local one-manifold data derived by localization can be consumed without
unpacking the quantitative cut and convergence tail of the package. -/
theorem HasOpenRectangularLocalization.exists_finiteJunctionBoundaryAtlases
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, HasFiniteJunctionBoundaryAtlas
        (openSpliceIn ∅ (B.carrier n)
          (closedCutRectangle (l n) (r n) (d n) (u n))) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, _hl, _hr, _hd, _hu, _hL, _hRcut, _hD, _hU, _hcorner,
      hpiecewise, _hfullAtlas, _hfiniteTopology, _hquantitative⟩
  exact ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex,
    htendsto, hcost, hpiecewise⟩

/-- Every localized crop has the complete actual boundary atlas required by
the retained finite-component and finite-chart-cut topology.  In particular,
no component list or loop is supplied as an input to localization. -/
theorem HasOpenRectangularLocalization.exists_boundaryHalfSpaceAtlases
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty (CMVBoundaryLocalAtlas.BoundaryHalfSpaceAtlas
        (openSpliceIn ∅ (B.carrier n)
          (closedCutRectangle (l n) (r n) (d n) (u n)))) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, _hl, _hr, _hd, _hu, _hL, _hRcut, _hD, _hU, _hcorner,
      _hpiecewise, hfullAtlas, _hfiniteTopology, _hquantitative⟩
  exact ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex,
    htendsto, hcost, hfullAtlas⟩

/-- Localization derives the finite connected-component inventory and finite
compact chart-arc cover termwise. -/
theorem HasOpenRectangularLocalization.exists_finiteBoundaryTopologies
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty (FiniteBoundaryTopology
        (openSpliceIn ∅ (B.carrier n)
          (closedCutRectangle (l n) (r n) (d n) (u n)))) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, _hl, _hr, _hd, _hu, _hL, _hRcut, _hD, _hU, _hcorner,
      _hpiecewise, _hfullAtlas, hfiniteTopology, _hquantitative⟩
  exact ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex,
    htendsto, hcost, hfiniteTopology⟩

/-- Localization refines the finite chart cut by every actual nonsmooth crop
junction.  Each resulting open quotient arc therefore consists entirely of
points carrying source-derived oriented smooth graph germs; no merely
topological chart is used as a regularity witness. -/
theorem HasOpenRectangularLocalization.exists_finitePiecewiseRegularBoundaryTopologies
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty (FinitePiecewiseRegularBoundaryTopology
        (openSpliceIn ∅ (B.carrier n)
          (closedCutRectangle (l n) (r n) (d n) (u n)))) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, _hl, _hr, _hd, _hu, _hL, _hRcut, _hD, _hU, _hcorner,
      hpiecewise, hfullAtlas, _hfiniteTopology, hquantitative⟩
  dsimp only at hquantitative
  rcases hquantitative with
    ⟨_htarget, _hopen, hbounded, _hcrop, _hcutFinite, _hcropFinite,
      _hcutTendsto, _hcropConv, _hcostBound⟩
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n
  obtain ⟨atlas⟩ := hfullAtlas n
  exact ⟨finitePiecewiseRegularBoundaryTopologyOfAtlas atlas
    (hbounded n) (hpiecewise n)⟩

/-- The termwise topology can be chosen with its exceptional set identified
definitionally with the actual rectangular splice-junction set.  The same
dependent package retains its occupied-left branch assignment, avoiding the
provenance loss of an existentially chosen exceptional set. -/
theorem HasOpenRectangularLocalization.exists_actualJunctionOrientedTopologies
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : FinitePiecewiseRegularBoundaryTopology
          (openSpliceIn ∅ (B.carrier n)
            (closedCutRectangle (l n) (r n) (d n) (u n))),
        T.exceptionalPoints =
            FiniteJunctionRepair.spliceJunctionSet
              ∅ (B.carrier n) (l n) (r n) (d n) (u n) ∧
          Nonempty (OccupiedLeftArcBranchAssignment T) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, hl, hr, hd, hu, hL, hRcut, hD, hU, _hcorner,
      _hpiecewise, hfullAtlas, _hfiniteTopology, hquantitative⟩
  dsimp only at hquantitative
  rcases hquantitative with
    ⟨_htarget, _hopen, hbounded, _hcrop, _hcutFinite, _hcropFinite,
      _hcutTendsto, _hcropConv, _hcostBound⟩
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n
  have hlr : l n < r n := by linarith [(hl n).2, (hr n).1]
  have hdu : d n < u n := by linarith [(hd n).2, (hu n).1]
  have hfinite :
      (FiniteJunctionRepair.spliceJunctionSet
        ∅ (B.carrier n) (l n) (r n) (d n) (u n)).Finite := by
    exact
      FiniteJunctionRepair.finite_spliceJunctionSet_of_selected_regularFinite_closedCutRectangle
        (A := ∅) (B := B.carrier n)
        (a₀ := -R - 2) (a₁ := -R - 1)
        (b₀ := R + 1) (b₁ := R + 2)
        (c₀ := -R - 2) (c₁ := -R - 1)
        (d₀ := R + 1) (d₁ := R + 2)
        (l := l n) (r := r n) (d := d n) (u := u n)
        (by linarith) (by linarith)
        (hl n) (hr n) (hd n) (hu n)
        (hL n) (hRcut n) (hD n) (hU n)
  obtain ⟨atlas⟩ := hfullAtlas n
  let data := finiteJunctionBoundaryData_openSpliceIn
    isSmoothDomain_empty (B.smooth n) hlr hdu hfinite
  let T := finitePiecewiseRegularBoundaryTopologyOfData
    atlas (hbounded n) data
  refine ⟨T, ?_, ⟨T.occupiedLeftArcBranchAssignment⟩⟩
  rfl

/-- The actual localized sequence admits a global occupied-left branch
assignment on every point of every finite open arc.  The assignment also
induces a reference branch on each half-edge; chart-independence and
cross-half-edge coherence are supplied by `CMVOrientedLoopOrientation`. -/
theorem HasOpenRectangularLocalization.exists_occupiedLeftArcBranchAssignments
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, Nonempty
        (Σ T : FinitePiecewiseRegularBoundaryTopology
            (openSpliceIn ∅ (B.carrier n)
              (closedCutRectangle (l n) (r n) (d n) (u n))),
          OccupiedLeftArcBranchAssignment T) := by
  obtain ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex,
      htendsto, hcost, htopology⟩ :=
    h.exists_finitePiecewiseRegularBoundaryTopologies
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex,
    htendsto, hcost, ?_⟩
  intro n
  obtain ⟨T⟩ := htopology n
  exact ⟨⟨T, T.occupiedLeftArcBranchAssignment⟩⟩
/-- The same localization witnesses provide both endpoint-controlled branches
at every transverse source/cut crossing. The source graph and straight cut
trace are smooth, embedded, nonstationary, occupied-left extensions through
the junction; their certified half-spaces reconstruct the cropped carrier
locally. Clean rectangle corners remain the two-straight-side case. -/
theorem HasOpenRectangularLocalization.exists_transverseEndpointTraces
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n (p : PlanePoint),
        p ∈ FiniteJunctionRepair.spliceJunctionSet
          ∅ (B.carrier n) (l n) (r n) (d n) (u n) →
        p ∉ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        Nonempty
          (FiniteJunctionRepair.OccupiedLeftTransverseEndpointTraces
            (openSpliceIn ∅ (B.carrier n)
              (closedCutRectangle (l n) (r n) (d n) (u n)))
            (B.carrier n) p) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, hl, hr, hd, hu, hL, hRcut, hD, hU, _hcorner,
      _hpiecewise, _hfullAtlas, _hfiniteTopology, _hquantitative⟩
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n p hpJ hpCorner
  exact exists_occupiedLeftTransverseEndpointTraces_of_noncornerJunction
    (B.smooth n).isOpen (by linarith) (by linarith)
    (hl n) (hr n) (hd n) (hu n)
    (hL n) (hRcut n) (hD n) (hU n) hpJ hpCorner
/-- The same selected rectangles also expose both endpoint-controlled straight
branches at every clean corner. The returned coordinate sides are exactly the
two inward half-spaces, locally reconstructing the rectangle interior. -/
theorem HasOpenRectangularLocalization.exists_cleanCornerCutTraces
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n (p : PlanePoint),
        p ∈ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        ∃ verticalSide horizontalSide :
            FiniteJunctionRepair.SpliceGraphOccupiedSide,
          ∀ᶠ q in 𝓝 p,
            q ∈ interior
                (closedCutRectangle (l n) (r n) (d n) (u n)) ↔
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  verticalSide
                  (FiniteJunctionRepair.cutNormalCoordinate
                    .vertical p q) ∧
                CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  horizontalSide
                  (FiniteJunctionRepair.cutNormalCoordinate
                    .horizontal p q) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, hl, hr, hd, hu, _hL, _hRcut, _hD, _hU, _hcorner,
      _hpiecewise, _hfullAtlas, _hfiniteTopology, _hquantitative⟩
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n p hp
  exact
    FiniteJunctionRepair.exists_occupiedCutSides_at_closedCutRectangle_corner
      (by linarith [(hl n).2, (hr n).1])
      (by linarith [(hd n).2, (hu n).1]) hp



/-- On every actual localized crop, each derived cut vertex has a cut-free
two-sided chart neighborhood, whose distinct negative and positive germ arcs
exhaust all incidence.  Thus every termwise finite-arc graph has vertex degree
exactly two without supplied adjacency data. -/
theorem HasOpenRectangularLocalization.exists_finiteBoundaryIncidences
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : FiniteBoundaryTopology
          (openSpliceIn ∅ (B.carrier n)
            (closedCutRectangle (l n) (r n) (d n) (u n))),
        ∀ v : T.chartCuts.cutPoints,
          ∃ N : CutPointCoreNeighborhood T.chartCuts v,
            Nat.card (T.chartCuts.IncidentArc v) = 2 ∧
            N.negativeArcIndex ≠ N.positiveArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.negativeArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.positiveArcIndex := by
  obtain ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
      hcost, htopology⟩ := h.exists_finiteBoundaryTopologies
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n
  obtain ⟨T⟩ := htopology n
  refine ⟨T, ?_⟩
  intro v
  let N := cutPointCoreNeighborhood T.chartCuts v
  exact ⟨N, N.incidentArc_natCard_eq_two,
    N.negativeArcIndex_ne_positiveArcIndex,
    N.cutPoint_mem_negativeArcClosure,
    N.cutPoint_mem_positiveArcClosure⟩


/-- The exact incidence data on every localized crop canonically generates a
finite half-edge traversal. Starting from any actual incident endpoint/arc
pair, repeatedly taking the other germ and crossing its arc returns after a
positive number of steps. -/
theorem HasOpenRectangularLocalization.exists_finiteBoundaryCyclicTraversals
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : FiniteBoundaryTopology
          (openSpliceIn ∅ (B.carrier n)
            (closedCutRectangle (l n) (r n) (d n) (u n))),
        (∀ v : T.chartCuts.cutPoints,
          ∃ N : CutPointCoreNeighborhood T.chartCuts v,
            Nat.card (T.chartCuts.IncidentArc v) = 2 ∧
            N.negativeArcIndex ≠ N.positiveArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.negativeArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.positiveArcIndex) ∧
        ∀ e : T.chartCuts.HalfEdge,
          ∃ k : ℕ, 0 < k ∧
            ((T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[k]) e = e := by
  obtain ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
      hcost, hincidence⟩ := h.exists_finiteBoundaryIncidences
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n
  obtain ⟨T, hvertices⟩ := hincidence n
  exact ⟨T, hvertices, T.chartCuts.exists_pos_iterate_walkStep_eq⟩

/-- The localized finite traversal is realized stepwise by actual embedded
compact boundary arcs.  Each path starts at the current cut vertex, ends at
the next walk vertex, and has exactly the selected arc closure as its image. -/
theorem HasOpenRectangularLocalization.exists_finiteBoundaryGeometricTraversals
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, ∃ T : FiniteBoundaryTopology
          (openSpliceIn ∅ (B.carrier n)
            (closedCutRectangle (l n) (r n) (d n) (u n))),
        (∀ v : T.chartCuts.cutPoints,
          ∃ N : CutPointCoreNeighborhood T.chartCuts v,
            Nat.card (T.chartCuts.IncidentArc v) = 2 ∧
            N.negativeArcIndex ≠ N.positiveArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.negativeArcIndex ∧
            v.1 ∈ T.chartCuts.finiteArcClosure N.positiveArcIndex) ∧
        ∀ e : T.chartCuts.HalfEdge,
          ∃ k : ℕ, 0 < k ∧
            ((T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[k]) e = e ∧
            ∀ i : Fin k,
              Function.Injective
                  (T.chartCuts.walkArcPath
                    (((T.chartCuts.walkStep :
                      T.chartCuts.HalfEdge →
                        T.chartCuts.HalfEdge)^[i.1]) e)) ∧
                Set.range
                    (T.chartCuts.walkArcPath
                      (((T.chartCuts.walkStep :
                        T.chartCuts.HalfEdge →
                          T.chartCuts.HalfEdge)^[i.1]) e)) =
                  Subtype.val ''
                    T.chartCuts.finiteArcClosure
                      (T.chartCuts.switchHalfEdge
                        (((T.chartCuts.walkStep :
                          T.chartCuts.HalfEdge →
                            T.chartCuts.HalfEdge)^[i.1]) e)).1.2 := by
  obtain ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
      hcost, htraversals⟩ := h.exists_finiteBoundaryCyclicTraversals
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  intro n
  obtain ⟨T, hvertices, _hcycles⟩ := htraversals n
  exact ⟨T, hvertices, T.chartCuts.exists_pos_geometric_walkCycle⟩


/-- Per-crop contract for the strongest currently justified geometric output:
all exceptional junctions are cuts. Every nonexceptional frontier point,
including each artificial chart-cut endpoint, has an explicit smooth
nonstationary local trace directed with the certified occupied side on its
left. Compact arcs form a once-indexed endpoint-overlap cover. Every selected
open arc has one occupied-left orientation in the normalized finite-arc path
parameter, shared by every local occupied-left chart along that arc, with the
induced endpoint-relative reversal under `crossHalfEdge`. Opposite traversals
are
quotiented; one selected minimal closed path realizes each geometric orbit and
visits each assigned arc exactly once. Its cut vertices do not repeat before
closure, and distinct nonadjacent traversal pieces are disjoint. Selected loop
images are pairwise disjoint, cover the complete frontier, and their literal
weighted Euclidean image costs sum with coefficient one to the actual
`smoothCost`. -/
def HasFiniteBoundaryClosedWalkPaths (lam : ℝ) (O : Set PlanePoint) : Prop :=
  ∃ T : FinitePiecewiseRegularBoundaryTopology O,
    smoothCost lam O =
      ∑' j : T.chartCuts.BoundaryLoopIndex,
        weightedTraceCost lam
          (Set.range (T.chartCuts.boundaryGeometricWalkLoop j).path) ∧
    (∀ p : CMVBoundaryLocalAtlas.FrontierSpace O,
      p.1 ∉ T.exceptionalPoints →
        ∃ axis : FiniteJunctionRepair.SpliceCutAxis,
          ∃ side : FiniteJunctionRepair.SpliceGraphOccupiedSide,
            Nonempty (FiniteJunctionRepair.OccupiedLeftRegularTrace
              axis side O p.1)) ∧
    HasGloballyOrientedOpenArcs T ∧
    T.chartCuts.HasNonduplicatingFiniteArcPathCover ∧
    (∀ h : T.chartCuts.HalfEdge,
      (Set.Iio
        (Function.minimalPeriod
          (T.chartCuts.walkStep :
            T.chartCuts.HalfEdge → T.chartCuts.HalfEdge) h)).InjOn
          (fun n =>
            (T.chartCuts.switchHalfEdge
              (((T.chartCuts.walkStep :
                T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n]) h)).1.2)) ∧
    T.chartCuts.HasEmbeddedBoundaryArcCycles ∧
    (∀ h e : T.chartCuts.HalfEdge,
      e ∈ T.chartCuts.walkCycle h →
        e ∉ T.chartCuts.walkCycle (T.chartCuts.crossHalfEdge h)) ∧
    Function.Surjective T.chartCuts.boundaryLoopIndexOfHalfEdge ∧
    (∀ h k : T.chartCuts.HalfEdge,
      T.chartCuts.boundaryLoopIndexOfHalfEdge h =
          T.chartCuts.boundaryLoopIndexOfHalfEdge k ↔
        T.chartCuts.walkStep.SameCycle h k ∨
          T.chartCuts.walkStep.SameCycle
            (T.chartCuts.crossHalfEdge h) k) ∧
    (frontier O = ∅ → IsEmpty T.chartCuts.BoundaryLoopIndex) ∧
    (∀ j : T.chartCuts.BoundaryLoopIndex,
      Set.range (T.chartCuts.boundaryGeometricWalkLoop j).path =
        ⋃ e : {e : T.chartCuts.ArcIndex //
            T.chartCuts.arcBoundaryLoopIndex e = j},
          Set.range (T.chartCuts.finiteArcPathLR e.1)) ∧
    (∀ (j : T.chartCuts.BoundaryLoopIndex) (e : T.chartCuts.ArcIndex),
      T.chartCuts.arcBoundaryLoopIndex e = j →
        ∃! n : ℕ,
          n < Function.minimalPeriod
            (T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)
            (T.chartCuts.boundaryLoopHalfEdge j) ∧
          (T.chartCuts.switchHalfEdge
            (((T.chartCuts.walkStep :
              T.chartCuts.HalfEdge → T.chartCuts.HalfEdge)^[n])
              (T.chartCuts.boundaryLoopHalfEdge j))).1.2 = e) ∧
    (∀ j : T.chartCuts.BoundaryLoopIndex,
      weightedTraceCost lam
          (Set.range (T.chartCuts.boundaryGeometricWalkLoop j).path) =
        ∑' e : {e : T.chartCuts.ArcIndex //
            T.chartCuts.arcBoundaryLoopIndex e = j},
          weightedTraceCost lam
            (Set.range (T.chartCuts.finiteArcPathLR e.1))) ∧
    (∀ j : T.chartCuts.BoundaryLoopIndex,
      IsCompact (Set.range
        (T.chartCuts.boundaryGeometricWalkLoop j).path) ∧
      MeasurableSet (Set.range
        (T.chartCuts.boundaryGeometricWalkLoop j).path)) ∧
    (∀ {j k : T.chartCuts.BoundaryLoopIndex}, j ≠ k →
      Disjoint
        (Set.range (T.chartCuts.boundaryGeometricWalkLoop j).path)
        (Set.range (T.chartCuts.boundaryGeometricWalkLoop k).path)) ∧
    (⋃ j : T.chartCuts.BoundaryLoopIndex,
      Set.range (T.chartCuts.boundaryGeometricWalkLoop j).path) =
        frontier O

/-- The strengthened localized output uses the same crop witnesses as the
retained convergence and cost estimates.  The selected minimal closed paths
realize exactly the once-indexed arc fibers, visit each assigned arc exactly
once, have nonrepeating cut vertices, and intersect only between
cyclically adjacent pieces. They cover the complete frontier and carry its
exact coefficient-one weighted Euclidean cost. Distinct selected loop images
are disjoint. Quotienting by directed walk orbit and crossed reversal removes
cyclic base-point and opposite-direction duplicates; an empty frontier yields
an empty family. Every nonexceptional frontier point, including every
artificial chart-cut endpoint, has an explicit `C∞`, everywhere-nonstationary
trace with a determinant certificate that the actual occupied side is left.
The same selected finite-arc topology now carries occupied-left branches on
every open arc and one propagated direction in the actual normalized
finite-arc path parameter, shared by every local occupied-left chart on that
arc. Its endpoint-relative direction reverses under `crossHalfEdge`. Every
transverse source/cut endpoint carries both regular occupied-left extensions
and its exact local crop model; clean rectangle corners carry the two inward
straight extensions. Compatibility with `switchHalfEdge`/`walkStep`, global
finite piecewise-`C¹` parameterizations, parameterized weighted-length
equality, and winding remain separate obligations. -/
theorem HasOpenRectangularLocalization.exists_finiteBoundaryClosedWalkPaths
    {lam : ℝ} {E : Set PlanePoint} {A : SmoothSequence}
    (h : HasOpenRectangularLocalization lam E A) :
    ∃ (B : SmoothSequence) (R : ℝ) (l r d u : ℕ → ℝ),
      0 ≤ R ∧
      E ⊆ Ioo (-R - 1) (R + 1) ×ˢ Ioo (-R - 1) (R + 1) ∧
      B.ConvergesTo E ∧
      (∃ phi : ℕ → ℕ, StrictMono phi ∧ B = A.reindex phi) ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      let W : ℕ → Set PlanePoint := fun n =>
        closedCutRectangle (l n) (r n) (d n) (u n)
      let cropped : ℕ → Set PlanePoint := fun n =>
        openSpliceIn ∅ (B.carrier n) (W n)
      let cutCost : ℕ → ENNReal := fun n =>
        weightedTraceCost lam (spliceCutTrace ∅ (B.carrier n) (W n))
      Tendsto cutCost atTop (𝓝 0) ∧
      Tendsto (fun n => characteristicDistance (cropped n) E)
        atTop (𝓝 0) ∧
      (∀ n, smoothCost lam (cropped n) ≤
        smoothCost lam (B.carrier n) + cutCost n) ∧
      (∀ n (p : PlanePoint),
        p ∈ FiniteJunctionRepair.spliceJunctionSet
          ∅ (B.carrier n) (l n) (r n) (d n) (u n) →
        p ∉ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        Nonempty
          (FiniteJunctionRepair.OccupiedLeftTransverseEndpointTraces
            (cropped n) (B.carrier n) p)) ∧
      (∀ n (p : PlanePoint),
        p ∈ ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint) →
        ∃ verticalSide horizontalSide :
            FiniteJunctionRepair.SpliceGraphOccupiedSide,
          ∀ᶠ q in 𝓝 p,
            q ∈ interior (W n) ↔
              CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  verticalSide
                  (FiniteJunctionRepair.cutNormalCoordinate
                    .vertical p q) ∧
                CMVBoundaryLocalAtlas.SmoothGraphAtlas.signedCoordinateOccupied
                  horizontalSide
                  (FiniteJunctionRepair.cutNormalCoordinate
                    .horizontal p q)) ∧
      ∀ n, HasFiniteBoundaryClosedWalkPaths lam (cropped n) := by
  unfold HasOpenRectangularLocalization at h
  rcases h with
    ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto, hcost,
      _hfinite, hl, hr, hd, hu, hL, hRcut, hD, hU, _hcorner,
      hpiecewise, hfullAtlas, _hfiniteTopology, hquantitative⟩
  dsimp only at hquantitative
  rcases hquantitative with
    ⟨_htarget, _hopen, hbounded, _hcrop, _hcutFinite, _hcropFinite,
      hcutTendsto, hcropConv, hcostBound⟩
  refine ⟨B, R, l, r, d, u, hR, hEcore, hconv, hreindex, htendsto,
    hcost, ?_⟩
  dsimp only
  refine ⟨hcutTendsto, hcropConv, hcostBound, ?_, ?_, ?_⟩
  · intro n p hpJ hpCorner
    exact exists_occupiedLeftTransverseEndpointTraces_of_noncornerJunction
      (B.smooth n).isOpen (by linarith) (by linarith)
      (hl n) (hr n) (hd n) (hu n)
      (hL n) (hRcut n) (hD n) (hU n) hpJ hpCorner
  · intro n p hp
    exact
      FiniteJunctionRepair.exists_occupiedCutSides_at_closedCutRectangle_corner
        (by linarith [(hl n).2, (hr n).1])
        (by linarith [(hd n).2, (hu n).1]) hp
  · intro n
    unfold HasFiniteBoundaryClosedWalkPaths
    obtain ⟨atlas⟩ := hfullAtlas n
    let T := finitePiecewiseRegularBoundaryTopologyOfAtlas atlas
      (hbounded n) (hpiecewise n)
    exact ⟨T, T.chartCuts.smoothCost_eq_sum_boundaryGeometricWalkLoops lam,
      T.exists_regularTrace_away_exceptionalPoints,
      T.hasGloballyOrientedOpenArcs,
      T.chartCuts.finiteArcPathLR_nonduplicating_cover,
      T.chartCuts.traversedArc_injOn,
      T.chartCuts.hasEmbeddedBoundaryArcCycles,
      T.chartCuts.disjoint_walkCycle_crossHalfEdge,
      T.chartCuts.boundaryLoopIndexOfHalfEdge_surjective,
      T.chartCuts.boundaryLoopIndexOfHalfEdge_eq_iff,
      T.chartCuts.isEmpty_boundaryLoopIndex_of_frontier_eq_empty,
      T.chartCuts.boundaryGeometricWalkLoop_path_range_eq_iUnion_arcs,
      fun j e he =>
        T.chartCuts.existsUnique_lt_minimalPeriod_traversedArc_eq
          (T.chartCuts.boundaryLoopHalfEdge j) e
          (he.trans
            (T.chartCuts.boundaryLoopIndexOfHalfEdge_boundaryLoopHalfEdge j).symm),
      T.chartCuts.weightedTraceCost_boundaryGeometricWalkLoop_eq_sum_arcs lam,
      fun j => ⟨T.chartCuts.isCompact_range_boundaryGeometricWalkLoop j,
        T.chartCuts.measurableSet_range_boundaryGeometricWalkLoop j⟩,
      T.chartCuts.disjoint_range_boundaryGeometricWalkLoop,
      T.chartCuts.iUnion_boundaryGeometricWalkLoop_path_range_eq_frontier⟩

end CMVRelaxation
