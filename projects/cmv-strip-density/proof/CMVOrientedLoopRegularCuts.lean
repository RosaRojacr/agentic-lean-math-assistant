import CMVLocalGraphSurgery

/-!
# Regular finite rectangular cuts for oriented-loop localization

The four cut coordinates below are selected from the actual local defining
functions of two smooth domains.  Regularity, finite frontier crossings, corner
avoidance, and the vanishing complete cut cost are conclusions rather than
inputs to later loop extraction.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology symmDiff

noncomputable section

namespace CMVRelaxation

/-- Two sequences of literal smooth domains with vanishing mismatch in four
fixed collars have simultaneous rectangular cuts that are transverse to both
frontiers, have finitely many crossings on every face, avoid all four corners,
and whose complete artificial trace has vanishing weighted cost. -/
theorem exists_regularFinite_closedCutRectangle_spliceCutTrace_tendsto_zero
    {lam : ℝ} (hlam : 1 < lam) (U G : ℕ → Set PlanePoint)
    (hU : ∀ n, IsSmoothDomain (U n)) (hG : ∀ n, IsSmoothDomain (G n))
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU : ∀ n,
      FrontierMeasure (U n) (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : ∀ n,
      FrontierMeasure (G n) (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hleft : Tendsto (fun n =>
      volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0))
    (hright : Tendsto (fun n =>
      volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0))
    (hlower : Tendsto (fun n =>
      volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0))
    (hupper : Tendsto (fun n =>
      volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0)) :
    ∃ l r d u : ℕ → ℝ,
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (U n) (G n)
        (closedCutRectangle a₀ a₁ c₀ d₁) (l n)) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (U n) (G n)
        (closedCutRectangle b₀ b₁ c₀ d₁) (r n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (U n) (G n)
        (closedCutRectangle a₀ b₁ c₀ c₁) (d n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (U n) (G n)
        (closedCutRectangle a₀ b₁ d₀ d₁) (u n)) ∧
      (∀ n, ∀ p ∈
        ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
          Set PlanePoint),
        p ∉ frontier (U n) ∧ p ∉ frontier (G n)) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (spliceCutTrace (U n) (G n)
            (closedCutRectangle (l n) (r n) (d n) (u n))))
        atTop (𝓝 0) := by
  have hselect : ∀ n,
      ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
        ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
          IsRegularFiniteVerticalSpliceCut (U n) (G n)
              (closedCutRectangle a₀ a₁ c₀ d₁) l ∧
          IsRegularFiniteVerticalSpliceCut (U n) (G n)
              (closedCutRectangle b₀ b₁ c₀ d₁) r ∧
          IsRegularFiniteHorizontalSpliceCut (U n) (G n)
              (closedCutRectangle a₀ b₁ c₀ c₁) d ∧
          IsRegularFiniteHorizontalSpliceCut (U n) (G n)
              (closedCutRectangle a₀ b₁ d₀ d₁) u ∧
          (∀ p ∈ ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint),
            p ∉ frontier (U n) ∧ p ∉ frontier (G n)) ∧
          weightedTraceCost lam
              (spliceCutTrace (U n) (G n)
                (closedCutRectangle l r d u)) ≤
            ENNReal.ofReal lam *
                (volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U n ∆ G n)) /
                  ENNReal.ofReal (a₁ - a₀)) +
              ENNReal.ofReal lam *
                (volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U n ∆ G n)) /
                  ENNReal.ofReal (b₁ - b₀)) +
                ENNReal.ofReal lam *
                  (volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U n ∆ G n)) /
                    ENNReal.ofReal (c₁ - c₀)) +
                  ENNReal.ofReal lam *
                    (volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U n ∆ G n)) /
                      ENNReal.ofReal (d₁ - d₀)) := by
    intro n
    have hregUL := (hU n).volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle a₀ a₁ c₀ d₁)
    have hregGL := (hG n).volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle a₀ a₁ c₀ d₁)
    have hregUR := (hU n).volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle b₀ b₁ c₀ d₁)
    have hregGR := (hG n).volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle b₀ b₁ c₀ d₁)
    have hregUD := (hU n).volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle a₀ b₁ c₀ c₁)
    have hregGD := (hG n).volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle a₀ b₁ c₀ c₁)
    have hregUU := (hU n).volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle a₀ b₁ d₀ d₁)
    have hregGU := (hG n).volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
      (isCompact_closedCutRectangle a₀ b₁ d₀ d₁)
    rcases exists_closedCutRectangle_regular_finite_spliceCutTrace_le_collar_averages
        hlam (U n) (G n) (hU n).isOpen.measurableSet
        (hG n).isOpen.measurableSet ha hab hb hc hcd hd
        (hfiniteU n) (hfiniteG n)
        hregUL hregGL hregUR hregGR hregUD hregGD hregUU hregGU with
      ⟨l, hl, r, hr, d, hdmem, u, humem,
        hlregU, hlregG, hrregU, hrregG, hdregU, hdregG, huregU, huregG,
        hlzeroU, hlzeroG, hrzeroU, hrzeroG,
        hdzeroU, hdzeroG, huzeroU, huzeroG,
        hlfiniteU, hlfiniteG, hrfiniteU, hrfiniteG,
        hdfiniteU, hdfiniteG, hufiniteU, hufiniteG,
        hcorner, hcost⟩
    exact ⟨l, hl, r, hr, d, hdmem, u, humem,
      ⟨hlregU, hlregG, hlzeroU, hlzeroG, hlfiniteU, hlfiniteG⟩,
      ⟨hrregU, hrregG, hrzeroU, hrzeroG, hrfiniteU, hrfiniteG⟩,
      ⟨hdregU, hdregG, hdzeroU, hdzeroG, hdfiniteU, hdfiniteG⟩,
      ⟨huregU, huregG, huzeroU, huzeroG, hufiniteU, hufiniteG⟩,
      hcorner, hcost⟩
  choose l hl r hr d hdmem u humem hregL hregR hregD hregU hcorner hcost
    using hselect
  refine ⟨l, r, d, u, hl, hr, hdmem, humem,
    hregL, hregR, hregD, hregU, hcorner, ?_⟩
  have tendsto_div : ∀ {f : ℕ → ENNReal} {w : ℝ},
      0 < w → Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => f n / ENNReal.ofReal w) atTop (𝓝 0) := by
    intro f w hw hf
    rw [show (fun n => f n / ENNReal.ofReal w) =
      fun n => (ENNReal.ofReal w)⁻¹ * f n by
        funext n
        rw [ENNReal.div_eq_inv_mul]]
    simpa using ENNReal.Tendsto.const_mul hf
      (Or.inr (ENNReal.inv_ne_top.2
        (ne_of_gt (ENNReal.ofReal_pos.2 hw))))
  have tendsto_scaled : ∀ {f : ℕ → ENNReal} {w : ℝ},
      0 < w → Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => ENNReal.ofReal lam *
        (f n / ENNReal.ofReal w)) atTop (𝓝 0) := by
    intro f w hw hf
    simpa using ENNReal.Tendsto.const_mul (tendsto_div hw hf)
      (Or.inr ENNReal.ofReal_ne_top)
  have hleft' := tendsto_scaled (sub_pos.mpr ha) hleft
  have hright' := tendsto_scaled (sub_pos.mpr hb) hright
  have hlower' := tendsto_scaled (sub_pos.mpr hc) hlower
  have hupper' := tendsto_scaled (sub_pos.mpr hd) hupper
  have hbudget : Tendsto (fun n =>
      ENNReal.ofReal lam *
          (volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U n ∆ G n)) /
            ENNReal.ofReal (a₁ - a₀)) +
        ENNReal.ofReal lam *
          (volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U n ∆ G n)) /
            ENNReal.ofReal (b₁ - b₀)) +
          ENNReal.ofReal lam *
            (volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U n ∆ G n)) /
              ENNReal.ofReal (c₁ - c₀)) +
            ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U n ∆ G n)) /
                ENNReal.ofReal (d₁ - d₀))) atTop (𝓝 0) := by
    simpa using ((hleft'.add hright').add hlower').add hupper'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbudget (fun _ => bot_le) hcost

end CMVRelaxation
