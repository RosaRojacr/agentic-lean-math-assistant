/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryOrderedChains

/-!
# Planar topology and completeness of intrinsic boundary orders

One-sided endpoint-limit compatibility closes every principal order ray in the
planar subtype topology.  Compact-to-Hausdorff uniqueness then identifies that
topology with the height-first order topology, and compact extrema of closures
supply all suprema and infima.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

open CMVRelaxation
open CMVSourceClassification

variable {E U : Set PlanePoint}

/-- If `f` converges from below at `a`, its right-limit function has the same
limit when approaching `a` from below. -/
theorem tendsto_rightLim_nhdsLT_of_tendsto
    {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace β] [T3Space β] {f : α → β} {a : α}
    (h : Tendsto f (𝓝[<] a) (𝓝 (Function.leftLim f a))) :
    Tendsto (Function.rightLim f) (𝓝[<] a)
      (𝓝 (Function.leftLim f a)) := by
  apply (closed_nhds_basis (Function.leftLim f a)).tendsto_right_iff.2
  rintro s ⟨s_mem, s_closed⟩
  rcases eq_or_neBot (𝓝[<] a) with hbot | hne
  · simp [hbot]
  obtain ⟨b, hb⟩ : (Iio a).Nonempty :=
    Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a))
  obtain ⟨u, au, hu⟩ : ∃ u, u < a ∧ Ioo u a ⊆ {x | f x ∈ s} := by
    have hs := (closed_nhds_basis (Function.leftLim f a)).tendsto_right_iff.1 h
      s ⟨s_mem, s_closed⟩
    simpa using (mem_nhdsLT_iff_exists_Ioo_subset' hb).1 hs
  filter_upwards [Ioo_mem_nhdsLT au] with c hc
  rcases eq_or_neBot (𝓝[>] c) with h'c | h'c
  · simpa [h'c, rightLim_eq_of_eq_bot] using hu hc
  by_cases! h''c : ¬ ∃ y, Tendsto f (𝓝[>] c) (𝓝 y)
  · simpa [rightLim_eq_of_not_tendsto _ h''c] using hu hc
  apply s_closed.mem_of_tendsto (tendsto_rightLim_of_tendsto h''c)
  filter_upwards [Ioo_mem_nhdsGT_of_mem ⟨hc.1.le, hc.2⟩] with d hd using hu hd

/-- If `f` converges from above at `a`, its left-limit function has the same
limit when approaching `a` from above. -/
theorem tendsto_leftLim_nhdsGT_of_tendsto
    {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace β] [T3Space β] {f : α → β} {a : α}
    (h : Tendsto f (𝓝[>] a) (𝓝 (Function.rightLim f a))) :
    Tendsto (Function.leftLim f) (𝓝[>] a)
      (𝓝 (Function.rightLim f a)) :=
  tendsto_rightLim_nhdsLT_of_tendsto (α := αᵒᵈ) h

/-- A convergent sequence in the left completed chain which stays strictly
below its limit height lands at the lower-side endpoint limit. -/
theorem leftCompletedChain_limit_from_below
    (D : SelectedBoundaryTopologyInput E U)
    (p : ℕ → D.leftCompletedChain) (q : D.leftCompletedChain)
    (hpq : Tendsto p atTop (𝓝 q))
    (hbelow : ∀ n, (p n).1.2 < q.1.2) :
    q.1.1 = Function.leftLim D.leftEndpoint q.1.2 := by
  have hpqVal : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpq
  have hqBounds := D.leftCompletedChain_snd_mem_Icc q
  have hqLower : D.lowerHeight < q.1.2 := by
    have hpLower := (D.leftCompletedChain_snd_mem_Icc (p 0)).1
    linarith [hbelow 0]
  have hpAboveLower : ∀ᶠ n in atTop, D.lowerHeight < (p n).1.2 :=
    hpqVal.snd_nhds (Ioi_mem_nhds hqLower)
  have hpOccupied : ∀ᶠ n in atTop, (p n).1.2 ∈ D.occupiedHeights := by
    filter_upwards [hpAboveLower] with n hn
    exact D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hn, (hbelow n).trans_le hqBounds.2⟩
  have hyWithin : Tendsto (fun n => (p n).1.2) atTop (𝓝[Iic q.1.2] q.1.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpqVal.snd_nhds,
      Filter.Eventually.of_forall fun n => (hbelow n).le⟩
  have hbase : Tendsto D.leftEndpoint (𝓝[<] q.1.2)
      (𝓝 (Function.leftLim D.leftEndpoint q.1.2)) := by
    rcases hqBounds.2.eq_or_lt with hqUpper | hqUpper
    · simpa only [hqUpper] using
        D.tendsto_leftEndpoint_nhdsLT_upperHeight_leftLim
    · exact D.tendsto_leftEndpoint_nhdsLT_leftLim
        (D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hqLower, hqUpper⟩)
  have hleft : Tendsto
      (fun n => Function.leftLim D.leftEndpoint (p n).1.2) atTop
      (𝓝 (Function.leftLim D.leftEndpoint q.1.2)) := by
    exact (continuousWithinAt_leftLim_Iic hbase).tendsto.comp hyWithin
  have hright : Tendsto
      (fun n => Function.rightLim D.leftEndpoint (p n).1.2) atTop
      (𝓝 (Function.leftLim D.leftEndpoint q.1.2)) := by
    have hcross := tendsto_rightLim_nhdsLT_of_tendsto hbase
    exact hcross.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hpqVal.snd_nhds,
        Filter.Eventually.of_forall hbelow⟩)
  have hxBounds : ∀ᶠ n in atTop,
      min (Function.leftLim D.leftEndpoint (p n).1.2)
          (Function.rightLim D.leftEndpoint (p n).1.2) ≤ (p n).1.1 ∧
      (p n).1.1 ≤ max (Function.leftLim D.leftEndpoint (p n).1.2)
          (Function.rightLim D.leftEndpoint (p n).1.2) := by
    filter_upwards [hpOccupied] with n hn
    exact (D.leftCompletedChain_mem_interior_iff hn).mp (p n).property
  have hmin : Tendsto
      (fun n => min (Function.leftLim D.leftEndpoint (p n).1.2)
        (Function.rightLim D.leftEndpoint (p n).1.2)) atTop
      (𝓝 (Function.leftLim D.leftEndpoint q.1.2)) := by
    simpa using hleft.min hright
  have hmax : Tendsto
      (fun n => max (Function.leftLim D.leftEndpoint (p n).1.2)
        (Function.rightLim D.leftEndpoint (p n).1.2)) atTop
      (𝓝 (Function.leftLim D.leftEndpoint q.1.2)) := by
    simpa using hleft.max hright
  have hx : Tendsto (fun n => (p n).1.1) atTop
      (𝓝 (Function.leftLim D.leftEndpoint q.1.2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax
      (hxBounds.mono fun _ hn => hn.1) (hxBounds.mono fun _ hn => hn.2)
  exact tendsto_nhds_unique hpqVal.fst_nhds hx

/-- A convergent sequence in the left completed chain which stays strictly
above its limit height lands at the upper-side endpoint limit. -/
theorem leftCompletedChain_limit_from_above
    (D : SelectedBoundaryTopologyInput E U)
    (p : ℕ → D.leftCompletedChain) (q : D.leftCompletedChain)
    (hpq : Tendsto p atTop (𝓝 q))
    (habove : ∀ n, q.1.2 < (p n).1.2) :
    q.1.1 = Function.rightLim D.leftEndpoint q.1.2 := by
  have hpqVal : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpq
  have hqBounds := D.leftCompletedChain_snd_mem_Icc q
  have hqUpper : q.1.2 < D.upperHeight := by
    have hpUpper := (D.leftCompletedChain_snd_mem_Icc (p 0)).2
    linarith [habove 0]
  have hpBelowUpper : ∀ᶠ n in atTop, (p n).1.2 < D.upperHeight :=
    hpqVal.snd_nhds (Iio_mem_nhds hqUpper)
  have hpOccupied : ∀ᶠ n in atTop, (p n).1.2 ∈ D.occupiedHeights := by
    filter_upwards [hpBelowUpper] with n hn
    exact D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hqBounds.1.trans_lt (habove n), hn⟩
  have hyWithin : Tendsto (fun n => (p n).1.2) atTop (𝓝[Ici q.1.2] q.1.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpqVal.snd_nhds,
      Filter.Eventually.of_forall fun n => (habove n).le⟩
  have hbase : Tendsto D.leftEndpoint (𝓝[>] q.1.2)
      (𝓝 (Function.rightLim D.leftEndpoint q.1.2)) := by
    rcases hqBounds.1.eq_or_lt with hqLower | hqLower
    · simpa only [← hqLower] using
        D.tendsto_leftEndpoint_nhdsGT_lowerHeight_rightLim
    · exact D.tendsto_leftEndpoint_nhdsGT_rightLim
        (D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hqLower, hqUpper⟩)
  have hleft : Tendsto
      (fun n => Function.leftLim D.leftEndpoint (p n).1.2) atTop
      (𝓝 (Function.rightLim D.leftEndpoint q.1.2)) := by
    have hcross := tendsto_leftLim_nhdsGT_of_tendsto hbase
    exact hcross.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hpqVal.snd_nhds,
        Filter.Eventually.of_forall habove⟩)
  have hright : Tendsto
      (fun n => Function.rightLim D.leftEndpoint (p n).1.2) atTop
      (𝓝 (Function.rightLim D.leftEndpoint q.1.2)) := by
    exact (continuousWithinAt_rightLim_Ici hbase).tendsto.comp hyWithin
  have hxBounds : ∀ᶠ n in atTop,
      min (Function.leftLim D.leftEndpoint (p n).1.2)
          (Function.rightLim D.leftEndpoint (p n).1.2) ≤ (p n).1.1 ∧
      (p n).1.1 ≤ max (Function.leftLim D.leftEndpoint (p n).1.2)
          (Function.rightLim D.leftEndpoint (p n).1.2) := by
    filter_upwards [hpOccupied] with n hn
    exact (D.leftCompletedChain_mem_interior_iff hn).mp (p n).property
  have hmin : Tendsto
      (fun n => min (Function.leftLim D.leftEndpoint (p n).1.2)
        (Function.rightLim D.leftEndpoint (p n).1.2)) atTop
      (𝓝 (Function.rightLim D.leftEndpoint q.1.2)) := by
    simpa using hleft.min hright
  have hmax : Tendsto
      (fun n => max (Function.leftLim D.leftEndpoint (p n).1.2)
        (Function.rightLim D.leftEndpoint (p n).1.2)) atTop
      (𝓝 (Function.rightLim D.leftEndpoint q.1.2)) := by
    simpa using hleft.max hright
  have hx : Tendsto (fun n => (p n).1.1) atTop
      (𝓝 (Function.rightLim D.leftEndpoint q.1.2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax
      (hxBounds.mono fun _ hn => hn.1) (hxBounds.mono fun _ hn => hn.2)
  exact tendsto_nhds_unique hpqVal.fst_nhds hx

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas


open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

open CMVRelaxation
open CMVSourceClassification

variable {E U : Set PlanePoint}

private theorem leftLim_secondary_le
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain) (hy : p.1.2 = q.1.2)
    (hqlower : D.lowerHeight < q.1.2)
    (hq : q.1.1 = Function.leftLim D.leftEndpoint q.1.2) :
    D.leftOrderSecondary q.1 ≤ D.leftOrderSecondary p.1 := by
  rcases p.property with hp | hp | hp
  · have : q.1.2 = D.lowerHeight := hy ▸ hp.1
    exact (hqlower.ne' this).elim
  · have hb := D.mem_occupiedHeights_iff_height_bounds.mp hp.1
    have hpseg := (D.leftCompletedChain_mem_interior_iff hp.1).mp p.property
    have hql : q.1.2 ≠ D.lowerHeight := by rw [← hy]; exact hb.1.ne'
    have hqu : q.1.2 ≠ D.upperHeight := by rw [← hy]; exact hb.2.ne
    rw [leftOrderSecondary, leftOrderSecondary, hy, hq]
    simp only [hql, hqu, if_false]
    rw [hy] at hpseg
    by_cases hdir : Function.leftLim D.leftEndpoint q.1.2 ≤
        Function.rightLim D.leftEndpoint q.1.2
    · simp only [hdir, if_true]
      simpa only [min_eq_left hdir] using hpseg.1
    · simp only [hdir, if_false]
      simpa only [max_eq_left (le_of_not_ge hdir)] using
        (neg_le_neg hpseg.2)
  · have hqy : q.1.2 = D.upperHeight := hy ▸ hp.1
    rw [leftOrderSecondary, leftOrderSecondary, hp.1, hqy]
    simp only [D.lowerHeight_lt_upperHeight.ne', if_false, if_true]
    rw [hq, hqy]
    simpa only [upperLeft] using hp.2.1

private theorem secondary_le_rightLim
    (D : SelectedBoundaryTopologyInput E U)
    (p q : D.leftCompletedChain) (hy : p.1.2 = q.1.2)
    (hqupper : q.1.2 < D.upperHeight)
    (hq : q.1.1 = Function.rightLim D.leftEndpoint q.1.2) :
    D.leftOrderSecondary p.1 ≤ D.leftOrderSecondary q.1 := by
  rcases p.property with hp | hp | hp
  · have hqy : q.1.2 = D.lowerHeight := hy ▸ hp.1
    rw [leftOrderSecondary, leftOrderSecondary, hp.1, hqy]
    simp only [if_true, neg_le_neg_iff]
    rw [hq, hqy]
    simpa only [lowerLeft] using hp.2.1
  · have hb := D.mem_occupiedHeights_iff_height_bounds.mp hp.1
    have hpseg := (D.leftCompletedChain_mem_interior_iff hp.1).mp p.property
    have hql : q.1.2 ≠ D.lowerHeight := by rw [← hy]; exact hb.1.ne'
    have hqu : q.1.2 ≠ D.upperHeight := by rw [← hy]; exact hb.2.ne
    rw [leftOrderSecondary, leftOrderSecondary, hy, hq]
    simp only [hql, hqu, if_false]
    rw [hy] at hpseg
    by_cases hdir : Function.leftLim D.leftEndpoint q.1.2 ≤
        Function.rightLim D.leftEndpoint q.1.2
    · simp only [hdir, if_true]
      simpa only [max_eq_right hdir] using hpseg.2
    · simp only [hdir, if_false, neg_le_neg_iff]
      simpa only [min_eq_right (le_of_not_ge hdir)] using hpseg.1
  · have : q.1.2 = D.upperHeight := hy ▸ hp.1
    exact (hqupper.ne this).elim

private theorem tendsto_leftSecondary_of_eventually_same_height
    (D : SelectedBoundaryTopologyInput E U)
    (p : ℕ → D.leftCompletedChain) (q : D.leftCompletedChain)
    (hpq : Tendsto p atTop (𝓝 q))
    (hy : ∀ᶠ n in atTop, (p n).1.2 = q.1.2) :
    Tendsto (fun n => D.leftOrderSecondary (p n).1) atTop
      (𝓝 (D.leftOrderSecondary q.1)) := by
  have hx : Tendsto (fun n => (p n).1.1) atTop (𝓝 q.1.1) :=
    (continuous_subtype_val.continuousAt.tendsto.comp hpq).fst_nhds
  by_cases hlower : q.1.2 = D.lowerHeight
  · rw [show D.leftOrderSecondary q.1 = -q.1.1 by
      simp [leftOrderSecondary, hlower]]
    apply hx.neg.congr'
    filter_upwards [hy] with n hn
    simp [leftOrderSecondary, hn, hlower]
  · by_cases hupper : q.1.2 = D.upperHeight
    · rw [show D.leftOrderSecondary q.1 = q.1.1 by
        simp [leftOrderSecondary, hupper,
          D.lowerHeight_lt_upperHeight.ne']]
      apply hx.congr'
      filter_upwards [hy] with n hn
      simp [leftOrderSecondary, hn, hupper,
        D.lowerHeight_lt_upperHeight.ne']
    · by_cases hdir : Function.leftLim D.leftEndpoint q.1.2 ≤
          Function.rightLim D.leftEndpoint q.1.2
      · rw [show D.leftOrderSecondary q.1 = q.1.1 by
          simp [leftOrderSecondary, hlower, hupper, hdir]]
        apply hx.congr'
        filter_upwards [hy] with n hn
        simp [leftOrderSecondary, hn, hlower, hupper, hdir]
      · rw [show D.leftOrderSecondary q.1 = -q.1.1 by
          simp [leftOrderSecondary, hlower, hupper, hdir]]
        apply hx.neg.congr'
        filter_upwards [hy] with n hn
        simp [leftOrderSecondary, hn, hlower, hupper, hdir]

theorem isClosed_leftCompletedChain_Iic
    (D : SelectedBoundaryTopologyInput E U) (a : D.leftCompletedChain) :
    IsClosed {p : D.leftCompletedChain |
      @LE.le _ D.leftCompletedChainLinearOrder.toLE p a} := by
  apply IsSeqClosed.isClosed
  intro p q hp hpq
  have hpqVal : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpq
  have hyLe : ∀ n, (p n).1.2 ≤ a.1.2 := by
    intro n
    have hpn := hp n
    change @LE.le _ D.leftCompletedChainLinearOrder.toLE (p n) a at hpn
    rcases (D.leftCompletedChain_le_iff (p n) a).mp hpn with h | h
    · exact h.le
    · exact h.1.le
  have hqLe : q.1.2 ≤ a.1.2 :=
    le_of_tendsto hpqVal.snd_nhds (Filter.Eventually.of_forall hyLe)
  apply (D.leftCompletedChain_le_iff q a).mpr
  rcases hqLe.eq_or_lt with hqa | hqa
  · right
    refine ⟨hqa, ?_⟩
    by_cases heq : ∀ᶠ n in atTop, (p n).1.2 = q.1.2
    · have hsec := tendsto_leftSecondary_of_eventually_same_height D p q hpq heq
      apply le_of_tendsto hsec
      filter_upwards [heq] with n hn
      have hpn := hp n
      change @LE.le _ D.leftCompletedChainLinearOrder.toLE (p n) a at hpn
      rcases (D.leftCompletedChain_le_iff (p n) a).mp hpn with h | h
      · linarith
      · exact h.2
    · obtain ⟨φ, hφmono, hφ⟩ :=
        extraction_of_frequently_atTop (Filter.not_eventually.mp heq)
      have hbelow : ∀ n, (p (φ n)).1.2 < q.1.2 := by
        intro n
        exact lt_of_le_of_ne (hqa ▸ hyLe (φ n)) (hφ n)
      have hpin := D.leftCompletedChain_limit_from_below (p ∘ φ) q
        (hpq.comp hφmono.tendsto_atTop) hbelow
      have hqlower : D.lowerHeight < q.1.2 :=
        (D.leftCompletedChain_snd_mem_Icc (p (φ 0))).1.trans_lt (hbelow 0)
      exact leftLim_secondary_le D a q hqa.symm hqlower hpin
  · exact Or.inl hqa

theorem isClosed_leftCompletedChain_Ici
    (D : SelectedBoundaryTopologyInput E U) (a : D.leftCompletedChain) :
    IsClosed {p : D.leftCompletedChain |
      @LE.le _ D.leftCompletedChainLinearOrder.toLE a p} := by
  apply IsSeqClosed.isClosed
  intro p q hp hpq
  have hpqVal : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpq
  have hyGe : ∀ n, a.1.2 ≤ (p n).1.2 := by
    intro n
    have hpn := hp n
    change @LE.le _ D.leftCompletedChainLinearOrder.toLE a (p n) at hpn
    rcases (D.leftCompletedChain_le_iff a (p n)).mp hpn with h | h
    · exact h.le
    · exact h.1.le
  have hqGe : a.1.2 ≤ q.1.2 := by
    have hneg := le_of_tendsto hpqVal.snd_nhds.neg
      (Filter.Eventually.of_forall fun n => neg_le_neg (hyGe n))
    linarith
  apply (D.leftCompletedChain_le_iff a q).mpr
  rcases hqGe.eq_or_lt with haq | haq
  · right
    refine ⟨haq, ?_⟩
    by_cases heq : ∀ᶠ n in atTop, (p n).1.2 = q.1.2
    · have hsec := tendsto_leftSecondary_of_eventually_same_height D p q hpq heq
      have hle : D.leftOrderSecondary a.1 ≤ D.leftOrderSecondary q.1 := by
        have := le_of_tendsto hsec.neg
          (heq.mono fun n hn => by
            have hpn := hp n
            change @LE.le _ D.leftCompletedChainLinearOrder.toLE a (p n) at hpn
            rcases (D.leftCompletedChain_le_iff a (p n)).mp hpn with h | h
            · have : a.1.2 = (p n).1.2 := haq.trans hn.symm
              exact (h.ne this).elim
            · exact neg_le_neg h.2)
        simpa only [neg_neg] using neg_le_neg this
      exact hle
    · obtain ⟨φ, hφmono, hφ⟩ :=
        extraction_of_frequently_atTop (Filter.not_eventually.mp heq)
      have habove : ∀ n, q.1.2 < (p (φ n)).1.2 := by
        intro n
        exact lt_of_le_of_ne (haq ▸ hyGe (φ n)) (Ne.symm (hφ n))
      have hpin := D.leftCompletedChain_limit_from_above (p ∘ φ) q
        (hpq.comp hφmono.tendsto_atTop) habove
      have hqupper : q.1.2 < D.upperHeight :=
        (habove 0).trans_le (D.leftCompletedChain_snd_mem_Icc (p (φ 0))).2
      exact secondary_le_rightLim D a q haq hqupper hpin
  · exact Or.inl haq

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

open CMVRelaxation CMVSourceClassification

variable {E U : Set PlanePoint}

theorem rightCompletedChain_limit_from_below
    (D : SelectedBoundaryTopologyInput E U)
    {p : ℕ → D.rightCompletedChain} {q : D.rightCompletedChain}
    (hpq : Tendsto p atTop (𝓝 q))
    (hbelow : ∀ n, (p n).1.2 < q.1.2) :
    q.1.1 = Function.leftLim D.rightEndpoint q.1.2 := by
  have hpqval : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpq
  have hpBounds := D.rightCompletedChain_snd_mem_Icc (p 0)
  have hqBounds := D.rightCompletedChain_snd_mem_Icc q
  have hqLower : D.lowerHeight < q.1.2 := hpBounds.1.trans_lt (hbelow 0)
  have hlimit : Tendsto D.rightEndpoint (𝓝[<] q.1.2)
      (𝓝 (Function.leftLim D.rightEndpoint q.1.2)) := by
    rcases hqBounds.2.eq_or_lt with hupper | hupper
    · rw [hupper]
      exact D.tendsto_rightEndpoint_nhdsLT_upperHeight_leftLim
    · exact D.tendsto_rightEndpoint_nhdsLT_leftLim
        (D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hqLower, hupper⟩)
  have hy : Tendsto (fun n => (p n).1.2) atTop (𝓝 q.1.2) :=
    hpqval.snd_nhds
  have hyLT : Tendsto (fun n => (p n).1.2) atTop (𝓝[<] q.1.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy, Filter.Eventually.of_forall hbelow⟩
  have hyIic : Tendsto (fun n => (p n).1.2) atTop (𝓝[Iic q.1.2] q.1.2) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hy, Filter.Eventually.of_forall fun n => (hbelow n).le⟩
  have hleft : Tendsto
      (fun n => Function.leftLim D.rightEndpoint (p n).1.2) atTop
      (𝓝 (Function.leftLim D.rightEndpoint q.1.2)) :=
    Filter.Tendsto.comp (continuousWithinAt_leftLim_Iic hlimit) hyIic
  have hright : Tendsto
      (fun n => Function.rightLim D.rightEndpoint (p n).1.2) atTop
      (𝓝 (Function.leftLim D.rightEndpoint q.1.2)) :=
    (tendsto_rightLim_nhdsLT_of_tendsto hlimit).comp hyLT
  have hoccupied : ∀ᶠ n in atTop, (p n).1.2 ∈ D.occupiedHeights := by
    have hlower : ∀ᶠ n in atTop, D.lowerHeight < (p n).1.2 :=
      hy (Ioi_mem_nhds hqLower)
    filter_upwards [hlower] with n hn
    exact D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hn, (hbelow n).trans_le hqBounds.2⟩
  have hfiber : ∀ᶠ n in atTop,
      (p n).1.1 ∈ uIcc (Function.leftLim D.rightEndpoint (p n).1.2)
        (Function.rightLim D.rightEndpoint (p n).1.2) := by
    filter_upwards [hoccupied] with n hn
    exact (D.rightCompletedChain_mem_interior_iff hn).mp (p n).property
  have hmin := hleft.min hright
  have hmax := hleft.max hright
  simp only [min_self] at hmin
  simp only [max_self] at hmax
  have hx : Tendsto (fun n => (p n).1.1) atTop
      (𝓝 (Function.leftLim D.rightEndpoint q.1.2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax
    · exact hfiber.mono fun _ hn => by
        rcases mem_uIcc.mp hn with hn | hn
        · exact (min_le_left _ _).trans hn.1
        · exact (min_le_right _ _).trans hn.1
    · exact hfiber.mono fun _ hn => by
        rcases mem_uIcc.mp hn with hn | hn
        · exact hn.2.trans (le_max_right _ _)
        · exact hn.2.trans (le_max_left _ _)
  exact tendsto_nhds_unique hpqval.fst_nhds hx


theorem rightCompletedChain_limit_from_above
    (D : SelectedBoundaryTopologyInput E U)
    {p : ℕ → D.rightCompletedChain} {q : D.rightCompletedChain}
    (hpq : Tendsto p atTop (𝓝 q))
    (habove : ∀ n, q.1.2 < (p n).1.2) :
    q.1.1 = Function.rightLim D.rightEndpoint q.1.2 := by
  have hpqval : Tendsto (fun n => (p n).1) atTop (𝓝 q.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpq
  have hpBounds := D.rightCompletedChain_snd_mem_Icc (p 0)
  have hqBounds := D.rightCompletedChain_snd_mem_Icc q
  have hqUpper : q.1.2 < D.upperHeight :=
    (habove 0).trans_le hpBounds.2
  have hlimit : Tendsto D.rightEndpoint (𝓝[>] q.1.2)
      (𝓝 (Function.rightLim D.rightEndpoint q.1.2)) := by
    rcases hqBounds.1.eq_or_lt with hlower | hlower
    · rw [← hlower]
      exact D.tendsto_rightEndpoint_nhdsGT_lowerHeight_rightLim
    · exact D.tendsto_rightEndpoint_nhdsGT_rightLim
        (D.mem_occupiedHeights_iff_height_bounds.mpr ⟨hlower, hqUpper⟩)
  have hy : Tendsto (fun n => (p n).1.2) atTop (𝓝 q.1.2) :=
    hpqval.snd_nhds
  have hyGT : Tendsto (fun n => (p n).1.2) atTop (𝓝[>] q.1.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy, Filter.Eventually.of_forall habove⟩
  have hyIci : Tendsto (fun n => (p n).1.2) atTop (𝓝[Ici q.1.2] q.1.2) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hy, Filter.Eventually.of_forall fun n => (habove n).le⟩
  have hleft : Tendsto
      (fun n => Function.leftLim D.rightEndpoint (p n).1.2) atTop
      (𝓝 (Function.rightLim D.rightEndpoint q.1.2)) :=
    (tendsto_leftLim_nhdsGT_of_tendsto hlimit).comp hyGT
  have hright : Tendsto
      (fun n => Function.rightLim D.rightEndpoint (p n).1.2) atTop
      (𝓝 (Function.rightLim D.rightEndpoint q.1.2)) :=
    Filter.Tendsto.comp (continuousWithinAt_rightLim_Ici hlimit) hyIci
  have hoccupied : ∀ᶠ n in atTop, (p n).1.2 ∈ D.occupiedHeights := by
    have hupper : ∀ᶠ n in atTop, (p n).1.2 < D.upperHeight :=
      hy (Iio_mem_nhds hqUpper)
    filter_upwards [hupper] with n hn
    exact D.mem_occupiedHeights_iff_height_bounds.mpr
      ⟨hqBounds.1.trans_lt (habove n), hn⟩
  have hfiber : ∀ᶠ n in atTop,
      (p n).1.1 ∈ uIcc (Function.leftLim D.rightEndpoint (p n).1.2)
        (Function.rightLim D.rightEndpoint (p n).1.2) := by
    filter_upwards [hoccupied] with n hn
    exact (D.rightCompletedChain_mem_interior_iff hn).mp (p n).property
  have hmin := hleft.min hright
  have hmax := hleft.max hright
  simp only [min_self] at hmin
  simp only [max_self] at hmax
  have hx : Tendsto (fun n => (p n).1.1) atTop
      (𝓝 (Function.rightLim D.rightEndpoint q.1.2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax
    · exact hfiber.mono fun _ hn => by
        rcases mem_uIcc.mp hn with hn | hn
        · exact (min_le_left _ _).trans hn.1
        · exact (min_le_right _ _).trans hn.1
    · exact hfiber.mono fun _ hn => by
        rcases mem_uIcc.mp hn with hn | hn
        · exact hn.2.trans (le_max_right _ _)
        · exact hn.2.trans (le_max_left _ _)
  exact tendsto_nhds_unique hpqval.fst_nhds hx

theorem isClosed_rightCompletedChain_Iic
    (D : SelectedBoundaryTopologyInput E U)
    (q : D.rightCompletedChain) :
    IsClosed {p : D.rightCompletedChain |
      @LE.le _ D.rightCompletedChainLinearOrder.toLE p q} := by
  apply IsSeqClosed.isClosed
  intro p r hp hpr
  have hprVal : Tendsto (fun n => (p n).1) atTop (𝓝 r.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpr
  have hpHeight : ∀ n, (p n).1.2 ≤ q.1.2 := by
    intro n
    rcases (D.rightCompletedChain_le_iff (p n) q).mp (hp n) with h | h
    · exact h.le
    · exact h.1.le
  have hrHeight : r.1.2 ≤ q.1.2 :=
    le_of_tendsto hprVal.snd_nhds
      (Filter.Eventually.of_forall hpHeight)
  rcases hrHeight.eq_or_lt with heq | hlt
  · apply (D.rightCompletedChain_le_iff r q).mpr
    right
    refine ⟨heq, ?_⟩
    by_cases hfreq : ∃ᶠ n in atTop, (p n).1.2 = q.1.2
    · obtain ⟨φ, hφ, hφHeight⟩ := extraction_of_frequently_atTop hfreq
      have hsub : Tendsto (fun n => p (φ n)) atTop (𝓝 r) :=
        hpr.comp hφ.tendsto_atTop
      have hsubVal : Tendsto (fun n => (p (φ n)).1) atTop (𝓝 r.1) :=
        continuous_subtype_val.continuousAt.tendsto.comp hsub
      have hsecLe : ∀ n,
          D.rightOrderSecondary (p (φ n)).1 ≤
            D.rightOrderSecondary q.1 := by
        intro n
        rcases (D.rightCompletedChain_le_iff (p (φ n)) q).mp
            (hp (φ n)) with h | h
        · rw [hφHeight n] at h
          exact (lt_irrefl q.1.2 h).elim
        · exact h.2
      have hsecTend : Tendsto
          (fun n => D.rightOrderSecondary (p (φ n)).1) atTop
          (𝓝 (D.rightOrderSecondary r.1)) := by
        have hx := hsubVal.fst_nhds
        by_cases hlower : q.1.2 = D.lowerHeight
        · simpa only [rightOrderSecondary, hφHeight, heq, hlower, if_pos]
            using hx
        · by_cases hupper : q.1.2 = D.upperHeight
          · simpa only [rightOrderSecondary, hφHeight, heq, hlower, hupper,
              D.lowerHeight_lt_upperHeight.ne', if_pos, if_false] using hx.neg
          · by_cases horiented : Function.leftLim D.rightEndpoint q.1.2 ≤
                Function.rightLim D.rightEndpoint q.1.2
            · simpa only [rightOrderSecondary, hφHeight, heq, hlower, hupper,
                horiented, if_pos, if_false] using hx
            · simpa only [rightOrderSecondary, hφHeight, heq, hlower, hupper,
                horiented, if_pos, if_false] using hx.neg
      exact le_of_tendsto hsecTend
        (Filter.Eventually.of_forall hsecLe)
    · have hne : ∀ᶠ n in atTop, (p n).1.2 ≠ q.1.2 :=
        not_frequently.mp hfreq
      have hstrict : ∀ᶠ n in atTop, (p n).1.2 < q.1.2 := by
        filter_upwards [hne] with n hn
        exact (hpHeight n).lt_of_ne hn
      obtain ⟨φ, hφ, hφStrict⟩ :=
        extraction_of_frequently_atTop hstrict.frequently
      have hsub : Tendsto (fun n => p (φ n)) atTop (𝓝 r) :=
        hpr.comp hφ.tendsto_atTop
      have hφStrictR : ∀ n, (p (φ n)).1.2 < r.1.2 := by
        intro n
        rw [heq]
        exact hφStrict n
      have hrLimit :=
        D.rightCompletedChain_limit_from_below
          (p := fun n => p (φ n)) (q := r) hsub hφStrictR
      have hrLimitQ :
          r.1.1 = Function.leftLim D.rightEndpoint q.1.2 := by
        rw [← heq]
        exact hrLimit
      have hqLower : D.lowerHeight < q.1.2 := by
        have hpLower := (D.rightCompletedChain_snd_mem_Icc (p (φ 0))).1
        exact hpLower.trans_lt (hφStrict 0)
      by_cases hupper : q.1.2 = D.upperHeight
      · have hqFiber : q.1.1 ∈ Icc D.upperSplit D.upperRight := by
          apply (D.rightCompletedChain_mem_upper_iff q.1.1).mp
          rw [← hupper]
          exact q.property
        unfold rightOrderSecondary
        rw [heq, hrLimitQ, hupper]
        simp only [D.lowerHeight_lt_upperHeight.ne', if_false, if_pos]
        simpa only [upperRight] using (neg_le_neg hqFiber.2)
      · have hoccupied : q.1.2 ∈ D.occupiedHeights :=
          D.mem_occupiedHeights_iff_height_bounds.mpr
            ⟨hqLower, (D.rightCompletedChain_snd_mem_Icc q).2.lt_of_ne hupper⟩
        have hqFiber := (D.rightCompletedChain_mem_interior_iff hoccupied).mp
          q.property
        unfold rightOrderSecondary
        rw [heq, hrLimitQ]
        simp only [hqLower.ne', hupper, if_false]
        by_cases horiented : Function.leftLim D.rightEndpoint q.1.2 ≤
            Function.rightLim D.rightEndpoint q.1.2
        · simp only [horiented, if_pos]
          simpa only [min_eq_left horiented] using hqFiber.1
        · simp only [horiented, if_false]
          have hreverse : Function.rightLim D.rightEndpoint q.1.2 ≤
              Function.leftLim D.rightEndpoint q.1.2 :=
            le_of_not_ge horiented
          have hqLe := hqFiber.2
          rw [max_eq_left hreverse] at hqLe
          linarith
  · exact (D.rightCompletedChain_le_iff r q).mpr (Or.inl hlt)

theorem isClosed_rightCompletedChain_Ici
    (D : SelectedBoundaryTopologyInput E U)
    (q : D.rightCompletedChain) :
    IsClosed {p : D.rightCompletedChain |
      @LE.le _ D.rightCompletedChainLinearOrder.toLE q p} := by
  apply IsSeqClosed.isClosed
  intro p r hp hpr
  have hprVal : Tendsto (fun n => (p n).1) atTop (𝓝 r.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp hpr
  have hpHeight : ∀ n, q.1.2 ≤ (p n).1.2 := by
    intro n
    rcases (D.rightCompletedChain_le_iff q (p n)).mp (hp n) with h | h
    · exact h.le
    · exact h.1.le
  have hrHeight : q.1.2 ≤ r.1.2 :=
    ge_of_tendsto hprVal.snd_nhds
      (Filter.Eventually.of_forall hpHeight)
  rcases hrHeight.eq_or_lt with heq | hlt
  · apply (D.rightCompletedChain_le_iff q r).mpr
    right
    refine ⟨heq, ?_⟩
    by_cases hfreq : ∃ᶠ n in atTop, (p n).1.2 = q.1.2
    · obtain ⟨φ, hφ, hφHeight⟩ := extraction_of_frequently_atTop hfreq
      have hsub : Tendsto (fun n => p (φ n)) atTop (𝓝 r) :=
        hpr.comp hφ.tendsto_atTop
      have hsubVal : Tendsto (fun n => (p (φ n)).1) atTop (𝓝 r.1) :=
        continuous_subtype_val.continuousAt.tendsto.comp hsub
      have hsecLe : ∀ n,
          D.rightOrderSecondary q.1 ≤
            D.rightOrderSecondary (p (φ n)).1 := by
        intro n
        rcases (D.rightCompletedChain_le_iff q (p (φ n))).mp
            (hp (φ n)) with h | h
        · rw [hφHeight n] at h
          exact (lt_irrefl q.1.2 h).elim
        · exact h.2
      have hsecTend : Tendsto
          (fun n => D.rightOrderSecondary (p (φ n)).1) atTop
          (𝓝 (D.rightOrderSecondary r.1)) := by
        have hx := hsubVal.fst_nhds
        by_cases hlower : q.1.2 = D.lowerHeight
        · simpa only [rightOrderSecondary, hφHeight, ← heq, hlower, if_pos]
            using hx
        · by_cases hupper : q.1.2 = D.upperHeight
          · simpa only [rightOrderSecondary, hφHeight, ← heq, hlower, hupper,
              D.lowerHeight_lt_upperHeight.ne', if_pos, if_false] using hx.neg
          · by_cases horiented : Function.leftLim D.rightEndpoint q.1.2 ≤
                Function.rightLim D.rightEndpoint q.1.2
            · simpa only [rightOrderSecondary, hφHeight, ← heq, hlower, hupper,
                horiented, if_pos, if_false] using hx
            · simpa only [rightOrderSecondary, hφHeight, ← heq, hlower, hupper,
                horiented, if_pos, if_false] using hx.neg
      exact ge_of_tendsto hsecTend
        (Filter.Eventually.of_forall hsecLe)
    · have hne : ∀ᶠ n in atTop, (p n).1.2 ≠ q.1.2 :=
        not_frequently.mp hfreq
      have hstrict : ∀ᶠ n in atTop, q.1.2 < (p n).1.2 := by
        filter_upwards [hne] with n hn
        exact (hpHeight n).lt_of_ne hn.symm
      obtain ⟨φ, hφ, hφStrict⟩ :=
        extraction_of_frequently_atTop hstrict.frequently
      have hsub : Tendsto (fun n => p (φ n)) atTop (𝓝 r) :=
        hpr.comp hφ.tendsto_atTop
      have hφStrictR : ∀ n, r.1.2 < (p (φ n)).1.2 := by
        intro n
        rw [← heq]
        exact hφStrict n
      have hrLimit :=
        D.rightCompletedChain_limit_from_above
          (p := fun n => p (φ n)) (q := r) hsub hφStrictR
      have hrLimitQ :
          r.1.1 = Function.rightLim D.rightEndpoint q.1.2 := by
        rw [heq]
        exact hrLimit
      have hqUpper : q.1.2 < D.upperHeight := by
        have hpUpper := (D.rightCompletedChain_snd_mem_Icc (p (φ 0))).2
        exact (hφStrict 0).trans_le hpUpper
      by_cases hlower : q.1.2 = D.lowerHeight
      · have hqFiber : q.1.1 ∈ Icc D.lowerSplit D.lowerRight := by
          apply (D.rightCompletedChain_mem_lower_iff q.1.1).mp
          rw [← hlower]
          exact q.property
        unfold rightOrderSecondary
        rw [← heq, hrLimitQ, hlower]
        simp only [if_pos]
        simpa only [lowerRight] using hqFiber.2
      · have hoccupied : q.1.2 ∈ D.occupiedHeights :=
          D.mem_occupiedHeights_iff_height_bounds.mpr
            ⟨(D.rightCompletedChain_snd_mem_Icc q).1.lt_of_ne (Ne.symm hlower),
              hqUpper⟩
        have hqFiber := (D.rightCompletedChain_mem_interior_iff hoccupied).mp
          q.property
        unfold rightOrderSecondary
        rw [← heq, hrLimitQ]
        simp only [hlower, hqUpper.ne, if_false]
        by_cases horiented : Function.leftLim D.rightEndpoint q.1.2 ≤
            Function.rightLim D.rightEndpoint q.1.2
        · simp only [horiented, if_pos]
          simpa only [max_eq_right horiented] using hqFiber.2
        · simp only [horiented, if_false]
          have hreverse : Function.rightLim D.rightEndpoint q.1.2 ≤
              Function.leftLim D.rightEndpoint q.1.2 :=
            le_of_not_ge horiented
          have hleQ := hqFiber.1
          rw [min_eq_right hreverse] at hleQ
          linarith
  · exact (D.rightCompletedChain_le_iff q r).mpr (Or.inl hlt)
end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
universe u

private theorem topology_eq_of_compact_to_t2 {X : Type u}
    (t₁ t₂ : TopologicalSpace X)
    (hc : @CompactSpace X t₁) (h2 : @T2Space X t₂)
    (h : t₁ ≤ t₂) : t₁ = t₂ := by
  have hid : @Continuous X X t₁ t₂ id := by
    exact continuous_iff_le_induced.mpr
      (by simpa only [@induced_id X t₂] using h)
  let e : X ≃ X := Equiv.refl X
  have he : @Continuous X X t₁ t₂ e := by simpa [e] using hid
  let H : @Homeomorph X X t₁ t₂ :=
    @Continuous.homeoOfEquivCompactToT2 X X t₁ t₂ hc h2 e he
  have hi : @Topology.IsInducing X X t₁ t₂ H :=
    @Homeomorph.isInducing X X t₁ t₂ H
  have hInduced : t₁ = TopologicalSpace.induced (H : X → X) t₂ :=
    @Topology.IsInducing.eq_induced X X t₁ t₂ H hi
  change t₁ = TopologicalSpace.induced id t₂ at hInduced
  simpa only [@induced_id X t₂] using hInduced

private theorem topology_eq_order_of_compact_closed_rays
    (α : Type u) [LinearOrder α] [t : TopologicalSpace α] [CompactSpace α]
    [ClosedIicTopology α] [ClosedIciTopology α] :
    t = Preorder.topology α := by
  have h_to_order : t ≤ Preorder.topology α := by
    rw [Preorder.topology]
    apply le_generateFrom
    rintro U ⟨a, rfl | rfl⟩
    · simpa only [compl_Iic] using
        (@isClosed_Iic α t _ _ (a := a)).isOpen_compl
    · simpa only [compl_Ici] using
        (@isClosed_Ici α t _ _ (a := a)).isOpen_compl
  have hOrder : @OrderTopology α (Preorder.topology α)
      (inferInstance : Preorder α) :=
    @OrderTopology.mk α (Preorder.topology α)
      (inferInstance : Preorder α) rfl
  have hClosed : @OrderClosedTopology α (Preorder.topology α)
      (inferInstance : Preorder α) :=
    @OrderTopology.to_orderClosedTopology α (Preorder.topology α)
      (inferInstance : LinearOrder α) hOrder
  have hT2 : @T2Space α (Preorder.topology α) :=
    @OrderClosedTopology.to_t2Space α (Preorder.topology α)
      (inferInstance : PartialOrder α) hClosed
  exact topology_eq_of_compact_to_t2 t (Preorder.topology α)
    (inferInstance : CompactSpace α) hT2 h_to_order

private noncomputable abbrev completeLinearOrderOfCompactClosedRays
    (α : Type u) [LinearOrder α] [TopologicalSpace α] [CompactSpace α]
    [ClosedIicTopology α] [ClosedIciTopology α] [Nonempty α] :
    CompleteLinearOrder α := by
  classical
  let bottom : α :=
    Classical.choose (isCompact_univ.exists_isLeast
      (univ_nonempty : (univ : Set α).Nonempty))
  have hbottom : IsLeast (univ : Set α) bottom :=
    Classical.choose_spec (isCompact_univ.exists_isLeast
      (univ_nonempty : (univ : Set α).Nonempty))
  let supChoice : Set α → α := fun s =>
    if hs : s.Nonempty then
      Classical.choose
        (isClosed_closure.isCompact.exists_isGreatest (hs.mono subset_closure))
    else
      bottom
  letI : SupSet α := ⟨supChoice⟩
  have hsup : ∀ s : Set α, IsLUB s (sSup s) := by
    intro s
    by_cases hs : s.Nonempty
    · have hgreatest : IsGreatest (closure s) (sSup s) := by
        change IsGreatest (closure s) (supChoice s)
        simp only [supChoice, hs, ↓reduceDIte]
        exact Classical.choose_spec
          (isClosed_closure.isCompact.exists_isGreatest (hs.mono subset_closure))
      refine ⟨fun x hx => hgreatest.2 (subset_closure hx), ?_⟩
      intro a ha
      exact (closure_minimal ha isClosed_Iic) hgreatest.1
    · have hempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨by simp, fun a _ => ?_⟩
      change supChoice ∅ ≤ a
      simpa only [supChoice, Set.not_nonempty_empty, ↓reduceDIte] using
        hbottom.2 (mem_univ a)
  let completeLattice : CompleteLattice α :=
    { completeLatticeOfSup α hsup with
      sup := max
      inf := min
      le_sup_left := le_max_left
      le_sup_right := le_max_right
      sup_le := fun _ _ _ => max_le
      inf_le_left := min_le_left
      inf_le_right := min_le_right
      le_inf := fun _ _ _ => le_min }
  exact { completeLattice, (inferInstance : LinearOrder α),
    LinearOrder.toBiheytingAlgebra α with }

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

variable {E U : Set PlanePoint}

/-- The planar subtype topology of the left chain is its intrinsic order topology. -/
theorem leftCompletedChain_topology_eq_orderTopology
    (D : SelectedBoundaryTopologyInput E U) :
    (inferInstance : TopologicalSpace D.leftCompletedChain) =
      @Preorder.topology D.leftCompletedChain
        D.leftCompletedChainLinearOrder.toPreorder := by
  exact @topology_eq_order_of_compact_closed_rays
    D.leftCompletedChain D.leftCompletedChainLinearOrder
    (inferInstance : TopologicalSpace D.leftCompletedChain)
    (isCompact_iff_compactSpace.mp D.isCompact_leftCompletedChain)
    (@ClosedIicTopology.mk D.leftCompletedChain
      (inferInstance : TopologicalSpace D.leftCompletedChain)
      D.leftCompletedChainLinearOrder.toPreorder
      D.isClosed_leftCompletedChain_Iic)
    (@ClosedIciTopology.mk D.leftCompletedChain
      (inferInstance : TopologicalSpace D.leftCompletedChain)
      D.leftCompletedChainLinearOrder.toPreorder
      D.isClosed_leftCompletedChain_Ici)

/-- The planar subtype topology of the right chain is its intrinsic order topology. -/
theorem rightCompletedChain_topology_eq_orderTopology
    (D : SelectedBoundaryTopologyInput E U) :
    (inferInstance : TopologicalSpace D.rightCompletedChain) =
      @Preorder.topology D.rightCompletedChain
        D.rightCompletedChainLinearOrder.toPreorder := by
  exact @topology_eq_order_of_compact_closed_rays
    D.rightCompletedChain D.rightCompletedChainLinearOrder
    (inferInstance : TopologicalSpace D.rightCompletedChain)
    (isCompact_iff_compactSpace.mp D.isCompact_rightCompletedChain)
    (@ClosedIicTopology.mk D.rightCompletedChain
      (inferInstance : TopologicalSpace D.rightCompletedChain)
      D.rightCompletedChainLinearOrder.toPreorder
      D.isClosed_rightCompletedChain_Iic)
    (@ClosedIciTopology.mk D.rightCompletedChain
      (inferInstance : TopologicalSpace D.rightCompletedChain)
      D.rightCompletedChainLinearOrder.toPreorder
      D.isClosed_rightCompletedChain_Ici)

/-- The left chain's planar topology is an order topology for its explicit order. -/
noncomputable abbrev leftCompletedChainPlanarOrderTopology
    (D : SelectedBoundaryTopologyInput E U) :
    @OrderTopology D.leftCompletedChain
      (inferInstance : TopologicalSpace D.leftCompletedChain)
      D.leftCompletedChainLinearOrder.toPreorder :=
  @OrderTopology.mk D.leftCompletedChain
    (inferInstance : TopologicalSpace D.leftCompletedChain)
    D.leftCompletedChainLinearOrder.toPreorder
    D.leftCompletedChain_topology_eq_orderTopology

/-- The right chain's planar topology is an order topology for its explicit order. -/
noncomputable abbrev rightCompletedChainPlanarOrderTopology
    (D : SelectedBoundaryTopologyInput E U) :
    @OrderTopology D.rightCompletedChain
      (inferInstance : TopologicalSpace D.rightCompletedChain)
      D.rightCompletedChainLinearOrder.toPreorder :=
  @OrderTopology.mk D.rightCompletedChain
    (inferInstance : TopologicalSpace D.rightCompletedChain)
    D.rightCompletedChainLinearOrder.toPreorder
    D.rightCompletedChain_topology_eq_orderTopology

/-- The compact left traversal admits every supremum and infimum. -/
noncomputable abbrev leftCompletedChainCompleteLinearOrder
    (D : SelectedBoundaryTopologyInput E U) :
    CompleteLinearOrder D.leftCompletedChain := by
  exact @completeLinearOrderOfCompactClosedRays
    D.leftCompletedChain D.leftCompletedChainLinearOrder
    (inferInstance : TopologicalSpace D.leftCompletedChain)
    (isCompact_iff_compactSpace.mp D.isCompact_leftCompletedChain)
    (@ClosedIicTopology.mk D.leftCompletedChain
      (inferInstance : TopologicalSpace D.leftCompletedChain)
      D.leftCompletedChainLinearOrder.toPreorder
      D.isClosed_leftCompletedChain_Iic)
    (@ClosedIciTopology.mk D.leftCompletedChain
      (inferInstance : TopologicalSpace D.leftCompletedChain)
      D.leftCompletedChainLinearOrder.toPreorder
      D.isClosed_leftCompletedChain_Ici)
    ⟨⟨D.lowerSplitPoint, D.lowerSplitPoint_mem_leftCompletedChain⟩⟩

/-- The compact right traversal admits every supremum and infimum. -/
noncomputable abbrev rightCompletedChainCompleteLinearOrder
    (D : SelectedBoundaryTopologyInput E U) :
    CompleteLinearOrder D.rightCompletedChain := by
  exact @completeLinearOrderOfCompactClosedRays
    D.rightCompletedChain D.rightCompletedChainLinearOrder
    (inferInstance : TopologicalSpace D.rightCompletedChain)
    (isCompact_iff_compactSpace.mp D.isCompact_rightCompletedChain)
    (@ClosedIicTopology.mk D.rightCompletedChain
      (inferInstance : TopologicalSpace D.rightCompletedChain)
      D.rightCompletedChainLinearOrder.toPreorder
      D.isClosed_rightCompletedChain_Iic)
    (@ClosedIciTopology.mk D.rightCompletedChain
      (inferInstance : TopologicalSpace D.rightCompletedChain)
      D.rightCompletedChainLinearOrder.toPreorder
      D.isClosed_rightCompletedChain_Ici)
    ⟨⟨D.lowerSplitPoint, D.lowerSplitPoint_mem_rightCompletedChain⟩⟩

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
