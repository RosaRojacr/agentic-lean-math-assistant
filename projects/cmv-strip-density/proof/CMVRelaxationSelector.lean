import CMVRelaxation

open Filter Set MeasureTheory Topology

namespace CMVRelaxation

/-- A strict upper bound on a liminf is witnessed arbitrarily far out in the
sequence; no attainment or eventual upper bound is required. -/
theorem exists_ge_of_liminf_lt {u : ℕ → ENNReal} {q : ENNReal}
    (h : liminf u atTop < q) (N : ℕ) :
    ∃ n, n ≥ N ∧ u n < q := by
  have hf : ∃ᶠ n in atTop, u n < q :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) h
  exact frequently_atTop.mp hf N

/-- A strict bound on the literal relaxed perimeter produces one actual smooth
approximant meeting both the prescribed distance and cost thresholds. -/
theorem exists_smoothDomain_of_relaxedPerimeter_lt
    (lam : ℝ) {E : Set PlanePoint} (_hE : NullMeasurableSet E volume)
    {q epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hrel : relaxedPerimeter lam E < ENNReal.ofReal q) :
    ∃ U : Set PlanePoint,
      IsSmoothDomain U ∧
      characteristicDistance U E < ENNReal.ofReal epsilon ∧
      smoothCost lam U < ENNReal.ofReal q := by
  unfold relaxedPerimeter at hrel
  rw [sInf_lt_iff] at hrel
  obtain ⟨c, ⟨A, _hE', hconv, hcost⟩, hc⟩ := hrel
  have hcheap : ∃ᶠ n in atTop,
      smoothCost lam (A.carrier n) < ENNReal.ofReal q := by
    rw [← hcost] at hc
    exact frequently_lt_of_liminf_lt (by isBoundedDefault) hc
  have hdist : ∀ᶠ n in atTop,
      characteristicDistance (A.carrier n) E < ENNReal.ofReal epsilon :=
    hconv.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon))
  obtain ⟨n, hncheap, hndist⟩ := (hcheap.and_eventually hdist).exists
  exact ⟨A.carrier n, A.smooth n, hndist, hncheap⟩

/-- Concrete positive-volume application: the universal selector, together
with the literal constant disk sequence and its finite cost, gives a genuinely
selected (not stipulated constant) disk approximant at every distance scale. -/
theorem unitDisk_exists_selected_approximant (lam : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ q : ℝ, ∃ U : Set PlanePoint,
      IsSmoothDomain U ∧
      characteristicDistance U unitDisk < ENNReal.ofReal epsilon ∧
      smoothCost lam U < ENNReal.ofReal q := by
  let c := smoothCost lam unitDisk
  have hc : c ≠ ⊤ := (smoothCost_unitDisk_lt_top lam).ne
  let q : ℝ := c.toReal + 1
  have hcq : c < ENNReal.ofReal q := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hc]
    dsimp [q]
    linarith
  have hrel_le : relaxedPerimeter lam unitDisk ≤ c := by
    apply sInf_le
    exact ⟨unitDiskConstantSequence,
      isOpen_unitDisk.measurableSet.nullMeasurableSet,
      unitDiskConstantSequence_converges,
      unitDiskConstantSequence_cost lam⟩
  refine ⟨q, ?_⟩
  exact exists_smoothDomain_of_relaxedPerimeter_lt lam
    isOpen_unitDisk.measurableSet.nullMeasurableSet hepsilon
    (hrel_le.trans_lt hcq)

end CMVRelaxation
