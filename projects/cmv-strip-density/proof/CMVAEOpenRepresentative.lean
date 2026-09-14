/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxation

/-!
# Almost-everywhere invariant open representatives

For a planar carrier `E`, `aeOpenRepresentative E` consists of the points that
have a ball whose complement in `E` has zero planar volume.  The construction
selects an open set from the measure class whenever that class has an open
representative.  It does not infer existence of such a representative from
relaxed minimality and does not identify topological frontiers under almost-
everywhere equality.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology symmDiff

noncomputable section

namespace CMVRelaxation

/-- Points having a neighborhood that is contained in `E` up to planar volume
zero. -/
def aeOpenRepresentative (E : Set PlanePoint) : Set PlanePoint :=
  {p | ∃ r > 0, volume (Metric.ball p r \ E) = 0}

@[simp] theorem mem_aeOpenRepresentative {E : Set PlanePoint} {p : PlanePoint} :
    p ∈ aeOpenRepresentative E ↔
      ∃ r > 0, volume (Metric.ball p r \ E) = 0 :=
  Iff.rfl

/-- The ball definition is the complement of the support of volume restricted
to the measure-theoretic complement. -/
theorem aeOpenRepresentative_eq_compl_support (E : Set PlanePoint) :
    aeOpenRepresentative E = (volume.restrict Eᶜ).supportᶜ := by
  ext p
  rw [mem_compl_iff, Measure.notMem_support_iff_exists]
  constructor
  · rintro ⟨r, hr, hzero⟩
    refine ⟨Metric.ball p r,
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr), ?_⟩
    rw [Measure.restrict_apply measurableSet_ball]
    simpa only [sdiff_eq, inter_comm] using hzero
  · rintro ⟨V, hV, hzero⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨r, hr, ?_⟩
    have hb : (volume.restrict Eᶜ) (Metric.ball p r) = 0 :=
      measure_mono_null hball hzero
    rw [Measure.restrict_apply measurableSet_ball] at hb
    simpa only [sdiff_eq] using hb

/-- The selected representative is open. -/
theorem isOpen_aeOpenRepresentative (E : Set PlanePoint) :
    IsOpen (aeOpenRepresentative E) := by
  rw [aeOpenRepresentative_eq_compl_support]
  exact Measure.isOpen_compl_support

/-- The construction depends only on the planar almost-everywhere class. -/
theorem aeOpenRepresentative_congr_ae {E F : Set PlanePoint}
    (hEF : E =ᵐ[volume] F) :
    aeOpenRepresentative E = aeOpenRepresentative F := by
  rw [aeOpenRepresentative_eq_compl_support,
    aeOpenRepresentative_eq_compl_support,
    Measure.restrict_congr_set hEF.compl]

/-- An open set is contained in its own selected representative. -/
theorem open_subset_aeOpenRepresentative_self {U : Set PlanePoint}
    (hU : IsOpen U) : U ⊆ aeOpenRepresentative U := by
  intro p hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU p hp
  refine ⟨r, hr, measure_mono_null ?_ measure_empty⟩
  intro q hq
  exact (hq.2 (hball hq.1)).elim

/-- Every explicitly supplied open representative of `E` is contained in the
selected representative. -/
theorem open_subset_aeOpenRepresentative {E U : Set PlanePoint}
    (hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    U ⊆ aeOpenRepresentative E := by
  rw [aeOpenRepresentative_congr_ae hEU]
  exact open_subset_aeOpenRepresentative_self hU

/-- The selected representative cannot leave the closure of the original
carrier. -/
theorem aeOpenRepresentative_subset_closure_self (E : Set PlanePoint) :
    aeOpenRepresentative E ⊆ closure E := by
  intro p hp
  apply Metric.mem_closure_iff.2
  intro s hs
  by_contra hnone
  have hfar : ∀ q, q ∈ E → s ≤ dist p q := by
    intro q hqE
    exact le_of_not_gt (fun hdist => hnone ⟨q, hqE, hdist⟩)
  rcases hp with ⟨r, hr, hzero⟩
  let t := min r s
  have ht : 0 < t := lt_min hr hs
  have hsub : Metric.ball p t ⊆ Metric.ball p r \ E := by
    intro q hq
    refine ⟨Metric.ball_subset_ball (min_le_left _ _) hq, ?_⟩
    intro hqE
    exact (not_lt_of_ge (hfar q hqE)) (by
      simpa only [Metric.mem_ball, dist_comm] using
        (Metric.ball_subset_ball (min_le_right _ _) hq))
  have hballzero : volume (Metric.ball p t) = 0 :=
    measure_mono_null hsub hzero
  exact (Metric.measure_ball_pos volume p ht).ne' hballzero

/-- Under an open almost-everywhere representative, the selected set stays in
that representative's closure. -/
theorem aeOpenRepresentative_subset_closure_open
    {E U : Set PlanePoint} (_hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    aeOpenRepresentative E ⊆ closure U := by
  rw [aeOpenRepresentative_congr_ae hEU]
  exact aeOpenRepresentative_subset_closure_self U

/-- Only a null set can be added to an arbitrary carrier by selection. -/
theorem volume_aeOpenRepresentative_sdiff (E : Set PlanePoint) :
    volume (aeOpenRepresentative E \ E) = 0 := by
  rw [aeOpenRepresentative_eq_compl_support]
  have hzero := Measure.measure_compl_support
    (μ := volume.restrict Eᶜ)
  rw [Measure.restrict_apply Measure.isOpen_compl_support.measurableSet] at hzero
  simpa only [sdiff_eq] using hzero

/-- Selection of an open set agrees with that set almost everywhere. -/
theorem aeOpenRepresentative_ae_eq_self_of_open {U : Set PlanePoint}
    (hU : IsOpen U) : aeOpenRepresentative U =ᵐ[volume] U := by
  rw [ae_eq_set]
  refine ⟨volume_aeOpenRepresentative_sdiff U, ?_⟩
  apply measure_mono_null (t := ∅)
  · intro p hp
    exact (hp.2 (open_subset_aeOpenRepresentative_self hU hp.1)).elim
  · exact measure_empty

/-- Selection agrees with every supplied open representative of the same
measure class. -/
theorem aeOpenRepresentative_ae_eq_open {E U : Set PlanePoint}
    (hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    aeOpenRepresentative E =ᵐ[volume] U := by
  rw [aeOpenRepresentative_congr_ae hEU]
  exact aeOpenRepresentative_ae_eq_self_of_open hU

/-- If `E` admits an open almost-everywhere representative, selection remains
in the measure class of `E`. -/
theorem aeOpenRepresentative_ae_eq {E U : Set PlanePoint}
    (hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    aeOpenRepresentative E =ᵐ[volume] E :=
  (aeOpenRepresentative_ae_eq_open hU hEU).trans hEU.symm

/-- Selection is idempotent, without an open-representative premise on `E`. -/
theorem aeOpenRepresentative_idempotent (E : Set PlanePoint) :
    aeOpenRepresentative (aeOpenRepresentative E) =
      aeOpenRepresentative E := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hp with ⟨r, hr, hzero⟩
    refine ⟨r, hr, ?_⟩
    apply measure_mono_null
      (show Metric.ball p r \ E ⊆
        (Metric.ball p r \ aeOpenRepresentative E) ∪
          (aeOpenRepresentative E \ E) by
        intro q hq
        by_cases hqO : q ∈ aeOpenRepresentative E
        · exact Or.inr ⟨hqO, hq.2⟩
        · exact Or.inl ⟨hq.1, hqO⟩)
    exact measure_union_null hzero (volume_aeOpenRepresentative_sdiff E)
  · exact open_subset_aeOpenRepresentative_self
      (isOpen_aeOpenRepresentative E)

/-- A stronger one-sided maximality form: an open set whose excess over `E` is
null lies in the selected representative. -/
theorem open_subset_aeOpenRepresentative_of_sdiff_null
    {E V : Set PlanePoint} (hV : IsOpen V)
    (hVE : volume (V \ E) = 0) :
    V ⊆ aeOpenRepresentative E := by
  intro p hp
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV p hp
  refine ⟨r, hr, measure_mono_null ?_ hVE⟩
  intro q hq
  exact ⟨hball hq.1, hq.2⟩

/-- If the measure class has an open representative, the selected
representative is the greatest open representative in that class. -/
theorem aeOpenRepresentative_isGreatest {E U : Set PlanePoint}
    (hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    IsGreatest
      {V : Set PlanePoint | IsOpen V ∧ V =ᵐ[volume] E}
      (aeOpenRepresentative E) := by
  refine ⟨⟨isOpen_aeOpenRepresentative E,
    aeOpenRepresentative_ae_eq hU hEU⟩, ?_⟩
  intro V hV
  exact open_subset_aeOpenRepresentative hV.1 hV.2.symm

/-- Boundedness transfers from a bounded almost-everywhere representative. -/
theorem isBounded_aeOpenRepresentative_of_ae
    {E U : Set PlanePoint} (hEU : E =ᵐ[volume] U)
    (hUbounded : Bornology.IsBounded U) :
    Bornology.IsBounded (aeOpenRepresentative E) := by
  rw [aeOpenRepresentative_congr_ae hEU]
  exact hUbounded.closure.subset
    (aeOpenRepresentative_subset_closure_self U)

/-- Connectedness transfers from an explicitly supplied connected open
representative. -/
theorem isConnected_aeOpenRepresentative_of_open_ae
    {E U : Set PlanePoint} (hU : IsOpen U) (hEU : E =ᵐ[volume] U)
    (hUconnected : IsConnected U) :
    IsConnected (aeOpenRepresentative E) :=
  hUconnected.subset_closure
    (open_subset_aeOpenRepresentative hU hEU)
    (aeOpenRepresentative_subset_closure_open hU hEU)

/-- The selected representative can fill null punctures in an open
representative, but it creates no new outer frontier: every selected-frontier
point is an actual frontier point of the supplied open representative. -/
theorem frontier_aeOpenRepresentative_subset_frontier_open
    {E U : Set PlanePoint} (hU : IsOpen U) (hEU : E =ᵐ[volume] U) :
    frontier (aeOpenRepresentative E) ⊆ frontier U := by
  intro p hp
  have hclosureSub :
      closure (aeOpenRepresentative E) ⊆ closure U :=
    closure_minimal
      (aeOpenRepresentative_subset_closure_open hU hEU) isClosed_closure
  have hpClosureU : p ∈ closure U :=
    hclosureSub (frontier_subset_closure hp)
  have hpNotSelected : p ∉ aeOpenRepresentative E := by
    have hp' := hp
    rw [(isOpen_aeOpenRepresentative E).frontier_eq] at hp'
    exact hp'.2
  have hpNotU : p ∉ U := by
    intro hpU
    exact hpNotSelected (open_subset_aeOpenRepresentative hU hEU hpU)
  rw [hU.frontier_eq]
  exact ⟨hpClosureU, hpNotU⟩

namespace PuncturedDiskExample

/-- The radius-two Euclidean disk from the retained accumulating-puncture
counterexample. -/
def disk : Set PlanePoint :=
  {p | p.1 ^ 2 + p.2 ^ 2 < 4}

/-- The punctures `(1 / (n + 1), 1)` accumulate at `(0, 1)`. -/
def punctureSequence (n : ℕ) : PlanePoint :=
  (1 / ((n : ℝ) + 1), 1)

/-- The accumulating sequence together with its limit point. -/
def accumulatingPunctures : Set PlanePoint :=
  insert (0, 1) (Set.range punctureSequence)

/-- The actual disk with the closed countable puncture set removed. -/
def puncturedDisk : Set PlanePoint :=
  disk \ accumulatingPunctures

theorem isOpen_disk : IsOpen disk := by
  exact isOpen_lt (by fun_prop) continuous_const

theorem accumulatingPunctures_countable : accumulatingPunctures.Countable := by
  exact (Set.countable_range punctureSequence).insert (0, 1)

theorem volume_accumulatingPunctures : volume accumulatingPunctures = 0 := by
  exact accumulatingPunctures_countable.measure_zero volume

theorem isClosed_accumulatingPunctures : IsClosed accumulatingPunctures := by
  have hx : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq : Tendsto punctureSequence atTop (𝓝 ((0, 1) : PlanePoint)) := by
    change Tendsto
      (fun n : ℕ => (1 / ((n : ℝ) + 1), (1 : ℝ)))
      atTop (𝓝 ((0, 1) : ℝ × ℝ))
    exact hx.prodMk_nhds tendsto_const_nhds
  exact hseq.isCompact_insert_range.isClosed

theorem accumulatingPunctures_subset_disk : accumulatingPunctures ⊆ disk := by
  rintro p (rfl | ⟨n, rfl⟩)
  · norm_num [disk]
  · change (1 / ((n : ℝ) + 1)) ^ 2 + 1 ^ 2 < 4
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by norm_num
    have hpos : 0 < (n : ℝ) + 1 := lt_of_lt_of_le zero_lt_one hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hpos).2 hn
    have hnonneg : 0 ≤ 1 / ((n : ℝ) + 1) :=
      le_of_lt (one_div_pos.mpr hpos)
    nlinarith

theorem isOpen_puncturedDisk : IsOpen puncturedDisk :=
  isOpen_disk.sdiff isClosed_accumulatingPunctures

private lemma exists_strict_exterior_mem_ball {p : PlanePoint} {r : ℝ}
    (hr : 0 < r) (hp : p ∉ disk) :
    ∃ q ∈ Metric.ball p r, 4 < q.1 ^ 2 + q.2 ^ 2 := by
  have hp' : 4 ≤ p.1 ^ 2 + p.2 ^ 2 := by
    simpa [disk] using (le_of_not_gt hp)
  rcases lt_trichotomy p.1 0 with hx | hx | hx
  · refine ⟨(p.1 - r / 2, p.2), ?_, ?_⟩
    · rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    · nlinarith [sq_nonneg (p.1 - r / 2)]
  · have hyne : p.2 ≠ 0 := by
      intro hy
      rw [hx, hy] at hp'
      norm_num at hp'
    rcases lt_or_gt_of_ne hyne with hy | hy
    · refine ⟨(p.1, p.2 - r / 2), ?_, ?_⟩
      · rw [Metric.mem_ball, Prod.dist_eq]
        simp [abs_of_pos hr]
        exact hr
      · nlinarith [sq_nonneg (p.2 - r / 2)]
    · refine ⟨(p.1, p.2 + r / 2), ?_, ?_⟩
      · rw [Metric.mem_ball, Prod.dist_eq]
        simp [abs_of_pos hr]
        exact hr
      · nlinarith [sq_nonneg (p.2 + r / 2)]
  · refine ⟨(p.1 + r / 2, p.2), ?_, ?_⟩
    · rw [Metric.mem_ball, Prod.dist_eq]
      simp [abs_of_pos hr]
      exact hr
    · nlinarith [sq_nonneg (p.1 + r / 2)]

/-- The original Euclidean disk is fixed exactly by the selected
representative. -/
theorem aeOpenRepresentative_disk : aeOpenRepresentative disk = disk := by
  apply Set.Subset.antisymm
  · rintro p ⟨r, hr, hzero⟩
    by_contra hp
    obtain ⟨q, hqball, hqext⟩ := exists_strict_exterior_mem_ball hr hp
    let V : Set PlanePoint := Metric.ball p r ∩
      {z | 4 < z.1 ^ 2 + z.2 ^ 2}
    have hVopen : IsOpen V := Metric.isOpen_ball.inter
      (isOpen_lt continuous_const (by fun_prop))
    have hVpos : 0 < volume V :=
      hVopen.measure_pos volume ⟨q, hqball, hqext⟩
    have hVsub : V ⊆ Metric.ball p r \ disk := by
      rintro z ⟨hzball, hzext⟩
      change 4 < z.1 ^ 2 + z.2 ^ 2 at hzext
      refine ⟨hzball, ?_⟩
      intro hzDisk
      exact (not_lt_of_ge hzDisk.le) hzext
    have hle := measure_mono (μ := volume) hVsub
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hVpos
  · exact open_subset_aeOpenRepresentative_self isOpen_disk

/-- The accumulating closed countable punctures are repaired exactly.  No
frontier equality or finite-contact premise is used. -/
theorem aeOpenRepresentative_puncturedDisk :
    aeOpenRepresentative puncturedDisk = disk := by
  have hnull : volume (disk ∩ accumulatingPunctures) = 0 :=
    measure_mono_null inter_subset_right volume_accumulatingPunctures
  have hae : puncturedDisk =ᵐ[volume] disk :=
    sdiff_ae_eq_self.mpr hnull
  rw [aeOpenRepresentative_congr_ae hae, aeOpenRepresentative_disk]

end PuncturedDiskExample

/-! ## Relaxed source semantics and selected frontiers -/

/-- Source admissibility for the concrete relaxed semantics is invariant under
planar almost-everywhere replacement. -/
theorem relaxedSourceSemantics_isAdmissible_congr_ae
    (lam : ℝ) {E F : Set PlanePoint} (hEF : E =ᵐ[volume] F) :
    (relaxedSourceSemantics lam).IsAdmissible E ↔
      (relaxedSourceSemantics lam).IsAdmissible F := by
  rw [relaxedSourceSemantics_isAdmissible,
    relaxedSourceSemantics_isAdmissible]
  exact and_congr
    (relaxedSourceSemantics_isFinitePerimeter_congr_ae lam hEF)
    (integrableOn_congr_set_ae hEF)

/-- Source minimality for the concrete relaxed semantics is invariant under
planar almost-everywhere replacement. -/
theorem relaxedSourceSemantics_isMinimizer_congr_ae
    (lam : ℝ) {E F : Set PlanePoint} (hEF : E =ᵐ[volume] F) :
    (relaxedSourceSemantics lam).IsMinimizer E ↔
      (relaxedSourceSemantics lam).IsMinimizer F := by
  have hadmissible :=
    relaxedSourceSemantics_isAdmissible_congr_ae lam hEF
  have harea := weightedArea_congr_ae lam hEF
  constructor
  · rintro ⟨hE, hmin⟩
    have hperimeter :=
      relaxedSourceSemantics_perimeter_congr_ae lam hE.1 hEF
    refine ⟨hadmissible.1 hE, ?_⟩
    intro competitor hcompetitor hcompetitorArea
    rw [← hperimeter]
    exact hmin competitor hcompetitor
      (hcompetitorArea.trans harea.symm)
  · rintro ⟨hF, hmin⟩
    have hperimeter :=
      relaxedSourceSemantics_perimeter_congr_ae lam hF.1 hEF.symm
    refine ⟨hadmissible.2 hF, ?_⟩
    intro competitor hcompetitor hcompetitorArea
    rw [← hperimeter]
    exact hmin competitor hcompetitor
      (hcompetitorArea.trans harea)

/-- Weighted-area integrability is preserved by selection when an explicit
open representative exists. -/
theorem integrableOn_aeOpenRepresentative_iff
    {lam : ℝ} {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) :
    IntegrableOn (StripDensity lam) (aeOpenRepresentative E) ↔
      IntegrableOn (StripDensity lam) E :=
  integrableOn_congr_set_ae (aeOpenRepresentative_ae_eq hU hEU)

/-- The weighted area itself is unchanged by selection. -/
theorem weightedArea_aeOpenRepresentative
    (lam : ℝ) {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) :
    _root_.WeightedArea lam (aeOpenRepresentative E) =
      _root_.WeightedArea lam E :=
  weightedArea_congr_ae lam (aeOpenRepresentative_ae_eq hU hEU)

/-- The extended relaxed perimeter is unchanged by selection, including at
the value `∞`. -/
theorem relaxedPerimeter_aeOpenRepresentative
    (lam : ℝ) {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) :
    relaxedPerimeter lam (aeOpenRepresentative E) =
      relaxedPerimeter lam E :=
  relaxedPerimeter_congr_ae lam (aeOpenRepresentative_ae_eq hU hEU)

/-- Concrete source finiteness is equivalent before and after selection. -/
theorem relaxedSourceSemantics_isFinitePerimeter_aeOpenRepresentative_iff
    (lam : ℝ) {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) :
    (relaxedSourceSemantics lam).IsFinitePerimeter
        (aeOpenRepresentative E) ↔
      (relaxedSourceSemantics lam).IsFinitePerimeter E :=
  relaxedSourceSemantics_isFinitePerimeter_congr_ae lam
    (aeOpenRepresentative_ae_eq hU hEU)

/-- Concrete source admissibility is equivalent before and after selection. -/
theorem relaxedSourceSemantics_isAdmissible_aeOpenRepresentative_iff
    (lam : ℝ) {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) :
    (relaxedSourceSemantics lam).IsAdmissible (aeOpenRepresentative E) ↔
      (relaxedSourceSemantics lam).IsAdmissible E :=
  relaxedSourceSemantics_isAdmissible_congr_ae lam
    (aeOpenRepresentative_ae_eq hU hEU)

/-- Concrete source minimality is equivalent before and after selection. -/
theorem relaxedSourceSemantics_isMinimizer_aeOpenRepresentative_iff
    (lam : ℝ) {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U) :
    (relaxedSourceSemantics lam).IsMinimizer (aeOpenRepresentative E) ↔
      (relaxedSourceSemantics lam).IsMinimizer E :=
  relaxedSourceSemantics_isMinimizer_congr_ae lam
    (aeOpenRepresentative_ae_eq hU hEU)

/-- Real source perimeter equality is used only after source finiteness has
been established. -/
theorem relaxedSourceSemantics_perimeter_aeOpenRepresentative
    (lam : ℝ) {E U : Set PlanePoint} (hU : IsOpen U)
    (hEU : E =ᵐ[volume] U)
    (hfinite :
      (relaxedSourceSemantics lam).IsFinitePerimeter
        (aeOpenRepresentative E)) :
    (relaxedSourceSemantics lam).perimeter (aeOpenRepresentative E) =
      (relaxedSourceSemantics lam).perimeter E :=
  relaxedSourceSemantics_perimeter_congr_ae lam hfinite
    (aeOpenRepresentative_ae_eq hU hEU)

/-- At every selected frontier point, both the original carrier and its
complement have positive planar volume in every positive-radius ball.  This is
qualitative neighborhood positivity, not a uniform density estimate. -/
theorem frontier_aeOpenRepresentative_volume_pos
    {E U : Set PlanePoint} (hU : IsOpen U) (hEU : E =ᵐ[volume] U)
    {p : PlanePoint} (hp : p ∈ frontier (aeOpenRepresentative E))
    {r : ℝ} (hr : 0 < r) :
    0 < volume (E ∩ Metric.ball p r) ∧
      0 < volume (Eᶜ ∩ Metric.ball p r) := by
  let O : Set PlanePoint := aeOpenRepresentative E
  have hOopen : IsOpen O := isOpen_aeOpenRepresentative E
  have hOE : O =ᵐ[volume] E :=
    aeOpenRepresentative_ae_eq hU hEU
  have hpClosure : p ∈ closure O := frontier_subset_closure hp
  obtain ⟨q, hqO, hqdist⟩ :=
    (Metric.mem_closure_iff.1 hpClosure) r hr
  have hnonempty : (O ∩ Metric.ball p r).Nonempty :=
    ⟨q, hqO, by
      simpa only [Metric.mem_ball, dist_comm] using hqdist⟩
  have hopen : IsOpen (O ∩ Metric.ball p r) :=
    hOopen.inter Metric.isOpen_ball
  have hOpos : 0 < volume (O ∩ Metric.ball p r) :=
    hopen.measure_pos volume hnonempty
  have hinter :
      (O ∩ Metric.ball p r : Set PlanePoint) =ᵐ[volume]
        (E ∩ Metric.ball p r : Set PlanePoint) :=
    hOE.inter (ae_eq_refl (Metric.ball p r))
  constructor
  · rw [← measure_congr hinter]
    exact hOpos
  · have hpNotO : p ∉ O := by
      intro hpO
      have hpInter : p ∈ O ∩ frontier O := ⟨hpO, hp⟩
      rw [hOopen.inter_frontier_eq] at hpInter
      exact hpInter
    have hne : volume (Metric.ball p r \ E) ≠ 0 := by
      intro hzero
      exact hpNotO ⟨r, hr, hzero⟩
    have hpos : 0 < volume (Metric.ball p r \ E) :=
      pos_iff_ne_zero.mpr hne
    simpa only [Set.sdiff_eq, inter_comm] using hpos

end CMVRelaxation
