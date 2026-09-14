import CMVFiniteBandCostComparison
import CMVAEIntervalSections

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation.FiniteBandRearrangement

/-- Equality in the one-component graph-speed comparison occurs exactly when
its two endpoint derivatives have zero sum, i.e. when the interval center has
zero derivative. -/
theorem centered_single_speed_eq_endpoint_speed_sum_iff (a b : ℝ) :
    2 * Real.sqrt (1 + ((b - a) / 2) ^ 2) =
        Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) ↔
      a + b = 0 := by
  constructor
  · intro h
    let A := Real.sqrt (1 + a ^ 2)
    let B := Real.sqrt (1 + b ^ 2)
    let C := Real.sqrt (1 + ((b - a) / 2) ^ 2)
    have hA : A ^ 2 = 1 + a ^ 2 := Real.sq_sqrt (by positivity)
    have hB : B ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
    have hC : C ^ 2 = 1 + ((b - a) / 2) ^ 2 := Real.sq_sqrt (by positivity)
    have hAB : A * B = 1 - a * b := by
      change 2 * C = A + B at h
      have hsquare : (2 * C) ^ 2 = (A + B) ^ 2 := congrArg (· ^ 2) h
      nlinarith [hA, hB, hC, hsquare]
    have hABsq : (A * B) ^ 2 = (1 + a ^ 2) * (1 + b ^ 2) := by
      rw [mul_pow, hA, hB]
    rw [hAB] at hABsq
    nlinarith [sq_nonneg (a + b)]
  · intro hab
    have hb : b = -a := by linarith
    subst b
    have harg : 1 + ((-a - a) / 2) ^ 2 = 1 + a ^ 2 := by ring
    rw [harg, neg_sq, two_mul]

/-- Strict one-component graph-speed improvement is equivalent to a moving
center. -/
theorem centered_single_speed_lt_endpoint_speed_sum_iff (a b : ℝ) :
    2 * Real.sqrt (1 + ((b - a) / 2) ^ 2) <
        Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) ↔
      a + b ≠ 0 := by
  have hle :
      2 * Real.sqrt (1 + ((b - a) / 2) ^ 2) ≤
        Real.sqrt (1 + a ^ 2) + Real.sqrt (1 + b ^ 2) := by
    simpa using centered_speed_le_endpoint_speed_sum
      (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
  constructor
  · intro hlt hab
    exact (ne_of_lt hlt)
      ((centered_single_speed_eq_endpoint_speed_sum_iff a b).2 hab)
  · intro hne
    exact lt_of_le_of_ne hle fun heq =>
      hne ((centered_single_speed_eq_endpoint_speed_sum_iff a b).1 heq)

namespace Region

/-- Canonical first component of a nonempty band. -/
def firstComponent (R : Region) (i : Fin R.bandCount) :
    Fin (R.componentCount i) :=
  ⟨0, R.componentCount_pos i⟩

/-- Midpoint of the first component.  Equality rigidity later proves that this
is the only component and that this function is constant on the band. -/
def bandCenter (R : Region) (i : Fin R.bandCount) (y : ℝ) : ℝ :=
  (R.left i (R.firstComponent i) y + R.right i (R.firstComponent i) y) / 2

lemma sum_eq_firstComponent_of_componentCount_eq_one
    (R : Region) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1)
    (f : Fin (R.componentCount i) → ℝ) :
    ∑ j, f j = f (R.firstComponent i) := by
  classical
  apply Finset.sum_eq_single (R.firstComponent i)
  · intro j _hj hne
    exfalso
    apply hne
    apply Fin.ext
    have hj := j.isLt
    dsimp only [firstComponent]
    omega
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

theorem totalWidth_eq_single_of_componentCount_eq_one
    (R : Region) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1) :
    R.totalWidth i =
      fun y => R.right i (R.firstComponent i) y -
        R.left i (R.firstComponent i) y := by
  funext y
  rw [Region.totalWidth,
    R.sum_eq_firstComponent_of_componentCount_eq_one i hsingle]

theorem bandCenter_contDiffOn (R : Region) (i : Fin R.bandCount) :
    ContDiffOn ℝ 1 (R.bandCenter i)
      (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
  exact ((R.left_contDiffOn i (R.firstComponent i)).add
    (R.right_contDiffOn i (R.firstComponent i))).div_const 2

theorem deriv_bandCenter (R : Region) (i : Fin R.bandCount)
    {y : ℝ} (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    deriv (R.bandCenter i) y =
      (deriv (R.left i (R.firstComponent i)) y +
        deriv (R.right i (R.firstComponent i)) y) / 2 := by
  have hl : DifferentiableAt ℝ (R.left i (R.firstComponent i)) y :=
    ((R.left_contDiffOn i (R.firstComponent i)).differentiableOn
      (by norm_num) y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hr : DifferentiableAt ℝ (R.right i (R.firstComponent i)) y :=
    ((R.right_contDiffOn i (R.firstComponent i)).differentiableOn
      (by norm_num) y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
  exact (hl.hasDerivAt.add hr.hasDerivAt).div_const 2 |>.deriv

theorem centeredBandGraphSpeed_lt_of_componentCount_eq_one_of_deriv_bandCenter_ne
    (R : Region) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ))
    (hcenter : deriv (R.bandCenter i) y ≠ 0) :
    R.centeredBandGraphSpeed i y < R.originalBandGraphSpeed i y := by
  have hwidthDiff : DifferentiableAt ℝ (R.totalWidth i) y :=
    ((R.totalWidth_contDiffOn i).differentiableOn (by norm_num) y hy)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hright :
      deriv (fun z => R.totalWidth i z / 2) y =
        deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.div_const 2 |>.deriv
  have hleft :
      deriv (fun z => -R.totalWidth i z / 2) y =
        -deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.neg.div_const 2 |>.deriv
  have hwidth :
      deriv (R.totalWidth i) y =
        deriv (R.right i (R.firstComponent i)) y -
          deriv (R.left i (R.firstComponent i)) y := by
    rw [R.deriv_totalWidth i hy,
      R.sum_eq_firstComponent_of_componentCount_eq_one i hsingle]
  have hsum :
      deriv (R.left i (R.firstComponent i)) y +
          deriv (R.right i (R.firstComponent i)) y ≠ 0 := by
    intro hz
    apply hcenter
    rw [R.deriv_bandCenter i hy]
    linarith
  rw [Region.centeredBandGraphSpeed, Region.originalBandGraphSpeed,
    hright, hleft, hwidth,
    R.sum_eq_firstComponent_of_componentCount_eq_one i hsingle]
  rw [neg_div, neg_sq, ← two_mul]
  exact (centered_single_speed_lt_endpoint_speed_sum_iff _ _).2 hsum

theorem centeredBandGraphSpeed_eq_of_componentCount_eq_one_of_deriv_bandCenter_eq
    (R : Region) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ))
    (hcenter : deriv (R.bandCenter i) y = 0) :
    R.centeredBandGraphSpeed i y = R.originalBandGraphSpeed i y := by
  have hwidthDiff : DifferentiableAt ℝ (R.totalWidth i) y :=
    ((R.totalWidth_contDiffOn i).differentiableOn (by norm_num) y hy)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hright :
      deriv (fun z => R.totalWidth i z / 2) y =
        deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.div_const 2 |>.deriv
  have hleft :
      deriv (fun z => -R.totalWidth i z / 2) y =
        -deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.neg.div_const 2 |>.deriv
  have hwidth :
      deriv (R.totalWidth i) y =
        deriv (R.right i (R.firstComponent i)) y -
          deriv (R.left i (R.firstComponent i)) y := by
    rw [R.deriv_totalWidth i hy,
      R.sum_eq_firstComponent_of_componentCount_eq_one i hsingle]
  have hsum :
      deriv (R.left i (R.firstComponent i)) y +
          deriv (R.right i (R.firstComponent i)) y = 0 := by
    rw [R.deriv_bandCenter i hy] at hcenter
    linarith
  rw [Region.centeredBandGraphSpeed, Region.originalBandGraphSpeed,
    hright, hleft, hwidth,
    R.sum_eq_firstComponent_of_componentCount_eq_one i hsingle]
  rw [neg_div, neg_sq, ← two_mul]
  exact (centered_single_speed_eq_endpoint_speed_sum_iff _ _).2 hsum

theorem centeredBandGraphCost_eq_of_componentCount_eq_one_of_deriv_bandCenter_eq
    (R : Region) (lam : ℝ) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1)
    (hcenter : ∀ y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ),
      deriv (R.bandCenter i) y = 0) :
    R.centeredBandGraphCost lam i = R.originalBandGraphCost lam i := by
  rw [R.centeredBandGraphCost_eq_integrals,
    R.originalBandGraphCost_eq_integrals]
  apply congrArg₂ (· + ·)
  · apply setLIntegral_congr_fun
      (measurableSet_Ioo.inter
        (measurableSet_le measurable_abs measurable_const))
    intro y hy
    change ENNReal.ofReal (R.centeredBandGraphSpeed i y) =
      ENNReal.ofReal (R.originalBandGraphSpeed i y)
    rw [R.centeredBandGraphSpeed_eq_of_componentCount_eq_one_of_deriv_bandCenter_eq
      i hsingle hy.1 (hcenter y hy.1)]
  · apply congrArg (ENNReal.ofReal lam * ·)
    apply setLIntegral_congr_fun
      (measurableSet_Ioo.diff
        (measurableSet_le measurable_abs measurable_const))
    intro y hy
    change ENNReal.ofReal (R.centeredBandGraphSpeed i y) =
      ENNReal.ofReal (R.originalBandGraphSpeed i y)
    rw [R.centeredBandGraphSpeed_eq_of_componentCount_eq_one_of_deriv_bandCenter_eq
      i hsingle hy.1 (hcenter y hy.1)]

theorem continuousOn_deriv_bandCenter (R : Region) (i : Fin R.bandCount) :
    ContinuousOn (deriv (R.bandCenter i))
      (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
  have h := (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo).1
    (R.bandCenter_contDiffOn i)
  exact h.2.2.continuousOn

/-- A nonstationary center at one interior height gives strict integrated graph
improvement.  `C¹` regularity supplies a positive-measure neighborhood; no
pointwise equality is inferred directly from integral equality. -/
theorem centeredBandGraphCost_lt_of_componentCount_eq_one_of_deriv_bandCenter_ne
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1) {y₀ : ℝ}
    (hy₀ : y₀ ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ))
    (hcenter : deriv (R.bandCenter i) y₀ ≠ 0) :
    R.centeredBandGraphCost lam i < R.originalBandGraphCost lam i := by
  let S := Ioo (R.cuts i.castSucc) (R.cuts i.succ)
  let Z : Set ℝ := {y | |y| ≤ 1}
  let S₀ := S ∩ Z
  let S₁ := S \ Z
  let C : ℝ → ENNReal := fun y =>
    ENNReal.ofReal (R.centeredBandGraphSpeed i y)
  let O : ℝ → ENNReal := fun y =>
    ENNReal.ofReal (R.originalBandGraphSpeed i y)
  have hCmeas : Measurable C := by
    dsimp only [C]
    apply ENNReal.measurable_ofReal.comp
    unfold Region.centeredBandGraphSpeed
    fun_prop
  have hOmeas : Measurable O := by
    dsimp only [O]
    apply ENNReal.measurable_ofReal.comp
    unfold Region.originalBandGraphSpeed
    fun_prop
  have hCintegrable : IntegrableOn (R.centeredBandGraphSpeed i) S := by
    dsimp only [S]
    unfold Region.centeredBandGraphSpeed
    exact
      (integrableOn_speed_neg_div_two (R.totalWidth_contDiffOn i)
        (R.totalWidth_speed_integrable i)).add
      (integrableOn_speed_div_two (R.totalWidth_contDiffOn i)
        (R.totalWidth_speed_integrable i))
  have hCfinite : (∫⁻ y in S, C y) ≠ ⊤ :=
    (hCintegrable.setLIntegral_lt_top).ne
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  have hZmeas : MeasurableSet Z :=
    measurableSet_le measurable_abs measurable_const
  have hS₀meas : MeasurableSet S₀ := hSmeas.inter hZmeas
  have hS₁meas : MeasurableSet S₁ := hSmeas.diff hZmeas
  have hderivContinuousAt : ContinuousAt (deriv (R.bandCenter i)) y₀ :=
    (R.continuousOn_deriv_bandCenter i y₀ hy₀).continuousAt
      (isOpen_Ioo.mem_nhds hy₀)
  have hnonzeroNhd : {y | deriv (R.bandCenter i) y ≠ 0} ∈ 𝓝 y₀ := by
    change deriv (R.bandCenter i) ⁻¹' ({0}ᶜ : Set ℝ) ∈ 𝓝 y₀
    exact hderivContinuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds (by simpa using hcenter))
  have hjoint :
      S ∩ {y | deriv (R.bandCenter i) y ≠ 0} ∈ 𝓝 y₀ :=
    inter_mem (isOpen_Ioo.mem_nhds hy₀) hnonzeroNhd
  rcases Metric.mem_nhds_iff.1 hjoint with ⟨ε, hε, hball⟩
  let J := Ioo (y₀ - ε / 2) (y₀ + ε / 2)
  have hJsub :
      J ⊆ S ∩ {y | deriv (R.bandCenter i) y ≠ 0} := by
    intro y hy
    apply hball
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hJmeas : MeasurableSet J := measurableSet_Ioo
  have hJmeasure :
      (volume.restrict S) J ≠ 0 := by
    rw [Measure.restrict_apply hJmeas,
      inter_eq_left.mpr (fun y hy => (hJsub hy).1)]
    exact ne_of_gt ((Measure.measure_Ioo_pos volume).2 (by linarith))
  have hstrictWhole : (∫⁻ y in S, C y) < ∫⁻ y in S, O y := by
    apply lintegral_strict_mono_of_ae_le_of_ae_lt_on
      hOmeas.aemeasurable hCfinite
    · filter_upwards [ae_restrict_mem hSmeas] with y hy
      exact ENNReal.ofReal_le_ofReal
        (R.centeredBandGraphSpeed_le_originalBandGraphSpeed i hy)
    · exact hJmeasure
    · filter_upwards with y
      intro hyJ
      have hy := hJsub hyJ
      have hlt :=
        R.centeredBandGraphSpeed_lt_of_componentCount_eq_one_of_deriv_bandCenter_ne
          i hsingle hy.1 hy.2
      exact (ENNReal.ofReal_lt_ofReal_iff
        (lt_of_le_of_lt (by
          unfold Region.centeredBandGraphSpeed
          positivity) hlt)).2 hlt
  have hdisjoint : Disjoint S₀ S₁ := by
    rw [Set.disjoint_left]
    intro y hy₀ hy₁
    exact hy₁.2 hy₀.2
  have hunion : S₀ ∪ S₁ = S := by
    ext y
    simp only [S₀, S₁, mem_union, mem_inter_iff, Set.mem_sdiff, Z, S]
    tauto
  have hpartition (f : ℝ → ENNReal) :
      (∫⁻ y in S, f y) = (∫⁻ y in S₀, f y) + ∫⁻ y in S₁, f y := by
    rw [← lintegral_union hS₁meas hdisjoint, hunion]
  have hstrictSplit :
      (∫⁻ y in S₀, C y) + (∫⁻ y in S₁, C y) <
        (∫⁻ y in S₀, O y) + ∫⁻ y in S₁, O y := by
    rw [← hpartition C, ← hpartition O]
    exact hstrictWhole
  have hC₁O₁ : (∫⁻ y in S₁, C y) ≤ ∫⁻ y in S₁, O y := by
    apply setLIntegral_mono' hS₁meas
    intro y hy
    exact ENNReal.ofReal_le_ofReal
      (R.centeredBandGraphSpeed_le_originalBandGraphSpeed i hy.1)
  have ha : (1 : ENNReal) ≤ ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hlam
  have hadecomp :
      ENNReal.ofReal lam = 1 + (ENNReal.ofReal lam - 1) :=
    (add_tsub_cancel_of_le ha).symm
  rw [R.centeredBandGraphCost_eq_integrals,
    R.originalBandGraphCost_eq_integrals]
  change (∫⁻ y in S₀, C y) + ENNReal.ofReal lam * (∫⁻ y in S₁, C y) <
    (∫⁻ y in S₀, O y) + ENNReal.ofReal lam * ∫⁻ y in S₁, O y
  rw [hadecomp, add_mul, one_mul, add_mul, one_mul]
  calc
    (∫⁻ y in S₀, C y) +
          ((∫⁻ y in S₁, C y) +
            (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, C y) =
        ((∫⁻ y in S₀, C y) + ∫⁻ y in S₁, C y) +
          (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, C y := by ac_rfl
    _ < ((∫⁻ y in S₀, O y) + ∫⁻ y in S₁, O y) +
          (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, O y := by
      apply ENNReal.add_lt_add_of_lt_of_le
      · apply ENNReal.mul_ne_top
        · exact ENNReal.sub_ne_top ENNReal.ofReal_ne_top
        · exact (hCintegrable.mono_set Set.sdiff_subset).setLIntegral_lt_top.ne
      · exact hstrictSplit
      · exact mul_le_mul_right hC₁O₁ _
    _ = (∫⁻ y in S₀, O y) +
          ((∫⁻ y in S₁, O y) +
            (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, O y) := by ac_rfl

theorem weightedTraceCost_centeredGraphTrace_lt_of_bandGraphCost_lt
    (R : Region) (lam : ℝ) (i : Fin R.bandCount)
    (hband : R.centeredBandGraphCost lam i <
      R.originalBandGraphCost lam i) :
    weightedTraceCost lam R.centeredGraphTrace <
      weightedTraceCost lam R.graphTrace := by
  rw [R.weightedTraceCost_centeredGraphTrace,
    R.weightedTraceCost_graphTrace,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  have hrestLe :
      (∑ k ∈ Finset.univ.erase i, R.centeredBandGraphCost lam k) ≤
        ∑ k ∈ Finset.univ.erase i, R.originalBandGraphCost lam k := by
    apply Finset.sum_le_sum
    intro k _hk
    exact R.centeredBandGraphCost_le_originalBandGraphCost lam k
  have hrestFinite :
      (∑ k ∈ Finset.univ.erase i, R.centeredBandGraphCost lam k) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro k _hk
    unfold Region.centeredBandGraphCost
    exact ENNReal.sum_ne_top.mpr fun side _ =>
      R.indexedCenteredGraphSpeedCost_ne_top lam (k, side)
  calc
    (∑ k, R.centeredBandGraphCost lam k) =
        (∑ k ∈ Finset.univ.erase i, R.centeredBandGraphCost lam k) +
          R.centeredBandGraphCost lam i :=
      (Finset.sum_erase_add Finset.univ
        (fun k => R.centeredBandGraphCost lam k) (Finset.mem_univ i)).symm
    _ < (∑ k ∈ Finset.univ.erase i, R.originalBandGraphCost lam k) +
          R.originalBandGraphCost lam i :=
      ENNReal.add_lt_add_of_le_of_lt hrestFinite hrestLe hband
    _ = ∑ k, R.originalBandGraphCost lam k :=
      Finset.sum_erase_add Finset.univ
        (fun k => R.originalBandGraphCost lam k) (Finset.mem_univ i)

theorem weightedTraceCost_completeCenteredFrontierTrace_lt_of_bandGraphCost_lt
    (R : Region) (lam : ℝ) (i : Fin R.bandCount)
    (hband : R.centeredBandGraphCost lam i <
      R.originalBandGraphCost lam i) :
    weightedTraceCost lam R.completeCenteredFrontierTrace <
      weightedTraceCost lam R.completeFrontierTrace := by
  have hhorizontalFinite :
      weightedTraceCost lam R.centeredHorizontalFrontierTrace ≠ ⊤ := by
    have hcomplete :=
      R.weightedTraceCost_completeCenteredFrontierTrace_ne_top lam
    rw [R.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal]
      at hcomplete
    exact (ENNReal.add_ne_top.mp hcomplete).2
  rw [R.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal,
    R.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal]
  exact ENNReal.add_lt_add_of_lt_of_le hhorizontalFinite
    (R.weightedTraceCost_centeredGraphTrace_lt_of_bandGraphCost_lt lam i hband)
    (R.weightedTraceCost_centeredHorizontalFrontierTrace_le lam)

/-- Any equality case of the complete literal rearrangement has exactly one
component in every open band. -/
theorem componentCount_eq_one_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier)) :
    ∀ i, R.componentCount i = 1 := by
  intro i
  have hle : R.componentCount i ≤ 1 := by
    by_contra hnot
    have hmulti : 1 < R.componentCount i := by omega
    have hlt := R.weightedTraceCost_frontier_centeredCarrier_lt hlam i hmulti
    exact (ne_of_lt hlt) heq
  exact Nat.le_antisymm hle (R.componentCount_pos i)


/-- Equality of the two literal frontier costs forces zero center derivative at
every interior height of every band. -/
theorem deriv_bandCenter_eq_zero_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    deriv (R.bandCenter i) y = 0 := by
  have hsingle := R.componentCount_eq_one_of_frontier_cost_eq hlam heq i
  by_contra hne
  have hband :=
    R.centeredBandGraphCost_lt_of_componentCount_eq_one_of_deriv_bandCenter_ne
      hlam i hsingle hy hne
  have hlt :=
    R.weightedTraceCost_completeCenteredFrontierTrace_lt_of_bandGraphCost_lt
      lam i hband
  rw [← R.weightedTraceCost_frontier_centeredCarrier,
    ← R.weightedTraceCost_frontier_carrier] at hlt
  exact (ne_of_lt hlt) heq

theorem weightedTraceCost_centeredGraphTrace_eq_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier)) :
    weightedTraceCost lam R.centeredGraphTrace =
      weightedTraceCost lam R.graphTrace := by
  rw [R.weightedTraceCost_centeredGraphTrace,
    R.weightedTraceCost_graphTrace,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact
    R.centeredBandGraphCost_eq_of_componentCount_eq_one_of_deriv_bandCenter_eq
      lam i (R.componentCount_eq_one_of_frontier_cost_eq hlam heq i)
      (fun y hy =>
        R.deriv_bandCenter_eq_zero_of_frontier_cost_eq hlam heq i hy)

theorem weightedTraceCost_centeredHorizontalFrontierTrace_eq_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier)) :
    weightedTraceCost lam R.centeredHorizontalFrontierTrace =
      weightedTraceCost lam R.horizontalFrontierTrace := by
  have hcomplete : weightedTraceCost lam R.completeCenteredFrontierTrace =
      weightedTraceCost lam R.completeFrontierTrace := by
    rw [← R.weightedTraceCost_frontier_centeredCarrier,
      ← R.weightedTraceCost_frontier_carrier]
    exact heq
  rw [R.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal,
    R.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal,
    R.weightedTraceCost_centeredGraphTrace_eq_of_frontier_cost_eq hlam heq]
      at hcomplete
  have hgraphFinite : weightedTraceCost lam R.graphTrace ≠ ⊤ := by
    have hfinite := R.weightedTraceCost_completeFrontierTrace_ne_top lam
    rw [R.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal]
      at hfinite
    exact (ENNReal.add_ne_top.mp hfinite).1
  exact (ENNReal.add_left_inj hgraphFinite).mp
    (by simpa only [add_comm] using hcomplete)

def originalSeamCost (R : Region) (lam : ℝ)
    (i : Fin (R.bandCount - 1)) : ENNReal :=
  ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
    volume
      (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.fiber (R.seamUpperBand i) (R.seamHeight i))

def centeredSeamCost (R : Region) (lam : ℝ)
    (i : Fin (R.bandCount - 1)) : ENNReal :=
  ENNReal.ofReal (StripDensity lam (0, R.seamHeight i)) *
    volume
      (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.centeredFiber (R.seamUpperBand i) (R.seamHeight i))

theorem centeredSeamCost_le_originalSeamCost
    (R : Region) (lam : ℝ) (i : Fin (R.bandCount - 1)) :
    R.centeredSeamCost lam i ≤ R.originalSeamCost lam i := by
  exact mul_le_mul_right (R.volume_centeredSeamSymmDiff_le i) _

theorem centeredSeamCost_ne_top
    (R : Region) (lam : ℝ) (i : Fin (R.bandCount - 1)) :
    R.centeredSeamCost lam i ≠ ⊤ := by
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (R.volume_centeredSeamSymmDiffFiber_ne_top i)

lemma finset_sum_component_eq_of_le_of_sum_eq
    {ι : Type*} [Fintype ι] (f g : ι → ENNReal)
    (hfinite : ∀ i, f i ≠ ⊤)
    (hle : ∀ i, f i ≤ g i)
    (hsum : ∑ i, f i = ∑ i, g i) :
    ∀ i, f i = g i := by
  intro i
  classical
  by_contra hne
  have hlt : f i < g i := lt_of_le_of_ne (hle i) hne
  have hrestLe :
      (∑ k ∈ Finset.univ.erase i, f k) ≤
        ∑ k ∈ Finset.univ.erase i, g k := by
    apply Finset.sum_le_sum
    intro k _hk
    exact hle k
  have hrestFinite :
      (∑ k ∈ Finset.univ.erase i, f k) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _hk => hfinite k
  have hsumlt : (∑ k, f k) < ∑ k, g k := by
    calc
      (∑ k, f k) =
          (∑ k ∈ Finset.univ.erase i, f k) + f i :=
        (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
      _ < (∑ k ∈ Finset.univ.erase i, g k) + g i :=
        ENNReal.add_lt_add_of_le_of_lt hrestFinite hrestLe hlt
      _ = ∑ k, g k :=
        Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
  exact (ne_of_lt hsumlt) hsum

theorem sum_centeredSeamCost_eq_sum_originalSeamCost_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier)) :
    (∑ i, R.centeredSeamCost lam i) =
      ∑ i, R.originalSeamCost lam i := by
  have hhorizontal :=
    R.weightedTraceCost_centeredHorizontalFrontierTrace_eq_of_frontier_cost_eq
      hlam heq
  rw [R.weightedTraceCost_centeredHorizontalFrontierTrace,
    R.weightedTraceCost_horizontalFrontierTrace,
    R.volume_centeredLowerOuterFiber_eq,
    R.volume_centeredUpperOuterFiber_eq] at hhorizontal
  let outer : ENNReal :=
    ENNReal.ofReal
        (StripDensity lam (0, R.cuts R.firstBand.castSucc)) *
      volume (R.fiber R.firstBand (R.cuts R.firstBand.castSucc)) +
    ENNReal.ofReal
        (StripDensity lam (0, R.cuts R.lastBand.succ)) *
      volume (R.fiber R.lastBand (R.cuts R.lastBand.succ))
  change outer + (∑ i, R.centeredSeamCost lam i) =
    outer + ∑ i, R.originalSeamCost lam i at hhorizontal
  have houterFinite : outer ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        R.volume_lowerOuterFiber_ne_top
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        R.volume_upperOuterFiber_ne_top
  exact (ENNReal.add_left_inj houterFinite).mp
    (by simpa only [add_comm] using hhorizontal)

theorem centeredSeamCost_eq_originalSeamCost_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin (R.bandCount - 1)) :
    R.centeredSeamCost lam i = R.originalSeamCost lam i := by
  exact finset_sum_component_eq_of_le_of_sum_eq
    (R.centeredSeamCost lam) (R.originalSeamCost lam)
    (R.centeredSeamCost_ne_top lam)
    (R.centeredSeamCost_le_originalSeamCost lam)
    (R.sum_centeredSeamCost_eq_sum_originalSeamCost_of_frontier_cost_eq hlam heq)
    i

/-- Matching one-sided widths at an equality-case seam force the original
symmetric-difference seam to have zero one-dimensional measure. -/
theorem volume_seamSymmDiff_eq_zero_of_frontier_cost_eq_of_width_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin (R.bandCount - 1))
    (hwidth :
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i)) :
    volume
      (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
        R.fiber (R.seamUpperBand i) (R.seamHeight i)) = 0 := by
  have hcenteredVolume :
      volume
        (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) = 0 := by
    rw [R.volume_centeredSeamSymmDiff_eq_abs_totalWidth, hwidth, sub_self,
      abs_zero, ENNReal.ofReal_zero]
  have hcost :=
    R.centeredSeamCost_eq_originalSeamCost_of_frontier_cost_eq hlam heq i
  rw [Region.centeredSeamCost, Region.originalSeamCost, hcenteredVolume,
    mul_zero] at hcost
  have hdensity :
      0 < StripDensity lam (0, R.seamHeight i) := by
    unfold StripDensity
    split_ifs <;> linarith
  exact (mul_eq_zero.mp hcost.symm).resolve_left
    (ENNReal.ofReal_pos.mpr hdensity).ne'

lemma center_eq_of_equal_positive_width_interval_symmDiff_zero
    {c d w : ℝ} (hw : 0 < w)
    (hzero :
      volume
        (Icc (c - w / 2) (c + w / 2) ∆
          Icc (d - w / 2) (d + w / 2)) = 0) :
    c = d := by
  have hnonzero_of_lt :
      ∀ {u v : ℝ}, u < v →
        volume
          (Icc (u - w / 2) (u + w / 2) ∆
            Icc (v - w / 2) (v + w / 2)) ≠ 0 := by
    intro u v huv
    let a := u - w / 2
    let b := min (u + w / 2) (v - w / 2)
    have hab : a < b := by
      dsimp only [a, b]
      rw [lt_min_iff]
      constructor <;> linarith
    have hsub :
        Ioo a b ⊆
          Icc (u - w / 2) (u + w / 2) ∆
            Icc (v - w / 2) (v + w / 2) := by
      intro x hx
      left
      constructor
      · constructor
        · exact hx.1.le
        · exact (hx.2.trans_le (min_le_left _ _)).le
      · intro hxv
        linarith [hx.2, min_le_right (u + w / 2) (v - w / 2), hxv.1]
    intro hmeasure
    have hIooZero := measure_mono_null hsub hmeasure
    exact (ne_of_gt ((Measure.measure_Ioo_pos volume).2 hab)) hIooZero
  rcases lt_trichotomy c d with hcd | hcd | hdc
  · exact False.elim ((hnonzero_of_lt hcd) hzero)
  · exact hcd
  · have hzero' :
        volume
          (Icc (d - w / 2) (d + w / 2) ∆
            Icc (c - w / 2) (c + w / 2)) = 0 := by
      simpa only [symmDiff_comm] using hzero
    exact False.elim ((hnonzero_of_lt hdc) hzero')

theorem fiber_eq_firstComponent_of_componentCount_eq_one
    (R : Region) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1) (y : ℝ) :
    R.fiber i y =
      Icc (R.left i (R.firstComponent i) y)
        (R.right i (R.firstComponent i) y) := by
  ext x
  constructor
  · intro hx
    rw [Region.fiber, mem_iUnion] at hx
    rcases hx with ⟨j, hx⟩
    have hj : j = R.firstComponent i := by
      apply Fin.ext
      have hjlt := j.isLt
      dsimp only [firstComponent]
      omega
    simpa only [hj] using hx
  · intro hx
    rw [Region.fiber, mem_iUnion]
    exact ⟨R.firstComponent i, hx⟩

theorem fiber_eq_Icc_bandCenter_totalWidth_of_componentCount_eq_one
    (R : Region) (i : Fin R.bandCount)
    (hsingle : R.componentCount i = 1) (y : ℝ) :
    R.fiber i y =
      Icc (R.bandCenter i y - R.totalWidth i y / 2)
        (R.bandCenter i y + R.totalWidth i y / 2) := by
  rw [R.fiber_eq_firstComponent_of_componentCount_eq_one i hsingle,
    R.totalWidth_eq_single_of_componentCount_eq_one i hsingle]
  unfold bandCenter
  ext x
  simp only [mem_Icc]
  constructor
  · intro hx
    constructor <;> linarith [hx.1, hx.2]
  · intro hx
    constructor <;> linarith [hx.1, hx.2]

/-- With positive matching one-sided width, the zero seam deficit forced by
cost equality identifies the two endpoint-extended band centers. -/
theorem bandCenter_seamLower_eq_seamUpper_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin (R.bandCount - 1))
    (hwidth :
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i)) :
    R.bandCenter (R.seamLowerBand i) (R.seamHeight i) =
      R.bandCenter (R.seamUpperBand i) (R.seamHeight i) := by
  have hsingleLower :=
    R.componentCount_eq_one_of_frontier_cost_eq hlam heq (R.seamLowerBand i)
  have hsingleUpper :=
    R.componentCount_eq_one_of_frontier_cost_eq hlam heq (R.seamUpperBand i)
  have hzero :=
    R.volume_seamSymmDiff_eq_zero_of_frontier_cost_eq_of_width_eq
      hlam heq i hwidth
  rw [R.fiber_eq_Icc_bandCenter_totalWidth_of_componentCount_eq_one
      (R.seamLowerBand i) hsingleLower,
    R.fiber_eq_Icc_bandCenter_totalWidth_of_componentCount_eq_one
      (R.seamUpperBand i) hsingleUpper, ← hwidth] at hzero
  exact center_eq_of_equal_positive_width_interval_symmDiff_zero hpos hzero

/-- The center selected by each equality-case band is constant through its
closed endpoints.  Only interior `C¹` regularity is used for the derivative
argument; global endpoint continuity performs the closure step. -/
theorem exists_bandCenter_eq_on_Icc_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin R.bandCount) :
    ∃ c : ℝ, ∀ y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ),
      R.bandCenter i y = c := by
  let S := Ioo (R.cuts i.castSucc) (R.cuts i.succ)
  have hab : R.cuts i.castSucc < R.cuts i.succ :=
    R.cuts_strict Fin.castSucc_lt_succ
  have hdiff : DifferentiableOn ℝ (R.bandCenter i) S :=
    (R.bandCenter_contDiffOn i).differentiableOn (by norm_num)
  have hzero : S.EqOn (deriv (R.bandCenter i)) 0 := by
    intro y hy
    exact R.deriv_bandCenter_eq_zero_of_frontier_cost_eq hlam heq i hy
  obtain ⟨c, hc⟩ :=
    isOpen_Ioo.exists_is_const_of_deriv_eq_zero
      isPreconnected_Ioo hdiff hzero
  have hcontinuous : Continuous (R.bandCenter i) :=
    ((R.left_continuous i (R.firstComponent i)).add
      (R.right_continuous i (R.firstComponent i))).div_const 2
  have hcEq : S.EqOn (R.bandCenter i) (fun _ => c) := hc
  have hclosed := Set.EqOn.closure hcEq hcontinuous continuous_const
  rw [show closure S = Icc (R.cuts i.castSucc) (R.cuts i.succ) by
    exact closure_Ioo hab.ne] at hclosed
  exact ⟨c, hclosed⟩

def bandAxis (R : Region) (i : Fin R.bandCount) : ℝ :=
  R.bandCenter i (R.cuts i.castSucc)

theorem bandCenter_eq_bandAxis_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    R.bandCenter i y = R.bandAxis i := by
  rcases R.exists_bandCenter_eq_on_Icc_of_frontier_cost_eq hlam heq i with
    ⟨c, hc⟩
  exact (hc y hy).trans
    (hc (R.cuts i.castSucc)
      ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩).symm

theorem bandAxis_seamLower_eq_seamUpper_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (i : Fin (R.bandCount - 1))
    (hwidth :
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i)) :
    R.bandAxis (R.seamLowerBand i) =
      R.bandAxis (R.seamUpperBand i) := by
  calc
    R.bandAxis (R.seamLowerBand i) =
        R.bandCenter (R.seamLowerBand i) (R.seamHeight i) := by
      symm
      apply R.bandCenter_eq_bandAxis_of_frontier_cost_eq hlam heq
      rw [R.cuts_seamLower_succ i]
      exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
    _ = R.bandCenter (R.seamUpperBand i) (R.seamHeight i) :=
      R.bandCenter_seamLower_eq_seamUpper_of_frontier_cost_eq
        hlam heq i hwidth hpos
    _ = R.bandAxis (R.seamUpperBand i) := by
      apply R.bandCenter_eq_bandAxis_of_frontier_cost_eq hlam heq
      exact ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩

lemma fin_value_eq_first_of_eq_succ {n : ℕ} (hn : 0 < n)
    (c : Fin n → ℝ)
    (hadj : ∀ i : Fin n, ∀ hi : i.val + 1 < n,
      c i = c ⟨i.val + 1, hi⟩) :
    ∀ i, c i = c ⟨0, hn⟩ := by
  have H : ∀ m : ℕ, ∀ hm : m < n, c ⟨m, hm⟩ = c ⟨0, hn⟩ := by
    intro m
    induction m with
    | zero =>
        intro hm
        rfl
    | succ m ih =>
        intro hm
        have hm' : m < n := by omega
        have hstep := hadj ⟨m, hm'⟩ (by omega)
        exact (by
          simpa only [Nat.succ_eq_add_one] using hstep.symm.trans (ih hm'))
  intro i
  exact H i.val i.isLt

/-- Positive matching seam widths turn the per-band equality centers into one
global horizontal axis. -/
theorem exists_globalAxis_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (hwidth : ∀ i : Fin (R.bandCount - 1),
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : ∀ i : Fin (R.bandCount - 1), 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i)) :
    ∃ axis : ℝ, ∀ i : Fin R.bandCount, ∀ y,
      y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) →
        R.bandCenter i y = axis := by
  let axis := R.bandAxis R.firstBand
  have hadj : ∀ i : Fin R.bandCount, ∀ hi : i.val + 1 < R.bandCount,
      R.bandAxis i = R.bandAxis ⟨i.val + 1, hi⟩ := by
    intro i hi
    let k : Fin (R.bandCount - 1) := ⟨i.val, by omega⟩
    have hk := R.bandAxis_seamLower_eq_seamUpper_of_frontier_cost_eq
      hlam heq k (hwidth k) (hpos k)
    have hlower : R.seamLowerBand k = i := Fin.ext rfl
    have hupper : R.seamUpperBand k = ⟨i.val + 1, hi⟩ := Fin.ext rfl
    simpa only [hlower, hupper] using hk
  have haxes : ∀ i : Fin R.bandCount, R.bandAxis i = axis := by
    intro i
    exact fin_value_eq_first_of_eq_succ R.bandCount_pos (R.bandAxis) hadj i
  refine ⟨axis, ?_⟩
  intro i y hy
  exact (R.bandCenter_eq_bandAxis_of_frontier_cost_eq hlam heq i hy).trans
    (haxes i)

theorem hasCenteredHorizontalIntervalSections_carrier
    (R : Region) (axis : ℝ)
    (hsingle : ∀ i, R.componentCount i = 1)
    (haxis : ∀ i : Fin R.bandCount, ∀ y,
      y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) →
        R.bandCenter i y = axis) :
    CMVSourceClassification.HasCenteredHorizontalIntervalSections
      axis R.carrier := by
  have hcutsZero : volume (Set.range R.cuts) = 0 :=
    (Set.finite_range R.cuts).measure_zero volume
  have hcutsAE : ∀ᵐ y : ℝ ∂volume, y ∉ Set.range R.cuts := by
    rw [ae_iff]
    simpa only [Set.ofPred_mem_eq, not_not] using hcutsZero
  filter_upwards [hcutsAE] with y hyCuts
  by_cases hactive :
      ∃ i : Fin R.bandCount,
        y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)
  · rcases hactive with ⟨i, hy⟩
    have hyOpen : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) := by
      refine ⟨lt_of_le_of_ne hy.1 ?_, lt_of_le_of_ne hy.2 ?_⟩
      · intro heq
        exact hyCuts ⟨i.castSucc, heq⟩
      · intro heq
        exact hyCuts ⟨i.succ, heq.symm⟩
    refine ⟨R.totalWidth i y,
      R.totalWidth_nonneg_of_mem_Icc i hy, ?_⟩
    apply Filter.EventuallyEq.of_eq
    change CMVRelaxation.horizontalSection R.carrier y =
      Icc (axis - R.totalWidth i y / 2) (axis + R.totalWidth i y / 2)
    rw [R.horizontalSection_carrier_of_mem_Ioo i hyOpen,
      R.fiber_eq_Icc_bandCenter_totalWidth_of_componentCount_eq_one
        i (hsingle i) y,
      haxis i y hy]
  · refine ⟨0, le_rfl, ?_⟩
    have hsection : horizontalSection R.carrier y = ∅ := by
      rw [R.horizontalSection_carrier]
      ext x
      simp only [mem_iUnion, mem_empty_iff_false, iff_false]
      rintro ⟨i, hx⟩
      have hnot :
          y ∉ Icc (R.cuts i.castSucc) (R.cuts i.succ) := by
        intro hy
        exact hactive ⟨i, hy⟩
      simp only [hnot, if_false, Set.mem_empty_iff_false] at hx
    change CMVRelaxation.horizontalSection R.carrier y =ᵐ[volume]
      Icc (axis - 0 / 2) (axis + 0 / 2)
    rw [hsection]
    simp only [zero_div, sub_zero, add_zero, Set.Icc_self]
    exact (ae_eq_empty.mpr (measure_singleton axis)).symm

theorem hasAEIntervalHorizontalSections_of_centered
    {E : Set PlanePoint} {axis : ℝ}
    (hcentered :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E) :
    HasAEIntervalHorizontalSections E := by
  filter_upwards [hcentered] with y hy
  rcases hy with ⟨length, hlength, hsection⟩
  exact ⟨Icc (axis - length / 2) (axis + length / 2),
    Set.ordConnected_Icc, hsection⟩

theorem hasCenteredHorizontalIntervalSections_of_ae_eq
    {E F : Set PlanePoint} {axis : ℝ}
    (hEF : E =ᵐ[volume] F)
    (hcentered :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections axis F) :
    CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E := by
  have hsections := ae_horizontalSection_congr_ae hEF
  filter_upwards [hsections, hcentered] with y hEFy hFy
  rcases hFy with ⟨length, hlength, hF⟩
  exact ⟨length, hlength, hEFy.trans hF⟩

/-- Conditional equality-rigidity export for a source carrier.  The `Region`
input retains the finite-band representation, globally continuous endpoint
representatives, interior `C¹` graph regularity, finite speed integrals, and
strictly positive interior component widths.  The remaining hypotheses retain
literal frontier-cost equality, positive matching one-sided widths at every
internal cut, and planar almost-everywhere source agreement explicitly. -/
theorem source_section_interfaces_of_frontier_cost_eq
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam)
    (heq : weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier))
    (hwidth : ∀ i : Fin (R.bandCount - 1),
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : ∀ i : Fin (R.bandCount - 1), 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i))
    {E : Set PlanePoint} (hE : E =ᵐ[volume] R.carrier) :
    ∃ axis : ℝ,
      HasAEIntervalHorizontalSections E ∧
        CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E := by
  rcases R.exists_globalAxis_of_frontier_cost_eq
    hlam heq hwidth hpos with ⟨axis, haxis⟩
  have hsingle := R.componentCount_eq_one_of_frontier_cost_eq hlam heq
  have hcarrier :=
    R.hasCenteredHorizontalIntervalSections_carrier axis hsingle haxis
  have hsource :=
    hasCenteredHorizontalIntervalSections_of_ae_eq hE hcarrier
  exact ⟨axis, hasAEIntervalHorizontalSections_of_centered hsource, hsource⟩

/-- A finite projection exhaustion is enough to lower-bound the cost of every
smooth sequence converging to the original finite-band carrier.  The geometric
work remains entirely in `hexhaust`: each family must have disjoint windows, a
finite total defect coefficient, and payoff approaching the literal complete
frontier cost.  This theorem only performs the one-charge liminf passage. -/
theorem weightedTraceCost_frontier_carrier_le_smoothSequence_cost_of_projection_exhaustion
    (R : Region) {lam : ℝ}
    (hexhaust : ∀ {eta : ℝ}, 0 < eta →
      ∃ N : ℕ, ∃ P : Fin N → RigidProjectionPatch lam R.carrier,
        Set.Pairwise (Set.univ : Set (Fin N))
          (Function.onFun Disjoint fun i => (P i).window) ∧
        (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
        weightedTraceCost lam (frontier R.carrier) ≤
          (∑ i, (P i).payoff) + ENNReal.ofReal eta)
    (A : SmoothSequence) (hconv : A.ConvergesTo R.carrier) :
    weightedTraceCost lam (frontier R.carrier) ≤ A.cost lam := by
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  have heta : 0 < (epsilon : ℝ) := NNReal.coe_pos.2 hepsilon
  obtain ⟨N, P, hpair, herror, hpayoff⟩ := hexhaust heta
  have hpair' : Set.Pairwise (↑(Finset.univ : Finset (Fin N)))
      (Function.onFun Disjoint fun i => (P i).window) := by
    simpa only [Finset.coe_univ] using hpair
  have hpoint : ∀ n,
      weightedTraceCost lam (frontier R.carrier) ≤
        smoothCost lam (A.carrier n) +
          (∑ i, (P i).errorCoefficient) *
            characteristicDistance (A.carrier n) R.carrier +
          ENNReal.ofReal (epsilon : ℝ) := by
    intro n
    have hsum :=
      RigidProjectionPatch.finset_sum_payoff_le_smoothCost_add_error
        (Finset.univ : Finset (Fin N)) P hpair'
        R.isClosed_carrier.measurableSet (A.smooth n).isOpen
    calc
      weightedTraceCost lam (frontier R.carrier) ≤
          (∑ i, (P i).payoff) + ENNReal.ofReal (epsilon : ℝ) :=
        hpayoff
      _ ≤ (smoothCost lam (A.carrier n) +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance (A.carrier n) R.carrier) +
            ENNReal.ofReal (epsilon : ℝ) := by
        apply add_le_add _ le_rfl
        simpa using hsum
  have hcost := A.cost_add_ge_of_pointwise_add_distance R.carrier
    (weightedTraceCost lam (frontier R.carrier))
    (∑ i, (P i).errorCoefficient) (ENNReal.ofReal (epsilon : ℝ))
    hconv herror hpoint
  simpa only [ENNReal.ofReal_coe_nnreal] using hcost

/-- The projection-exhaustion interface implies the actual extended relaxed
lower bound.  No finite-cost or near-minimizer sequence is selected: the
sequence-level result is applied directly to every member of the defining
`sInf`. -/
theorem weightedTraceCost_frontier_carrier_le_relaxedPerimeter_of_projection_exhaustion
    (R : Region) {lam : ℝ}
    (hexhaust : ∀ {eta : ℝ}, 0 < eta →
      ∃ N : ℕ, ∃ P : Fin N → RigidProjectionPatch lam R.carrier,
        Set.Pairwise (Set.univ : Set (Fin N))
          (Function.onFun Disjoint fun i => (P i).window) ∧
        (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
        weightedTraceCost lam (frontier R.carrier) ≤
          (∑ i, (P i).payoff) + ENNReal.ofReal eta) :
    weightedTraceCost lam (frontier R.carrier) ≤
      relaxedPerimeter lam R.carrier := by
  unfold relaxedPerimeter
  apply le_sInf
  intro c hc
  rcases hc with ⟨A, _, hconv, rfl⟩
  exact
    R.weightedTraceCost_frontier_carrier_le_smoothSequence_cost_of_projection_exhaustion
      hexhaust A hconv

/-- A concrete centered recovery sequence supplies the recovery-type upper
bound required by the minimality sandwich. -/
theorem relaxedPerimeter_centeredCarrier_le_of_recovery
    (R : Region) {lam : ℝ} (A : SmoothSequence)
    (hconv : A.ConvergesTo R.centeredCarrier)
    (hcost : A.cost lam ≤
      weightedTraceCost lam (frontier R.centeredCarrier)) :
    relaxedPerimeter lam R.centeredCarrier ≤
      weightedTraceCost lam (frontier R.centeredCarrier) := by
  apply le_trans _ hcost
  unfold relaxedPerimeter
  apply sInf_le
  exact ⟨A, R.isClosed_centeredCarrier.measurableSet.nullMeasurableSet,
    hconv, rfl⟩


/-- Source minimality and the two source/frontier directions force equality of
the two literal frontier costs.  The original carrier needs the projection-type
lower bound, while the centered competitor needs the recovery-type upper bound.
Finite-band boundedness and the retained finite centered frontier cost construct
the centered source-admissibility witness internally.  No equality between
relaxed perimeter and topological-frontier cost is assumed. -/
theorem frontier_cost_eq_of_minimizer_and_bounds
    (R : Region) {lam : ℝ}
    (hmin : (relaxedSourceSemantics lam).IsMinimizer R.carrier)
    (horiginalLower :
      weightedTraceCost lam (frontier R.carrier) ≤
        relaxedPerimeter lam R.carrier)
    (hcenteredUpper :
      relaxedPerimeter lam R.centeredCarrier ≤
        weightedTraceCost lam (frontier R.centeredCarrier)) :
    weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier) := by
  have hcenteredFinite :
      (relaxedSourceSemantics lam).IsFinitePerimeter R.centeredCarrier := by
    refine ⟨R.isClosed_centeredCarrier.measurableSet.nullMeasurableSet, ?_⟩
    exact hcenteredUpper.trans_lt
      (lt_top_iff_ne_top.mpr
        (R.weightedTraceCost_frontier_centeredCarrier_ne_top lam))
  have hcenteredAdmissible :
      (relaxedSourceSemantics lam).IsAdmissible R.centeredCarrier :=
    ⟨hcenteredFinite, R.integrableOn_centeredCarrier lam⟩
  have hsourceLeReal :=
    hmin.2 R.centeredCarrier hcenteredAdmissible
      (weightedArea_carrier_eq_centeredCarrier R lam).symm
  have hsourceLe :
      relaxedPerimeter lam R.carrier ≤
        relaxedPerimeter lam R.centeredCarrier :=
    (relaxedSourceSemantics_perimeter_le_iff
      hmin.1.1 hcenteredFinite).1 hsourceLeReal
  have horiginalLeCentered :
      weightedTraceCost lam (frontier R.carrier) ≤
        weightedTraceCost lam (frontier R.centeredCarrier) :=
    horiginalLower.trans (hsourceLe.trans hcenteredUpper)
  exact le_antisymm
    (R.weightedTraceCost_frontier_centeredCarrier_le lam)
    horiginalLeCentered
/-- Projection exhaustion of the original carrier and one concrete recovery of
the centered carrier discharge both source/frontier directions in the
minimality sandwich. -/
theorem frontier_cost_eq_of_minimizer_and_projection_exhaustion_and_recovery
    (R : Region) {lam : ℝ}
    (hmin : (relaxedSourceSemantics lam).IsMinimizer R.carrier)
    (hexhaust : ∀ {eta : ℝ}, 0 < eta →
      ∃ N : ℕ, ∃ P : Fin N → RigidProjectionPatch lam R.carrier,
        Set.Pairwise (Set.univ : Set (Fin N))
          (Function.onFun Disjoint fun i => (P i).window) ∧
        (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
        weightedTraceCost lam (frontier R.carrier) ≤
          (∑ i, (P i).payoff) + ENNReal.ofReal eta)
    (A : SmoothSequence) (hconv : A.ConvergesTo R.centeredCarrier)
    (hcost : A.cost lam ≤
      weightedTraceCost lam (frontier R.centeredCarrier)) :
    weightedTraceCost lam (frontier R.centeredCarrier) =
      weightedTraceCost lam (frontier R.carrier) := by
  apply R.frontier_cost_eq_of_minimizer_and_bounds hmin
  · exact
      R.weightedTraceCost_frontier_carrier_le_relaxedPerimeter_of_projection_exhaustion
        hexhaust
  · exact R.relaxedPerimeter_centeredCarrier_le_of_recovery A hconv hcost

/-- The source-facing equality-rigidity bridge.  Almost-everywhere agreement
transports the alleged source minimizer to the literal finite-band carrier;
the frontier bounds remain attached only to that selected representative. -/
theorem source_section_interfaces_of_minimizer_and_frontier_bounds
    (R : Region) {lam : ℝ} (hlam : 1 < lam)
    (horiginalLower :
      weightedTraceCost lam (frontier R.carrier) ≤
        relaxedPerimeter lam R.carrier)
    (hcenteredUpper :
      relaxedPerimeter lam R.centeredCarrier ≤
        weightedTraceCost lam (frontier R.centeredCarrier))
    (hwidth : ∀ i : Fin (R.bandCount - 1),
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : ∀ i : Fin (R.bandCount - 1), 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i))
    {E : Set PlanePoint}
    (hmin : (relaxedSourceSemantics lam).IsMinimizer E)
    (hE : E =ᵐ[volume] R.carrier) :
    ∃ axis : ℝ,
      HasAEIntervalHorizontalSections E ∧
        CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E := by
  have hregionMinimizer :
      (relaxedSourceSemantics lam).IsMinimizer R.carrier :=
    (relaxedSourceSemantics_isMinimizer_congr_ae lam hE).1 hmin
  have heq := R.frontier_cost_eq_of_minimizer_and_bounds
    hregionMinimizer horiginalLower hcenteredUpper
  exact R.source_section_interfaces_of_frontier_cost_eq
    hlam.le heq hwidth hpos hE

/-- Source-facing finite-band rigidity with the two geometric deliverables
exposed in their constructive forms: a finite projection exhaustion for every
positive deficit and one centered smooth recovery sequence.  Finite-band
representation, positive matching seam widths, and planar almost-everywhere
agreement remain explicit. -/
theorem source_section_interfaces_of_projection_exhaustion_and_recovery
    (R : Region) {lam : ℝ} (hlam : 1 < lam)
    (hexhaust : ∀ {eta : ℝ}, 0 < eta →
      ∃ N : ℕ, ∃ P : Fin N → RigidProjectionPatch lam R.carrier,
        Set.Pairwise (Set.univ : Set (Fin N))
          (Function.onFun Disjoint fun i => (P i).window) ∧
        (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
        weightedTraceCost lam (frontier R.carrier) ≤
          (∑ i, (P i).payoff) + ENNReal.ofReal eta)
    (A : SmoothSequence) (hconv : A.ConvergesTo R.centeredCarrier)
    (hcost : A.cost lam ≤
      weightedTraceCost lam (frontier R.centeredCarrier))
    (hwidth : ∀ i : Fin (R.bandCount - 1),
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i) =
        R.totalWidth (R.seamUpperBand i) (R.seamHeight i))
    (hpos : ∀ i : Fin (R.bandCount - 1), 0 <
      R.totalWidth (R.seamLowerBand i) (R.seamHeight i))
    {E : Set PlanePoint}
    (hmin : (relaxedSourceSemantics lam).IsMinimizer E)
    (hE : E =ᵐ[volume] R.carrier) :
    ∃ axis : ℝ,
      HasAEIntervalHorizontalSections E ∧
        CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E := by
  apply R.source_section_interfaces_of_minimizer_and_frontier_bounds
    hlam
  · exact
      R.weightedTraceCost_frontier_carrier_le_relaxedPerimeter_of_projection_exhaustion
        hexhaust
  · exact R.relaxedPerimeter_centeredCarrier_le_of_recovery A hconv hcost
  · exact hwidth
  · exact hpos
  · exact hmin
  · exact hE
end Region
end CMVRelaxation.FiniteBandRearrangement
