import CMVRelativeLevelTraceAveraging
import CMVFiniteJunctionRepair

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section

namespace CMVRelaxation

/-- Euclidean speed of a planar parameterization, expressed in the project's
coordinate carrier. -/
def euclideanParametricSpeed (γ : ℝ → PlanePoint) (t : ℝ) : ℝ :=
  Real.sqrt
    ((deriv (fun s => (γ s).1) t) ^ 2 +
      (deriv (fun s => (γ s).2) t) ^ 2)

private def complexParam (γ : ℝ → PlanePoint) (t : ℝ) : ℂ :=
  Complex.ofRealCLM ((γ t).2) + (γ t).1 • Complex.I

private def complexVelocity (γ : ℝ → PlanePoint) (t : ℝ) : ℂ :=
  Complex.ofRealCLM (deriv (fun s => (γ s).2) t) +
    deriv (fun s => (γ s).1) t • Complex.I

private lemma hasDerivAt_complexParam
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ) (t : ℝ) :
    HasDerivAt (complexParam γ) (complexVelocity γ t) t := by
  exact FiniteJunctionRepair.hasDerivAt_planeComplexParam
    (hγ.fst.differentiable (by norm_num) t)
    (hγ.snd.differentiable (by norm_num) t)

private lemma norm_complexVelocity
    (γ : ℝ → PlanePoint) (t : ℝ) :
    ‖complexVelocity γ t‖ = euclideanParametricSpeed γ t := by
  exact FiniteJunctionRepair.norm_planeComplexParam_deriv

private lemma norm_complexParam_sub_tangent_le
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b t₀ u v ε : ℝ}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b)
    (hclose : ∀ t ∈ Icc a b,
      ‖complexVelocity γ t - complexVelocity γ t₀‖ ≤ ε) :
    ‖complexParam γ v - complexParam γ u -
        (v - u) • complexVelocity γ t₀‖ ≤ ε * |v - u| := by
  let r : ℝ → ℂ := fun t =>
    complexParam γ t - (t - t₀) • complexVelocity γ t₀
  have hrderiv (t : ℝ) :
      HasDerivAt r (complexVelocity γ t - complexVelocity γ t₀) t := by
    have hlinear : HasDerivAt
        (fun s : ℝ => (s - t₀) • complexVelocity γ t₀)
        (complexVelocity γ t₀) t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).sub_const t₀).smul_const
          (complexVelocity γ t₀)
    exact (hasDerivAt_complexParam hγ t).sub hlinear
  have hmvt :=
    (convex_Icc a b).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (C := ε)
      (fun t _ht => (hrderiv t).hasFDerivAt.hasFDerivWithinAt)
      (fun t ht => by
        rw [ContinuousLinearMap.norm_toSpanSingleton]
        exact hclose t ht)
      hu hv
  dsimp only [r] at hmvt
  rw [Real.norm_eq_abs] at hmvt
  convert hmvt using 1
  congr 1
  module


/-- An arbitrarily sharp upper estimate for a compact `C¹` planar trace. -/
theorem hausdorffMeasure_parametricCurve_Icc_le_intervalIntegral_add
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b η : ℝ} (hab : a < b) (hη : 0 < η) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) ≤
      ENNReal.ofReal
        ((∫ t in a..b, euclideanParametricSpeed γ t) + η) := by
  let x : ℝ → ℝ := fun t => (γ t).1
  let y : ℝ → ℝ := fun t => (γ t).2
  let F : ℝ → ℝ := euclideanParametricSpeed γ
  have hx : ContDiff ℝ 1 x := hγ.fst
  have hy : ContDiff ℝ 1 y := hγ.snd
  have hF : Continuous F := by
    dsimp only [F, euclideanParametricSpeed, x, y]
    exact ((hx.continuous_deriv (by norm_num)).pow 2 |>.add
      ((hy.continuous_deriv (by norm_num)).pow 2)).sqrt
  let ε := η / (4 * (b - a))
  have hε : 0 < ε :=
    div_pos hη (mul_pos (by norm_num) (sub_pos.mpr hab))
  have huc : UniformContinuousOn F (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hcloseF⟩ := huc ε hε
  obtain ⟨N, hN, hdδ, hmidneg⟩ :=
    exists_midpoint_sum_add_ge_intervalIntegral
      hF.neg hab (half_pos hη) hδ
  let d := (b - a) / (N : ℝ)
  let p : ℕ → ℝ := fun k => a + (k : ℝ) * d
  let m : Fin N → ℝ := fun i => a + ((i : ℝ) + 1 / 2) * d
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNreal
  have hp0 : p 0 = a := by simp [p]
  have hpN : p N = b := by
    dsimp [p, d]
    field_simp [hNreal.ne']
    ring_nf
  have hpmono : Monotone p := by
    intro i j hij
    dsimp [p]
    gcongr
  have hm_between (i : Fin N) :
      m i ∈ Icc (p i.1) (p (i.1 + 1)) := by
    have hm_eq : m i = (p i.1 + p (i.1 + 1)) / 2 := by
      dsimp [m, p]
      push_cast
      ring
    rw [hm_eq]
    constructor <;> linarith [hpmono (Nat.le_succ i.1)]
  have hcell_mem (i : Fin N) :
      Icc (p i.1) (p (i.1 + 1)) ⊆ Icc a b := by
    intro t ht
    constructor
    · rw [← hp0]
      exact (hpmono (Nat.zero_le i.1)).trans ht.1
    · rw [← hpN]
      exact ht.2.trans (hpmono (Nat.succ_le_iff.mpr i.2))
  have hmmem (i : Fin N) : m i ∈ Icc a b :=
    hcell_mem i (hm_between i)
  have hspeed (i : Fin N) :
      ∀ t ∈ Icc (p i.1) (p (i.1 + 1)), F t ≤ F (m i) + ε := by
    intro t ht
    have hdist : dist t (m i) < δ := by
      rw [Real.dist_eq]
      have htm : |t - m i| ≤ d := by
        rw [abs_le]
        have hstep : p (i.1 + 1) - p i.1 = d := by
          dsimp [p]
          push_cast
          ring
        constructor <;>
          linarith [ht.1, ht.2, (hm_between i).1, (hm_between i).2]
      exact htm.trans_lt hdδ
    have hc := hcloseF t (hcell_mem i ht) (m i) (hmmem i) hdist
    rw [Real.dist_eq] at hc
    linarith [le_abs_self (F t - F (m i))]
  let K : Fin N → NNReal := fun i => Real.toNNReal (F (m i) + ε)
  have hKcoe (i : Fin N) : (K i : ℝ) = F (m i) + ε := by
    dsimp [K]
    exact max_eq_left (add_nonneg (Real.sqrt_nonneg _) hε.le)
  have hcellMeasure (i : Fin N) :
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (γ '' Icc (p i.1) (p (i.1 + 1)))) ≤
        (K i : ENNReal) * ENNReal.ofReal d := by
    have hstep : p (i.1 + 1) - p i.1 = d := by
      dsimp [p]
      push_cast
      ring
    rw [← hstep]
    have hmeasure :=
      FiniteJunctionRepair.hausdorffMeasure_euclideanPlaneParam_Icc_le
        (a := p i.1) (b := p (i.1 + 1)) (K := K i)
        (hx.differentiable (by norm_num)) (hy.differentiable (by norm_num))
        (fun t ht => by
          rw [hKcoe]
          exact hspeed i t ht)
    simpa only [x, y] using hmeasure
  have hcover :
      planeEuclideanHomeomorph '' (γ '' Icc a b) ⊆
        {planeEuclideanHomeomorph (γ a)} ∪
          ⋃ i ∈ Finset.range N,
            planeEuclideanHomeomorph ''
              (γ '' Icc (p i) (p (i + 1))) := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have htp : t ∈ Icc (p 0) (p N) := by rwa [hp0, hpN]
    rcases Icc_subset_singleton_union_iUnion_adjacent p N htp with
      ht0 | htcells
    · left
      rw [mem_singleton_iff] at ht0 ⊢
      rw [ht0, hp0]
    · right
      simp only [mem_iUnion, Finset.mem_range] at htcells ⊢
      rcases htcells with ⟨i, hi, hti⟩
      exact ⟨i, hi, γ t, ⟨t, hti, rfl⟩, rfl⟩
  have hKofReal (i : Fin N) :
      (K i : ENNReal) = ENNReal.ofReal (F (m i) + ε) := by
    rw [← ENNReal.ofReal_coe_nnreal, hKcoe]
  have hsumENN :
      ∑ i : Fin N, (K i : ENNReal) * ENNReal.ofReal d =
        ENNReal.ofReal (∑ i : Fin N, (F (m i) + ε) * d) := by
    symm
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i _
      have hnonneg : 0 ≤ F (m i) + ε :=
        add_nonneg (Real.sqrt_nonneg _) hε.le
      rw [ENNReal.ofReal_mul hnonneg, ← hKofReal]
    · intro i _
      exact mul_nonneg (add_nonneg (Real.sqrt_nonneg _) hε.le) hd.le
  have hmid :
      (∑ i : Fin N, F (m i) * d) ≤
        (∫ t in a..b, F t) + η / 2 := by
    change (∫ t in a..b, -F t) ≤
      (∑ i : Fin N, -F (m i) * d) + η / 2 at hmidneg
    rw [intervalIntegral.integral_neg] at hmidneg
    have hsumneg : (∑ i : Fin N, -F (m i) * d) =
        -(∑ i : Fin N, F (m i) * d) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
    rw [hsumneg] at hmidneg
    linarith
  have hsumExpand :
      (∑ i : Fin N, (F (m i) + ε) * d) =
        (∑ i : Fin N, F (m i) * d) + (N : ℝ) * (ε * d) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hNeps : (N : ℝ) * (ε * d) = η / 4 := by
    dsimp [ε, d]
    field_simp [hNreal.ne', (sub_pos.mpr hab).ne']
  have hsumReal :
      (∑ i : Fin N, (F (m i) + ε) * d) ≤
        (∫ t in a..b, F t) + η := by
    rw [hsumExpand, hNeps]
    linarith
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  calc
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) ≤
        (μH[1] : Measure EuclideanPlane)
          ({planeEuclideanHomeomorph (γ a)} ∪
            ⋃ i ∈ Finset.range N,
              planeEuclideanHomeomorph ''
                (γ '' Icc (p i) (p (i + 1)))) :=
      measure_mono hcover
    _ ≤ (μH[1] : Measure EuclideanPlane)
          {planeEuclideanHomeomorph (γ a)} +
        (μH[1] : Measure EuclideanPlane)
          (⋃ i ∈ Finset.range N,
            planeEuclideanHomeomorph ''
              (γ '' Icc (p i) (p (i + 1)))) :=
      measure_union_le _ _
    _ ≤ ∑ i ∈ Finset.range N,
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (γ '' Icc (p i) (p (i + 1)))) := by
      simpa using
        (MeasureTheory.measure_biUnion_finset_le
          (μ := (μH[1] : Measure EuclideanPlane))
          (Finset.range N)
          (fun i => planeEuclideanHomeomorph ''
            (γ '' Icc (p i) (p (i + 1)))))
    _ = ∑ i : Fin N,
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (γ '' Icc (p i.1) (p (i.1 + 1)))) :=
      (Fin.sum_univ_eq_sum_range
        (fun i => (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (γ '' Icc (p i) (p (i + 1))))) N).symm
    _ ≤ ∑ i : Fin N, (K i : ENNReal) * ENNReal.ofReal d :=
      Finset.sum_le_sum fun i _ => hcellMeasure i
    _ = ENNReal.ofReal (∑ i : Fin N, (F (m i) + ε) * d) :=
      hsumENN
    _ ≤ ENNReal.ofReal ((∫ t in a..b, F t) + η) :=
      ENNReal.ofReal_le_ofReal hsumReal
    _ = _ := rfl

/-- The Euclidean `H¹` mass of a compact `C¹` planar trace is at most its
parametric speed integral. -/
theorem hausdorffMeasure_parametricCurve_Icc_le_intervalIntegral
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b : ℝ} (hab : a ≤ b) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) ≤
      ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) := by
  rcases hab.eq_or_lt with rfl | hab
  · let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
      Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
    simp
  · have hInt : 0 ≤ ∫ t in a..b, euclideanParametricSpeed γ t :=
      intervalIntegral.integral_nonneg hab.le
        (fun t _ => Real.sqrt_nonneg _)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    have happrox :=
      hausdorffMeasure_parametricCurve_Icc_le_intervalIntegral_add
        hγ hab hεreal
    rw [ENNReal.ofReal_add hInt hεreal.le,
      ENNReal.ofReal_coe_nnreal] at happrox
    exact happrox

private lemma dist_planeParam_eq_norm_complexParam_sub
    (γ : ℝ → PlanePoint) (u v : ℝ) :
    dist (planeEuclideanHomeomorph (γ u))
        (planeEuclideanHomeomorph (γ v)) =
      ‖complexParam γ v - complexParam γ u‖ := by
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change Real.sqrt
      (dist (γ u).1 (γ v).1 ^ 2 + dist (γ u).2 (γ v).2 ^ 2) =
    ‖complexParam γ v - complexParam γ u‖
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [complexParam, Complex.ofRealCLM_apply, Complex.add_re,
    Complex.ofReal_re, Complex.smul_re, Complex.I_re,
    Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
    Complex.sub_re, Complex.sub_im, Real.dist_eq]
  rw [sq_abs, sq_abs]
  ring

/-- For an injective regular `C¹` planar curve, the speed integral is a lower
bound for the Euclidean `H¹` mass of its trace. -/
theorem intervalIntegral_le_hausdorffMeasure_parametricCurve_Icc
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Icc a b))
    (hregular : ∀ t ∈ Icc a b, 0 < euclideanParametricSpeed γ t) :
    ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) ≤
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let F : ℝ → ℝ := euclideanParametricSpeed γ
  have hx : ContDiff ℝ 1 (fun t => (γ t).1) := hγ.fst
  have hy : ContDiff ℝ 1 (fun t => (γ t).2) := hγ.snd
  have hF : Continuous F := by
    dsimp only [F, euclideanParametricSpeed]
    exact ((hx.continuous_deriv (by norm_num)).pow 2 |>.add
      ((hy.continuous_deriv (by norm_num)).pow 2)).sqrt
  have hV : Continuous (complexVelocity γ) := by
    change Continuous (fun t =>
      Complex.ofRealCLM (deriv (fun s => (γ s).2) t) +
        deriv (fun s => (γ s).1) t • Complex.I)
    fun_prop
  obtain ⟨tmin, htmin, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hF.continuousOn
  have hFmin : 0 < F tmin := hregular tmin htmin
  have hInt : 0 ≤ ∫ t in a..b, F t :=
    intervalIntegral.integral_nonneg hab.le
      (fun t _ => Real.sqrt_nonneg _)
  apply ENNReal.le_of_forall_pos_le_add
  intro η hη _hmeasureTop
  have hηreal : 0 < (η : ℝ) := by exact_mod_cast hη
  let ε : ℝ :=
    min ((η : ℝ) / (4 * (b - a))) (F tmin / 2)
  have hε : 0 < ε := lt_min
    (div_pos hηreal (mul_pos (by norm_num) (sub_pos.mpr hab)))
    (half_pos hFmin)
  have hεbudget : ε ≤ (η : ℝ) / (4 * (b - a)) :=
    min_le_left _ _
  have hεmin : ε ≤ F tmin / 2 := min_le_right _ _
  have huc : UniformContinuousOn (complexVelocity γ) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hV.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hcloseV⟩ := huc ε hε
  obtain ⟨N, hN, hdδ, hmid⟩ :=
    exists_midpoint_sum_add_ge_intervalIntegral hF hab
      (div_pos hηreal (by norm_num : (0 : ℝ) < 4)) hδ
  let d : ℝ := (b - a) / (N : ℝ)
  let p : ℕ → ℝ := uniformPartitionPoint a b N
  let m : Fin N → ℝ := fun i => a + ((i : ℝ) + 1 / 2) * d
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNreal
  have hpstep (i : ℕ) : p (i + 1) - p i = d := by
    dsimp [p, uniformPartitionPoint, d]
    push_cast
    ring
  have hp0 : p 0 = a := by simp [p, uniformPartitionPoint]
  have hpN : p N = b := by
    dsimp [p, uniformPartitionPoint]
    field_simp [hNreal.ne']
    ring
  have hpmono : Monotone p := by
    intro i j hij
    dsimp [p, uniformPartitionPoint]
    gcongr
  have hcell_mem (i : Fin N) :
      Icc (p i.1) (p (i.1 + 1)) ⊆ Icc a b := by
    intro t ht
    constructor
    · rw [← hp0]
      exact (hpmono (Nat.zero_le i.1)).trans ht.1
    · rw [← hpN]
      exact ht.2.trans (hpmono (Nat.succ_le_iff.mpr i.2))
  have hm_between (i : Fin N) :
      m i ∈ Icc (p i.1) (p (i.1 + 1)) := by
    have hm_eq : m i = (p i.1 + p (i.1 + 1)) / 2 := by
      dsimp [m, p, uniformPartitionPoint, d]
      push_cast
      ring
    rw [hm_eq]
    constructor <;> linarith [hpmono (Nat.le_succ i.1)]
  have hchord (i : Fin N) :
      ENNReal.ofReal ((F (m i) - ε) * d) ≤
        ENNReal.ofReal
          (dist (planeEuclideanHomeomorph (γ (p i.1)))
            (planeEuclideanHomeomorph (γ (p (i.1 + 1))))) := by
    have hclose :
        ∀ t ∈ Icc (p i.1) (p (i.1 + 1)),
          ‖complexVelocity γ t - complexVelocity γ (m i)‖ ≤ ε := by
      intro t ht
      have hdist : dist t (m i) < δ := by
        rw [Real.dist_eq]
        have htm : |t - m i| ≤ d := by
          rw [abs_le]
          constructor <;>
            linarith [ht.1, ht.2, (hm_between i).1,
              (hm_between i).2, hpstep i.1]
        exact htm.trans_lt hdδ
      have hc := hcloseV t (hcell_mem i ht) (m i)
        (hcell_mem i (hm_between i)) hdist
      rw [dist_eq_norm] at hc
      exact hc.le
    have hrem := norm_complexParam_sub_tangent_le hγ
      (by exact ⟨le_rfl, hpmono (Nat.le_succ i.1)⟩)
      (by exact ⟨hpmono (Nat.le_succ i.1), le_rfl⟩) hclose
    rw [hpstep i.1, abs_of_pos hd] at hrem
    let A : ℂ :=
      complexParam γ (p (i.1 + 1)) - complexParam γ (p i.1)
    let B : ℂ := d • complexVelocity γ (m i)
    have htri : ‖B‖ ≤ ‖A‖ + ‖A - B‖ := by
      calc
        ‖B‖ = ‖(B - A) + A‖ := by
          congr 1
          module
        _ ≤ ‖B - A‖ + ‖A‖ := norm_add_le _ _
        _ = ‖A‖ + ‖A - B‖ := by
          have hnorm : ‖B - A‖ = ‖A - B‖ := by
            rw [← norm_neg (B - A)]
            congr 1
            module
          rw [hnorm, add_comm]
    have hB : ‖B‖ = d * F (m i) := by
      dsimp only [B]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd,
        norm_complexVelocity]
    have hreal :
        (F (m i) - ε) * d ≤
          dist (planeEuclideanHomeomorph (γ (p i.1)))
            (planeEuclideanHomeomorph (γ (p (i.1 + 1)))) := by
      rw [dist_planeParam_eq_norm_complexParam_sub]
      dsimp only [A, B] at htri
      rw [hB] at htri
      linarith
    exact ENNReal.ofReal_le_ofReal hreal
  have hterm_nonneg (i : Fin N) : 0 ≤ (F (m i) - ε) * d := by
    apply mul_nonneg _ hd.le
    have hmglobal := hcell_mem i (hm_between i)
    have hminimum : F tmin ≤ F (m i) := hmin hmglobal
    linarith
  have hsumENN :
      ENNReal.ofReal (∑ i : Fin N, (F (m i) - ε) * d) =
        ∑ i : Fin N, ENNReal.ofReal ((F (m i) - ε) * d) :=
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm_nonneg i)
  have hcurveContinuous : Continuous
      (fun t : ℝ => planeEuclideanHomeomorph (γ t)) :=
    planeEuclideanHomeomorph.continuous.comp hγ.continuous
  have hcurveInj : Set.InjOn
      (fun t : ℝ => planeEuclideanHomeomorph (γ t)) (Icc a b) := by
    intro u hu v hv huv
    exact hinj hu hv (planeEuclideanHomeomorph.injective huv)
  have hpolygon :=
    uniformPartitionChordSum_le_hausdorffMeasure_image_Icc
      hcurveContinuous hab hN hcurveInj
  have hlowerMeasure :
      ENNReal.ofReal (∑ i : Fin N, (F (m i) - ε) * d) ≤
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' (γ '' Icc a b)) := by
    rw [hsumENN]
    refine (Finset.sum_le_sum fun i _ => hchord i).trans ?_
    simpa only [Set.image_image, Function.comp_apply, p,
      uniformPartitionPoint] using hpolygon
  have hNd : (N : ℝ) * d = b - a := by
    dsimp [d]
    field_simp [hNreal.ne']
  have herror : (N : ℝ) * (ε * d) ≤ (η : ℝ) / 4 := by
    calc
      (N : ℝ) * (ε * d) = ε * ((N : ℝ) * d) := by ring
      _ = ε * (b - a) := by rw [hNd]
      _ ≤ ((η : ℝ) / (4 * (b - a))) * (b - a) :=
        mul_le_mul_of_nonneg_right hεbudget (sub_pos.mpr hab).le
      _ = (η : ℝ) / 4 := by
        field_simp [(sub_pos.mpr hab).ne']
  have hsumExpand :
      (∑ i : Fin N, (F (m i) - ε) * d) =
        (∑ i : Fin N, F (m i) * d) - (N : ℝ) * (ε * d) := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hreal :
      (∫ t in a..b, F t) ≤
        (∑ i : Fin N, (F (m i) - ε) * d) + (η : ℝ) / 2 := by
    rw [hsumExpand]
    change (∫ t in a..b, F t) ≤
      (∑ i : Fin N, F (m i) * d) + (η : ℝ) / 4 at hmid
    linarith
  have hsum_nonneg : 0 ≤ ∑ i : Fin N, (F (m i) - ε) * d :=
    Finset.sum_nonneg fun i _ => hterm_nonneg i
  change ENNReal.ofReal (∫ t in a..b, F t) ≤ _
  calc
    ENNReal.ofReal (∫ t in a..b, F t) ≤
        ENNReal.ofReal
          ((∑ i : Fin N, (F (m i) - ε) * d) + (η : ℝ) / 2) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (∑ i : Fin N, (F (m i) - ε) * d) +
        ENNReal.ofReal ((η : ℝ) / 2) := by
      rw [ENNReal.ofReal_add hsum_nonneg
        (div_nonneg hηreal.le (by norm_num))]
    _ ≤ (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' (γ '' Icc a b)) + η := by
      apply add_le_add hlowerMeasure
      calc
        ENNReal.ofReal ((η : ℝ) / 2) ≤ ENNReal.ofReal (η : ℝ) :=
          ENNReal.ofReal_le_ofReal (by linarith)
        _ = η := ENNReal.ofReal_coe_nnreal

/-- Exact arclength formula when regularity is stated directly as positivity
of the Euclidean coordinate speed. -/
theorem hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral_of_speed_pos
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Icc a b))
    (hregular : ∀ t ∈ Icc a b, 0 < euclideanParametricSpeed γ t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) =
      ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) :=
  le_antisymm
    (hausdorffMeasure_parametricCurve_Icc_le_intervalIntegral hγ hab)
    (intervalIntegral_le_hausdorffMeasure_parametricCurve_Icc
      hγ hab hinj hregular)

/-- Nonvanishing of the usual Fréchet derivative implies positivity of the
coordinate Euclidean speed. -/
lemma euclideanParametricSpeed_pos_of_fderiv_ne_zero
    {γ : ℝ → PlanePoint} {t : ℝ} (hγ : DifferentiableAt ℝ γ t)
    (hregular : fderiv ℝ γ t ≠ 0) :
    0 < euclideanParametricSpeed γ t := by
  have hone : fderiv ℝ γ t 1 ≠ 0 := by
    intro hone
    apply hregular
    apply ContinuousLinearMap.ext
    intro r
    rw [show r = r • (1 : ℝ) by simp, map_smul, hone, smul_zero]
    rfl
  have hx : DifferentiableAt ℝ (fun s => (γ s).1) t :=
    hγ.hasFDerivAt.fst.differentiableAt
  have hy : DifferentiableAt ℝ (fun s => (γ s).2) t :=
    hγ.hasFDerivAt.snd.differentiableAt
  have hpair :
      fderiv ℝ γ t 1 =
        (deriv (fun s => (γ s).1) t,
          deriv (fun s => (γ s).2) t) := by
    have hprod := hx.fderiv_prodMk hy
    have happly := congrArg (fun L => L 1) hprod
    simpa only [Prod.eta, ContinuousLinearMap.prod_apply, deriv] using happly
  rw [euclideanParametricSpeed]
  apply Real.sqrt_pos.2
  by_contra hsum
  have hnonneg :
      0 ≤ (deriv (fun s => (γ s).1) t) ^ 2 +
        (deriv (fun s => (γ s).2) t) ^ 2 := by positivity
  have hsumzero :
      (deriv (fun s => (γ s).1) t) ^ 2 +
        (deriv (fun s => (γ s).2) t) ^ 2 = 0 :=
    le_antisymm (le_of_not_gt hsum) hnonneg
  have hxzero : deriv (fun s => (γ s).1) t = 0 := by
    nlinarith [sq_nonneg (deriv (fun s => (γ s).2) t)]
  have hyzero : deriv (fun s => (γ s).2) t = 0 := by
    nlinarith [sq_nonneg (deriv (fun s => (γ s).1) t)]
  apply hone
  rw [hpair, hxzero, hyzero]
  rfl

/-- Exact arclength formula for an injective regular `C¹` planar
parameterization.  The target is the genuine Euclidean realization used by the
project's Hausdorff measure. -/
theorem hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Icc a b))
    (hregular : ∀ t ∈ Icc a b, fderiv ℝ γ t ≠ 0) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) =
      ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) := by
  apply hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral_of_speed_pos
    hγ hab hinj
  intro t ht
  exact euclideanParametricSpeed_pos_of_fderiv_ne_zero
    (hγ.differentiable (by norm_num) t) (hregular t ht)

/-- Global-injectivity form of the exact regular parametric arclength formula. -/
theorem hausdorffMeasure_injective_regularParametricCurve_Icc_eq_intervalIntegral
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    (hinj : Function.Injective γ)
    (hregular : ∀ t, fderiv ℝ γ t ≠ 0)
    {a b : ℝ} (hab : a ≤ b) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Icc a b)) =
      ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) :=
  hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral
    hγ hab hinj.injOn (fun t _ => hregular t)

/-- Half-open endpoint form under direct positivity of the Euclidean
coordinate speed. -/
theorem hausdorffMeasure_regularParametricCurve_Ico_eq_intervalIntegral_of_speed_pos
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Icc a b))
    (hregular : ∀ t ∈ Icc a b, 0 < euclideanParametricSpeed γ t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Ico a b)) =
      ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) := by
  rw [show planeEuclideanHomeomorph '' (γ '' Ico a b) =
      (fun t => planeEuclideanHomeomorph (γ t)) '' Ico a b by
        rw [Set.image_image]]
  rw [hausdorffMeasure_image_Ico_eq_Icc
    (S := Icc a b)
    (fun u hu v hv huv =>
      hinj hu hv (planeEuclideanHomeomorph.injective huv))
    hab (fun _ ht => ht)]
  rw [← Set.image_image]
  exact
    hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral_of_speed_pos
      hγ hab hinj hregular

/-- Half-open endpoint form; deleting the terminal point does not alter
Euclidean `H¹`. -/
theorem hausdorffMeasure_regularParametricCurve_Ico_eq_intervalIntegral
    {γ : ℝ → PlanePoint} (hγ : ContDiff ℝ 1 γ)
    {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Icc a b))
    (hregular : ∀ t ∈ Icc a b, fderiv ℝ γ t ≠ 0) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (γ '' Ico a b)) =
      ENNReal.ofReal (∫ t in a..b, euclideanParametricSpeed γ t) := by
  apply
    hausdorffMeasure_regularParametricCurve_Ico_eq_intervalIntegral_of_speed_pos
      hγ hab hinj
  intro t ht
  exact euclideanParametricSpeed_pos_of_fderiv_ne_zero
    (hγ.differentiable (by norm_num) t) (hregular t ht)
end CMVRelaxation
