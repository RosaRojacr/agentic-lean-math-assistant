import CMVGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal

noncomputable section


/-- A circle parametrized by signed arclength in the standard Euclidean complex plane. -/
def unitCircleArc (r s : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (Complex.I * (s / r : ℝ))

lemma continuous_unitCircleArc (r : ℝ) : Continuous (unitCircleArc r) := by
  unfold unitCircleArc
  fun_prop

lemma unitCircleArc_sub_factor {r s t : ℝ} (_hr : r ≠ 0) :
    unitCircleArc r s - unitCircleArc r t =
      (r : ℂ) * Complex.exp (Complex.I * (t / r : ℝ)) *
        (Complex.exp (Complex.I * ((s - t) / r : ℝ)) - 1) := by
  have he : Complex.exp (Complex.I * (s / r : ℝ)) =
      Complex.exp (Complex.I * (t / r : ℝ)) *
        Complex.exp (Complex.I * ((s - t) / r : ℝ)) := by
    rw [← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [unitCircleArc, unitCircleArc, he]
  ring

lemma lipschitzWith_unitCircleArc {r : ℝ} (hr : 0 < r) :
    LipschitzWith 1 (unitCircleArc r) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  simp only [NNReal.coe_one, one_mul, Complex.dist_eq]
  rw [unitCircleArc_sub_factor hr.ne', norm_mul, norm_mul]
  have hexp : ‖Complex.exp (Complex.I * (t / r : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp, mul_one]
  have hnormr : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  rw [hnormr]
  calc
    r * ‖Complex.exp (Complex.I * ((s - t) / r : ℝ)) - 1‖
        ≤ r * ‖(s - t) / r‖ := by
          gcongr
          exact Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = ‖s - t‖ := by
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr]
      field_simp
    _ = dist s t := by simp only [Real.norm_eq_abs, Real.dist_eq]

lemma unitCircleArc_dist {r s t : ℝ} (hr : 0 < r) :
    dist (unitCircleArc r s) (unitCircleArc r t) =
      r * |2 * Real.sin (((s - t) / r) / 2)| := by
  rw [Complex.dist_eq, unitCircleArc_sub_factor hr.ne', norm_mul, norm_mul]
  have hexp : ‖Complex.exp (Complex.I * (t / r : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp, mul_one]
  have hnormr : ‖(r : ℂ)‖ = r := by simp [abs_of_pos hr]
  rw [hnormr, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [Real.norm_eq_abs]

lemma unitCircleArc_injOn {r theta : ℝ} (hr : 0 < r)
    (htheta : theta ∈ Ioo 0 Real.pi) :
    Set.InjOn (unitCircleArc r) (Icc (-r * theta) (r * theta)) := by
  intro s hs t ht hst
  have hsdiv : s / r ∈ Icc (-theta) theta := by
    constructor
    · apply (le_div_iff₀ hr).2
      nlinarith [hs.1]
    · apply (div_le_iff₀ hr).2
      nlinarith [hs.2]
  have htdiv : t / r ∈ Icc (-theta) theta := by
    constructor
    · apply (le_div_iff₀ hr).2
      nlinarith [ht.1]
    · apply (div_le_iff₀ hr).2
      nlinarith [ht.2]
  rcases hsdiv with ⟨hsl, hsr⟩
  rcases htdiv with ⟨htl, htr⟩
  have hdist : |s / r - t / r| < 2 * Real.pi := by
    rw [abs_lt]
    constructor <;> nlinarith [htheta.2]
  have hcircle : circleMap 0 r (s / r) = circleMap 0 r (t / r) := by
    simpa [unitCircleArc, circleMap_zero, mul_comm] using hst
  have hang := eq_of_circleMap_eq hr.ne' hdist hcircle
  exact (div_left_inj' hr.ne').mp hang

lemma hausdorffMeasure_unitCircleArc_image_le {r a b : ℝ} (hr : 0 < r) :
    (μH[1] : Measure ℂ) (unitCircleArc r '' Icc a b) ≤
      ENNReal.ofReal (b - a) := by
  calc
    (μH[1] : Measure ℂ) (unitCircleArc r '' Icc a b)
        ≤ (μH[1] : Measure ℝ) (Icc a b) := by
          simpa using (lipschitzWith_unitCircleArc hr).hausdorffMeasure_image_le
            (d := (1 : ℝ)) (by norm_num) (Icc a b)
    _ = ENNReal.ofReal (b - a) := by
      rw [hausdorffMeasure_real, Real.volume_Icc]

/-- Every continuous curve image has H¹ mass at least the distance between its endpoints. -/
lemma ofReal_dist_le_hausdorffMeasure_image_Icc
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : ℝ → E} (hf : Continuous f) {u v : ℝ} (huv : u ≤ v) :
    ENNReal.ofReal (dist (f u) (f v)) ≤
      (μH[1] : Measure E) (f '' Icc u v) := by
  let g : E → ℝ := fun z => dist (f u) z
  have hg : LipschitzWith 1 g := LipschitzWith.dist_right (f u)
  have hI : Icc 0 (dist (f u) (f v)) ⊆ g '' (f '' Icc u v) := by
    have hIV := intermediate_value_Icc huv (hg.continuous.comp hf).continuousOn
    simpa only [g, dist_self, Set.image_image, Function.comp_apply] using hIV
  calc
    ENNReal.ofReal (dist (f u) (f v)) =
        (μH[1] : Measure ℝ) (Icc 0 (dist (f u) (f v))) := by
          rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero]
    _ ≤ (μH[1] : Measure ℝ) (g '' (f '' Icc u v)) := measure_mono hI
    _ ≤ (μH[1] : Measure E) (f '' Icc u v) := by
      simpa using hg.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num)
        (f '' Icc u v)

lemma image_Ico_eq_image_Icc_diff_endpoint
    {α : Type*} {f : ℝ → α} {S : Set ℝ} (hf : Set.InjOn f S)
    {u v : ℝ} (huv : u ≤ v) (hsub : Icc u v ⊆ S) :
    f '' Ico u v = f '' Icc u v \ {f v} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, ⟨hx.1, hx.2.le⟩, rfl⟩, ?_⟩
    simp only [mem_singleton_iff]
    intro hfv
    have hxv := hf (hsub ⟨hx.1, hx.2.le⟩) (hsub ⟨huv, le_rfl⟩) hfv
    exact hx.2.ne hxv
  · rintro ⟨⟨x, hx, rfl⟩, hne⟩
    refine ⟨x, ⟨hx.1, lt_of_le_of_ne hx.2 ?_⟩, rfl⟩
    intro hxv
    subst x
    exact hne (mem_singleton (f v))

lemma hausdorffMeasure_image_Ico_eq_Icc
    {E : Type*} [EMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {f : ℝ → E} {S : Set ℝ} (hf : Set.InjOn f S)
    {u v : ℝ} (huv : u ≤ v) (hsub : Icc u v ⊆ S) :
    (μH[1] : Measure E) (f '' Ico u v) =
      (μH[1] : Measure E) (f '' Icc u v) := by
  rw [image_Ico_eq_image_Icc_diff_endpoint hf huv hsub]
  letI : NullSingletonClass (μH[1] : Measure E) :=
    Measure.nullSingletonClass_hausdorff E (by norm_num)
  exact measure_sdiff_null (measure_singleton (f v))

/-- Equally spaced partition points on the signed-arclength interval. -/
def capPartitionPoint (r theta : ℝ) (N i : ℕ) : ℝ :=
  -r * theta + (i : ℝ) * (2 * r * theta / (N : ℝ))

lemma capPartitionPoint_zero (r theta : ℝ) (N : ℕ) :
    capPartitionPoint r theta N 0 = -r * theta := by
  simp [capPartitionPoint]

lemma capPartitionPoint_end {r theta : ℝ} {N : ℕ} (hN : 0 < N) :
    capPartitionPoint r theta N N = r * theta := by
  unfold capPartitionPoint
  field_simp [Nat.ne_of_gt hN]
  ring

lemma monotone_capPartitionPoint {r theta : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    {N : ℕ} (hN : 0 < N) : Monotone (capPartitionPoint r theta N) := by
  intro i j hij
  unfold capPartitionPoint
  have hden : 0 < (N : ℝ) := by positivity
  have hstep : 0 ≤ 2 * r * theta / (N : ℝ) := (div_pos (by positivity) hden).le
  gcongr

lemma capPartitionPoint_mem {r theta : ℝ} (hr : 0 < r) (htheta : 0 < theta)
    {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    capPartitionPoint r theta N i ∈ Icc (-r * theta) (r * theta) := by
  have hm := monotone_capPartitionPoint hr htheta hN
  constructor
  · rw [← capPartitionPoint_zero r theta N]
    exact hm (Nat.zero_le i)
  · rw [← capPartitionPoint_end hN]
    exact hm hi

lemma capPartitionPoint_dist {r theta : ℝ} (hr : 0 < r)
    (htheta : theta ∈ Ioo 0 Real.pi) {N i : ℕ} (hN : 0 < N) :
    dist (unitCircleArc r (capPartitionPoint r theta N i))
      (unitCircleArc r (capPartitionPoint r theta N (i + 1))) =
        2 * r * Real.sin (theta / (N : ℝ)) := by
  rw [unitCircleArc_dist hr]
  have hNreal : 0 < (N : ℝ) := by positivity
  have harg :
      ((capPartitionPoint r theta N i - capPartitionPoint r theta N (i + 1)) / r) / 2 =
        -(theta / (N : ℝ)) := by
    unfold capPartitionPoint
    push_cast
    field_simp [hr.ne', hNreal.ne']
    ring
  have hangle_pos : 0 < theta / (N : ℝ) := div_pos htheta.1 hNreal
  have hN_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hangle_lt : theta / (N : ℝ) < Real.pi := by
    apply (div_lt_iff₀ hNreal).2
    nlinarith [htheta.2, Real.pi_pos]
  rw [harg, Real.sin_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_neg, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt)]
  ring

lemma cap_partition_polygon_lower {r theta : ℝ} (hr : 0 < r)
    (htheta : theta ∈ Ioo 0 Real.pi) (N : ℕ) (hN : 0 < N) :
    ENNReal.ofReal ((N : ℝ) * (2 * r * Real.sin (theta / (N : ℝ)))) ≤
      (μH[1] : Measure ℂ)
        (unitCircleArc r '' Icc (-r * theta) (r * theta)) := by
  let p : ℕ → ℝ := capPartitionPoint r theta N
  let A : ℕ → Set ℝ := fun i => Ico (p i) (p (i + 1))
  let S : Set ℝ := Icc (-r * theta) (r * theta)
  let f : ℝ → ℂ := unitCircleArc r
  let μ : Measure ℂ := μH[1]
  have hpmono : Monotone p := monotone_capPartitionPoint hr htheta.1 hN
  have hinj : Set.InjOn f S := unitCircleArc_injOn hr htheta
  have hpiece_sub (i : ℕ) (hi : i < N) : Icc (p i) (p (i + 1)) ⊆ S := by
    intro x hx
    exact ⟨(capPartitionPoint_mem hr htheta.1 hN hi.le).1.trans hx.1,
      hx.2.trans (capPartitionPoint_mem hr htheta.1 hN (Nat.succ_le_iff.mpr hi)).2⟩
  have hpair : Set.Pairwise (↑(Finset.range N))
      (Function.onFun Disjoint fun i => f '' A i) := by
    intro i hi j hj hij
    change Disjoint (f '' A i) (f '' A j)
    have hsrc : Disjoint (A i) (A j) := hpmono.pairwise_disjoint_on_Ico_succ hij
    rw [Set.disjoint_left]
    rintro y ⟨x, hxi, rfl⟩ ⟨z, hzj, hzx⟩
    have hiN : i < N := Finset.mem_range.mp hi
    have hjN : j < N := Finset.mem_range.mp hj
    have hxS : x ∈ S := hpiece_sub i hiN ⟨hxi.1, hxi.2.le⟩
    have hzS : z ∈ S := hpiece_sub j hjN ⟨hzj.1, hzj.2.le⟩
    have hxz : x = z := hinj hxS hzS hzx.symm
    exact (Set.disjoint_left.mp hsrc) hxi (hxz ▸ hzj)
  have hmeas (i : ℕ) (hi : i ∈ Finset.range N) : MeasurableSet (f '' A i) := by
    have hiN : i < N := Finset.mem_range.mp hi
    rw [show f '' A i = f '' Icc (p i) (p (i + 1)) \ {f (p (i + 1))} by
      exact image_Ico_eq_image_Icc_diff_endpoint hinj (hpmono (Nat.le_succ i))
        (hpiece_sub i hiN)]
    exact (isCompact_Icc.image (continuous_unitCircleArc r)).measurableSet.diff
      (measurableSet_singleton _)
  have hunion_sub : (⋃ i ∈ Finset.range N, f '' A i) ⊆ f '' S := by
    intro y hy
    rcases mem_iUnion.mp hy with ⟨i, hy⟩
    rcases mem_iUnion.mp hy with ⟨hi, hy⟩
    rcases hy with ⟨x, hxA, rfl⟩
    exact ⟨x, hpiece_sub i (Finset.mem_range.mp hi) ⟨hxA.1, hxA.2.le⟩, rfl⟩
  calc
    ENNReal.ofReal ((N : ℝ) * (2 * r * Real.sin (theta / (N : ℝ)))) =
        ∑ i ∈ Finset.range N,
          ENNReal.ofReal (2 * r * Real.sin (theta / (N : ℝ))) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range N, μ (f '' A i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      rw [hausdorffMeasure_image_Ico_eq_Icc hinj (hpmono (Nat.le_succ i))
        (hpiece_sub i hiN)]
      simpa [f, p, μ, capPartitionPoint_dist hr htheta hN] using
        ofReal_dist_le_hausdorffMeasure_image_Icc (continuous_unitCircleArc r)
          (hpmono (Nat.le_succ i))
    _ = μ (⋃ i ∈ Finset.range N, f '' A i) :=
      (measure_biUnion_finset hpair hmeas).symm
    _ ≤ μ (f '' S) := measure_mono hunion_sub

lemma tendsto_cap_polygon_length {r theta : ℝ} (htheta : 0 < theta) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        (2 * r * Real.sin (theta / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (2 * r * theta)) := by
  have hden : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_iff (R := ℝ)).2 (tendsto_add_atTop_nat 1)
  have hquot : Tendsto (fun n : ℕ => theta / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    hden.const_div_atTop theta
  have hsinc : Tendsto (fun n : ℕ => Real.sinc (theta / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 1) := by
    convert (Real.continuous_sinc.tendsto 0).comp hquot using 1 <;>
      simp [Function.comp_def]
  have hscaled : Tendsto
      (fun n : ℕ => (2 * r * theta) * Real.sinc (theta / ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (2 * r * theta)) := by
    simpa using hsinc.const_mul (2 * r * theta)
  apply hscaled.congr'
  filter_upwards [] with n
  have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hq : theta / (((n + 1 : ℕ) : ℝ)) ≠ 0 := div_ne_zero htheta.ne' hN
  rw [Real.sinc_of_ne_zero hq]
  field_simp

/-- Exact H¹ mass of every injective circular arc with half-angle in `(0, π)`. -/
theorem hausdorffMeasure_unitCircleArc_image_eq {r theta : ℝ} (hr : 0 < r)
    (htheta : theta ∈ Ioo 0 Real.pi) :
    (μH[1] : Measure ℂ)
        (unitCircleArc r '' Icc (-r * theta) (r * theta)) =
      ENNReal.ofReal (2 * r * theta) := by
  apply le_antisymm
  · calc
      (μH[1] : Measure ℂ)
          (unitCircleArc r '' Icc (-r * theta) (r * theta)) ≤
        ENNReal.ofReal (r * theta - (-r * theta)) :=
          hausdorffMeasure_unitCircleArc_image_le hr
      _ = ENNReal.ofReal (2 * r * theta) := by congr 1 <;> ring
  · apply le_of_tendsto'
      (ENNReal.tendsto_ofReal (tendsto_cap_polygon_length (r := r) htheta.1))
    intro n
    exact cap_partition_polygon_lower hr htheta (n + 1) (Nat.zero_lt_succ n)

/-- Rotation of the standard complex circle by the signed-arclength phase `m`. -/
noncomputable def unitCircleArcRotation (r m : ℝ) (z : ℂ) : ℂ :=
  z * Complex.exp (Complex.I * (m / r : ℝ))

lemma isometry_unitCircleArcRotation (r m : ℝ) :
    Isometry (unitCircleArcRotation r m) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [Complex.dist_eq, Complex.dist_eq]
  simp only [unitCircleArcRotation, ← sub_mul, norm_mul, Complex.norm_exp]
  norm_num

lemma unitCircleArcRotation_apply {r : ℝ} (hr : r ≠ 0) (m s : ℝ) :
    unitCircleArcRotation r m (unitCircleArc r s) =
      unitCircleArc r (s + m) := by
  unfold unitCircleArcRotation unitCircleArc
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp

lemma unitCircleArcRotation_image_Icc {r : ℝ} (hr : r ≠ 0)
    (m u v : ℝ) :
    unitCircleArcRotation r m '' (unitCircleArc r '' Icc u v) =
      unitCircleArc r '' Icc (u + m) (v + m) := by
  ext z
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨s + m, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    exact (unitCircleArcRotation_apply hr m s).symm
  · rintro ⟨t, ht, rfl⟩
    refine ⟨unitCircleArc r (t - m), ?_, ?_⟩
    · exact ⟨t - m, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    · rw [unitCircleArcRotation_apply hr]
      congr 1
      ring

/-- Exact H¹ mass of an arbitrary injective signed-arclength interval on a
circle.  The strict span bound rules out wrapping through a full revolution. -/
theorem hausdorffMeasure_unitCircleArc_image_eq_of_span_lt_two_pi
    {r u v : ℝ} (hr : 0 < r) (huv : u < v)
    (hspan : v - u < 2 * Real.pi * r) :
    (μH[1] : Measure ℂ) (unitCircleArc r '' Icc u v) =
      ENNReal.ofReal (v - u) := by
  let theta : ℝ := (v - u) / (2 * r)
  let m : ℝ := (u + v) / 2
  have htheta : theta ∈ Ioo 0 Real.pi := by
    dsimp [theta]
    constructor
    · exact div_pos (sub_pos.mpr huv) (mul_pos (by norm_num) hr)
    · apply (div_lt_iff₀ (mul_pos (by norm_num) hr)).2
      nlinarith [Real.pi_pos]
  have hleft : -r * theta + m = u := by
    dsimp [theta, m]
    field_simp [hr.ne']
    ring
  have hright : r * theta + m = v := by
    dsimp [theta, m]
    field_simp [hr.ne']
    ring
  calc
    (μH[1] : Measure ℂ) (unitCircleArc r '' Icc u v) =
        (μH[1] : Measure ℂ)
          (unitCircleArcRotation r m ''
            (unitCircleArc r '' Icc (-r * theta) (r * theta))) := by
              rw [unitCircleArcRotation_image_Icc hr.ne', hleft, hright]
    _ = (μH[1] : Measure ℂ)
          (unitCircleArc r '' Icc (-r * theta) (r * theta)) :=
      (isometry_unitCircleArcRotation r m).hausdorffMeasure_image
        (Or.inl (by norm_num)) _
    _ = ENNReal.ofReal (2 * r * theta) :=
      hausdorffMeasure_unitCircleArc_image_eq hr htheta
    _ = ENNReal.ofReal (v - u) := by
      congr 1
      dsimp [theta]
      field_simp [hr.ne']


/-- Translation and possible reflection carrying the standard complex circle to a cap. -/
noncomputable def capComplexIsometryMap (c : OneSidedCircularCap) (z : ℂ) :
    EuclideanPlane :=
  match c.side with
  | .upper => WithLp.toLp 2
      (c.midpointX + z.im, c.baseY - c.radius * Real.cos c.theta + z.re)
  | .lower => WithLp.toLp 2
      (c.midpointX + z.im, c.baseY + c.radius * Real.cos c.theta - z.re)

lemma isometry_capComplexIsometryMap (c : OneSidedCircularCap) :
    Isometry (capComplexIsometryMap c) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  simp only [capComplexIsometryMap]
  split <;>
    norm_num [Real.dist_eq, sq_abs] <;>
    rw [← Real.sqrt_eq_rpow, Complex.dist_eq_re_im] <;>
    congr 1 <;> ring

lemma unitCircleArc_eq (r s : ℝ) :
    unitCircleArc r s =
      (r : ℂ) * ((Real.cos (s / r) : ℂ) + (Real.sin (s / r) : ℂ) * Complex.I) := by
  unfold unitCircleArc
  rw [show Complex.I * (s / r : ℝ) = ((s / r : ℝ) : ℂ) * Complex.I by ring]
  rw [Complex.exp_ofReal_mul_I]

lemma unitCircleArc_re (r s : ℝ) :
    (unitCircleArc r s).re = r * Real.cos (s / r) := by
  rw [unitCircleArc_eq]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma unitCircleArc_im (r s : ℝ) :
    (unitCircleArc r s).im = r * Real.sin (s / r) := by
  rw [unitCircleArc_eq]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

noncomputable def realizedCapParam (c : OneSidedCircularCap) (s : ℝ) :
    EuclideanPlane :=
  planeEuclideanHomeomorph (capParam c s)

lemma realizedCapParam_eq (c : OneSidedCircularCap) (s : ℝ) :
    realizedCapParam c s = capComplexIsometryMap c (unitCircleArc c.radius s) := by
  rw [show realizedCapParam c s = WithLp.toLp 2 (capParam c s) by rfl]
  cases hside : c.side <;>
    simp [capParam, OneSidedCircularCap.arcPoint, capComplexIsometryMap,
      unitCircleArc_re, unitCircleArc_im, hside] <;>
    ring

lemma continuous_realizedCapParam (c : OneSidedCircularCap) :
    Continuous (realizedCapParam c) := by
  rw [show realizedCapParam c = capComplexIsometryMap c ∘
      unitCircleArc c.radius by
    funext s
    exact realizedCapParam_eq c s]
  exact (isometry_capComplexIsometryMap c).continuous.comp
    (continuous_unitCircleArc c.radius)

lemma cap_arcLength_eq_two_radius_theta (c : OneSidedCircularCap) :
    c.arcLength = 2 * c.radius * c.theta := by
  rw [OneSidedCircularCap.arcLength, OneSidedCircularCap.radius, ell]
  field_simp [ne_of_gt c.sin_theta_pos]

/-- Exact Euclidean H¹ mass for every existing `OneSidedCircularCap`, including major arcs. -/
theorem exact_euclidean_capParam_hausdorffMeasure (c : OneSidedCircularCap) :
    (μH[1] : Measure EuclideanPlane)
        (realizedCapParam c '' Icc (capStart c) (capEnd c)) =
      ENNReal.ofReal c.arcLength := by
  have hfun : realizedCapParam c = capComplexIsometryMap c ∘ unitCircleArc c.radius := by
    funext s
    exact realizedCapParam_eq c s
  calc
    (μH[1] : Measure EuclideanPlane)
        (realizedCapParam c '' Icc (capStart c) (capEnd c)) =
      (μH[1] : Measure EuclideanPlane)
        (capComplexIsometryMap c ''
          (unitCircleArc c.radius '' Icc (capStart c) (capEnd c))) := by
            rw [hfun]
            congr 1
            simpa only [Function.comp_apply] using (Set.image_image _ _ _).symm
    _ = (μH[1] : Measure ℂ)
        (unitCircleArc c.radius '' Icc (capStart c) (capEnd c)) :=
      (isometry_capComplexIsometryMap c).hausdorffMeasure_image
        (Or.inl (by norm_num)) _
    _ = ENNReal.ofReal (2 * c.radius * c.theta) := by
      simpa [capStart, capEnd] using
        hausdorffMeasure_unitCircleArc_image_eq c.radius_pos
          ⟨c.theta_pos, c.theta_lt_pi⟩
    _ = ENNReal.ofReal c.arcLength := by rw [cap_arcLength_eq_two_radius_theta]


private lemma core_radius_mul_curvature' (c : StripCore) :
    c.radius * c.curvature = 1 := by
  rw [StripCore.radius]
  field_simp [ne_of_gt c.curvature_pos]

private lemma core_angle_mem' {c : StripCore} {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    s / c.radius ∈ Icc (-c.sideAngle) c.sideAngle := by
  have hr := c.radius_pos
  constructor
  · apply (le_div_iff₀ hr).2
    simpa [coreArcStart, mul_comm] using hs.1
  · apply (div_le_iff₀ hr).2
    simpa [coreArcEnd, mul_comm] using hs.2

private lemma coreParam_y_bound' (c : StripCore) {s : ℝ}
    (hs : s ∈ Icc (coreArcStart c) (coreArcEnd c)) :
    |c.radius * Real.sin (s / c.radius)| ≤ 1 := by
  have hu := core_angle_mem' hs
  have habs : |s / c.radius| ≤ c.sideAngle := abs_le.mpr hu
  have hpi : |s / c.radius| ≤ Real.pi := by
    linarith [c.sideAngle_le_pi_div_two, Real.pi_pos]
  have hsin : |Real.sin (s / c.radius)| ≤ Real.sin c.sideAngle := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hpi]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      ((show -(Real.pi / 2) ≤ 0 by linarith [Real.pi_pos]).trans (abs_nonneg _))
      c.sideAngle_le_pi_div_two habs
  rw [abs_mul, abs_of_pos c.radius_pos]
  calc
    c.radius * |Real.sin (s / c.radius)| ≤ c.radius * Real.sin c.sideAngle :=
      mul_le_mul_of_nonneg_left hsin c.radius_pos.le
    _ = 1 := by rw [c.sin_sideAngle, core_radius_mul_curvature' c]

theorem leftCoreParam_image_Icc (c : StripCore) :
    leftCoreParam c '' Icc (coreArcStart c) (coreArcEnd c) =
      c.leftArcTrace := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hu := core_angle_mem' hs
    have htrig := Real.sin_sq_add_cos_sq (s / c.radius)
    have hcircle :
        ((leftCoreParam c s).1 - c.leftCenterX) ^ 2 +
          (leftCoreParam c s).2 ^ 2 = c.radius ^ 2 := by
      simp only [leftCoreParam, Prod.fst, Prod.snd]
      nlinarith [sq_nonneg c.radius]
    have habs : |s / c.radius| ≤ c.sideAngle := abs_le.mpr hu
    have hcos : Real.cos c.sideAngle ≤ Real.cos (s / c.radius) := by
      simpa only [Real.cos_abs] using
        (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (s / c.radius))
          c.sideAngle_lt_pi.le habs)
    have hx : (leftCoreParam c s).1 ≤ -c.chord / 2 := by
      simp only [leftCoreParam, Prod.fst]
      unfold StripCore.leftCenterX
      nlinarith [mul_le_mul_of_nonneg_left hcos c.radius_pos.le]
    exact ⟨hcircle, hx, coreParam_y_bound' c hs⟩
  · intro hp
    change (p.1 - c.leftCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      p.1 ≤ -c.chord / 2 ∧ |p.2| ≤ 1 at hp
    let u : ℝ := Real.arcsin (p.2 / c.radius)
    have hp2 := abs_le.mp hp.2.2
    have hlo : -c.curvature ≤ p.2 / c.radius := by
      apply (le_div_iff₀ c.radius_pos).2
      nlinarith [core_radius_mul_curvature' c]
    have hhi : p.2 / c.radius ≤ c.curvature := by
      apply (div_le_iff₀ c.radius_pos).2
      nlinarith [core_radius_mul_curvature' c]
    have hu : u ∈ Icc (-c.sideAngle) c.sideAngle := by
      constructor
      · simpa [u, StripCore.sideAngle] using Real.arcsin_le_arcsin hlo
      · simpa [u, StripCore.sideAngle] using Real.arcsin_le_arcsin hhi
    have hratio : p.2 / c.radius ∈ Icc (-1 : ℝ) 1 :=
      ⟨(by linarith [c.curvature_le_one] : (-1 : ℝ) ≤ -c.curvature) |>.trans hlo,
        hhi.trans c.curvature_le_one⟩
    have hsinu : Real.sin u = p.2 / c.radius :=
      Real.sin_arcsin hratio.1 hratio.2
    have hy : c.radius * Real.sin u = p.2 := by
      rw [hsinu]
      field_simp [ne_of_gt c.radius_pos]
    have hcostheta : 0 ≤ Real.cos c.sideAngle :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [c.sideAngle_pos, Real.pi_pos],
          c.sideAngle_le_pi_div_two⟩
    have hxu : p.1 - c.leftCenterX ≤ 0 := by
      unfold StripCore.leftCenterX
      nlinarith [mul_nonneg c.radius_pos.le hcostheta]
    have hcosu : 0 ≤ Real.cos u :=
      Real.cos_nonneg_of_mem_Icc
        ⟨(neg_le_neg c.sideAngle_le_pi_div_two).trans hu.1,
          hu.2.trans c.sideAngle_le_pi_div_two⟩
    have htrig := Real.sin_sq_add_cos_sq u
    have hsquares :
        (p.1 - c.leftCenterX) ^ 2 = (c.radius * Real.cos u) ^ 2 := by
      calc
        _ = c.radius ^ 2 - p.2 ^ 2 := by nlinarith [hp.1]
        _ = (c.radius * Real.cos u) ^ 2 := by rw [← hy]; nlinarith
    have hcosprod : 0 ≤ c.radius * Real.cos u :=
      mul_nonneg c.radius_pos.le hcosu
    have hx : p.1 = c.leftCenterX - c.radius * Real.cos u := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hpos | hneg
      · have hz : p.1 - c.leftCenterX = 0 := by nlinarith
        nlinarith
      · linarith
    refine ⟨c.radius * u, ?_, ?_⟩
    · change -c.radius * c.sideAngle ≤ c.radius * u ∧
        c.radius * u ≤ c.radius * c.sideAngle
      constructor <;> nlinarith [c.radius_pos, hu.1, hu.2]
    · have hdiv : c.radius * u / c.radius = u := by
        field_simp [ne_of_gt c.radius_pos]
      apply Prod.ext
      · simp [leftCoreParam, hdiv, hx]
      · simp [leftCoreParam, hdiv, hy]

theorem rightCoreParam_image_Icc (c : StripCore) :
    rightCoreParam c '' Icc (coreArcStart c) (coreArcEnd c) =
      c.rightArcTrace := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hu := core_angle_mem' hs
    have htrig := Real.sin_sq_add_cos_sq (s / c.radius)
    have hcircle :
        ((rightCoreParam c s).1 - c.rightCenterX) ^ 2 +
          (rightCoreParam c s).2 ^ 2 = c.radius ^ 2 := by
      simp only [rightCoreParam, Prod.fst, Prod.snd]
      nlinarith [sq_nonneg c.radius]
    have habs : |s / c.radius| ≤ c.sideAngle := abs_le.mpr hu
    have hcos : Real.cos c.sideAngle ≤ Real.cos (s / c.radius) := by
      simpa only [Real.cos_abs] using
        (Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (s / c.radius))
          c.sideAngle_lt_pi.le habs)
    have hx : c.chord / 2 ≤ (rightCoreParam c s).1 := by
      simp only [rightCoreParam, Prod.fst]
      unfold StripCore.rightCenterX
      nlinarith [mul_le_mul_of_nonneg_left hcos c.radius_pos.le]
    exact ⟨hcircle, hx, coreParam_y_bound' c hs⟩
  · intro hp
    change (p.1 - c.rightCenterX) ^ 2 + p.2 ^ 2 = c.radius ^ 2 ∧
      c.chord / 2 ≤ p.1 ∧ |p.2| ≤ 1 at hp
    let u : ℝ := Real.arcsin (p.2 / c.radius)
    have hp2 := abs_le.mp hp.2.2
    have hlo : -c.curvature ≤ p.2 / c.radius := by
      apply (le_div_iff₀ c.radius_pos).2
      nlinarith [core_radius_mul_curvature' c]
    have hhi : p.2 / c.radius ≤ c.curvature := by
      apply (div_le_iff₀ c.radius_pos).2
      nlinarith [core_radius_mul_curvature' c]
    have hu : u ∈ Icc (-c.sideAngle) c.sideAngle := by
      constructor
      · simpa [u, StripCore.sideAngle] using Real.arcsin_le_arcsin hlo
      · simpa [u, StripCore.sideAngle] using Real.arcsin_le_arcsin hhi
    have hratio : p.2 / c.radius ∈ Icc (-1 : ℝ) 1 :=
      ⟨(by linarith [c.curvature_le_one] : (-1 : ℝ) ≤ -c.curvature) |>.trans hlo,
        hhi.trans c.curvature_le_one⟩
    have hsinu : Real.sin u = p.2 / c.radius :=
      Real.sin_arcsin hratio.1 hratio.2
    have hy : c.radius * Real.sin u = p.2 := by
      rw [hsinu]
      field_simp [ne_of_gt c.radius_pos]
    have hcostheta : 0 ≤ Real.cos c.sideAngle :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [c.sideAngle_pos, Real.pi_pos],
          c.sideAngle_le_pi_div_two⟩
    have hxu : 0 ≤ p.1 - c.rightCenterX := by
      unfold StripCore.rightCenterX
      nlinarith [mul_nonneg c.radius_pos.le hcostheta]
    have hcosu : 0 ≤ Real.cos u :=
      Real.cos_nonneg_of_mem_Icc
        ⟨(neg_le_neg c.sideAngle_le_pi_div_two).trans hu.1,
          hu.2.trans c.sideAngle_le_pi_div_two⟩
    have htrig := Real.sin_sq_add_cos_sq u
    have hsquares :
        (p.1 - c.rightCenterX) ^ 2 = (c.radius * Real.cos u) ^ 2 := by
      calc
        _ = c.radius ^ 2 - p.2 ^ 2 := by nlinarith [hp.1]
        _ = (c.radius * Real.cos u) ^ 2 := by rw [← hy]; nlinarith
    have hcosprod : 0 ≤ c.radius * Real.cos u :=
      mul_nonneg c.radius_pos.le hcosu
    have hx : p.1 = c.rightCenterX + c.radius * Real.cos u := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hpos | hneg
      · linarith
      · have hz : p.1 - c.rightCenterX = 0 := by nlinarith
        nlinarith
    refine ⟨c.radius * u, ?_, ?_⟩
    · change -c.radius * c.sideAngle ≤ c.radius * u ∧
        c.radius * u ≤ c.radius * c.sideAngle
      constructor <;> nlinarith [c.radius_pos, hu.1, hu.2]
    · have hdiv : c.radius * u / c.radius = u := by
        field_simp [ne_of_gt c.radius_pos]
      apply Prod.ext
      · simp [rightCoreParam, hdiv, hx]
      · simp [rightCoreParam, hdiv, hy]

noncomputable def leftCoreComplexIsometryMap (c : StripCore) (z : ℂ) :
    EuclideanPlane :=
  WithLp.toLp 2 (c.leftCenterX - z.re, z.im)

noncomputable def rightCoreComplexIsometryMap (c : StripCore) (z : ℂ) :
    EuclideanPlane :=
  WithLp.toLp 2 (c.rightCenterX + z.re, z.im)

lemma isometry_leftCoreComplexIsometryMap (c : StripCore) :
    Isometry (leftCoreComplexIsometryMap c) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  simp only [leftCoreComplexIsometryMap]
  norm_num [Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow, Complex.dist_eq_re_im]
  congr 1
  ring

lemma isometry_rightCoreComplexIsometryMap (c : StripCore) :
    Isometry (rightCoreComplexIsometryMap c) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  simp only [rightCoreComplexIsometryMap]
  norm_num [Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow, Complex.dist_eq_re_im]

noncomputable def realizedLeftCoreParam (c : StripCore) (s : ℝ) :
    EuclideanPlane :=
  planeEuclideanHomeomorph (leftCoreParam c s)

noncomputable def realizedRightCoreParam (c : StripCore) (s : ℝ) :
    EuclideanPlane :=
  planeEuclideanHomeomorph (rightCoreParam c s)

lemma realizedLeftCoreParam_eq (c : StripCore) (s : ℝ) :
    realizedLeftCoreParam c s =
      leftCoreComplexIsometryMap c (unitCircleArc c.radius s) := by
  rw [show realizedLeftCoreParam c s = WithLp.toLp 2 (leftCoreParam c s) by rfl]
  simp [leftCoreParam, leftCoreComplexIsometryMap,
    unitCircleArc_re, unitCircleArc_im]

lemma realizedRightCoreParam_eq (c : StripCore) (s : ℝ) :
    realizedRightCoreParam c s =
      rightCoreComplexIsometryMap c (unitCircleArc c.radius s) := by
  rw [show realizedRightCoreParam c s = WithLp.toLp 2 (rightCoreParam c s) by rfl]
  simp [rightCoreParam, rightCoreComplexIsometryMap,
    unitCircleArc_re, unitCircleArc_im]

lemma continuous_realizedLeftCoreParam (c : StripCore) :
    Continuous (realizedLeftCoreParam c) := by
  rw [show realizedLeftCoreParam c = leftCoreComplexIsometryMap c ∘
      unitCircleArc c.radius by
    funext s
    exact realizedLeftCoreParam_eq c s]
  exact (isometry_leftCoreComplexIsometryMap c).continuous.comp
    (continuous_unitCircleArc c.radius)

lemma continuous_realizedRightCoreParam (c : StripCore) :
    Continuous (realizedRightCoreParam c) := by
  rw [show realizedRightCoreParam c = rightCoreComplexIsometryMap c ∘
      unitCircleArc c.radius by
    funext s
    exact realizedRightCoreParam_eq c s]
  exact (isometry_rightCoreComplexIsometryMap c).continuous.comp
    (continuous_unitCircleArc c.radius)

theorem exact_euclidean_leftCoreParam_hausdorffMeasure (c : StripCore) :
    (μH[1] : Measure EuclideanPlane)
      (realizedLeftCoreParam c '' Icc (coreArcStart c) (coreArcEnd c)) =
      ENNReal.ofReal (coreArcEnd c - coreArcStart c) := by
  have hfun : realizedLeftCoreParam c =
      leftCoreComplexIsometryMap c ∘ unitCircleArc c.radius := by
    funext s
    exact realizedLeftCoreParam_eq c s
  calc
    _ = (μH[1] : Measure EuclideanPlane)
        (leftCoreComplexIsometryMap c ''
          (unitCircleArc c.radius '' Icc (coreArcStart c) (coreArcEnd c))) := by
      rw [hfun]
      congr 1
      simpa only [Function.comp_apply] using (Set.image_image _ _ _).symm
    _ = (μH[1] : Measure ℂ)
        (unitCircleArc c.radius '' Icc (coreArcStart c) (coreArcEnd c)) :=
      (isometry_leftCoreComplexIsometryMap c).hausdorffMeasure_image
        (Or.inl (by norm_num)) _
    _ = ENNReal.ofReal (2 * c.radius * c.sideAngle) := by
      simpa [coreArcStart, coreArcEnd] using
        hausdorffMeasure_unitCircleArc_image_eq c.radius_pos
          ⟨c.sideAngle_pos, c.sideAngle_lt_pi⟩
    _ = ENNReal.ofReal (coreArcEnd c - coreArcStart c) := by
      congr 1
      simp only [coreArcStart, coreArcEnd]
      ring

theorem exact_euclidean_rightCoreParam_hausdorffMeasure (c : StripCore) :
    (μH[1] : Measure EuclideanPlane)
      (realizedRightCoreParam c '' Icc (coreArcStart c) (coreArcEnd c)) =
      ENNReal.ofReal (coreArcEnd c - coreArcStart c) := by
  have hfun : realizedRightCoreParam c =
      rightCoreComplexIsometryMap c ∘ unitCircleArc c.radius := by
    funext s
    exact realizedRightCoreParam_eq c s
  calc
    _ = (μH[1] : Measure EuclideanPlane)
        (rightCoreComplexIsometryMap c ''
          (unitCircleArc c.radius '' Icc (coreArcStart c) (coreArcEnd c))) := by
      rw [hfun]
      congr 1
      simpa only [Function.comp_apply] using (Set.image_image _ _ _).symm
    _ = (μH[1] : Measure ℂ)
        (unitCircleArc c.radius '' Icc (coreArcStart c) (coreArcEnd c)) :=
      (isometry_rightCoreComplexIsometryMap c).hausdorffMeasure_image
        (Or.inl (by norm_num)) _
    _ = ENNReal.ofReal (2 * c.radius * c.sideAngle) := by
      simpa [coreArcStart, coreArcEnd] using
        hausdorffMeasure_unitCircleArc_image_eq c.radius_pos
          ⟨c.sideAngle_pos, c.sideAngle_lt_pi⟩
    _ = ENNReal.ofReal (coreArcEnd c - coreArcStart c) := by
      congr 1
      simp only [coreArcStart, coreArcEnd]
      ring

theorem realizedLeftCoreParam_image_Icc (c : StripCore) :
    realizedLeftCoreParam c '' Icc (coreArcStart c) (coreArcEnd c) =
      planeEuclideanHomeomorph '' c.leftArcTrace := by
  calc
    _ = planeEuclideanHomeomorph ''
        (leftCoreParam c '' Icc (coreArcStart c) (coreArcEnd c)) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [leftCoreParam_image_Icc]

theorem realizedRightCoreParam_image_Icc (c : StripCore) :
    realizedRightCoreParam c '' Icc (coreArcStart c) (coreArcEnd c) =
      planeEuclideanHomeomorph '' c.rightArcTrace := by
  calc
    _ = planeEuclideanHomeomorph ''
        (rightCoreParam c '' Icc (coreArcStart c) (coreArcEnd c)) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [rightCoreParam_image_Icc]

theorem exact_euclidean_leftArcTrace_hausdorffMeasure (c : StripCore) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' c.leftArcTrace) =
      ENNReal.ofReal (coreArcEnd c - coreArcStart c) := by
  rw [← realizedLeftCoreParam_image_Icc]
  exact exact_euclidean_leftCoreParam_hausdorffMeasure c

theorem exact_euclidean_rightArcTrace_hausdorffMeasure (c : StripCore) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' c.rightArcTrace) =
      ENNReal.ofReal (coreArcEnd c - coreArcStart c) := by
  rw [← realizedRightCoreParam_image_Icc]
  exact exact_euclidean_rightCoreParam_hausdorffMeasure c

theorem segmentParam_image_Icc (seg : HorizontalSegment) :
    segmentParam seg '' Icc (segmentStart seg) (segmentEnd seg) = seg.carrier := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : -seg.chord / 2 ≤ s ∧ s ≤ seg.chord / 2 := by
      simpa only [segmentStart, segmentEnd, mem_Icc] using hs
    have habs : |s| ≤ seg.chord / 2 := by
      rw [abs_le]
      constructor <;> linarith [hs'.1]
    change seg.baseY = seg.baseY ∧
      |seg.midpointX + s - seg.midpointX| ≤ seg.chord / 2
    rw [add_sub_cancel_left]
    exact ⟨rfl, habs⟩
  · intro hp
    change p.2 = seg.baseY ∧ |p.1 - seg.midpointX| ≤ seg.chord / 2 at hp
    refine ⟨p.1 - seg.midpointX, ?_, ?_⟩
    · have hb := abs_le.mp hp.2
      simpa only [segmentStart, segmentEnd, mem_Icc]
        using (show -seg.chord / 2 ≤ p.1 - seg.midpointX ∧
          p.1 - seg.midpointX ≤ seg.chord / 2 by
            constructor <;> linarith [hb.1])
    · apply Prod.ext
      · simp [segmentParam]
      · simpa [segmentParam] using hp.1.symm

@[simp] lemma planeEuclideanHomeomorph_apply (p : PlanePoint) :
    planeEuclideanHomeomorph p = WithLp.toLp 2 p := rfl

noncomputable def realizedSegmentParam (seg : HorizontalSegment) (s : ℝ) :
    EuclideanPlane :=
  planeEuclideanHomeomorph (segmentParam seg s)

lemma continuous_realizedSegmentParam (seg : HorizontalSegment) :
    Continuous (realizedSegmentParam seg) := by
  unfold realizedSegmentParam segmentParam
  fun_prop

theorem realizedSegmentParam_image_affineSegment (seg : HorizontalSegment) :
    realizedSegmentParam seg '' Icc (segmentStart seg) (segmentEnd seg) =
      affineSegment ℝ
        (planeEuclideanHomeomorph seg.leftEndpoint)
        (planeEuclideanHomeomorph seg.rightEndpoint) := by
  rw [affineSegment]
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : -seg.chord / 2 ≤ s ∧ s ≤ seg.chord / 2 := by
      simpa only [segmentStart, segmentEnd, mem_Icc] using hs
    let t : ℝ := (s + seg.chord / 2) / seg.chord
    refine ⟨t, ?_, ?_⟩
    · constructor
      · exact div_nonneg (by linarith) seg.chord_pos.le
      · exact (div_le_one seg.chord_pos).2 (by linarith)
    · rw [AffineMap.lineMap_apply_module, WithLp.ext_iff]
      apply Prod.ext
      · simp [realizedSegmentParam, planeEuclideanHomeomorph_apply, segmentParam,
          HorizontalSegment.leftEndpoint, HorizontalSegment.rightEndpoint, t]
        field_simp [ne_of_gt seg.chord_pos]
        ring
      · simp [realizedSegmentParam, planeEuclideanHomeomorph_apply, segmentParam,
          HorizontalSegment.leftEndpoint, HorizontalSegment.rightEndpoint]
        ring
  · rintro ⟨t, ht, rfl⟩
    let s : ℝ := -seg.chord / 2 + t * seg.chord
    refine ⟨s, ?_, ?_⟩
    · change -seg.chord / 2 ≤ s ∧ s ≤ seg.chord / 2
      dsimp [s]
      constructor <;> nlinarith [seg.chord_pos, ht.1, ht.2]
    · rw [AffineMap.lineMap_apply_module, WithLp.ext_iff]
      apply Prod.ext
      · simp [realizedSegmentParam, planeEuclideanHomeomorph_apply, segmentParam,
          HorizontalSegment.leftEndpoint, HorizontalSegment.rightEndpoint, s]
        ring
      · simp [realizedSegmentParam, planeEuclideanHomeomorph_apply, segmentParam,
          HorizontalSegment.leftEndpoint, HorizontalSegment.rightEndpoint]
        ring

theorem realizedSegmentParam_image_carrier (seg : HorizontalSegment) :
    realizedSegmentParam seg '' Icc (segmentStart seg) (segmentEnd seg) =
      planeEuclideanHomeomorph '' seg.carrier := by
  calc
    _ = planeEuclideanHomeomorph ''
        (segmentParam seg '' Icc (segmentStart seg) (segmentEnd seg)) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [segmentParam_image_Icc]

lemma segmentEndpoint_edist (seg : HorizontalSegment) :
    edist (planeEuclideanHomeomorph seg.leftEndpoint)
      (planeEuclideanHomeomorph seg.rightEndpoint) =
      ENNReal.ofReal seg.euclideanLength := by
  rw [edist_dist, WithLp.prod_dist_eq_add (by norm_num)]
  simp only [planeEuclideanHomeomorph_apply]
  norm_num [Real.dist_eq, HorizontalSegment.leftEndpoint,
    HorizontalSegment.rightEndpoint, HorizontalSegment.euclideanLength]
  congr 1
  have h : seg.midpointX -
      (seg.midpointX + seg.chord / 2 + seg.chord / 2) = -seg.chord := by ring
  rw [h, neg_sq, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
    abs_of_pos seg.chord_pos]

theorem exact_euclidean_segmentCarrier_hausdorffMeasure
    (seg : HorizontalSegment) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' seg.carrier) =
      ENNReal.ofReal seg.euclideanLength := by
  rw [← realizedSegmentParam_image_carrier,
    realizedSegmentParam_image_affineSegment,
    hausdorffMeasure_affineSegment,
    segmentEndpoint_edist]

theorem capParam_image_Icc_eq_arcTrace (c : OneSidedCircularCap) :
    capParam c '' Icc (capStart c) (capEnd c) = c.arcTrace := by
  apply Set.Subset.antisymm
  · rintro p ⟨s, hs, rfl⟩
    have ht : s / c.radius ∈ Icc (-c.theta) c.theta := by
      have hr := c.radius_pos
      constructor
      · apply (le_div_iff₀ hr).2
        simpa [capStart, mul_comm] using hs.1
      · apply (div_le_iff₀ hr).2
        simpa [capEnd, mul_comm] using hs.2
    have habs : |s / c.radius| ≤ c.theta := (abs_le).2 ht
    constructor
    · cases hside : c.side <;>
        simp only [capParam, OneSidedCircularCap.radiusSquaredAt,
          OneSidedCircularCap.center, OneSidedCircularCap.arcPoint, hside]
      all_goals
        nlinarith [Real.sin_sq_add_cos_sq (s / c.radius)]
    · exact c.arcPoint_in_closed_side habs
  · intro p hp
    cases hside : c.side with
    | upper =>
        let z : ℂ := ⟨p.2 - (c.baseY - c.radius * Real.cos c.theta),
          p.1 - c.midpointX⟩
        have hcircle :
            (p.1 - c.midpointX) ^ 2 +
                (p.2 - (c.baseY - c.radius * Real.cos c.theta)) ^ 2 =
              c.radius ^ 2 := by
          simpa [OneSidedCircularCap.arcTrace,
            OneSidedCircularCap.radiusSquaredAt,
            OneSidedCircularCap.center, hside] using hp.1
        have hnorm_sq : ‖z‖ ^ 2 = c.radius ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [z]
          nlinarith
        have hnorm : ‖z‖ = c.radius := by
          nlinarith [norm_nonneg z, c.radius_pos]
        have hsin :
            c.radius * Real.sin z.arg = p.1 - c.midpointX := by
          simpa [hnorm, z] using Complex.norm_mul_sin_arg z
        have hcos :
            c.radius * Real.cos z.arg =
              p.2 - (c.baseY - c.radius * Real.cos c.theta) := by
          simpa [hnorm, z] using Complex.norm_mul_cos_arg z
        have hsidep : c.baseY ≤ p.2 := by
          simpa [OneSidedCircularCap.arcTrace, hside] using hp.2
        have hcos_le : Real.cos c.theta ≤ Real.cos z.arg := by
          nlinarith [c.radius_pos]
        have harg : |z.arg| ≤ c.theta := by
          by_contra h
          have hlt : c.theta < |z.arg| := lt_of_not_ge h
          have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
            (le_of_lt c.theta_pos) (Complex.abs_arg_le_pi z) hlt
          rw [Real.cos_abs] at hc
          linarith
        let s := c.radius * z.arg
        have hs : s ∈ Icc (capStart c) (capEnd c) := by
          rcases (abs_le.mp harg) with ⟨hl, hu⟩
          dsimp [s]
          constructor <;> simp only [capStart, capEnd] <;>
            nlinarith [c.radius_pos]
        refine ⟨s, hs, ?_⟩
        have hangle : s / c.radius = z.arg := by
          dsimp [s]
          field_simp [ne_of_gt c.radius_pos]
        apply Prod.ext
        · simp only [capParam, OneSidedCircularCap.arcPoint, hside,
            hangle]
          linarith
        · simp only [capParam, OneSidedCircularCap.arcPoint, hside,
            hangle]
          linarith
    | lower =>
        let z : ℂ := ⟨(c.baseY + c.radius * Real.cos c.theta) - p.2,
          p.1 - c.midpointX⟩
        have hcircle :
            (p.1 - c.midpointX) ^ 2 +
                (p.2 - (c.baseY + c.radius * Real.cos c.theta)) ^ 2 =
              c.radius ^ 2 := by
          simpa [OneSidedCircularCap.arcTrace,
            OneSidedCircularCap.radiusSquaredAt,
            OneSidedCircularCap.center, hside] using hp.1
        have hnorm_sq : ‖z‖ ^ 2 = c.radius ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [z]
          nlinarith
        have hnorm : ‖z‖ = c.radius := by
          nlinarith [norm_nonneg z, c.radius_pos]
        have hsin :
            c.radius * Real.sin z.arg = p.1 - c.midpointX := by
          simpa [hnorm, z] using Complex.norm_mul_sin_arg z
        have hcos :
            c.radius * Real.cos z.arg =
              (c.baseY + c.radius * Real.cos c.theta) - p.2 := by
          simpa [hnorm, z] using Complex.norm_mul_cos_arg z
        have hsidep : p.2 ≤ c.baseY := by
          simpa [OneSidedCircularCap.arcTrace, hside] using hp.2
        have hcos_le : Real.cos c.theta ≤ Real.cos z.arg := by
          nlinarith [c.radius_pos]
        have harg : |z.arg| ≤ c.theta := by
          by_contra h
          have hlt : c.theta < |z.arg| := lt_of_not_ge h
          have hc := Real.cos_lt_cos_of_nonneg_of_le_pi
            (le_of_lt c.theta_pos) (Complex.abs_arg_le_pi z) hlt
          rw [Real.cos_abs] at hc
          linarith
        let s := c.radius * z.arg
        have hs : s ∈ Icc (capStart c) (capEnd c) := by
          rcases (abs_le.mp harg) with ⟨hl, hu⟩
          dsimp [s]
          constructor <;> simp only [capStart, capEnd] <;>
            nlinarith [c.radius_pos]
        refine ⟨s, hs, ?_⟩
        have hangle : s / c.radius = z.arg := by
          dsimp [s]
          field_simp [ne_of_gt c.radius_pos]
        apply Prod.ext
        · simp only [capParam, OneSidedCircularCap.arcPoint, hside,
            hangle]
          linarith
        · simp only [capParam, OneSidedCircularCap.arcPoint, hside,
            hangle]
          linarith

theorem realizedCapParam_image_Icc (c : OneSidedCircularCap) :
    realizedCapParam c '' Icc (capStart c) (capEnd c) =
      planeEuclideanHomeomorph '' c.arcTrace := by
  calc
    _ = planeEuclideanHomeomorph ''
        (capParam c '' Icc (capStart c) (capEnd c)) := by
      rw [Set.image_image]
      rfl
    _ = _ := by rw [capParam_image_Icc_eq_arcTrace]

theorem exact_euclidean_capTrace_hausdorffMeasure
    (c : OneSidedCircularCap) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' c.arcTrace) =
      ENNReal.ofReal c.arcLength := by
  rw [← realizedCapParam_image_Icc]
  exact exact_euclidean_capParam_hausdorffMeasure c

theorem measurableSet_euclidean_leftArcTrace (c : StripCore) :
    MeasurableSet (planeEuclideanHomeomorph '' c.leftArcTrace) := by
  rw [← realizedLeftCoreParam_image_Icc]
  exact (isCompact_Icc.image (continuous_realizedLeftCoreParam c)).measurableSet

theorem measurableSet_euclidean_rightArcTrace (c : StripCore) :
    MeasurableSet (planeEuclideanHomeomorph '' c.rightArcTrace) := by
  rw [← realizedRightCoreParam_image_Icc]
  exact (isCompact_Icc.image (continuous_realizedRightCoreParam c)).measurableSet

theorem measurableSet_euclidean_segmentCarrier (seg : HorizontalSegment) :
    MeasurableSet (planeEuclideanHomeomorph '' seg.carrier) := by
  rw [← realizedSegmentParam_image_carrier]
  exact (isCompact_Icc.image (continuous_realizedSegmentParam seg)).measurableSet

theorem measurableSet_euclidean_capTrace (c : OneSidedCircularCap) :
    MeasurableSet (planeEuclideanHomeomorph '' c.arcTrace) := by
  rw [← realizedCapParam_image_Icc]
  exact (isCompact_Icc.image (continuous_realizedCapParam c)).measurableSet

/-- Union of all six pairwise intersections of four primitive traces. -/
def pairwiseOverlap (A B C D : Set PlanePoint) : Set PlanePoint :=
  (A ∩ B) ∪ ((A ∩ C) ∪ ((A ∩ D) ∪
    ((B ∩ C) ∪ ((B ∩ D) ∪ (C ∩ D)))))

/-- The four possible primitive joins in either assembly. -/
def joinSet (q : ℝ) : Set PlanePoint :=
  {(-q / 2, 1), (q / 2, 1), (-q / 2, -1), (q / 2, -1)}

private lemma eq_left_of_bounds {q x : ℝ} (hx : x ≤ -q / 2)
    (hab : |x| ≤ q / 2) : x = -q / 2 := by
  linarith [(abs_le.mp hab).1]

private lemma eq_right_of_bounds {q x : ℝ} (hx : q / 2 ≤ x)
    (hab : |x| ≤ q / 2) : x = q / 2 := by
  exact le_antisymm (abs_le.mp hab).2 hx

private lemma four_upper_arc_x_bound (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ OneSidedCircularCap.arcTrace a.upperCap)
    (hy : p.2 = 1) : |p.1| ≤ a.core.chord / 2 := by
  have hcarrier : p ∈ a.upperCap.carrier := ⟨hp.1.le, hp.2⟩
  have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
    hcarrier (by simpa [FourArcAssembly.upperCap] using hy)
  simpa [FourArcAssembly.upperCap] using hchord.2

private lemma four_lower_arc_x_bound (a : FourArcAssembly) {p : PlanePoint}
    (hp : p ∈ OneSidedCircularCap.arcTrace a.lowerCap)
    (hy : p.2 = -1) : |p.1| ≤ a.core.chord / 2 := by
  have hcarrier : p ∈ a.lowerCap.carrier := ⟨hp.1.le, hp.2⟩
  have hchord := a.lowerCap.mem_chordCarrier_of_mem_carrier_of_eq_base
    hcarrier (by simpa [FourArcAssembly.lowerCap] using hy)
  simpa [FourArcAssembly.lowerCap] using hchord.2

theorem fourArc_pairwiseOverlap_subset_joinSet (a : FourArcAssembly) :
    pairwiseOverlap
      (StripCore.leftArcTrace a.core)
      (StripCore.rightArcTrace a.core)
      (OneSidedCircularCap.arcTrace a.upperCap)
      (OneSidedCircularCap.arcTrace a.lowerCap) ⊆
        joinSet a.core.chord := by
  intro p hp
  simp only [pairwiseOverlap, mem_union, mem_inter_iff] at hp
  rcases hp with hLR | hLU | hLL | hRU | hRL | hUL
  · exact False.elim (by
      have hl := hLR.1.2.1
      have hr := hLR.2.2.1
      linarith [a.core.chord_pos])
  · have hyCore : p.2 ≤ 1 := (le_abs_self p.2).trans hLU.1.2.2
    have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [FourArcAssembly.upperCap] using hLU.2.2
    have hy : p.2 = 1 := le_antisymm hyCore hyCap
    have hxBound := four_upper_arc_x_bound a hLU.2 hy
    have hx := eq_left_of_bounds hLU.1.2.1 hxBound
    have hpEq : p = (-a.core.chord / 2, 1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hyCore : -1 ≤ p.2 := by
      linarith [(neg_le_abs p.2).trans hLL.1.2.2]
    have hyCap : p.2 ≤ (-1 : ℝ) := by
      simpa [FourArcAssembly.lowerCap] using hLL.2.2
    have hy : p.2 = -1 := le_antisymm hyCap hyCore
    have hxBound := four_lower_arc_x_bound a hLL.2 hy
    have hx := eq_left_of_bounds hLL.1.2.1 hxBound
    have hpEq : p = (-a.core.chord / 2, -1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hyCore : p.2 ≤ 1 := (le_abs_self p.2).trans hRU.1.2.2
    have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [FourArcAssembly.upperCap] using hRU.2.2
    have hy : p.2 = 1 := le_antisymm hyCore hyCap
    have hxBound := four_upper_arc_x_bound a hRU.2 hy
    have hx := eq_right_of_bounds hRU.1.2.1 hxBound
    have hpEq : p = (a.core.chord / 2, 1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hyCore : -1 ≤ p.2 := by
      linarith [(neg_le_abs p.2).trans hRL.1.2.2]
    have hyCap : p.2 ≤ (-1 : ℝ) := by
      simpa [FourArcAssembly.lowerCap] using hRL.2.2
    have hy : p.2 = -1 := le_antisymm hyCap hyCore
    have hxBound := four_lower_arc_x_bound a hRL.2 hy
    have hx := eq_right_of_bounds hRL.1.2.1 hxBound
    have hpEq : p = (a.core.chord / 2, -1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hyUpper : (1 : ℝ) ≤ p.2 := by
      simpa [FourArcAssembly.upperCap] using hUL.1.2
    have hyLower : p.2 ≤ (-1 : ℝ) := by
      simpa [FourArcAssembly.lowerCap] using hUL.2.2
    linarith

private lemma replacement_upper_arc_x_bound (a : ReplacementAssembly)
    {p : PlanePoint} (hp : p ∈ OneSidedCircularCap.arcTrace a.upperCap)
    (hy : p.2 = 1) : |p.1| ≤ a.core.chord / 2 := by
  have hcarrier : p ∈ a.upperCap.carrier := ⟨hp.1.le, hp.2⟩
  have hchord := a.upperCap.mem_chordCarrier_of_mem_carrier_of_eq_base
    hcarrier (by simpa [ReplacementAssembly.upperCap] using hy)
  simpa [ReplacementAssembly.upperCap] using hchord.2

theorem replacement_pairwiseOverlap_subset_joinSet (a : ReplacementAssembly) :
    pairwiseOverlap
      (StripCore.leftArcTrace a.core)
      (StripCore.rightArcTrace a.core)
      (OneSidedCircularCap.arcTrace a.upperCap)
      a.exposedLowerChord.carrier ⊆ joinSet a.core.chord := by
  intro p hp
  simp only [pairwiseOverlap, mem_union, mem_inter_iff] at hp
  rcases hp with hLR | hLU | hLS | hRU | hRS | hUS
  · exact False.elim (by
      have hl := hLR.1.2.1
      have hr := hLR.2.2.1
      linarith [a.core.chord_pos])
  · have hyCore : p.2 ≤ 1 := (le_abs_self p.2).trans hLU.1.2.2
    have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [ReplacementAssembly.upperCap] using hLU.2.2
    have hy : p.2 = 1 := le_antisymm hyCore hyCap
    have hxBound := replacement_upper_arc_x_bound a hLU.2 hy
    have hx := eq_left_of_bounds hLU.1.2.1 hxBound
    have hpEq : p = (-a.core.chord / 2, 1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hy : p.2 = -1 := by
      simpa [ReplacementAssembly.exposedLowerChord] using hLS.2.1
    have hxBound : |p.1| ≤ a.core.chord / 2 := by
      simpa [ReplacementAssembly.exposedLowerChord] using hLS.2.2
    have hx := eq_left_of_bounds hLS.1.2.1 hxBound
    have hpEq : p = (-a.core.chord / 2, -1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hyCore : p.2 ≤ 1 := (le_abs_self p.2).trans hRU.1.2.2
    have hyCap : (1 : ℝ) ≤ p.2 := by
      simpa [ReplacementAssembly.upperCap] using hRU.2.2
    have hy : p.2 = 1 := le_antisymm hyCore hyCap
    have hxBound := replacement_upper_arc_x_bound a hRU.2 hy
    have hx := eq_right_of_bounds hRU.1.2.1 hxBound
    have hpEq : p = (a.core.chord / 2, 1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hy : p.2 = -1 := by
      simpa [ReplacementAssembly.exposedLowerChord] using hRS.2.1
    have hxBound : |p.1| ≤ a.core.chord / 2 := by
      simpa [ReplacementAssembly.exposedLowerChord] using hRS.2.2
    have hx := eq_right_of_bounds hRS.1.2.1 hxBound
    have hpEq : p = (a.core.chord / 2, -1) := Prod.ext hx hy
    simp [joinSet, hpEq]
  · have hyUpper : (1 : ℝ) ≤ p.2 := by
      simpa [ReplacementAssembly.upperCap] using hUS.1.2
    have hySegment : p.2 = -1 := by
      simpa [ReplacementAssembly.exposedLowerChord] using hUS.2.1
    linarith

theorem joinSet_finite (q : ℝ) : (joinSet q).Finite := by
  simp [joinSet]

/-- The join set realized in the metric where Euclidean H¹ is formed. -/
def euclideanJoinSet (q : ℝ) : Set EuclideanPlane :=
  planeEuclideanHomeomorph '' joinSet q

theorem euclideanJoinSet_finite (q : ℝ) : (euclideanJoinSet q).Finite :=
  (joinSet_finite q).image planeEuclideanHomeomorph

theorem hausdorffMeasure_one_euclideanJoinSet (q : ℝ) :
    (μH[1] : Measure EuclideanPlane) (euclideanJoinSet q) = 0 := by
  let _ := Measure.nullSingletonClass_hausdorff EuclideanPlane
    (by norm_num : (0 : ℝ) < 1)
  exact (euclideanJoinSet_finite q).measure_zero μH[1]

theorem fourArc_pairwiseOverlap_h1_null (a : FourArcAssembly) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' pairwiseOverlap
        (StripCore.leftArcTrace a.core)
        (StripCore.rightArcTrace a.core)
        (OneSidedCircularCap.arcTrace a.upperCap)
        (OneSidedCircularCap.arcTrace a.lowerCap)) = 0 := by
  exact measure_mono_null
    (image_mono (fourArc_pairwiseOverlap_subset_joinSet a))
    (hausdorffMeasure_one_euclideanJoinSet a.core.chord)

theorem replacement_pairwiseOverlap_h1_null (a : ReplacementAssembly) :
    (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' pairwiseOverlap
        (StripCore.leftArcTrace a.core)
        (StripCore.rightArcTrace a.core)
        (OneSidedCircularCap.arcTrace a.upperCap)
        a.exposedLowerChord.carrier) = 0 := by
  exact measure_mono_null
    (image_mono (replacement_pairwiseOverlap_subset_joinSet a))
    (hausdorffMeasure_one_euclideanJoinSet a.core.chord)

private theorem strictChord_not_mem_arcTrace
    (c : OneSidedCircularCap) {p : PlanePoint}
    (hy : p.2 = c.baseY)
    (hx : |p.1 - c.midpointX| < c.chord / 2) :
    p ∉ c.arcTrace := by
  intro harc
  have hcircle :
      (p.1 - c.midpointX) ^ 2 + (c.radius * Real.cos c.theta) ^ 2 =
        c.radius ^ 2 := by
    cases hside : c.side <;>
      simpa [OneSidedCircularCap.arcTrace,
        OneSidedCircularCap.radiusSquaredAt, OneSidedCircularCap.center,
        hside, hy] using harc.1
  have htrig := Real.sin_sq_add_cos_sq c.theta
  have hscale := congrArg (fun z : ℝ => c.radius ^ 2 * z) htrig
  have hrsSq := congrArg (fun z : ℝ => z ^ 2) c.radius_mul_sin
  have habs : |p.1 - c.midpointX| = c.chord / 2 := by
    have hhalf : 0 ≤ c.chord / 2 :=
      (div_pos c.chord_pos (by norm_num)).le
    rw [← sq_eq_sq₀ (abs_nonneg (p.1 - c.midpointX)) hhalf, sq_abs]
    nlinarith
  exact (ne_of_lt hx) habs

theorem replacement_strictUpperChord_mem_interior
    (a : ReplacementAssembly) {p : PlanePoint}
    (hp : p.2 = 1 ∧ |p.1| < a.core.chord / 2) :
    p ∈ interior a.carrier := by
  have hnot : p ∉ frontier a.carrier := by
    rw [a.frontier_carrier]
    rintro (hleft | hright | hupper | hlower)
    · linarith [(abs_lt.mp hp.2).1, hleft.2.1]
    · linarith [(abs_lt.mp hp.2).2, hright.2.1]
    · exact strictChord_not_mem_arcTrace a.upperCap
        (by simpa [ReplacementAssembly.upperCap] using hp.1)
        (by simpa [ReplacementAssembly.upperCap] using hp.2) hupper
    · have hy : p.2 = -1 := by
        simpa [ReplacementAssembly.exposedLowerChord,
          HorizontalSegment.carrier] using hlower.1
      linarith
  have hchord : p ∈ a.upperCap.chordCarrier := by
    simpa [ReplacementAssembly.upperCap,
      OneSidedCircularCap.chordCarrier] using ⟨hp.1, hp.2.le⟩
  have hcarrier : p ∈ a.carrier :=
    Or.inr (a.upperCap.chordCarrier_subset_carrier hchord)
  by_contra hnint
  exact hnot ((mem_frontier_iff_notMem_interior hcarrier).2 hnint)

theorem fourArc_euclidean_frontier (a : FourArcAssembly) :
    frontier (planeEuclideanHomeomorph '' a.carrier) =
      (planeEuclideanHomeomorph '' StripCore.leftArcTrace a.core) ∪
        ((planeEuclideanHomeomorph '' StripCore.rightArcTrace a.core) ∪
          ((planeEuclideanHomeomorph ''
              OneSidedCircularCap.arcTrace a.upperCap) ∪
            (planeEuclideanHomeomorph ''
              OneSidedCircularCap.arcTrace a.lowerCap))) := by
  rw [← planeEuclideanHomeomorph.image_frontier, a.frontier_carrier]
  simp only [FourArcAssembly.boundaryTrace, image_union]

theorem replacement_euclidean_frontier (a : ReplacementAssembly) :
    frontier (planeEuclideanHomeomorph '' a.carrier) =
      (planeEuclideanHomeomorph '' StripCore.leftArcTrace a.core) ∪
        ((planeEuclideanHomeomorph '' StripCore.rightArcTrace a.core) ∪
          ((planeEuclideanHomeomorph ''
              OneSidedCircularCap.arcTrace a.upperCap) ∪
            (planeEuclideanHomeomorph '' a.exposedLowerChord.carrier))) := by
  rw [← planeEuclideanHomeomorph.image_frontier, a.frontier_carrier]
  simp only [ReplacementAssembly.boundaryTrace, image_union]

theorem replacement_euclidean_upper_interface (a : ReplacementAssembly) :
    (planeEuclideanHomeomorph '' a.core.carrier) ∩
        (planeEuclideanHomeomorph '' a.upperCap.carrier) =
      planeEuclideanHomeomorph '' a.upperCap.chordCarrier := by
  rw [← Set.image_inter planeEuclideanHomeomorph.injective,
    a.core_inter_upperCap_eq_chord]

theorem replacement_euclidean_strictUpperChord_subset_interior
    (a : ReplacementAssembly) :
    planeEuclideanHomeomorph ''
        {p : PlanePoint | p.2 = 1 ∧ |p.1| < a.core.chord / 2} ⊆
      interior (planeEuclideanHomeomorph '' a.carrier) := by
  rw [← planeEuclideanHomeomorph.image_interior]
  exact image_mono (fun _ hp => replacement_strictUpperChord_mem_interior a hp)

theorem replacement_full_lower_segment_exposed (a : ReplacementAssembly) :
    a.exposedLowerChord.carrier ⊆
      a.boundaryTrace ∩ frontier a.carrier := by
  intro p hp
  exact ⟨Or.inr (Or.inr (Or.inr hp)),
    a.exposedLowerChord_subset_frontier hp⟩

theorem replacement_euclidean_exposedLowerChord_subset_frontier
    (a : ReplacementAssembly) :
    planeEuclideanHomeomorph '' a.exposedLowerChord.carrier ⊆
      frontier (planeEuclideanHomeomorph '' a.carrier) := by
  rw [← planeEuclideanHomeomorph.image_frontier]
  exact image_mono a.exposedLowerChord_subset_frontier

/-- Strip density transported to the Euclidean realization used by `FrontierMeasure`. -/
def euclideanStripDensity (lam : ℝ) (z : EuclideanPlane) : ℝ :=
  StripDensity lam (planeEuclideanHomeomorph.symm z)

private theorem measurable_euclideanStripDensity (lam : ℝ) :
    Measurable (euclideanStripDensity lam) :=
  (measurable_stripDensity lam).comp
    planeEuclideanHomeomorph.symm.continuous.measurable

private lemma euclideanStripDensity_bound (lam : ℝ) (z : EuclideanPlane) :
    ‖euclideanStripDensity lam z‖ ≤ 1 + |lam| := by
  change |StripDensity lam (planeEuclideanHomeomorph.symm z)| ≤ 1 + |lam|
  unfold StripDensity
  split_ifs <;> norm_num

/-- The transported strip density is integrable on every set of finite `H¹` mass. -/
lemma euclideanStripDensity_integrableOn_of_measure_ne_top
    (lam : ℝ) {s : Set EuclideanPlane}
    (hs : (μH[1] : Measure EuclideanPlane) s ≠ ∞) :
    IntegrableOn (euclideanStripDensity lam) s (μH[1] : Measure EuclideanPlane) := by
  apply Measure.integrableOn_of_bounded (M := 1 + |lam|) hs
  · exact (measurable_euclideanStripDensity lam).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (euclideanStripDensity_bound lam)

private theorem left_integral (lam : ℝ) (c : StripCore) :
    (∫ z in planeEuclideanHomeomorph '' c.leftArcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      coreArcEnd c - coreArcStart c := by
  calc
    _ = ∫ _z in planeEuclideanHomeomorph '' c.leftArcTrace,
        (1 : ℝ) ∂(μH[1] : Measure EuclideanPlane) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_euclidean_leftArcTrace c)] with z hz
      rcases hz with ⟨p, hp, rfl⟩
      have hp' : p ∈ leftCoreParam c ''
          Icc (coreArcStart c) (coreArcEnd c) := by
        simpa only [leftCoreParam_image_Icc] using hp
      rcases hp' with ⟨s, hs, rfl⟩
      change StripDensity lam
        (planeEuclideanHomeomorph.symm
          (planeEuclideanHomeomorph (leftCoreParam c s))) = 1
      rw [planeEuclideanHomeomorph.symm_apply_apply]
      exact leftCore_strip_density lam c hs
    _ = coreArcEnd c - coreArcStart c := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one, Measure.real,
        exact_euclidean_leftArcTrace_hausdorffMeasure]
      apply ENNReal.toReal_ofReal
      unfold coreArcEnd coreArcStart
      nlinarith [mul_pos c.radius_pos c.sideAngle_pos]

private theorem right_integral (lam : ℝ) (c : StripCore) :
    (∫ z in planeEuclideanHomeomorph '' c.rightArcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      coreArcEnd c - coreArcStart c := by
  calc
    _ = ∫ _z in planeEuclideanHomeomorph '' c.rightArcTrace,
        (1 : ℝ) ∂(μH[1] : Measure EuclideanPlane) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_euclidean_rightArcTrace c)] with z hz
      rcases hz with ⟨p, hp, rfl⟩
      have hp' : p ∈ rightCoreParam c ''
          Icc (coreArcStart c) (coreArcEnd c) := by
        simpa only [rightCoreParam_image_Icc] using hp
      rcases hp' with ⟨s, hs, rfl⟩
      change StripDensity lam
        (planeEuclideanHomeomorph.symm
          (planeEuclideanHomeomorph (rightCoreParam c s))) = 1
      rw [planeEuclideanHomeomorph.symm_apply_apply]
      exact rightCore_strip_density lam c hs
    _ = coreArcEnd c - coreArcStart c := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one, Measure.real,
        exact_euclidean_rightArcTrace_hausdorffMeasure]
      apply ENNReal.toReal_ofReal
      unfold coreArcEnd coreArcStart
      nlinarith [mul_pos c.radius_pos c.sideAngle_pos]

private theorem segment_integral (lam : ℝ) (seg : HorizontalSegment)
    (hbase : |seg.baseY| ≤ 1) :
    (∫ z in planeEuclideanHomeomorph '' seg.carrier,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      seg.euclideanLength := by
  calc
    _ = ∫ _z in planeEuclideanHomeomorph '' seg.carrier,
        (1 : ℝ) ∂(μH[1] : Measure EuclideanPlane) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_euclidean_segmentCarrier seg)] with z hz
      rcases hz with ⟨p, hp, rfl⟩
      have hp' : p ∈ segmentParam seg ''
          Icc (segmentStart seg) (segmentEnd seg) := by
        simpa only [segmentParam_image_Icc] using hp
      rcases hp' with ⟨s, _hs, rfl⟩
      change StripDensity lam
        (planeEuclideanHomeomorph.symm
          (planeEuclideanHomeomorph (segmentParam seg s))) = 1
      rw [planeEuclideanHomeomorph.symm_apply_apply]
      exact segment_strip_density lam seg hbase s
    _ = seg.euclideanLength := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one, Measure.real,
        exact_euclidean_segmentCarrier_hausdorffMeasure]
      exact ENNReal.toReal_ofReal seg.chord_pos.le

private theorem cap_integral (lam : ℝ) (c : OneSidedCircularCap)
    (hdensity : ∀ {s : ℝ}, s ∈ Ioo (capStart c) (capEnd c) →
      StripDensity lam (capParam c s) = lam) :
    (∫ z in planeEuclideanHomeomorph '' c.arcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      lam * c.arcLength := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane
      (by norm_num : (0 : ℝ) < 1)
  have hnot : ∀ᵐ z ∂(μH[1] : Measure EuclideanPlane),
      z ∉ ({planeEuclideanHomeomorph c.leftEndpoint,
        planeEuclideanHomeomorph c.rightEndpoint} : Set EuclideanPlane) :=
    (show ({planeEuclideanHomeomorph c.leftEndpoint,
      planeEuclideanHomeomorph c.rightEndpoint} :
        Set EuclideanPlane).Finite by simp).countable.ae_notMem _
  calc
    _ = ∫ _z in planeEuclideanHomeomorph '' c.arcTrace,
        lam ∂(μH[1] : Measure EuclideanPlane) := by
      apply integral_congr_ae
      filter_upwards [
        ae_restrict_mem (measurableSet_euclidean_capTrace c),
        ae_restrict_of_ae hnot] with z hz hzne
      rcases hz with ⟨p, hp, rfl⟩
      have hp' : p ∈ capParam c '' Icc (capStart c) (capEnd c) := by
        simpa only [capParam_image_Icc_eq_arcTrace] using hp
      rcases hp' with ⟨s, hs, rfl⟩
      have hsStart : s ≠ capStart c := by
        intro h
        subst s
        simp at hzne
      have hsEnd : s ≠ capEnd c := by
        intro h
        subst s
        simp at hzne
      have hsInterior : s ∈ Ioo (capStart c) (capEnd c) :=
        ⟨lt_of_le_of_ne hs.1 hsStart.symm, lt_of_le_of_ne hs.2 hsEnd⟩
      change StripDensity lam
        (planeEuclideanHomeomorph.symm
          (planeEuclideanHomeomorph (capParam c s))) = lam
      rw [planeEuclideanHomeomorph.symm_apply_apply]
      exact hdensity hsInterior
    _ = lam * c.arcLength := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, Measure.real,
        exact_euclidean_capTrace_hausdorffMeasure]
      rw [ENNReal.toReal_ofReal c.arcLength_pos.le]
      ring

/-- The transported density integral over an upper exterior cap is its
Euclidean arc length multiplied by the exterior density. -/
theorem upper_cap_integral (lam : ℝ)
    (c : OneSidedCircularCap) (hside : c.side = .upper)
    (hbase : c.baseY = 1) :
    (∫ z in planeEuclideanHomeomorph '' c.arcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      lam * c.arcLength :=
  cap_integral lam c (cap_upper_external_density lam c hside hbase)

private theorem lower_cap_integral (lam : ℝ)
    (c : OneSidedCircularCap) (hside : c.side = .lower)
    (hbase : c.baseY = -1) :
    (∫ z in planeEuclideanHomeomorph '' c.arcTrace,
        euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      lam * c.arcLength :=
  cap_integral lam c (cap_lower_external_density lam c hside hbase)

/-- Split an integral over four pairwise almost-disjoint measurable pieces. -/
theorem integral_four_union
    {f : EuclideanPlane → ℝ} {A B C D : Set EuclideanPlane}
    (hAB : AEDisjoint (μH[1] : Measure EuclideanPlane) A B)
    (hAC : AEDisjoint (μH[1] : Measure EuclideanPlane) A C)
    (hAD : AEDisjoint (μH[1] : Measure EuclideanPlane) A D)
    (hBC : AEDisjoint (μH[1] : Measure EuclideanPlane) B C)
    (hBD : AEDisjoint (μH[1] : Measure EuclideanPlane) B D)
    (hCD : AEDisjoint (μH[1] : Measure EuclideanPlane) C D)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hfA : IntegrableOn f A (μH[1] : Measure EuclideanPlane))
    (hfB : IntegrableOn f B (μH[1] : Measure EuclideanPlane))
    (hfC : IntegrableOn f C (μH[1] : Measure EuclideanPlane))
    (hfD : IntegrableOn f D (μH[1] : Measure EuclideanPlane)) :
    (∫ z in A ∪ (B ∪ (C ∪ D)), f z ∂(μH[1] : Measure EuclideanPlane)) =
      (∫ z in A, f z ∂(μH[1] : Measure EuclideanPlane)) +
        ((∫ z in B, f z ∂(μH[1] : Measure EuclideanPlane)) +
          ((∫ z in C, f z ∂(μH[1] : Measure EuclideanPlane)) +
            ∫ z in D, f z ∂(μH[1] : Measure EuclideanPlane))) := by
  rw [setIntegral_union₀
      (hAB.union_right (hAC.union_right hAD))
      (hB.union (hC.union hD)).nullMeasurableSet
      hfA (hfB.union (hfC.union hfD)),
    setIntegral_union₀
      (hBC.union_right hBD)
      (hC.union hD).nullMeasurableSet
      hfB (hfC.union hfD),
    setIntegral_union₀ hCD hD.nullMeasurableSet hfC hfD]

/-- The union of all six pairwise overlaps among four Euclidean sets. -/
def euclideanPairwiseOverlap {α : Type*}
    (A B C D : Set α) : Set α :=
  (A ∩ B) ∪ ((A ∩ C) ∪ ((A ∩ D) ∪
    ((B ∩ C) ∪ ((B ∩ D) ∪ (C ∩ D)))))

/-- A null union of all pairwise overlaps makes the four sets pairwise
almost disjoint. -/
theorem pairwise_aedisjoint_of_overlap_null
    {A B C D : Set EuclideanPlane}
    (hnull : (μH[1] : Measure EuclideanPlane)
      (euclideanPairwiseOverlap A B C D) = 0) :
    AEDisjoint (μH[1] : Measure EuclideanPlane) A B ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) C D := by
  refine ⟨measure_mono_null (fun _ hz => Or.inl hz) hnull,
    measure_mono_null (fun _ hz => Or.inr (Or.inl hz)) hnull,
    measure_mono_null (fun _ hz => Or.inr (Or.inr (Or.inl hz))) hnull,
    measure_mono_null (fun _ hz => Or.inr (Or.inr (Or.inr (Or.inl hz)))) hnull,
    measure_mono_null
      (fun _ hz => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))) hnull,
    measure_mono_null
      (fun _ hz => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hz))))) hnull⟩

private theorem fourArc_pairwise (a : FourArcAssembly) :
    let A := planeEuclideanHomeomorph '' StripCore.leftArcTrace a.core
    let B := planeEuclideanHomeomorph '' StripCore.rightArcTrace a.core
    let C := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace a.upperCap
    let D := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace a.lowerCap
    AEDisjoint (μH[1] : Measure EuclideanPlane) A B ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) C D := by
  dsimp only
  apply pairwise_aedisjoint_of_overlap_null
  simpa only [euclideanPairwiseOverlap, pairwiseOverlap, image_union,
    Set.image_inter planeEuclideanHomeomorph.injective] using
    fourArc_pairwiseOverlap_h1_null a

private theorem replacement_pairwise (a : ReplacementAssembly) :
    let A := planeEuclideanHomeomorph '' StripCore.leftArcTrace a.core
    let B := planeEuclideanHomeomorph '' StripCore.rightArcTrace a.core
    let C := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace a.upperCap
    let D := planeEuclideanHomeomorph '' a.exposedLowerChord.carrier
    AEDisjoint (μH[1] : Measure EuclideanPlane) A B ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) A D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B C ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) B D ∧
    AEDisjoint (μH[1] : Measure EuclideanPlane) C D := by
  dsimp only
  apply pairwise_aedisjoint_of_overlap_null
  simpa only [euclideanPairwiseOverlap, pairwiseOverlap, image_union,
    Set.image_inter planeEuclideanHomeomorph.injective] using
    replacement_pairwiseOverlap_h1_null a

private theorem core_param_length (c : StripCore) :
    coreArcEnd c - coreArcStart c = 2 * ell c.sideAngle := by
  unfold coreArcEnd coreArcStart StripCore.radius ell
  rw [c.sin_sideAngle]
  field_simp [ne_of_gt c.curvature_pos]
  ring

/-- The complete topological frontier of a strip core includes both circular
side arcs and both horizontal segments.  All four pieces have density one. -/
theorem stripCore_frontier_weightedPerimeter_eq
    (lam : ℝ) (c : StripCore) :
    WeightedPerimeter lam (FrontierMeasure c.carrier) =
      c.boundaryArcLength + 2 * c.chord := by
  let upper : HorizontalSegment :=
    { chord := c.chord
      midpointX := 0
      baseY := 1
      chord_pos := c.chord_pos }
  let lower : HorizontalSegment :=
    { chord := c.chord
      midpointX := 0
      baseY := -1
      chord_pos := c.chord_pos }
  have hupper : upper.carrier = c.upperChordTrace := by
    ext p
    simp [upper, HorizontalSegment.carrier, StripCore.upperChordTrace]
  have hlower : lower.carrier = c.lowerChordTrace := by
    ext p
    simp [lower, HorizontalSegment.carrier, StripCore.lowerChordTrace]
  have hoverlap :
      pairwiseOverlap c.leftArcTrace c.rightArcTrace
          upper.carrier lower.carrier ⊆ joinSet c.chord := by
    intro p hp
    simp only [pairwiseOverlap, mem_union, mem_inter_iff] at hp
    rcases hp with hLR | hLU | hLL | hRU | hRL | hUL
    · exact False.elim (by
        have hl := hLR.1.2.1
        have hr := hLR.2.2.1
        linarith [c.chord_pos])
    · have hy : p.2 = 1 := by
        simpa [upper, HorizontalSegment.carrier] using hLU.2.1
      have hxBound : |p.1| ≤ c.chord / 2 := by
        simpa [upper, HorizontalSegment.carrier] using hLU.2.2
      have hx := eq_left_of_bounds hLU.1.2.1 hxBound
      have hpEq : p = (-c.chord / 2, 1) := Prod.ext hx hy
      simp [joinSet, hpEq]
    · have hy : p.2 = -1 := by
        simpa [lower, HorizontalSegment.carrier] using hLL.2.1
      have hxBound : |p.1| ≤ c.chord / 2 := by
        simpa [lower, HorizontalSegment.carrier] using hLL.2.2
      have hx := eq_left_of_bounds hLL.1.2.1 hxBound
      have hpEq : p = (-c.chord / 2, -1) := Prod.ext hx hy
      simp [joinSet, hpEq]
    · have hy : p.2 = 1 := by
        simpa [upper, HorizontalSegment.carrier] using hRU.2.1
      have hxBound : |p.1| ≤ c.chord / 2 := by
        simpa [upper, HorizontalSegment.carrier] using hRU.2.2
      have hx := eq_right_of_bounds hRU.1.2.1 hxBound
      have hpEq : p = (c.chord / 2, 1) := Prod.ext hx hy
      simp [joinSet, hpEq]
    · have hy : p.2 = -1 := by
        simpa [lower, HorizontalSegment.carrier] using hRL.2.1
      have hxBound : |p.1| ≤ c.chord / 2 := by
        simpa [lower, HorizontalSegment.carrier] using hRL.2.2
      have hx := eq_right_of_bounds hRL.1.2.1 hxBound
      have hpEq : p = (c.chord / 2, -1) := Prod.ext hx hy
      simp [joinSet, hpEq]
    · have hyUpper : p.2 = 1 := by
        simpa [upper, HorizontalSegment.carrier] using hUL.1.1
      have hyLower : p.2 = -1 := by
        simpa [lower, HorizontalSegment.carrier] using hUL.2.1
      linarith
  have hnull :
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' pairwiseOverlap
            c.leftArcTrace c.rightArcTrace upper.carrier lower.carrier) = 0 :=
    measure_mono_null (image_mono hoverlap)
      (hausdorffMeasure_one_euclideanJoinSet c.chord)
  have hpairs :
      AEDisjoint (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' c.leftArcTrace)
          (planeEuclideanHomeomorph '' c.rightArcTrace) ∧
      AEDisjoint (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' c.leftArcTrace)
          (planeEuclideanHomeomorph '' upper.carrier) ∧
      AEDisjoint (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' c.leftArcTrace)
          (planeEuclideanHomeomorph '' lower.carrier) ∧
      AEDisjoint (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' c.rightArcTrace)
          (planeEuclideanHomeomorph '' upper.carrier) ∧
      AEDisjoint (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' c.rightArcTrace)
          (planeEuclideanHomeomorph '' lower.carrier) ∧
      AEDisjoint (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' upper.carrier)
          (planeEuclideanHomeomorph '' lower.carrier) := by
    apply pairwise_aedisjoint_of_overlap_null
    simpa only [euclideanPairwiseOverlap, pairwiseOverlap, image_union,
      Set.image_inter planeEuclideanHomeomorph.injective] using hnull
  rcases hpairs with ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  have hAint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' c.leftArcTrace) (by
      rw [exact_euclidean_leftArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  have hBint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' c.rightArcTrace) (by
      rw [exact_euclidean_rightArcTrace_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  have hCint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' upper.carrier) (by
      rw [exact_euclidean_segmentCarrier_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  have hDint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph '' lower.carrier) (by
      rw [exact_euclidean_segmentCarrier_hausdorffMeasure]
      exact ENNReal.ofReal_ne_top)
  unfold WeightedPerimeter FrontierMeasure
  rw [integral_map
    planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable
    (measurable_stripDensity lam).aestronglyMeasurable]
  change (∫ z in frontier (planeEuclideanHomeomorph '' c.carrier),
    euclideanStripDensity lam z ∂(μH[1] : Measure EuclideanPlane)) =
      c.boundaryArcLength + 2 * c.chord
  rw [← planeEuclideanHomeomorph.image_frontier, c.frontier_carrier,
    image_union, image_union, image_union, ← hupper, ← hlower]
  rw [integral_four_union hAB hAC hAD hBC hBD hCD
    (measurableSet_euclidean_rightArcTrace c)
    (measurableSet_euclidean_segmentCarrier upper)
    (measurableSet_euclidean_segmentCarrier lower)
    hAint hBint hCint hDint]
  rw [left_integral, right_integral,
    segment_integral lam upper (by simp [upper]),
    segment_integral lam lower (by simp [lower]),
    core_param_length, StripCore.boundaryArcLength]
  simp only [upper, lower, HorizontalSegment.euclideanLength]
  ring

/-- The explicit four-arc boundary cost equals the canonical weighted H¹
integral on the complete topological frontier of its coordinate carrier. -/
theorem fourArc_frontier_weightedPerimeter_eq
    (lam : ℝ) (assembly : FourArcAssembly) :
    assembly.weightedPerimeter lam =
      WeightedPerimeter lam (FrontierMeasure assembly.carrier) := by
  rcases fourArc_pairwise assembly with
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  have hAint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      StripCore.leftArcTrace assembly.core) (by
        rw [exact_euclidean_leftArcTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hBint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      StripCore.rightArcTrace assembly.core) (by
        rw [exact_euclidean_rightArcTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hCint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace assembly.upperCap) (by
        rw [exact_euclidean_capTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hDint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace assembly.lowerCap) (by
        rw [exact_euclidean_capTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  rw [FourArcAssembly.weightedPerimeter_formula]
  symm
  unfold WeightedPerimeter FrontierMeasure
  rw [integral_map
    planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable
    (measurable_stripDensity lam).aestronglyMeasurable]
  change (∫ z in frontier (planeEuclideanHomeomorph '' assembly.carrier),
    euclideanStripDensity lam z
      ∂(μH[1] : Measure EuclideanPlane)) =
    assembly.core.boundaryArcLength +
      lam * (assembly.upperCap.arcLength + assembly.lowerCap.arcLength)
  rw [fourArc_euclidean_frontier]
  rw [integral_four_union hAB hAC hAD hBC hBD hCD
    (measurableSet_euclidean_rightArcTrace assembly.core)
    (measurableSet_euclidean_capTrace assembly.upperCap)
    (measurableSet_euclidean_capTrace assembly.lowerCap)
    hAint hBint hCint hDint]
  rw [left_integral, right_integral,
    upper_cap_integral lam assembly.upperCap rfl rfl,
    lower_cap_integral lam assembly.lowerCap rfl rfl,
    core_param_length, StripCore.boundaryArcLength]
  ring

/-- The explicit replacement boundary cost equals the canonical weighted H¹
integral on the complete topological frontier of its coordinate carrier. -/
theorem replacement_frontier_weightedPerimeter_eq
    (lam : ℝ) (assembly : ReplacementAssembly) :
    assembly.weightedPerimeter lam =
      WeightedPerimeter lam (FrontierMeasure assembly.carrier) := by
  rcases replacement_pairwise assembly with
    ⟨hAB, hAC, hAD, hBC, hBD, hCD⟩
  have hAint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      StripCore.leftArcTrace assembly.core) (by
        rw [exact_euclidean_leftArcTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hBint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      StripCore.rightArcTrace assembly.core) (by
        rw [exact_euclidean_rightArcTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hCint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      OneSidedCircularCap.arcTrace assembly.upperCap) (by
        rw [exact_euclidean_capTrace_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  have hDint := euclideanStripDensity_integrableOn_of_measure_ne_top
    lam (s := planeEuclideanHomeomorph ''
      assembly.exposedLowerChord.carrier) (by
        rw [exact_euclidean_segmentCarrier_hausdorffMeasure]
        exact ENNReal.ofReal_ne_top)
  rw [ReplacementAssembly.weightedPerimeter_formula]
  symm
  unfold WeightedPerimeter FrontierMeasure
  rw [integral_map
    planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable
    (measurable_stripDensity lam).aestronglyMeasurable]
  change (∫ z in frontier (planeEuclideanHomeomorph '' assembly.carrier),
    euclideanStripDensity lam z
      ∂(μH[1] : Measure EuclideanPlane)) =
    assembly.core.boundaryArcLength + lam * assembly.upperCap.arcLength +
      assembly.exposedLowerChord.euclideanLength
  rw [replacement_euclidean_frontier]
  rw [integral_four_union hAB hAC hAD hBC hBD hCD
    (measurableSet_euclidean_rightArcTrace assembly.core)
    (measurableSet_euclidean_capTrace assembly.upperCap)
    (measurableSet_euclidean_segmentCarrier assembly.exposedLowerChord)
    hAint hBint hCint hDint]
  rw [left_integral, right_integral,
    upper_cap_integral lam assembly.upperCap rfl rfl,
    segment_integral lam assembly.exposedLowerChord (by
      simp [ReplacementAssembly.exposedLowerChord]),
    core_param_length, StripCore.boundaryArcLength]
  ring

/-! ## Canonical finite-perimeter realizations -/

/-- A finite Euclidean `H¹` mass for the complete frontier is enough to make
the bounded strip density integrable against its canonical frontier measure. -/
lemma stripDensity_integrable_frontierMeasure_of_measure_ne_top
    (lam : ℝ) {carrier : Set PlanePoint}
    (hfrontier :
      (μH[1] : Measure EuclideanPlane)
          (frontier (planeEuclideanHomeomorph '' carrier)) ≠ ⊤) :
    Integrable (StripDensity lam) (FrontierMeasure carrier) := by
  unfold FrontierMeasure
  rw [integrable_map_measure
    (measurable_stripDensity lam).aestronglyMeasurable
    planeEuclideanHomeomorph.symm.continuous.measurable.aemeasurable]
  change IntegrableOn (euclideanStripDensity lam)
    (frontier (planeEuclideanHomeomorph '' carrier))
    (μH[1] : Measure EuclideanPlane)
  exact euclideanStripDensity_integrableOn_of_measure_ne_top lam hfrontier

namespace FourArcAssembly

/-- The four-arc carrier has finite weighted area. -/
theorem integrableOn_carrier (lam : ℝ) (a : FourArcAssembly) :
    IntegrableOn (StripDensity lam) a.carrier := by
  rw [carrier]
  exact ((core_integrableOn lam a.core).union
    (cap_integrableOn lam a.upperCap)).union
      (cap_integrableOn lam a.lowerCap)

/-- The complete four-arc frontier has finite weighted perimeter. -/
theorem integrable_frontierMeasure (lam : ℝ) (a : FourArcAssembly) :
    Integrable (StripDensity lam) (FrontierMeasure a.carrier) := by
  apply stripDensity_integrable_frontierMeasure_of_measure_ne_top
  rw [fourArc_euclidean_frontier]
  apply measure_union_ne_top
  · rw [exact_euclidean_leftArcTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  apply measure_union_ne_top
  · rw [exact_euclidean_rightArcTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  apply measure_union_ne_top
  · rw [exact_euclidean_capTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  · rw [exact_euclidean_capTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top

end FourArcAssembly

namespace ReplacementAssembly

/-- The cap-replacement carrier has finite weighted area. -/
theorem integrableOn_carrier (lam : ℝ) (a : ReplacementAssembly) :
    IntegrableOn (StripDensity lam) a.carrier := by
  rw [carrier]
  exact (core_integrableOn lam a.core).union
    (cap_integrableOn lam a.upperCap)

/-- The complete cap-replacement frontier has finite weighted perimeter. -/
theorem integrable_frontierMeasure (lam : ℝ) (a : ReplacementAssembly) :
    Integrable (StripDensity lam) (FrontierMeasure a.carrier) := by
  apply stripDensity_integrable_frontierMeasure_of_measure_ne_top
  rw [replacement_euclidean_frontier]
  apply measure_union_ne_top
  · rw [exact_euclidean_leftArcTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  apply measure_union_ne_top
  · rw [exact_euclidean_rightArcTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  apply measure_union_ne_top
  · rw [exact_euclidean_capTrace_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top
  · rw [exact_euclidean_segmentCarrier_hausdorffMeasure]
    exact ENNReal.ofReal_ne_top

end ReplacementAssembly

namespace AdmissibleCompetitor

/-- Every constructor in the modeled comparison class has the canonical
finite-perimeter-region semantics. -/
def toFinitePerimeterRegion {lam : ℝ} :
    AdmissibleCompetitor lam → FinitePerimeterRegion lam
  | .empty => {
      carrier := ∅
      measurable_carrier := MeasurableSet.empty
      finite_weighted_area := by simp
      finite_weighted_perimeter := by simp [FrontierMeasure] }
  | .general region => region
  | .fourArc a => {
      carrier := a.carrier
      measurable_carrier := a.measurableSet_carrier
      finite_weighted_area := a.integrableOn_carrier lam
      finite_weighted_perimeter := a.integrable_frontierMeasure lam }
  | .replacement a => {
      carrier := a.carrier
      measurable_carrier := a.measurableSet_carrier
      finite_weighted_area := a.integrableOn_carrier lam
      finite_weighted_perimeter := a.integrable_frontierMeasure lam }

@[simp] theorem toFinitePerimeterRegion_carrier {lam : ℝ}
    (r : AdmissibleCompetitor lam) :
    r.toFinitePerimeterRegion.carrier = r.carrier := by
  cases r <;> rfl

@[simp] theorem toFinitePerimeterRegion_weightedArea {lam : ℝ}
    (r : AdmissibleCompetitor lam) :
    r.toFinitePerimeterRegion.weightedArea = r.WeightedArea := by
  rw [FinitePerimeterRegion.weightedArea, weightedArea_eq_carrier,
    toFinitePerimeterRegion_carrier]

@[simp] theorem toFinitePerimeterRegion_weightedPerimeter {lam : ℝ}
    (r : AdmissibleCompetitor lam) :
    r.toFinitePerimeterRegion.weightedPerimeter = r.WeightedPerimeter := by
  unfold FinitePerimeterRegion.weightedPerimeter
    AdmissibleCompetitor.WeightedPerimeter
  rw [toFinitePerimeterRegion_carrier]

/-- The modeled comparison class embeds value-preservingly into canonical
finite-perimeter regions. -/
theorem exists_finitePerimeterRegion {lam : ℝ}
    (r : AdmissibleCompetitor lam) :
    ∃ region : FinitePerimeterRegion lam,
      region.carrier = r.carrier ∧
      region.weightedArea = r.WeightedArea ∧
      region.weightedPerimeter = r.WeightedPerimeter := by
  exact ⟨r.toFinitePerimeterRegion,
    r.toFinitePerimeterRegion_carrier,
    r.toFinitePerimeterRegion_weightedArea,
    r.toFinitePerimeterRegion_weightedPerimeter⟩

end AdmissibleCompetitor
#print axioms fourArc_frontier_weightedPerimeter_eq
#print axioms replacement_frontier_weightedPerimeter_eq
#print axioms exact_euclidean_capParam_hausdorffMeasure
#print axioms capParam_image_Icc_eq_arcTrace
#print axioms exact_euclidean_capTrace_hausdorffMeasure
#print axioms leftCoreParam_image_Icc
#print axioms rightCoreParam_image_Icc
#print axioms exact_euclidean_leftArcTrace_hausdorffMeasure
#print axioms exact_euclidean_rightArcTrace_hausdorffMeasure
#print axioms segmentParam_image_Icc
#print axioms realizedSegmentParam_image_affineSegment
#print axioms exact_euclidean_segmentCarrier_hausdorffMeasure
#print axioms measurableSet_euclidean_leftArcTrace
#print axioms measurableSet_euclidean_rightArcTrace
#print axioms measurableSet_euclidean_segmentCarrier
#print axioms measurableSet_euclidean_capTrace
#print axioms fourArc_pairwiseOverlap_subset_joinSet
#print axioms replacement_pairwiseOverlap_subset_joinSet
#print axioms fourArc_pairwiseOverlap_h1_null
#print axioms replacement_pairwiseOverlap_h1_null
#print axioms fourArc_euclidean_frontier
#print axioms replacement_euclidean_frontier
#print axioms replacement_euclidean_upper_interface
#print axioms replacement_euclidean_strictUpperChord_subset_interior
#print axioms replacement_euclidean_exposedLowerChord_subset_frontier
