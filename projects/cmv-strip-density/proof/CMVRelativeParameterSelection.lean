import CMVLocalGraphSurgery

open Set Function Filter MeasureTheory
open scoped Topology ContDiff symmDiff Manifold ENNReal

noncomputable section

namespace CMVRelaxation
/-- A smooth map from a lower-dimensional finite-dimensional real normed space
has null range for the Hausdorff measure in the target dimension. -/
theorem hausdorffMeasure_range_eq_zero_of_finrank_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {g : E → F} (hg : ContDiff ℝ 1 g)
    (hEF : Module.finrank ℝ E < Module.finrank ℝ F) :
    (μH[Module.finrank ℝ F] : Measure F) (Set.range g) = 0 := by
  apply hausdorffMeasure_of_dimH_lt
    (d := (Module.finrank ℝ F : NNReal))
  exact hg.dimH_range_le.trans_lt (by exact_mod_cast hEF)

/-- Canonical top-dimensional Hausdorff measure on the three-dimensional
bounded-perturbation parameter space. -/
abbrev boundedParameterMeasure : Measure (PlanePoint × ℝ) :=
  μH[Module.finrank ℝ (PlanePoint × ℝ)]

theorem boundedParameterMeasure_eq_hausdorffMeasure_three :
    boundedParameterMeasure =
      (μH[3] : Measure (PlanePoint × ℝ)) := by
  norm_num [boundedParameterMeasure, PlanePoint]

/-- The exceptional parameter set for the three-parameter bounded regularization
has zero three-dimensional Hausdorff measure. -/
theorem hausdorffMeasure_three_range_boundedBadJet_eq_zero
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    boundedParameterMeasure (Set.range (boundedBadJet f)) = 0 := by
  exact hausdorffMeasure_range_eq_zero_of_finrank_lt
    ((contDiff_boundedBadJet hf).of_le (by simp))
    (by norm_num [PlanePoint])

/-- Almost every bounded-regularization parameter is a regular parameter. -/
theorem ae_not_mem_range_boundedBadJet
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ c : PlanePoint × ℝ ∂boundedParameterMeasure,
      c ∉ Set.range (boundedBadJet f) := by
  rw [ae_iff]
  apply measure_mono_null
    (show {c | ¬c ∉ Set.range (boundedBadJet f)} ⊆
      Set.range (boundedBadJet f) by
      intro c hc
      exact Classical.byContradiction (fun h => hc h))
  exact hausdorffMeasure_three_range_boundedBadJet_eq_zero hf

/-- A positive finite averaging set cannot have all of its below-average points
inside a null exceptional set. -/
theorem exists_not_mem_null_and_le_setLAverage
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {bad s : Set α} (hbad : μ bad = 0)
    (hs₀ : μ s ≠ 0) (hs_top : μ s ≠ (∞ : ℝ≥0∞))
    {L : α → ℝ≥0∞} (hL : AEMeasurable L (μ.restrict s)) :
    ∃ x ∈ s, x ∉ bad ∧ L x ≤ ⨍⁻ y in s, L y ∂μ := by
  have hpositive :
      0 < μ {x ∈ s | L x ≤ ⨍⁻ y in s, L y ∂μ} :=
    measure_le_setLAverage_pos hs₀ hs_top hL
  have hnsubset :
      ¬ {x ∈ s | L x ≤ ⨍⁻ y in s, L y ∂μ} ⊆ bad := by
    intro hsubset
    have hzero :
        μ {x ∈ s | L x ≤ ⨍⁻ y in s, L y ∂μ} = 0 :=
      measure_mono_null hsubset hbad
    exact hpositive.ne' hzero
  obtain ⟨x, hxgood, hxbad⟩ := Set.not_subset.mp hnsubset
  exact ⟨x, hxgood.1, hxbad, hxgood.2⟩

/-- Selection of a regular bounded perturbation parameter whose chosen
measurable cost does not exceed its set average. -/
theorem exists_regularBoundedParameter_le_setLAverage
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {s : Set (PlanePoint × ℝ)}
    (hs₀ : boundedParameterMeasure s ≠ 0)
    (hs_top : boundedParameterMeasure s ≠ (∞ : ℝ≥0∞))
    {L : (PlanePoint × ℝ) → ℝ≥0∞}
    (hL : AEMeasurable L (boundedParameterMeasure.restrict s)) :
    ∃ c ∈ s, c ∉ Set.range (boundedBadJet f) ∧
      L c ≤ ⨍⁻ q in s, L q
        ∂boundedParameterMeasure := by
  exact exists_not_mem_null_and_le_setLAverage boundedParameterMeasure
    (hausdorffMeasure_three_range_boundedBadJet_eq_zero hf)
    hs₀ hs_top hL

/-- A below-average regular parameter can be selected in every parameter ball.
The ball membership gives the requested arbitrarily small perturbation. -/
theorem exists_small_regularBoundedParameter_le_setLAverage
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε)
    {L : (PlanePoint × ℝ) → ℝ≥0∞}
    (hL : AEMeasurable L
      (boundedParameterMeasure.restrict (Metric.ball 0 ε))) :
    ∃ c : PlanePoint × ℝ, ‖c‖ < ε ∧
      c ∉ Set.range (boundedBadJet f) ∧
      L c ≤ ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε, L q
        ∂boundedParameterMeasure := by
  obtain ⟨c, hc, hregular, hcost⟩ :=
    exists_regularBoundedParameter_le_setLAverage hf
      (Metric.measure_ball_pos boundedParameterMeasure
        (0 : PlanePoint × ℝ) hε).ne'
      (measure_ball_lt_top :
        boundedParameterMeasure
          (Metric.ball (0 : PlanePoint × ℝ) ε) < (∞ : ℝ≥0∞)).ne
      hL
  exact ⟨c, by simpa [Metric.mem_ball] using hc, hregular, hcost⟩

/-- Exact first derivative of the bounded perturbation. -/
theorem fderiv_boundedPerturb
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : PlanePoint × ℝ) (p : PlanePoint) :
    fderiv ℝ (boundedPerturb f c) p =
      fderiv ℝ f p -
        c.1.1 • (1 + p.1 ^ 2)⁻¹ •
          ContinuousLinearMap.fst ℝ ℝ ℝ -
        c.1.2 • (1 + p.2 ^ 2)⁻¹ •
          ContinuousLinearMap.snd ℝ ℝ ℝ := by
  let D : PlanePoint →L[ℝ] ℝ :=
    fderiv ℝ f p -
      c.1.1 • (1 + p.1 ^ 2)⁻¹ •
        ContinuousLinearMap.fst ℝ ℝ ℝ -
      c.1.2 • (1 + p.2 ^ 2)⁻¹ •
        ContinuousLinearMap.snd ℝ ℝ ℝ
  have hder : HasFDerivAt (boundedPerturb f c) D p := by
    unfold boundedPerturb
    simpa [D] using
      (((hf.differentiable (by simp) p).hasFDerivAt.sub
        (((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).arctan).const_mul
          c.1.1)).sub
        (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).arctan).const_mul
          c.1.2)).sub_const c.2
  exact hder.fderiv

/-- The first derivative changes by at most twice the parameter norm,
uniformly in space. -/
theorem norm_fderiv_boundedPerturb_sub_le
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : PlanePoint × ℝ) (p : PlanePoint) :
    ‖fderiv ℝ (boundedPerturb f c) p - fderiv ℝ f p‖ ≤
      2 * ‖c‖ := by
  let A : PlanePoint →L[ℝ] ℝ :=
    c.1.1 • (1 + p.1 ^ 2)⁻¹ •
      ContinuousLinearMap.fst ℝ ℝ ℝ
  let B : PlanePoint →L[ℝ] ℝ :=
    c.1.2 • (1 + p.2 ^ 2)⁻¹ •
      ContinuousLinearMap.snd ℝ ℝ ℝ
  have hc11 : |c.1.1| ≤ ‖c‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_fst_le c.1).trans (norm_fst_le c)
  have hc12 : |c.1.2| ≤ ‖c‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_snd_le c.1).trans (norm_fst_le c)
  have hdenx : ‖(1 + p.1 ^ 2)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact (inv_le_one₀ (by positivity)).2
      (by nlinarith [sq_nonneg p.1])
  have hdeny : ‖(1 + p.2 ^ 2)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact (inv_le_one₀ (by positivity)).2
      (by nlinarith [sq_nonneg p.2])
  have hA : ‖A‖ ≤ ‖c‖ := by
    dsimp [A]
    rw [norm_smul, norm_smul,
      ContinuousLinearMap.norm_fst, mul_one, Real.norm_eq_abs]
    simpa using
      mul_le_mul hc11 hdenx (norm_nonneg _) (norm_nonneg _)
  have hB : ‖B‖ ≤ ‖c‖ := by
    dsimp [B]
    rw [norm_smul, norm_smul,
      ContinuousLinearMap.norm_snd, mul_one, Real.norm_eq_abs]
    simpa using
      mul_le_mul hc12 hdeny (norm_nonneg _) (norm_nonneg _)
  rw [fderiv_boundedPerturb hf]
  change ‖(fderiv ℝ f p - A - B) - fderiv ℝ f p‖ ≤ 2 * ‖c‖
  have hrearrange :
      (fderiv ℝ f p - A - B) - fderiv ℝ f p = -(A + B) := by
    abel
  rw [hrearrange, norm_neg]
  calc
    ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
    _ ≤ ‖c‖ + ‖c‖ := add_le_add hA hB
    _ = 2 * ‖c‖ := by ring

/-- Exact first derivative after multiplying the bounded perturbation by a
smooth localization cutoff. -/
theorem fderiv_localizedBoundedPerturb
    {f χ : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (c : PlanePoint × ℝ) (p : PlanePoint) :
    fderiv ℝ (localizedBoundedPerturb f χ c) p =
      fderiv ℝ f p +
        (χ p •
            (fderiv ℝ (boundedPerturb f c) p - fderiv ℝ f p) +
          (boundedPerturb f c p - f p) • fderiv ℝ χ p) := by
  have hfder := (hf.differentiable (by simp) p).hasFDerivAt
  have hχder := (hχ.differentiable (by simp) p).hasFDerivAt
  have hbder := ((contDiff_boundedPerturb hf c).differentiable
    (by simp) p).hasFDerivAt
  have hlocal := hfder.add (hχder.mul (hbder.sub hfder))
  change fderiv ℝ (f + χ * (boundedPerturb f c - f)) p = _
  exact hlocal.fderiv

/-- Quantitative `C¹` control survives smooth localization. The coefficient
records only a uniform derivative bound for the cutoff. -/
theorem norm_fderiv_localizedBoundedPerturb_sub_le
    {f χ : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (c : PlanePoint × ℝ)
    (hχrange : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    {M : ℝ} (hχderiv : ∀ p, ‖fderiv ℝ χ p‖ ≤ M)
    (p : PlanePoint) :
    ‖fderiv ℝ (localizedBoundedPerturb f χ c) p -
      fderiv ℝ f p‖ ≤
        (2 + (Real.pi + 1) * M) * ‖c‖ := by
  let D : PlanePoint →L[ℝ] ℝ :=
    fderiv ℝ (boundedPerturb f c) p - fderiv ℝ f p
  let δ : ℝ := boundedPerturb f c p - f p
  have hχabs : |χ p| ≤ 1 := by
    rw [abs_of_nonneg (hχrange p).1]
    exact (hχrange p).2
  have hD : ‖D‖ ≤ 2 * ‖c‖ :=
    norm_fderiv_boundedPerturb_sub_le hf c p
  have hδ : |δ| ≤ (Real.pi + 1) * ‖c‖ :=
    abs_boundedPerturb_sub_le f c p
  have hM : 0 ≤ M :=
    (norm_nonneg (fderiv ℝ χ p)).trans (hχderiv p)
  have hfirst : ‖χ p • D‖ ≤ 2 * ‖c‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa using
      mul_le_mul hχabs hD (norm_nonneg D) zero_le_one
  have hsecond :
      ‖δ • fderiv ℝ χ p‖ ≤
        ((Real.pi + 1) * ‖c‖) * M := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hδ (hχderiv p) (norm_nonneg _)
      (mul_nonneg (by positivity) (norm_nonneg c))
  rw [fderiv_localizedBoundedPerturb hf hχ, add_sub_cancel_left]
  change ‖χ p • D + δ • fderiv ℝ χ p‖ ≤
    (2 + (Real.pi + 1) * M) * ‖c‖
  calc
    ‖χ p • D + δ • fderiv ℝ χ p‖ ≤
        ‖χ p • D‖ + ‖δ • fderiv ℝ χ p‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖c‖ + ((Real.pi + 1) * ‖c‖) * M :=
      add_le_add hfirst hsecond
    _ = (2 + (Real.pi + 1) * M) * ‖c‖ := by ring

/-- Where the cutoff vanishes on a neighborhood, localization leaves both the
phase and its first derivative unchanged. -/
theorem localizedBoundedPerturb_eq_and_fderiv_eq_of_eventuallyEq_zero
    (f χ : PlanePoint → ℝ) (c : PlanePoint × ℝ) (p : PlanePoint)
    (hχzero : χ =ᶠ[𝓝 p] fun _ => 0) :
    localizedBoundedPerturb f χ c p = f p ∧
      fderiv ℝ (localizedBoundedPerturb f χ c) p = fderiv ℝ f p := by
  have heq : localizedBoundedPerturb f χ c =ᶠ[𝓝 p] f := by
    filter_upwards [hχzero] with q hq
    simp [localizedBoundedPerturb, hq]
  exact ⟨heq.eq_of_nhds, heq.fderiv_eq⟩

/-- A compactly supported cutoff makes the perturbation itself compactly
supported relative to the original phase. -/
theorem hasCompactSupport_localizedBoundedPerturb_sub
    (f χ : PlanePoint → ℝ) (c : PlanePoint × ℝ)
    (hχ : HasCompactSupport χ) :
    HasCompactSupport
      (fun p => localizedBoundedPerturb f χ c p - f p) := by
  have heq :
      (fun p => localizedBoundedPerturb f χ c p - f p) =
        χ * (boundedPerturb f c - f) := by
    funext p
    simp [localizedBoundedPerturb]
  rw [heq]
  exact hχ.mul_right

/-- End-to-end small regularization: below-average selection, regular zero
level, and uniform quantitative `C⁰`/`C¹` control. -/
theorem exists_small_regularBoundedPerturb_with_C1_control
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε)
    {L : (PlanePoint × ℝ) → ℝ≥0∞}
    (hL : AEMeasurable L
      (boundedParameterMeasure.restrict (Metric.ball 0 ε))) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, boundedPerturb f c p = 0 →
        fderiv ℝ (boundedPerturb f c) p ≠ 0) ∧
      (∀ p, |boundedPerturb f c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (boundedPerturb f c) p -
        fderiv ℝ f p‖ < 2 * ε) ∧
      L c ≤ ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε, L q
        ∂boundedParameterMeasure := by
  obtain ⟨c, hc, hregular, hcost⟩ :=
    exists_small_regularBoundedParameter_le_setLAverage hf hε hL
  refine ⟨c, hc, boundedPerturb_regular hf hregular, ?_, ?_, hcost⟩
  · intro p
    exact (abs_boundedPerturb_sub_le f c p).trans_lt
      (mul_lt_mul_of_pos_left hc (by positivity))
  · intro p
    exact (norm_fderiv_boundedPerturb_sub_le hf c p).trans_lt
      (mul_lt_mul_of_pos_left hc (by norm_num))

/-- End-to-end compactly supported regularization.  A cutoff equal to one near
`K` transfers regularity from the bounded perturbation there; the quantitative
nonvanishing margin for `f` excludes new zeroes outside `K`. -/
theorem exists_small_regularLocalizedBoundedPerturb_with_C1_control
    {f χ : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    (hχ : ContDiff ℝ ∞ χ) (hχsupport : HasCompactSupport χ)
    (hχrange : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    {M : ℝ} (hχderiv : ∀ p, ‖fderiv ℝ χ p‖ ≤ M)
    (K : Set PlanePoint) (hχone : ∀ p ∈ K, χ =ᶠ[𝓝 p] fun _ => 1)
    {ε : ℝ} (hε : 0 < ε)
    (hfaway : ∀ p ∉ K, (Real.pi + 1) * ε ≤ |f p|)
    {L : (PlanePoint × ℝ) → ℝ≥0∞}
    (hL : AEMeasurable L
      (boundedParameterMeasure.restrict (Metric.ball 0 ε))) :
    ∃ c : PlanePoint × ℝ,
      ‖c‖ < ε ∧
      (∀ p, localizedBoundedPerturb f χ c p = 0 →
        fderiv ℝ (localizedBoundedPerturb f χ c) p ≠ 0) ∧
      (∀ p, |localizedBoundedPerturb f χ c p - f p| <
        (Real.pi + 1) * ε) ∧
      (∀ p, ‖fderiv ℝ (localizedBoundedPerturb f χ c) p -
        fderiv ℝ f p‖ < (2 + (Real.pi + 1) * M) * ε) ∧
      HasCompactSupport
        (fun p => localizedBoundedPerturb f χ c p - f p) ∧
      L c ≤ ⨍⁻ q in Metric.ball (0 : PlanePoint × ℝ) ε, L q
        ∂boundedParameterMeasure := by
  obtain ⟨c, hc, hreg, _hC0, _hC1, hcost⟩ :=
    exists_small_regularBoundedPerturb_with_C1_control hf hε hL
  have hM : 0 ≤ M :=
    (norm_nonneg (fderiv ℝ χ 0)).trans (hχderiv 0)
  refine ⟨c, hc, ?_, ?_, ?_,
    hasCompactSupport_localizedBoundedPerturb_sub f χ c hχsupport, hcost⟩
  · intro p hpzero
    have hpK : p ∈ K := by
      by_contra hpK
      have hdisp := abs_localizedBoundedPerturb_sub_le f χ c hχrange p
      have hdispStrict :
          |localizedBoundedPerturb f χ c p - f p| <
            (Real.pi + 1) * ε :=
        hdisp.trans_lt (mul_lt_mul_of_pos_left hc (by positivity))
      have hfp : |f p| =
          |localizedBoundedPerturb f χ c p - f p| := by
        rw [hpzero, zero_sub, abs_neg]
      linarith [hfaway p hpK]
    have heq : localizedBoundedPerturb f χ c =ᶠ[𝓝 p]
        boundedPerturb f c := by
      filter_upwards [hχone p hpK] with q hq
      simp [localizedBoundedPerturb, hq]
    have hboundedZero : boundedPerturb f c p = 0 := by
      rw [← heq.eq_of_nhds]
      exact hpzero
    rw [heq.fderiv_eq]
    exact hreg p hboundedZero
  · intro p
    exact (abs_localizedBoundedPerturb_sub_le f χ c hχrange p).trans_lt
      (mul_lt_mul_of_pos_left hc (by positivity))
  · intro p
    exact (norm_fderiv_localizedBoundedPerturb_sub_le hf hχ c hχrange
      hχderiv p).trans_lt
      (mul_lt_mul_of_pos_left hc (by positivity))

end CMVRelaxation
