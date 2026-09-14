import CMVRegularGermScaledSplice

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

namespace RegularCornerChartApplicability

variable {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}

/-- The first-order source velocity of the literal anti-diagonal connector. -/
def connectorVelocity (C : ActualRegularTraceCorner side) : PlanePoint :=
  (C.incident.velocity.1 - C.interface.velocity.1,
    C.incident.velocity.2 - C.interface.velocity.2)

/-- Precisely the source-geometric differentiability needed to put a metric on
`RegularCornerChartApplicability.connectorParam`.  The chart is `C¹`, its two
coordinate differentials agree with the already stored germ velocities, and
the resulting anti-diagonal velocity is nonzero.  There is deliberately no
competitor, frontier, cost, contact, or perimeter-saving datum here. -/
structure MetricApplicability (A : RegularCornerChartApplicability C) : Prop where
  chart_contDiff : ContDiff ℝ 1 A.chart
  fderiv_incident :
    fderiv ℝ A.chart (0, 0) (1, 0) = C.incident.velocity
  fderiv_interface :
    fderiv ℝ A.chart (0, 0) (0, 1) = C.interface.velocity
  connectorVelocity_ne : connectorVelocity C ≠ (0, 0)

namespace MetricApplicability

variable (M : MetricApplicability A)

/-- Source-coordinate speed of the anti-diagonal direction through the chart. -/
def connectorSpeedAt (_M : MetricApplicability A) (q : PlanePoint) : ℝ :=
  Real.sqrt
    (((fderiv ℝ A.chart q (1, -1)).1) ^ 2 +
      ((fderiv ℝ A.chart q (1, -1)).2) ^ 2)

/-- Parametric arclength of the literal scale-`r` connector. -/
def connectorArcLength (_M : MetricApplicability A) (r : ℝ) : ℝ :=
  ∫ t in 0..r, euclideanParametricSpeed (A.connectorParam r) t

lemma connectorParam_contDiff (M : MetricApplicability A) (r : ℝ) :
    ContDiff ℝ 1 (A.connectorParam r) := by
  exact (MetricApplicability.chart_contDiff M).comp
    (contDiff_id.prodMk (contDiff_const.sub contDiff_id))

lemma connectorParam_hasDerivAt (M : MetricApplicability A) (r t : ℝ) :
    HasDerivAt (A.connectorParam r)
      (fderiv ℝ A.chart (t, r - t) (1, -1)) t := by
  have hin : HasDerivAt (fun s : ℝ => (s, r - s)) (1, -1) t := by
    convert (hasDerivAt_id t).prodMk
      ((hasDerivAt_const t r).sub (hasDerivAt_id t)) using 1 <;>
        norm_num [Pi.sub_apply, id_eq]
  change HasDerivAt (fun s : ℝ => A.chart (s, r - s))
    (fderiv ℝ A.chart (t, r - t) (1, -1)) t
  exact
    ((MetricApplicability.chart_contDiff M).differentiable (by norm_num)
      (t, r - t)).hasFDerivAt.comp_hasDerivAt t hin

lemma euclideanParametricSpeed_connectorParam (r t : ℝ) :
    euclideanParametricSpeed (A.connectorParam r) t =
      M.connectorSpeedAt (t, r - t) := by
  have h := connectorParam_hasDerivAt M r t
  have hx : deriv (fun s => (A.connectorParam r s).1) t =
      (fderiv ℝ A.chart (t, r - t) (1, -1)).1 := by
    simpa using h.hasFDerivAt.fst.hasDerivAt.deriv
  have hy : deriv (fun s => (A.connectorParam r s).2) t =
      (fderiv ℝ A.chart (t, r - t) (1, -1)).2 := by
    simpa using h.hasFDerivAt.snd.hasDerivAt.deriv
  unfold euclideanParametricSpeed connectorSpeedAt
  rw [hx, hy]

lemma continuous_connectorSpeedAt : Continuous M.connectorSpeedAt := by
  have hD : Continuous (fun q => fderiv ℝ A.chart q (1, -1)) :=
    ((MetricApplicability.chart_contDiff M).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  exact ((hD.fst.pow 2).add (hD.snd.pow 2)).sqrt

lemma fderiv_antiDiagonal_zero (M : MetricApplicability A) :
    fderiv ℝ A.chart (0, 0) (1, -1) = connectorVelocity C := by
  have hvec : ((1, -1) : PlanePoint) = (1, 0) - (0, 1) := by ext <;> norm_num
  rw [hvec, map_sub, MetricApplicability.fderiv_incident M,
    MetricApplicability.fderiv_interface M]
  rfl

lemma connectorSpeedAt_zero :
    M.connectorSpeedAt (0, 0) = euclideanSpeed (connectorVelocity C) := by
  rw [connectorSpeedAt, fderiv_antiDiagonal_zero M]
  unfold euclideanSpeed complexVector
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma connectorSpeedAt_zero_pos : 0 < M.connectorSpeedAt (0, 0) := by
  rw [connectorSpeedAt_zero M]
  exact euclideanSpeed_pos (MetricApplicability.connectorVelocity_ne M)
/-- The chart anti-diagonal speed is the endpoint velocity-difference norm
used by the regular tangent coefficient. -/
lemma euclideanSpeed_connectorVelocity :
    euclideanSpeed (connectorVelocity C) =
      ‖complexVector C.incident.velocity -
        complexVector C.interface.velocity‖ := by
  unfold euclideanSpeed
  congr 1
  apply Complex.ext <;> simp [connectorVelocity, complexVector]


/-- One source radius on which every positive literal connector is regular.
Injectivity itself is global because the underlying chart is a homeomorphism. -/
theorem exists_connectorMetricRadius (M : MetricApplicability A) :
    ∃ ρ > 0, ∀ r ∈ Ioc 0 ρ, ∀ t ∈ Icc 0 r,
      0 < euclideanParametricSpeed (A.connectorParam r) t := by
  have hev : ∀ᶠ q in 𝓝 ((0, 0) : PlanePoint), 0 < M.connectorSpeedAt q :=
    (continuous_connectorSpeedAt M).continuousAt.eventually
      (Ioi_mem_nhds (connectorSpeedAt_zero_pos M))
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro r hr t ht
  rw [euclideanParametricSpeed_connectorParam M]
  apply hball
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [sub_zero]
  rw [max_lt_iff]
  constructor
  · rw [abs_of_nonneg ht.1]
    linarith [ht.2, hr.2]
  · have hrt : 0 ≤ r - t := sub_nonneg.mpr ht.2
    rw [abs_of_nonneg hrt]
    linarith [ht.1, hr.2]

/-- The literal connector is injective on every parameter interval. -/
theorem connectorParam_injOn_metric (r : ℝ) :
    Set.InjOn (A.connectorParam r) (Icc 0 r) :=
  A.connectorParam_injOn r

/-- For every sufficiently small positive scale, the Euclidean `H¹` of the
literal connector is exactly its parametric arclength. -/
theorem exists_hausdorffMeasure_connectorTrace_eq_connectorArcLength :
    ∃ ρ > 0, ∀ r ∈ Ioc 0 ρ,
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' A.connectorTrace r) =
        ENNReal.ofReal (M.connectorArcLength r) := by
  obtain ⟨ρ, hρ, hregular⟩ := exists_connectorMetricRadius M
  refine ⟨ρ, hρ, ?_⟩
  intro r hr
  rw [A.connectorTrace_eq_image_Icc hr.1.le]
  unfold connectorArcLength
  exact
    hausdorffMeasure_regularParametricCurve_Icc_eq_intervalIntegral_of_speed_pos
      (connectorParam_contDiff M r) hr.1.le (A.connectorParam_injOn r)
        (hregular r hr)
/-- At every sufficiently small positive scale, the literal connector cost is
its exact parametric arclength times the source phase price. -/
theorem exists_weightedTraceCost_connector_eq_phase_connectorArcLength
    (P : PhysicalPhaseApplicability A) (lam : ℝ) :
    ∃ ρ > 0, ∀ r ∈ Ioc 0 ρ,
      weightedTraceCost lam (A.connectorTrace r) =
        ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal (M.connectorArcLength r) := by
  obtain ⟨ρ, hρ, hmass⟩ :=
    M.exists_hausdorffMeasure_connectorTrace_eq_connectorArcLength
  have hmin : 0 < min ρ A.localRadius :=
    lt_min hρ A.localRadius_pos
  refine ⟨min ρ A.localRadius / 2, half_pos hmin, ?_⟩
  intro r hr
  have hlocal : r < A.localRadius :=
    hr.2.trans_lt ((half_lt_self hmin).trans_le (min_le_right _ _))
  have hrho : r ≤ ρ :=
    hr.2.trans ((div_le_self hmin.le one_le_two).trans (min_le_left _ _))
  rw [PhysicalPhaseApplicability.weightedTraceCost_connector_eq_phase_hausdorff
      A P lam hr.1 hlocal,
    hmass r ⟨hr.1, hrho⟩]


private lemma connectorArcLength_rescale {r : ℝ} (hr : r ≠ 0) :
    M.connectorArcLength r / r =
      ∫ s in 0..1, M.connectorSpeedAt (r * s, r * (1 - s)) := by
  let f : ℝ → ℝ := fun t => M.connectorSpeedAt (t, r - t)
  have hchange := intervalIntegral.integral_comp_mul_left f hr
    (a := 0) (b := 1)
  have hleft : (∫ s in 0..1, f (r * s)) =
      ∫ s in 0..1, M.connectorSpeedAt (r * s, r * (1 - s)) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    dsimp [f]
    congr 2
    ring
  rw [hleft] at hchange
  have harc : M.connectorArcLength r = ∫ t in 0..r, f t := by
    unfold connectorArcLength
    apply intervalIntegral.integral_congr
    intro t _ht
    exact euclideanParametricSpeed_connectorParam M r t
  rw [harc]
  rw [show r * 0 = 0 by ring, show r * 1 = r by ring] at hchange
  simpa only [smul_eq_mul, div_eq_inv_mul] using hchange.symm
/-- First-order metric coefficient of the regular germ splice. -/
theorem tendsto_connectorArcLength_div :
    Tendsto (fun r => M.connectorArcLength r / r) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed (connectorVelocity C))) := by
  let F : ℝ → ℝ → ℝ := fun r s =>
    M.connectorSpeedAt (r * s, r * (1 - s))
  have hF : Continuous F.uncurry := by
    apply (continuous_connectorSpeedAt M).comp
    fun_prop
  have hI : Continuous (fun r => ∫ s in 0..1, F r s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have hlim : Tendsto (fun r => ∫ s in 0..1, F r s) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed (connectorVelocity C))) := by
    have hzero : (∫ s in 0..1, F 0 s) =
        euclideanSpeed (connectorVelocity C) := by
      simp [F, connectorSpeedAt_zero M]
    rw [← hzero]

    exact hI.continuousAt.mono_left inf_le_left
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (connectorArcLength_rescale M hr.ne').symm
/-- Removed regular-germ arclength minus the arclength of the literal
chart-image connector. -/
def metricTraceGain
    (incidentWeight interfaceWeight connectorWeight r : ℝ) : ℝ :=
  incidentWeight * C.incident.arcLength r +
    interfaceWeight * C.interface.arcLength r -
      connectorWeight * M.connectorArcLength r

/-- The literal connector has exactly the same first-order coefficient as the
endpoint chord, now derived from its actual parametric arclength. -/
theorem tendsto_metricTraceGain_div
    (incidentWeight interfaceWeight connectorWeight : ℝ) :
    Tendsto
      (fun r => M.metricTraceGain incidentWeight interfaceWeight
        connectorWeight r / r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (tangentGainCoefficient C.incident C.interface
        incidentWeight interfaceWeight connectorWeight)) := by
  have hi := C.incident.tendsto_arcLength_div.const_mul incidentWeight
  have hf := C.interface.tendsto_arcLength_div.const_mul interfaceWeight
  have hc := M.tendsto_connectorArcLength_div.const_mul connectorWeight
  rw [euclideanSpeed_connectorVelocity (C := C)] at hc
  convert (hi.add hf).sub hc using 1 <;>
    simp [metricTraceGain, tangentGainCoefficient, sub_div, add_div,
      mul_div_assoc]

/-- A positive tangent coefficient gives strict shortening for the literal
metric connector at every sufficiently small positive scale. -/
theorem eventually_metricTraceGain_pos
    (incidentWeight interfaceWeight connectorWeight : ℝ)
    (hgain : 0 < tangentGainCoefficient C.incident C.interface
      incidentWeight interfaceWeight connectorWeight) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < M.metricTraceGain incidentWeight interfaceWeight
        connectorWeight r := by
  have hquot := (M.tendsto_metricTraceGain_div incidentWeight
    interfaceWeight connectorWeight).eventually (eventually_gt_nhds hgain)
  filter_upwards [hquot, self_mem_nhdsWithin] with r hquotient hr
  rcases (div_pos_iff.mp hquotient) with h | h
  · exact h.1
  · exact (not_lt_of_ge hr.le h.2).elim

/-- Nonnegativity of endpoint arclength on a positive parameter interval. -/
private lemma endpointArcLength_nonneg
    {junction : PlanePoint} (T : RegularEndpointTrace junction)
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ T.arcLength r := by
  unfold RegularEndpointTrace.arcLength
  exact intervalIntegral.integral_nonneg hr
    (fun _ _ => norm_nonneg _)

/-- The retained part of a positive endpoint interval has nonnegative
arclength. -/
private lemma endpointArcLength_two_sub_nonneg
    {junction : PlanePoint} (T : RegularEndpointTrace junction)
    {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ T.arcLength (2 * r) - T.arcLength r := by
  rw [RegularEndpointTrace.arcLength, RegularEndpointTrace.arcLength,
    intervalIntegral.integral_interval_sub_left
      (T.speed_continuous.intervalIntegrable 0 (2 * r))
      (T.speed_continuous.intervalIntegrable 0 r)]
  exact intervalIntegral.integral_nonneg (by linarith)
    (fun _ _ => norm_nonneg _)

/-- The literal chart-image connector also has nonnegative parametric
arclength. -/
private lemma connectorArcLength_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ M.connectorArcLength r := by
  unfold connectorArcLength
  exact intervalIntegral.integral_nonneg hr
    (fun _ _ => Real.sqrt_nonneg _)

/-- Both source phases have nonnegative literal price when `1 ≤ lambda`. -/
private lemma phaseWeight_nonneg
    (P : PhysicalPhaseApplicability A) {lam : ℝ} (hlam : 1 ≤ lam) :
    0 ≤ P.phase.weight lam := by
  cases P.phase <;>
    simp [LocalTracePhase.weight, (show (0 : ℝ) ≤ lam from le_trans (by norm_num) hlam)]

/-- At a fixed regular scale, positivity of the intrinsic metric trace gain
is strict shortening of the actual constructed local frontier.  The connector
cost equality is derived from its literal trace; no chord surrogate or
subtraction of extended costs is used. -/
theorem local_inside_cost_lt_of_metricTraceGain_pos
    (P : PhysicalPhaseApplicability A) {lam r : ℝ}
    (hlam : 1 ≤ lam) (hr : 0 < r)
    (hlocal : 2 * r < A.localRadius) (htrace : 2 * r ≤ C.radius)
    (hincidentRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.incident.speed t)
    (hinterfaceRegular :
      ∀ t ∈ Icc 0 (2 * r), 0 < C.interface.speed t)
    (hconnector :
      weightedTraceCost lam (A.connectorTrace r) =
        ENNReal.ofReal (P.phase.weight lam) *
          ENNReal.ofReal (M.connectorArcLength r))
    (hgain :
      0 < M.metricTraceGain (P.phase.weight lam) 1
        (P.phase.weight lam) r) :
    smoothCostOn lam (A.localModel r) (interior (A.window r)) <
      smoothCostOn lam C.representative (interior (A.window r)) := by
  rw [PhysicalPhaseApplicability.localModel_inside_cost_eq_phase_arcLength_add_connector
      A P lam hr hlocal htrace hincidentRegular hinterfaceRegular,
    PhysicalPhaseApplicability.representative_inside_cost_eq_phase_arcLengths
      A P lam hr hlocal htrace hincidentRegular hinterfaceRegular,
    hconnector]
  have hw : 0 ≤ P.phase.weight lam := phaseWeight_nonneg P hlam
  have hiTwo : 0 ≤ C.incident.arcLength (2 * r) :=
    endpointArcLength_nonneg C.incident (by linarith)
  have hfTwo : 0 ≤ C.interface.arcLength (2 * r) :=
    endpointArcLength_nonneg C.interface (by linarith)
  have hiDiff :
      0 ≤ C.incident.arcLength (2 * r) - C.incident.arcLength r :=
    endpointArcLength_two_sub_nonneg C.incident hr.le
  have hfDiff :
      0 ≤ C.interface.arcLength (2 * r) - C.interface.arcLength r :=
    endpointArcLength_two_sub_nonneg C.interface hr.le
  have hc : 0 ≤ M.connectorArcLength r :=
    connectorArcLength_nonneg M hr.le
  rw [← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_add (mul_nonneg hw hiDiff) hfDiff,
    ← ENNReal.ofReal_add
      (add_nonneg (mul_nonneg hw hiDiff) hfDiff) (mul_nonneg hw hc),
    ← ENNReal.ofReal_add (mul_nonneg hw hiTwo) hfTwo]
  apply (ENNReal.ofReal_lt_ofReal_iff ?_).2
  · unfold metricTraceGain at hgain
    linarith
  · unfold metricTraceGain at hgain
    nlinarith [mul_nonneg hw hiDiff, hfDiff, mul_nonneg hw hc]

/-- A strict local shortening propagates to the complete frontier whenever
the unchanged exterior contribution is finite.  The cutting boundary is
already included in that exterior contribution by `competitor_complete_cost`;
no extended-value subtraction is performed. -/
theorem competitor_complete_cost_lt_of_local_inside_cost_lt
    {lam r : ℝ} (hr : 0 < r) (hlocal : 2 * r < A.localRadius)
    (hinside :
      smoothCostOn lam (A.localModel r) (interior (A.window r)) <
        smoothCostOn lam C.representative (interior (A.window r)))
    (houtside :
      smoothCostOn lam C.representative (interior (A.window r))ᶜ ≠ ⊤) :
    smoothCost lam (A.competitor r) <
      smoothCost lam C.representative := by
  rw [A.competitor_complete_cost lam hr hlocal,
    ← smoothCostOn_add_compl lam C.representative
      isOpen_interior.measurableSet]
  exact ENNReal.add_lt_add_of_lt_of_le houtside hinside le_rfl

/-- A positive tangent coefficient therefore shortens the literal local
frontier at every sufficiently small positive scale.  Regularity,
multiplicity one, source prices, and connector arclength are all discharged by
the source-geometric applicability structures. -/
theorem eventually_local_inside_cost_lt
    (M : MetricApplicability A) (P : PhysicalPhaseApplicability A)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hgain :
      0 < tangentGainCoefficient C.incident C.interface
        (P.phase.weight lam) 1 (P.phase.weight lam)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCostOn lam (A.localModel r) (interior (A.window r)) <
        smoothCostOn lam C.representative (interior (A.window r)) := by
  obtain ⟨ρt, hρt, hρtLocal, hiRegular, hfRegular⟩ :=
    A.exists_traceMetricRadius
  obtain ⟨ρc, hρc, hconnector⟩ :=
    exists_weightedTraceCost_connector_eq_phase_connectorArcLength M P lam
  have hmetric :=
    M.eventually_metricTraceGain_pos
      (P.phase.weight lam) 1 (P.phase.weight lam) hgain
  have hsmallTrace : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρt :=
    ((eventually_lt_nhds (half_pos hρt)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have hsmallSource : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < C.radius :=
    ((eventually_lt_nhds (half_pos C.radius_pos)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have hsmallConnector : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ≤ ρc :=
    ((eventually_lt_nhds hρc).filter_mono inf_le_left).mono
      (fun _ hr => hr.le)
  filter_upwards [self_mem_nhdsWithin, hmetric, hsmallTrace,
    hsmallSource, hsmallConnector] with r hr hrGain hrTrace hrSource hrConnector
  apply M.local_inside_cost_lt_of_metricTraceGain_pos P hlam hr
    (hrTrace.trans_le hρtLocal) hrSource.le
  · intro t ht
    exact hiRegular t ⟨ht.1, ht.2.trans hrTrace.le⟩
  · intro t ht
    exact hfRegular t ⟨ht.1, ht.2.trans hrTrace.le⟩
  · exact hconnector r ⟨hr, hrConnector⟩
  · exact hrGain

/-- Independent positive source scalings preserve the metric bridge whenever
the correspondingly scaled endpoint-velocity difference is nonzero. -/
theorem positiveDiagonalReparam_metric
    (M : MetricApplicability A)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hne : (a * C.incident.velocity.1 - b * C.interface.velocity.1,
      a * C.incident.velocity.2 - b * C.interface.velocity.2) ≠ (0, 0)) :
    MetricApplicability (A.positiveDiagonalReparam a b ha hb) where
  chart_contDiff := by
    exact (MetricApplicability.chart_contDiff M).comp
      ((contDiff_const.mul contDiff_fst).prodMk
        (contDiff_const.mul contDiff_snd))
  fderiv_incident := by
    let d : PlanePoint → PlanePoint := fun q => (a * q.1, b * q.2)
    let D : PlanePoint →L[ℝ] PlanePoint :=
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (b • ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hd : HasFDerivAt d D (0, 0) := by
      dsimp [d, D]
      fun_prop
    have hc := ((MetricApplicability.chart_contDiff M).differentiable
      (by norm_num) (d (0, 0))).hasFDerivAt.comp (0, 0) hd
    have happly := congrArg
      (fun L : PlanePoint →L[ℝ] PlanePoint => L (1, 0)) hc.fderiv
    change fderiv ℝ (A.chart ∘ d) (0, 0) (1, 0) =
      (a * C.incident.velocity.1, a * C.incident.velocity.2)
    rw [happly]
    simp only [ContinuousLinearMap.comp_apply]
    dsimp [d, D]
    simp only [smul_apply]
    simp
    have haVec : ((a, 0) : PlanePoint) = a • ((1, 0) : PlanePoint) := by
      ext <;> simp
    rw [haVec, map_smul, MetricApplicability.fderiv_incident M]
    ext <;> simp
  fderiv_interface := by
    let d : PlanePoint → PlanePoint := fun q => (a * q.1, b * q.2)
    let D : PlanePoint →L[ℝ] PlanePoint :=
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (b • ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hd : HasFDerivAt d D (0, 0) := by
      dsimp [d, D]
      fun_prop
    have hc := ((MetricApplicability.chart_contDiff M).differentiable
      (by norm_num) (d (0, 0))).hasFDerivAt.comp (0, 0) hd
    have happly := congrArg
      (fun L : PlanePoint →L[ℝ] PlanePoint => L (0, 1)) hc.fderiv
    change fderiv ℝ (A.chart ∘ d) (0, 0) (0, 1) =
      (b * C.interface.velocity.1, b * C.interface.velocity.2)
    rw [happly]
    simp only [ContinuousLinearMap.comp_apply]
    dsimp [d, D]
    simp only [smul_apply]
    simp
    have hbVec : ((0, b) : PlanePoint) = b • ((0, 1) : PlanePoint) := by
      ext <;> simp
    rw [hbVec, map_smul, MetricApplicability.fderiv_interface M]
    ext <;> simp
  connectorVelocity_ne := by
    simpa [connectorVelocity, ActualRegularTraceCorner.positiveDiagonalReparam,
      RegularEndpointTrace.positiveReparam] using hne

/-- The asymptotic coefficient after independent positive source scalings is
the Euclidean norm of the correspondingly scaled velocity difference. -/
theorem tendsto_connectorArcLength_div_positiveDiagonal
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hne : (a * C.incident.velocity.1 - b * C.interface.velocity.1,
      a * C.incident.velocity.2 - b * C.interface.velocity.2) ≠ (0, 0)) :
    Tendsto
      (fun r =>
        connectorArcLength (positiveDiagonalReparam_metric M a b ha hb hne) r / r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed
        (a * C.incident.velocity.1 - b * C.interface.velocity.1,
          a * C.incident.velocity.2 - b * C.interface.velocity.2))) := by
  simpa [connectorVelocity, ActualRegularTraceCorner.positiveDiagonalReparam,
    RegularEndpointTrace.positiveReparam] using
      tendsto_connectorArcLength_div
        (positiveDiagonalReparam_metric M a b ha hb hne)

/-- Independent positive endpoint scales feed the complete literal comparison,
not merely the abstract tangent coefficient.  The transformed chart still
splices the same representative, and both initial conormals are preserved by
the positive reparameterizations. -/
theorem eventually_positiveDiagonal_local_inside_cost_lt
    (M : MetricApplicability A) (P : PhysicalPhaseApplicability A)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hne : (a * C.incident.velocity.1 - b * C.interface.velocity.1,
      a * C.incident.velocity.2 - b * C.interface.velocity.2) ≠ (0, 0))
    (hgain :
      0 < tangentGainCoefficient
        (C.incident.positiveReparam a ha)
        (C.interface.positiveReparam b hb)
        (P.phase.weight lam) 1 (P.phase.weight lam)) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCostOn lam
          ((A.positiveDiagonalReparam a b ha hb).localModel r)
          (interior ((A.positiveDiagonalReparam a b ha hb).window r)) <
        smoothCostOn lam C.representative
          (interior ((A.positiveDiagonalReparam a b ha hb).window r)) := by
  let C' := C.positiveDiagonalReparam a b ha hb
  let A' := A.positiveDiagonalReparam a b ha hb
  let M' := M.positiveDiagonalReparam_metric a b ha hb hne
  let P' := P.positiveDiagonalReparam a b ha hb
  have hgain' :
      0 < tangentGainCoefficient C'.incident C'.interface
        (P'.phase.weight lam) 1 (P'.phase.weight lam) := by
    simpa [C', P', ActualRegularTraceCorner.positiveDiagonalReparam,
      PhysicalPhaseApplicability.positiveDiagonalReparam] using hgain
  have hactual :=
    eventually_local_inside_cost_lt M' P' lam hlam hgain'
  simpa [A', C', ActualRegularTraceCorner.positiveDiagonalReparam] using hactual

end MetricApplicability

end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison
