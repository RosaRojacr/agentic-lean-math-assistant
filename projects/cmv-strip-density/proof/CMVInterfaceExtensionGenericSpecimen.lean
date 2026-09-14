import CMVRegularGermInterfaceExtension
import CMVInterfaceExtensionSpecimen

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.InterfaceExtensionGenericSpecimen

open FiniteBandRearrangement
open RegularTraceCornerComparison
open RegularTraceCornerComparison.RegularCornerChartApplicability

/-- The affine corner chart whose coordinate axes are the specimen's incident
and interface traces. -/
def affineChart : PlanePoint ≃ₜ PlanePoint where
  toFun q := (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)
  invFun p := (5 / 4 * (p.2 - 1), p.1 + 3 / 4 * (p.2 - 1))
  left_inv q := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem affineChart_apply (q : PlanePoint) :
    affineChart q = (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1) := rfl

private lemma oldOpen_height_gt_one {p : PlanePoint}
    (hp : p ∈ InterfaceExtensionSpecimen.oldOpen) : 1 < p.2 := by
  have hpNhd : InterfaceExtensionSpecimen.oldRegion.carrier ∈ 𝓝 p :=
    mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset
  rcases Metric.mem_nhds_iff.mp hpNhd with ⟨ε, hε, hball⟩
  let z : PlanePoint := (p.1, p.2 - ε / 2)
  have hzball : z ∈ Metric.ball p ε := by
    change dist z p < ε
    rw [Prod.dist_eq, dist_self, max_eq_right]
    · dsimp [z]
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hε]
      linarith
    · exact dist_nonneg
  have hz := hball hzball
  rw [Region.carrier, mem_iUnion] at hz
  rcases hz with ⟨i, hz⟩
  rw [Region.bandCarrier, mem_iUnion] at hz
  rcases hz with ⟨j, hz⟩
  rw [InterfaceExtensionSpecimen.oldRegion.mem_componentCarrier_iff] at hz
  fin_cases i
  fin_cases j
  have hzLower := hz.1.1
  change 1 ≤ z.2 at hzLower
  dsimp [z] at hzLower
  linarith

private lemma oldOpen_left_lt {p : PlanePoint}
    (hp : p ∈ InterfaceExtensionSpecimen.oldOpen) :
    InterfaceExtensionSpecimen.oldLeft p.2 < p.1 := by
  have hpNhd : InterfaceExtensionSpecimen.oldRegion.carrier ∈ 𝓝 p :=
    mem_of_superset (isOpen_interior.mem_nhds hp) interior_subset
  rcases Metric.mem_nhds_iff.mp hpNhd with ⟨ε, hε, hball⟩
  let z : PlanePoint := (p.1 - ε / 2, p.2)
  have hzball : z ∈ Metric.ball p ε := by
    change dist z p < ε
    rw [Prod.dist_eq, dist_self, max_eq_left]
    · dsimp [z]
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hε]
      linarith
    · exact dist_nonneg
  have hz := hball hzball
  rw [Region.carrier, mem_iUnion] at hz
  rcases hz with ⟨i, hz⟩
  rw [Region.bandCarrier, mem_iUnion] at hz
  rcases hz with ⟨j, hz⟩
  rw [InterfaceExtensionSpecimen.oldRegion.mem_componentCarrier_iff] at hz
  fin_cases i
  fin_cases j
  have hzLeft := hz.2.1
  change InterfaceExtensionSpecimen.oldLeft z.2 ≤ z.1 at hzLeft
  dsimp [z] at hzLeft
  linarith

/-- The specimen is exactly the occupied first quadrant in the affine chart on
this fixed coordinate neighborhood. -/
def affineApplicability :
    RegularCornerChartApplicability InterfaceExtensionSpecimen.actualCorner where
  chart := affineChart
  localRadius := 1 / 4
  localRadius_pos := by norm_num
  chart_zero := by simp [InterfaceExtensionSpecimen.actualCorner,
    InterfaceExtensionSpecimen.junction]
  incident_axis := by
    intro t ht
    simp [InterfaceExtensionSpecimen.actualCorner,
      InterfaceExtensionSpecimen.incident_curve,
      InterfaceExtensionSpecimen.incidentCurve]
    constructor <;> ring
  interface_axis := by
    intro t ht
    simp [InterfaceExtensionSpecimen.actualCorner,
      InterfaceExtensionSpecimen.interface_curve,
      InterfaceExtensionSpecimen.interfaceCurve]
  representative_local := by
    intro q hq
    change affineChart q ∈ InterfaceExtensionSpecimen.oldOpen ↔ q ∈ openCorner
    simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add] at hq
    constructor
    · intro hp
      have hy := oldOpen_height_gt_one hp
      have hx := oldOpen_left_lt hp
      rw [affineChart_apply] at hy hx
      unfold InterfaceExtensionSpecimen.oldLeft at hx
      change 0 < q.1 ∧ 0 < q.2
      constructor <;> linarith
    · rintro ⟨hq1, hq2⟩
      change affineChart q ∈ interior InterfaceExtensionSpecimen.oldRegion.carrier
      let i : Fin InterfaceExtensionSpecimen.oldRegion.bandCount :=
        ⟨0, by simp [InterfaceExtensionSpecimen.oldRegion]⟩
      let j : Fin (InterfaceExtensionSpecimen.oldRegion.componentCount i) :=
        ⟨0, by simp [i, InterfaceExtensionSpecimen.oldRegion]⟩
      apply interior_mono (show
        InterfaceExtensionSpecimen.oldRegion.componentCarrier i j ⊆
          InterfaceExtensionSpecimen.oldRegion.carrier by
        intro p hp
        rw [Region.carrier, mem_iUnion]
        refine ⟨i, ?_⟩
        rw [Region.bandCarrier, mem_iUnion]
        exact ⟨j, hp⟩)
      apply InterfaceExtensionSpecimen.oldRegion.mem_interior_componentCarrier_of_strict
      · rw [affineChart_apply]
        change 1 < 1 + 4 / 5 * q.1 ∧ 1 + 4 / 5 * q.1 < (9 : ℝ) / 5
        constructor <;> nlinarith [hq.1.2]
      · rw [affineChart_apply]
        change InterfaceExtensionSpecimen.oldLeft (1 + 4 / 5 * q.1) <
            -3 / 5 * q.1 + q.2 ∧
          -3 / 5 * q.1 + q.2 <
            InterfaceExtensionSpecimen.oldRight (1 + 4 / 5 * q.1)
        unfold InterfaceExtensionSpecimen.oldLeft InterfaceExtensionSpecimen.oldRight
        constructor <;> nlinarith [hq.2.1, hq.2.2]
  coordinateBound := 2
  coordinateBound_pos := by norm_num
  chart_coordinate_bound := by
    intro q hq
    simp only [affineChart_apply, InterfaceExtensionSpecimen.actualCorner,
      InterfaceExtensionSpecimen.junction, sub_zero]
    constructor
    · calc
        |-3 / 5 * q.1 + q.2| ≤ |-3 / 5 * q.1| + |q.2| := abs_add_le _ _
        _ = 3 / 5 * |q.1| + |q.2| := by rw [abs_mul]; norm_num
        _ ≤ 2 * (|q.1| + |q.2|) := by
          nlinarith [abs_nonneg q.1, abs_nonneg q.2]
    · rw [add_sub_cancel_left, abs_mul]
      norm_num
      nlinarith [abs_nonneg q.1, abs_nonneg q.2]

/-- The affine chart has the required first-order metric data. -/
theorem metricApplicability : affineApplicability.MetricApplicability where
  chart_contDiff := by
    change ContDiff ℝ 1 (fun q : PlanePoint =>
      (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1))
    fun_prop
  fderiv_incident := by
    change fderiv ℝ (fun q : PlanePoint =>
      (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) (0, 0) (1, 0) = _
    have hdiff : DifferentiableAt ℝ (fun q : PlanePoint =>
        (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) (0, 0) := by
      fun_prop
    have hin : HasDerivAt (fun t : ℝ => ((t, 0) : PlanePoint)) (1, 0) 0 := by
      convert (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk
        (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))) using 1
      all_goals norm_num
    have hcomp : HasDerivAt
        ((fun q : PlanePoint =>
          (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) ∘
            fun t : ℝ => ((t, 0) : PlanePoint))
        (fderiv ℝ (fun q : PlanePoint =>
          (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) (0, 0) (1, 0)) 0 :=
      hdiff.hasFDerivAt.comp_hasDerivAt
        (f := fun t : ℝ => ((t, 0) : PlanePoint)) (0 : ℝ) hin
    have hexp : HasDerivAt
        (fun t : ℝ => (-3 / 5 * t, 1 + 4 / 5 * t))
        ((-3 / 5, 4 / 5) : PlanePoint) 0 := by
      convert ((hasDerivAt_const (x := (0 : ℝ)) (c := (-3 / 5 : ℝ))).mul
        (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ))).prodMk
          ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
            ((hasDerivAt_const (x := (0 : ℝ)) (c := (4 / 5 : ℝ))).mul
              (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)))) using 1 <;>
        norm_num
    have heq :
        ((fun q : PlanePoint =>
          (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) ∘
            fun t : ℝ => ((t, 0) : PlanePoint)) =
          fun t : ℝ => (-3 / 5 * t, 1 + 4 / 5 * t) := by
      funext t
      simp
    rw [heq] at hcomp
    simpa [InterfaceExtensionSpecimen.actualCorner] using hcomp.unique hexp
  fderiv_interface := by
    change fderiv ℝ (fun q : PlanePoint =>
      (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) (0, 0) (0, 1) = _
    have hdiff : DifferentiableAt ℝ (fun q : PlanePoint =>
        (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) (0, 0) := by
      fun_prop
    have hin : HasDerivAt
        (fun t : ℝ => (((0 : ℝ), t) : PlanePoint)) ((0 : ℝ), (1 : ℝ)) 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).prodMk
        (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)) using 1
      all_goals norm_num
    have hcomp : HasDerivAt
        ((fun q : PlanePoint =>
          (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) ∘
            fun t : ℝ => (((0 : ℝ), t) : PlanePoint))
        (fderiv ℝ (fun q : PlanePoint =>
          (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) (0, 0) (0, 1)) 0 :=
      hdiff.hasFDerivAt.comp_hasDerivAt
        (f := fun t : ℝ => (((0 : ℝ), t) : PlanePoint)) (0 : ℝ) hin
    have hexp : HasDerivAt
        (fun t : ℝ => (t, (1 : ℝ))) (((1 : ℝ), (0 : ℝ)) : PlanePoint) 0 := by
      convert (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).prodMk
        (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))) using 1
      all_goals norm_num
    have heq :
        ((fun q : PlanePoint =>
          (-3 / 5 * q.1 + q.2, 1 + 4 / 5 * q.1)) ∘
            fun t : ℝ => (((0 : ℝ), t) : PlanePoint)) =
          fun t : ℝ => (t, (1 : ℝ)) := by
      funext t
      simp
    rw [heq] at hcomp
    simpa [InterfaceExtensionSpecimen.actualCorner] using hcomp.unique hexp
  connectorVelocity_ne := by
    simp [RegularCornerChartApplicability.connectorVelocity,
      InterfaceExtensionSpecimen.actualCorner]

/-- The signed interface axis stays on the upper strip interface. -/
theorem signedInterfaceApplicability :
    affineApplicability.SignedInterfaceApplicability where
  signed_interface_on_strip := by
    intro t ht
    simp [affineApplicability, StripInterface.height]

/-- The whole signed incident-side sector of the affine chart is exterior. -/
def signedIncidentPhaseApplicability :
    affineApplicability.SignedIncidentPhaseApplicability where
  phase := .exterior
  signed_right_sector_phase := by
    intro q hq hq1
    change 1 < |(affineChart q).2|
    rw [affineChart_apply, abs_of_pos]
    · linarith
    · linarith

/-- The incident parameter is already unit-speed. -/
theorem normalizedIncidentScale_eq_one :
    normalizedExtensionIncidentScale InterfaceExtensionSpecimen.actualCorner = 1 := by
  change (euclideanSpeed InterfaceExtensionSpecimen.incidentTrace.velocity)⁻¹ = 1
  rw [InterfaceExtensionSpecimen.incident_speed_one]
  norm_num

/-- At `lambda = 2`, the normalized interface parameter scale is `2/15`. -/
theorem normalizedInterfaceScale_two_eq :
    normalizedExtensionInterfaceScale InterfaceExtensionSpecimen.actualCorner 2 = 2 / 15 := by
  rw [normalizedExtensionInterfaceScale,
    InterfaceExtensionSpecimen.actualCorner_conormal_product]
  change extensionEndpointRatio 2 (-3 / 5) *
    (euclideanSpeed InterfaceExtensionSpecimen.interfaceTrace.velocity)⁻¹ = 2 / 15
  rw [InterfaceExtensionSpecimen.interface_speed_one]
  norm_num [extensionEndpointRatio]

/-- The endpoint-normalized applicability used by the descending extension
family.  Its representative is definitionally the unchanged affine specimen;
only the two source parameters are positively rescaled. -/
def normalizedApplicability :
    RegularCornerChartApplicability
      (InterfaceExtensionSpecimen.actualCorner.positiveDiagonalReparam
        (normalizedExtensionIncidentScale InterfaceExtensionSpecimen.actualCorner)
        (normalizedExtensionInterfaceScale InterfaceExtensionSpecimen.actualCorner 2)
        normalizedExtensionIncidentScale_pos
        (normalizedExtensionInterfaceScale_pos (by norm_num)
          (by rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]
              norm_num))) :=
  affineApplicability.positiveDiagonalReparam
    (normalizedExtensionIncidentScale InterfaceExtensionSpecimen.actualCorner)
    (normalizedExtensionInterfaceScale InterfaceExtensionSpecimen.actualCorner 2)
    normalizedExtensionIncidentScale_pos
    (normalizedExtensionInterfaceScale_pos (by norm_num)
      (by rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]
          norm_num))

/-- The generic normalized extension theorem gives a strict local cost decrease
for the literal specimen at `lambda = 2`. -/
theorem eventually_normalizedExtension_local_inside_cost_lt :
    let a := normalizedExtensionIncidentScale InterfaceExtensionSpecimen.actualCorner
    let b := normalizedExtensionInterfaceScale InterfaceExtensionSpecimen.actualCorner 2
    let A' := affineApplicability.positiveDiagonalReparam a b
      normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos (by norm_num)
        (by rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]; norm_num))
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCostOn 2 (A'.extensionLocalModel r) (interior (A'.window r)) <
        smoothCostOn 2 InterfaceExtensionSpecimen.actualCorner.representative
          (interior (A'.window r)) := by
  apply affineApplicability.eventually_normalizedExtension_local_inside_cost_lt_of_conormal_lt
    metricApplicability signedInterfaceApplicability signedIncidentPhaseApplicability 2
  · norm_num
  · rfl
  · rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]
    norm_num

/-- The normalized specimen extension has a uniform linear complete-frontier
gain, not merely a qualitative strict decrease. -/
theorem eventually_normalizedExtension_complete_cost_add_linear_le :
    ∃ k > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost 2 (normalizedApplicability.extensionCompetitor r) +
          ENNReal.ofReal (k * r) ≤
        smoothCost 2 InterfaceExtensionSpecimen.actualCorner.representative := by
  simpa [normalizedApplicability,
    InterfaceExtensionSpecimen.actualCorner] using
    affineApplicability.eventually_normalizedExtension_complete_cost_add_linear_le_of_conormal_lt
      metricApplicability signedInterfaceApplicability
        signedIncidentPhaseApplicability 2 (by norm_num) rfl
          (by rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]
              norm_num)

/-- The unchanged finite-band representative has finite complete cost. -/
theorem actualCorner_smoothCost_eq :
    smoothCost 2 InterfaceExtensionSpecimen.actualCorner.representative =
      ENNReal.ofReal 7 := by
  rw [show InterfaceExtensionSpecimen.actualCorner.representative =
    InterfaceExtensionSpecimen.oldOpen from rfl]
  rw [smoothCost_eq_weightedTraceCost_frontier]
  rw [InterfaceExtensionSpecimen.frontier_oldOpen,
    InterfaceExtensionSpecimen.old_complete_frontier_cost]

/-- The generic extension family consists of actual localized competitors and
strictly lowers their complete frontier cost at all sufficiently small scales. -/
theorem eventually_normalizedExtension_complete_cost_lt :
    let a := normalizedExtensionIncidentScale InterfaceExtensionSpecimen.actualCorner
    let b := normalizedExtensionInterfaceScale InterfaceExtensionSpecimen.actualCorner 2
    let A' := affineApplicability.positiveDiagonalReparam a b
      normalizedExtensionIncidentScale_pos
      (normalizedExtensionInterfaceScale_pos (by norm_num)
        (by rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]; norm_num))
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      smoothCost 2 (A'.extensionCompetitor r) <
        smoothCost 2 InterfaceExtensionSpecimen.actualCorner.representative := by
  dsimp only
  let a := normalizedExtensionIncidentScale InterfaceExtensionSpecimen.actualCorner
  let b := normalizedExtensionInterfaceScale InterfaceExtensionSpecimen.actualCorner 2
  have ha : 0 < a := normalizedExtensionIncidentScale_pos
  have hb : 0 < b := normalizedExtensionInterfaceScale_pos (by norm_num)
    (by rw [InterfaceExtensionSpecimen.actualCorner_conormal_product]; norm_num)
  let A' := affineApplicability.positiveDiagonalReparam a b ha hb
  have hinside := eventually_normalizedExtension_local_inside_cost_lt
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < A'.localRadius :=
    ((eventually_lt_nhds (half_pos A'.localRadius_pos)).filter_mono inf_le_left).mono
      (fun _ hr => by linarith)
  have htotal :
      smoothCost 2 InterfaceExtensionSpecimen.actualCorner.representative < ⊤ := by
    rw [actualCorner_smoothCost_eq]
    simp
  filter_upwards [self_mem_nhdsWithin, hinside, hsmall] with r hr hrInside hrLocal
  apply ExtensionMetricApplicability.extensionCompetitor_complete_cost_lt_of_local_inside_cost_lt
    (A := A') hr hrLocal hrInside
  apply ne_of_lt
  calc
    smoothCostOn 2 InterfaceExtensionSpecimen.actualCorner.representative
        (interior (A'.window r))ᶜ ≤
        smoothCostOn 2 InterfaceExtensionSpecimen.actualCorner.representative univ :=
      smoothCostOn_mono 2 InterfaceExtensionSpecimen.actualCorner.representative
        (subset_univ _)
    _ = smoothCost 2 InterfaceExtensionSpecimen.actualCorner.representative := by
      simp only [smoothCostOn, smoothCost, Measure.restrict_univ]
    _ < ⊤ := htotal

end CMVRelaxation.InterfaceExtensionGenericSpecimen
