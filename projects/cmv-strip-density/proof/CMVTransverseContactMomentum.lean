import CMVTransverseContactVariation
import CMVRelativeLevelTraceAveraging

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval symmDiff ENNReal

noncomputable section

namespace CMVTransverseContactVariation
open CMVTwoPatchGraphVariation

namespace HorizontalGraphPatch

/-- Open graph trace; omitted endpoints have zero one-dimensional cost. -/
def openGraphTrace (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t : ℝ) : Set PlanePoint :=
  (fun y : ℝ => (P.variedGraph v t y, y)) '' Ioo P.a P.b

/-- Real constant-zone weighted Euclidean graph length. -/
def weightedGraphLength (lam : ℝ) (P : HorizontalGraphPatch)
    (v : ℝ → ℝ) (t : ℝ) : ℝ :=
  P.zone.weight lam * ∫ y in P.a..P.b,
    Real.sqrt (1 + (deriv (P.variedGraph v t) y) ^ 2)

lemma variedGraph_contDiff (P : HorizontalGraphPatch) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) (t : ℝ) :
    ContDiff ℝ 2 (P.variedGraph v t) := by
  unfold variedGraph
  exact P.graph_contDiff.add (contDiff_const.mul hv)

lemma deriv_variedGraph (P : HorizontalGraphPatch) {v : ℝ → ℝ}
    (hv : Differentiable ℝ v) (t y : ℝ) :
    deriv (P.variedGraph v t) y = deriv P.graph y + t * deriv v y := by
  change deriv (P.graph + fun z => t * v z) y = _
  simpa only [deriv_const_mul_field] using
    deriv_add (P.graph_contDiff.differentiable (by norm_num) y) ((hv y).const_mul t)

/-- First variation of the real weighted Euclidean graph length. -/
theorem weightedGraphLength_hasDerivAt
    (lam : ℝ) (P : HorizontalGraphPatch) {v : ℝ → ℝ}
    (hv : ContDiff ℝ 2 v) :
    HasDerivAt (P.weightedGraphLength lam v)
      (P.zone.weight lam * ∫ y in P.a..P.b,
        deriv P.graph y * deriv v y /
          Real.sqrt (1 + (deriv P.graph y) ^ 2)) 0 := by
  have hbase := graphLengthIntegral_hasDerivAt
    (a := P.a) (b := P.b) (p := deriv P.graph) (q := deriv v)
    (P.graph_contDiff.continuous_deriv (by norm_num))
    (hv.continuous_deriv (by norm_num))
  have hscaled := hbase.const_mul (P.zone.weight lam)
  apply hscaled.congr_of_eventuallyEq
  filter_upwards with t
  unfold weightedGraphLength
  congr 2
  funext y
  rw [P.deriv_variedGraph (hv.differentiable (by norm_num))]

/-- The graph functional is the actual density-weighted Euclidean H1 cost of
its open literal trace. -/
theorem weightedTraceCost_openGraphTrace_eq
    {lam : ℝ} (hlam : 1 < lam) (P : HorizontalGraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) {t : ℝ}
    (hshift : ∀ y ∈ Ioo P.a P.b, |t * v y| ≤ T.radius) :
    CMVRelaxation.weightedTraceCost lam (P.openGraphTrace v t) =
      ENNReal.ofReal (P.weightedGraphLength lam v t) := by
  have hg : ContDiff ℝ 1 (P.variedGraph v t) :=
    (P.variedGraph_contDiff hv t).of_le (by norm_num)
  have hdensity : ∀ p ∈ P.openGraphTrace v t,
      StripDensity lam p = P.zone.weight lam := by
    rintro _ ⟨y, hy, rfl⟩
    apply DensityZone.stripDensity_eq_weight
    apply T.tube_in_zone y hy
    simpa only [HorizontalGraphPatch.variedGraph, add_sub_cancel_left] using hshift y hy
  unfold openGraphTrace
  rw [CMVRelaxation.weightedTraceCost_horizontalGraph_image_eq_const_mul_setLIntegral
    lam (P.zone.weight lam) hg measurableSet_Ioo hdensity]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · rw [← ENNReal.ofReal_mul (DensityZone.weight_pos (zone := P.zone) hlam).le]
    congr 1
    unfold weightedGraphLength
    congr 1
    rw [intervalIntegral.integral_of_le P.a_lt_b.le,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  · exact (continuous_const.add ((hg.continuous_deriv (by norm_num)).pow 2)).sqrt
      |>.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  · exact Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _

theorem weightedTraceCost_singleton (lam : ℝ) (p : PlanePoint) :
    CMVRelaxation.weightedTraceCost lam {p} = 0 := by
  unfold CMVRelaxation.weightedTraceCost
  rw [show planeEuclideanHomeomorph '' ({p} : Set PlanePoint) =
      {planeEuclideanHomeomorph p} by simp]
  apply setLIntegral_measure_zero
  exact
    (MeasureTheory.Measure.nullSingletonClass_hausdorff
      EuclideanPlane (by norm_num)).measure_singleton _
theorem weightedTraceCost_insert (lam : ℝ) (p : PlanePoint)
    (S : Set PlanePoint) :
    CMVRelaxation.weightedTraceCost lam (insert p S) =
      CMVRelaxation.weightedTraceCost lam S := by
  by_cases hp : p ∈ S
  · rw [insert_eq_of_mem hp]
  · unfold CMVRelaxation.weightedTraceCost
    rw [Set.image_insert_eq]
    rw [MeasureTheory.lintegral_insert]
    · have hsingle :
          (μH[1] : Measure EuclideanPlane) {planeEuclideanHomeomorph p} = 0 :=
        (MeasureTheory.Measure.nullSingletonClass_hausdorff
          EuclideanPlane (by norm_num)).measure_singleton _
      rw [hsingle, mul_zero, zero_add]
    · intro himage
      rcases himage with ⟨q, hq, heq⟩
      apply hp
      exact planeEuclideanHomeomorph.injective heq ▸ hq

/-- Closed graph trace; both omitted endpoints are restored explicitly. -/
def closedGraphTrace (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t : ℝ) :
    Set PlanePoint :=
  (fun y : ℝ => (P.variedGraph v t y, y)) '' Icc P.a P.b

lemma closedGraphTrace_eq_insert_open (P : HorizontalGraphPatch)
    (v : ℝ → ℝ) (t : ℝ) :
    P.closedGraphTrace v t =
      insert (P.variedGraph v t P.a, P.a)
        (insert (P.variedGraph v t P.b, P.b) (P.openGraphTrace v t)) := by
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hya : y = P.a
    · subst y
      exact Set.mem_insert _ _
    by_cases hyb : y = P.b
    · subst y
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    exact Set.mem_insert_of_mem _ <| Set.mem_insert_of_mem _ <|
      ⟨y, ⟨lt_of_le_of_ne hy.1 (Ne.symm hya),
        lt_of_le_of_ne hy.2 hyb⟩, rfl⟩
  · simp only [Set.mem_insert_iff, openGraphTrace]
    rintro (rfl | rfl | ⟨y, hy, rfl⟩)
    · exact ⟨P.a, left_mem_Icc.mpr P.a_lt_b.le, rfl⟩
    · exact ⟨P.b, right_mem_Icc.mpr P.a_lt_b.le, rfl⟩
    · exact ⟨y, ⟨hy.1.le, hy.2.le⟩, rfl⟩

/-- Restoring every graph endpoint, including the common contact singleton,
does not alter its density-weighted Euclidean H1 cost. -/
theorem weightedTraceCost_closedGraphTrace_eq_open
    (lam : ℝ) (P : HorizontalGraphPatch) (v : ℝ → ℝ) (t : ℝ) :
    CMVRelaxation.weightedTraceCost lam (P.closedGraphTrace v t) =
      CMVRelaxation.weightedTraceCost lam (P.openGraphTrace v t) := by
  rw [P.closedGraphTrace_eq_insert_open,
    weightedTraceCost_insert, weightedTraceCost_insert]

end HorizontalGraphPatch

namespace ContactData

/-- Sum of all three changed graph lengths at fixed contact-support radius. -/
def totalWeightedGraphLength (lam : ℝ) (D : ContactData) (t : ℝ) : ℝ :=
  D.minus.weightedGraphLength lam D.minusVelocity t +
    D.plus.weightedGraphLength lam D.plusVelocity t +
      D.compensation.weightedGraphLength lam (D.compensationVelocity lam) t

/-- Derivative of the complete fixed-radius graph functional. -/
def contactFirstVariation (lam : ℝ) (D : ContactData) : ℝ :=
  D.minus.zone.weight lam *
      (∫ y in D.minus.a..D.minus.b,
        contactMomentum D.minus y * deriv D.minusVelocity y) +
    D.plus.zone.weight lam *
      (∫ y in D.plus.a..D.plus.b,
        contactMomentum D.plus y * deriv D.plusVelocity y) +
    D.compensation.zone.weight lam *
      (∫ y in D.compensation.a..D.compensation.b,
        contactMomentum D.compensation y *
          deriv (D.compensationVelocity lam) y)

/-- The variation parameter is differentiated at zero while the contact
support radius remains fixed. -/
theorem totalWeightedGraphLength_hasDerivAt
    (lam : ℝ) (D : ContactData) :
    HasDerivAt (D.totalWeightedGraphLength lam)
      (D.contactFirstVariation lam) 0 := by
  have hm := D.minus.weightedGraphLength_hasDerivAt
    lam D.minusVelocity_contDiff
  have hp := D.plus.weightedGraphLength_hasDerivAt
    lam D.plusVelocity_contDiff
  have hc := D.compensation.weightedGraphLength_hasDerivAt
    lam (D.compensationVelocity_contDiff lam)
  have hfun :
      D.totalWeightedGraphLength lam =
        D.minus.weightedGraphLength lam D.minusVelocity +
          D.plus.weightedGraphLength lam D.plusVelocity +
            D.compensation.weightedGraphLength
              lam (D.compensationVelocity lam) := rfl
  rw [hfun]
  apply ((hm.add hp).add hc).congr_deriv
  unfold contactFirstVariation contactMomentum
  simp only [div_mul_eq_mul_div]

end ContactData

/-- Derivative of horizontal graph momentum in the increasing-y orientation. -/
def contactCurvature (P : HorizontalGraphPatch) (y : ℝ) : ℝ :=
  deriv (deriv P.graph) y /
    Real.sqrt (1 + (deriv P.graph y) ^ 2) ^ 3

namespace HorizontalGraphPatch

lemma contactMomentum_contDiff (P : HorizontalGraphPatch) :
    ContDiff ℝ 1 (contactMomentum P) := by
  unfold contactMomentum
  have hd : ContDiff ℝ 1 (deriv P.graph) :=
    (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
  apply ContDiff.div
  · exact hd
  · exact (contDiff_const.add (hd.pow 2)).sqrt
      (by intro y; positivity)
  · intro y
    positivity

lemma contactCurvature_continuous (P : HorizontalGraphPatch) :
    Continuous (contactCurvature P) := by
  unfold contactCurvature
  have hd : ContDiff ℝ 1 (deriv P.graph) :=
    (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
  apply Continuous.div
  · exact hd.continuous_deriv (by norm_num)
  · exact ((continuous_const.add (hd.continuous.pow 2)).sqrt.pow 3)
  · intro y
    positivity

theorem contactMomentum_hasDerivAt (P : HorizontalGraphPatch) (y : ℝ) :
    HasDerivAt (contactMomentum P) (contactCurvature P y) y := by
  have hd : ContDiff ℝ 1 (deriv P.graph) :=
    (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
  have hu : HasDerivAt (deriv P.graph) (deriv (deriv P.graph) y) y :=
    (hd.differentiable (by norm_num) y).hasDerivAt
  have hinner : HasDerivAt (fun z : ℝ => 1 + (deriv P.graph z) ^ 2)
      (2 * deriv P.graph y * deriv (deriv P.graph) y) y := by
    simpa only [Pi.add_apply, Pi.pow_apply] using!
      ((hasDerivAt_const y 1).add (hu.pow 2)).congr_deriv (by norm_num)
  have hroot : Real.sqrt (1 + (deriv P.graph y) ^ 2) ≠ 0 := by
    positivity
  have hraw := hu.div (hinner.sqrt (by positivity)) hroot
  apply hraw.congr_deriv
  change
    (deriv (deriv P.graph) y * Real.sqrt (1 + deriv P.graph y ^ 2) -
        deriv P.graph y *
          (2 * deriv P.graph y * deriv (deriv P.graph) y /
            (2 * Real.sqrt (1 + deriv P.graph y ^ 2)))) /
        Real.sqrt (1 + deriv P.graph y ^ 2) ^ 2 =
      deriv (deriv P.graph) y /
        Real.sqrt (1 + deriv P.graph y ^ 2) ^ 3
  have hsq : Real.sqrt (1 + deriv P.graph y ^ 2) ^ 2 =
      1 + deriv P.graph y ^ 2 :=
    Real.sq_sqrt (by positivity)
  field_simp [hroot]
  rw [hsq]
  ring

end HorizontalGraphPatch

namespace ContactData

/-- Integration by parts isolates the incoming contact momentum. -/
theorem minus_firstVariation_eq_contact_sub_remainder (D : ContactData) :
    (∫ y in D.minus.a..D.minus.b,
        contactMomentum D.minus y * deriv D.minusVelocity y) =
      contactMomentum D.minus D.interfaceY -
        ∫ y in D.minus.a..D.minus.b,
          contactCurvature D.minus y * D.minusVelocity y := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := D.minus.a) (b := D.minus.b)
    (u := contactMomentum D.minus) (v := D.minusVelocity)
    (u' := contactCurvature D.minus) (v' := deriv D.minusVelocity)
    (fun y _ => D.minus.contactMomentum_hasDerivAt y)
    (fun y _ =>
      (D.minusVelocity_contDiff.differentiable (by norm_num) y).hasDerivAt)
    (D.minus.contactCurvature_continuous.intervalIntegrable _ _)
    ((D.minusVelocity_contDiff.continuous_deriv (by norm_num)).intervalIntegrable _ _)
  have ha : D.minusVelocity D.minus.a = 0 := by
    apply D.minusVelocity_eq_zero_of_outer
    rw [D.minus_a]
    linarith [D.rho_pos]
  have hb : D.minusVelocity D.minus.b = 1 := by
    rw [D.minus_b]
    exact D.minusVelocity_contact
  rw [hb, ha, mul_one, mul_zero, sub_zero] at hparts
  have hmom :
      contactMomentum D.minus D.minus.b =
        contactMomentum D.minus D.interfaceY := by
    rw [D.minus_b]
  rw [hmom] at hparts
  exact hparts

/-- Integration by parts isolates minus the outgoing contact momentum. -/
theorem plus_firstVariation_eq_neg_contact_sub_remainder (D : ContactData) :
    (∫ y in D.plus.a..D.plus.b,
        contactMomentum D.plus y * deriv D.plusVelocity y) =
      -contactMomentum D.plus D.interfaceY -
        ∫ y in D.plus.a..D.plus.b,
          contactCurvature D.plus y * D.plusVelocity y := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := D.plus.a) (b := D.plus.b)
    (u := contactMomentum D.plus) (v := D.plusVelocity)
    (u' := contactCurvature D.plus) (v' := deriv D.plusVelocity)
    (fun y _ => D.plus.contactMomentum_hasDerivAt y)
    (fun y _ =>
      (D.plusVelocity_contDiff.differentiable (by norm_num) y).hasDerivAt)
    (D.plus.contactCurvature_continuous.intervalIntegrable _ _)
    ((D.plusVelocity_contDiff.continuous_deriv (by norm_num)).intervalIntegrable _ _)
  have hb : D.plusVelocity D.plus.b = 0 := by
    apply D.plusVelocity_eq_zero_of_outer
    rw [D.plus_b]
    linarith [D.rho_pos]
  have ha : D.plusVelocity D.plus.a = 1 := by
    rw [D.plus_a]
    exact D.plusVelocity_contact
  rw [ha, hb, mul_zero, mul_one, zero_sub] at hparts
  have hmom :
      contactMomentum D.plus D.plus.a =
        contactMomentum D.plus D.interfaceY := by
    rw [D.plus_a]
  rw [hmom] at hparts
  exact hparts

/-- Fixed remote-patch response to its normalized unit compensation bump. -/
def compensationMomentumResponse (D : ContactData) : ℝ :=
  ∫ y in D.compensation.a..D.compensation.b,
    contactMomentum D.compensation y *
      deriv D.compensation.compensationBump y

end ContactData

namespace HorizontalGraphPatch


lemma compensationBump_left_eq_zero (P : HorizontalGraphPatch) :
    P.compensationBump P.a = 0 := by
  by_contra hne
  have hsupport : P.a ∈ support P.compensationBump := hne
  have hinside := P.tsupport_compensationBump_subset
    (subset_tsupport P.compensationBump hsupport)
  exact (lt_irrefl P.a hinside.1)

lemma compensationBump_right_eq_zero (P : HorizontalGraphPatch) :
    P.compensationBump P.b = 0 := by
  by_contra hne
  have hsupport : P.b ∈ support P.compensationBump := hne
  have hinside := P.tsupport_compensationBump_subset
    (subset_tsupport P.compensationBump hsupport)
  exact (lt_irrefl P.b hinside.2)

end HorizontalGraphPatch

namespace ContactData

/-- The compensation derivative is integrated by parts before estimating it.
The normalized bump therefore contributes no inverse support-radius factor. -/
theorem compensationMomentumResponse_eq_neg_curvature_average
    (D : ContactData) :
    D.compensationMomentumResponse =
      -∫ y in D.compensation.a..D.compensation.b,
        contactCurvature D.compensation y *
          D.compensation.compensationBump y := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := D.compensation.a) (b := D.compensation.b)
    (u := contactMomentum D.compensation)
    (v := D.compensation.compensationBump)
    (u' := contactCurvature D.compensation)
    (v' := deriv D.compensation.compensationBump)
    (fun y _ => D.compensation.contactMomentum_hasDerivAt y)
    (fun y _ =>
      (D.compensation.compensationBump_contDiff.differentiable
        (by simp) y).hasDerivAt)
    (D.compensation.contactCurvature_continuous.intervalIntegrable _ _)
    ((D.compensation.compensationBump_contDiff.continuous_deriv
      (by simp)).intervalIntegrable _ _)
  rw [D.compensation.compensationBump_left_eq_zero,
    D.compensation.compensationBump_right_eq_zero,
    mul_zero, mul_zero, sub_zero, zero_sub] at hparts
  unfold compensationMomentumResponse
  exact hparts

/-- A curvature bound controls the remote response by the same constant,
independently of the compensation interval width. -/
theorem abs_compensationMomentumResponse_le (D : ContactData) {M : ℝ}
    (hcurvature : ∀ y ∈ Icc D.compensation.a D.compensation.b,
      |contactCurvature D.compensation y| ≤ M) :
    |D.compensationMomentumResponse| ≤ M := by
  rw [D.compensationMomentumResponse_eq_neg_curvature_average, abs_neg]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume)
    (f := fun y => contactCurvature D.compensation y *
      D.compensation.compensationBump y)
    (g := fun y => M * D.compensation.compensationBump y)
    D.compensation.a_lt_b.le
    (Filter.Eventually.of_forall fun y hy => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (D.compensation.compensationBump_nonneg y)]
      exact mul_le_mul_of_nonneg_right
        (hcurvature y ⟨hy.1.le, hy.2⟩)
        (D.compensation.compensationBump_nonneg y))
    ((continuous_const.mul
      D.compensation.compensationBump_contDiff.continuous).intervalIntegrable
        _ _)
  rw [Real.norm_eq_abs,
    intervalIntegral.integral_const_mul,
    D.compensation.intervalIntegral_compensationBump, mul_one] at hbound
  exact hbound
theorem compensation_firstVariation_eq_coefficient_mul_response
    (lam : ℝ) (D : ContactData) :
    (∫ y in D.compensation.a..D.compensation.b,
        contactMomentum D.compensation y *
          deriv (D.compensationVelocity lam) y) =
      D.compensationCoefficient lam * D.compensationMomentumResponse := by
  calc
    (∫ y in D.compensation.a..D.compensation.b,
        contactMomentum D.compensation y *
          deriv (D.compensationVelocity lam) y) =
        ∫ y in D.compensation.a..D.compensation.b,
          D.compensationCoefficient lam *
            (contactMomentum D.compensation y *
              deriv D.compensation.compensationBump y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      have hderiv :
          deriv (D.compensationVelocity lam) y =
            D.compensationCoefficient lam *
              deriv D.compensation.compensationBump y := by
        unfold compensationVelocity
        rw [deriv_const_mul_field]
      change contactMomentum D.compensation y *
          deriv (D.compensationVelocity lam) y =
        D.compensationCoefficient lam *
          (contactMomentum D.compensation y *
            deriv D.compensation.compensationBump y)
      rw [hderiv]
      ring
    _ = D.compensationCoefficient lam * D.compensationMomentumResponse := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- Exact decomposition into the contact momentum jump and three controlled
fixed-radius remainders. -/
theorem contactFirstVariation_eq_transmissionDefect_sub_remainders
    (lam : ℝ) (D : ContactData) :
    D.contactFirstVariation lam =
      transmissionDefect lam D -
        D.minus.zone.weight lam *
          (∫ y in D.minus.a..D.minus.b,
            contactCurvature D.minus y * D.minusVelocity y) -
        D.plus.zone.weight lam *
          (∫ y in D.plus.a..D.plus.b,
            contactCurvature D.plus y * D.plusVelocity y) +
        D.compensation.zone.weight lam *
          D.compensationCoefficient lam *
            D.compensationMomentumResponse := by
  rw [contactFirstVariation, D.minus_firstVariation_eq_contact_sub_remainder,
    D.plus_firstVariation_eq_neg_contact_sub_remainder,
    D.compensation_firstVariation_eq_coefficient_mul_response]
  unfold transmissionDefect
  ring

private lemma abs_integral_contactCurvature_mul_le
    (P : HorizontalGraphPatch) {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hcurvature : ∀ y ∈ uIcc a b, |contactCurvature P y| ≤ M)
    {v : ℝ → ℝ} (hv : ∀ y, |v y| ≤ 1) :
    |∫ y in a..b, contactCurvature P y * v y| ≤ M * (b - a) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := M)
    (f := fun y => contactCurvature P y * v y)
    (fun y hy => by
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |contactCurvature P y| * |v y| ≤ M * 1 :=
          mul_le_mul (hcurvature y (uIoc_subset_uIcc hy)) (hv y)
            (abs_nonneg _) hM
        _ = M := mul_one M)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  exact hbound

theorem abs_minus_curvature_remainder_le
    (D : ContactData) {M : ℝ} (hM : 0 ≤ M)
    (hcurvature : ∀ y ∈ Icc D.minus.a D.minus.b,
      |contactCurvature D.minus y| ≤ M) :
    |∫ y in D.minus.a..D.minus.b,
        contactCurvature D.minus y * D.minusVelocity y| ≤
      M * D.rho := by
  have hbound := abs_integral_contactCurvature_mul_le D.minus
    D.minus.a_lt_b.le hM (by
      intro y hy
      rw [uIcc_of_le D.minus.a_lt_b.le] at hy
      exact hcurvature y hy) D.abs_minusVelocity_le_one
  have hwidth : D.minus.b - D.minus.a = D.rho := by
    rw [D.minus_a, D.minus_b]
    ring
  rwa [hwidth] at hbound

theorem abs_plus_curvature_remainder_le
    (D : ContactData) {M : ℝ} (hM : 0 ≤ M)
    (hcurvature : ∀ y ∈ Icc D.plus.a D.plus.b,
      |contactCurvature D.plus y| ≤ M) :
    |∫ y in D.plus.a..D.plus.b,
        contactCurvature D.plus y * D.plusVelocity y| ≤
      M * D.rho := by
  have hbound := abs_integral_contactCurvature_mul_le D.plus
    D.plus.a_lt_b.le hM (by
      intro y hy
      rw [uIcc_of_le D.plus.a_lt_b.le] at hy
      exact hcurvature y hy) D.abs_plusVelocity_le_one
  have hwidth : D.plus.b - D.plus.a = D.rho := by
    rw [D.plus_a, D.plus_b]
    ring
  rwa [hwidth] at hbound

private lemma DensityZone.weight_le_lam
    {lam : ℝ} (hlam : 1 < lam) (zone : DensityZone) :
    zone.weight lam ≤ lam := by
  cases zone with
  | interior =>
      simp [DensityZone.weight]
      linarith
  | exterior => simp [DensityZone.weight]

/-- Quantitative fixed-radius error estimate.  Every remainder is `O(rho)`;
no derivative of a rescaled cutoff is estimated directly. -/
theorem abs_contactFirstVariation_sub_transmissionDefect_le
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData) {M : ℝ} (hM : 0 ≤ M)
    (hminus : ∀ y ∈ Icc D.minus.a D.minus.b,
      |contactCurvature D.minus y| ≤ M)
    (hplus : ∀ y ∈ Icc D.plus.a D.plus.b,
      |contactCurvature D.plus y| ≤ M)
    (hcompensation : ∀ y ∈ Icc D.compensation.a D.compensation.b,
      |contactCurvature D.compensation y| ≤ M) :
    |D.contactFirstVariation lam - transmissionDefect lam D| ≤
      ((2 * lam + lam * (lam + 1)) * M) * D.rho := by
  let Rm := ∫ y in D.minus.a..D.minus.b,
    contactCurvature D.minus y * D.minusVelocity y
  let Rp := ∫ y in D.plus.a..D.plus.b,
    contactCurvature D.plus y * D.plusVelocity y
  let Rc := D.compensationMomentumResponse
  let c := D.compensationCoefficient lam
  have hRm : |Rm| ≤ M * D.rho :=
    D.abs_minus_curvature_remainder_le hM hminus
  have hRp : |Rp| ≤ M * D.rho :=
    D.abs_plus_curvature_remainder_le hM hplus
  have hRc : |Rc| ≤ M :=
    D.abs_compensationMomentumResponse_le hcompensation
  have hc : |c| ≤ (lam + 1) * D.rho :=
    D.abs_compensationCoefficient_le_lam_add_one_mul_rho hlam
  have hwm : 0 < D.minus.zone.weight lam :=
    DensityZone.weight_pos hlam
  have hwp : 0 < D.plus.zone.weight lam :=
    DensityZone.weight_pos hlam
  have hwc : 0 < D.compensation.zone.weight lam :=
    DensityZone.weight_pos hlam
  have hwml : D.minus.zone.weight lam ≤ lam :=
    DensityZone.weight_le_lam hlam D.minus.zone
  have hwpl : D.plus.zone.weight lam ≤ lam :=
    DensityZone.weight_le_lam hlam D.plus.zone
  have hwcl : D.compensation.zone.weight lam ≤ lam :=
    DensityZone.weight_le_lam hlam D.compensation.zone
  have hlam1 : 0 ≤ lam + 1 := by linarith
  have hrho : 0 ≤ D.rho := D.rho_pos.le
  rw [D.contactFirstVariation_eq_transmissionDefect_sub_remainders]
  change
    |transmissionDefect lam D -
          D.minus.zone.weight lam * Rm -
          D.plus.zone.weight lam * Rp +
          D.compensation.zone.weight lam * c * Rc -
        transmissionDefect lam D| ≤ _
  calc
    |transmissionDefect lam D -
          D.minus.zone.weight lam * Rm -
          D.plus.zone.weight lam * Rp +
          D.compensation.zone.weight lam * c * Rc -
        transmissionDefect lam D| =
        |-D.minus.zone.weight lam * Rm -
          D.plus.zone.weight lam * Rp +
          D.compensation.zone.weight lam * c * Rc| := by
      congr 1
      ring
    _ ≤ |D.minus.zone.weight lam * Rm| +
          |D.plus.zone.weight lam * Rp| +
          |D.compensation.zone.weight lam * c * Rc| := by
      calc
        |(-D.minus.zone.weight lam * Rm -
            D.plus.zone.weight lam * Rp) +
            D.compensation.zone.weight lam * c * Rc| ≤
            |(-D.minus.zone.weight lam * Rm -
              D.plus.zone.weight lam * Rp)| +
              |D.compensation.zone.weight lam * c * Rc| :=
          abs_add_le _ _
        _ ≤ (|-D.minus.zone.weight lam * Rm| +
              |-D.plus.zone.weight lam * Rp|) +
              |D.compensation.zone.weight lam * c * Rc| :=
          by
            have habs :
                |-D.minus.zone.weight lam * Rm -
                    D.plus.zone.weight lam * Rp| ≤
                  |-D.minus.zone.weight lam * Rm| +
                    |-D.plus.zone.weight lam * Rp| := by
              rw [show -D.minus.zone.weight lam * Rm -
                  D.plus.zone.weight lam * Rp =
                (-D.minus.zone.weight lam * Rm) +
                  (-D.plus.zone.weight lam * Rp) by ring]
              exact abs_add_le _ _
            exact add_le_add habs le_rfl
        _ = |D.minus.zone.weight lam * Rm| +
              |D.plus.zone.weight lam * Rp| +
              |D.compensation.zone.weight lam * c * Rc| := by
          rw [show -D.minus.zone.weight lam * Rm =
              -(D.minus.zone.weight lam * Rm) by ring,
            show -D.plus.zone.weight lam * Rp =
              -(D.plus.zone.weight lam * Rp) by ring,
            abs_neg, abs_neg]
    _ = D.minus.zone.weight lam * |Rm| +
          D.plus.zone.weight lam * |Rp| +
          D.compensation.zone.weight lam * |c| * |Rc| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos hwm, abs_of_pos hwp, abs_of_pos hwc]
    _ ≤ lam * (M * D.rho) +
          lam * (M * D.rho) +
          lam * ((lam + 1) * D.rho) * M := by
      gcongr
    _ = ((2 * lam + lam * (lam + 1)) * M) * D.rho := by
      ring

/-- Once the `O(rho)` error is smaller than a nonzero contact defect, the
complete fixed-radius graph derivative cannot vanish. -/
theorem contactFirstVariation_ne_zero_of_error_lt_abs_transmissionDefect
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData) {M : ℝ} (hM : 0 ≤ M)
    (hminus : ∀ y ∈ Icc D.minus.a D.minus.b,
      |contactCurvature D.minus y| ≤ M)
    (hplus : ∀ y ∈ Icc D.plus.a D.plus.b,
      |contactCurvature D.plus y| ≤ M)
    (hcompensation : ∀ y ∈ Icc D.compensation.a D.compensation.b,
      |contactCurvature D.compensation y| ≤ M)
    (hsmall :
      ((2 * lam + lam * (lam + 1)) * M) * D.rho <
        |transmissionDefect lam D|) :
    D.contactFirstVariation lam ≠ 0 := by
  intro hzero
  have hbound := D.abs_contactFirstVariation_sub_transmissionDefect_le
    hlam hM hminus hplus hcompensation
  rw [hzero, zero_sub, abs_neg] at hbound
  exact (not_lt_of_ge hbound) hsmall


/-- After differentiating each fixed-radius family, the residual against the
contact momentum jump vanishes as the support radii shrink. -/
theorem tendsto_contactFirstVariation_sub_transmissionDefect
    {α : Type*} {l : Filter α} {lam M : ℝ} (hlam : 1 < lam) (hM : 0 ≤ M)
    (D : α → ContactData)
    (hrho : Tendsto (fun i => (D i).rho) l (𝓝 0))
    (hminus : ∀ᶠ i in l, ∀ y ∈ Icc (D i).minus.a (D i).minus.b,
      |contactCurvature (D i).minus y| ≤ M)
    (hplus : ∀ᶠ i in l, ∀ y ∈ Icc (D i).plus.a (D i).plus.b,
      |contactCurvature (D i).plus y| ≤ M)
    (hcompensation : ∀ᶠ i in l,
      ∀ y ∈ Icc (D i).compensation.a (D i).compensation.b,
        |contactCurvature (D i).compensation y| ≤ M) :
    Tendsto
      (fun i => (D i).contactFirstVariation lam - transmissionDefect lam (D i))
      l (𝓝 0) := by
  let K := (2 * lam + lam * (lam + 1)) * M
  have hlam0 : 0 < lam := lt_trans zero_lt_one hlam
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hbound : ∀ᶠ i in l,
      |(D i).contactFirstVariation lam - transmissionDefect lam (D i)| ≤
        K * (D i).rho := by
    filter_upwards [hminus, hplus, hcompensation] with i hmi hpi hci
    exact (D i).abs_contactFirstVariation_sub_transmissionDefect_le
      hlam hM hmi hpi hci
  have hupper : Tendsto (fun i => K * (D i).rho) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hrho)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero'
      (Filter.Eventually.of_forall fun i =>
        abs_nonneg ((D i).contactFirstVariation lam -
          transmissionDefect lam (D i)))
      hbound hupper

/-- If the actual contact momenta themselves converge, the differentiated
complete graph functional converges to their signed transmission jump. -/
theorem tendsto_contactFirstVariation
    {α : Type*} {l : Filter α} {lam M defect : ℝ}
    (hlam : 1 < lam) (hM : 0 ≤ M) (D : α → ContactData)
    (hrho : Tendsto (fun i => (D i).rho) l (𝓝 0))
    (hminus : ∀ᶠ i in l, ∀ y ∈ Icc (D i).minus.a (D i).minus.b,
      |contactCurvature (D i).minus y| ≤ M)
    (hplus : ∀ᶠ i in l, ∀ y ∈ Icc (D i).plus.a (D i).plus.b,
      |contactCurvature (D i).plus y| ≤ M)
    (hcompensation : ∀ᶠ i in l,
      ∀ y ∈ Icc (D i).compensation.a (D i).compensation.b,
        |contactCurvature (D i).compensation y| ≤ M)
    (hdefect : Tendsto (fun i => transmissionDefect lam (D i))
      l (𝓝 defect)) :
    Tendsto (fun i => (D i).contactFirstVariation lam) l (𝓝 defect) := by
  have herr :=
    tendsto_contactFirstVariation_sub_transmissionDefect
      hlam hM D hrho hminus hplus hcompensation
  have hsum := herr.add hdefect
  convert hsum using 1
  · funext i
    ring
  · simp

/-- A nonzero limiting transmission defect makes the fixed-radius derivative
nonzero eventually along every shrinking-support family satisfying the
uniform curvature bounds. -/
theorem eventually_contactFirstVariation_ne_zero
    {α : Type*} {l : Filter α} {lam M defect : ℝ}
    (hlam : 1 < lam) (hM : 0 ≤ M) (D : α → ContactData)
    (hrho : Tendsto (fun i => (D i).rho) l (𝓝 0))
    (hminus : ∀ᶠ i in l, ∀ y ∈ Icc (D i).minus.a (D i).minus.b,
      |contactCurvature (D i).minus y| ≤ M)
    (hplus : ∀ᶠ i in l, ∀ y ∈ Icc (D i).plus.a (D i).plus.b,
      |contactCurvature (D i).plus y| ≤ M)
    (hcompensation : ∀ᶠ i in l,
      ∀ y ∈ Icc (D i).compensation.a (D i).compensation.b,
        |contactCurvature (D i).compensation y| ≤ M)
    (hdefect : Tendsto (fun i => transmissionDefect lam (D i))
      l (𝓝 defect))
    (hdefect_ne : defect ≠ 0) :
    ∀ᶠ i in l, (D i).contactFirstVariation lam ≠ 0 :=
  (tendsto_contactFirstVariation
    hlam hM D hrho hminus hplus hcompensation hdefect).eventually_ne hdefect_ne

/-- At one fixed support radius, all three changed traces are actual
density-weighted Euclidean H1 graph costs. -/
theorem weightedTraceCosts_eq_graphLengths
    {lam : ℝ} (hlam : 1 < lam) (D : ContactData)
    (minusTube : D.minus.Tube) (plusTube : D.plus.Tube)
    (compensationTube : D.compensation.Tube) {t : ℝ}
    (hminus : ∀ y ∈ Ioo D.minus.a D.minus.b,
      |t * D.minusVelocity y| ≤ minusTube.radius)
    (hplus : ∀ y ∈ Ioo D.plus.a D.plus.b,
      |t * D.plusVelocity y| ≤ plusTube.radius)
    (hcompensation : ∀ y ∈ Ioo D.compensation.a D.compensation.b,
      |t * D.compensationVelocity lam y| ≤ compensationTube.radius) :
    CMVRelaxation.weightedTraceCost lam
        (D.minus.closedGraphTrace D.minusVelocity t) =
          ENNReal.ofReal (D.minus.weightedGraphLength lam D.minusVelocity t) ∧
      CMVRelaxation.weightedTraceCost lam
        (D.plus.closedGraphTrace D.plusVelocity t) =
          ENNReal.ofReal (D.plus.weightedGraphLength lam D.plusVelocity t) ∧
      CMVRelaxation.weightedTraceCost lam
        (D.compensation.closedGraphTrace (D.compensationVelocity lam) t) =
          ENNReal.ofReal
            (D.compensation.weightedGraphLength
              lam (D.compensationVelocity lam) t) := by
  constructor
  · rw [D.minus.weightedTraceCost_closedGraphTrace_eq_open]
    exact D.minus.weightedTraceCost_openGraphTrace_eq
      hlam minusTube D.minusVelocity_contDiff hminus
  constructor
  · rw [D.plus.weightedTraceCost_closedGraphTrace_eq_open]
    exact D.plus.weightedTraceCost_openGraphTrace_eq
      hlam plusTube D.plusVelocity_contDiff hplus
  · rw [D.compensation.weightedTraceCost_closedGraphTrace_eq_open]
    exact D.compensation.weightedTraceCost_openGraphTrace_eq
      hlam compensationTube (D.compensationVelocity_contDiff lam) hcompensation

/-- The unique point shared by the two displaced incident traces has zero H1
cost; no density-interface segment is inserted into the graph functional. -/
theorem weightedTraceCost_commonContact_singleton
    (lam : ℝ) (D : ContactData) (t : ℝ) :
    CMVRelaxation.weightedTraceCost lam
      {(D.minus.variedGraph D.minusVelocity t D.interfaceY, D.interfaceY)} = 0 :=
  HorizontalGraphPatch.weightedTraceCost_singleton lam _

end ContactData

namespace ActualContactData

/-- A nonzero derivative of the fixed-radius, exact-area graph family gives
strict descent for one parameter sign. -/
theorem exists_exactArea_graphLength_descent_of_firstVariation_ne_zero
    {lam : ℝ} (hlam : 1 < lam) (A : ActualContactData)
    (hne : A.contact.contactFirstVariation lam ≠ 0) :
    ∃ ε > 0, ∃ t : ℝ, |t| < ε ∧ t ≠ 0 ∧
      WeightedArea lam (A.variedCarrier lam t) =
        WeightedArea lam A.actualCarrier ∧
      A.contact.totalWeightedGraphLength lam t <
        A.contact.totalWeightedGraphLength lam 0 := by
  have hderiv := A.contact.totalWeightedGraphLength_hasDerivAt lam
  have hnotmin :
      ¬ IsLocalMin (A.contact.totalWeightedGraphLength lam) 0 := by
    intro hmin
    exact hne (hmin.hasDerivAt_eq_zero hderiv)
  rcases A.transverse_contact_exact_area_checkpoint hlam with
    ⟨ε, hε, hlocal⟩
  have hexists :
      ∃ t : ℝ, |t| < ε ∧
        A.contact.totalWeightedGraphLength lam t <
          A.contact.totalWeightedGraphLength lam 0 := by
    by_contra hnone
    apply hnotmin
    change ∀ᶠ t in 𝓝 (0 : ℝ),
      A.contact.totalWeightedGraphLength lam 0 ≤
        A.contact.totalWeightedGraphLength lam t
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with t ht
    apply le_of_not_gt
    intro hdescend
    apply hnone
    exact ⟨t, by simpa [Real.dist_eq] using ht, hdescend⟩
  rcases hexists with ⟨t, ht, hdescend⟩
  rcases hlocal t ht with
    ⟨_hminus, _hplus, _hcompensation, harea, _hdiff, _houtside,
      _hmeet, _hminusOuter, _hplusOuter, _hcoefficient⟩
  refine ⟨ε, hε, t, ht, ?_, harea, hdescend⟩
  intro htzero
  subst t
  exact (lt_irrefl _ hdescend)


/-- Quantitative nonzero transmission defect plus sufficiently small support
gives exact-area strict graph-length descent for one parameter sign. -/
theorem exists_exactArea_graphLength_descent_of_transmissionDefect
    {lam : ℝ} (hlam : 1 < lam) (A : ActualContactData)
    {M : ℝ} (hM : 0 ≤ M)
    (hminus : ∀ y ∈ Icc A.contact.minus.a A.contact.minus.b,
      |contactCurvature A.contact.minus y| ≤ M)
    (hplus : ∀ y ∈ Icc A.contact.plus.a A.contact.plus.b,
      |contactCurvature A.contact.plus y| ≤ M)
    (hcompensation :
      ∀ y ∈ Icc A.contact.compensation.a A.contact.compensation.b,
        |contactCurvature A.contact.compensation y| ≤ M)
    (hsmall :
      ((2 * lam + lam * (lam + 1)) * M) * A.contact.rho <
        |transmissionDefect lam A.contact|) :
    ∃ ε > 0, ∃ t : ℝ, |t| < ε ∧ t ≠ 0 ∧
      WeightedArea lam (A.variedCarrier lam t) =
        WeightedArea lam A.actualCarrier ∧
      A.contact.totalWeightedGraphLength lam t <
        A.contact.totalWeightedGraphLength lam 0 :=
  A.exists_exactArea_graphLength_descent_of_firstVariation_ne_zero hlam
    (A.contact.contactFirstVariation_ne_zero_of_error_lt_abs_transmissionDefect
      hlam hM hminus hplus hcompensation hsmall)
end ActualContactData



namespace Examples

/-- On the affine mismatch specimen every fixed-radius remainder vanishes, so
the complete derivative is exactly its nonzero transmission defect. -/
theorem contactFirstVariation_eq_transmissionDefect :
    contact.contactFirstVariation 2 = transmissionDefect 2 contact := by
  rw [contact.contactFirstVariation_eq_transmissionDefect_sub_remainders]
  have hm :
      (∫ y in contact.minus.a..contact.minus.b,
        contactCurvature contact.minus y * contact.minusVelocity y) = 0 := by
    have hfun :
        (fun y => contactCurvature contact.minus y * contact.minusVelocity y) =
          0 := by
      funext y
      simp [contactCurvature, contact, minusPatch]
    rw [hfun]
    exact intervalIntegral.integral_zero
  have hp :
      (∫ y in contact.plus.a..contact.plus.b,
        contactCurvature contact.plus y * contact.plusVelocity y) = 0 := by
    have hfun :
        (fun y => contactCurvature contact.plus y * contact.plusVelocity y) =
          0 := by
      funext y
      simp [contactCurvature, contact, plusPatch]
    rw [hfun]
    exact intervalIntegral.integral_zero
  have hc : contact.compensationMomentumResponse = 0 := by
    unfold ContactData.compensationMomentumResponse
    have hfun :
        (fun y => contactMomentum contact.compensation y *
          deriv contact.compensation.compensationBump y) = 0 := by
      funext y
      simp [contactMomentum, contact, compensationPatch]
    rw [hfun]
    exact intervalIntegral.integral_zero
  rw [hm, hp, hc]
  ring

theorem contactFirstVariation_ne_zero :
    contact.contactFirstVariation 2 ≠ 0 := by
  rw [contactFirstVariation_eq_transmissionDefect]
  exact transmissionDefect_ne_zero

/-- The nonzero upper-interface, occupied-left defect gives an exact-area
strict graph-length descent for one parameter sign. -/
theorem exact_area_graphLength_descent :
    ∃ ε > 0, ∃ t : ℝ, |t| < ε ∧ t ≠ 0 ∧
      WeightedArea 2 (actual.variedCarrier 2 t) =
        WeightedArea 2 actual.actualCarrier ∧
      contact.totalWeightedGraphLength 2 t <
        contact.totalWeightedGraphLength 2 0 :=
  actual.exists_exactArea_graphLength_descent_of_firstVariation_ne_zero
    (by norm_num) contactFirstVariation_ne_zero

end Examples

/-! ## Lower-interface, occupied-right exercise -/

namespace LowerAboveExamples

/-- Exterior affine germ approaching the lower interface from below. -/
def minusPatch : HorizontalGraphPatch where
  a := -5 / 4
  b := -1
  base := 2
  graph := fun y => -y - 1
  lowerBound := -1 / 2
  upperBound := 2
  zone := .exterior
  side := .above
  a_lt_b := by norm_num
  graph_contDiff := by fun_prop
  base_order_graph := by
    intro y hy
    norm_num at hy ⊢
    linarith
  lowerBound_le_base := by norm_num
  base_le_upperBound := le_rfl
  graph_bounds := by
    intro y hy
    norm_num at hy ⊢
    constructor <;> linarith
  carrier_in_zone := by
    intro p hp
    simp only [mem_horizontalRegionBetween, mem_Ioo] at hp
    change 1 < |p.2|
    rw [abs_of_neg (by linarith [hp.1.2])]
    linarith [hp.1.2]

/-- Interior affine germ leaving the lower interface from above. -/
def plusPatch : HorizontalGraphPatch where
  a := -1
  b := -3 / 4
  base := 2
  graph := fun _ => 0
  lowerBound := -1 / 2
  upperBound := 2
  zone := .interior
  side := .above
  a_lt_b := by norm_num
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := by norm_num
  base_le_upperBound := le_rfl
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    intro p hp
    simp only [mem_horizontalRegionBetween, mem_Ioo] at hp
    change |p.2| ≤ 1
    rw [abs_of_nonpos (by linarith [hp.1.1])]
    linarith [hp.1.1]

/-- Remote density-one compensation patch on the opposite side. -/
def compensationPatch : HorizontalGraphPatch where
  a := 1 / 4
  b := 1 / 2
  base := -1
  graph := fun _ => -2
  lowerBound := -5 / 2
  upperBound := -1
  zone := .interior
  side := .above
  a_lt_b := by norm_num
  graph_contDiff := contDiff_const
  base_order_graph := by intros; norm_num
  lowerBound_le_base := by norm_num
  base_le_upperBound := le_rfl
  graph_bounds := by intros; norm_num
  carrier_in_zone := by
    intro p hp
    simp only [mem_horizontalRegionBetween, mem_Ioo] at hp
    change |p.2| ≤ 1
    rw [abs_of_nonneg (by linarith [hp.1.1])]
    linarith [hp.1.2]

/-- Literal lower-interface contact in the other occupied-side orientation. -/
def contact : ContactData where
  interfaceY := -1
  rho := 1 / 4
  rho_pos := by norm_num
  interface_eq := Or.inr rfl
  minus := minusPatch
  plus := plusPatch
  compensation := compensationPatch
  minus_a := by norm_num [minusPatch]
  minus_b := rfl
  plus_a := rfl
  plus_b := by norm_num [plusPatch]
  common_side := rfl
  different_zones := by decide
  graphs_meet := by norm_num [minusPatch, plusPatch]
  compensation_vertical_disjoint := by
    rw [Set.disjoint_left]
    intro y hyComp hyContact
    norm_num [compensationPatch] at hyComp hyContact
    linarith

def minusTube : minusPatch.Tube where
  radius := 1 / 8
  radius_pos := by norm_num
  order_clearance := by
    intro y hy
    norm_num [minusPatch] at hy ⊢
    linarith
  graph_lower_clearance := by
    intro y hy
    norm_num [minusPatch] at hy ⊢
    linarith
  graph_upper_clearance := by
    intro y hy
    norm_num [minusPatch] at hy ⊢
    linarith
  tube_in_zone := by
    intro y hy _x _hx
    change 1 < |y|
    norm_num [minusPatch] at hy
    rw [abs_of_neg (by linarith)]
    linarith

def plusTube : plusPatch.Tube where
  radius := 1 / 8
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [plusPatch]
  graph_lower_clearance := by intros; norm_num [plusPatch]
  graph_upper_clearance := by intros; norm_num [plusPatch]
  tube_in_zone := by
    intro y hy _x _hx
    change |y| ≤ 1
    norm_num [plusPatch] at hy
    rw [abs_of_nonpos (by linarith)]
    linarith [hy.1]

def compensationTube : compensationPatch.Tube where
  radius := 1 / 8
  radius_pos := by norm_num
  order_clearance := by intros; norm_num [compensationPatch]
  graph_lower_clearance := by intros; norm_num [compensationPatch]
  graph_upper_clearance := by intros; norm_num [compensationPatch]
  tube_in_zone := by
    intro y hy _x _hx
    change |y| ≤ 1
    norm_num [compensationPatch] at hy
    rw [abs_of_nonneg (by linarith)]
    linarith

def actual : ActualContactData where
  contact := contact
  minusTube := by simpa [contact] using minusTube
  plusTube := by simpa [contact] using plusTube
  compensationTube := by simpa [contact] using compensationTube
  actualCarrier := contact.baselineRibbons
  fixedCarrier := ∅
  actualCarrier_eq_fixed_union := by simp
  measurableSet_actualCarrier := by
    simpa [ContactData.baselineRibbons, contact] using
      (minusPatch.measurableSet_carrier.union
        plusPatch.measurableSet_carrier).union
          compensationPatch.measurableSet_carrier
  measurableSet_fixedCarrier := MeasurableSet.empty
  actualCarrier_bounded := by
    simpa [ContactData.baselineRibbons, contact] using
      (minusPatch.carrier_bounded.union plusPatch.carrier_bounded).union
        compensationPatch.carrier_bounded
  fixed_disjoint_baseline := Set.empty_disjoint _
  fixed_disjoint_supportTubes := Set.empty_disjoint _

/-- The lower-interface slopes violate the same increasing-y momentum law. -/
theorem transmissionDefect_ne_zero :
    transmissionDefect 2 contact ≠ 0 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  simp [transmissionDefect, contactMomentum, contact, minusPatch, plusPatch,
    DensityZone.weight]

theorem contactFirstVariation_eq_transmissionDefect :
    contact.contactFirstVariation 2 = transmissionDefect 2 contact := by
  rw [contact.contactFirstVariation_eq_transmissionDefect_sub_remainders]
  have hm :
      (∫ y in contact.minus.a..contact.minus.b,
        contactCurvature contact.minus y * contact.minusVelocity y) = 0 := by
    have hfun :
        (fun y => contactCurvature contact.minus y * contact.minusVelocity y) =
          0 := by
      funext y
      simp [contactCurvature, contact, minusPatch]
    rw [hfun]
    exact intervalIntegral.integral_zero
  have hp :
      (∫ y in contact.plus.a..contact.plus.b,
        contactCurvature contact.plus y * contact.plusVelocity y) = 0 := by
    have hfun :
        (fun y => contactCurvature contact.plus y * contact.plusVelocity y) =
          0 := by
      funext y
      simp [contactCurvature, contact, plusPatch]
    rw [hfun]
    exact intervalIntegral.integral_zero
  have hc : contact.compensationMomentumResponse = 0 := by
    unfold ContactData.compensationMomentumResponse
    have hfun :
        (fun y => contactMomentum contact.compensation y *
          deriv contact.compensation.compensationBump y) = 0 := by
      funext y
      simp [contactMomentum, contact, compensationPatch]
    rw [hfun]
    exact intervalIntegral.integral_zero
  rw [hm, hp, hc]
  ring

theorem contactFirstVariation_ne_zero :
    contact.contactFirstVariation 2 ≠ 0 := by
  rw [contactFirstVariation_eq_transmissionDefect]
  exact transmissionDefect_ne_zero

/-- The lower-interface, occupied-right defect likewise gives exact-area
strict graph-length descent for one parameter sign. -/
theorem exact_area_graphLength_descent :
    ∃ ε > 0, ∃ t : ℝ, |t| < ε ∧ t ≠ 0 ∧
      WeightedArea 2 (actual.variedCarrier 2 t) =
        WeightedArea 2 actual.actualCarrier ∧
      contact.totalWeightedGraphLength 2 t <
        contact.totalWeightedGraphLength 2 0 :=
  actual.exists_exactArea_graphLength_descent_of_firstVariation_ne_zero
    (by norm_num) contactFirstVariation_ne_zero

end LowerAboveExamples
end CMVTransverseContactVariation
