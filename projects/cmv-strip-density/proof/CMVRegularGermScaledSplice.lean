import CMVRegularGermSplice

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

namespace RegularEndpointTrace

/-- Positive linear reparameterization of an endpoint germ. -/
def positiveReparam {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) :
    RegularEndpointTrace junction where
  curve t := T.curve (a * t)
  velocity := (a * T.velocity.1, a * T.velocity.2)
  curve_zero := by simp [T.curve_zero]
  complex_contDiff :=
    T.complex_contDiff.comp (contDiff_const.mul contDiff_id)
  hasDerivAt_zero := by
    have hdiff : DifferentiableAt ℝ
        (fun t => complexVector (T.curve (a * t))) 0 :=
      (T.complex_contDiff.comp
        (contDiff_const.mul contDiff_id)).differentiable (by norm_num) |>
          Differentiable.differentiableAt
    have hvel :
        complexVector (a * T.velocity.1, a * T.velocity.2) =
          a • complexVector T.velocity := by
      apply Complex.ext <;> simp [complexVector]
    convert hdiff.hasDerivAt using 1
    · apply AddCommGroup.ext
      rfl
    · rw [deriv_comp_mul_left a
          (fun t => complexVector (T.curve t)) 0]
      simp only [mul_zero]
      rw [T.deriv_complexCurve_zero]
      exact hvel
  velocity_ne := by
    intro h
    apply T.velocity_ne
    apply Prod.ext
    · have hx := congrArg Prod.fst h
      dsimp at hx
      exact (mul_eq_zero.mp hx).resolve_left ha.ne'
    · have hy := congrArg Prod.snd h
      dsimp at hy
      exact (mul_eq_zero.mp hy).resolve_left ha.ne'

@[simp] theorem positiveReparam_curve {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (T.positiveReparam a ha).curve t = T.curve (a * t) := rfl

@[simp] theorem positiveReparam_velocity {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) :
    (T.positiveReparam a ha).velocity = a • T.velocity := rfl

theorem positiveReparam_euclideanSpeed {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) :
    euclideanSpeed (T.positiveReparam a ha).velocity =
      a * euclideanSpeed T.velocity := by
  rw [euclideanSpeed, euclideanSpeed]
  have hvec :
      complexVector (T.positiveReparam a ha).velocity =
        a • complexVector T.velocity := by
    apply Complex.ext <;> simp [positiveReparam, complexVector]
  rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
/-- Positive linear reparameterization scales the complete pointwise speed. -/
theorem positiveReparam_speed {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (T.positiveReparam a ha).speed t = a * T.speed (a * t) := by
  unfold speed
  change ‖deriv (fun u => complexVector (T.curve (a * u))) t‖ =
    a * ‖deriv (fun u => complexVector (T.curve u)) (a * t)‖
  rw [deriv_comp_mul_left a (fun u => complexVector (T.curve u)) t,
    norm_smul, Real.norm_eq_abs, abs_of_pos ha]

/-- Hence reparameterized arclength at scale `r` is the original arclength at
the independently scaled endpoint parameter `a*r`. -/
theorem positiveReparam_arcLength {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    (T.positiveReparam a ha).arcLength r = T.arcLength (a * r) := by
  unfold arcLength
  simp_rw [T.positiveReparam_speed a ha]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.mul_integral_comp_mul_left]
  simp


def unitScale {junction : PlanePoint} (T : RegularEndpointTrace junction) : ℝ :=
  (euclideanSpeed T.velocity)⁻¹

theorem unitScale_pos {junction : PlanePoint}
    (T : RegularEndpointTrace junction) : 0 < T.unitScale :=
  inv_pos.mpr (euclideanSpeed_pos T.velocity_ne)

theorem unitScale_reparam_euclideanSpeed {junction : PlanePoint}
    (T : RegularEndpointTrace junction) :
    euclideanSpeed (T.positiveReparam T.unitScale T.unitScale_pos).velocity = 1 := by
  rw [T.positiveReparam_euclideanSpeed T.unitScale T.unitScale_pos]
  exact inv_mul_cancel₀ (ne_of_gt (euclideanSpeed_pos T.velocity_ne))

theorem positiveReparam_unitTangent {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (a : ℝ) (ha : 0 < a) :
    unitTangent (T.positiveReparam a ha).velocity =
      unitTangent T.velocity := by
  rw [unitTangent, unitTangent, T.positiveReparam_euclideanSpeed a ha,
    T.positiveReparam_velocity a ha]
  ext <;> exact mul_div_mul_left _ _ ha.ne'

/-- Positive endpoint rescaling preserves the oriented endpoint conormal.
Negative scales are deliberately excluded because they reverse orientation. -/
theorem positiveReparam_endpointConormal {junction : PlanePoint}
    (T : RegularEndpointTrace junction) (orientation : EndpointOrientation)
    (a : ℝ) (ha : 0 < a) :
    endpointConormal orientation (T.positiveReparam a ha).velocity =
      endpointConormal orientation T.velocity := by
  cases orientation <;> simp only [endpointConormal] <;>
    rw [T.positiveReparam_unitTangent a ha]

end RegularEndpointTrace

/-- Squared Euclidean speed is the source-coordinate self inner product. -/
lemma euclideanSpeed_sq_eq_planeInner_self (v : PlanePoint) :
    euclideanSpeed v ^ 2 = planeInner v v := by
  rw [euclideanSpeed, Complex.sq_norm, Complex.normSq_apply]
  simp [complexVector, planeInner]

/-- Squared separation of two independently scaled source vectors. -/
lemma complexVector_scaled_sub_norm_sq (v z : PlanePoint) (a b : ℝ) :
    ‖complexVector (a • v) - complexVector (b • z)‖ ^ 2 =
      a ^ 2 * planeInner v v + b ^ 2 * planeInner z z -
        2 * a * b * planeInner v z := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [complexVector, planeInner]
  ring

/-- Initial endpoint conormals preserve the inner product of the corresponding
unit tangents: both orientations contribute the same minus sign. -/
lemma planeInner_initialConormal_eq_unitTangent
    (v z : PlanePoint) :
    planeInner (endpointConormal .initial v)
        (endpointConormal .initial z) =
      planeInner (unitTangent v) (unitTangent z) := by
  simp [endpointConormal, planeInner]

/-- Clearing the two positive speed denominators recovers the unnormalized
source-vector inner product. -/
lemma euclideanSpeeds_mul_planeInner_unitTangents
    {v z : PlanePoint} (hv : v ≠ (0, 0)) (hz : z ≠ (0, 0)) :
    euclideanSpeed v * euclideanSpeed z *
        planeInner (unitTangent v) (unitTangent z) =
      planeInner v z := by
  have hsv : euclideanSpeed v ≠ 0 := ne_of_gt (euclideanSpeed_pos hv)
  have hsz : euclideanSpeed z ≠ 0 := ne_of_gt (euclideanSpeed_pos hz)
  simp only [planeInner, unitTangent]
  field_simp [hsv, hsz]

/-- Exact conormal formula for the first-order squared endpoint separation
under independent positive parameter scales.  This is valid at horizontal and
vertical tangencies and fixes the orientation used by the later unilateral
comparison. -/
theorem positiveReparam_velocityDifference_norm_sq
    {junction : PlanePoint} (I F : RegularEndpointTrace junction)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖complexVector (I.positiveReparam a ha).velocity -
        complexVector (F.positiveReparam b hb).velocity‖ ^ 2 =
      (a * euclideanSpeed I.velocity) ^ 2 +
        (b * euclideanSpeed F.velocity) ^ 2 -
          2 * (a * euclideanSpeed I.velocity) *
            (b * euclideanSpeed F.velocity) *
              planeInner (endpointConormal .initial I.velocity)
                (endpointConormal .initial F.velocity) := by
  rw [I.positiveReparam_velocity a ha, F.positiveReparam_velocity b hb,
    complexVector_scaled_sub_norm_sq,
    ← euclideanSpeed_sq_eq_planeInner_self I.velocity,
    ← euclideanSpeed_sq_eq_planeInner_self F.velocity,
    planeInner_initialConormal_eq_unitTangent]
  have hdot :=
    euclideanSpeeds_mul_planeInner_unitTangents
      I.velocity_ne F.velocity_ne
  rw [← hdot]
  ring

/-- Every strict gain produced by an independently scaled trimming splice lies
on the `-1 / w`-greater side of the two initial-conormal inner product.  This
is only the direction detected by this literal splice; it does not assert a
contact law or local minimality. -/
theorem conormal_gt_neg_inv_of_positiveReparam_tangentGain_pos
    {junction : PlanePoint} (I F : RegularEndpointTrace junction)
    (w a b : ℝ) (hw : 1 ≤ w) (ha : 0 < a) (hb : 0 < b)
    (hgain :
      0 < tangentGainCoefficient
        (I.positiveReparam a ha) (F.positiveReparam b hb) w 1 w) :
    -1 / w <
      planeInner (endpointConormal .initial I.velocity)
        (endpointConormal .initial F.velocity) := by
  let x := a * euclideanSpeed I.velocity
  let y := b * euclideanSpeed F.velocity
  let d :=
    ‖complexVector (I.positiveReparam a ha).velocity -
      complexVector (F.positiveReparam b hb).velocity‖
  let c :=
    planeInner (endpointConormal .initial I.velocity)
      (endpointConormal .initial F.velocity)
  have hwpos : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hx : 0 < x :=
    mul_pos ha (euclideanSpeed_pos I.velocity_ne)
  have hy : 0 < y :=
    mul_pos hb (euclideanSpeed_pos F.velocity_ne)
  have hd : 0 ≤ d := norm_nonneg _
  have hgain' : 0 < w * x + y - w * d := by
    unfold tangentGainCoefficient at hgain
    rw [I.positiveReparam_euclideanSpeed a ha,
      F.positiveReparam_euclideanSpeed b hb] at hgain
    simpa [x, y, d] using hgain
  have hsq :
      d ^ 2 = x ^ 2 + y ^ 2 - 2 * x * y * c := by
    simpa [x, y, d, c] using
      positiveReparam_velocityDifference_norm_sq I F a b ha hb
  by_contra hnot
  have hc : c ≤ -1 / w := le_of_not_gt hnot
  have hinv : w * (-1 / w) = -1 := by
    field_simp [hwpos.ne']
  have hcLinear : 1 + w * c ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hc hwpos.le
    rw [hinv] at hmul
    linarith
  have hwSq : 0 ≤ w ^ 2 - 1 := by nlinarith
  have htermOne : 0 ≤ (w ^ 2 - 1) * y ^ 2 :=
    mul_nonneg hwSq (sq_nonneg y)
  have htermTwo : 0 ≤
      (2 * w * x * y) * (-(1 + w * c)) :=
    mul_nonneg (by positivity) (neg_nonneg.mpr hcLinear)
  have hsquares : (w * x + y) ^ 2 ≤ (w * d) ^ 2 := by
    nlinarith
  have hlinear : w * x + y ≤ w * d := by
    have hleft : 0 ≤ w * x + y := by positivity
    have hright : 0 ≤ w * d := mul_nonneg hwpos.le hd
    nlinarith [sq_nonneg ((w * d) + (w * x + y))]
  linarith

/-- Consequently, every independently scaled trimming splice has nonpositive
tangent gain on the `-1 / w`-less side.  This makes the one-sided orientation
of the constructed comparison explicit. -/
theorem positiveReparam_tangentGain_nonpos_of_conormal_le
    {junction : PlanePoint} (I F : RegularEndpointTrace junction)
    (w a b : ℝ) (hw : 1 ≤ w) (ha : 0 < a) (hb : 0 < b)
    (hc :
      planeInner (endpointConormal .initial I.velocity)
          (endpointConormal .initial F.velocity) ≤
        -1 / w) :
    tangentGainCoefficient
      (I.positiveReparam a ha) (F.positiveReparam b hb) w 1 w ≤ 0 := by
  apply not_lt.mp
  intro hgain
  exact (not_lt_of_ge hc)
    (conormal_gt_neg_inv_of_positiveReparam_tangentGain_pos
      I F w a b hw ha hb hgain)

/-- Positive diagonal change of source coordinates. -/
def positiveDiagonalHomeomorph (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    PlanePoint ≃ₜ PlanePoint :=
  (Homeomorph.smulOfNeZero a ha.ne').prodCongr
    (Homeomorph.smulOfNeZero b hb.ne')

@[simp] theorem positiveDiagonalHomeomorph_apply
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (q : PlanePoint) :
    positiveDiagonalHomeomorph a b ha hb q = (a * q.1, b * q.2) := by
  rfl

private lemma scaled_parameter_le {R a b t : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Icc 0 (R / (a + b))) :
    a * t ∈ Icc 0 R := by
  have hab : 0 < a + b := add_pos ha hb
  constructor
  · exact mul_nonneg ha.le ht.1
  · calc
      a * t ≤ a * (R / (a + b)) := mul_le_mul_of_nonneg_left ht.2 ha.le
      _ ≤ (a + b) * (R / (a + b)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb.le)
          (div_nonneg hR.le hab.le)
      _ = R := by field_simp [hab.ne']

private lemma scaled_parameter_le_right {R a b t : ℝ}
    (hR : 0 < R) (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Icc 0 (R / (a + b))) :
    b * t ∈ Icc 0 R := by
  have hab : 0 < a + b := add_pos ha hb
  constructor
  · exact mul_nonneg hb.le ht.1
  · calc
      b * t ≤ b * (R / (a + b)) := mul_le_mul_of_nonneg_left ht.2 hb.le
      _ ≤ (a + b) * (R / (a + b)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha.le)
          (div_nonneg hR.le hab.le)
      _ = R := by field_simp [hab.ne']

/-- Reparameterize the two germs independently while keeping the carrier. -/
def ActualRegularTraceCorner.positiveDiagonalReparam
    {side : StripInterface} (C : ActualRegularTraceCorner side)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ActualRegularTraceCorner side where
  representative := C.representative
  representative_isOpen := C.representative_isOpen
  representative_isBounded := C.representative_isBounded
  junction := C.junction
  junction_on_interface := C.junction_on_interface
  radius := C.radius / (a + b)
  radius_pos := div_pos C.radius_pos (add_pos ha hb)
  incident := C.incident.positiveReparam a ha
  interface := C.interface.positiveReparam b hb
  incident_on_frontier := by
    rintro p ⟨t, ht, rfl⟩
    exact C.incident_on_frontier
      ⟨a * t, scaled_parameter_le C.radius_pos ha hb ht, rfl⟩
  interface_on_frontier := by
    rintro p ⟨t, ht, rfl⟩
    exact C.interface_on_frontier
      ⟨b * t, scaled_parameter_le_right C.radius_pos ha hb ht, rfl⟩
  interface_on_strip := by
    intro t ht
    exact C.interface_on_strip (b * t)
      (scaled_parameter_le_right C.radius_pos ha hb ht)
  traces_meet_only_at_junction := by
    apply Subset.antisymm
    · rintro p ⟨⟨t, ht, htp⟩, ⟨u, hu, hup⟩⟩
      have hpOld : p ∈
          (C.incident.curve '' Icc 0 C.radius) ∩
            (C.interface.curve '' Icc 0 C.radius) := by
        constructor
        · exact ⟨a * t, scaled_parameter_le C.radius_pos ha hb ht, htp⟩
        · exact ⟨b * u, scaled_parameter_le_right C.radius_pos ha hb hu, hup⟩
      rw [C.traces_meet_only_at_junction] at hpOld
      exact hpOld
    · intro p hp
      have hpj : p = C.junction := by simpa using hp
      subst p
      constructor
      · exact ⟨0, ⟨le_rfl, (div_pos C.radius_pos (add_pos ha hb)).le⟩,
          by simp [RegularEndpointTrace.positiveReparam, C.incident.curve_zero]⟩
      · exact ⟨0, ⟨le_rfl, (div_pos C.radius_pos (add_pos ha hb)).le⟩,
          by simp [RegularEndpointTrace.positiveReparam, C.interface.curve_zero]⟩

namespace RegularCornerChartApplicability

/-- Transport a corner chart through a positive diagonal source change. -/
def positiveDiagonalReparam {side : StripInterface}
    {C : ActualRegularTraceCorner side}
    (A : RegularCornerChartApplicability C)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    RegularCornerChartApplicability (C.positiveDiagonalReparam a b ha hb) where
  chart := (positiveDiagonalHomeomorph a b ha hb).trans A.chart
  localRadius := A.localRadius / (a + b)
  localRadius_pos := div_pos A.localRadius_pos (add_pos ha hb)
  chart_zero := by
    change A.chart (a * 0, b * 0) = C.junction
    simpa using A.chart_zero
  incident_axis := by
    intro t ht
    simpa [positiveDiagonalHomeomorph,
      ActualRegularTraceCorner.positiveDiagonalReparam,
      RegularEndpointTrace.positiveReparam] using
        A.incident_axis (a * t)
          (scaled_parameter_le A.localRadius_pos ha hb ht)
  interface_axis := by
    intro t ht
    simpa [positiveDiagonalHomeomorph,
      ActualRegularTraceCorner.positiveDiagonalReparam,
      RegularEndpointTrace.positiveReparam] using
        A.interface_axis (b * t)
          (scaled_parameter_le_right A.localRadius_pos ha hb ht)
  representative_local := by
    intro q hq
    have hab : 0 < a + b := add_pos ha hb
    have hscaled :
        (a * q.1, b * q.2) ∈ openLocalizationSquare (0, 0) A.localRadius := by
      simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
        at hq ⊢
      rcases hq with ⟨hx, hy⟩
      have hLa : a * (A.localRadius / (a + b)) < A.localRadius := by
        calc
          a * (A.localRadius / (a + b)) <
              (a + b) * (A.localRadius / (a + b)) :=
            mul_lt_mul_of_pos_right (lt_add_of_pos_right a hb)
              (div_pos A.localRadius_pos hab)
          _ = A.localRadius := by field_simp [hab.ne']
      have hLb : b * (A.localRadius / (a + b)) < A.localRadius := by
        calc
          b * (A.localRadius / (a + b)) <
              (a + b) * (A.localRadius / (a + b)) :=
            mul_lt_mul_of_pos_right (lt_add_of_pos_left b ha)
              (div_pos A.localRadius_pos hab)
          _ = A.localRadius := by field_simp [hab.ne']
      constructor
      · constructor <;> nlinarith [mul_lt_mul_of_pos_left hx.1 ha,
          mul_lt_mul_of_pos_left hx.2 ha]
      · constructor <;> nlinarith [mul_lt_mul_of_pos_left hy.1 hb,
          mul_lt_mul_of_pos_left hy.2 hb]
    change (A.chart (a * q.1, b * q.2) ∈ C.representative ↔ q ∈ openCorner)
    rw [A.representative_local _ hscaled]
    simp only [openCorner, mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨pos_of_mul_pos_right hx ha.le, pos_of_mul_pos_right hy hb.le⟩
    · rintro ⟨hx, hy⟩
      exact ⟨mul_pos ha hx, mul_pos hb hy⟩
  coordinateBound := A.coordinateBound * (a + b)
  coordinateBound_pos := mul_pos A.coordinateBound_pos (add_pos ha hb)
  chart_coordinate_bound := by
    intro q hq
    have hab : 0 < a + b := add_pos ha hb
    have hscaled :
        (a * q.1, b * q.2) ∈ localizationSquare (0, 0) A.localRadius := by
      simp only [localizationSquare, mem_prod, mem_Icc, zero_sub, zero_add]
        at hq ⊢
      rcases hq with ⟨hx, hy⟩
      have hLa : a * (A.localRadius / (a + b)) ≤ A.localRadius := by
        calc
          a * (A.localRadius / (a + b)) ≤
              (a + b) * (A.localRadius / (a + b)) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hb.le)
              (div_nonneg A.localRadius_pos.le hab.le)
          _ = A.localRadius := by field_simp [hab.ne']
      have hLb : b * (A.localRadius / (a + b)) ≤ A.localRadius := by
        calc
          b * (A.localRadius / (a + b)) ≤
              (a + b) * (A.localRadius / (a + b)) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha.le)
              (div_nonneg A.localRadius_pos.le hab.le)
          _ = A.localRadius := by field_simp [hab.ne']
      constructor
      · constructor <;> nlinarith [mul_le_mul_of_nonneg_left hx.1 ha.le,
          mul_le_mul_of_nonneg_left hx.2 ha.le]
      · constructor <;> nlinarith [mul_le_mul_of_nonneg_left hy.1 hb.le,
          mul_le_mul_of_nonneg_left hy.2 hb.le]
    have hbound := A.chart_coordinate_bound (a * q.1, b * q.2) hscaled
    have hxy :
        A.coordinateBound * (|a * q.1| + |b * q.2|) ≤
          (A.coordinateBound * (a + b)) * (|q.1| + |q.2|) := by
      rw [abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb]
      nlinarith [A.coordinateBound_pos.le, abs_nonneg q.1, abs_nonneg q.2,
        mul_nonneg ha.le (abs_nonneg q.2), mul_nonneg hb.le (abs_nonneg q.1)]
    exact ⟨hbound.1.trans hxy, hbound.2.trans hxy⟩

/-- The equal-coordinate connector endpoint is the original incident point at
`a*r`. -/
theorem positiveDiagonalReparam_incident_endpoint
    {side : StripInterface} {C : ActualRegularTraceCorner side}
    (A : RegularCornerChartApplicability C)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {r : ℝ} (hr : 0 ≤ r)
    (hrlocal : r ≤ (A.positiveDiagonalReparam a b ha hb).localRadius) :
    C.incident.curve (a * r) ∈
      (A.positiveDiagonalReparam a b ha hb).connectorTrace r := by
  let B := A.positiveDiagonalReparam a b ha hb
  refine ⟨(r, 0), ⟨hr, le_rfl, by simp⟩, ?_⟩
  simpa [B, ActualRegularTraceCorner.positiveDiagonalReparam,
    RegularEndpointTrace.positiveReparam] using
      B.incident_axis r ⟨hr, hrlocal⟩

/-- The other equal-coordinate connector endpoint is the original interface
point at `b*r`. -/
theorem positiveDiagonalReparam_interface_endpoint
    {side : StripInterface} {C : ActualRegularTraceCorner side}
    (A : RegularCornerChartApplicability C)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    {r : ℝ} (hr : 0 ≤ r)
    (hrlocal : r ≤ (A.positiveDiagonalReparam a b ha hb).localRadius) :
    C.interface.curve (b * r) ∈
      (A.positiveDiagonalReparam a b ha hb).connectorTrace r := by
  let B := A.positiveDiagonalReparam a b ha hb
  refine ⟨(0, r), ⟨le_rfl, hr, by simp⟩, ?_⟩
  simpa [B, ActualRegularTraceCorner.positiveDiagonalReparam,
    RegularEndpointTrace.positiveReparam] using
      B.interface_axis r ⟨hr, hrlocal⟩

/-- Source-side physical phase information is preserved by positive diagonal
reparameterization; no competitor or cost formula is added. -/
def PhysicalPhaseApplicability.positiveDiagonalReparam
    {side : StripInterface} {C : ActualRegularTraceCorner side}
    {A : RegularCornerChartApplicability C}
    (P : PhysicalPhaseApplicability A)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    PhysicalPhaseApplicability (A.positiveDiagonalReparam a b ha hb) where
  phase := P.phase
  chart_sector_phase := by
    intro q hq hqFirst hqSecond
    change q ∈
      openLocalizationSquare (0, 0) (A.localRadius / (a + b)) at hq
    have hab : 0 < a + b := add_pos ha hb
    have hscaled :
        (a * q.1, b * q.2) ∈
          openLocalizationSquare (0, 0) A.localRadius := by
      simp only [openLocalizationSquare, mem_prod, mem_Ioo, zero_sub, zero_add]
        at hq ⊢
      rcases hq with ⟨hx, hy⟩
      have hLa :
          a * (A.localRadius / (a + b)) < A.localRadius := by
        calc
          a * (A.localRadius / (a + b)) <
              (a + b) * (A.localRadius / (a + b)) :=
            mul_lt_mul_of_pos_right (lt_add_of_pos_right a hb)
              (div_pos A.localRadius_pos hab)
          _ = A.localRadius := by field_simp [hab.ne']
      have hLb :
          b * (A.localRadius / (a + b)) < A.localRadius := by
        calc
          b * (A.localRadius / (a + b)) <
              (a + b) * (A.localRadius / (a + b)) :=
            mul_lt_mul_of_pos_right (lt_add_of_pos_left b ha)
              (div_pos A.localRadius_pos hab)
          _ = A.localRadius := by field_simp [hab.ne']
      constructor
      · constructor <;> nlinarith [mul_lt_mul_of_pos_left hx.1 ha,
          mul_lt_mul_of_pos_left hx.2 ha]
      · constructor <;> nlinarith [mul_lt_mul_of_pos_left hy.1 hb,
          mul_lt_mul_of_pos_left hy.2 hb]
    change P.phase.Contains (A.chart (a * q.1, b * q.2))
    exact P.chart_sector_phase (a * q.1, b * q.2) hscaled
      (mul_pos ha hqFirst) (mul_nonneg hb.le hqSecond)

end RegularCornerChartApplicability
end CMVRelaxation.RegularTraceCornerComparison
