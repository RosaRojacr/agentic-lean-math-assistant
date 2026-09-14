import CMVRegularGermMetricSplice

/-!
# Interface-extending regular corner comparison

The trimming splice in `CMVRegularGermMetricSplice` removes positive lengths
from both incident germs.  This module records the distinct first-order move
needed on the opposite side of the CMV Proposition 2.14 inequality: keep the
old positive interface ray, continue it through the contact, remove only an
initial incident length, and join the two new endpoints.

Nothing here assumes a contact law, first variation, comparison cost, or source
minimality.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

/-- First-order gain for an interface-extending replacement.  The old incident
piece has price `w`, the newly exposed interface has price one, and the joining
trace lies in the incident phase and again has price `w`. -/
def extensionTangentGain (w x y c : ℝ) : ℝ :=
  w * x - y - w * Real.sqrt (x ^ 2 + y ^ 2 + 2 * x * y * c)

/-- The positive endpoint-length ratio selected from a strict violation
`c < -1/w`.  It is half the positive interval allowed by the squared gain. -/
def extensionEndpointRatio (w c : ℝ) : ℝ :=
  -w * (1 + w * c) / (w ^ 2 - 1)

lemma extensionEndpointRatio_pos {w c : ℝ} (hw : 1 < w)
    (hc : c < -1 / w) :
    0 < extensionEndpointRatio w c := by
  have hwpos : 0 < w := lt_trans zero_lt_one hw
  have hden : 0 < w ^ 2 - 1 := by nlinarith
  have hnum : 0 < -(1 + w * c) := by
    have hcw : c * w < -1 := by
      apply (lt_div_iff₀ hwpos).mp
      simpa only [neg_div] using hc
    nlinarith
  rw [extensionEndpointRatio]
  have hrewrite : -w * (1 + w * c) = w * -(1 + w * c) := by ring
  rw [hrewrite]
  exact div_pos (mul_pos hwpos hnum) hden

lemma extensionEndpointRatio_lt_weight {w c : ℝ} (hw : 1 < w)
    (hcLower : -1 ≤ c) :
    extensionEndpointRatio w c < w := by
  have hwpos : 0 < w := lt_trans zero_lt_one hw
  have hwm1 : 0 < w - 1 := sub_pos.mpr hw
  have hwp1 : 0 < w + 1 := by linarith
  have hden : 0 < w ^ 2 - 1 := by nlinarith
  have hA : -(1 + w * c) ≤ w - 1 := by
    have := mul_le_mul_of_nonneg_left hcLower hwpos.le
    nlinarith
  have hmul : w * (-(1 + w * c)) ≤ w * (w - 1) :=
    mul_le_mul_of_nonneg_left hA hwpos.le
  have hratio :
      extensionEndpointRatio w c ≤ w / (w + 1) := by
    rw [extensionEndpointRatio]
    have hfactor : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rw [hfactor]
    apply (div_le_iff₀ (mul_pos hwm1 hwp1)).2
    have hright :
        w / (w + 1) * ((w - 1) * (w + 1)) = w * (w - 1) := by
      field_simp [hwp1.ne']
    rw [hright]
    nlinarith [hmul]
  have hfrac : w / (w + 1) < w := by
    apply (div_lt_iff₀ hwp1).2
    nlinarith
  exact hratio.trans_lt hfrac

/-- Exact quadratic margin left after the chosen endpoint ratio. -/
lemma extensionEndpointRatio_square_margin {w c : ℝ} (hw : 1 < w)
    (hc : c < -1 / w) :
    0 < (w - extensionEndpointRatio w c) ^ 2 -
      w ^ 2 * (1 + extensionEndpointRatio w c ^ 2 +
        2 * extensionEndpointRatio w c * c) := by
  let t := extensionEndpointRatio w c
  have hwpos : 0 < w := lt_trans zero_lt_one hw
  have ht : 0 < t := extensionEndpointRatio_pos hw hc
  have hlinear : (w ^ 2 - 1) * t = -w * (1 + w * c) := by
    dsimp [t, extensionEndpointRatio]
    field_simp [show w ^ 2 - 1 ≠ 0 by nlinarith]
  have hneg : 0 < -w * (1 + w * c) := by
    have hcw : c * w < -1 := by
      apply (lt_div_iff₀ hwpos).mp
      simpa only [neg_div] using hc
    nlinarith
  dsimp [t] at ht hlinear ⊢
  nlinarith

/-- A strict lower-bound violation admits a positive interface-extension ratio
with positive first-order weighted gain.  The lower bound `-1 ≤ c` is the
unit-conormal constraint; it is derived from actual conormals below. -/
theorem extensionTangentGain_pos_at_endpointRatio {w c : ℝ} (hw : 1 < w)
    (hcLower : -1 ≤ c) (hc : c < -1 / w) :
    0 < extensionTangentGain w 1 (extensionEndpointRatio w c) c := by
  let t := extensionEndpointRatio w c
  let Q := 1 + t ^ 2 + 2 * t * c
  have hwpos : 0 < w := lt_trans zero_lt_one hw
  have ht : 0 < t := extensionEndpointRatio_pos hw hc
  have htw : t < w := extensionEndpointRatio_lt_weight hw hcLower
  have hQ : 0 ≤ Q := by
    have hcTerm := mul_le_mul_of_nonneg_left hcLower (by positivity : 0 ≤ 2 * t)
    dsimp [Q]
    nlinarith [sq_nonneg (1 - t)]
  have hsqrt : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ
  have hmargin := extensionEndpointRatio_square_margin hw hc
  have hsq : (w * Real.sqrt Q) ^ 2 < (w - t) ^ 2 := by
    dsimp [Q] at hsqrt ⊢
    rw [mul_pow, hsqrt]
    simpa [t] using hmargin
  have hleft : 0 < w - t := sub_pos.mpr htw
  have hright : 0 ≤ w * Real.sqrt Q :=
    mul_nonneg hwpos.le (Real.sqrt_nonneg Q)
  have hroot : w * Real.sqrt Q < w - t := by nlinarith
  simpa [extensionTangentGain, t, Q] using (sub_pos.mpr hroot)

/-- A pair of unit vectors has scalar product at least `-1`. -/
lemma planeInner_ge_neg_one_of_unit {u v : PlanePoint}
    (hu : planeInner u u = 1) (hv : planeInner v v = 1) :
    -1 ≤ planeInner u v := by
  have hsq : 0 ≤ (u.1 + v.1) ^ 2 + (u.2 + v.2) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [planeInner] at hu hv ⊢
  nlinarith

/-- The lower scalar-product bound needed by the sign calculation is automatic
for the two actual outward endpoint conormals. -/
theorem ActualRegularTraceCorner.conormal_inner_ge_neg_one
    {side : StripInterface} (C : ActualRegularTraceCorner side) :
    -1 ≤ planeInner C.incidentConormal C.interfaceConormal :=
  planeInner_ge_neg_one_of_unit C.incidentConormal_unit
    C.interfaceConormal_unit

/-- A strict exterior contact violation produces a concrete positive endpoint
ratio for the interface-extending move. -/
theorem ActualRegularTraceCorner.extensionTangentGain_pos_of_conormal_lt
    {side : StripInterface} (C : ActualRegularTraceCorner side)
    {w : ℝ} (hw : 1 < w)
    (hc : planeInner C.incidentConormal C.interfaceConormal < -1 / w) :
    0 < extensionTangentGain w 1
      (extensionEndpointRatio w
        (planeInner C.incidentConormal C.interfaceConormal))
      (planeInner C.incidentConormal C.interfaceConormal) :=
  extensionTangentGain_pos_at_endpointRatio hw
    C.conormal_inner_ge_neg_one hc

/-- Squared first-order joining length when the interface endpoint moves along
the continuation opposite its existing ray.  The plus sign is forced by that
continuation and is distinct from the trimming splice's velocity difference. -/
theorem positiveReparam_velocitySum_norm_sq
    {junction : PlanePoint} (I F : RegularEndpointTrace junction)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ‖complexVector (I.positiveReparam a ha).velocity +
        complexVector (F.positiveReparam b hb).velocity‖ ^ 2 =
      (a * euclideanSpeed I.velocity) ^ 2 +
        (b * euclideanSpeed F.velocity) ^ 2 +
          2 * (a * euclideanSpeed I.velocity) *
            (b * euclideanSpeed F.velocity) *
              planeInner (endpointConormal .initial I.velocity)
                (endpointConormal .initial F.velocity) := by
  rw [I.positiveReparam_velocity a ha, F.positiveReparam_velocity b hb,
    Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, complexVector_re, complexVector_im,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hsum :
      (a * I.velocity.1 + b * F.velocity.1) *
            (a * I.velocity.1 + b * F.velocity.1) +
          (a * I.velocity.2 + b * F.velocity.2) *
            (a * I.velocity.2 + b * F.velocity.2) =
        a ^ 2 * planeInner I.velocity I.velocity +
          b ^ 2 * planeInner F.velocity F.velocity +
            2 * a * b * planeInner I.velocity F.velocity := by
    simp only [planeInner]
    ring
  rw [hsum, ← euclideanSpeed_sq_eq_planeInner_self I.velocity,
    ← euclideanSpeed_sq_eq_planeInner_self F.velocity,
    planeInner_initialConormal_eq_unitTangent]
  have hdot := euclideanSpeeds_mul_planeInner_unitTangents
    I.velocity_ne F.velocity_ne
  rw [← hdot]
  ring

/-- Outward-conormal dictionary for the added interface continuation.  Reversing
the interface velocity reverses its initial endpoint conormal; no conormal
orientation is silently changed on the retained positive interface germ. -/
lemma endpointConormal_initial_neg (v : PlanePoint) :
    endpointConormal .initial (-v.1, -v.2) =
      (- (endpointConormal .initial v).1,
        - (endpointConormal .initial v).2) := by
  by_cases hv : v = (0, 0)
  · subst v
    simp [endpointConormal, unitTangent]
  · have hs : euclideanSpeed (-v.1, -v.2) = euclideanSpeed v := by
      have hcv :
          complexVector (-v.1, -v.2) = -complexVector v := by
        apply Complex.ext <;> simp [complexVector]
      change ‖complexVector (-v.1, -v.2)‖ = ‖complexVector v‖
      rw [hcv, norm_neg]
    ext <;> simp only [endpointConormal, unitTangent, hs] <;> ring

/-- Moving a positive distance on the continued interface has first-order
physical displacement opposite to the retained interface tangent. -/
def interfaceContinuationDisplacement {junction : PlanePoint}
    (F : RegularEndpointTrace junction) (y : ℝ) : PlanePoint :=
  (-y * (unitTangent F.velocity).1, -y * (unitTangent F.velocity).2)

lemma interfaceContinuationDisplacement_eq_neg_smul
    {junction : PlanePoint} (F : RegularEndpointTrace junction) (y : ℝ) :
    interfaceContinuationDisplacement F y = -y • unitTangent F.velocity := by
  rfl

/-- Bookkeeping identity distinguishing this move from trimming: incident
length `x` is removed, interface length `y` is added, and the connector receives
incident price `w`. -/
lemma extension_gain_bookkeeping (w x y connectorLength : ℝ) :
    w * x - (y + w * connectorLength) =
      w * x - y - w * connectorLength := by ring



/-! ## Concrete sign witness used by the independent specimen -/

namespace LambdaTwoExtension

def incidentVelocity : PlanePoint := (-3 / 5, 4 / 5)

def interfaceVelocity : PlanePoint := (1, 0)

lemma incidentVelocity_ne : incidentVelocity ≠ (0, 0) := by
  intro h
  have := congrArg Prod.snd h
  norm_num [incidentVelocity] at this

lemma interfaceVelocity_ne : interfaceVelocity ≠ (0, 0) := by
  intro h
  have := congrArg Prod.fst h
  norm_num [interfaceVelocity] at this

lemma incidentVelocity_speed : euclideanSpeed incidentVelocity = 1 := by
  rw [euclideanSpeed, Complex.norm_def]
  norm_num [complexVector, incidentVelocity, Complex.normSq_apply]

lemma interfaceVelocity_speed : euclideanSpeed interfaceVelocity = 1 := by
  norm_num [euclideanSpeed, complexVector, interfaceVelocity]

/-- Literal initial outward conormals of the two oriented specimen germs. -/
lemma endpointConormals :
    endpointConormal .initial incidentVelocity = (3 / 5, -4 / 5) ∧
      endpointConormal .initial interfaceVelocity = (-1, 0) := by
  rw [endpointConormal, endpointConormal, unitTangent, unitTangent,
    incidentVelocity_speed, interfaceVelocity_speed]
  norm_num [incidentVelocity, interfaceVelocity]

/-- The specimen lies strictly on the violating side `c < -1/2`. -/
lemma conormal_inner_eq : planeInner
    (endpointConormal .initial incidentVelocity)
    (endpointConormal .initial interfaceVelocity) = -3 / 5 := by
  rw [endpointConormals.1, endpointConormals.2]
  norm_num [planeInner]

lemma two_sqrt_eightyNine_lt_nineteen :
    2 * Real.sqrt 89 < 19 := by
  have hs0 := Real.sqrt_nonneg 89
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 89)
  nlinarith

/-- Removing unit incident length, exposing interface length `1/10`, and
inserting the exterior connector gives strict first-order descent at
`lambda = 2`. -/
theorem extension_gain_pos :
    0 < extensionTangentGain 2 1 (1 / 10) (-3 / 5) := by
  have hs :
      Real.sqrt ((1 : ℝ) ^ 2 + (1 / 10 : ℝ) ^ 2 +
        2 * 1 * (1 / 10) * (-3 / 5)) = Real.sqrt 89 / 10 := by
    rw [show (1 : ℝ) ^ 2 + (1 / 10 : ℝ) ^ 2 +
        2 * 1 * (1 / 10) * (-3 / 5) = 89 / 100 by norm_num,
      show (89 / 100 : ℝ) = 89 / 10 ^ 2 by norm_num,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 89)]
    norm_num
  rw [extensionTangentGain, hs]
  linarith [two_sqrt_eightyNine_lt_nineteen]
/-- The general endpoint-ratio constructor specializes to the positive
`2/15` choice; the independent specimen uses the simpler interior choice
`1/10`. -/
lemma endpointRatio_eq : extensionEndpointRatio 2 (-3 / 5) = 2 / 15 := by
  norm_num [extensionEndpointRatio]

end LambdaTwoExtension

/-! ## Reference geometry of the extension move -/

/-- Lower boundary of the interface-extending reference corner.  It is the
joining line on `0 ≤ u ≤ x` and the old incident axis for `x ≤ u`. -/
def extensionFloor (x y u : ℝ) : ℝ :=
  min ((y / x) * u - y) 0

lemma continuous_extensionFloor (x y : ℝ) :
    Continuous (extensionFloor x y) := by
  exact (((continuous_const.mul continuous_id).sub continuous_const).min
    continuous_const)

/-- Vertical shear by a continuous graph. -/
def verticalShear (f : ℝ → ℝ) (hf : Continuous f) :
    PlanePoint ≃ₜ PlanePoint where
  toFun q := (q.1, q.2 + f q.1)
  invFun q := (q.1, q.2 - f q.1)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp
  continuous_toFun :=
    continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst))
  continuous_invFun :=
    continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst))

@[simp] theorem verticalShear_apply (f : ℝ → ℝ) (hf : Continuous f)
    (q : PlanePoint) :
    verticalShear f hf q = (q.1, q.2 + f q.1) := rfl

/-- Shear realizing the interface-extending reference corner. -/
def extensionShear (x y : ℝ) : PlanePoint ≃ₜ PlanePoint :=
  verticalShear (extensionFloor x y) (continuous_extensionFloor x y)

@[simp] theorem extensionShear_apply (x y : ℝ) (q : PlanePoint) :
    extensionShear x y q = (q.1, q.2 + extensionFloor x y q.1) := rfl

/-- Open reference corner after continuing the interface through the old
contact and exposing a joining segment. -/
def interfaceExtendedOpenCorner (x y : ℝ) : Set PlanePoint :=
  extensionShear x y '' openCorner

lemma isOpen_interfaceExtendedOpenCorner (x y : ℝ) :
    IsOpen (interfaceExtendedOpenCorner x y) :=
  (extensionShear x y).isOpenMap _ isOpen_openCorner

theorem mem_interfaceExtendedOpenCorner (x y : ℝ) (q : PlanePoint) :
    q ∈ interfaceExtendedOpenCorner x y ↔
      0 < q.1 ∧ extensionFloor x y q.1 < q.2 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change 0 < z.1 ∧
      extensionFloor x y z.1 < z.2 + extensionFloor x y z.1
    exact ⟨hz.1, by linarith [hz.2]⟩
  · rintro ⟨hx, hy⟩
    refine ⟨(q.1, q.2 - extensionFloor x y q.1), ?_, ?_⟩
    · exact ⟨hx, by linarith⟩
    · ext <;> simp

/-- The complete continued interface ray, including the retained positive
part and the newly exposed negative segment. -/
def extendedInterfaceRay (y : ℝ) : Set PlanePoint :=
  {q | q.1 = 0 ∧ -y ≤ q.2}

/-- Only the newly exposed interface segment. -/
def negativeInterfaceSegment (y : ℝ) : Set PlanePoint :=
  {q | q.1 = 0 ∧ -y ≤ q.2 ∧ q.2 ≤ 0}

/-- Joining segment from the continued-interface endpoint `(0,-y)` to the
incident endpoint `(x,0)`. -/
def extensionConnector (x y : ℝ) : Set PlanePoint :=
  {q | 0 ≤ q.1 ∧ q.1 ≤ x ∧ q.2 = (y / x) * q.1 - y}

lemma extensionFloor_eq_line {x y u : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (_hu₀ : 0 ≤ u) (hux : u ≤ x) :
    extensionFloor x y u = (y / x) * u - y := by
  rw [extensionFloor, min_eq_left]
  have hdiv : 0 ≤ y / x := div_nonneg hy hx.le
  have hmul := mul_le_mul_of_nonneg_left hux hdiv
  have hcancel : (y / x) * x = y := by field_simp [hx.ne']
  rw [hcancel] at hmul
  linarith

lemma extensionFloor_eq_zero {x y u : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hxu : x ≤ u) :
    extensionFloor x y u = 0 := by
  rw [extensionFloor, min_eq_right]
  have hdiv : 0 ≤ y / x := div_nonneg hy hx.le
  have hmul := mul_le_mul_of_nonneg_left hxu hdiv
  have hcancel : (y / x) * x = y := by field_simp [hx.ne']
  rw [hcancel] at hmul
  linarith

lemma frontier_openCorner_eq_axes :
    frontier openCorner =
      {q : PlanePoint | 0 ≤ q.1 ∧ q.2 = 0} ∪
        {q : PlanePoint | q.1 = 0 ∧ 0 ≤ q.2} := by
  change frontier (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) = _
  rw [frontier_prod_eq, closure_Ioi, frontier_Ioi]
  ext q
  simp

private lemma extensionShear_image_horizontalAxis
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    extensionShear x y ''
        {q : PlanePoint | 0 ≤ q.1 ∧ q.2 = 0} =
      retainedIncidentRay x ∪ extensionConnector x y := by
  ext q
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    dsimp at hu hv ⊢
    subst v
    by_cases hux : u ≤ x
    · right
      exact ⟨hu, hux, by
        simpa using extensionFloor_eq_line hx hy.le hu hux⟩
    · left
      have hxu : x ≤ u := le_of_not_ge hux
      exact ⟨hxu, by
        simpa using extensionFloor_eq_zero hx hy.le hxu⟩
  · rintro (hq | hq)
    · refine ⟨(q.1, 0), ⟨le_trans hx.le hq.1, rfl⟩, ?_⟩
      rw [extensionShear_apply, extensionFloor_eq_zero hx hy.le hq.1]
      apply Prod.ext
      · rfl
      · simpa using hq.2.symm
    · refine ⟨(q.1, 0), ⟨hq.1, rfl⟩, ?_⟩
      rw [extensionShear_apply,
        extensionFloor_eq_line hx hy.le hq.1 hq.2.1]
      apply Prod.ext
      · rfl
      · simpa using hq.2.2.symm

private lemma extensionShear_image_verticalAxis
    {x y : ℝ} (_hx : 0 < x) (hy : 0 < y) :
    extensionShear x y ''
        {q : PlanePoint | q.1 = 0 ∧ 0 ≤ q.2} =
      extendedInterfaceRay y := by
  ext q
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    dsimp at hu hv ⊢
    subst u
    have hfloor : extensionFloor x y 0 = -y := by
      rw [extensionFloor]
      simp [hy.le]
    exact ⟨rfl, by rw [hfloor]; linarith⟩
  · rintro ⟨hq₁, hq₂⟩
    refine ⟨(0, q.2 + y), ⟨rfl, by linarith⟩, ?_⟩
    have hfloor : extensionFloor x y 0 = -y := by
      rw [extensionFloor]
      simp [hy.le]
    apply Prod.ext
    · simpa using hq₁.symm
    · simp [hfloor]

/-- Exact complete frontier of the reference extension geometry. -/
theorem frontier_interfaceExtendedOpenCorner {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    frontier (interfaceExtendedOpenCorner x y) =
      retainedIncidentRay x ∪ extendedInterfaceRay y ∪
        extensionConnector x y := by
  rw [interfaceExtendedOpenCorner, ← (extensionShear x y).image_frontier,
    frontier_openCorner_eq_axes, image_union,
    extensionShear_image_horizontalAxis hx hy,
    extensionShear_image_verticalAxis hx hy]
  ext q
  simp only [mem_union]
  tauto

lemma extendedInterfaceRay_eq_positive_union_negative {y : ℝ} (hy : 0 ≤ y) :
    extendedInterfaceRay y =
      retainedInterfaceRay 0 ∪ negativeInterfaceSegment y := by
  ext q
  simp only [extendedInterfaceRay, retainedInterfaceRay,
    negativeInterfaceSegment, mem_union, mem_ofPred_eq]
  constructor
  · intro hq
    by_cases hq₂ : 0 ≤ q.2
    · exact Or.inl ⟨hq.1, hq₂⟩
    · exact Or.inr ⟨hq.1, hq.2, le_of_not_ge hq₂⟩
  · rintro (hq | hq)
    · exact ⟨hq.1, le_trans (neg_nonpos.mpr hy) hq.2⟩
    · exact ⟨hq.1, hq.2.1⟩

/-- Four-piece accounting explicitly separates the added interface segment
from the retained positive interface ray and from the removed incident ray. -/
theorem frontier_interfaceExtendedOpenCorner_four_pieces {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) :
    frontier (interfaceExtendedOpenCorner x y) =
      retainedIncidentRay x ∪ retainedInterfaceRay 0 ∪
        negativeInterfaceSegment y ∪ extensionConnector x y := by
  rw [frontier_interfaceExtendedOpenCorner hx hy,
    extendedInterfaceRay_eq_positive_union_negative hy.le]
  ext q
  simp only [mem_union]
  tauto

end CMVRelaxation.RegularTraceCornerComparison
