/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVGeometry
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constant-curvature source traces

This module integrates constant signed curvature on an actual planar trace.  The
position and tangent derivatives are coordinatewise `HasDerivAt` facts; no
supporting-circle membership or reparameterization is assumed.  Continuity
extends the center invariant and circle identity through both closed endpoints.
-/

open Set Real

noncomputable section

namespace CMVCurvatureIntegration

/-- The center selected by position, unit tangent, and nonzero signed curvature. -/
def centerInvariant (trace tangent : ℝ → PlanePoint) (curvature t : ℝ) : PlanePoint :=
  ((trace t).1 - (tangent t).2 / curvature,
    (trace t).2 + (tangent t).1 / curvature)

/-- A scalar function continuous on a closed interval and with zero derivative
on its interior is constant through both endpoints. -/
lemma eqOn_Icc_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) :
    Set.EqOn f (fun _ => f a) (Icc a b) := by
  have hdiff : DifferentiableOn ℝ f (Ioo a b) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hzero : (Ioo a b).EqOn (deriv f) 0 := by
    intro x hx
    simpa using (hderiv x hx).deriv
  obtain ⟨c, hc⟩ :=
    isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero
  have hclosure : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hcont' : ∀ x ∈ closure (Ioo a b), ContinuousWithinAt f (Ioo a b) x := by
    intro x hx
    apply (hcont x (hclosure ▸ hx)).mono
    exact Ioo_subset_Icc_self
  have hccl : (closure (Ioo a b)).EqOn f (fun _ => c) :=
    ContinuousWithinAt.eqOn_const_closure hcont' hc
  have hcIcc : (Icc a b).EqOn f (fun _ => c) := hclosure ▸ hccl
  intro x hx
  exact (hcIcc hx).trans (hcIcc ⟨le_rfl, hab.le⟩).symm

/-- A genuine unit-speed planar trace whose actual tangent has constant signed
curvature on the interior of a nondegenerate closed parameter interval. -/
structure UnitSpeedConstantCurvatureOn
    (trace tangent : ℝ → PlanePoint) (curvature a b : ℝ) : Prop where
  start_lt_finish : a < b
  curvature_ne_zero : curvature ≠ 0
  trace_fst_continuous : ContinuousOn (fun t => (trace t).1) (Icc a b)
  trace_snd_continuous : ContinuousOn (fun t => (trace t).2) (Icc a b)
  tangent_fst_continuous : ContinuousOn (fun t => (tangent t).1) (Icc a b)
  tangent_snd_continuous : ContinuousOn (fun t => (tangent t).2) (Icc a b)
  trace_fst_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (trace u).1) (tangent t).1 t
  trace_snd_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (trace u).2) (tangent t).2 t
  tangent_fst_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (tangent u).1) (-curvature * (tangent t).2) t
  tangent_snd_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (tangent u).2) (curvature * (tangent t).1) t
  unit_speed : ∀ t ∈ Icc a b, (tangent t).1 ^ 2 + (tangent t).2 ^ 2 = 1

namespace UnitSpeedConstantCurvatureOn

variable {trace tangent : ℝ → PlanePoint} {curvature a b : ℝ}
    (h : UnitSpeedConstantCurvatureOn trace tangent curvature a b)

include h

lemma center_fst_hasDerivAt_zero {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (centerInvariant trace tangent curvature u).1) 0 t := by
  change HasDerivAt
    (fun u => (trace u).1 - (tangent u).2 / curvature) 0 t
  have hd := (h.trace_fst_derivative t ht).sub
    ((h.tangent_snd_derivative t ht).div_const curvature)
  exact hd.congr_deriv (by
    field_simp [h.curvature_ne_zero]
    ring)

lemma center_snd_hasDerivAt_zero {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (centerInvariant trace tangent curvature u).2) 0 t := by
  change HasDerivAt
    (fun u => (trace u).2 + (tangent u).1 / curvature) 0 t
  have hd := (h.trace_snd_derivative t ht).add
    ((h.tangent_fst_derivative t ht).div_const curvature)
  exact hd.congr_deriv (by
    field_simp [h.curvature_ne_zero]
    ring)

lemma center_fst_continuousOn :
    ContinuousOn (fun t => (centerInvariant trace tangent curvature t).1) (Icc a b) := by
  exact h.trace_fst_continuous.sub (h.tangent_snd_continuous.div_const curvature)

lemma center_snd_continuousOn :
    ContinuousOn (fun t => (centerInvariant trace tangent curvature t).2) (Icc a b) := by
  exact h.trace_snd_continuous.add (h.tangent_fst_continuous.div_const curvature)

/-- The center invariant is constant on the whole closed parameter interval.
The endpoint values are obtained by continuity; no endpoint derivative is used. -/
theorem center_invariant {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    centerInvariant trace tangent curvature s =
      centerInvariant trace tangent curvature t := by
  have hfst := eqOn_Icc_of_hasDerivAt_zero h.start_lt_finish
    h.center_fst_continuousOn (fun _ ht' => h.center_fst_hasDerivAt_zero ht')
  have hsnd := eqOn_Icc_of_hasDerivAt_zero h.start_lt_finish
    h.center_snd_continuousOn (fun _ ht' => h.center_snd_hasDerivAt_zero ht')
  apply Prod.ext
  · exact (hfst hs).trans (hfst ht).symm
  · exact (hsnd hs).trans (hsnd ht).symm

/-- Every point, including both endpoints, lies on the circle selected by the
constant center and signed curvature. -/
theorem closed_circle_identity {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ((trace t).1 - (centerInvariant trace tangent curvature s).1) ^ 2 +
      ((trace t).2 - (centerInvariant trace tangent curvature s).2) ^ 2 =
        (1 / curvature) ^ 2 := by
  rw [h.center_invariant hs ht]
  have hu := h.unit_speed t ht
  simp only [centerInvariant]
  field_simp [h.curvature_ne_zero]
  nlinarith

/-- Both closed parameter endpoints lie on the same supporting circle. -/
theorem closed_endpoints_circle_identity :
    (((trace a).1 - (centerInvariant trace tangent curvature a).1) ^ 2 +
        ((trace a).2 - (centerInvariant trace tangent curvature a).2) ^ 2 =
          (1 / curvature) ^ 2) ∧
      (((trace b).1 - (centerInvariant trace tangent curvature a).1) ^ 2 +
        ((trace b).2 - (centerInvariant trace tangent curvature a).2) ^ 2 =
          (1 / curvature) ^ 2) := by
  constructor
  · exact h.closed_circle_identity
      ⟨le_rfl, h.start_lt_finish.le⟩ ⟨le_rfl, h.start_lt_finish.le⟩
  · exact h.closed_circle_identity
      ⟨le_rfl, h.start_lt_finish.le⟩ ⟨h.start_lt_finish.le, le_rfl⟩

omit h in
/-- Positive traversal curvature gives the ordinary radius-square identity. -/
theorem closed_circle_identity_of_positive_radius
    {radius s t : ℝ}
    (hradius : 0 < radius)
    (hp : UnitSpeedConstantCurvatureOn trace tangent (1 / radius) a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ((trace t).1 - (centerInvariant trace tangent (1 / radius) s).1) ^ 2 +
      ((trace t).2 - (centerInvariant trace tangent (1 / radius) s).2) ^ 2 =
        radius ^ 2 := by
  rw [hp.closed_circle_identity hs ht]
  field_simp [hradius.ne']

omit h in
/-- Reversing traversal changes the signed curvature but not the supporting circle. -/
theorem closed_circle_identity_of_negative_radius
    {radius s t : ℝ}
    (hradius : 0 < radius)
    (hn : UnitSpeedConstantCurvatureOn trace tangent (-1 / radius) a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ((trace t).1 - (centerInvariant trace tangent (-1 / radius) s).1) ^ 2 +
      ((trace t).2 - (centerInvariant trace tangent (-1 / radius) s).2) ^ 2 =
        radius ^ 2 := by
  rw [hn.closed_circle_identity hs ht]
  field_simp [hradius.ne']

end UnitSpeedConstantCurvatureOn

/-! ## Arbitrary positive-speed traces -/

/-- Euclidean speed of an actual coordinate velocity. -/
def euclideanSpeed (velocity : ℝ → PlanePoint) (t : ℝ) : ℝ :=
  √((velocity t).1 ^ 2 + (velocity t).2 ^ 2)

/-- Unit tangent obtained from the actual coordinate velocity. -/
def normalizedTangent (velocity : ℝ → PlanePoint) (t : ℝ) : PlanePoint :=
  ((velocity t).1 / euclideanSpeed velocity t,
    (velocity t).2 / euclideanSpeed velocity t)

/-- A regular planar trace at arbitrary positive Euclidean speed whose signed
curvature, computed from its actual first and second coordinate derivatives, is
constant.  Closed-endpoint velocity continuity and positivity are explicit;
derivatives are required only on the relative interior. -/
structure ArbitrarySpeedConstantCurvatureOn
    (trace velocity acceleration : ℝ → PlanePoint)
    (curvature a b : ℝ) : Prop where
  start_lt_finish : a < b
  curvature_ne_zero : curvature ≠ 0
  trace_fst_continuous : ContinuousOn (fun t => (trace t).1) (Icc a b)
  trace_snd_continuous : ContinuousOn (fun t => (trace t).2) (Icc a b)
  velocity_fst_continuous : ContinuousOn (fun t => (velocity t).1) (Icc a b)
  velocity_snd_continuous : ContinuousOn (fun t => (velocity t).2) (Icc a b)
  trace_fst_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (trace u).1) (velocity t).1 t
  trace_snd_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (trace u).2) (velocity t).2 t
  velocity_fst_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (velocity u).1) (acceleration t).1 t
  velocity_snd_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun u => (velocity u).2) (acceleration t).2 t
  positive_speed : ∀ t ∈ Icc a b, 0 < euclideanSpeed velocity t
  signed_curvature : ∀ t ∈ Ioo a b,
    (velocity t).1 * (acceleration t).2 -
        (velocity t).2 * (acceleration t).1 =
      curvature * euclideanSpeed velocity t ^ 3

namespace ArbitrarySpeedConstantCurvatureOn

variable {trace velocity acceleration : ℝ → PlanePoint}
    {curvature a b : ℝ}
    (h : ArbitrarySpeedConstantCurvatureOn
      trace velocity acceleration curvature a b)

include h

omit h in
lemma speed_sq (t : ℝ) :
    euclideanSpeed velocity t ^ 2 =
      (velocity t).1 ^ 2 + (velocity t).2 ^ 2 := by
  unfold euclideanSpeed
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma speed_ne {t : ℝ} (ht : t ∈ Icc a b) :
    euclideanSpeed velocity t ≠ 0 :=
  (h.positive_speed t ht).ne'

lemma normalized_tangent_unit {t : ℝ} (ht : t ∈ Icc a b) :
    (normalizedTangent velocity t).1 ^ 2 +
        (normalizedTangent velocity t).2 ^ 2 = 1 := by
  have hsne := h.speed_ne ht
  have hsq := speed_sq (velocity := velocity) t
  simp only [normalizedTangent]
  field_simp [hsne]
  nlinarith

lemma speed_continuousOn :
    ContinuousOn (euclideanSpeed velocity) (Icc a b) := by
  exact
    ((h.velocity_fst_continuous.pow 2).add
      (h.velocity_snd_continuous.pow 2)).sqrt

lemma normalized_tangent_fst_continuousOn :
    ContinuousOn (fun t => (normalizedTangent velocity t).1) (Icc a b) := by
  exact h.velocity_fst_continuous.div h.speed_continuousOn
    (fun t ht => h.speed_ne ht)

lemma normalized_tangent_snd_continuousOn :
    ContinuousOn (fun t => (normalizedTangent velocity t).2) (Icc a b) := by
  exact h.velocity_snd_continuous.div h.speed_continuousOn
    (fun t ht => h.speed_ne ht)

/-- The derivative of speed is obtained from the actual acceleration; it is not
an independently supplied parameter-speed derivative. -/
lemma speed_hasDerivAt {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (euclideanSpeed velocity)
      (((velocity t).1 * (acceleration t).1 +
          (velocity t).2 * (acceleration t).2) /
        euclideanSpeed velocity t) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hx := (h.velocity_fst_derivative t ht).pow 2
  have hy := (h.velocity_snd_derivative t ht).pow 2
  have hnorm :
      HasDerivAt
        (((fun u => (velocity u).1) ^ 2) +
          ((fun u => (velocity u).2) ^ 2))
        (2 * ((velocity t).1 * (acceleration t).1 +
          (velocity t).2 * (acceleration t).2)) t := by
    exact (hx.add hy).congr_deriv (by norm_num; ring)
  have hnorm_ne :
      (velocity t).1 ^ 2 + (velocity t).2 ^ 2 ≠ 0 := by
    intro hzero
    have hsq := speed_sq (velocity := velocity) t
    have hspos := h.positive_speed t htIcc
    nlinarith
  have hsqrt := hnorm.sqrt (by
    simpa only [Pi.add_apply, Pi.pow_apply] using hnorm_ne)
  change HasDerivAt
    (fun u => √((velocity u).1 ^ 2 + (velocity u).2 ^ 2))
    (((velocity t).1 * (acceleration t).1 +
        (velocity t).2 * (acceleration t).2) /
      euclideanSpeed velocity t) t
  simpa only [Pi.add_apply, Pi.pow_apply] using hsqrt.congr_deriv (by
    have hsne := h.speed_ne htIcc
    unfold euclideanSpeed at hsne ⊢
    simp only [Pi.add_apply, Pi.pow_apply]
    field_simp [hsne])
/-- The normalized tangent equation follows from the signed-curvature
determinant and the actual speed derivative. -/
lemma normalized_tangent_fst_hasDerivAt {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (normalizedTangent velocity u).1)
      (-curvature * (velocity t).2) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hsne := h.speed_ne htIcc
  have hraw := (h.velocity_fst_derivative t ht).div
    (h.speed_hasDerivAt ht) hsne
  change HasDerivAt
    (fun u => (velocity u).1 / euclideanSpeed velocity u)
    (-curvature * (velocity t).2) t
  exact hraw.congr_deriv (by
    have hsq := speed_sq (velocity := velocity) t
    have hcurv := h.signed_curvature t ht
    field_simp [hsne]
    linear_combination
      (acceleration t).1 * hsq - (velocity t).2 * hcurv)

lemma normalized_tangent_snd_hasDerivAt {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (normalizedTangent velocity u).2)
      (curvature * (velocity t).1) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hsne := h.speed_ne htIcc
  have hraw := (h.velocity_snd_derivative t ht).div
    (h.speed_hasDerivAt ht) hsne
  change HasDerivAt
    (fun u => (velocity u).2 / euclideanSpeed velocity u)
    (curvature * (velocity t).1) t
  exact hraw.congr_deriv (by
    have hsq := speed_sq (velocity := velocity) t
    have hcurv := h.signed_curvature t ht
    field_simp [hsne]
    linear_combination
      (acceleration t).2 * hsq + (velocity t).1 * hcurv)

/-- The actual position derivative is speed times the derived unit tangent. -/
lemma trace_fst_hasDerivAt_speed_mul_tangent {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (trace u).1)
      (euclideanSpeed velocity t * (normalizedTangent velocity t).1) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact (h.trace_fst_derivative t ht).congr_deriv (by
    simp only [normalizedTangent]
    field_simp [h.speed_ne htIcc])

/-- The second actual position derivative coordinate has the same
speed-times-unit-tangent form. -/
lemma trace_snd_hasDerivAt_speed_mul_tangent {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (trace u).2)
      (euclideanSpeed velocity t * (normalizedTangent velocity t).2) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact (h.trace_snd_derivative t ht).congr_deriv (by
    simp only [normalizedTangent]
    field_simp [h.speed_ne htIcc])

/-- First coordinate of the arbitrary-parameter Frenet equation
`T' = speed * curvature * J T`. -/
lemma normalized_tangent_fst_frenet {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (normalizedTangent velocity u).1)
      (-(euclideanSpeed velocity t * curvature *
        (normalizedTangent velocity t).2)) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact (h.normalized_tangent_fst_hasDerivAt ht).congr_deriv (by
    simp only [normalizedTangent]
    field_simp [h.speed_ne htIcc])

/-- Second coordinate of the arbitrary-parameter Frenet equation
`T' = speed * curvature * J T`. -/
lemma normalized_tangent_snd_frenet {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (normalizedTangent velocity u).2)
      (euclideanSpeed velocity t * curvature *
        (normalizedTangent velocity t).1) t := by
  have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  exact (h.normalized_tangent_snd_hasDerivAt ht).congr_deriv (by
    simp only [normalizedTangent]
    field_simp [h.speed_ne htIcc])

/-- The full normalized-tangent differential equation is derived from the
actual first and second coordinate derivatives, with no supplied
reparameterization. -/
theorem normalized_tangent_differential_equation {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun u => (normalizedTangent velocity u).1)
        (-(euclideanSpeed velocity t * curvature *
          (normalizedTangent velocity t).2)) t ∧
      HasDerivAt (fun u => (normalizedTangent velocity u).2)
        (euclideanSpeed velocity t * curvature *
          (normalizedTangent velocity t).1) t :=
  ⟨h.normalized_tangent_fst_frenet ht,
    h.normalized_tangent_snd_frenet ht⟩

lemma center_fst_hasDerivAt_zero {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt
      (fun u => (centerInvariant trace (normalizedTangent velocity)
        curvature u).1) 0 t := by
  change HasDerivAt
    (fun u => (trace u).1 - (normalizedTangent velocity u).2 / curvature) 0 t
  have hd := (h.trace_fst_hasDerivAt_speed_mul_tangent ht).sub
    ((h.normalized_tangent_snd_frenet ht).div_const curvature)
  exact hd.congr_deriv (by
    field_simp [h.curvature_ne_zero]
    ring)

lemma center_snd_hasDerivAt_zero {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt
      (fun u => (centerInvariant trace (normalizedTangent velocity)
        curvature u).2) 0 t := by
  change HasDerivAt
    (fun u => (trace u).2 + (normalizedTangent velocity u).1 / curvature) 0 t
  have hd := (h.trace_snd_hasDerivAt_speed_mul_tangent ht).add
    ((h.normalized_tangent_fst_frenet ht).div_const curvature)
  exact hd.congr_deriv (by
    field_simp [h.curvature_ne_zero]
    ring)

lemma center_fst_continuousOn :
    ContinuousOn
      (fun t => (centerInvariant trace (normalizedTangent velocity)
        curvature t).1) (Icc a b) := by
  exact h.trace_fst_continuous.sub
    (h.normalized_tangent_snd_continuousOn.div_const curvature)

lemma center_snd_continuousOn :
    ContinuousOn
      (fun t => (centerInvariant trace (normalizedTangent velocity)
        curvature t).2) (Icc a b) := by
  exact h.trace_snd_continuous.add
    (h.normalized_tangent_fst_continuousOn.div_const curvature)

/-- The supporting-circle center is constant for an arbitrary positive-speed
parameterization. -/
theorem center_invariant {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    centerInvariant trace (normalizedTangent velocity) curvature s =
      centerInvariant trace (normalizedTangent velocity) curvature t := by
  have hfst := eqOn_Icc_of_hasDerivAt_zero h.start_lt_finish
    h.center_fst_continuousOn (fun _ hu => h.center_fst_hasDerivAt_zero hu)
  have hsnd := eqOn_Icc_of_hasDerivAt_zero h.start_lt_finish
    h.center_snd_continuousOn (fun _ hu => h.center_snd_hasDerivAt_zero hu)
  apply Prod.ext
  · exact (hfst hs).trans (hfst ht).symm
  · exact (hsnd hs).trans (hsnd ht).symm

/-- Every closed-interval point lies on the supporting circle selected by the
derived normalized tangent. -/
theorem closed_circle_identity {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ((trace t).1 -
        (centerInvariant trace (normalizedTangent velocity) curvature s).1) ^ 2 +
      ((trace t).2 -
        (centerInvariant trace (normalizedTangent velocity) curvature s).2) ^ 2 =
        (1 / curvature) ^ 2 := by
  rw [h.center_invariant hs ht]
  have hu := h.normalized_tangent_unit ht
  simp only [centerInvariant]
  field_simp [h.curvature_ne_zero]
  nlinarith

/-- Both parameter endpoints satisfy the same derived supporting-circle
identity; no endpoint acceleration or tangent direction is required. -/
theorem closed_endpoints_circle_identity :
    (((trace a).1 -
          (centerInvariant trace (normalizedTangent velocity) curvature a).1) ^ 2 +
        ((trace a).2 -
          (centerInvariant trace (normalizedTangent velocity) curvature a).2) ^ 2 =
          (1 / curvature) ^ 2) ∧
      (((trace b).1 -
          (centerInvariant trace (normalizedTangent velocity) curvature a).1) ^ 2 +
        ((trace b).2 -
          (centerInvariant trace (normalizedTangent velocity) curvature a).2) ^ 2 =
          (1 / curvature) ^ 2) := by
  constructor
  · exact h.closed_circle_identity
      ⟨le_rfl, h.start_lt_finish.le⟩ ⟨le_rfl, h.start_lt_finish.le⟩
  · exact h.closed_circle_identity
      ⟨le_rfl, h.start_lt_finish.le⟩ ⟨h.start_lt_finish.le, le_rfl⟩

omit h in
/-- Positive signed curvature gives a radius-`radius` supporting circle for an
arbitrary positive-speed trace. -/
theorem closed_circle_identity_of_positive_radius
    {radius s t : ℝ}
    (hradius : 0 < radius)
    (hp : ArbitrarySpeedConstantCurvatureOn
      trace velocity acceleration (1 / radius) a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ((trace t).1 -
        (centerInvariant trace (normalizedTangent velocity) (1 / radius) s).1) ^ 2 +
      ((trace t).2 -
        (centerInvariant trace (normalizedTangent velocity) (1 / radius) s).2) ^ 2 =
        radius ^ 2 := by
  rw [hp.closed_circle_identity hs ht]
  field_simp [hradius.ne']

omit h in
/-- Negative signed curvature changes orientation but gives the same
radius-`radius` supporting-circle conclusion. -/
theorem closed_circle_identity_of_negative_radius
    {radius s t : ℝ}
    (hradius : 0 < radius)
    (hn : ArbitrarySpeedConstantCurvatureOn
      trace velocity acceleration (-1 / radius) a b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ((trace t).1 -
        (centerInvariant trace (normalizedTangent velocity) (-1 / radius) s).1) ^ 2 +
      ((trace t).2 -
        (centerInvariant trace (normalizedTangent velocity) (-1 / radius) s).2) ^ 2 =
        radius ^ 2 := by
  rw [hn.closed_circle_identity hs ht]
  field_simp [hradius.ne']

end ArbitrarySpeedConstantCurvatureOn
end CMVCurvatureIntegration
