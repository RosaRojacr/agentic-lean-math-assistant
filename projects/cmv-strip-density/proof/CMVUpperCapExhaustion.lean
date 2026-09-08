/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRigidProjection
import TypeThreeAssembly
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Isometry

/-!
# Shared upper-cap projection patches

Finite tangent rectangles on an actual upper circular cap, with collars and
strip-density weights stated in the source coordinate plane.  One implementation
serves both closed-curvature `FourArcCandidate` values and branch-complete
`TypeThreeAssembly` values, including major caps.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff BigOperators

noncomputable section

namespace CMVRelaxation

/-- The Euclidean coordinate plane identified isometrically with `ℂ`, with the
real part representing the second source coordinate and the imaginary part the
first. -/
def tangentComplexEquiv : EuclideanPlane ≃ᵢ ℂ where
  toEquiv :=
    { toFun := fun p => ⟨(WithLp.ofLp p).2, (WithLp.ofLp p).1⟩
      invFun := fun z => WithLp.toLp 2 (z.im, z.re)
      left_inv := by
        intro p
        rfl
      right_inv := by
        intro z
        rfl }
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    rw [WithLp.prod_dist_eq_add (by norm_num)]
    norm_num [Real.dist_eq, sq_abs]
    rw [← Real.sqrt_eq_rpow]
    congr 1
    ring

/-- Tangent/outward-normal coordinates at signed arclength `s` on the circle
with source center `center` and radius `r`.  The local origin is the circle
point; the first local coordinate is tangent and the second is outward normal. -/
def upperCircleTangentFrame (center : PlanePoint) (r s : ℝ) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  tangentComplexEquiv.trans <|
    (rotation (Circle.exp (s / r))).toIsometryEquiv.trans <|
    (IsometryEquiv.addLeft
      (⟨center.2, center.1⟩ + unitCircleArc r s)).trans
      tangentComplexEquiv.symm

@[simp] theorem tangentComplexEquiv_apply (p : EuclideanPlane) :
    tangentComplexEquiv p =
      ⟨(WithLp.ofLp p).2, (WithLp.ofLp p).1⟩ := rfl

@[simp] theorem tangentComplexEquiv_symm_apply (z : ℂ) :
    tangentComplexEquiv.symm z = WithLp.toLp 2 (z.im, z.re) := rfl

@[simp] theorem planeEuclideanHomeomorph_symm_tangentComplexEquiv_symm
    (z : ℂ) :
    planeEuclideanHomeomorph.symm (tangentComplexEquiv.symm z) =
      (z.im, z.re) := rfl

@[simp] theorem planeEuclideanHomeomorph_symm_toLp (p : PlanePoint) :
    planeEuclideanHomeomorph.symm (WithLp.toLp 2 p) = p := rfl

@[simp] theorem euclideanRigidMap_upperCircleTangentFrame
    (center : PlanePoint) (r s : ℝ) (p : PlanePoint) :
    euclideanRigidMap (upperCircleTangentFrame center r s) p =
      (center.1 + r * Real.sin (s / r) +
          p.1 * Real.cos (s / r) + p.2 * Real.sin (s / r),
        center.2 + r * Real.cos (s / r) -
          p.1 * Real.sin (s / r) + p.2 * Real.cos (s / r)) := by
  have hcast :
      (s : ℂ) / (r : ℂ) = ((s / r : ℝ) : ℂ) := by
    push_cast
    rfl
  apply Prod.ext
  · simp [euclideanRigidMap, upperCircleTangentFrame,
      rotation_apply, Circle.coe_exp, unitCircleArc]
    rw [mul_comm Complex.I]
    rw [hcast, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  · simp [euclideanRigidMap, upperCircleTangentFrame,
      rotation_apply, Circle.coe_exp, unitCircleArc]
    rw [mul_comm Complex.I]
    rw [hcast, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring

lemma tangentRectangle_radius_lt_sin
    {kappa d : ℝ} (hkappa_pos : 0 < kappa)
    (hkappa_lt : kappa < 1 / 2) (hd_pos : 0 < d)
    (hd_lt : d < 1 / 4) (hquad : 4 * d ^ 2 < kappa) :
    √((1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4) < Real.sin d := by
  have hkappa_sq : kappa ^ 2 < kappa / 2 := by
    nlinarith [mul_pos hkappa_pos (sub_pos.mpr hkappa_lt)]
  have hfactor :
      (1 - kappa) ^ 2 + 4 * d ^ 2 < (1 - d ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (d ^ 2), sq_nonneg kappa]
  have hone : 0 < 1 - d ^ 2 := by nlinarith [sq_nonneg d]
  have hd_one : d < 1 := lt_trans hd_lt (by norm_num)
  have hright : 0 < d * (1 - d ^ 2) := mul_pos hd_pos hone
  have hsqrt :
      √((1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4) <
        d * (1 - d ^ 2) := by
    rw [Real.sqrt_lt' hright]
    nlinarith [sq_pos_of_pos hd_pos]
  have hcubic := Real.sin_ge_sub_cube hd_pos.le
  have hpoly : d * (1 - d ^ 2) ≤ d - d ^ 3 / 6 := by
    nlinarith [pow_pos hd_pos 3]
  exact hsqrt.trans_le (hpoly.trans hcubic)

private lemma dist_planeEuclideanHomeomorph_zero (p : PlanePoint) :
    dist (planeEuclideanHomeomorph p) 0 = √(p.1 ^ 2 + p.2 ^ 2) := by
  change dist (WithLp.toLp 2 p) 0 = _
  rw [WithLp.prod_dist_eq_of_L2]
  simp

lemma rigidProjectionBox_euclidean_subset_ball
    {r kappa d : ℝ} (hr : 0 < r) (hkappa_pos : 0 < kappa)
    (hkappa_lt : kappa < 1 / 2) (hd_pos : 0 < d)
    (hd_lt : d < 1 / 4) (hquad : 4 * d ^ 2 < kappa)
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) :
    planeEuclideanHomeomorph ''
        rigidProjectionBox e
          (-r * (1 - kappa) * d) (r * (1 - kappa) * d)
          0 (r * d ^ 2) ⊆
      Metric.ball (e 0) (r * Real.sin d) := by
  have hsin := tangentRectangle_radius_lt_sin
    hkappa_pos hkappa_lt hd_pos hd_lt hquad
  have hsin_pos : 0 < Real.sin d :=
    Real.sin_pos_of_pos_of_lt_pi hd_pos
      (by linarith [Real.pi_gt_three])
  have hA :
      0 ≤ (1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4 := by positivity
  have hsquares :
      (1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4 <
        (Real.sin d) ^ 2 := by
    have hsq := (sq_lt_sq₀
      (Real.sqrt_nonneg
        ((1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4))
      hsin_pos.le).2 hsin
    rwa [Real.sq_sqrt hA] at hsq
  have hscale :
      r ^ 2 * ((1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4) <
        (r * Real.sin d) ^ 2 := by
    calc
      r ^ 2 * ((1 - kappa) ^ 2 * d ^ 2 + 4 * d ^ 4) <
          r ^ 2 * (Real.sin d) ^ 2 :=
        mul_lt_mul_of_pos_left hsquares (sq_pos_of_pos hr)
      _ = (r * Real.sin d) ^ 2 := by ring
  rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
  rw [Metric.mem_ball, planeEuclideanHomeomorph_euclideanRigidMap,
    e.dist_eq, dist_planeEuclideanHomeomorph_zero]
  change p.1 ∈ Icc (-r * (1 - kappa) * d)
      (r * (1 - kappa) * d) ∧
    p.2 ∈ Icc (0 - 2 * (r * d ^ 2))
      (0 + 2 * (r * d ^ 2)) at hp
  have hw_pos : 0 < r * (1 - kappa) * d := by
    have : 0 < 1 - kappa := by linarith
    positivity
  have hz_pos : 0 < 2 * (r * d ^ 2) := by positivity
  have hxprod :
      0 ≤ (p.1 + r * (1 - kappa) * d) *
        (r * (1 - kappa) * d - p.1) :=
    mul_nonneg (by linarith [hp.1.1]) (by linarith [hp.1.2])
  have hzprod :
      0 ≤ (p.2 + 2 * (r * d ^ 2)) *
        (2 * (r * d ^ 2) - p.2) :=
    mul_nonneg (by linarith [hp.2.1]) (by linarith [hp.2.2])
  rw [Real.sqrt_lt' (mul_pos hr hsin_pos)]
  nlinarith [hscale]

lemma tangentRectangle_lower_circle
    {r kappa d x z : ℝ} (hr : 0 < r)
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (hx : x ∈ Icc (-r * (1 - kappa) * d)
      (r * (1 - kappa) * d))
    (hz : z ∈ Icc (-2 * (r * d ^ 2)) (-(r * d ^ 2))) :
    x ^ 2 + (r + z) ^ 2 < r ^ 2 := by
  have hkappa_sq : kappa ^ 2 < kappa / 2 := by
    nlinarith [mul_pos hkappa_pos (sub_pos.mpr hkappa_lt)]
  have hd_sq : d ^ 2 < 1 / 16 := by nlinarith [sq_pos_of_pos hd_pos]
  have hcornerNorm :
      (1 - kappa) ^ 2 * d ^ 2 + (1 - d ^ 2) ^ 2 < 1 := by
    nlinarith [sq_nonneg kappa, sq_nonneg d,
      mul_pos hkappa_pos (sq_pos_of_pos hd_pos)]
  have hcorner :
      (r * (1 - kappa) * d) ^ 2 +
          (r * (1 - d ^ 2)) ^ 2 < r ^ 2 := by
    have hscale := mul_lt_mul_of_pos_left hcornerNorm (sq_pos_of_pos hr)
    nlinarith
  have hxprod :
      0 ≤ (x + r * (1 - kappa) * d) *
        (r * (1 - kappa) * d - x) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have h2d : 2 * d ^ 2 < 1 := by nlinarith
  have hr2d : 2 * (r * d ^ 2) < r := by
    have := mul_lt_mul_of_pos_left h2d hr
    nlinarith
  have hrz_pos : 0 < r + z := by linarith [hz.1]
  have hone : 0 < 1 - d ^ 2 := by nlinarith
  have htop_pos : 0 < r * (1 - d ^ 2) := mul_pos hr hone
  have hrz_le : r + z ≤ r * (1 - d ^ 2) := by
    nlinarith [hz.2]
  have hzsq :
      (r + z) ^ 2 ≤ (r * (1 - d ^ 2)) ^ 2 :=
    (sq_le_sq₀ hrz_pos.le htop_pos.le).2 hrz_le
  nlinarith [hxprod]

lemma tangentRectangle_upper_circle
    {r d x z : ℝ} (hr : 0 < r) (hd_pos : 0 < d)
    (hz : r * d ^ 2 ≤ z) :
    r ^ 2 < x ^ 2 + (r + z) ^ 2 := by
  have hrz : r < r + z := by
    nlinarith [mul_pos hr (sq_pos_of_pos hd_pos)]
  have hsquare := (sq_lt_sq₀ hr.le (by linarith : 0 ≤ r + z)).2 hrz
  nlinarith [sq_nonneg x]

lemma upperCircleTangentFrame_radiusSquared
    (center : PlanePoint) (r s : ℝ) (p : PlanePoint) :
    let q := euclideanRigidMap (upperCircleTangentFrame center r s) p
    (q.1 - center.1) ^ 2 + (q.2 - center.2) ^ 2 =
      p.1 ^ 2 + (r + p.2) ^ 2 := by
  simp only [euclideanRigidMap_upperCircleTangentFrame]
  have htrig := Real.sin_sq_add_cos_sq (s / r)
  nlinarith

private lemma source_snd_dist_le_euclidean_dist (p q : PlanePoint) :
    dist p.2 q.2 ≤
      dist (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q) := by
  have h := WithLp.dist_snd_le
    (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q)
  change dist p.2 q.2 ≤ _ at h
  exact h

private lemma window_source_above
    {W : Set PlanePoint} {q : PlanePoint} {rad gap : ℝ}
    (hW : planeEuclideanHomeomorph '' W ⊆
      Metric.ball (planeEuclideanHomeomorph q) rad)
    (hq : 1 + gap ≤ q.2) (hrad : rad < gap) :
    ∀ p ∈ W, 1 < p.2 := by
  intro p hp
  have hball := hW ⟨p, hp, rfl⟩
  rw [Metric.mem_ball] at hball
  have hcoord := source_snd_dist_le_euclidean_dist p q
  rw [Real.dist_eq] at hcoord
  have hleft : q.2 - p.2 ≤ |p.2 - q.2| := by
    calc
      q.2 - p.2 ≤ |q.2 - p.2| := le_abs_self _
      _ = |p.2 - q.2| := abs_sub_comm _ _
  linarith

lemma upperCircleTangentFrame_center_dist
    {r : ℝ} (hr : 0 < r) (center : PlanePoint) (s t : ℝ) :
    dist ((upperCircleTangentFrame center r s) 0)
        ((upperCircleTangentFrame center r t) 0) =
      r * |2 * Real.sin (((s - t) / r) / 2)| := by
  have hframe (u : ℝ) :
      tangentComplexEquiv ((upperCircleTangentFrame center r u) 0) =
        ⟨center.2, center.1⟩ + unitCircleArc r u := by
    apply Complex.ext <;> simp [upperCircleTangentFrame, rotation_apply]
  rw [← tangentComplexEquiv.dist_eq, hframe s, hframe t, dist_add_left]
  exact unitCircleArc_dist hr

/-- Exact finite-mesh separation on any circular arc of half-angle below `π`.
For distinct ordered mesh cells, the intervening angle stays at least one mesh
step from both endpoints.  The reflected branch `sin (π - x) = sin x` is what
allows the estimate to remain valid when the intervening angle crosses `π / 2`.
-/
theorem finiteMesh_index_bounds_and_sin
    {d theta alpha : ℝ} {N : ℕ}
    (hd_pos : 0 < d) (hd_eq : d = theta / (N : ℝ))
    (htheta_pos : 0 < theta) (htheta_lt : theta < alpha)
    (halpha_lt_pi : alpha < Real.pi) (hN : 0 < N)
    {i j : Fin N} (hij : i < j) :
    d ≤ ((j.1 : ℝ) - (i.1 : ℝ)) * d ∧
      ((j.1 : ℝ) - (i.1 : ℝ)) * d ≤ theta - d ∧
      Real.sin d ≤
        Real.sin (((j.1 : ℝ) - (i.1 : ℝ)) * d) := by
  have hdiff_one : (1 : ℝ) ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hs : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hij
    have hsR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hs
    linarith
  have hdiff_upper :
      (j.1 : ℝ) - (i.1 : ℝ) ≤ (N : ℝ) - 1 := by
    have hj : j.1 + 1 ≤ N := Nat.succ_le_iff.mpr j.2
    have hjR : (j.1 : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hj
    have hiR : 0 ≤ (i.1 : ℝ) := by positivity
    linarith
  have hNreal : 0 < (N : ℝ) := by positivity
  have hNd : (N : ℝ) * d = theta := by
    rw [hd_eq]
    field_simp [hNreal.ne']
  let x := ((j.1 : ℝ) - (i.1 : ℝ)) * d
  have hdx : d ≤ x := by
    have hmul := mul_le_mul_of_nonneg_right hdiff_one hd_pos.le
    simpa only [one_mul, x] using hmul
  have hxtheta_d : x ≤ theta - d := by
    have hmul := mul_le_mul_of_nonneg_right hdiff_upper hd_pos.le
    dsimp [x]
    nlinarith
  have hxtheta : x < theta := by linarith
  have hd_pi : d < Real.pi := lt_of_le_of_lt hdx
    (hxtheta.trans (htheta_lt.trans halpha_lt_pi))
  have hsind : 0 < Real.sin d :=
    Real.sin_pos_of_pos_of_lt_pi hd_pos hd_pi
  have hsin : Real.sin d ≤ Real.sin x := by
    by_cases hxhalf : x ≤ Real.pi / 2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) hxhalf hdx
    · have hxhalf' : Real.pi / 2 < x := lt_of_not_ge hxhalf
      have hreflect_half : Real.pi - x ≤ Real.pi / 2 := by linarith
      have hdreflect : d ≤ Real.pi - x := by
        linarith [hxtheta_d, htheta_lt, halpha_lt_pi]
      have hreflect :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos, hxtheta]) hreflect_half hdreflect
      simpa only [Real.sin_pi_sub] using hreflect
  exact ⟨hdx, hxtheta_d, hsin⟩



/-- Source-facing data needed by the tangent-window construction for one upper
circular cap.  The carrier-specific work is confined to the two disk-membership
fields; mesh separation, collars, payoff, and summation are shared. -/
structure UpperCapPatchSource (lam : ℝ) where
  carrier : Set PlanePoint
  cap : OneSidedCircularCap
  cap_baseY : cap.baseY = 1
  cap_side : cap.side = .upper
  upper_disk_mem_carrier :
    ∀ {p : PlanePoint},
      cap.radiusSquaredAt p ≤ cap.radius ^ 2 →
      (1 : ℝ) ≤ p.2 → p ∈ carrier
  carrier_above_mem_upper_disk :
    ∀ {p : PlanePoint}, p ∈ carrier → (1 : ℝ) < p.2 →
      cap.radiusSquaredAt p ≤ cap.radius ^ 2
  measurableSet_carrier : MeasurableSet carrier


namespace UpperCapPatch

variable {lam : ℝ} (source : UpperCapPatchSource lam)

private abbrev cap : OneSidedCircularCap :=
  source.cap

/-- The signed-arclength midpoint of cell `i`, expressed as an odd node of the
existing `2N` equal partition. -/
def midpointS (theta : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  capPartitionPoint (cap source).radius theta (2 * N) (2 * i.1 + 1)

def midpointAngle (theta : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  midpointS source theta N i / (cap source).radius

private lemma midpointAngle_eq
    {theta : ℝ} {N : ℕ} (hN : 0 < N) (i : Fin N) :
    midpointAngle source theta N i =
      -theta + (2 * (i.1 : ℝ) + 1) * (theta / (N : ℝ)) := by
  have hr := (cap source).radius_pos
  unfold midpointAngle midpointS capPartitionPoint
  push_cast
  field_simp [hr.ne', Nat.ne_of_gt hN]

private lemma midpointAngle_abs_lt
    {theta : ℝ} {N : ℕ} (htheta : 0 < theta)
    (hN : 0 < N) (i : Fin N) :
    |midpointAngle source theta N i| < theta := by
  rw [midpointAngle_eq source hN]
  have hNreal : 0 < (N : ℝ) := by positivity
  have hd : 0 < theta / (N : ℝ) := div_pos htheta hNreal
  have hi : i.1 + 1 ≤ N := Nat.succ_le_iff.mpr i.2
  have hiR : (i.1 : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hi
  rw [abs_lt]
  constructor <;> nlinarith [div_mul_cancel₀ theta hNreal.ne']

private lemma upperCircleTangentFrame_origin
    {theta : ℝ} {N : ℕ} (i : Fin N) :
    euclideanRigidMap
        (upperCircleTangentFrame (cap source).center (cap source).radius
          (midpointS source theta N i)) (0, 0) =
      (cap source).arcPoint (midpointAngle source theta N i) := by
  rw [euclideanRigidMap_upperCircleTangentFrame]
  simp [midpointAngle, cap, OneSidedCircularCap.center,
    OneSidedCircularCap.arcPoint, source.cap_side, source.cap_baseY]
  ring

private lemma upper_disk_mem_carrier
    {p : PlanePoint}
    (hdisk : (cap source).radiusSquaredAt p ≤ (cap source).radius ^ 2)
    (hy : (1 : ℝ) ≤ p.2) :
    p ∈ source.carrier :=
  source.upper_disk_mem_carrier hdisk hy

private lemma carrier_above_mem_upper_disk
    {p : PlanePoint} (hp : p ∈ source.carrier)
    (hy : (1 : ℝ) < p.2) :
    (cap source).radiusSquaredAt p ≤ (cap source).radius ^ 2 :=
  source.carrier_above_mem_upper_disk hp hy

def frame (theta : ℝ) (N : ℕ) (i : Fin N) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  upperCircleTangentFrame (cap source).center (cap source).radius
    (midpointS source theta N i)

private noncomputable def patch
    {kappa d theta : ℝ} {N : ℕ} (i : Fin N)
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (habove :
      ∀ q ∈ rigidProjectionBox (frame source theta N i)
        (-(cap source).radius * (1 - kappa) * d)
        ((cap source).radius * (1 - kappa) * d) 0
        ((cap source).radius * d ^ 2), 1 < q.2) :
    RigidProjectionPatch lam source.carrier where
  frame := frame source theta N i
  a := -(cap source).radius * (1 - kappa) * d
  b := (cap source).radius * (1 - kappa) * d
  y₀ := 0
  rho := (cap source).radius * d ^ 2
  weight := lam
  rho_pos := mul_pos (cap source).radius_pos (sq_pos_of_pos hd_pos)
  lower_collar := by
    rintro q ⟨p, hp, rfl⟩
    change p.1 ∈ Icc (-(cap source).radius * (1 - kappa) * d)
          ((cap source).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 - 2 * ((cap source).radius * d ^ 2))
          (0 - ((cap source).radius * d ^ 2)) at hp
    have hfull :
        euclideanRigidMap (frame source theta N i) p ∈
          rigidProjectionBox (frame source theta N i)
            (-(cap source).radius * (1 - kappa) * d)
            ((cap source).radius * (1 - kappa) * d) 0
            ((cap source).radius * d ^ 2) := by
      refine ⟨p, ?_, rfl⟩
      change p.1 ∈ Icc (-(cap source).radius * (1 - kappa) * d)
          ((cap source).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 - 2 * ((cap source).radius * d ^ 2))
          (0 + 2 * ((cap source).radius * d ^ 2))
      exact ⟨hp.1, ⟨hp.2.1, by
        have hrho : 0 < (cap source).radius * d ^ 2 :=
          mul_pos (cap source).radius_pos (sq_pos_of_pos hd_pos)
        linarith [hp.2.2]⟩⟩
    have hy := habove _ hfull
    have hz : p.2 ∈ Icc
        (-2 * ((cap source).radius * d ^ 2))
        (-((cap source).radius * d ^ 2)) := by
      constructor <;> linarith [hp.2.1, hp.2.2]
    have hcircle := tangentRectangle_lower_circle
      (cap source).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hp.1 hz
    have hid := upperCircleTangentFrame_radiusSquared
      (cap source).center (cap source).radius
      (midpointS source theta N i) p
    apply upper_disk_mem_carrier source _ hy.le
    change
      ((euclideanRigidMap (frame source theta N i) p).1 -
          (cap source).center.1) ^ 2 +
        ((euclideanRigidMap (frame source theta N i) p).2 -
          (cap source).center.2) ^ 2 ≤
        (cap source).radius ^ 2
    rw [show frame source theta N i =
      upperCircleTangentFrame (cap source).center (cap source).radius
        (midpointS source theta N i) by rfl]
    rw [hid]
    exact hcircle.le
  upper_collar := by
    rw [Set.disjoint_left]
    rintro q ⟨p, hp, rfl⟩ hcarrier
    change p.1 ∈ Icc (-(cap source).radius * (1 - kappa) * d)
          ((cap source).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 + ((cap source).radius * d ^ 2))
          (0 + 2 * ((cap source).radius * d ^ 2)) at hp
    have hfull :
        euclideanRigidMap (frame source theta N i) p ∈
          rigidProjectionBox (frame source theta N i)
            (-(cap source).radius * (1 - kappa) * d)
            ((cap source).radius * (1 - kappa) * d) 0
            ((cap source).radius * d ^ 2) := by
      refine ⟨p, ?_, rfl⟩
      change p.1 ∈ Icc (-(cap source).radius * (1 - kappa) * d)
          ((cap source).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 - 2 * ((cap source).radius * d ^ 2))
          (0 + 2 * ((cap source).radius * d ^ 2))
      exact ⟨hp.1, ⟨by
        have hrho : 0 < (cap source).radius * d ^ 2 :=
          mul_pos (cap source).radius_pos (sq_pos_of_pos hd_pos)
        linarith [hp.2.1], hp.2.2⟩⟩
    have hy := habove _ hfull
    have hz : (cap source).radius * d ^ 2 ≤ p.2 := by
      linarith [hp.2.1]
    have hout := tangentRectangle_upper_circle (x := p.1)
      (cap source).radius_pos hd_pos hz
    have hid := upperCircleTangentFrame_radiusSquared
      (cap source).center (cap source).radius
      (midpointS source theta N i) p
    have hin := carrier_above_mem_upper_disk source hcarrier hy
    change
      ((euclideanRigidMap (frame source theta N i) p).1 -
          (cap source).center.1) ^ 2 +
        ((euclideanRigidMap (frame source theta N i) p).2 -
          (cap source).center.2) ^ 2 ≤
        (cap source).radius ^ 2 at hin
    rw [show frame source theta N i =
      upperCircleTangentFrame (cap source).center (cap source).radius
        (midpointS source theta N i) by rfl] at hin
    rw [hid] at hin
    exact (not_lt_of_ge hin) hout
  density_lower := by
    intro q hq
    have hy := habove q hq
    have houtside : ¬ |q.2| ≤ (1 : ℝ) := by
      intro hstrip
      linarith [le_trans (le_abs_self q.2) hstrip]
    rw [StripDensity, if_neg houtside]
private lemma frame_origin_above_gap
    {theta : ℝ} {N : ℕ} (htheta_pos : 0 < theta)
    (htheta_lt : theta < source.cap.theta)
    (hN : 0 < N) (i : Fin N) :
    1 + (cap source).radius *
        (Real.cos theta - Real.cos source.cap.theta) ≤
      (euclideanRigidMap (frame source theta N i) (0, 0)).2 := by
  have hu := midpointAngle_abs_lt source htheta_pos hN i
  have halpha_pi : source.cap.theta ≤ Real.pi :=
    le_trans source.cap.theta_lt_pi.le
      (by linarith [Real.pi_pos])
  have htheta_pi : theta ≤ Real.pi :=
    htheta_lt.le.trans halpha_pi
  have hcos :
      Real.cos theta ≤ Real.cos (midpointAngle source theta N i) := by
    rw [← Real.cos_abs (midpointAngle source theta N i)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg _) htheta_pi hu.le
  have hradius : 0 < (cap source).radius := (cap source).radius_pos
  rw [show frame source theta N i =
    upperCircleTangentFrame (cap source).center (cap source).radius
      (midpointS source theta N i) by rfl,
    upperCircleTangentFrame_origin source i]
  simp only [OneSidedCircularCap.arcPoint, source.cap_side,
    source.cap_baseY]
  nlinarith

private lemma window_above
    {kappa d theta : ℝ} {N : ℕ}
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (hquad : 4 * d ^ 2 < kappa)
    (htheta_pos : 0 < theta)
    (htheta_lt : theta < source.cap.theta)
    (hN : 0 < N)
    (hclear :
      (cap source).radius * Real.sin d <
        (cap source).radius *
          (Real.cos theta - Real.cos source.cap.theta))
    (i : Fin N) :
    ∀ q ∈ rigidProjectionBox (frame source theta N i)
        (-(cap source).radius * (1 - kappa) * d)
        ((cap source).radius * (1 - kappa) * d) 0
        ((cap source).radius * d ^ 2), 1 < q.2 := by
  let q₀ : PlanePoint :=
    euclideanRigidMap (frame source theta N i) (0, 0)
  have hball := rigidProjectionBox_euclidean_subset_ball
    (cap source).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hquad
    (frame source theta N i)
  have hball' :
      planeEuclideanHomeomorph ''
          rigidProjectionBox (frame source theta N i)
            (-(cap source).radius * (1 - kappa) * d)
            ((cap source).radius * (1 - kappa) * d) 0
            ((cap source).radius * d ^ 2) ⊆
        Metric.ball (planeEuclideanHomeomorph q₀)
          ((cap source).radius * Real.sin d) := by
    have hq₀ :
        planeEuclideanHomeomorph q₀ = (frame source theta N i) 0 := by
      change planeEuclideanHomeomorph
        (euclideanRigidMap (frame source theta N i) (0, 0)) =
          (frame source theta N i) 0
      rw [planeEuclideanHomeomorph_euclideanRigidMap]
      rfl
    rw [hq₀]
    exact hball
  exact window_source_above hball'
    (frame_origin_above_gap source htheta_pos htheta_lt hN i) hclear
private lemma frame_centers_separated
    {d theta : ℝ} {N : ℕ}
    (hd_pos : 0 < d) (hd_eq : d = theta / (N : ℝ))
    (htheta_pos : 0 < theta)
    (htheta_lt : theta < source.cap.theta)
    (hN : 0 < N) {i j : Fin N} (hij : i < j) :
    2 * (cap source).radius * Real.sin d ≤
      dist ((frame source theta N i) 0) ((frame source theta N j) 0) := by
  have hr := (cap source).radius_pos
  have harg :
      ((midpointS source theta N i - midpointS source theta N j) /
          (cap source).radius) / 2 =
        -(((j.1 : ℝ) - (i.1 : ℝ)) * d) := by
    have hquot :
        (midpointS source theta N i - midpointS source theta N j) /
            (cap source).radius =
          midpointAngle source theta N i -
            midpointAngle source theta N j := by
      unfold midpointAngle
      field_simp [hr.ne']
    rw [hquot, midpointAngle_eq source hN, midpointAngle_eq source hN,
      hd_eq]
    ring
  let x := ((j.1 : ℝ) - (i.1 : ℝ)) * d
  have halpha_lt_pi : source.cap.theta < Real.pi :=
    source.cap.theta_lt_pi
  have hmesh := finiteMesh_index_bounds_and_sin hd_pos hd_eq htheta_pos
    htheta_lt halpha_lt_pi hN hij
  have hsin : Real.sin d ≤ Real.sin x := by
    simpa only [x] using hmesh.2.2
  have hsind : 0 < Real.sin d :=
    Real.sin_pos_of_pos_of_lt_pi hd_pos
      (lt_of_le_of_lt hmesh.1
        ((lt_of_le_of_lt hmesh.2.1 (by linarith)).trans
          (htheta_lt.trans halpha_lt_pi)))
  have hsinx : 0 ≤ Real.sin x := hsind.le.trans hsin
  rw [frame, frame, upperCircleTangentFrame_center_dist hr, harg,
    Real.sin_neg, abs_of_nonpos (by nlinarith : 2 * -Real.sin x ≤ 0)]
  nlinarith

private lemma patch_windows_disjoint_of_lt
    {kappa d theta : ℝ} {N : ℕ}
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (hquad : 4 * d ^ 2 < kappa)
    (hd_eq : d = theta / (N : ℝ))
    (htheta_pos : 0 < theta)
    (htheta_lt : theta < source.cap.theta)
    (hN : 0 < N)
    (habove : ∀ i : Fin N,
      ∀ q ∈ rigidProjectionBox (frame source theta N i)
        (-(cap source).radius * (1 - kappa) * d)
        ((cap source).radius * (1 - kappa) * d) 0
        ((cap source).radius * d ^ 2), 1 < q.2)
    {i j : Fin N} (hij : i < j) :
    Disjoint
      (patch source i hkappa_pos hkappa_lt hd_pos hd_lt (habove i)).window
      (patch source j hkappa_pos hkappa_lt hd_pos hd_lt (habove j)).window := by
  rw [Set.disjoint_left]
  intro q hqi hqj
  have hbi := rigidProjectionBox_euclidean_subset_ball
    (cap source).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hquad
    (frame source theta N i)
    ⟨q, hqi, rfl⟩
  have hbj := rigidProjectionBox_euclidean_subset_ball
    (cap source).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hquad
    (frame source theta N j)
    ⟨q, hqj, rfl⟩
  rw [Metric.mem_ball] at hbi hbj
  have htriangle :=
    dist_triangle ((frame source theta N i) 0)
      (planeEuclideanHomeomorph q) ((frame source theta N j) 0)
  have hsep := frame_centers_separated source hd_pos hd_eq
    htheta_pos htheta_lt hN hij
  rw [dist_comm (planeEuclideanHomeomorph q)
    ((frame source theta N i) 0)] at hbi
  linarith


private lemma exists_patch_parameters
    (hlam_gt : 1 < lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ d : ℝ,
      0 < kappa ∧ kappa < 1 / 2 ∧
      theta = (1 - kappa) * source.cap.theta ∧
      0 < theta ∧ theta < source.cap.theta ∧
      0 < N ∧ d = theta / (N : ℝ) ∧
      0 < d ∧ d < 1 / 4 ∧ 4 * d ^ 2 < kappa ∧
      (cap source).radius * Real.sin d <
        (cap source).radius *
          (Real.cos theta - Real.cos source.cap.theta) ∧
      lam * (cap source).arcLength <
        2 * lam * (cap source).radius * (1 - kappa) * theta + eta := by
  let T := lam * (cap source).arcLength
  have hlam : 0 < lam := lt_trans (by norm_num) hlam_gt
  have hT : 0 < T := mul_pos hlam (cap source).arcLength_pos
  let kappa := eta / (8 * (T + eta))
  have hden : 0 < 8 * (T + eta) := by positivity
  have hkappa_pos : 0 < kappa := div_pos heta hden
  have hkappa_lt_eighth : kappa < (1 : ℝ) / 8 := by
    dsimp [kappa]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hkappa_lt : kappa < (1 : ℝ) / 2 := by linarith
  let theta := (1 - kappa) * source.cap.theta
  have halpha := source.cap.theta_pos
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    exact mul_pos (by linarith) halpha
  have htheta_lt : theta < source.cap.theta := by
    dsimp [theta]
    have hone : 1 - kappa < 1 := by linarith
    simpa only [one_mul] using
      (mul_lt_mul_of_pos_right hone halpha)
  have halpha_pi : source.cap.theta ≤ Real.pi :=
    source.cap.theta_lt_pi.le.trans
      (by linarith [Real.pi_pos])
  have hcos :
      Real.cos source.cap.theta < Real.cos theta :=
    Real.cos_lt_cos_of_nonneg_of_le_pi htheta_pos.le halpha_pi htheta_lt
  let gap := (cap source).radius *
    (Real.cos theta - Real.cos source.cap.theta)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact mul_pos (cap source).radius_pos (sub_pos.mpr hcos)
  let eps := min ((1 : ℝ) / 4)
    (min (kappa / 4) (gap / (cap source).radius))
  have heps : 0 < eps := by
    dsimp [eps]
    exact lt_min (by norm_num) (lt_min (by positivity) (div_pos hgap
      (cap source).radius_pos))
  obtain ⟨N, hNlarge⟩ := exists_nat_gt (theta / eps)
  have hNreal_pos : 0 < (N : ℝ) :=
    (div_pos htheta_pos heps).trans hNlarge
  have hN : 0 < N := by exact_mod_cast hNreal_pos
  let d := theta / (N : ℝ)
  have hd_pos : 0 < d := div_pos htheta_pos hNreal_pos
  have hd_lt_eps : d < eps := by
    rw [div_lt_iff₀ hNreal_pos]
    simpa only [mul_comm] using (div_lt_iff₀ heps).mp hNlarge
  have hd_lt : d < (1 : ℝ) / 4 :=
    hd_lt_eps.trans_le (min_le_left _ _)
  have hd_lt_kappa : d < kappa / 4 :=
    hd_lt_eps.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hd_lt_gap : d < gap / (cap source).radius :=
    hd_lt_eps.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hquad : 4 * d ^ 2 < kappa := by
    have hdquarter : 4 * d < 1 := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hdquarter hd_pos
    nlinarith
  have hclear :
      (cap source).radius * Real.sin d < gap := by
    have hsind := Real.sin_lt hd_pos
    have hscaled :=
      mul_lt_mul_of_pos_left hsind (cap source).radius_pos
    have hdgap := (lt_div_iff₀ (cap source).radius_pos).mp hd_lt_gap
    nlinarith
  have hkappa_den : kappa * (8 * (T + eta)) = eta := by
    dsimp [kappa]
    field_simp [hden.ne']
  have htwok : 2 * T * kappa < eta := by
    have hpositive : 0 < kappa * (6 * T + 8 * eta) := by positivity
    nlinarith
  have htarget :
      T = 2 * lam * (cap source).radius *
        source.cap.theta := by
    dsimp [T]
    rw [cap_arcLength_eq_two_radius_theta]
    ring
  rw [htarget] at htwok
  have hpay :
      T < 2 * lam * (cap source).radius * (1 - kappa) * theta + eta := by
    rw [htarget]
    dsimp [theta]
    have halpha' : 0 < source.cap.theta := halpha
    have hcoef :
        0 < 2 * lam * (cap source).radius * source.cap.theta :=
      mul_pos (mul_pos (mul_pos (by norm_num) hlam)
        (cap source).radius_pos) halpha'
    have hnonneg :
        0 ≤ (2 * lam * (cap source).radius * source.cap.theta) *
          kappa ^ 2 :=
      mul_nonneg hcoef.le (sq_nonneg kappa)
    nlinarith
  refine ⟨kappa, theta, N, d, hkappa_pos, hkappa_lt, rfl,
    htheta_pos, htheta_lt, hN, rfl, hd_pos, hd_lt, hquad, ?_, ?_⟩
  · simpa [gap] using hclear
  · simpa [T] using hpay

private lemma sum_patch_payoff_eq
    {kappa d theta : ℝ} {N : ℕ}
    (hlam : 0 ≤ lam)
    (_hkappa_lt : kappa < 1)
    (hd_pos : 0 < d) (hN : 0 < N)
    (hd_eq : d = theta / (N : ℝ))
    (hkappa_pos : 0 < kappa) (hkappa_half : kappa < 1 / 2)
    (hd_quarter : d < 1 / 4)
    (habove : ∀ i : Fin N,
      ∀ q ∈ rigidProjectionBox (frame source theta N i)
        (-(cap source).radius * (1 - kappa) * d)
        ((cap source).radius * (1 - kappa) * d) 0
        ((cap source).radius * d ^ 2), 1 < q.2) :
    (∑ i : Fin N,
        (patch source i hkappa_pos hkappa_half hd_pos hd_quarter
          (habove i)).payoff) =
      ENNReal.ofReal
        (2 * lam * (cap source).radius * (1 - kappa) * theta) := by
  let value := 2 * lam * (cap source).radius * (1 - kappa) * d
  have hvalue : 0 ≤ value := by
    dsimp [value]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hlam) (cap source).radius_pos.le)
          (by linarith))
      hd_pos.le
  calc
    (∑ i : Fin N,
        (patch source i hkappa_pos hkappa_half hd_pos hd_quarter
          (habove i)).payoff) =
        ∑ _i : Fin N, ENNReal.ofReal value := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [RigidProjectionPatch.payoff, patch]
      rw [← ENNReal.ofReal_mul hlam]
      congr 1
      dsimp [value]
      ring
    _ = ENNReal.ofReal ((N : ℝ) * value) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ENNReal.ofReal_natCast]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal
        (2 * lam * (cap source).radius * (1 - kappa) * theta) := by
      congr 1
      have hNreal : (N : ℝ) ≠ 0 := by positivity
      dsimp [value]
      rw [hd_eq]
      field_simp [hNreal]

/-- Every upper-cap source admits finitely many pairwise-disjoint, complete
tangent windows on its actual upper cap. Their projected payoff misses the
weighted upper-cap arclength by at most `eta`, and the generic rigid-patch
summation theorem charges all windows to one global smooth cost and one
characteristic-function defect. -/
theorem exists_patch_family_and_bound
    (hlam_gt : 1 < lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
      RigidProjectionPatch lam source.carrier,
      0 < N ∧
      (∀ i, (P i).weight = lam) ∧
      (∀ i, (P i).window ⊆ {p : PlanePoint | 1 < p.2}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (lam * source.cap.arcLength) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost lam U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U source.carrier := by
  obtain ⟨kappa, theta, N, d, hkappa_pos, hkappa_lt, htheta,
    htheta_pos, htheta_lt, hN, hd, hd_pos, hd_lt, hquad, hclear,
    hpay⟩ := exists_patch_parameters source hlam_gt heta
  let habove : ∀ i : Fin N,
      ∀ q ∈ rigidProjectionBox (frame source theta N i)
        (-(cap source).radius * (1 - kappa) * d)
        ((cap source).radius * (1 - kappa) * d) 0
        ((cap source).radius * d ^ 2), 1 < q.2 :=
    fun i => window_above source hkappa_pos hkappa_lt hd_pos hd_lt
      hquad htheta_pos htheta_lt hN hclear i
  let P : Fin N → RigidProjectionPatch lam source.carrier :=
    fun i => patch source i hkappa_pos hkappa_lt hd_pos hd_lt (habove i)
  have hpair :
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact patch_windows_disjoint_of_lt source hkappa_pos hkappa_lt
        hd_pos hd_lt hquad hd htheta_pos htheta_lt hN habove hijlt
    · exact (patch_windows_disjoint_of_lt source hkappa_pos hkappa_lt
        hd_pos hd_lt hquad hd htheta_pos htheta_lt hN habove hjilt).symm
  have hsum :
      (∑ i : Fin N, (P i).payoff) =
        ENNReal.ofReal
          (2 * lam * (cap source).radius * (1 - kappa) * theta) := by
    exact sum_patch_payoff_eq source
      (le_trans (by norm_num) hlam_gt.le)
      (by linarith) hd_pos hN hd hkappa_pos hkappa_lt hd_lt habove
  have hE : MeasurableSet source.carrier :=
    source.measurableSet_carrier
  refine ⟨N, P, hN, ?_, ?_, hpair, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i q hq
    exact habove i q hq
  · apply ENNReal.sum_ne_top.2
    intro i _
    rw [RigidProjectionPatch.errorCoefficient]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2 (P i).rho_pos).ne'
  · rw [hsum, ← ENNReal.ofReal_add]
    · exact ENNReal.ofReal_le_ofReal hpay.le
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num)
              (le_trans (by norm_num) hlam_gt.le))
            (cap source).radius_pos.le)
          (by linarith))
        htheta_pos.le
    · exact heta.le
  · intro U hU
    have hpair' :
        Set.Pairwise (↑(Finset.univ : Finset (Fin N)))
          (Function.onFun Disjoint fun i => (P i).window) := by
      simpa using hpair
    exact RigidProjectionPatch.finset_sum_payoff_le_smoothCost_add_error
      (Finset.univ : Finset (Fin N)) P hpair' hE hU

end UpperCapPatch


namespace FourArcUpperCap

variable {lam : ℝ}

/-- The literal four-arc carrier and its upper cap, packaged for the shared
full-angle tangent-window implementation. -/
def source (profile : FourArcCandidate lam) : UpperCapPatchSource lam where
  carrier := profile.assembly.carrier
  cap := profile.assembly.upperCap
  cap_baseY := rfl
  cap_side := rfl
  upper_disk_mem_carrier := by
    intro p hdisk hy
    refine Or.inl (Or.inr ?_)
    exact ⟨hdisk, hy⟩
  carrier_above_mem_upper_disk := by
    intro p hp hy
    rcases hp with (hcore | hupper) | hlower
    · have hbound := profile.assembly.core.carrier_y_bounds hcore
      linarith [le_trans (le_abs_self p.2) hbound]
    · exact hupper.1
    · have hbelow : p.2 ≤ (-1 : ℝ) := by
        simpa [FourArcAssembly.lowerCap] using hlower.2
      linarith
  measurableSet_carrier := profile.assembly.measurableSet_carrier

/-- Every four-arc candidate admits the shared finite upper-cap patch family. -/
theorem exists_upperCap_patch_family_and_bound
    (profile : FourArcCandidate lam) (hlam_gt : 1 < lam)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
      RigidProjectionPatch lam profile.assembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = lam) ∧
      (∀ i, (P i).window ⊆ {p : PlanePoint | 1 < p.2}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (lam * profile.assembly.upperCap.arcLength) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost lam U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U profile.assembly.carrier := by
  simpa only [source] using
    UpperCapPatch.exists_patch_family_and_bound (source profile) hlam_gt heta

end FourArcUpperCap

namespace TypeThreeUpperCap

variable {lam : ℝ}

/-- The actual branch-complete type-(iii) carrier and exterior cap, packaged for
the shared full-angle tangent-window implementation. -/
def source (a : TypeThreeAssembly lam) : UpperCapPatchSource lam where
  carrier := a.carrier
  cap := a.outerCap
  cap_baseY := rfl
  cap_side := rfl
  upper_disk_mem_carrier := by
    intro p hdisk hy
    exact Or.inr ⟨hdisk, hy⟩
  carrier_above_mem_upper_disk := by
    intro p hp hy
    exact ((a.mem_carrier_iff_mem_outerCap_of_one_lt hy).mp hp).1
  measurableSet_carrier := a.measurableSet_carrier

/-- Every actual type-(iii) assembly, on the major, semicircular, or minor
branch, admits finite pairwise-disjoint complete exterior windows whose payoff
approaches its full weighted upper-cap arclength. -/
theorem exists_upperCap_patch_family_and_bound
    (a : TypeThreeAssembly lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N → RigidProjectionPatch lam a.carrier,
      0 < N ∧
      (∀ i, (P i).weight = lam) ∧
      (∀ i, (P i).window ⊆ {p : PlanePoint | 1 < p.2}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal (lam * a.outerCap.arcLength) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost lam U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U a.carrier := by
  simpa only [source] using
    UpperCapPatch.exists_patch_family_and_bound (source a) a.density_jump heta

/-- A concrete source assembly whose exterior cap is on the major branch. -/
def majorArcAssembly : TypeThreeAssembly (2 : ℝ) where
  h := 1 / 4
  density_jump := by norm_num
  h_pos := by norm_num
  h_lt_one := by norm_num

/-- The concrete `lambda = 2`, `h = 1/4` gate genuinely exercises an angle
strictly above a semicircle. -/
theorem majorArcAssembly_outerAngle_major :
    Real.pi / 2 < majorArcAssembly.outerAngle := by
  exact majorArcAssembly.outerAngle_major (by norm_num [majorArcAssembly])

/-- Compiled major-arc application of the universal source-connected patch
family. -/
theorem majorArcAssembly_exists_upperCap_patch_family_and_bound
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
      RigidProjectionPatch (2 : ℝ) majorArcAssembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = (2 : ℝ)) ∧
      (∀ i, (P i).window ⊆ {p : PlanePoint | 1 < p.2}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal ((2 : ℝ) * majorArcAssembly.outerCap.arcLength) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost (2 : ℝ) U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U majorArcAssembly.carrier :=
  exists_upperCap_patch_family_and_bound majorArcAssembly heta

end TypeThreeUpperCap

end CMVRelaxation
