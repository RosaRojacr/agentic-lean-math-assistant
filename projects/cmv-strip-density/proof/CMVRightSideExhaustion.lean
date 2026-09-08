/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVUpperCapExhaustion

/-!
# Four-arc right-side projection patches

Finite tangent rectangles on the actual right circular side of every four-arc
candidate, including the closed-curvature endpoint.  Each complete window stays
strictly inside the strip, so its density weight is exactly one.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff BigOperators

noncomputable section

namespace CMVRelaxation

/-- Tangent/outward-normal coordinates on the right side of a circle.  The
first local coordinate follows decreasing polar angle and the second points
radially outward. -/
def rightCircleTangentFrame (center : PlanePoint) (r s : ℝ) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  upperCircleTangentFrame center r (r * (Real.pi / 2) - s)

@[simp] theorem euclideanRigidMap_rightCircleTangentFrame
    (center : PlanePoint) {r s : ℝ} (hr : r ≠ 0) (p : PlanePoint) :
    euclideanRigidMap (rightCircleTangentFrame center r s) p =
      (center.1 + r * Real.cos (s / r) +
          p.1 * Real.sin (s / r) + p.2 * Real.cos (s / r),
        center.2 + r * Real.sin (s / r) -
          p.1 * Real.cos (s / r) + p.2 * Real.sin (s / r)) := by
  have harg :
      (r * (Real.pi / 2) - s) / r = Real.pi / 2 - s / r := by
    field_simp [hr]
  rw [rightCircleTangentFrame, euclideanRigidMap_upperCircleTangentFrame, harg,
    Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

lemma rightCircleTangentFrame_radiusSquared
    (center : PlanePoint) (r s : ℝ) (p : PlanePoint) :
    let q := euclideanRigidMap (rightCircleTangentFrame center r s) p
    (q.1 - center.1) ^ 2 + (q.2 - center.2) ^ 2 =
      p.1 ^ 2 + (r + p.2) ^ 2 := by
  simpa only [rightCircleTangentFrame] using
    upperCircleTangentFrame_radiusSquared center r
      (r * (Real.pi / 2) - s) p

lemma rightCircleTangentFrame_center_dist
    {r : ℝ} (hr : 0 < r) (center : PlanePoint) (s t : ℝ) :
    dist ((rightCircleTangentFrame center r s) 0)
        ((rightCircleTangentFrame center r t) 0) =
      r * |2 * Real.sin (((s - t) / r) / 2)| := by
  rw [rightCircleTangentFrame, rightCircleTangentFrame,
    upperCircleTangentFrame_center_dist hr]
  have harg :
      (((r * (Real.pi / 2) - s) - (r * (Real.pi / 2) - t)) / r) / 2 =
        -(((s - t) / r) / 2) := by
    field_simp [hr.ne']
    ring
  rw [harg, Real.sin_neg]
  have hneg : 2 * -Real.sin (((s - t) / r) / 2) =
      -(2 * Real.sin (((s - t) / r) / 2)) := by ring
  rw [hneg, abs_neg]

private lemma source_fst_dist_le_euclidean_dist (p q : PlanePoint) :
    dist p.1 q.1 ≤
      dist (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q) := by
  have h := WithLp.dist_fst_le
    (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q)
  change dist p.1 q.1 ≤ _ at h
  exact h

private lemma source_snd_dist_le_euclidean_dist (p q : PlanePoint) :
    dist p.2 q.2 ≤
      dist (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q) := by
  have h := WithLp.dist_snd_le
    (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q)
  change dist p.2 q.2 ≤ _ at h
  exact h

namespace FourArcRightSide

variable {lam : ℝ} (profile : FourArcCandidate lam)

private abbrev core : StripCore := profile.stripCore

private lemma core_radius_mul_sin_sideAngle :
    (core profile).radius * Real.sin (core profile).sideAngle = 1 := by
  rw [StripCore.radius, (core profile).sin_sideAngle]
  field_simp [(core profile).curvature_pos.ne']

/-- The signed-arclength midpoint of side cell `i`. -/
def midpointS (theta : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  capPartitionPoint (core profile).radius theta (2 * N) (2 * i.1 + 1)

def midpointAngle (theta : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  midpointS profile theta N i / (core profile).radius

private lemma midpointAngle_eq
    {theta : ℝ} {N : ℕ} (hN : 0 < N) (i : Fin N) :
    midpointAngle profile theta N i =
      -theta + (2 * (i.1 : ℝ) + 1) * (theta / (N : ℝ)) := by
  have hr := (core profile).radius_pos
  unfold midpointAngle midpointS capPartitionPoint
  push_cast
  field_simp [hr.ne', Nat.ne_of_gt hN]

private lemma midpointAngle_abs_lt
    {theta : ℝ} {N : ℕ} (htheta : 0 < theta)
    (hN : 0 < N) (i : Fin N) :
    |midpointAngle profile theta N i| < theta := by
  rw [midpointAngle_eq profile hN]
  have hNreal : 0 < (N : ℝ) := by positivity
  have hd : 0 < theta / (N : ℝ) := div_pos htheta hNreal
  have hi : i.1 + 1 ≤ N := Nat.succ_le_iff.mpr i.2
  have hiR : (i.1 : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hi
  rw [abs_lt]
  constructor <;> nlinarith [div_mul_cancel₀ theta hNreal.ne']

/-- The actual tangent frame on the right circular side. -/
def frame (theta : ℝ) (N : ℕ) (i : Fin N) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  rightCircleTangentFrame ((core profile).rightCenterX, 0)
    (core profile).radius (midpointS profile theta N i)

private lemma frame_origin
    {theta : ℝ} {N : ℕ} (i : Fin N) :
    euclideanRigidMap (frame profile theta N i) (0, 0) =
      rightCoreParam (core profile) (midpointS profile theta N i) := by
  rw [frame, euclideanRigidMap_rightCircleTangentFrame
    ((core profile).rightCenterX, 0) (core profile).radius_pos.ne']
  simp [rightCoreParam]

private lemma frame_origin_right_gap
    {theta : ℝ} {N : ℕ} (htheta_pos : 0 < theta)
    (htheta_lt : theta < (core profile).sideAngle)
    (hN : 0 < N) (i : Fin N) :
    (core profile).chord / 2 + (core profile).radius *
        (Real.cos theta - Real.cos (core profile).sideAngle) ≤
      (euclideanRigidMap (frame profile theta N i) (0, 0)).1 := by
  have hu := midpointAngle_abs_lt profile htheta_pos hN i
  have hangle_pi : (core profile).sideAngle ≤ Real.pi :=
    (core profile).sideAngle_le_pi_div_two.trans
      (by linarith [Real.pi_pos])
  have htheta_pi : theta ≤ Real.pi := htheta_lt.le.trans hangle_pi
  have hcos :
      Real.cos theta ≤ Real.cos (midpointAngle profile theta N i) := by
    rw [← Real.cos_abs (midpointAngle profile theta N i)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi
      (abs_nonneg _) htheta_pi hu.le
  rw [frame_origin profile i]
  change (core profile).chord / 2 + (core profile).radius *
      (Real.cos theta - Real.cos (core profile).sideAngle) ≤
    (core profile).rightCenterX + (core profile).radius *
      Real.cos (midpointAngle profile theta N i)
  rw [StripCore.rightCenterX]
  nlinarith [(core profile).radius_pos]

private lemma frame_origin_abs_snd_le
    {theta : ℝ} {N : ℕ} (htheta_pos : 0 < theta)
    (htheta_lt : theta < (core profile).sideAngle)
    (hN : 0 < N) (i : Fin N) :
    |(euclideanRigidMap (frame profile theta N i) (0, 0)).2| ≤
      (core profile).radius * Real.sin theta := by
  have hu := midpointAngle_abs_lt profile htheta_pos hN i
  have htheta_half : theta ≤ Real.pi / 2 :=
    htheta_lt.le.trans (core profile).sideAngle_le_pi_div_two
  have hu_pi : |midpointAngle profile theta N i| ≤ Real.pi :=
    hu.le.trans (htheta_half.trans (by linarith [Real.pi_pos]))
  have hsin :
      |Real.sin (midpointAngle profile theta N i)| ≤ Real.sin theta := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hu_pi]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by
        have habs := abs_nonneg (midpointAngle profile theta N i)
        linarith [Real.pi_pos]) htheta_half hu.le
  rw [frame_origin profile i]
  change |(core profile).radius *
      Real.sin (midpointAngle profile theta N i)| ≤ _
  rw [abs_mul, abs_of_pos (core profile).radius_pos]
  exact mul_le_mul_of_nonneg_left hsin (core profile).radius_pos.le

private lemma window_right_and_inside_strip
    {kappa d theta : ℝ} {N : ℕ}
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (hquad : 4 * d ^ 2 < kappa)
    (htheta_pos : 0 < theta)
    (htheta_lt : theta < (core profile).sideAngle)
    (hN : 0 < N)
    (hclearX :
      (core profile).radius * Real.sin d <
        (core profile).radius *
          (Real.cos theta - Real.cos (core profile).sideAngle))
    (hclearY :
      (core profile).radius * Real.sin d <
        (core profile).radius *
          (Real.sin (core profile).sideAngle - Real.sin theta))
    (i : Fin N) :
    ∀ q ∈ rigidProjectionBox (frame profile theta N i)
        (-(core profile).radius * (1 - kappa) * d)
        ((core profile).radius * (1 - kappa) * d) 0
        ((core profile).radius * d ^ 2),
      (core profile).chord / 2 < q.1 ∧ |q.2| < 1 := by
  let q₀ : PlanePoint :=
    euclideanRigidMap (frame profile theta N i) (0, 0)
  have hball := rigidProjectionBox_euclidean_subset_ball
    (core profile).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hquad
    (frame profile theta N i)
  have hball' :
      planeEuclideanHomeomorph ''
          rigidProjectionBox (frame profile theta N i)
            (-(core profile).radius * (1 - kappa) * d)
            ((core profile).radius * (1 - kappa) * d) 0
            ((core profile).radius * d ^ 2) ⊆
        Metric.ball (planeEuclideanHomeomorph q₀)
          ((core profile).radius * Real.sin d) := by
    have hq₀ :
        planeEuclideanHomeomorph q₀ = (frame profile theta N i) 0 := by
      change planeEuclideanHomeomorph
        (euclideanRigidMap (frame profile theta N i) (0, 0)) =
          (frame profile theta N i) 0
      rw [planeEuclideanHomeomorph_euclideanRigidMap]
      rfl
    rw [hq₀]
    exact hball
  intro q hq
  have hb := hball' ⟨q, hq, rfl⟩
  rw [Metric.mem_ball] at hb
  have hxcoord := source_fst_dist_le_euclidean_dist q q₀
  have hycoord := source_snd_dist_le_euclidean_dist q q₀
  rw [Real.dist_eq] at hxcoord hycoord
  have hxabs : |q.1 - q₀.1| < (core profile).radius * Real.sin d :=
    hxcoord.trans_lt hb
  have hyabs : |q.2 - q₀.2| < (core profile).radius * Real.sin d :=
    hycoord.trans_lt hb
  have hxgap := frame_origin_right_gap profile htheta_pos htheta_lt hN i
  have hxleft : q₀.1 - q.1 ≤ |q.1 - q₀.1| := by
    calc
      q₀.1 - q.1 ≤ |q₀.1 - q.1| := le_abs_self _
      _ = |q.1 - q₀.1| := abs_sub_comm _ _
  have hx : (core profile).chord / 2 < q.1 := by
    dsimp [q₀] at hxgap hxleft
    linarith
  have hq₀y := frame_origin_abs_snd_le profile
    htheta_pos htheta_lt hN i
  have hytriangle : |q.2| ≤ |q.2 - q₀.2| + |q₀.2| := by
    calc
      |q.2| = |(q.2 - q₀.2) + q₀.2| := by ring_nf
      _ ≤ |q.2 - q₀.2| + |q₀.2| := abs_add_le _ _
  have hytotal :
      (core profile).radius * Real.sin d +
          (core profile).radius * Real.sin theta < 1 := by
    rw [← core_radius_mul_sin_sideAngle profile]
    linarith
  constructor
  · exact hx
  · exact hytriangle.trans_lt (by linarith)

private noncomputable def patch
    {kappa d theta : ℝ} {N : ℕ} (i : Fin N)
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (hloc :
      ∀ q ∈ rigidProjectionBox (frame profile theta N i)
        (-(core profile).radius * (1 - kappa) * d)
        ((core profile).radius * (1 - kappa) * d) 0
        ((core profile).radius * d ^ 2),
        (core profile).chord / 2 < q.1 ∧ |q.2| < 1) :
    RigidProjectionPatch lam profile.assembly.carrier where
  frame := frame profile theta N i
  a := -(core profile).radius * (1 - kappa) * d
  b := (core profile).radius * (1 - kappa) * d
  y₀ := 0
  rho := (core profile).radius * d ^ 2
  weight := 1
  rho_pos := mul_pos (core profile).radius_pos (sq_pos_of_pos hd_pos)
  lower_collar := by
    rintro q ⟨p, hp, rfl⟩
    change p.1 ∈ Icc (-(core profile).radius * (1 - kappa) * d)
          ((core profile).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 - 2 * ((core profile).radius * d ^ 2))
          (0 - ((core profile).radius * d ^ 2)) at hp
    have hfull :
        euclideanRigidMap (frame profile theta N i) p ∈
          rigidProjectionBox (frame profile theta N i)
            (-(core profile).radius * (1 - kappa) * d)
            ((core profile).radius * (1 - kappa) * d) 0
            ((core profile).radius * d ^ 2) := by
      refine ⟨p, ?_, rfl⟩
      change p.1 ∈ Icc (-(core profile).radius * (1 - kappa) * d)
          ((core profile).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 - 2 * ((core profile).radius * d ^ 2))
          (0 + 2 * ((core profile).radius * d ^ 2))
      exact ⟨hp.1, ⟨hp.2.1, by
        have hrho : 0 < (core profile).radius * d ^ 2 :=
          mul_pos (core profile).radius_pos (sq_pos_of_pos hd_pos)
        linarith [hp.2.2]⟩⟩
    have hposition := hloc _ hfull
    have hz : p.2 ∈ Icc
        (-2 * ((core profile).radius * d ^ 2))
        (-((core profile).radius * d ^ 2)) := by
      constructor <;> linarith [hp.2.1, hp.2.2]
    have hcircle := tangentRectangle_lower_circle
      (core profile).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hp.1 hz
    have hid := rightCircleTangentFrame_radiusSquared
      ((core profile).rightCenterX, 0) (core profile).radius
      (midpointS profile theta N i) p
    refine Or.inl (Or.inl (Or.inr ?_))
    change
      ((euclideanRigidMap (frame profile theta N i) p).1 -
          (core profile).rightCenterX) ^ 2 +
        (euclideanRigidMap (frame profile theta N i) p).2 ^ 2 ≤
          (core profile).radius ^ 2 ∧
      (core profile).chord / 2 ≤
        (euclideanRigidMap (frame profile theta N i) p).1 ∧
      |(euclideanRigidMap (frame profile theta N i) p).2| ≤ 1
    refine ⟨?_, ?_, hposition.2.le⟩
    · have hinside := hid.trans_le hcircle.le
      simpa only [frame, Prod.fst, Prod.snd, sub_zero] using hinside
    · exact hposition.1.le
  upper_collar := by
    rw [Set.disjoint_left]
    rintro q ⟨p, hp, rfl⟩ hcarrier
    change p.1 ∈ Icc (-(core profile).radius * (1 - kappa) * d)
          ((core profile).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 + ((core profile).radius * d ^ 2))
          (0 + 2 * ((core profile).radius * d ^ 2)) at hp
    have hfull :
        euclideanRigidMap (frame profile theta N i) p ∈
          rigidProjectionBox (frame profile theta N i)
            (-(core profile).radius * (1 - kappa) * d)
            ((core profile).radius * (1 - kappa) * d) 0
            ((core profile).radius * d ^ 2) := by
      refine ⟨p, ?_, rfl⟩
      change p.1 ∈ Icc (-(core profile).radius * (1 - kappa) * d)
          ((core profile).radius * (1 - kappa) * d) ∧
        p.2 ∈ Icc
          (0 - 2 * ((core profile).radius * d ^ 2))
          (0 + 2 * ((core profile).radius * d ^ 2))
      exact ⟨hp.1, ⟨by
        have hrho : 0 < (core profile).radius * d ^ 2 :=
          mul_pos (core profile).radius_pos (sq_pos_of_pos hd_pos)
        linarith [hp.2.1], hp.2.2⟩⟩
    have hposition := hloc _ hfull
    have hz : (core profile).radius * d ^ 2 ≤ p.2 := by
      linarith [hp.2.1]
    have hout := tangentRectangle_upper_circle
      (x := p.1) (core profile).radius_pos hd_pos hz
    have hin :
        ((euclideanRigidMap (frame profile theta N i) p).1 -
            (core profile).rightCenterX) ^ 2 +
          (euclideanRigidMap (frame profile theta N i) p).2 ^ 2 ≤
            (core profile).radius ^ 2 := by
      rcases hcarrier with (hcore | hupper) | hlower
      · rcases hcore with (hrect | hleft) | hright
        · change -((core profile).chord) / 2 ≤ _ ∧
              _ ≤ (core profile).chord / 2 ∧ _ at hrect
          linarith [hposition.1]
        · change _ ∧ _ ≤ -((core profile).chord) / 2 ∧ _ at hleft
          have hleftx :
              (euclideanRigidMap (frame profile theta N i) p).1 ≤
                -((core profile).chord / 2) := by
            linarith [hleft.2.1]
          have houter_pos : 0 < (core profile).chord / 2 := by
            linarith [(core profile).chord_pos]
          linarith [hposition.1]
        · exact hright.1
      · have hy : (1 : ℝ) ≤
            (euclideanRigidMap (frame profile theta N i) p).2 := by
          simpa only [FourArcAssembly.upperCap, OneSidedCircularCap.carrier,
            CapSide.upper, and_self] using hupper.2
        have habs := abs_lt.mp hposition.2
        linarith
      · have hy :
            (euclideanRigidMap (frame profile theta N i) p).2 ≤ (-1 : ℝ) := by
          simpa only [FourArcAssembly.lowerCap, OneSidedCircularCap.carrier,
            CapSide.lower, and_self] using hlower.2
        have habs := abs_lt.mp hposition.2
        linarith
    have hid := rightCircleTangentFrame_radiusSquared
      ((core profile).rightCenterX, 0) (core profile).radius
      (midpointS profile theta N i) p
    change
      ((euclideanRigidMap
          (rightCircleTangentFrame ((core profile).rightCenterX, 0)
            (core profile).radius (midpointS profile theta N i)) p).1 -
          (core profile).rightCenterX) ^ 2 +
        (euclideanRigidMap
          (rightCircleTangentFrame ((core profile).rightCenterX, 0)
            (core profile).radius (midpointS profile theta N i)) p).2 ^ 2 ≤
          (core profile).radius ^ 2 at hin
    have hin₀ :
        ((euclideanRigidMap
            (rightCircleTangentFrame ((core profile).rightCenterX, 0)
              (core profile).radius (midpointS profile theta N i)) p).1 -
            (((core profile).rightCenterX, 0) : PlanePoint).1) ^ 2 +
          ((euclideanRigidMap
            (rightCircleTangentFrame ((core profile).rightCenterX, 0)
              (core profile).radius (midpointS profile theta N i)) p).2 -
            (((core profile).rightCenterX, 0) : PlanePoint).2) ^ 2 ≤
          (core profile).radius ^ 2 := by
      simpa only [Prod.fst, Prod.snd, sub_zero] using hin
    have hin' : p.1 ^ 2 + ((core profile).radius + p.2) ^ 2 ≤
        (core profile).radius ^ 2 :=
      hid.symm.trans_le hin₀
    exact (not_lt_of_ge hin') hout
  density_lower := by
    intro q hq
    rw [StripDensity, if_pos (hloc q hq).2.le]

private lemma frame_centers_separated
    {d theta : ℝ} {N : ℕ}
    (hd_pos : 0 < d) (hd_eq : d = theta / (N : ℝ))
    (htheta_pos : 0 < theta)
    (htheta_lt : theta < (core profile).sideAngle)
    (hN : 0 < N) {i j : Fin N} (hij : i < j) :
    2 * (core profile).radius * Real.sin d ≤
      dist ((frame profile theta N i) 0) ((frame profile theta N j) 0) := by
  have hr := (core profile).radius_pos
  have harg :
      ((midpointS profile theta N i - midpointS profile theta N j) /
          (core profile).radius) / 2 =
        -(((j.1 : ℝ) - (i.1 : ℝ)) * d) := by
    have hquot :
        (midpointS profile theta N i - midpointS profile theta N j) /
            (core profile).radius =
          midpointAngle profile theta N i -
            midpointAngle profile theta N j := by
      unfold midpointAngle
      field_simp [hr.ne']
    rw [hquot, midpointAngle_eq profile hN, midpointAngle_eq profile hN,
      hd_eq]
    ring
  have hdiff_one : (1 : ℝ) ≤ (j.1 : ℝ) - (i.1 : ℝ) := by
    have hs : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hij
    have hsR : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by exact_mod_cast hs
    linarith
  have hdiff_lt : (j.1 : ℝ) - (i.1 : ℝ) < (N : ℝ) := by
    have hjR : (j.1 : ℝ) < (N : ℝ) := by exact_mod_cast j.2
    have hiR : 0 ≤ (i.1 : ℝ) := by positivity
    linarith
  have hNreal : 0 < (N : ℝ) := by positivity
  have hNd : (N : ℝ) * d = theta := by
    rw [hd_eq]
    field_simp [hNreal.ne']
  let x := ((j.1 : ℝ) - (i.1 : ℝ)) * d
  have hdx : d ≤ x := by
    dsimp [x]
    have hfactor : 0 ≤ ((j.1 : ℝ) - (i.1 : ℝ) - 1) * d :=
      mul_nonneg (by linarith) hd_pos.le
    nlinarith
  have hxtheta : x < theta := by
    dsimp [x]
    have hmul := mul_lt_mul_of_pos_right hdiff_lt hd_pos
    nlinarith
  have hxhalf : x ≤ Real.pi / 2 :=
    hxtheta.le.trans (htheta_lt.le.trans
      (core profile).sideAngle_le_pi_div_two)
  have hsind : 0 < Real.sin d :=
    Real.sin_pos_of_pos_of_lt_pi hd_pos
      (lt_of_le_of_lt hdx (hxtheta.trans
        (htheta_lt.trans (core profile).sideAngle_lt_pi)))
  have hsin : Real.sin d ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hxhalf hdx
  have hsinx : 0 ≤ Real.sin x := hsind.le.trans hsin
  rw [frame, frame, rightCircleTangentFrame_center_dist hr, harg,
    Real.sin_neg, abs_of_nonpos (by nlinarith : 2 * -Real.sin x ≤ 0)]
  nlinarith

private lemma patch_windows_disjoint_of_lt
    {kappa d theta : ℝ} {N : ℕ}
    (hkappa_pos : 0 < kappa) (hkappa_lt : kappa < 1 / 2)
    (hd_pos : 0 < d) (hd_lt : d < 1 / 4)
    (hquad : 4 * d ^ 2 < kappa)
    (hd_eq : d = theta / (N : ℝ))
    (htheta_pos : 0 < theta)
    (htheta_lt : theta < (core profile).sideAngle)
    (hN : 0 < N)
    (hloc : ∀ i : Fin N,
      ∀ q ∈ rigidProjectionBox (frame profile theta N i)
        (-(core profile).radius * (1 - kappa) * d)
        ((core profile).radius * (1 - kappa) * d) 0
        ((core profile).radius * d ^ 2),
        (core profile).chord / 2 < q.1 ∧ |q.2| < 1)
    {i j : Fin N} (hij : i < j) :
    Disjoint
      (patch profile i hkappa_pos hkappa_lt hd_pos hd_lt (hloc i)).window
      (patch profile j hkappa_pos hkappa_lt hd_pos hd_lt (hloc j)).window := by
  rw [Set.disjoint_left]
  intro q hqi hqj
  have hbi := rigidProjectionBox_euclidean_subset_ball
    (core profile).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hquad
    (frame profile theta N i) ⟨q, hqi, rfl⟩
  have hbj := rigidProjectionBox_euclidean_subset_ball
    (core profile).radius_pos hkappa_pos hkappa_lt hd_pos hd_lt hquad
    (frame profile theta N j) ⟨q, hqj, rfl⟩
  rw [Metric.mem_ball] at hbi hbj
  have htriangle :=
    dist_triangle ((frame profile theta N i) 0)
      (planeEuclideanHomeomorph q) ((frame profile theta N j) 0)
  have hsep := frame_centers_separated profile hd_pos hd_eq
    htheta_pos htheta_lt hN hij
  rw [dist_comm (planeEuclideanHomeomorph q)
    ((frame profile theta N i) 0)] at hbi
  linarith

private lemma exists_patch_parameters
    {eta : ℝ} (heta : 0 < eta) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ d : ℝ,
      0 < kappa ∧ kappa < 1 / 2 ∧
      theta = (1 - kappa) * (core profile).sideAngle ∧
      0 < theta ∧ theta < (core profile).sideAngle ∧
      0 < N ∧ d = theta / (N : ℝ) ∧
      0 < d ∧ d < 1 / 4 ∧ 4 * d ^ 2 < kappa ∧
      (core profile).radius * Real.sin d <
        (core profile).radius *
          (Real.cos theta - Real.cos (core profile).sideAngle) ∧
      (core profile).radius * Real.sin d <
        (core profile).radius *
          (Real.sin (core profile).sideAngle - Real.sin theta) ∧
      2 * (core profile).radius * (core profile).sideAngle <
        2 * (core profile).radius * (1 - kappa) * theta + eta := by
  let T := 2 * (core profile).radius * (core profile).sideAngle
  have hT : 0 < T := by
    dsimp [T]
    exact mul_pos
      (mul_pos (by norm_num) (core profile).radius_pos)
      (core profile).sideAngle_pos
  let kappa := eta / (8 * (T + eta))
  have hden : 0 < 8 * (T + eta) := by positivity
  have hkappa_pos : 0 < kappa := div_pos heta hden
  have hkappa_lt_eighth : kappa < (1 : ℝ) / 8 := by
    dsimp [kappa]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hkappa_lt : kappa < (1 : ℝ) / 2 := by linarith
  let theta := (1 - kappa) * (core profile).sideAngle
  have hbeta := (core profile).sideAngle_pos
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    exact mul_pos (by linarith) hbeta
  have htheta_lt : theta < (core profile).sideAngle := by
    dsimp [theta]
    nlinarith
  have hbeta_pi : (core profile).sideAngle ≤ Real.pi :=
    (core profile).sideAngle_le_pi_div_two.trans
      (by linarith [Real.pi_pos])
  have hcos :
      Real.cos (core profile).sideAngle < Real.cos theta :=
    Real.cos_lt_cos_of_nonneg_of_le_pi htheta_pos.le hbeta_pi htheta_lt
  have hsin :
      Real.sin theta < Real.sin (core profile).sideAngle := by
    exact Real.strictMonoOn_sin
      ⟨by linarith [Real.pi_pos], htheta_lt.le.trans
        (core profile).sideAngle_le_pi_div_two⟩
      ⟨by linarith [Real.pi_pos], (core profile).sideAngle_le_pi_div_two⟩
      htheta_lt
  let gapX := (core profile).radius *
    (Real.cos theta - Real.cos (core profile).sideAngle)
  let gapY := (core profile).radius *
    (Real.sin (core profile).sideAngle - Real.sin theta)
  have hgapX : 0 < gapX := by
    dsimp [gapX]
    exact mul_pos (core profile).radius_pos (sub_pos.mpr hcos)
  have hgapY : 0 < gapY := by
    dsimp [gapY]
    exact mul_pos (core profile).radius_pos (sub_pos.mpr hsin)
  let eps := min ((1 : ℝ) / 4)
    (min (kappa / 4)
      (min (gapX / (core profile).radius)
        (gapY / (core profile).radius)))
  have heps : 0 < eps := by
    dsimp [eps]
    exact lt_min (by norm_num)
      (lt_min (by positivity)
        (lt_min (div_pos hgapX (core profile).radius_pos)
          (div_pos hgapY (core profile).radius_pos)))
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
  have hd_lt_gapX : d < gapX / (core profile).radius :=
    hd_lt_eps.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hd_lt_gapY : d < gapY / (core profile).radius :=
    hd_lt_eps.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hquad : 4 * d ^ 2 < kappa := by
    have hdquarter : 4 * d < 1 := by nlinarith
    have hmul := mul_lt_mul_of_pos_right hdquarter hd_pos
    nlinarith
  have hclearX : (core profile).radius * Real.sin d < gapX := by
    have hsind := Real.sin_lt hd_pos
    have hscaled := mul_lt_mul_of_pos_left hsind (core profile).radius_pos
    have hdgap := (lt_div_iff₀ (core profile).radius_pos).mp hd_lt_gapX
    nlinarith
  have hclearY : (core profile).radius * Real.sin d < gapY := by
    have hsind := Real.sin_lt hd_pos
    have hscaled := mul_lt_mul_of_pos_left hsind (core profile).radius_pos
    have hdgap := (lt_div_iff₀ (core profile).radius_pos).mp hd_lt_gapY
    nlinarith
  have hkappa_den : kappa * (8 * (T + eta)) = eta := by
    dsimp [kappa]
    field_simp [hden.ne']
  have htwok : 2 * T * kappa < eta := by
    have hpositive : 0 < kappa * (6 * T + 8 * eta) := by positivity
    nlinarith
  have hpay :
      T < 2 * (core profile).radius * (1 - kappa) * theta + eta := by
    dsimp [T, theta] at htwok ⊢
    have hnonneg :
        0 ≤ (2 * (core profile).radius * (core profile).sideAngle) *
          kappa ^ 2 := by positivity
    nlinarith
  refine ⟨kappa, theta, N, d, hkappa_pos, hkappa_lt, rfl,
    htheta_pos, htheta_lt, hN, rfl, hd_pos, hd_lt, hquad, ?_, ?_, ?_⟩
  · simpa [gapX] using hclearX
  · simpa [gapY] using hclearY
  · simpa [T] using hpay

private lemma sum_patch_payoff_eq
    {kappa d theta : ℝ} {N : ℕ}
    (_hkappa_lt : kappa < 1)
    (hd_pos : 0 < d) (hN : 0 < N)
    (hd_eq : d = theta / (N : ℝ))
    (hkappa_pos : 0 < kappa) (hkappa_half : kappa < 1 / 2)
    (hd_quarter : d < 1 / 4)
    (hloc : ∀ i : Fin N,
      ∀ q ∈ rigidProjectionBox (frame profile theta N i)
        (-(core profile).radius * (1 - kappa) * d)
        ((core profile).radius * (1 - kappa) * d) 0
        ((core profile).radius * d ^ 2),
        (core profile).chord / 2 < q.1 ∧ |q.2| < 1) :
    (∑ i : Fin N,
        (patch profile i hkappa_pos hkappa_half hd_pos hd_quarter
          (hloc i)).payoff) =
      ENNReal.ofReal
        (2 * (core profile).radius * (1 - kappa) * theta) := by
  let value := 2 * (core profile).radius * (1 - kappa) * d
  have hvalue : 0 ≤ value := by
    dsimp [value]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (core profile).radius_pos.le)
        (by linarith))
      hd_pos.le
  calc
    (∑ i : Fin N,
        (patch profile i hkappa_pos hkappa_half hd_pos hd_quarter
          (hloc i)).payoff) =
        ∑ _i : Fin N, ENNReal.ofReal value := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [RigidProjectionPatch.payoff, patch, ENNReal.ofReal_one,
        one_mul]
      congr 1
      dsimp [value]
      ring
    _ = ENNReal.ofReal ((N : ℝ) * value) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ENNReal.ofReal
        (2 * (core profile).radius * (1 - kappa) * theta) := by
      congr 1
      have hNreal : (N : ℝ) ≠ 0 := by positivity
      dsimp [value]
      rw [hd_eq]
      field_simp [hNreal]

/-- Every four-arc candidate admits finitely many pairwise-disjoint complete
windows on its actual right circular side.  The windows stay in
`x > capChord / 2` and `|y| < 1`, hence have exact density weight one.  Their
payoff approaches the complete right-side arclength, and the generic summation
theorem charges only one global smooth cost. -/
theorem exists_rightSide_patch_family_and_bound
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∃ P : Fin N →
      RigidProjectionPatch lam profile.assembly.carrier,
      0 < N ∧
      (∀ i, (P i).weight = 1) ∧
      (∀ i, (P i).window ⊆
        {p : PlanePoint | profile.capChord / 2 < p.1 ∧ |p.2| < 1}) ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) ∧
      (∑ i, (P i).errorCoefficient) ≠ ⊤ ∧
      ENNReal.ofReal
          (coreArcEnd profile.stripCore -
            coreArcStart profile.stripCore) ≤
        (∑ i, (P i).payoff) + ENNReal.ofReal eta ∧
      ∀ {U : Set PlanePoint}, IsOpen U →
        (∑ i, (P i).payoff) ≤
          smoothCost lam U +
            (∑ i, (P i).errorCoefficient) *
              characteristicDistance U profile.assembly.carrier := by
  obtain ⟨kappa, theta, N, d, hkappa_pos, hkappa_lt, htheta,
    htheta_pos, htheta_lt, hN, hd, hd_pos, hd_lt, hquad, hclearX,
    hclearY, hpay⟩ := exists_patch_parameters profile heta
  let hloc : ∀ i : Fin N,
      ∀ q ∈ rigidProjectionBox (frame profile theta N i)
        (-(core profile).radius * (1 - kappa) * d)
        ((core profile).radius * (1 - kappa) * d) 0
        ((core profile).radius * d ^ 2),
        (core profile).chord / 2 < q.1 ∧ |q.2| < 1 :=
    fun i => window_right_and_inside_strip profile hkappa_pos hkappa_lt
      hd_pos hd_lt hquad htheta_pos htheta_lt hN hclearX hclearY i
  let P : Fin N → RigidProjectionPatch lam profile.assembly.carrier :=
    fun i => patch profile i hkappa_pos hkappa_lt hd_pos hd_lt (hloc i)
  have hpair :
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (P i).window) := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact patch_windows_disjoint_of_lt profile hkappa_pos hkappa_lt
        hd_pos hd_lt hquad hd htheta_pos htheta_lt hN hloc hijlt
    · exact (patch_windows_disjoint_of_lt profile hkappa_pos hkappa_lt
        hd_pos hd_lt hquad hd htheta_pos htheta_lt hN hloc hjilt).symm
  have hsum :
      (∑ i : Fin N, (P i).payoff) =
        ENNReal.ofReal
          (2 * (core profile).radius * (1 - kappa) * theta) := by
    exact sum_patch_payoff_eq profile (by linarith) hd_pos hN hd
      hkappa_pos hkappa_lt hd_lt hloc
  have hlength :
      coreArcEnd (core profile) - coreArcStart (core profile) =
        2 * (core profile).radius * (core profile).sideAngle := by
    simp only [coreArcEnd, coreArcStart]
    ring
  have hE : MeasurableSet profile.assembly.carrier :=
    profile.assembly.measurableSet_carrier
  refine ⟨N, P, hN, ?_, ?_, hpair, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i q hq
    change profile.capChord / 2 < q.1 ∧ |q.2| < 1
    simpa only [core, FourArcCandidate.stripCore] using hloc i q hq
  · apply ENNReal.sum_ne_top.2
    intro i _
    rw [RigidProjectionPatch.errorCoefficient]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2 (P i).rho_pos).ne'
  · rw [show profile.stripCore = core profile by rfl,
      hlength, hsum, ← ENNReal.ofReal_add]
    · exact ENNReal.ofReal_le_ofReal hpay.le
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (core profile).radius_pos.le)
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

end FourArcRightSide

end CMVRelaxation
