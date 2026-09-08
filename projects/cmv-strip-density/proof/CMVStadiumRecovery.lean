/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTypeThreeLowerRecovery

/-!
# Strip-contained stadium recovery

The positive-width target is the literal curvature-one `StripCore`.  The
zero-width endpoint is kept separately as a closed disk, with the existing open
unit disk as its smooth representative.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVRelaxation.StadiumRecovery

/-- The literal positive-width curvature-one strip core. -/
def core (W : ℝ) (hW : 0 < W) : StripCore where
  chord := W
  curvature := 1
  chord_pos := hW
  curvature_pos := zero_lt_one
  curvature_le_one := le_rfl

/-- The target carrier, without replacing its complete topological frontier by
an independently chosen boundary measure. -/
def carrier (W : ℝ) (hW : 0 < W) : Set PlanePoint :=
  (core W hW).carrier

@[simp] theorem core_sideAngle (W : ℝ) (hW : 0 < W) :
    (core W hW).sideAngle = Real.pi / 2 := by
  simp [core, StripCore.sideAngle, Real.arcsin_one]

@[simp] theorem core_euclideanArea (W : ℝ) (hW : 0 < W) :
    (core W hW).euclideanArea = 2 * W + Real.pi := by
  rw [StripCore.euclideanArea, core_sideAngle, area,
    Real.sin_pi_div_two, Real.cos_pi_div_two]
  simp [core]
  ring

@[simp] theorem core_boundaryArcLength (W : ℝ) (hW : 0 < W) :
    (core W hW).boundaryArcLength = 2 * Real.pi := by
  rw [StripCore.boundaryArcLength, core_sideAngle, ell,
    Real.sin_pi_div_two]
  ring
/-- The literal stadium has weighted area `2W + pi`, independently of the
exterior density, because it remains in the closed strip. -/
theorem weightedArea_carrier (lam W : ℝ) (hW : 0 < W) :
    WeightedArea lam (carrier W hW) = 2 * W + Real.pi := by
  rw [carrier, (core W hW).weightedArea_formula]
  exact core_euclideanArea W hW

/-- Complete-frontier accounting.  The `2W` term is the pair of horizontal
segments and is not part of `StripCore.boundaryArcLength`. -/
theorem frontierWeightedPerimeter_carrier (lam W : ℝ) (hW : 0 < W) :
    WeightedPerimeter lam (FrontierMeasure (carrier W hW)) =
      2 * W + 2 * Real.pi := by
  rw [carrier, stripCore_frontier_weightedPerimeter_eq,
    core_boundaryArcLength]
  simp [core]
  ring

/-- The geometric endpoint used for lower-bound patches. -/
def closedUnitDisk : Set PlanePoint :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1}

/-- Open and closed unit-disk representatives differ only on their circular
level set, which has planar measure zero. -/
theorem closedUnitDisk_ae_eq_unitDisk :
    closedUnitDisk =ᵐ[volume] unitDisk := by
  have hboundary :
      volume {p : PlanePoint | p.1 ^ 2 = 1 - p.2 ^ 2} = 0 :=
    CMVRelaxation.FrozenCanonicalCap.volume_squaredWidthBoundary
      (fun y : ℝ => 1 - y ^ 2) (by fun_prop)
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null
      (t := {p : PlanePoint | p.1 ^ 2 = 1 - p.2 ^ 2})
    · rintro p ⟨hpClosed, hpNotOpen⟩
      change p.1 ^ 2 + p.2 ^ 2 ≤ 1 at hpClosed
      change ¬p.1 ^ 2 + p.2 ^ 2 < 1 at hpNotOpen
      change p.1 ^ 2 = 1 - p.2 ^ 2
      linarith
    · exact hboundary
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpOpen, hpNotClosed⟩
      change p.1 ^ 2 + p.2 ^ 2 < 1 at hpOpen
      exact (hpNotClosed hpOpen.le).elim
    · exact measure_empty

/-- Euclidean realization of the closed endpoint. -/
theorem closedUnitDisk_euclidean_image :
    planeEuclideanHomeomorph '' closedUnitDisk =
      Metric.closedBall (0 : EuclideanPlane) 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right,
      ← sq_le_sq₀ (norm_nonneg (planeEuclideanHomeomorph p)) zero_le_one]
    have hsq : ‖WithLp.toLp 2 p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      simpa [sq_abs] using WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 p)
    change ‖WithLp.toLp 2 p‖ ^ 2 ≤ 1 ^ 2
    norm_num only [one_pow]
    rw [hsq]
    exact hp
  · intro z hz
    obtain ⟨p, rfl⟩ := planeEuclideanHomeomorph.surjective z
    refine ⟨p, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    have hsq : ‖WithLp.toLp 2 p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      simpa [sq_abs] using WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 p)
    change ‖WithLp.toLp 2 p‖ ≤ 1 at hz
    change p.1 ^ 2 + p.2 ^ 2 ≤ 1
    rw [← hsq]
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg (WithLp.toLp 2 p)) zero_le_one).2 hz
    simpa only [one_pow] using hsquare

/-- The open approximation and closed geometric endpoint have exactly the same
complete Euclidean frontier. -/
theorem frontier_unitDisk_euclidean_eq_closed :
    frontier (planeEuclideanHomeomorph '' unitDisk) =
      frontier (planeEuclideanHomeomorph '' closedUnitDisk) := by
  rw [unitDisk_euclidean_image, closedUnitDisk_euclidean_image,
    frontier_ball (0 : EuclideanPlane) one_ne_zero,
    frontier_closedBall (0 : EuclideanPlane) one_ne_zero]

/-- The existing open-disk smooth approximant has exactly the closed target's
complete-frontier cost. -/
theorem smoothCost_unitDisk_eq_closed (lam : ℝ) :
    smoothCost lam unitDisk = smoothCost lam closedUnitDisk := by
  rw [CMVRelaxation.FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral,
    CMVRelaxation.FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral,
    frontier_unitDisk_euclidean_eq_closed]

/-- The existing constant open-disk sequence converges to the literal closed
disk target through the checked almost-everywhere bridge. -/
theorem unitDiskConstantSequence_converges_closed :
    unitDiskConstantSequence.ConvergesTo closedUnitDisk :=
  (unitDiskConstantSequence.convergesTo_congr_ae
    closedUnitDisk_ae_eq_unitDisk).2 unitDiskConstantSequence_converges

/-- Relaxed endpoint semantics is independent of choosing the open or closed
disk representative. -/
theorem relaxedPerimeter_closedUnitDisk_eq (lam : ℝ) :
    relaxedPerimeter lam closedUnitDisk = relaxedPerimeter lam unitDisk :=
  relaxedPerimeter_congr_ae lam closedUnitDisk_ae_eq_unitDisk

/-- The retained smooth cutoff, renamed for the stadium's outward horizontal
coordinate. -/
def cutoff : ℝ → ℝ :=
  CMVRelaxation.TypeThreeRecovery.lowerContactWeight

lemma contDiff_cutoff : ContDiff ℝ ∞ cutoff :=
  CMVRelaxation.TypeThreeRecovery.contDiff_lowerContactWeight

lemma cutoff_mem_Icc (t : ℝ) : cutoff t ∈ Icc (0 : ℝ) 1 :=
  CMVRelaxation.TypeThreeRecovery.lowerContactWeight_mem_Icc t

lemma cutoff_eq_zero {t : ℝ} (ht : t ≤ 1 / 3) : cutoff t = 0 :=
  CMVRelaxation.TypeThreeRecovery.lowerContactWeight_eq_zero ht

lemma cutoff_eq_one {t : ℝ} (ht : 2 / 3 ≤ t) : cutoff t = 1 :=
  CMVRelaxation.TypeThreeRecovery.lowerContactWeight_eq_one ht

/-- Smooth squared vertical half-height.  The two cutoff terms face away from
opposite ends of the central segment. -/
def q (W epsilon x : ℝ) : ℝ :=
  1 - cutoff ((x - W / 2) / epsilon) * (x - W / 2) ^ 2 -
    cutoff ((-x - W / 2) / epsilon) * (-x - W / 2) ^ 2

lemma contDiff_q (W epsilon : ℝ) : ContDiff ℝ ∞ (q W epsilon) := by
  have hright : ContDiff ℝ ∞
      (fun x : ℝ => cutoff ((x - W / 2) / epsilon)) :=
    contDiff_cutoff.comp ((contDiff_id.sub contDiff_const).div_const epsilon)
  have hleft : ContDiff ℝ ∞
      (fun x : ℝ => cutoff ((-x - W / 2) / epsilon)) :=
    contDiff_cutoff.comp
      ((contDiff_id.neg.sub contDiff_const).div_const epsilon)
  unfold q
  exact (contDiff_const.sub
    (hright.mul ((contDiff_id.sub contDiff_const).pow 2))).sub
      (hleft.mul ((contDiff_id.neg.sub contDiff_const).pow 2))

lemma q_le_one (W epsilon x : ℝ) : q W epsilon x ≤ 1 := by
  have hr := (cutoff_mem_Icc ((x - W / 2) / epsilon)).1
  have hl := (cutoff_mem_Icc ((-x - W / 2) / epsilon)).1
  unfold q
  nlinarith [sq_nonneg (x - W / 2), sq_nonneg (-x - W / 2)]

/-- The actual open recovery domain uses squared vertical height; no coordinate
swap is used in any density claim. -/
def domain (W epsilon : ℝ) : Set PlanePoint :=
  {p | p.2 ^ 2 < q W epsilon p.1}

lemma domain_y_lt_one {W epsilon : ℝ} {p : PlanePoint}
    (hp : p ∈ domain W epsilon) : |p.2| < 1 := by
  change p.2 ^ 2 < q W epsilon p.1 at hp
  have hsq : p.2 ^ 2 < 1 := hp.trans_le (q_le_one W epsilon p.1)
  have habsSq : |p.2| ^ 2 < (1 : ℝ) ^ 2 := by
    simpa only [sq_abs, one_pow] using hsq
  exact (sq_lt_sq₀ (abs_nonneg p.2) zero_le_one).mp habsSq

/-- Every recovery closure stays in the closed density-one strip. -/
theorem closure_domain_subset_closedStrip (W epsilon : ℝ) :
    closure (domain W epsilon) ⊆ {p : PlanePoint | |p.2| ≤ 1} := by
  apply closure_minimal
  · intro p hp
    exact (domain_y_lt_one hp).le
  · exact isClosed_le continuous_snd.abs continuous_const

end CMVRelaxation.StadiumRecovery
