/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVProjectionDefect

/-!
# Positive horizontal dilation transport

This module treats positive horizontal dilation in the coordinate plane and in
its Euclidean `L²` realization.  It controls literal complete frontiers and the
extended weighted smooth cost without finiteness or regularity assumptions.
-/

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal

noncomputable section

namespace CMVRelaxation

/-- Positive horizontal dilation `(x, y) ↦ (t * x, y)`. -/
def horizontalDilation (t : ℝ) (ht : 0 < t) : PlanePoint ≃ₜ PlanePoint where
  toFun p := (t * p.1, p.2)
  invFun p := (t⁻¹ * p.1, p.2)
  left_inv p := by ext <;> simp [ht.ne']
  right_inv p := by ext <;> simp [ht.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem horizontalDilation_apply (t : ℝ) (ht : 0 < t)
    (p : PlanePoint) :
    horizontalDilation t ht p = (t * p.1, p.2) :=
  rfl

@[simp] theorem horizontalDilation_symm_apply (t : ℝ) (ht : 0 < t)
    (p : PlanePoint) :
    (horizontalDilation t ht).symm p = (t⁻¹ * p.1, p.2) :=
  rfl

@[simp] theorem horizontalDilation_inverse_apply (t : ℝ) (ht : 0 < t)
    (p : PlanePoint) :
    (horizontalDilation t ht).symm (horizontalDilation t ht p) = p :=
  (horizontalDilation t ht).symm_apply_apply p

@[simp] theorem horizontalDilation_apply_inverse (t : ℝ) (ht : 0 < t)
    (p : PlanePoint) :
    horizontalDilation t ht ((horizontalDilation t ht).symm p) = p :=
  (horizontalDilation t ht).apply_symm_apply p

theorem mem_horizontalDilation_image_iff (t : ℝ) (ht : 0 < t)
    (U : Set PlanePoint) (p : PlanePoint) :
    p ∈ horizontalDilation t ht '' U ↔
      (horizontalDilation t ht).symm p ∈ U := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [horizontalDilation_symm_apply, horizontalDilation_apply, ht.ne'] using hq
  · intro hp
    exact ⟨(horizontalDilation t ht).symm p, hp,
      (horizontalDilation t ht).apply_symm_apply p⟩


@[simp] theorem stripDensity_horizontalDilation (lam t : ℝ) (ht : 0 < t)
    (p : PlanePoint) :
    StripDensity lam (horizontalDilation t ht p) = StripDensity lam p := by
  rfl
/-- The conjugate of horizontal dilation on the Euclidean `L²` plane. -/
def euclideanHorizontalDilation (t : ℝ) (ht : 0 < t) :
    EuclideanPlane ≃ₜ EuclideanPlane :=
  planeEuclideanHomeomorph.symm.trans
    ((horizontalDilation t ht).trans planeEuclideanHomeomorph)

@[simp] theorem euclideanHorizontalDilation_apply (t : ℝ) (ht : 0 < t)
    (p : EuclideanPlane) :
    euclideanHorizontalDilation t ht p =
      WithLp.toLp 2 (t * (WithLp.ofLp p).1, (WithLp.ofLp p).2) :=
  rfl

@[simp] theorem euclideanHorizontalDilation_symm_apply (t : ℝ) (ht : 0 < t)
    (p : EuclideanPlane) :
    (euclideanHorizontalDilation t ht).symm p =
      WithLp.toLp 2 (t⁻¹ * (WithLp.ofLp p).1, (WithLp.ofLp p).2) :=
  rfl

lemma max_horizontalDilation_nonneg (t : ℝ) : 0 ≤ max t 1 :=
  le_trans zero_le_one (le_max_right _ _)

def horizontalDilationConstant (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (max t 1)

@[simp] theorem coe_horizontalDilationConstant (t : ℝ) :
    (horizontalDilationConstant t : ℝ) = max t 1 := by
  simp [horizontalDilationConstant]

/-- Sharp `L²` Lipschitz constant for positive horizontal dilation. -/
theorem lipschitzWith_euclideanHorizontalDilation (t : ℝ) (ht : 0 < t) :
    LipschitzWith (horizontalDilationConstant t)
      (euclideanHorizontalDilation t ht) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro p q
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  simp only [euclideanHorizontalDilation_apply]
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  rw [coe_horizontalDilationConstant]
  norm_num
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have ht0 : 0 ≤ t := ht.le
  have hct : t ≤ max t 1 := le_max_left _ _
  have hc1 : 1 ≤ max t 1 := le_max_right _ _
  have hx : 0 ≤ dist (WithLp.fst p) (WithLp.fst q) := dist_nonneg
  have hy : 0 ≤ dist (WithLp.snd p) (WithLp.snd q) := dist_nonneg
  have hdist :
      dist (t * WithLp.fst p) (t * WithLp.fst q) =
        t * dist (WithLp.fst p) (WithLp.fst q) := by
    change dist (t • WithLp.fst p) (t • WithLp.fst q) = _
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg ht0]
  rw [hdist]
  have hsq :
      (t * dist (WithLp.fst p) (WithLp.fst q)) ^ 2 +
          dist (WithLp.snd p) (WithLp.snd q) ^ 2 ≤
        (max t 1) ^ 2 *
          (dist (WithLp.fst p) (WithLp.fst q) ^ 2 +
            dist (WithLp.snd p) (WithLp.snd q) ^ 2) := by
    have hta0 : 0 ≤ t * dist (WithLp.fst p) (WithLp.fst q) :=
      mul_nonneg ht0 hx
    have hca0 : 0 ≤ max t 1 * dist (WithLp.fst p) (WithLp.fst q) :=
      mul_nonneg (max_horizontalDilation_nonneg t) hx
    have hta :
        t * dist (WithLp.fst p) (WithLp.fst q) ≤
          max t 1 * dist (WithLp.fst p) (WithLp.fst q) :=
      mul_le_mul_of_nonneg_right hct hx
    have hxa :=
      (sq_le_sq₀ hta0 hca0).2 hta
    have hb :
        dist (WithLp.snd p) (WithLp.snd q) ≤
          max t 1 * dist (WithLp.snd p) (WithLp.snd q) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hy
    have hcb0 : 0 ≤ max t 1 * dist (WithLp.snd p) (WithLp.snd q) :=
      mul_nonneg (max_horizontalDilation_nonneg t) hy
    have hya := (sq_le_sq₀ hy hcb0).2 hb
    calc
      _ ≤ (max t 1 * dist (WithLp.fst p) (WithLp.fst q)) ^ 2 +
          (max t 1 * dist (WithLp.snd p) (WithLp.snd q)) ^ 2 :=
        add_le_add hxa hya
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt ((max t 1) ^ 2 *
        (dist (WithLp.fst p) (WithLp.fst q) ^ 2 +
          dist (WithLp.snd p) (WithLp.snd q) ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg (max t 1)),
        Real.sqrt_sq (max_horizontalDilation_nonneg t)]


/-- Horizontal dilation increases one-dimensional Hausdorff measure, even
after restriction to an arbitrary subset, by at most its sharp Lipschitz
constant. -/
theorem hausdorffRestrict_euclideanHorizontalDilation_le
    (t : ℝ) (ht : 0 < t) (s : Set EuclideanPlane) :
    (μH[1] : Measure EuclideanPlane).restrict
        (euclideanHorizontalDilation t ht '' s) ≤
      (horizontalDilationConstant t : ℝ≥0∞) •
        Measure.map (euclideanHorizontalDilation t ht)
          ((μH[1] : Measure EuclideanPlane).restrict s) := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.restrict_apply hA, Measure.smul_apply,
    Measure.map_apply (euclideanHorizontalDilation t ht).measurable hA,
    Measure.restrict_apply
      (hA.preimage (euclideanHorizontalDilation t ht).measurable)]
  rw [← Set.image_preimage_inter]
  simpa using
    (lipschitzWith_euclideanHorizontalDilation t ht).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num)
      ((euclideanHorizontalDilation t ht) ⁻¹' A ∩ s)

private theorem euclidean_image_horizontalDilation
    (t : ℝ) (ht : 0 < t) (U : Set PlanePoint) :
    planeEuclideanHomeomorph '' (horizontalDilation t ht '' U) =
      euclideanHorizontalDilation t ht ''
        (planeEuclideanHomeomorph '' U) := by
  rw [Set.image_image, Set.image_image]
  rfl

/-- Horizontal dilation carries the literal complete frontier in the
Euclidean realization onto the literal complete frontier of the image. -/
theorem euclideanFrontier_horizontalDilation
    (t : ℝ) (ht : 0 < t) (U : Set PlanePoint) :
    frontier
        (planeEuclideanHomeomorph '' (horizontalDilation t ht '' U)) =
      euclideanHorizontalDilation t ht ''
        frontier (planeEuclideanHomeomorph '' U) := by
  rw [euclidean_image_horizontalDilation]
  simpa using
    ((euclideanHorizontalDilation t ht).image_frontier
      (planeEuclideanHomeomorph '' U)).symm

/-- Literal complete-frontier Euclidean `H¹` is dominated by the sharp
horizontal-dilation Lipschitz factor. -/
theorem hausdorffMeasure_euclideanFrontier_horizontalDilation_le
    (t : ℝ) (ht : 0 < t) (U : Set PlanePoint) :
    (μH[1] : Measure EuclideanPlane)
        (frontier
          (planeEuclideanHomeomorph '' (horizontalDilation t ht '' U))) ≤
      (horizontalDilationConstant t : ℝ≥0∞) *
        (μH[1] : Measure EuclideanPlane)
          (frontier (planeEuclideanHomeomorph '' U)) := by
  rw [euclideanFrontier_horizontalDilation]
  simpa using
    (lipschitzWith_euclideanHorizontalDilation t ht).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num)
      (frontier (planeEuclideanHomeomorph '' U))


/-- The complete-frontier measure of a horizontally dilated carrier is
dominated by the dilated pushforward of its original complete-frontier
measure.  This is a measure inequality, so it controls every measurable
frontier portion at once. -/
theorem frontierMeasure_horizontalDilation_le
    (t : ℝ) (ht : 0 < t) (U : Set PlanePoint) :
    FrontierMeasure (horizontalDilation t ht '' U) ≤
      (horizontalDilationConstant t : ℝ≥0∞) •
        Measure.map (horizontalDilation t ht) (FrontierMeasure U) := by
  have hfrontier := euclideanFrontier_horizontalDilation t ht U
  unfold FrontierMeasure
  rw [hfrontier]
  calc
    Measure.map planeEuclideanHomeomorph.symm
        ((μH[1] : Measure EuclideanPlane).restrict
          (euclideanHorizontalDilation t ht ''
            frontier (planeEuclideanHomeomorph '' U))) ≤
        Measure.map planeEuclideanHomeomorph.symm
          ((horizontalDilationConstant t : ℝ≥0∞) •
            Measure.map (euclideanHorizontalDilation t ht)
              ((μH[1] : Measure EuclideanPlane).restrict
                (frontier (planeEuclideanHomeomorph '' U)))) :=
      Measure.map_mono
        (hausdorffRestrict_euclideanHorizontalDilation_le t ht
          (frontier (planeEuclideanHomeomorph '' U)))
        planeEuclideanHomeomorph.symm.measurable
    _ = (horizontalDilationConstant t : ℝ≥0∞) •
        Measure.map (horizontalDilation t ht)
          (Measure.map planeEuclideanHomeomorph.symm
            ((μH[1] : Measure EuclideanPlane).restrict
              (frontier (planeEuclideanHomeomorph '' U)))) := by
      rw [Measure.map_smul,
        Measure.map_map planeEuclideanHomeomorph.symm.measurable
          (euclideanHorizontalDilation t ht).measurable,
        Measure.map_map (horizontalDilation t ht).measurable
          planeEuclideanHomeomorph.symm.measurable]
      rfl

/-- Positive horizontal dilation increases the extended weighted
complete-frontier cost by at most its sharp Euclidean Lipschitz constant.
The proof is in `ℝ≥0∞`, so no finiteness assumption is imposed on either
cost. -/
theorem smoothCost_horizontalDilation_le
    (lam t : ℝ) (ht : 0 < t) (U : Set PlanePoint) :
    smoothCost lam (horizontalDilation t ht '' U) ≤
      (horizontalDilationConstant t : ℝ≥0∞) * smoothCost lam U := by
  unfold smoothCost
  calc
    (∫⁻ p, ENNReal.ofReal (StripDensity lam p)
        ∂FrontierMeasure (horizontalDilation t ht '' U)) ≤
        ∫⁻ p, ENNReal.ofReal (StripDensity lam p)
          ∂((horizontalDilationConstant t : ℝ≥0∞) •
            Measure.map (horizontalDilation t ht) (FrontierMeasure U)) :=
      lintegral_mono'
        (frontierMeasure_horizontalDilation_le t ht U) le_rfl
    _ = (horizontalDilationConstant t : ℝ≥0∞) *
        ∫⁻ p, ENNReal.ofReal (StripDensity lam p)
          ∂Measure.map (horizontalDilation t ht) (FrontierMeasure U) := by
      rw [lintegral_smul_measure]
      rfl
    _ = (horizontalDilationConstant t : ℝ≥0∞) *
        ∫⁻ p, ENNReal.ofReal
          (StripDensity lam (horizontalDilation t ht p))
          ∂FrontierMeasure U := by
      rw [(horizontalDilation t ht).measurableEmbedding.lintegral_map]
    _ = (horizontalDilationConstant t : ℝ≥0∞) *
        ∫⁻ p, ENNReal.ofReal (StripDensity lam p)
          ∂FrontierMeasure U := by
      congr 1



end CMVRelaxation
