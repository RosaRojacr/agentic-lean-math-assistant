/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVProjectionDefect
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rigid-coordinate projection defects

The axis-aligned projection estimate is transported through arbitrary Euclidean
isometries.  This permits finite families of genuinely disjoint local boxes,
with each box aligned to its own boundary tangent, while all local frontier
charges are paid by one global smooth cost.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff

noncomputable section

namespace CMVRelaxation

/-- An arbitrary Euclidean rigid motion, transported back to the coordinate
plane used by the CMV carriers. -/
def euclideanRigidMap (e : EuclideanPlane ≃ᵢ EuclideanPlane) :
    PlanePoint ≃ₜ PlanePoint :=
  planeEuclideanHomeomorph.trans
    (e.toHomeomorph.trans planeEuclideanHomeomorph.symm)

@[simp] theorem planeEuclideanHomeomorph_euclideanRigidMap
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (p : PlanePoint) :
    planeEuclideanHomeomorph (euclideanRigidMap e p) =
      e (planeEuclideanHomeomorph p) := by
  rfl

@[simp] theorem planeEuclideanHomeomorph_euclideanRigidMap_symm
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (p : PlanePoint) :
    planeEuclideanHomeomorph ((euclideanRigidMap e).symm p) =
      e.symm (planeEuclideanHomeomorph p) := by
  rfl

/-- Every Euclidean isometry equivalence preserves the ambient Lebesgue
measure.  Mazur--Ulam splits it into a linear isometry and a translation. -/
theorem measurePreserving_euclideanIsometry
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) :
    MeasurePreserving e (volume : Measure EuclideanPlane) volume := by
  let L : EuclideanPlane ≃ₗᵢ[ℝ] EuclideanPlane :=
    e.toRealLinearIsometryEquiv
  have hL : MeasurePreserving L
      (volume : Measure EuclideanPlane) volume := L.measurePreserving
  have ht : MeasurePreserving (fun z : EuclideanPlane => z + e 0)
      (volume : Measure EuclideanPlane) volume :=
    measurePreserving_add_right (volume : Measure EuclideanPlane) (e 0)
  have hcomp := ht.comp hL
  convert hcomp using 1
  funext z
  simp only [Function.comp_apply, L,
    IsometryEquiv.toRealLinearIsometryEquiv_apply]
  exact (sub_add_cancel (e z) (e 0)).symm

/-- The coordinate realization of a Euclidean rigid motion preserves planar
Lebesgue measure. -/
theorem measurePreserving_euclideanRigidMap
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) :
    MeasurePreserving (euclideanRigidMap e)
      (volume : Measure PlanePoint) volume := by
  exact WithLp.volume_preserving_ofLp ℝ ℝ |>.comp
    ((measurePreserving_euclideanIsometry e).comp
      (WithLp.volume_preserving_toLp ℝ ℝ))

private theorem volume_euclideanRigidMap_image
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (S : Set PlanePoint) :
    volume (euclideanRigidMap e '' S) = volume S := by
  have h := (measurePreserving_euclideanRigidMap e).setLIntegral_comp_emb
    (euclideanRigidMap e).measurableEmbedding
    (fun _ : PlanePoint => (1 : ℝ≥0∞)) S
  simpa using h.symm

/-- Rigid motions are exact isometries of the global characteristic-function
distance. -/
theorem characteristicDistance_euclideanRigidMap
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (E F : Set PlanePoint) :
    characteristicDistance (euclideanRigidMap e '' E)
      (euclideanRigidMap e '' F) = characteristicDistance E F := by
  rw [characteristicDistance, characteristicDistance,
    ← Set.image_symmDiff (euclideanRigidMap e).injective]
  exact volume_euclideanRigidMap_image e (E ∆ F)

/-- A local coordinate box after an arbitrary Euclidean rigid motion. -/
def rigidProjectionBox (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (a b y₀ rho : ℝ) : Set PlanePoint :=
  euclideanRigidMap e '' projectionBox a b y₀ rho

lemma isCompact_rigidProjectionBox
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (a b y₀ rho : ℝ) :
    IsCompact (rigidProjectionBox e a b y₀ rho) := by
  exact (isCompact_projectionBox a b y₀ rho).image
    (euclideanRigidMap e).continuous

private lemma rigid_image_preimage_image
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (S : Set PlanePoint) :
    euclideanRigidMap e '' ((euclideanRigidMap e).symm '' S) = S := by
  exact (euclideanRigidMap e).image_symm_image S

private lemma rigid_frontier_box_image
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (U : Set PlanePoint)
    (a b y₀ rho : ℝ) :
    euclideanRigidMap e ''
        (frontier ((euclideanRigidMap e).symm '' U) ∩
          projectionBox a b y₀ rho) =
      frontier U ∩ rigidProjectionBox e a b y₀ rho := by
  rw [Set.image_inter (euclideanRigidMap e).injective,
    (euclideanRigidMap e).image_frontier,
    rigid_image_preimage_image, rigidProjectionBox]

private lemma rigid_local_frontier_measure
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (U : Set PlanePoint)
    (a b y₀ rho : ℝ) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          (frontier ((euclideanRigidMap e).symm '' U) ∩
            projectionBox a b y₀ rho)) =
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          (frontier U ∩ rigidProjectionBox e a b y₀ rho)) := by
  let S : Set PlanePoint :=
    frontier ((euclideanRigidMap e).symm '' U) ∩
      projectionBox a b y₀ rho
  have himage :
      e '' (planeEuclideanHomeomorph '' S) =
        planeEuclideanHomeomorph ''
          (frontier U ∩ rigidProjectionBox e a b y₀ rho) := by
    rw [← rigid_frontier_box_image e U a b y₀ rho]
    ext z
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨euclideanRigidMap e p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨planeEuclideanHomeomorph p,
        ⟨p, hp, rfl⟩, rfl⟩
  calc
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' S) =
      (μH[1] : Measure EuclideanPlane)
        (e '' (planeEuclideanHomeomorph '' S)) := by
          symm
          exact e.isometry.hausdorffMeasure_image (Or.inl (by norm_num)) _
    _ = _ := congrArg _ himage

/-- The axis-aligned projection defect transported to an arbitrary rigid
coordinate frame.  The target collar assumptions are stated directly in the
original CMV coordinate plane. -/
theorem rigid_projection_defect
    {E U : Set PlanePoint} {a b y₀ rho : ℝ}
    (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : MeasurableSet E) (hU : IsOpen U)
    (hrho : 0 < rho)
    (hlower :
      euclideanRigidMap e ''
          (Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho)) ⊆ E)
    (hupper :
      Disjoint
        (euclideanRigidMap e ''
          (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho))) E) :
    ENNReal.ofReal (b - a) ≤
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (frontier U ∩ rigidProjectionBox e a b y₀ rho)) +
        characteristicDistance U E / ENNReal.ofReal rho := by
  let R := euclideanRigidMap e
  let E₀ : Set PlanePoint := R.symm '' E
  let U₀ : Set PlanePoint := R.symm '' U
  have hE₀ : MeasurableSet E₀ := by
    have heq : E₀ = R ⁻¹' E := by
      ext p
      simp only [E₀, R, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨q, hq, rfl⟩
        simpa using hq
      · intro hp
        exact ⟨R p, hp, R.symm_apply_apply p⟩
    rw [heq]
    exact hE.preimage R.measurable
  have hU₀ : IsOpen U₀ := R.symm.isOpenMap U hU
  have hlower₀ :
      Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho) ⊆ E₀ := by
    intro p hp
    exact ⟨R p, hlower ⟨p, hp, rfl⟩, R.symm_apply_apply p⟩
  have hupper₀ :
      Disjoint (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho)) E₀ := by
    rw [Set.disjoint_left]
    intro p hpbox hpE
    rcases hpE with ⟨q, hq, hqp⟩
    have hq_eq : q = R p := by
      simpa [R] using congrArg R hqp
    subst q
    exact (Set.disjoint_left.mp hupper) ⟨p, hpbox, rfl⟩ hq
  have hproj := projection_defect hE₀ hU₀ hrho hlower₀ hupper₀
  have hfront :
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (frontier U₀ ∩ projectionBox a b y₀ rho)) =
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph ''
            (frontier U ∩ rigidProjectionBox e a b y₀ rho)) := by
    exact rigid_local_frontier_measure e U a b y₀ rho
  have hdist : characteristicDistance U₀ E₀ = characteristicDistance U E := by
    have h := characteristicDistance_euclideanRigidMap e U₀ E₀
    rw [rigid_image_preimage_image, rigid_image_preimage_image] at h
    exact h.symm
  simpa only [hfront, hdist] using hproj

/-- One rigid box charges only its local weighted frontier contribution.  This
localized form, unlike `projection_defect_smoothCost`, can be summed over
disjoint boxes without multiplying the global smooth cost. -/
theorem rigid_projection_defect_setLIntegral
    {E U : Set PlanePoint} {a b y₀ rho : ℝ}
    (e : EuclideanPlane ≃ᵢ EuclideanPlane)
    (hE : MeasurableSet E) (hU : IsOpen U)
    (hrho : 0 < rho)
    (hlower :
      euclideanRigidMap e ''
          (Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho)) ⊆ E)
    (hupper :
      Disjoint
        (euclideanRigidMap e ''
          (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho))) E)
    (lam w : ℝ)
    (hwindow : ∀ p ∈ rigidProjectionBox e a b y₀ rho,
      w ≤ StripDensity lam p) :
    ENNReal.ofReal w * ENNReal.ofReal (b - a) ≤
      (∫⁻ p in rigidProjectionBox e a b y₀ rho,
          ENNReal.ofReal (StripDensity lam p) ∂FrontierMeasure U) +
        (ENNReal.ofReal w / ENNReal.ofReal rho) *
          characteristicDistance U E := by
  let Q := rigidProjectionBox e a b y₀ rho
  have hQ : MeasurableSet Q :=
    (isCompact_rigidProjectionBox e a b y₀ rho).measurableSet
  have hproj := rigid_projection_defect e hE hU hrho hlower hupper
  have hlocal :
      ENNReal.ofReal w *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph '' (frontier U ∩ Q)) ≤
        ∫⁻ p in Q, ENNReal.ofReal (StripDensity lam p)
          ∂FrontierMeasure U := by
    rw [← frontierMeasure_apply_eq_euclidean U Q hQ]
    exact ofReal_mul_frontierMeasure_le_setLIntegral hQ lam w hwindow
  calc
    ENNReal.ofReal w * ENNReal.ofReal (b - a) ≤
        ENNReal.ofReal w *
          ((μH[1] : Measure EuclideanPlane)
              (planeEuclideanHomeomorph '' (frontier U ∩ Q)) +
            characteristicDistance U E / ENNReal.ofReal rho) := by
      simpa only [mul_comm] using
        mul_le_mul_left hproj (ENNReal.ofReal w)
    _ = ENNReal.ofReal w *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph '' (frontier U ∩ Q)) +
        (ENNReal.ofReal w / ENNReal.ofReal rho) *
          characteristicDistance U E := by
      rw [mul_add]
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ (∫⁻ p in Q, ENNReal.ofReal (StripDensity lam p)
          ∂FrontierMeasure U) +
        (ENNReal.ofReal w / ENNReal.ofReal rho) *
          characteristicDistance U E :=
      add_le_add hlocal le_rfl

/-- Complete geometric and density data for one rigid projection patch. -/
structure RigidProjectionPatch (lam : ℝ) (E : Set PlanePoint) where
  frame : EuclideanPlane ≃ᵢ EuclideanPlane
  a : ℝ
  b : ℝ
  y₀ : ℝ
  rho : ℝ
  weight : ℝ
  rho_pos : 0 < rho
  lower_collar :
    euclideanRigidMap frame ''
        (Icc a b ×ˢ Icc (y₀ - 2 * rho) (y₀ - rho)) ⊆ E
  upper_collar :
    Disjoint
      (euclideanRigidMap frame ''
        (Icc a b ×ˢ Icc (y₀ + rho) (y₀ + 2 * rho))) E
  density_lower :
    ∀ p ∈ rigidProjectionBox frame a b y₀ rho,
      weight ≤ StripDensity lam p

namespace RigidProjectionPatch

variable {lam : ℝ} {E : Set PlanePoint}

/-- The actual compact window occupied by a patch. -/
def window (P : RigidProjectionPatch lam E) : Set PlanePoint :=
  rigidProjectionBox P.frame P.a P.b P.y₀ P.rho

lemma isCompact_window (P : RigidProjectionPatch lam E) :
    IsCompact P.window :=
  isCompact_rigidProjectionBox P.frame P.a P.b P.y₀ P.rho

lemma measurableSet_window (P : RigidProjectionPatch lam E) :
    MeasurableSet P.window :=
  P.isCompact_window.measurableSet

/-- Weighted projected width recovered from this patch. -/
def payoff (P : RigidProjectionPatch lam E) : ℝ≥0∞ :=
  ENNReal.ofReal P.weight * ENNReal.ofReal (P.b - P.a)

/-- Coefficient multiplying the global characteristic-function defect. -/
def errorCoefficient (P : RigidProjectionPatch lam E) : ℝ≥0∞ :=
  ENNReal.ofReal P.weight / ENNReal.ofReal P.rho

/-- One certified patch is bounded by its local frontier charge and one global
characteristic-function defect. -/
theorem payoff_le_localCost_add_error
    (P : RigidProjectionPatch lam E) (hE : MeasurableSet E)
    {U : Set PlanePoint} (hU : IsOpen U) :
    P.payoff ≤
      (∫⁻ p in P.window, ENNReal.ofReal (StripDensity lam p)
        ∂FrontierMeasure U) +
      P.errorCoefficient * characteristicDistance U E := by
  exact rigid_projection_defect_setLIntegral P.frame hE hU P.rho_pos
    P.lower_collar P.upper_collar lam P.weight P.density_lower

/-- Pairwise-disjoint rigid windows pay into one global smooth cost.  This is
the finite summation theorem required before any curve-specific exhaustion:
neither the smooth cost nor the characteristic defect is duplicated per box. -/
theorem finset_sum_payoff_le_smoothCost_add_error
    {ι : Type*} (s : Finset ι) (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    (hE : MeasurableSet E) {U : Set PlanePoint} (hU : IsOpen U) :
    ∑ i ∈ s, (P i).payoff ≤
      smoothCost lam U +
        (∑ i ∈ s, (P i).errorCoefficient) *
          characteristicDistance U E := by
  let f : PlanePoint → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (StripDensity lam p)
  let D : ℝ≥0∞ := characteristicDistance U E
  have hlocal :
      (∑ i ∈ s, ∫⁻ p in (P i).window, f p ∂FrontierMeasure U) ≤
        smoothCost lam U := by
    rw [← lintegral_biUnion_finset hpair
      (fun i _ => (P i).measurableSet_window)]
    exact setLIntegral_le_lintegral _ _
  calc
    ∑ i ∈ s, (P i).payoff ≤
        ∑ i ∈ s,
          ((∫⁻ p in (P i).window, f p ∂FrontierMeasure U) +
            (P i).errorCoefficient * D) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (P i).payoff_le_localCost_add_error hE hU
    _ = (∑ i ∈ s,
          ∫⁻ p in (P i).window, f p ∂FrontierMeasure U) +
        (∑ i ∈ s, (P i).errorCoefficient) * D := by
      rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ smoothCost lam U +
        (∑ i ∈ s, (P i).errorCoefficient) *
          characteristicDistance U E := by
      exact add_le_add hlocal le_rfl

end RigidProjectionPatch

end CMVRelaxation
