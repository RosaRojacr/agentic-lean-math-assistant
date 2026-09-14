/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxation
import CMVRigidProjection
import CMVTwoPatchGraphVariation
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Local graph surgery foundations for the CMV relaxation

This module isolates the local smooth-domain and graph-collar facts needed for
sharp replacement inside an arbitrary unchanged carrier.  It does not assume a
local perimeter representation or assert the relaxed-cost replacement estimate.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff symmDiff Manifold

noncomputable section

namespace CMVRelaxation

/-- An open set locally equal near every frontier point to a smooth domain is a
smooth domain. -/
theorem IsSmoothDomain.of_locally_eq
    {U : Set PlanePoint} (hUopen : IsOpen U)
    (hlocal : ∀ p ∈ frontier U,
      ∃ (M V : Set PlanePoint), IsSmoothDomain M ∧ IsOpen V ∧ p ∈ V ∧
        U ∩ V = M ∩ V) :
    IsSmoothDomain U := by
  refine ⟨hUopen, ?_⟩
  intro p hp
  rcases hlocal p hp with ⟨M, V, hM, hVopen, hpV, hUV⟩
  have hpUV : p ∈ frontier U ∩ V := ⟨hp, hpV⟩
  rw [← frontier_inter_open_inter hVopen, hUV,
    frontier_inter_open_inter hVopen] at hpUV
  rcases hM.regular_boundary p hpUV.1 with
    ⟨W, g, D, hWopen, hpW, hg, hgp, hderiv, hD, hMW⟩
  refine ⟨V ∩ W, g, D, hVopen.inter hWopen, ⟨hpV, hpW⟩,
    hg.mono inter_subset_right, hgp, hderiv, hD, ?_⟩
  calc
    U ∩ (V ∩ W) = (U ∩ V) ∩ W := by
      ext q
      simp only [mem_inter_iff]
      tauto
    _ = (M ∩ V) ∩ W := by rw [hUV]
    _ = V ∩ (M ∩ W) := by
      ext q
      simp only [mem_inter_iff]
      tauto
    _ = V ∩ (W ∩ {q | g q < 0}) := by rw [hMW]
    _ = (V ∩ W) ∩ {q | g q < 0} := by
      ext q
      simp only [mem_inter_iff]
      tauto

/-- Frontiers agree inside an open window whenever the carriers agree there. -/
lemma frontier_inter_eq_of_inter_open_eq
    {U M W : Set PlanePoint} (hW : IsOpen W)
    (hlocal : U ∩ W = M ∩ W) :
    frontier U ∩ W = frontier M ∩ W := by
  rw [← frontier_inter_open_inter hW, hlocal,
    frontier_inter_open_inter hW]

/-- Complete-frontier measure restrictions agree on every measurable set where
the two complete frontiers agree.  Unlike the open-locality specialization
below, this form also applies to closed complements of splice interiors. -/
theorem frontierMeasure_restrict_eq_of_frontier_inter_eq
    {U M W : Set PlanePoint} (hW : MeasurableSet W)
    (hfrontier : frontier U ∩ W = frontier M ∩ W) :
    (FrontierMeasure U).restrict W = (FrontierMeasure M).restrict W := by
  apply Measure.ext
  intro Q hQ
  rw [Measure.restrict_apply hQ, Measure.restrict_apply hQ,
    frontierMeasure_apply_eq_euclidean U (Q ∩ W)
      (hQ.inter hW),
    frontierMeasure_apply_eq_euclidean M (Q ∩ W)
      (hQ.inter hW)]
  apply congrArg (fun S : Set EuclideanPlane => (μH[1]) S)
  apply congrArg (fun S : Set PlanePoint => planeEuclideanHomeomorph '' S)
  calc
    frontier U ∩ (Q ∩ W) = (frontier U ∩ W) ∩ Q := by
      ext p
      simp only [mem_inter_iff]
      tauto
    _ = (frontier M ∩ W) ∩ Q := by rw [hfrontier]
    _ = frontier M ∩ (Q ∩ W) := by
      ext p
      simp only [mem_inter_iff]
      tauto

/-- Complete-frontier measure is local on open windows. -/
theorem frontierMeasure_restrict_eq_of_inter_open_eq
    {U M W : Set PlanePoint} (hW : IsOpen W)
    (hlocal : U ∩ W = M ∩ W) :
    (FrontierMeasure U).restrict W = (FrontierMeasure M).restrict W := by
  apply frontierMeasure_restrict_eq_of_frontier_inter_eq hW.measurableSet
  exact frontier_inter_eq_of_inter_open_eq hW hlocal

/-- Weighted complete-frontier cost restricted to a window. -/
def smoothCostOn (lam : ℝ) (U W : Set PlanePoint) : ENNReal :=
  ∫⁻ p in W, ENNReal.ofReal (StripDensity lam p) ∂FrontierMeasure U

/-- Local smooth cost agrees on a measurable window whenever the corresponding
complete-frontier portions agree there. -/
theorem smoothCostOn_eq_of_frontier_inter_eq
    (lam : ℝ) {U M W : Set PlanePoint} (hW : MeasurableSet W)
    (hfrontier : frontier U ∩ W = frontier M ∩ W) :
    smoothCostOn lam U W = smoothCostOn lam M W := by
  unfold smoothCostOn
  rw [frontierMeasure_restrict_eq_of_frontier_inter_eq hW hfrontier]

/-- Local smooth cost depends only on the carrier inside the open window. -/
theorem smoothCostOn_eq_of_inter_open_eq
    (lam : ℝ) {U M W : Set PlanePoint} (hW : IsOpen W)
    (hlocal : U ∩ W = M ∩ W) :
    smoothCostOn lam U W = smoothCostOn lam M W := by
  apply smoothCostOn_eq_of_frontier_inter_eq lam hW.measurableSet
  exact frontier_inter_eq_of_inter_open_eq hW hlocal

/-- Smooth cost splits exactly across a measurable window and its complement. -/
theorem smoothCostOn_add_compl
    (lam : ℝ) (U : Set PlanePoint) {W : Set PlanePoint}
    (hW : MeasurableSet W) :
    smoothCostOn lam U W + smoothCostOn lam U Wᶜ = smoothCost lam U := by
  exact lintegral_add_compl _ hW

namespace RigidProjectionPatch

variable {lam : ℝ} {E : Set PlanePoint}

/-- Pairwise-disjoint rigid windows contained in a localization window charge
only the corresponding local complete-frontier cost.  This is
the sharp local form needed to recover the old graph contribution before the
unchanged exterior cost is reattached. -/
theorem finset_sum_payoff_le_smoothCostOn_add_error
    {ι : Type*} (s : Finset ι) (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    {W : Set PlanePoint}
    (hsub : ∀ i ∈ s, (P i).window ⊆ W)
    (hE : MeasurableSet E) {U : Set PlanePoint} (hU : IsOpen U) :
    ∑ i ∈ s, (P i).payoff ≤
      smoothCostOn lam U W +
        (∑ i ∈ s, (P i).errorCoefficient) *
          characteristicDistance U E := by
  let f : PlanePoint → ENNReal :=
    fun p => ENNReal.ofReal (StripDensity lam p)
  let D : ENNReal := characteristicDistance U E
  have hlocal :
      (∑ i ∈ s, ∫⁻ p in (P i).window, f p ∂FrontierMeasure U) ≤
        smoothCostOn lam U W := by
    rw [← lintegral_biUnion_finset hpair
      (fun i _ => (P i).measurableSet_window)]
    apply MeasureTheory.lintegral_mono_set
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hi, hp⟩
    exact hsub i hi hp
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
    _ ≤ smoothCostOn lam U W +
        (∑ i ∈ s, (P i).errorCoefficient) *
          characteristicDistance U E :=
      add_le_add hlocal le_rfl

end RigidProjectionPatch

/-- Every fixed finite local projection family survives an actual smooth
recovery sequence: its finite characteristic-distance coefficient vanishes,
leaving a lower bound on the localized cost liminf. -/
theorem SmoothSequence.finset_sum_payoff_le_liminf_smoothCostOn
    {lam : ℝ} {E : Set PlanePoint} (A : SmoothSequence)
    (hconv : A.ConvergesTo E)
    {ι : Type*} (s : Finset ι) (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    {W : Set PlanePoint}
    (hsub : ∀ i ∈ s, (P i).window ⊆ W)
    (hE : MeasurableSet E) :
    ∑ i ∈ s, (P i).payoff ≤
      liminf (fun n => smoothCostOn lam (A.carrier n) W) atTop := by
  let C : ENNReal := ∑ i ∈ s, (P i).errorCoefficient
  have hC : C ≠ ⊤ := by
    dsimp only [C]
    apply ENNReal.sum_ne_top.2
    intro i hi
    rw [RigidProjectionPatch.errorCoefficient]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2 (P i).rho_pos).ne'
  have herr : Tendsto
      (fun n => C * characteristicDistance (A.carrier n) E)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr hC)
  rw [← ENNReal.liminf_add_of_right_tendsto_zero herr]
  apply le_liminf_of_le (by isBoundedDefault)
  filter_upwards with n
  exact RigidProjectionPatch.finset_sum_payoff_le_smoothCostOn_add_error
    s P hpair hsub hE (A.smooth n).isOpen

/-- A global `C²` real graph admits a global `C∞` replacement with uniformly
close slope.  Anchoring at `a` turns the slope estimate into the stated
pointwise graph estimate, without claiming uniform closeness on all of `ℝ`. -/
theorem exists_contDiff_infty_deriv_close_anchor
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (a : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ g a = f a ∧
      (∀ x, |deriv g x - deriv f x| < ε) ∧
      ∀ x, |g x - f x| ≤ ε * |x - a| := by
  have hdf : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp hf).2.2
  obtain ⟨k, hk, hkclose, _⟩ :=
    hdf.continuous.exists_contDiff_approx (⊤ : ℕ∞)
      (ε := fun _ : ℝ => ε) continuous_const (fun _ => hε)
  let g : ℝ → ℝ := fun x => f a + ∫ y in a..x, k y
  have hgdiff : Differentiable ℝ g := by
    exact (differentiable_const (f a)).add
      (intervalIntegral.differentiable_integral_of_continuous hk.continuous)
  have hgderiv : deriv g = k := by
    funext x
    have hI := intervalIntegral.integral_hasDerivAt_right
      (hk.continuous.intervalIntegrable a x)
      hk.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hk.continuous.continuousAt
    simpa only [g, deriv_const_add] using hI.deriv
  have hg : ContDiff ℝ ∞ g :=
    contDiff_infty_iff_deriv.mpr ⟨hgdiff, by simpa only [hgderiv] using hk⟩
  have hga : g a = f a := by simp [g]
  have hslope : ∀ x, |deriv g x - deriv f x| < ε := by
    intro x
    rw [hgderiv]
    simpa only [Real.dist_eq] using hkclose x
  refine ⟨g, hg, hga, hslope, ?_⟩
  let h : ℝ → ℝ := fun x => g x - f x
  have hdiff : Differentiable ℝ h :=
    hg.differentiable (by simp) |>.sub
      (hf.differentiable (by norm_num))
  have hderiv (x : ℝ) : deriv h x = deriv g x - deriv f x := by
    exact deriv_sub (hg.differentiable (by simp) x)
      (hf.differentiable (by norm_num) x)
  have hbound : ∀ x, ‖deriv h x‖₊ ≤ ⟨ε, hε.le⟩ := by
    intro x
    rw [hderiv]
    change |deriv g x - deriv f x| ≤ ε
    exact (hslope x).le
  have hlip : LipschitzWith ⟨ε, hε.le⟩ h :=
    lipschitzWith_of_nnnorm_deriv_le hdiff hbound
  intro x
  have hx := hlip.dist_le_mul x a
  change |h x - h a| ≤ ε * |x - a| at hx
  simpa only [h, hga, sub_self, sub_zero] using hx

/-- The Euclidean graph-speed integrand is one-Lipschitz in the slope.  This
is the reverse triangle inequality applied to `(1,p)` and `(1,q)` in `ℂ`. -/
theorem abs_graphSpeed_sub_graphSpeed_le (p q : ℝ) :
    |Real.sqrt (1 + p ^ 2) - Real.sqrt (1 + q ^ 2)| ≤ |p - q| := by
  have h := abs_norm_sub_norm_le (⟨1, p⟩ : ℂ) (⟨1, q⟩ : ℂ)
  simpa [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_sq_eq_abs] using h

/-- Tangent/outward-normal coordinates at a point of a graph. -/
def graphTangentFrame (x₀ y₀ slope : ℝ) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  tangentComplexEquiv.trans <|
    (rotation (Circle.exp (-Real.arctan slope))).toIsometryEquiv.trans <|
    (IsometryEquiv.addLeft (⟨y₀, x₀⟩ : ℂ)).trans
      tangentComplexEquiv.symm

@[simp] theorem euclideanRigidMap_graphTangentFrame
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    euclideanRigidMap (graphTangentFrame x₀ y₀ slope) p =
      (x₀ + p.1 * Real.cos (Real.arctan slope) -
          p.2 * Real.sin (Real.arctan slope),
        y₀ + p.1 * Real.sin (Real.arctan slope) +
          p.2 * Real.cos (Real.arctan slope)) := by
  apply Prod.ext
  · simp only [euclideanRigidMap, graphTangentFrame, Circle.exp_neg, map_inv,
      Homeomorph.trans_apply, planeEuclideanHomeomorph_apply,
      IsometryEquiv.coe_toHomeomorph, IsometryEquiv.trans_apply,
      tangentComplexEquiv_apply, LinearIsometryEquiv.coe_toIsometryEquiv,
      LinearIsometryEquiv.coe_inv, rotation_symm,
      IsometryEquiv.addLeft_apply, tangentComplexEquiv_symm_apply,
      Complex.add_im, Complex.add_re,
      planeEuclideanHomeomorph_symm_toLp]
    rw [rotation_symm, rotation_apply]
    rw [← Circle.exp_neg]
    simp only [Circle.coe_exp]
    rw [Complex.mul_im]
    rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [Real.cos_neg, Real.sin_neg]
    ring
  · simp only [euclideanRigidMap, graphTangentFrame, Circle.exp_neg, map_inv,
      Homeomorph.trans_apply, planeEuclideanHomeomorph_apply,
      IsometryEquiv.coe_toHomeomorph, IsometryEquiv.trans_apply,
      tangentComplexEquiv_apply, LinearIsometryEquiv.coe_toIsometryEquiv,
      LinearIsometryEquiv.coe_inv, rotation_symm,
      IsometryEquiv.addLeft_apply, tangentComplexEquiv_symm_apply,
      Complex.add_im, Complex.add_re,
      planeEuclideanHomeomorph_symm_toLp]
    rw [rotation_symm, rotation_apply]
    rw [← Circle.exp_neg]
    simp only [Circle.coe_exp]
    rw [Complex.mul_re]
    rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [Real.cos_neg, Real.sin_neg]
    ring

/-- The second tangent-frame coordinate is signed normal displacement from the
affine tangent line, normalized by graph speed. -/
theorem graphTangentFrame_normal_displacement
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    (euclideanRigidMap (graphTangentFrame x₀ y₀ slope) p).2 - y₀ -
        slope * ((euclideanRigidMap
          (graphTangentFrame x₀ y₀ slope) p).1 - x₀) =
      p.2 * Real.sqrt (1 + slope ^ 2) := by
  rw [euclideanRigidMap_graphTangentFrame]
  rw [Real.cos_arctan, Real.sin_arctan]
  have hsqrt : Real.sqrt (1 + slope ^ 2) ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + slope ^ 2)]
  ring

/-- A tangent box with graph residual below its collar thickness is a certified
rigid projection patch for the strict subgraph. -/
noncomputable def subgraphTangentPatch
    (lam weight : ℝ) (f : ℝ → ℝ) (x₀ a b rho : ℝ)
    (hrho : 0 < rho)
    (hresidual : ∀ p ∈ Icc a b ×ˢ Icc (-2 * rho) (2 * rho),
      |f (euclideanRigidMap
            (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - f x₀ -
          deriv f x₀ *
            ((euclideanRigidMap
              (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - x₀)| <
        rho * Real.sqrt (1 + (deriv f x₀) ^ 2))
    (hdensity : ∀ q ∈ rigidProjectionBox
      (graphTangentFrame x₀ (f x₀) (deriv f x₀)) a b 0 rho,
      weight ≤ StripDensity lam q) :
    RigidProjectionPatch lam {q : PlanePoint | q.2 < f q.1} where
  frame := graphTangentFrame x₀ (f x₀) (deriv f x₀)
  a := a
  b := b
  y₀ := 0
  rho := rho
  weight := weight
  rho_pos := hrho
  lower_collar := by
    rintro _ ⟨p, hp, rfl⟩
    change p.1 ∈ Icc a b ∧
      p.2 ∈ Icc (0 - 2 * rho) (0 - rho) at hp
    norm_num at hp
    have hpfull : p ∈ Icc a b ×ˢ Icc (-2 * rho) (2 * rho) := by
      exact ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
    have hres := hresidual p hpfull
    have hnormal := graphTangentFrame_normal_displacement
      x₀ (f x₀) (deriv f x₀) p
    have hspeed : 0 < Real.sqrt (1 + (deriv f x₀) ^ 2) := by
      positivity
    have hpnormal :
        p.2 * Real.sqrt (1 + (deriv f x₀) ^ 2) ≤
          -rho * Real.sqrt (1 + (deriv f x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hp.2.2 hspeed.le
    change (euclideanRigidMap
      (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).2 <
        f (euclideanRigidMap
          (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1
    linarith [neg_abs_le (f (euclideanRigidMap
      (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - f x₀ -
        deriv f x₀ * ((euclideanRigidMap
          (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - x₀))]
  upper_collar := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hcarrier
    change p.1 ∈ Icc a b ∧
      p.2 ∈ Icc (0 + rho) (0 + 2 * rho) at hp
    norm_num at hp
    have hpfull : p ∈ Icc a b ×ˢ Icc (-2 * rho) (2 * rho) := by
      exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
    have hres := hresidual p hpfull
    have hnormal := graphTangentFrame_normal_displacement
      x₀ (f x₀) (deriv f x₀) p
    have hspeed : 0 < Real.sqrt (1 + (deriv f x₀) ^ 2) := by
      positivity
    have hpnormal :
        rho * Real.sqrt (1 + (deriv f x₀) ^ 2) ≤
          p.2 * Real.sqrt (1 + (deriv f x₀) ^ 2) :=
      mul_le_mul_of_nonneg_right hp.2.1 hspeed.le
    change (euclideanRigidMap
      (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).2 <
        f (euclideanRigidMap
          (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 at hcarrier
    linarith [le_abs_self (f (euclideanRigidMap
      (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - f x₀ -
        deriv f x₀ * ((euclideanRigidMap
          (graphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - x₀))]
  density_lower := hdensity

/-- Tangent coordinates with the normal directed into a strict supergraph. -/
def supergraphTangentFrame (x₀ y₀ slope : ℝ) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  (IsometryEquiv.neg EuclideanPlane).trans
    (graphTangentFrame x₀ y₀ slope)

@[simp] theorem euclideanRigidMap_supergraphTangentFrame
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    euclideanRigidMap (supergraphTangentFrame x₀ y₀ slope) p =
      euclideanRigidMap (graphTangentFrame x₀ y₀ slope) (-p.1, -p.2) := by
  rfl

/-- In the supergraph frame, negative local height is positive signed normal
height in the original tangent frame. -/
theorem supergraphTangentFrame_normal_displacement
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    (euclideanRigidMap (supergraphTangentFrame x₀ y₀ slope) p).2 - y₀ -
        slope * ((euclideanRigidMap
          (supergraphTangentFrame x₀ y₀ slope) p).1 - x₀) =
      -p.2 * Real.sqrt (1 + slope ^ 2) := by
  rw [euclideanRigidMap_supergraphTangentFrame]
  simpa using graphTangentFrame_normal_displacement
    x₀ y₀ slope (-p.1, -p.2)

/-- A tangent box with graph residual below its collar thickness is a certified
rigid projection patch for the strict supergraph. -/
noncomputable def supergraphTangentPatch
    (lam weight : ℝ) (f : ℝ → ℝ) (x₀ a b rho : ℝ)
    (hrho : 0 < rho)
    (hresidual : ∀ p ∈ Icc a b ×ˢ Icc (-2 * rho) (2 * rho),
      |f (euclideanRigidMap
            (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - f x₀ -
          deriv f x₀ *
            ((euclideanRigidMap
              (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - x₀)| <
        rho * Real.sqrt (1 + (deriv f x₀) ^ 2))
    (hdensity : ∀ q ∈ rigidProjectionBox
      (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) a b 0 rho,
      weight ≤ StripDensity lam q) :
    RigidProjectionPatch lam {q : PlanePoint | f q.1 < q.2} where
  frame := supergraphTangentFrame x₀ (f x₀) (deriv f x₀)
  a := a
  b := b
  y₀ := 0
  rho := rho
  weight := weight
  rho_pos := hrho
  lower_collar := by
    rintro _ ⟨p, hp, rfl⟩
    change p.1 ∈ Icc a b ∧
      p.2 ∈ Icc (0 - 2 * rho) (0 - rho) at hp
    norm_num at hp
    have hpfull : p ∈ Icc a b ×ˢ Icc (-2 * rho) (2 * rho) := by
      exact ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
    have hres := hresidual p hpfull
    have hnormal := supergraphTangentFrame_normal_displacement
      x₀ (f x₀) (deriv f x₀) p
    have hspeed : 0 < Real.sqrt (1 + (deriv f x₀) ^ 2) := by
      positivity
    have hpnormal :
        rho * Real.sqrt (1 + (deriv f x₀) ^ 2) ≤
          -p.2 * Real.sqrt (1 + (deriv f x₀) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hspeed.le
      linarith [hp.2.2]
    change f (euclideanRigidMap
      (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 <
        (euclideanRigidMap
          (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).2
    linarith [le_abs_self (f (euclideanRigidMap
      (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - f x₀ -
        deriv f x₀ * ((euclideanRigidMap
          (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - x₀))]
  upper_collar := by
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ hcarrier
    change p.1 ∈ Icc a b ∧
      p.2 ∈ Icc (0 + rho) (0 + 2 * rho) at hp
    norm_num at hp
    have hpfull : p ∈ Icc a b ×ˢ Icc (-2 * rho) (2 * rho) := by
      exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2⟩⟩
    have hres := hresidual p hpfull
    have hnormal := supergraphTangentFrame_normal_displacement
      x₀ (f x₀) (deriv f x₀) p
    have hspeed : 0 < Real.sqrt (1 + (deriv f x₀) ^ 2) := by
      positivity
    have hpnormal :
        -p.2 * Real.sqrt (1 + (deriv f x₀) ^ 2) ≤
          -rho * Real.sqrt (1 + (deriv f x₀) ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hspeed.le
      linarith [hp.2.1]
    change f (euclideanRigidMap
      (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 <
        (euclideanRigidMap
          (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).2 at hcarrier
    linarith [neg_abs_le (f (euclideanRigidMap
      (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - f x₀ -
        deriv f x₀ * ((euclideanRigidMap
          (supergraphTangentFrame x₀ (f x₀) (deriv f x₀)) p).1 - x₀))]
  density_lower := hdensity

/-- Source horizontal displacement is bounded by the local tangent
coordinates. -/
theorem abs_graphTangentFrame_fst_sub_le
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    |(euclideanRigidMap (graphTangentFrame x₀ y₀ slope) p).1 - x₀| ≤
      |p.1| + |p.2| := by
  simp only [euclideanRigidMap_graphTangentFrame]
  have hcos := Real.abs_cos_le_one (Real.arctan slope)
  have hsin := Real.abs_sin_le_one (Real.arctan slope)
  calc
    |x₀ + p.1 * Real.cos (Real.arctan slope) -
          p.2 * Real.sin (Real.arctan slope) - x₀| =
        |p.1 * Real.cos (Real.arctan slope) -
          p.2 * Real.sin (Real.arctan slope)| := by ring_nf
    _ ≤ |p.1 * Real.cos (Real.arctan slope)| +
          |p.2 * Real.sin (Real.arctan slope)| := abs_sub _ _
    _ = |p.1| * |Real.cos (Real.arctan slope)| +
          |p.2| * |Real.sin (Real.arctan slope)| := by
      rw [abs_mul, abs_mul]
    _ ≤ |p.1| * 1 + |p.2| * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hcos (abs_nonneg p.1))
        (mul_le_mul_of_nonneg_left hsin (abs_nonneg p.2))
    _ = |p.1| + |p.2| := by ring

/-- The normal-reversed frame has the same horizontal displacement bound. -/
theorem abs_supergraphTangentFrame_fst_sub_le
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    |(euclideanRigidMap (supergraphTangentFrame x₀ y₀ slope) p).1 - x₀| ≤
      |p.1| + |p.2| := by
  rw [euclideanRigidMap_supergraphTangentFrame]
  simpa only [abs_neg] using
    abs_graphTangentFrame_fst_sub_le x₀ y₀ slope (-p.1, -p.2)

/-- A tangent remainder estimate on a source neighborhood supplies the strict
residual inequality needed by a rigid tangent patch. -/
theorem tangentBox_residual_lt_of_bound
    (f : ℝ → ℝ) (x₀ slope h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (R : PlanePoint → PlanePoint)
    (hR : ∀ p, |(R p).1 - x₀| ≤ |p.1| + |p.2|)
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |f x - f x₀ - slope * (x - x₀)| ≤ ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho) :
    ∀ p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
      |f (R p).1 - f x₀ - slope * ((R p).1 - x₀)| <
        rho * Real.sqrt (1 + slope ^ 2) := by
  intro p hp
  have hp₁ : |p.1| ≤ h := abs_le.mpr ⟨hp.1.1, hp.1.2⟩
  have hp₂ : |p.2| ≤ 2 * rho :=
    abs_le.mpr ⟨by linarith [hp.2.1], hp.2.2⟩
  have hdx : |(R p).1 - x₀| ≤ h + 2 * rho :=
    (hR p).trans (add_le_add hp₁ hp₂)
  have hres := htangent (R p).1 hdx
  have hscaled :
      ε * |(R p).1 - x₀| ≤ ε * (h + 2 * rho) :=
    mul_le_mul_of_nonneg_left hdx hε
  have hspeed : 1 ≤ Real.sqrt (1 + slope ^ 2) := by
    have hsqrt_nonneg := Real.sqrt_nonneg (1 + slope ^ 2)
    have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + slope ^ 2)
    nlinarith [sq_nonneg slope]
  calc
    |f (R p).1 - f x₀ - slope * ((R p).1 - x₀)| ≤
        ε * |(R p).1 - x₀| := hres
    _ ≤ ε * (h + 2 * rho) := hscaled
    _ < rho := hsmall
    _ = rho * 1 := by ring
    _ ≤ rho * Real.sqrt (1 + slope ^ 2) :=
      mul_le_mul_of_nonneg_left hspeed hrho.le

/-- Uniform slope control on an interval gives a first-order tangent remainder
bound.  This is the analytic input for placing thin rigid projection boxes on
an arbitrary `C¹` graph; no curvature formula or circular model is used. -/
theorem abs_sub_tangent_le_of_deriv_close
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    {a b x₀ x ε : ℝ} (hx₀ : x₀ ∈ Icc a b) (hx : x ∈ Icc a b)
    (hclose : ∀ y ∈ Icc a b, |deriv f y - deriv f x₀| ≤ ε) :
    |f x - f x₀ - deriv f x₀ * (x - x₀)| ≤ ε * |x - x₀| := by
  let r : ℝ → ℝ :=
    fun y => f y - f x₀ - deriv f x₀ * (y - x₀)
  have hrderiv (y : ℝ) :
      HasDerivAt r (deriv f y - deriv f x₀) y := by
    have hlinear :
        HasDerivAt (fun z : ℝ => deriv f x₀ * (z - x₀))
          (deriv f x₀) y := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id y).sub_const x₀).const_mul (deriv f x₀)
    change HasDerivAt
      ((fun z : ℝ => f z - f x₀) -
        fun z : ℝ => deriv f x₀ * (z - x₀))
      (deriv f y - deriv f x₀) y
    exact ((hf y).hasDerivAt.sub_const (f x₀)).sub hlinear
  have hmvt :=
    (convex_Icc a b).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (C := ε)
      (fun y _hy => (hrderiv y).hasFDerivAt.hasFDerivWithinAt)
      (fun y hy => by
        rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
        exact hclose y hy)
      hx₀ hx
  simpa only [r, sub_self, mul_zero, sub_zero, Real.norm_eq_abs,
    Real.dist_eq] using hmvt

/-- A `C²` graph has one derivative-control scale on every compact interval.
Together with `abs_sub_tangent_le_of_deriv_close`, this gives a common
thinness scale for a finite family of tangent projection windows. -/
theorem exists_uniform_deriv_close_on_Icc
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) {a b ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₀ ∈ Icc a b, ∀ x ∈ Icc a b,
      |x - x₀| < δ → |deriv f x - deriv f x₀| < ε := by
  have huc : UniformContinuousOn (deriv f) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (hf.continuous_deriv (by norm_num)).continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hclose⟩ := huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ x hx hdist
  simpa only [Real.dist_eq] using hclose x hx x₀ hx₀ hdist

/-- On a compact interval, a `C²` graph lies in uniformly thin cones about all
of its tangent lines.  This is the graph-side geometric input for choosing a
single scale for a finite tangent-patch exhaustion. -/
theorem exists_uniform_tangent_remainder_on_Icc
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) {a b ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x₀ ∈ Icc a b, ∀ x ∈ Icc a b,
      |x - x₀| < δ →
        |f x - f x₀ - deriv f x₀ * (x - x₀)| ≤ ε * |x - x₀| := by
  obtain ⟨δ, hδ, hclose⟩ :=
    exists_uniform_deriv_close_on_Icc f hf hε
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ x hx hdist
  apply abs_sub_tangent_le_of_deriv_close
    (hf.differentiable (by norm_num))
    (a := min x₀ x) (b := max x₀ x)
    (by simp) (by simp)
  intro y hy
  have hyI : y ∈ Icc a b :=
    ordConnected_Icc.uIcc_subset hx₀ hx hy
  have hydist : |y - x₀| < δ := by
    rw [← Real.dist_eq, dist_comm]
    exact (Real.dist_left_le_of_mem_uIcc hy).trans_lt
      (by simpa only [Real.dist_eq, abs_sub_comm] using hdist)
  exact (hclose x₀ hx₀ y hyI hydist).le

/-- The global smoothing can be chosen with graph length on any prescribed
ordered interval within `epsilon * (b-a)` of the original `C²` graph length.
Thus passing to the literal `C∞` approximation class creates a removable
additive allowance, rather than a multiplicative perimeter distortion. -/
theorem exists_contDiff_infty_graphLength_close_anchor
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) {a b ε : ℝ}
    (hab : a ≤ b) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ g a = f a ∧
      (∀ x, |deriv g x - deriv f x| < ε) ∧
      (∀ x, |g x - f x| ≤ ε * |x - a|) ∧
      |(∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2)) -
          ∫ x in a..b, Real.sqrt (1 + (deriv f x) ^ 2)| ≤
        ε * (b - a) := by
  obtain ⟨g, hg, hga, hslope, hvalue⟩ :=
    exists_contDiff_infty_deriv_close_anchor f hf a hε
  refine ⟨g, hg, hga, hslope, hvalue, ?_⟩
  have hdg : Continuous (deriv g) := hg.continuous_deriv (by simp)
  have hdf : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hgc : Continuous
      (fun x => Real.sqrt (1 + (deriv g x) ^ 2)) :=
    (continuous_const.add (hdg.pow 2)).sqrt
  have hfc : Continuous
      (fun x => Real.sqrt (1 + (deriv f x) ^ 2)) :=
    (continuous_const.add (hdf.pow 2)).sqrt
  rw [← intervalIntegral.integral_sub
    (hgc.intervalIntegrable a b) (hfc.intervalIntegrable a b)]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := ε)
    (f := fun x => Real.sqrt (1 + (deriv g x) ^ 2) -
      Real.sqrt (1 + (deriv f x) ^ 2))
    (fun x _hx => by
      rw [Real.norm_eq_abs]
      exact (abs_graphSpeed_sub_graphSpeed_le
        (deriv g x) (deriv f x)).trans (hslope x).le)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hbound
  exact hbound

/-- A strict subgraph of a global smooth real function is a smooth domain. -/
theorem isSmoothDomain_subgraph {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsSmoothDomain {p : PlanePoint | p.2 < f p.1} := by
  let U : Set PlanePoint := {p | p.2 < f p.1}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_snd (hf.continuous.comp continuous_fst)
  refine ⟨hUopen, ?_⟩
  intro p hp
  let g : PlanePoint → ℝ := fun q => q.2 - f q.1
  let D : PlanePoint →L[ℝ] ℝ :=
    ContinuousLinearMap.snd ℝ ℝ ℝ -
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv f p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hfderiv : HasDerivAt f (deriv f p.1) p.1 :=
    (hf.differentiable (by simp) p.1).hasDerivAt
  have hgderiv : HasFDerivAt g D p := by
    change HasFDerivAt ((fun q : PlanePoint => q.2) - f ∘ Prod.fst) D p
    simpa [D] using (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub
      (hfderiv.hasFDerivAt.comp p
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p)))
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hzero
    norm_num [D] at happ
  have hboundary : p.2 = f p.1 :=
    frontier_lt_subset_eq continuous_snd
      (hf.continuous.comp continuous_fst) hp
  refine ⟨Set.univ, g, D, isOpen_univ, Set.mem_univ p, ?_, ?_,
    hgderiv, hD, ?_⟩
  · exact (contDiff_snd.sub (hf.comp contDiff_fst)).contDiffOn
  · dsimp [g]
    linarith
  · ext q
    simp only [Set.mem_inter_iff, Set.mem_univ, Set.mem_ofPred_eq,
      true_and, and_true, g]
    constructor <;> intro h <;> linarith

/-- A strict supergraph of a global smooth real function is a smooth domain. -/
theorem isSmoothDomain_supergraph {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    IsSmoothDomain {p : PlanePoint | f p.1 < p.2} := by
  let U : Set PlanePoint := {p | f p.1 < p.2}
  have hUopen : IsOpen U :=
    isOpen_lt (hf.continuous.comp continuous_fst) continuous_snd
  refine ⟨hUopen, ?_⟩
  intro p hp
  let g : PlanePoint → ℝ := fun q => f q.1 - q.2
  let D : PlanePoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.toSpanSingleton ℝ (deriv f p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfderiv : HasDerivAt f (deriv f p.1) p.1 :=
    (hf.differentiable (by simp) p.1).hasDerivAt
  have hgderiv : HasFDerivAt g D p := by
    change HasFDerivAt (f ∘ Prod.fst - fun q : PlanePoint => q.2) D p
    simpa [D] using
      (hfderiv.hasFDerivAt.comp p
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).sub
        (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hzero
    norm_num [D] at happ
  have hboundary : f p.1 = p.2 :=
    frontier_lt_subset_eq (hf.continuous.comp continuous_fst)
      continuous_snd hp
  refine ⟨Set.univ, g, D, isOpen_univ, Set.mem_univ p, ?_, ?_,
    hgderiv, hD, ?_⟩
  · exact ((hf.comp contDiff_fst).sub contDiff_snd).contDiffOn
  · dsimp [g]
    linarith
  · ext q
    simp only [Set.mem_inter_iff, Set.mem_univ, Set.mem_ofPred_eq,
      true_and, and_true, g]
    constructor <;> intro h <;> linarith

end CMVRelaxation

namespace CMVTwoPatchGraphVariation

namespace GraphPatch

/-- The genuinely open part of a protected graph tube.  Endpoint collars are
handled separately; this open neighborhood is the one on which frontier
locality applies without introducing vertical cut faces. -/
def openGraphTube (P : GraphPatch) (T : P.Tube) : Set PlanePoint :=
  {p | p.1 ∈ Ioo P.a P.b ∧ |p.2 - P.graph p.1| < T.radius}

theorem isOpen_openGraphTube (P : GraphPatch) (T : P.Tube) :
    IsOpen (P.openGraphTube T) := by
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_lt
      ((continuous_snd.sub
        (P.graph_contDiff.continuous.comp continuous_fst)).abs)
      continuous_const)

theorem openGraphTube_subset_graphTube (P : GraphPatch) (T : P.Tube) :
    P.openGraphTube T ⊆ P.graphTube T := by
  rintro p ⟨hx, hy⟩
  exact ⟨⟨hx.1, hx.2.le⟩, hy⟩

/-- The unbounded occupied side of a displayed boundary graph.  Local graph
tubes cut this model down to the literal ribbon. -/
def occupiedGraphDomain (P : GraphPatch) (g : ℝ → ℝ) : Set PlanePoint :=
  match P.side with
  | .below => {p | p.2 < g p.1}
  | .above => {p | g p.1 < p.2}

theorem isOpen_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : Continuous g) :
    IsOpen (P.occupiedGraphDomain g) := by
  cases hside : P.side with
  | below =>
      simp only [occupiedGraphDomain, hside]
      exact isOpen_lt continuous_snd (hg.comp continuous_fst)
  | above =>
      simp only [occupiedGraphDomain, hside]
      exact isOpen_lt (hg.comp continuous_fst) continuous_snd

private theorem frontier_subgraph {g : ℝ → ℝ} (hg : Continuous g) :
    frontier {p : PlanePoint | p.2 < g p.1} =
      (fun x : ℝ => (x, g x)) '' univ := by
  apply Set.Subset.antisymm
  · intro p hp
    have heq := frontier_lt_subset_eq continuous_snd
      (hg.comp continuous_fst) hp
    refine ⟨p.1, Set.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · exact heq.symm
  · rintro _ ⟨x, _hx, rfl⟩
    rw [frontier_eq_closure_inter_closure]
    constructor
    · let q : ℕ → PlanePoint := fun n =>
        (x, g x - 1 / (n + 1 : ℝ))
      have hy : Tendsto (fun n : ℕ => g x - 1 / (n + 1 : ℝ))
          atTop (𝓝 (g x)) := by
        simpa only [sub_zero] using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hq : Tendsto q atTop (𝓝 (x, g x)) :=
        tendsto_const_nhds.prodMk_nhds hy
      apply mem_closure_of_tendsto hq
      filter_upwards [] with n
      have hn : (0 : ℝ) < n + 1 := by positivity
      change g x - 1 / (n + 1 : ℝ) < g x
      linarith [div_pos zero_lt_one hn]
    · let q : ℕ → PlanePoint := fun n =>
        (x, g x + 1 / (n + 1 : ℝ))
      have hy : Tendsto (fun n : ℕ => g x + 1 / (n + 1 : ℝ))
          atTop (𝓝 (g x)) := by
        simpa only [add_zero] using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hq : Tendsto q atTop (𝓝 (x, g x)) :=
        tendsto_const_nhds.prodMk_nhds hy
      apply mem_closure_of_tendsto hq
      filter_upwards [] with n
      have hn : (0 : ℝ) < n + 1 := by positivity
      change ¬g x + 1 / (n + 1 : ℝ) < g x
      linarith [div_pos zero_lt_one hn]

private theorem frontier_supergraph {g : ℝ → ℝ} (hg : Continuous g) :
    frontier {p : PlanePoint | g p.1 < p.2} =
      (fun x : ℝ => (x, g x)) '' univ := by
  apply Set.Subset.antisymm
  · intro p hp
    have heq := frontier_lt_subset_eq (hg.comp continuous_fst)
      continuous_snd hp
    exact ⟨p.1, Set.mem_univ _, Prod.ext rfl heq⟩
  · rintro _ ⟨x, _hx, rfl⟩
    rw [frontier_eq_closure_inter_closure]
    constructor
    · let q : ℕ → PlanePoint := fun n =>
        (x, g x + 1 / (n + 1 : ℝ))
      have hy : Tendsto (fun n : ℕ => g x + 1 / (n + 1 : ℝ))
          atTop (𝓝 (g x)) := by
        simpa only [add_zero] using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hq : Tendsto q atTop (𝓝 (x, g x)) :=
        tendsto_const_nhds.prodMk_nhds hy
      apply mem_closure_of_tendsto hq
      filter_upwards [] with n
      have hn : (0 : ℝ) < n + 1 := by positivity
      change g x < g x + 1 / (n + 1 : ℝ)
      linarith [div_pos zero_lt_one hn]
    · let q : ℕ → PlanePoint := fun n =>
        (x, g x - 1 / (n + 1 : ℝ))
      have hy : Tendsto (fun n : ℕ => g x - 1 / (n + 1 : ℝ))
          atTop (𝓝 (g x)) := by
        simpa only [sub_zero] using tendsto_const_nhds.sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hq : Tendsto q atTop (𝓝 (x, g x)) :=
        tendsto_const_nhds.prodMk_nhds hy
      apply mem_closure_of_tendsto hq
      filter_upwards [] with n
      have hn : (0 : ℝ) < n + 1 := by positivity
      change ¬g x < g x - 1 / (n + 1 : ℝ)
      linarith [div_pos zero_lt_one hn]

/-- The complete frontier of either occupied graph side is exactly the graph.
The result is independent of the side orientation. -/
theorem frontier_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : Continuous g) :
    frontier (P.occupiedGraphDomain g) =
      (fun x : ℝ => (x, g x)) '' univ := by
  cases hside : P.side with
  | below =>
      simpa only [occupiedGraphDomain, hside] using frontier_subgraph hg
  | above =>
      simpa only [occupiedGraphDomain, hside] using frontier_supergraph hg

/-- A smooth occupied-side graph model belongs to the literal smooth-domain
class used by `relaxedPerimeter`. -/
theorem isSmoothDomain_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    CMVRelaxation.IsSmoothDomain (P.occupiedGraphDomain g) := by
  cases hside : P.side with
  | below =>
      simpa only [occupiedGraphDomain, hside] using
        CMVRelaxation.isSmoothDomain_subgraph hg
  | above =>
      simpa only [occupiedGraphDomain, hside] using
        CMVRelaxation.isSmoothDomain_supergraph hg

/-- A protected graph tube remains valid after halving its radius.  This is
used to reserve the other half for the `C²`-to-`C∞` smoothing displacement. -/
def Tube.half (P : GraphPatch) (T : P.Tube) : P.Tube where
  radius := T.radius / 2
  radius_pos := half_pos T.radius_pos
  order_clearance := by
    intro x hx
    have h := T.order_clearance x hx
    cases hside : P.side <;>
      simp only [hside] at h ⊢ <;>
      linarith [T.radius_pos]
  graph_lower_clearance := by
    intro x hx
    have h := T.graph_lower_clearance x hx
    linarith [T.radius_pos]
  graph_upper_clearance := by
    intro x hx
    have h := T.graph_upper_clearance x hx
    linarith [T.radius_pos]
  closed_tube_in_zone := by
    intro x hx y hy
    exact T.closed_tube_in_zone x hx y
      (hy.trans (half_le_self T.radius_pos.le))

/-- A `C²` varied graph in either constant-density zone has `C∞` graph
approximants whose literal weighted graph lengths differ by only a removable
additive allowance.  The estimate retains weight `1` or `lambda` exactly. -/
theorem exists_smoothGraph_weightedLength_close
    (P : GraphPatch) {lam : ℝ} (hlam : 1 < lam)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hzone : ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph v t x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      g P.a = P.variedGraph v t P.a ∧
      (∀ x, |deriv g x - deriv (P.variedGraph v t) x| < ε) ∧
      (∀ x, |g x - P.variedGraph v t x| ≤ ε * |x - P.a|) ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g x) ^ 2)) -
        weightedGraphLength lam P v t| ≤
        P.zone.weight lam * ε * (P.b - P.a) := by
  have hf : ContDiff ℝ 2 (P.variedGraph v t) := by
    change ContDiff ℝ 2 (fun x => P.graph x + t * v x)
    exact P.graph_contDiff.add (contDiff_const.mul hv)
  obtain ⟨g, hg, hga, hslope, hvalue, hlength⟩ :=
    CMVRelaxation.exists_contDiff_infty_graphLength_close_anchor
      (P.variedGraph v t) hf P.a_lt_b.le hε
  refine ⟨g, hg, hga, hslope, hvalue, ?_⟩
  rw [weightedGraphLength_eq_weight lam P hzone, ← mul_sub,
    abs_mul, abs_of_pos (DensityZone.weight_pos (zone := P.zone) hlam)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hlength
      (DensityZone.weight_pos (zone := P.zone) hlam).le

/-- If both the `C²` graph displacement and its smoothing allowance fit into
half of a protected tube, the smooth graph stays in that same tube and hence
in the same literal density zone.  This closes the `C²`/`C∞` and density
locality gap simultaneously. -/
theorem exists_smoothGraph_in_tube_weightedLength_close
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} (hlam : 1 < lam)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hshift : ∀ x ∈ Icc P.a P.b, |t * v x| ≤ T.radius / 2)
    {ε : ℝ} (hε : 0 < ε)
    (hfit : ε * (P.b - P.a) < T.radius / 2) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      g P.a = P.variedGraph v t P.a ∧
      (∀ x, |deriv g x - deriv (P.variedGraph v t) x| < ε) ∧
      (∀ x, |g x - P.variedGraph v t x| ≤ ε * |x - P.a|) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g x)) ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g x) ^ 2)) -
        weightedGraphLength lam P v t| ≤
        P.zone.weight lam * ε * (P.b - P.a) := by
  have hzone : ∀ x ∈ Ioc P.a P.b,
      P.zone.Contains (x, P.variedGraph v t x) := by
    intro x hx
    apply T.closed_tube_in_zone x ⟨hx.1.le, hx.2⟩
    have hs := hshift x ⟨hx.1.le, hx.2⟩
    simpa only [variedGraph, add_sub_cancel_left] using
      hs.trans (half_le_self T.radius_pos.le)
  obtain ⟨g, hg, hga, hslope, hvalue, hlength⟩ :=
    P.exists_smoothGraph_weightedLength_close hlam hv t hzone hε
  refine ⟨g, hg, hga, hslope, hvalue, ?_, hlength⟩
  intro x hx
  apply T.closed_tube_in_zone x hx
  have hxabs : |x - P.a| ≤ P.b - P.a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  have hclose : |g x - P.variedGraph v t x| < T.radius / 2 :=
    lt_of_le_of_lt (hvalue x)
      ((mul_le_mul_of_nonneg_left hxabs hε.le).trans_lt hfit)
  have hold : |P.variedGraph v t x - P.graph x| ≤ T.radius / 2 := by
    simpa only [variedGraph, add_sub_cancel_left] using hshift x hx
  exact (calc
    |g x - P.graph x| ≤
        |g x - P.variedGraph v t x| +
          |P.variedGraph v t x - P.graph x| := abs_sub_le _ _ _
    _ < T.radius / 2 + T.radius / 2 := add_lt_add_of_lt_of_le hclose hold
    _ = T.radius := by ring).le

/-- Every positive cost allowance admits a density-local `C∞` graph
approximation.  Both the geometric tube budget and the exact constant weight
are absorbed into the chosen slope tolerance. -/
theorem exists_smoothGraph_in_tube_weightedLength_lt
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} (hlam : 1 < lam)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hshift : ∀ x ∈ Icc P.a P.b, |t * v x| ≤ T.radius / 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      g P.a = P.variedGraph v t P.a ∧
      (∀ x ∈ Icc P.a P.b, |g x - P.graph x| < T.radius) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g x)) ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g x) ^ 2)) -
        weightedGraphLength lam P v t| < η := by
  let d := P.b - P.a
  let w := P.zone.weight lam
  have hd : 0 < d := sub_pos.mpr P.a_lt_b
  have hw : 0 < w := DensityZone.weight_pos (zone := P.zone) hlam
  let ε := min (T.radius / (4 * d)) (η / (2 * w * d))
  have hε : 0 < ε := lt_min
    (div_pos T.radius_pos (mul_pos (by norm_num) hd))
    (div_pos hη (mul_pos (mul_pos (by norm_num) hw) hd))
  have hfit : ε * (P.b - P.a) < T.radius / 2 := by
    change ε * d < T.radius / 2
    calc
      ε * d ≤ (T.radius / (4 * d)) * d :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hd.le
      _ = T.radius / 4 := by field_simp
      _ < T.radius / 2 := by linarith [T.radius_pos]
  obtain ⟨g, hg, hga, _hslope, hvalue, hzone, hlength⟩ :=
    P.exists_smoothGraph_in_tube_weightedLength_close
      T hlam hv t hshift hε hfit
  refine ⟨g, hg, hga, ?_, hzone, hlength.trans_lt ?_⟩
  · intro x hx
    have hxabs : |x - P.a| ≤ P.b - P.a := by
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [hx.2]
    have hsmooth : |g x - P.variedGraph v t x| < T.radius / 2 :=
      (hvalue x).trans_lt
        ((mul_le_mul_of_nonneg_left hxabs hε.le).trans_lt hfit)
    have hvaried :
        |P.variedGraph v t x - P.graph x| ≤ T.radius / 2 := by
      simpa only [variedGraph, add_sub_cancel_left] using hshift x hx
    calc
      |g x - P.graph x| ≤
          |g x - P.variedGraph v t x| +
            |P.variedGraph v t x - P.graph x| := abs_sub_le _ _ _
      _ < T.radius / 2 + T.radius / 2 :=
        add_lt_add_of_lt_of_le hsmooth hvaried
      _ = T.radius := by ring
  change w * ε * d < η
  calc
    w * ε * d ≤ w * (η / (2 * w * d)) * d := by
      gcongr
      exact min_le_right _ _
    _ = η / 2 := by field_simp
    _ < η := by linarith

/-- Inside its protected tube, a below-occupied ribbon is exactly the strict
subgraph of its displayed boundary graph. -/
theorem mem_carrier_iff_lt_graph_of_mem_graphTube
    (P : GraphPatch) (T : P.Tube) (hside : P.side = .below)
    {p : PlanePoint} (hp : p ∈ P.graphTube T) :
    p ∈ P.carrier ↔ p.2 < P.graph p.1 := by
  rcases hp with ⟨hx, hy⟩
  have hclear := T.order_clearance p.1 hx
  simp only [hside] at hclear
  have hlower := (abs_lt.mp hy).1
  simp only [carrier, hside, regionBetween, Set.mem_ofPred_eq, mem_Ioo]
  constructor
  · exact fun h => h.2.2
  · intro hgraph
    exact ⟨hx, by linarith, hgraph⟩

/-- Inside its protected tube, an above-occupied ribbon is exactly the strict
supergraph of its displayed boundary graph. -/
theorem mem_carrier_iff_graph_lt_of_mem_graphTube
    (P : GraphPatch) (T : P.Tube) (hside : P.side = .above)
    {p : PlanePoint} (hp : p ∈ P.graphTube T) :
    p ∈ P.carrier ↔ P.graph p.1 < p.2 := by
  rcases hp with ⟨hx, hy⟩
  have hclear := T.order_clearance p.1 hx
  simp only [hside] at hclear
  have hupper := (abs_lt.mp hy).2
  simp only [carrier, hside, regionBetween, Set.mem_ofPred_eq, mem_Ioo]
  constructor
  · exact fun h => h.2.1
  · intro hgraph
    exact ⟨hx, hgraph, by linarith⟩

/-- The same protected old tube identifies a below-occupied varied ribbon with
the strict subgraph of the varied graph. -/
theorem mem_variedCarrier_iff_lt_variedGraph_of_mem_graphTube
    (P : GraphPatch) (T : P.Tube) (hside : P.side = .below)
    (v : ℝ → ℝ) (t : ℝ) {p : PlanePoint} (hp : p ∈ P.graphTube T) :
    p ∈ P.variedCarrier v t ↔ p.2 < P.variedGraph v t p.1 := by
  rcases hp with ⟨hx, hy⟩
  have hclear := T.order_clearance p.1 hx
  simp only [hside] at hclear
  have hlower := (abs_lt.mp hy).1
  simp only [variedCarrier, hside, regionBetween, Set.mem_ofPred_eq, mem_Ioo]
  constructor
  · exact fun h => h.2.2
  · intro hgraph
    exact ⟨hx, by linarith, hgraph⟩

/-- The same protected old tube identifies an above-occupied varied ribbon with
the strict supergraph of the varied graph. -/
theorem mem_variedCarrier_iff_variedGraph_lt_of_mem_graphTube
    (P : GraphPatch) (T : P.Tube) (hside : P.side = .above)
    (v : ℝ → ℝ) (t : ℝ) {p : PlanePoint} (hp : p ∈ P.graphTube T) :
    p ∈ P.variedCarrier v t ↔ P.variedGraph v t p.1 < p.2 := by
  rcases hp with ⟨hx, hy⟩
  have hclear := T.order_clearance p.1 hx
  simp only [hside] at hclear
  have hupper := (abs_lt.mp hy).2
  simp only [variedCarrier, hside, regionBetween, Set.mem_ofPred_eq, mem_Ioo]
  constructor
  · exact fun h => h.2.1
  · intro hgraph
    exact ⟨hx, hgraph, by linarith⟩


/-- The side-specific collar statements combine into one exact local graph
model for either occupied-side orientation. -/
theorem mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
    (P : GraphPatch) (T : P.Tube) {p : PlanePoint}
    (hp : p ∈ P.graphTube T) :
    p ∈ P.carrier ↔ p ∈ P.occupiedGraphDomain P.graph := by
  cases hside : P.side with
  | below =>
      simpa only [occupiedGraphDomain, hside, Set.mem_ofPred_eq] using
        P.mem_carrier_iff_lt_graph_of_mem_graphTube T hside hp
  | above =>
      simpa only [occupiedGraphDomain, hside, Set.mem_ofPred_eq] using
        P.mem_carrier_iff_graph_lt_of_mem_graphTube T hside hp

open CMVRelaxation

/-- Side-oriented tangent frame for a graph patch. -/
def tangentFrame (P : GraphPatch) (x₀ : ℝ) :
    EuclideanPlane ≃ᵢ EuclideanPlane :=
  match P.side with
  | .below => graphTangentFrame x₀ (P.graph x₀) (deriv P.graph x₀)
  | .above => supergraphTangentFrame x₀ (P.graph x₀) (deriv P.graph x₀)

private theorem coordinateProjectionBox_subset_graphTube
    (P : GraphPatch) (T : P.Tube) (R : PlanePoint → PlanePoint)
    (x₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (hfst : ∀ p, |(R p).1 - x₀| ≤ |p.1| + |p.2|)
    (hnormal : ∀ p,
      |(R p).2 - P.graph x₀ -
          deriv P.graph x₀ * ((R p).1 - x₀)| =
        |p.2| * Real.sqrt (1 + (deriv P.graph x₀) ^ 2))
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho)
    (hleft : h + 2 * rho < x₀ - P.a)
    (hright : h + 2 * rho < P.b - x₀)
    (htube : 3 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) <
      T.radius) :
    R '' projectionBox (-h) h 0 rho ⊆ P.graphTube T := by
  rintro _ ⟨p, hp, rfl⟩
  change p.1 ∈ Icc (-h) h ∧
    p.2 ∈ Icc (0 - 2 * rho) (0 + 2 * rho) at hp
  have hpfull : p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho) := by
    exact ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hp₁ : |p.1| ≤ h := abs_le.mpr ⟨hp.1.1, hp.1.2⟩
  have hp₂ : |p.2| ≤ 2 * rho :=
    abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hdx : |(R p).1 - x₀| ≤ h + 2 * rho :=
    (hfst p).trans (add_le_add hp₁ hp₂)
  refine ⟨?_, ?_⟩
  · rw [mem_Ioc]
    have hb := abs_le.mp hdx
    constructor <;> linarith
  · have hres := tangentBox_residual_lt_of_bound
      P.graph x₀ (deriv P.graph x₀) h rho ε hrho hε R hfst
      htangent hsmall p hpfull
    let normal := (R p).2 - P.graph x₀ -
      deriv P.graph x₀ * ((R p).1 - x₀)
    let residual := P.graph (R p).1 - P.graph x₀ -
      deriv P.graph x₀ * ((R p).1 - x₀)
    have hnormal' : |normal| =
        |p.2| * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) := by
      exact hnormal p
    change |residual| <
      rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) at hres
    have hdecomp : (R p).2 - P.graph (R p).1 = normal - residual := by
      dsimp [normal, residual]
      ring
    rw [hdecomp]
    have hspeed : 0 ≤ Real.sqrt (1 + (deriv P.graph x₀) ^ 2) :=
      Real.sqrt_nonneg _
    calc
      |normal - residual| ≤ |normal| + |residual| := abs_sub _ _
      _ = |p.2| * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) +
          |residual| := by rw [hnormal']
      _ < 2 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) +
          rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) :=
        add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_right hp₂ hspeed) hres
      _ = 3 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) := by
        ring
      _ < T.radius := htube

/-- A tangent box whose horizontal and normal excursions fit the protected
interval and tube stays inside that tube. -/
theorem tangentProjectionBox_subset_graphTube
    (P : GraphPatch) (T : P.Tube) (x₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho)
    (hleft : h + 2 * rho < x₀ - P.a)
    (hright : h + 2 * rho < P.b - x₀)
    (htube : 3 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) <
      T.radius) :
    rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      P.graphTube T := by
  cases hside : P.side with
  | below =>
      simp only [tangentFrame, hside, rigidProjectionBox]
      apply coordinateProjectionBox_subset_graphTube P T _ x₀ h rho ε
        hrho hε (abs_graphTangentFrame_fst_sub_le
          x₀ (P.graph x₀) (deriv P.graph x₀))
      · intro p
        rw [graphTangentFrame_normal_displacement, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      · exact htangent
      · exact hsmall
      · exact hleft
      · exact hright
      · exact htube
  | above =>
      simp only [tangentFrame, hside, rigidProjectionBox]
      apply coordinateProjectionBox_subset_graphTube P T _ x₀ h rho ε
        hrho hε (abs_supergraphTangentFrame_fst_sub_le
          x₀ (P.graph x₀) (deriv P.graph x₀))
      · intro p
        rw [supergraphTangentFrame_normal_displacement, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_neg]
      · exact htangent
      · exact hsmall
      · exact hleft
      · exact hright
      · exact htube

/-- Every interior graph point admits a positive tangent scale whose complete
projection box remains in the protected tube. -/
theorem exists_tangentProjectionBox_in_graphTube
    (P : GraphPatch) (T : P.Tube) {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo P.a P.b) :
    ∃ r > 0,
      (∀ x, |x - x₀| ≤ r + 2 * r →
        |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
          (1 / 4 : ℝ) * |x - x₀|) ∧
      rigidProjectionBox (P.tangentFrame x₀) (-r) r 0 r ⊆
        P.graphTube T := by
  obtain ⟨δ, hδ, hrem⟩ :=
    exists_uniform_tangent_remainder_on_Icc P.graph
      (P.graph_contDiff.of_le (by norm_num)) (a := P.a) (b := P.b)
      (ε := (1 / 4 : ℝ)) (by norm_num)
  let speed := Real.sqrt (1 + (deriv P.graph x₀) ^ 2)
  have hspeed : 0 < speed := by
    dsimp [speed]
    positivity
  let B := min δ
    (min (x₀ - P.a) (min (P.b - x₀) (T.radius / speed)))
  have hB : 0 < B := by
    dsimp [B]
    exact lt_min hδ
      (lt_min (sub_pos.mpr hx₀.1)
        (lt_min (sub_pos.mpr hx₀.2) (div_pos T.radius_pos hspeed)))
  have hBδ : B ≤ δ := min_le_left _ _
  have hBleft : B ≤ x₀ - P.a :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hBright : B ≤ P.b - x₀ :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hBtube : B ≤ T.radius / speed :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
  let r := B / 8
  have hr : 0 < r := div_pos hB (by norm_num)
  have hrδ : r + 2 * r < δ := by
    dsimp [r]
    nlinarith
  have hrleft : r + 2 * r < x₀ - P.a := by
    dsimp [r]
    nlinarith
  have hrright : r + 2 * r < P.b - x₀ := by
    dsimp [r]
    nlinarith
  have hrtube : 3 * r * speed < T.radius := by
    have hBspeed : B * speed ≤ T.radius :=
      (le_div_iff₀ hspeed).mp hBtube
    dsimp [r]
    nlinarith [mul_pos hB hspeed]
  have htangent : ∀ x, |x - x₀| ≤ r + 2 * r →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        (1 / 4 : ℝ) * |x - x₀| := by
    intro x hx
    apply hrem x₀ ⟨hx₀.1.le, hx₀.2.le⟩ x
    · rw [mem_Icc]
      have hxb := abs_le.mp hx
      constructor <;> linarith
    · exact hx.trans_lt hrδ
  refine ⟨r, hr, htangent, ?_⟩
  apply P.tangentProjectionBox_subset_graphTube T x₀ r r (1 / 4 : ℝ)
    hr (by norm_num) htangent
  · nlinarith
  · exact hrleft
  · exact hrright
  · simpa only [speed] using hrtube

/-- Quantitative tangent data inside a protected tube yields a rigid projection
patch for any carrier agreeing there with the occupied graph side. -/
noncomputable def tangentRigidProjectionPatch
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} {E : Set PlanePoint}
    (x₀ h rho ε : ℝ) (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho)
    (hwindow : rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      P.graphTube T)
    (hlocal : ∀ q ∈ P.graphTube T,
      q ∈ P.occupiedGraphDomain P.graph ↔ q ∈ E) :
    RigidProjectionPatch lam E := by
  cases hside : P.side with
  | below =>
      simp only [tangentFrame, hside] at hwindow
      let Q₀ := subgraphTangentPatch lam (P.zone.weight lam) P.graph
        x₀ (-h) h rho hrho
        (tangentBox_residual_lt_of_bound P.graph x₀ (deriv P.graph x₀)
          h rho ε hrho hε _
          (abs_graphTangentFrame_fst_sub_le
            x₀ (P.graph x₀) (deriv P.graph x₀)) htangent hsmall)
        (by
          intro q hq
          have hqtube : q ∈ P.graphTube T := hwindow hq
          have hz := P.closedGraphTube_in_zone T
            (P.graphTube_subset_closedGraphTube T hqtube)
          rw [P.zone.stripDensity_eq_weight hz])
      apply Q₀.changeCarrierOnWindow
      intro q hq
      have hqtube : q ∈ P.graphTube T := by
        apply hwindow
        simpa [Q₀, RigidProjectionPatch.window,
          subgraphTangentPatch] using hq
      simpa [occupiedGraphDomain, hside] using hlocal q hqtube
  | above =>
      simp only [tangentFrame, hside] at hwindow
      let Q₀ := supergraphTangentPatch lam (P.zone.weight lam) P.graph
        x₀ (-h) h rho hrho
        (tangentBox_residual_lt_of_bound P.graph x₀ (deriv P.graph x₀)
          h rho ε hrho hε _
          (abs_supergraphTangentFrame_fst_sub_le
            x₀ (P.graph x₀) (deriv P.graph x₀)) htangent hsmall)
        (by
          intro q hq
          have hqtube : q ∈ P.graphTube T := hwindow hq
          have hz := P.closedGraphTube_in_zone T
            (P.graphTube_subset_closedGraphTube T hqtube)
          rw [P.zone.stripDensity_eq_weight hz])
      apply Q₀.changeCarrierOnWindow
      intro q hq
      have hqtube : q ∈ P.graphTube T := by
        apply hwindow
        simpa [Q₀, RigidProjectionPatch.window,
          supergraphTangentPatch] using hq
      simpa [occupiedGraphDomain, hside] using hlocal q hqtube

/-- The local tangent constructor specializes to the graph patch's literal
bounded ribbon carrier. -/
noncomputable def tangentRigidProjectionPatch_carrier
    (P : GraphPatch) (T : P.Tube) (lam : ℝ)
    (x₀ h rho ε : ℝ) (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho)
    (hwindow : rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      P.graphTube T) :
    RigidProjectionPatch lam P.carrier :=
  P.tangentRigidProjectionPatch T x₀ h rho ε hrho hε htangent hsmall
    hwindow (fun _ hp =>
      (P.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube T hp).symm)

/-- The varied ribbon has the corresponding exact occupied-side graph model
inside the same protected old tube. -/
theorem mem_variedCarrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
    (P : GraphPatch) (T : P.Tube) (v : ℝ → ℝ) (t : ℝ)
    {p : PlanePoint} (hp : p ∈ P.graphTube T) :
    p ∈ P.variedCarrier v t ↔
      p ∈ P.occupiedGraphDomain (P.variedGraph v t) := by
  cases hside : P.side with
  | below =>
      simpa only [occupiedGraphDomain, hside, Set.mem_ofPred_eq] using
        P.mem_variedCarrier_iff_lt_variedGraph_of_mem_graphTube
          T hside v t hp
  | above =>
      simpa only [occupiedGraphDomain, hside, Set.mem_ofPred_eq] using
        P.mem_variedCarrier_iff_variedGraph_lt_of_mem_graphTube
          T hside v t hp
end GraphPatch

/-- A closed support contained in a nonempty bounded open interval admits a
strictly smaller closed interval collar. -/
theorem exists_compact_interval_of_tsupport_subset
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hsub : tsupport f ⊆ Ioo a b) :
    ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧ tsupport f ⊆ Icc c d := by
  have hcompact : IsCompact (tsupport f) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
      (hsub.trans Ioo_subset_Icc_self)
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨xmin, hxmin, hmin⟩ :=
      hcompact.exists_isMinOn hne continuousOn_id
    obtain ⟨xmax, hxmax, hmax⟩ :=
      hcompact.exists_isMaxOn hne continuousOn_id
    obtain ⟨c, hc⟩ := exists_between (hsub hxmin).1
    obtain ⟨d, hd⟩ := exists_between (hsub hxmax).2
    refine ⟨c, d, hc.1, ?_, hd.2, ?_⟩
    · exact hc.2.trans_le ((hmin hxmax).trans hd.1.le)
    · intro x hx
      exact ⟨hc.2.le.trans (hmin hx), (hmax hx).trans hd.1.le⟩
  · refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, ?_, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · intro x hx
      exact (hne ⟨x, hx⟩).elim

namespace PrimaryVariation

/-- Every primary perturbation has an endpoint collar on which it vanishes. -/
theorem exists_compact_support_interval {P : GraphPatch}
    (V : PrimaryVariation P) :
    ∃ c d : ℝ, P.a < c ∧ c < d ∧ d < P.b ∧
      tsupport V ⊆ Icc c d :=
  exists_compact_interval_of_tsupport_subset P.a_lt_b V.tsupport_subset

end PrimaryVariation

/-- The normalized compensation perturbation also has an endpoint collar on
which it vanishes. -/
theorem exists_compact_support_interval_velocityTwo
    (lam : ℝ) (P₁ P₂ : GraphPatch) (V : PrimaryVariation P₁) :
    ∃ c d : ℝ, P₂.a < c ∧ c < d ∧ d < P₂.b ∧
      tsupport (velocityTwo lam P₁ P₂ V) ⊆ Icc c d :=
  exists_compact_interval_of_tsupport_subset P₂.a_lt_b
    (tsupport_velocityTwo_subset lam P₁ P₂ V)

namespace ActualTwoPatchData

private theorem firstTube_not_mem_fixedCarrier
    (A : ActualTwoPatchData) {p : PlanePoint}
    (hp : p ∈ A.patches.first.graphTube A.firstTube) :
    p ∉ A.fixedCarrier := by
  intro hfixed
  exact Set.disjoint_left.1 A.fixed_disjoint_closedGraphTubes hfixed
    (Or.inl (A.patches.first.graphTube_subset_closedGraphTube A.firstTube hp))

private theorem secondTube_not_mem_fixedCarrier
    (A : ActualTwoPatchData) {p : PlanePoint}
    (hp : p ∈ A.patches.second.graphTube A.secondTube) :
    p ∉ A.fixedCarrier := by
  intro hfixed
  exact Set.disjoint_left.1 A.fixed_disjoint_closedGraphTubes hfixed
    (Or.inr (A.patches.second.graphTube_subset_closedGraphTube A.secondTube hp))

private theorem firstTube_not_mem_secondVariedCarrier
    (A : ActualTwoPatchData) (v : ℝ → ℝ) (t : ℝ) {p : PlanePoint}
    (hp : p ∈ A.patches.first.graphTube A.firstTube) :
    p ∉ A.patches.second.variedCarrier v t := by
  intro hsecond
  exact Set.disjoint_left.1 A.patches.horizontal_disjoint
    ⟨hp.1.1.le, hp.1.2⟩
    ⟨(TwoPatchData.variedCarrier_fst_mem A.patches.second hsecond).1.le,
      (TwoPatchData.variedCarrier_fst_mem A.patches.second hsecond).2⟩

private theorem secondTube_not_mem_firstVariedCarrier
    (A : ActualTwoPatchData) (v : ℝ → ℝ) (t : ℝ) {p : PlanePoint}
    (hp : p ∈ A.patches.second.graphTube A.secondTube) :
    p ∉ A.patches.first.variedCarrier v t := by
  intro hfirst
  exact Set.disjoint_left.1 A.patches.horizontal_disjoint
    ⟨(TwoPatchData.variedCarrier_fst_mem A.patches.first hfirst).1.le,
      (TwoPatchData.variedCarrier_fst_mem A.patches.first hfirst).2⟩
    ⟨hp.1.1.le, hp.1.2⟩

/-- The literal actual carrier has exactly its first occupied graph side
throughout the first protected tube. -/
theorem mem_actualCarrier_iff_mem_firstCarrier_of_mem_graphTube
    (A : ActualTwoPatchData) {p : PlanePoint}
    (hp : p ∈ A.patches.first.graphTube A.firstTube) :
    p ∈ A.actualCarrier ↔ p ∈ A.patches.first.carrier := by
  rw [A.actualCarrier_eq_fixed_union]
  have hfixed := A.firstTube_not_mem_fixedCarrier hp
  have hsecondVaried := A.firstTube_not_mem_secondVariedCarrier
    A.patches.second.graph 0 hp
  have hsecond : p ∉ A.patches.second.carrier := by
    simpa only [GraphPatch.variedCarrier_zero] using hsecondVaried
  simp [hfixed, hsecond]

/-- The literal actual carrier has exactly its second occupied graph side
throughout the second protected tube. -/
theorem mem_actualCarrier_iff_mem_secondCarrier_of_mem_graphTube
    (A : ActualTwoPatchData) {p : PlanePoint}
    (hp : p ∈ A.patches.second.graphTube A.secondTube) :
    p ∈ A.actualCarrier ↔ p ∈ A.patches.second.carrier := by
  rw [A.actualCarrier_eq_fixed_union]
  have hfixed := A.secondTube_not_mem_fixedCarrier hp
  have hfirstVaried := A.secondTube_not_mem_firstVariedCarrier
    A.patches.first.graph 0 hp
  have hfirst : p ∉ A.patches.first.carrier := by
    simpa only [GraphPatch.variedCarrier_zero] using hfirstVaried
  simp [hfixed, hfirst]

/-- The varied actual carrier is exactly the first varied ribbon throughout the
first protected tube; arbitrary fixed geometry is absent there. -/
theorem mem_variedCarrier_iff_mem_firstVariedCarrier_of_mem_graphTube
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) (t : ℝ) {p : PlanePoint}
    (hp : p ∈ A.patches.first.graphTube A.firstTube) :
    p ∈ A.variedCarrier lam V t ↔
      p ∈ A.patches.first.variedCarrier V t := by
  have hfixed := A.firstTube_not_mem_fixedCarrier hp
  have hsecond := A.firstTube_not_mem_secondVariedCarrier
    (velocityTwo lam A.patches.first A.patches.second V) t hp
  simp [ActualTwoPatchData.variedCarrier, TwoPatchData.compensatedCarrier,
    TwoPatchData.variedCarrier, hfixed, hsecond]

/-- The varied actual carrier is exactly the second varied ribbon throughout
the second protected tube; arbitrary fixed geometry is absent there. -/
theorem mem_variedCarrier_iff_mem_secondVariedCarrier_of_mem_graphTube
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) (t : ℝ) {p : PlanePoint}
    (hp : p ∈ A.patches.second.graphTube A.secondTube) :
    p ∈ A.variedCarrier lam V t ↔
      p ∈ A.patches.second.variedCarrier
        (velocityTwo lam A.patches.first A.patches.second V) t := by
  have hfixed := A.secondTube_not_mem_fixedCarrier hp
  have hfirst := A.secondTube_not_mem_firstVariedCarrier V t hp
  simp [ActualTwoPatchData.variedCarrier, TwoPatchData.compensatedCarrier,
    TwoPatchData.variedCarrier, hfixed, hfirst]


/-- Exact local occupied-side model for the actual carrier in the first
protected graph tube. -/
theorem actualCarrier_inter_firstGraphTube
    (A : ActualTwoPatchData) :
    A.actualCarrier ∩ A.patches.first.graphTube A.firstTube =
      A.patches.first.occupiedGraphDomain A.patches.first.graph ∩
        A.patches.first.graphTube A.firstTube := by
  ext p
  by_cases hp : p ∈ A.patches.first.graphTube A.firstTube
  · simp only [Set.mem_inter_iff, hp, and_true]
    exact (A.mem_actualCarrier_iff_mem_firstCarrier_of_mem_graphTube hp).trans
      (A.patches.first.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        A.firstTube hp)
  · simp [hp]

/-- Exact local occupied-side model for the actual carrier in the second
protected graph tube. -/
theorem actualCarrier_inter_secondGraphTube
    (A : ActualTwoPatchData) :
    A.actualCarrier ∩ A.patches.second.graphTube A.secondTube =
      A.patches.second.occupiedGraphDomain A.patches.second.graph ∩
        A.patches.second.graphTube A.secondTube := by
  ext p
  by_cases hp : p ∈ A.patches.second.graphTube A.secondTube
  · simp only [Set.mem_inter_iff, hp, and_true]
    exact (A.mem_actualCarrier_iff_mem_secondCarrier_of_mem_graphTube hp).trans
      (A.patches.second.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        A.secondTube hp)
  · simp [hp]

/-- Exact local occupied-side model for the varied carrier in the first
protected graph tube. -/
theorem variedCarrier_inter_firstGraphTube
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) (t : ℝ) :
    A.variedCarrier lam V t ∩
        A.patches.first.graphTube A.firstTube =
      A.patches.first.occupiedGraphDomain
          (A.patches.first.variedGraph V t) ∩
        A.patches.first.graphTube A.firstTube := by
  ext p
  by_cases hp : p ∈ A.patches.first.graphTube A.firstTube
  · simp only [Set.mem_inter_iff, hp, and_true]
    exact
      (A.mem_variedCarrier_iff_mem_firstVariedCarrier_of_mem_graphTube
        lam V t hp).trans
      (GraphPatch.mem_variedCarrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        A.patches.first A.firstTube V t hp)
  · simp [hp]

/-- Exact local occupied-side model for the varied carrier in the second
protected graph tube. -/
theorem variedCarrier_inter_secondGraphTube
    (A : ActualTwoPatchData) (lam : ℝ)
    (V : PrimaryVariation A.patches.first) (t : ℝ) :
    A.variedCarrier lam V t ∩
        A.patches.second.graphTube A.secondTube =
      A.patches.second.occupiedGraphDomain
          (A.patches.second.variedGraph
            (velocityTwo lam A.patches.first A.patches.second V) t) ∩
        A.patches.second.graphTube A.secondTube := by
  ext p
  by_cases hp : p ∈ A.patches.second.graphTube A.secondTube
  · simp only [Set.mem_inter_iff, hp, and_true]
    exact
      (A.mem_variedCarrier_iff_mem_secondVariedCarrier_of_mem_graphTube
        lam V t hp).trans
      (GraphPatch.mem_variedCarrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        A.patches.second A.secondTube
        (velocityTwo lam A.patches.first A.patches.second V) t hp)
  · simp [hp]
end ActualTwoPatchData


/-! ## Common endpoint-collar smoothing -/

/-- A `C∞` cutoff which is zero before `c₀` and after `d₀`, and one
throughout `[c₁, d₁]`.  The separated four-cut form is used to make two
independently smoothed graph approximants agree on endpoint collars. -/
def graphBlendCutoff (c₀ c₁ d₁ d₀ x : ℝ) : ℝ :=
  Real.smoothTransition ((x - c₀) / (c₁ - c₀)) *
    Real.smoothTransition ((d₀ - x) / (d₀ - d₁))

theorem contDiff_graphBlendCutoff (c₀ c₁ d₁ d₀ : ℝ) :
    ContDiff ℝ ∞ (graphBlendCutoff c₀ c₁ d₁ d₀) := by
  unfold graphBlendCutoff
  exact
    (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub contDiff_id).div_const _))

theorem graphBlendCutoff_nonneg (c₀ c₁ d₁ d₀ x : ℝ) :
    0 ≤ graphBlendCutoff c₀ c₁ d₁ d₀ x :=
  mul_nonneg (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

theorem graphBlendCutoff_le_one (c₀ c₁ d₁ d₀ x : ℝ) :
    graphBlendCutoff c₀ c₁ d₁ d₀ x ≤ 1 := by
  unfold graphBlendCutoff
  nlinarith [Real.smoothTransition.nonneg ((x - c₀) / (c₁ - c₀)),
    Real.smoothTransition.le_one ((x - c₀) / (c₁ - c₀)),
    Real.smoothTransition.nonneg ((d₀ - x) / (d₀ - d₁)),
    Real.smoothTransition.le_one ((d₀ - x) / (d₀ - d₁))]

theorem graphBlendCutoff_eq_zero_of_le_left
    {c₀ c₁ d₁ d₀ x : ℝ} (hc : c₀ < c₁) (hx : x ≤ c₀) :
    graphBlendCutoff c₀ c₁ d₁ d₀ x = 0 := by
  unfold graphBlendCutoff
  rw [Real.smoothTransition.zero_of_nonpos]
  · exact zero_mul _
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
      (sub_nonneg.mpr hc.le)

theorem graphBlendCutoff_eq_zero_of_right_le
    {c₀ c₁ d₁ d₀ x : ℝ} (hd : d₁ < d₀) (hx : d₀ ≤ x) :
    graphBlendCutoff c₀ c₁ d₁ d₀ x = 0 := by
  unfold graphBlendCutoff
  have hz :
      Real.smoothTransition ((d₀ - x) / (d₀ - d₁)) = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
        (sub_nonneg.mpr hd.le))
  rw [hz, mul_zero]

theorem graphBlendCutoff_eq_one
    {c₀ c₁ d₁ d₀ x : ℝ} (hc : c₀ < c₁) (hd : d₁ < d₀)
    (hx : x ∈ Icc c₁ d₁) :
    graphBlendCutoff c₀ c₁ d₁ d₀ x = 1 := by
  unfold graphBlendCutoff
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le,
    one_mul]
  · exact (one_le_div₀ (sub_pos.mpr hd)).2 (by linarith [hx.2])
  · exact (one_le_div₀ (sub_pos.mpr hc)).2 (by linarith [hx.1])

theorem deriv_graphBlendCutoff_eq_zero_of_lt_left
    {c₀ c₁ d₁ d₀ x : ℝ} (hc : c₀ < c₁) (hx : x < c₀) :
    deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x = 0 := by
  have heq : graphBlendCutoff c₀ c₁ d₁ d₀ =ᶠ[𝓝 x]
      fun _ : ℝ => 0 := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact graphBlendCutoff_eq_zero_of_le_left hc hy.le
  simpa using heq.deriv_eq

theorem deriv_graphBlendCutoff_eq_zero_of_right_lt
    {c₀ c₁ d₁ d₀ x : ℝ} (hd : d₁ < d₀) (hx : d₀ < x) :
    deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x = 0 := by
  have heq : graphBlendCutoff c₀ c₁ d₁ d₀ =ᶠ[𝓝 x]
      fun _ : ℝ => 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact graphBlendCutoff_eq_zero_of_right_le hd hy.le
  simpa using heq.deriv_eq

/-- The gluing cutoff has a finite global slope bound, constructed internally
from compactness and its constant exterior pieces. -/
theorem exists_graphBlendCutoff_deriv_bound
    {c₀ c₁ d₁ d₀ : ℝ} (hc : c₀ < c₁) (hd : d₁ < d₀) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ x : ℝ, |deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x| ≤ D := by
  have hcontinuous : Continuous
      (fun x : ℝ => |deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x|) :=
    ((contDiff_graphBlendCutoff c₀ c₁ d₁ d₀).continuous_deriv
      (by simp)).abs
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcontinuous.continuousOn)
  refine ⟨max 1 M, le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc c₀ d₀
  · exact (hM _ (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  · rw [mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [deriv_graphBlendCutoff_eq_zero_of_lt_left hc (lt_of_not_ge hx),
        abs_zero]
      exact le_trans (by norm_num) (le_max_left _ _)
    · rw [deriv_graphBlendCutoff_eq_zero_of_right_lt hd (lt_of_not_ge hx),
        abs_zero]
      exact le_trans (by norm_num) (le_max_left _ _)

/-- Smoothly splice an independently smoothed replacement graph into a common
old graph, using the endpoint-collar cutoff. -/
def blendGraphs (c₀ c₁ d₁ d₀ : ℝ) (g₀ g₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  g₀ x + graphBlendCutoff c₀ c₁ d₁ d₀ x * (g₁ x - g₀ x)

theorem contDiff_blendGraphs
    {c₀ c₁ d₁ d₀ : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hg₀ : ContDiff ℝ ∞ g₀) (hg₁ : ContDiff ℝ ∞ g₁) :
    ContDiff ℝ ∞ (blendGraphs c₀ c₁ d₁ d₀ g₀ g₁) := by
  unfold blendGraphs
  exact hg₀.add ((contDiff_graphBlendCutoff c₀ c₁ d₁ d₀).mul
    (hg₁.sub hg₀))

theorem blendGraphs_eq_left
    {c₀ c₁ d₁ d₀ x : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hc : c₀ < c₁) (hx : x ≤ c₀) :
    blendGraphs c₀ c₁ d₁ d₀ g₀ g₁ x = g₀ x := by
  rw [blendGraphs, graphBlendCutoff_eq_zero_of_le_left hc hx]
  ring

theorem blendGraphs_eq_right
    {c₀ c₁ d₁ d₀ x : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hd : d₁ < d₀) (hx : d₀ ≤ x) :
    blendGraphs c₀ c₁ d₁ d₀ g₀ g₁ x = g₀ x := by
  rw [blendGraphs, graphBlendCutoff_eq_zero_of_right_le hd hx]
  ring

theorem blendGraphs_eq_inner
    {c₀ c₁ d₁ d₀ x : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hc : c₀ < c₁) (hd : d₁ < d₀) (hx : x ∈ Icc c₁ d₁) :
    blendGraphs c₀ c₁ d₁ d₀ g₀ g₁ x = g₁ x := by
  rw [blendGraphs, graphBlendCutoff_eq_one hc hd hx]
  ring

/-- Exact derivative of the smooth graph splice.  The middle term is the only
transition cost; it is controlled by the cutoff slope and the `C⁰` separation
of the two anchored approximants. -/
theorem deriv_blendGraphs
    {c₀ c₁ d₁ d₀ x : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hg₀ : ContDiff ℝ ∞ g₀) (hg₁ : ContDiff ℝ ∞ g₁) :
    deriv (blendGraphs c₀ c₁ d₁ d₀ g₀ g₁) x =
      deriv g₀ x +
        deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x * (g₁ x - g₀ x) +
        graphBlendCutoff c₀ c₁ d₁ d₀ x *
          (deriv g₁ x - deriv g₀ x) := by
  have hcut : DifferentiableAt ℝ
      (graphBlendCutoff c₀ c₁ d₁ d₀) x :=
    (contDiff_graphBlendCutoff c₀ c₁ d₁ d₀).differentiable
      (by simp) x
  have hg₀d : DifferentiableAt ℝ g₀ x := hg₀.differentiable (by simp) x
  have hg₁d : DifferentiableAt ℝ g₁ x := hg₁.differentiable (by simp) x
  unfold blendGraphs
  change deriv
      (g₀ + graphBlendCutoff c₀ c₁ d₁ d₀ * (g₁ - g₀)) x = _
  rw [deriv_add hg₀d (hcut.mul (hg₁d.sub hg₀d)),
    deriv_mul hcut (hg₁d.sub hg₀d), deriv_sub hg₁d hg₀d]
  simp only [Pi.sub_apply]
  ring

theorem deriv_graphBlendCutoff_eq_zero_of_eq_one
    {c₀ c₁ d₁ d₀ x : ℝ}
    (hx : graphBlendCutoff c₀ c₁ d₁ d₀ x = 1) :
    deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x = 0 := by
  have hmax : IsLocalMax (graphBlendCutoff c₀ c₁ d₁ d₀) x := by
    filter_upwards [] with y
    rw [hx]
    exact graphBlendCutoff_le_one c₀ c₁ d₁ d₀ y
  exact hmax.hasDerivAt_eq_zero
    ((contDiff_graphBlendCutoff c₀ c₁ d₁ d₀).differentiable
      (by simp) x).hasDerivAt

theorem deriv_blendGraphs_eq_inner
    {c₀ c₁ d₁ d₀ x : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hc : c₀ < c₁) (hd : d₁ < d₀) (hx : x ∈ Icc c₁ d₁)
    (hg₀ : ContDiff ℝ ∞ g₀) (hg₁ : ContDiff ℝ ∞ g₁) :
    deriv (blendGraphs c₀ c₁ d₁ d₀ g₀ g₁) x = deriv g₁ x := by
  rw [deriv_blendGraphs hg₀ hg₁,
    deriv_graphBlendCutoff_eq_zero_of_eq_one
      (graphBlendCutoff_eq_one hc hd hx),
    graphBlendCutoff_eq_one hc hd hx]
  ring

/-- A convex graph splice is no farther from a common reference value than
the worse of its two endpoint graphs. -/
theorem abs_blendGraphs_sub_le
    {c₀ c₁ d₁ d₀ x z A : ℝ} {g₀ g₁ : ℝ → ℝ}
    (h₀ : |g₀ x - z| ≤ A) (h₁ : |g₁ x - z| ≤ A) :
    |blendGraphs c₀ c₁ d₁ d₀ g₀ g₁ x - z| ≤ A := by
  let q := graphBlendCutoff c₀ c₁ d₁ d₀ x
  have hq0 : 0 ≤ q := graphBlendCutoff_nonneg _ _ _ _ _
  have hq1 : q ≤ 1 := graphBlendCutoff_le_one _ _ _ _ _
  have heq :
      blendGraphs c₀ c₁ d₁ d₀ g₀ g₁ x - z =
        (1 - q) * (g₀ x - z) + q * (g₁ x - z) := by
    simp only [blendGraphs, q]
    ring
  rw [heq]
  calc
    |(1 - q) * (g₀ x - z) + q * (g₁ x - z)| ≤
        |(1 - q) * (g₀ x - z)| + |q * (g₁ x - z)| := abs_add_le _ _
    _ = (1 - q) * |g₀ x - z| + q * |g₁ x - z| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq0,
        abs_of_nonneg (sub_nonneg.mpr hq1)]
    _ ≤ (1 - q) * A + q * A := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr hq1))
        (mul_le_mul_of_nonneg_left h₁ hq0)
    _ = A := by ring

/-- Pointwise slope control for a smooth graph splice.  The only extra term is
the cutoff derivative times the value separation of the two anchored
approximants. -/
theorem abs_deriv_blendGraphs_sub_le
    {c₀ c₁ d₁ d₀ x p ε D B : ℝ} {g₀ g₁ : ℝ → ℝ}
    (hg₀ : ContDiff ℝ ∞ g₀) (hg₁ : ContDiff ℝ ∞ g₁)
    (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hcut : |deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x| ≤ D)
    (hsep : |g₁ x - g₀ x| ≤ B)
    (h₀ : |deriv g₀ x - p| ≤ ε)
    (h₁ : |deriv g₁ x - p| ≤ ε) :
    |deriv (blendGraphs c₀ c₁ d₁ d₀ g₀ g₁) x - p| ≤
      3 * ε + D * B := by
  let q := graphBlendCutoff c₀ c₁ d₁ d₀ x
  have hq0 : 0 ≤ q := graphBlendCutoff_nonneg _ _ _ _ _
  have hq1 : q ≤ 1 := graphBlendCutoff_le_one _ _ _ _ _
  have hB : 0 ≤ B := (abs_nonneg (g₁ x - g₀ x)).trans hsep
  have hdiff :
      |(deriv g₁ x - p) - (deriv g₀ x - p)| ≤ 2 * ε := by
    calc
      |(deriv g₁ x - p) - (deriv g₀ x - p)| ≤
          |deriv g₁ x - p| + |deriv g₀ x - p| := abs_sub _ _
      _ ≤ ε + ε := add_le_add h₁ h₀
      _ = 2 * ε := by ring
  have hcutTerm :
      |deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x *
          (g₁ x - g₀ x)| ≤ D * B := by
    rw [abs_mul]
    exact mul_le_mul hcut hsep (abs_nonneg _) hD
  have hconvexTerm :
      |q * ((deriv g₁ x - p) - (deriv g₀ x - p))| ≤ 2 * ε := by
    rw [abs_mul, abs_of_nonneg hq0]
    calc
      q * |(deriv g₁ x - p) - (deriv g₀ x - p)| ≤ q * (2 * ε) :=
        mul_le_mul_of_nonneg_left hdiff hq0
      _ ≤ 1 * (2 * ε) :=
        mul_le_mul_of_nonneg_right hq1 (mul_nonneg (by norm_num) hε)
      _ = 2 * ε := one_mul _
  have heq :
      deriv (blendGraphs c₀ c₁ d₁ d₀ g₀ g₁) x - p =
        (deriv g₀ x - p) +
          deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x * (g₁ x - g₀ x) +
          q * ((deriv g₁ x - p) - (deriv g₀ x - p)) := by
    rw [deriv_blendGraphs hg₀ hg₁]
    simp only [q]
    ring
  rw [heq]
  calc
    |(deriv g₀ x - p) +
        deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x * (g₁ x - g₀ x) +
        q * ((deriv g₁ x - p) - (deriv g₀ x - p))| ≤
      |deriv g₀ x - p| +
        |deriv (graphBlendCutoff c₀ c₁ d₁ d₀) x * (g₁ x - g₀ x)| +
        |q * ((deriv g₁ x - p) - (deriv g₀ x - p))| := by
          exact (abs_add_le _ _).trans (by
            gcongr
            exact abs_add_le _ _)
    _ ≤ ε + D * B + 2 * ε :=
      add_le_add (add_le_add h₀ hcutTerm) hconvexTerm
    _ = 3 * ε + D * B := by ring

namespace PrimaryVariation

/-- Outside any closed interval containing its topological support, a primary
variation and its derivative both vanish.  The derivative statement uses an
actual zero neighborhood, not only pointwise support containment. -/
theorem eq_zero_and_deriv_eq_zero_of_not_mem_support_interval
    {P : GraphPatch} (V : PrimaryVariation P) {c d x : ℝ}
    (hsupport : tsupport V ⊆ Icc c d) (hx : x ∉ Icc c d) :
    V x = 0 ∧ deriv V x = 0 := by
  have heq : V =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    by_contra hne
    exact hy (hsupport (subset_tsupport V hne))
  constructor
  · simpa using heq.eq_of_nhds
  · simpa using heq.deriv_eq

end PrimaryVariation

namespace GraphPatch

/-- A compactly supported `C²` graph replacement admits old and new `C∞`
approximants which agree on both endpoint collars, converge uniformly to their
respective literal graphs, stay in the same protected constant-density tube,
and approximate the two literal weighted graph lengths to any prescribed
additive accuracy.

The common endpoint graph is constructed by blending two independently
anchored smooth approximants.  The cutoff-transition cost is controlled
explicitly by its internally bounded derivative and therefore vanishes with
the smoothing tolerance. -/
theorem exists_common_smoothGraphs_in_tube_weightedLength_lt
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} (hlam : 1 < lam)
    (V : PrimaryVariation P) (t : ℝ)
    (hshift : ∀ x ∈ Icc P.a P.b, |t * V x| ≤ T.radius / 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ (g₀ g₁ : ℝ → ℝ) (c₀ d₀ : ℝ),
      P.a < c₀ ∧ c₀ < d₀ ∧ d₀ < P.b ∧
      ContDiff ℝ ∞ g₀ ∧ ContDiff ℝ ∞ g₁ ∧
      (∀ x, x ≤ c₀ → g₁ x = g₀ x) ∧
      (∀ x, d₀ ≤ x → g₁ x = g₀ x) ∧
      (∀ x ∈ Icc P.a P.b, |g₀ x - P.graph x| < η) ∧
      (∀ x ∈ Icc P.a P.b, |g₁ x - P.variedGraph V t x| < η) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g₀ x)) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g₁ x)) ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₀ x) ^ 2)) -
        weightedGraphLength lam P V 0| < η ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₁ x) ^ 2)) -
        weightedGraphLength lam P V t| < η := by
  obtain ⟨c, d, hac, hcd, hdb, hsupport⟩ :=
    V.exists_compact_support_interval
  obtain ⟨c₀, hac₀, hc₀c⟩ := exists_between hac
  obtain ⟨d₀, hdd₀, hd₀b⟩ := exists_between hdb
  obtain ⟨D, hDone, hDbound⟩ :=
    exists_graphBlendCutoff_deriv_bound hc₀c hdd₀
  let Δ := P.b - P.a
  let w := P.zone.weight lam
  let C := 3 + 2 * D * Δ
  have hΔ : 0 < Δ := sub_pos.mpr P.a_lt_b
  have hw : 0 < w := DensityZone.weight_pos hlam
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hDone
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hCone : 1 ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hD.le hΔ.le]
  let ε := min (T.radius / (4 * Δ))
    (min (η / (2 * w * C * Δ)) (η / (2 * Δ)))
  have hε : 0 < ε := lt_min
    (div_pos T.radius_pos (mul_pos (by norm_num) hΔ))
    (lt_min
      (div_pos hη (mul_pos (mul_pos (mul_pos (by norm_num) hw) hC) hΔ))
      (div_pos hη (mul_pos (by norm_num) hΔ)))
  have hεΔ : ε * Δ < T.radius / 2 := by
    calc
      ε * Δ ≤ (T.radius / (4 * Δ)) * Δ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hΔ.le
      _ = T.radius / 4 := by field_simp
      _ < T.radius / 2 := by linarith [T.radius_pos]
  have hcostAllowance : w * (ε * C * Δ) < η := by
    calc
      w * (ε * C * Δ) ≤
          w * ((η / (2 * w * C * Δ)) * C * Δ) := by
            gcongr
            exact (min_le_right _ _).trans (min_le_left _ _)
      _ = η / 2 := by field_simp
      _ < η := by linarith
  have hvalueAllowance : ε * Δ < η := by
    calc
      ε * Δ ≤ (η / (2 * Δ)) * Δ := by
        gcongr
        exact (min_le_right _ _).trans (min_le_right _ _)
      _ = η / 2 := by field_simp
      _ < η := by linarith
  obtain ⟨g₀, hg₀, hg₀a, hslope₀, hvalue₀, hlength₀⟩ :=
    CMVRelaxation.exists_contDiff_infty_graphLength_close_anchor
      P.graph P.graph_contDiff P.a_lt_b.le hε
  have hvaried : ContDiff ℝ 2 (P.variedGraph V t) := by
    change ContDiff ℝ 2 (fun x => P.graph x + t * V x)
    exact P.graph_contDiff.add (contDiff_const.mul V.contDiff)
  obtain ⟨gRaw, hgRaw, hgRawA, hslopeRaw, hvalueRaw, _hlengthRaw⟩ :=
    CMVRelaxation.exists_contDiff_infty_graphLength_close_anchor
      (P.variedGraph V t) hvaried P.a_lt_b.le hε
  let g₁ := blendGraphs c₀ c d d₀ g₀ gRaw
  have hg₁ : ContDiff ℝ ∞ g₁ :=
    contDiff_blendGraphs hg₀ hgRaw
  have hxΔ {x : ℝ} (hx : x ∈ Icc P.a P.b) :
      |x - P.a| ≤ Δ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    dsimp only [Δ]
    linarith [hx.2]
  have hvalue₀' {x : ℝ} (hx : x ∈ Icc P.a P.b) :
      |g₀ x - P.graph x| ≤ ε * Δ :=
    (hvalue₀ x).trans
      (mul_le_mul_of_nonneg_left (hxΔ hx) hε.le)
  have hvalueRaw' {x : ℝ} (hx : x ∈ Icc P.a P.b) :
      |gRaw x - P.variedGraph V t x| ≤ ε * Δ :=
    (hvalueRaw x).trans
      (mul_le_mul_of_nonneg_left (hxΔ hx) hε.le)
  have hvalue₁ {x : ℝ} (hx : x ∈ Icc P.a P.b) :
      |g₁ x - P.variedGraph V t x| ≤ ε * Δ := by
    by_cases hxcd : x ∈ Icc c d
    · rw [show g₁ x = gRaw x by
        exact blendGraphs_eq_inner hc₀c hdd₀ hxcd]
      exact hvalueRaw' hx
    · obtain ⟨hVx, _hVderiv⟩ :=
        V.eq_zero_and_deriv_eq_zero_of_not_mem_support_interval
          hsupport hxcd
      have htarget : P.variedGraph V t x = P.graph x := by
        simp [GraphPatch.variedGraph, hVx]
      rw [htarget]
      apply abs_blendGraphs_sub_le
      · exact hvalue₀' hx
      · simpa only [htarget] using hvalueRaw' hx
  have hzoneTarget :
      ∀ x ∈ Ioc P.a P.b,
        P.zone.Contains (x, P.variedGraph V t x) := by
    intro x hx
    apply T.closed_tube_in_zone x ⟨hx.1.le, hx.2⟩
    simpa only [GraphPatch.variedGraph, add_sub_cancel_left] using
      (hshift x ⟨hx.1.le, hx.2⟩).trans
        (half_le_self T.radius_pos.le)
  have hzone₀ :
      ∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g₀ x) := by
    intro x hx
    apply T.closed_tube_in_zone x hx
    exact (hvalue₀' hx).trans
      (le_of_lt (hεΔ.trans (half_lt_self T.radius_pos)))
  have hzone₁ :
      ∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g₁ x) := by
    intro x hx
    apply T.closed_tube_in_zone x hx
    exact le_of_lt <| calc
      |g₁ x - P.graph x| ≤
          |g₁ x - P.variedGraph V t x| +
            |P.variedGraph V t x - P.graph x| := abs_sub_le _ _ _
      _ ≤ ε * Δ + T.radius / 2 := by
        exact add_le_add (hvalue₁ hx)
          (by simpa only [GraphPatch.variedGraph, add_sub_cancel_left] using
            hshift x hx)
      _ < T.radius / 2 + T.radius / 2 :=
        add_lt_add_of_lt_of_le hεΔ le_rfl
      _ = T.radius := by ring
  have hzoneZero :
      ∀ x ∈ Ioc P.a P.b,
        P.zone.Contains (x, P.variedGraph V 0 x) := by
    intro x hx
    simpa only [P.variedGraph_zero V] using
      T.closed_tube_in_zone x ⟨hx.1.le, hx.2⟩ (P.graph x) (by
        simpa using T.radius_pos.le)
  have holdCost :
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₀ x) ^ 2)) -
        weightedGraphLength lam P V 0| < η := by
    rw [weightedGraphLength_eq_weight lam P hzoneZero, ← mul_sub,
      abs_mul, abs_of_pos hw]
    rw [P.variedGraph_zero V]
    apply lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hlength₀ hw.le)
    calc
      w * (ε * Δ) ≤ w * (ε * C * Δ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (by nlinarith [hCone, hε]) hΔ.le)
          hw.le
      _ < η := hcostAllowance
  have hslope₁ :
      ∀ x ∈ Icc P.a P.b,
        |deriv g₁ x - deriv (P.variedGraph V t) x| ≤ ε * C := by
    intro x hx
    by_cases hxcd : x ∈ Icc c d
    · rw [show deriv g₁ x = deriv gRaw x by
        exact deriv_blendGraphs_eq_inner hc₀c hdd₀ hxcd hg₀ hgRaw]
      exact (hslopeRaw x).le.trans
        (by have := hCone
            nlinarith [hε])
    · obtain ⟨hVx, hVderiv⟩ :=
        V.eq_zero_and_deriv_eq_zero_of_not_mem_support_interval
          hsupport hxcd
      have htarget : P.variedGraph V t x = P.graph x := by
        simp [GraphPatch.variedGraph, hVx]
      have htargetDeriv :
          deriv (P.variedGraph V t) x = deriv P.graph x := by
        rw [deriv_variedGraph P (V.contDiff.differentiable (by norm_num)) t x,
          hVderiv]
        ring
      have hsep : |gRaw x - g₀ x| ≤ 2 * ε * Δ := by
        calc
          |gRaw x - g₀ x| ≤
              |gRaw x - P.graph x| + |P.graph x - g₀ x| :=
            abs_sub_le _ _ _
          _ ≤ ε * Δ + ε * Δ := by
            rw [← abs_neg (P.graph x - g₀ x), neg_sub]
            exact add_le_add
              (by simpa only [htarget] using hvalueRaw' hx)
              (hvalue₀' hx)
          _ = 2 * ε * Δ := by ring
      rw [htargetDeriv]
      have hrawSlope : |deriv gRaw x - deriv P.graph x| ≤ ε := by
        simpa only [htargetDeriv] using (hslopeRaw x).le
      exact (abs_deriv_blendGraphs_sub_le hg₀ hgRaw hε.le hD.le
        (hDbound x) hsep (hslope₀ x).le hrawSlope).trans (by
          dsimp only [C]
          ring_nf
          exact le_rfl)
  have hlength₁ :
      |(∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₁ x) ^ 2)) -
          ∫ x in P.a..P.b,
            Real.sqrt (1 + (deriv (P.variedGraph V t) x) ^ 2)| ≤
        ε * C * Δ := by
    have hg₁c : Continuous (fun x =>
        Real.sqrt (1 + (deriv g₁ x) ^ 2)) :=
      (continuous_const.add
        ((hg₁.continuous_deriv (by simp)).pow 2)).sqrt
    have hvariedc : Continuous (fun x =>
        Real.sqrt (1 + (deriv (P.variedGraph V t) x) ^ 2)) :=
      (continuous_const.add
        ((hvaried.continuous_deriv (by norm_num)).pow 2)).sqrt
    rw [← intervalIntegral.integral_sub
      (hg₁c.intervalIntegrable P.a P.b)
      (hvariedc.intervalIntegrable P.a P.b)]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := P.a) (b := P.b) (C := ε * C)
      (f := fun x => Real.sqrt (1 + (deriv g₁ x) ^ 2) -
        Real.sqrt (1 + (deriv (P.variedGraph V t) x) ^ 2))
      (fun x hx => by
        have hx' : x ∈ Icc P.a P.b := by
          have hxIoc : x ∈ Ioc P.a P.b := by
            simpa [Set.uIoc_of_le P.a_lt_b.le] using hx
          exact ⟨hxIoc.1.le, hxIoc.2⟩
        rw [Real.norm_eq_abs]
        exact (CMVRelaxation.abs_graphSpeed_sub_graphSpeed_le
          (deriv g₁ x) (deriv (P.variedGraph V t) x)).trans
          (hslope₁ x hx'))
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr P.a_lt_b.le)] at hbound
    simpa only [Δ, mul_assoc] using hbound
  have hnewCost :
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₁ x) ^ 2)) -
        weightedGraphLength lam P V t| < η := by
    rw [weightedGraphLength_eq_weight lam P hzoneTarget, ← mul_sub,
      abs_mul, abs_of_pos hw]
    exact (mul_le_mul_of_nonneg_left hlength₁ hw.le).trans_lt
      hcostAllowance
  refine ⟨g₀, g₁, c₀, d₀, hac₀, hc₀c.trans (hcd.trans hdd₀),
    hd₀b, hg₀, hg₁, ?_, ?_, ?_, ?_, hzone₀, hzone₁,
    holdCost, hnewCost⟩
  · intro x hx
    exact blendGraphs_eq_left hc₀c hx
  · intro x hx
    exact blendGraphs_eq_right hdd₀ hx
  · intro x hx
    exact (hvalue₀' hx).trans_lt hvalueAllowance
  · intro x hx
    exact (hvalue₁ hx).trans_lt hvalueAllowance

end GraphPatch
end CMVTwoPatchGraphVariation

namespace CMVRelaxation

/-- Closed vertical band between two graphs over a base set. -/
def closedGraphBand (g h : ℝ → ℝ) (s : Set ℝ) : Set PlanePoint :=
  {p | p.1 ∈ s ∧
    p.2 ∈ Icc (min (g p.1) (h p.1)) (max (g p.1) (h p.1))}

lemma measurableSet_closedGraphBand {g h : ℝ → ℝ} {s : Set ℝ}
    (hg : Measurable g) (hh : Measurable h) (hs : MeasurableSet s) :
    MeasurableSet (closedGraphBand g h s) := by
  simpa only [closedGraphBand] using
    measurableSet_region_between_cc (hg.min hh) (hg.max hh) hs

/-- The planar volume of a closed vertical graph band is the integral of the
pointwise graph separation. -/
lemma volume_closedGraphBand {g h : ℝ → ℝ} {s : Set ℝ}
    (hg : Measurable g) (hh : Measurable h) (hs : MeasurableSet s) :
    volume (closedGraphBand g h s) =
      ∫⁻ x in s, ENNReal.ofReal |g x - h x| := by
  classical
  rw [Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_closedGraphBand hg hh hs)]
  have hsection :
      (fun x => volume (Prod.mk x ⁻¹' closedGraphBand g h s)) =
        s.indicator (fun x => ENNReal.ofReal |g x - h x|) := by
    funext x
    rw [indicator_apply]
    split_ifs with hx
    · have hfiber : Prod.mk x ⁻¹' closedGraphBand g h s =
          Icc (min (g x) (h x)) (max (g x) (h x)) := by
        ext y
        simp [closedGraphBand, hx]
      rw [hfiber, Real.volume_Icc, max_sub_min_eq_abs, abs_sub_comm]
    · have hfiber : Prod.mk x ⁻¹' closedGraphBand g h s = ∅ := by
        ext y
        simp [closedGraphBand, hx]
      simp [hfiber]
  rw [hsection, lintegral_indicator hs]

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

lemma occupiedGraphDomain_symmDiff_inter_prod_subset_closedGraphBand
    (P : GraphPatch) (g h : ℝ → ℝ) (s : Set ℝ) :
    (P.occupiedGraphDomain g ∆ P.occupiedGraphDomain h) ∩
        (s ×ˢ (univ : Set ℝ)) ⊆ closedGraphBand g h s := by
  intro p hp
  rcases hp with ⟨hp, hps⟩
  have hxs : p.1 ∈ s := hps.1
  change p.1 ∈ s ∧
    min (g p.1) (h p.1) ≤ p.2 ∧
    p.2 ≤ max (g p.1) (h p.1)
  refine ⟨hxs, ?_⟩
  cases hside : P.side
  · simp only [GraphPatch.occupiedGraphDomain, hside,
      Set.mem_symmDiff, Set.mem_ofPred_eq] at hp
    rcases hp with hp | hp
    · exact ⟨(min_le_right _ _).trans (le_of_not_gt hp.2),
        hp.1.le.trans (le_max_left _ _)⟩
    · exact ⟨(min_le_left _ _).trans (le_of_not_gt hp.2),
        hp.1.le.trans (le_max_right _ _)⟩
  · simp only [GraphPatch.occupiedGraphDomain, hside,
      Set.mem_symmDiff, Set.mem_ofPred_eq] at hp
    rcases hp with hp | hp
    · exact ⟨(min_le_left _ _).trans hp.1.le,
        (le_of_not_gt hp.2).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans hp.1.le,
        (le_of_not_gt hp.2).trans (le_max_left _ _)⟩

/-- Uniform graph convergence controls the local planar mismatch of the two
occupied-side models. -/
theorem volume_occupiedGraphDomain_symmDiff_inter_prod_le
    (P : GraphPatch) {g h : ℝ → ℝ} {s : Set ℝ}
    (hg : Measurable g) (hh : Measurable h) (hs : MeasurableSet s) :
    volume ((P.occupiedGraphDomain g ∆ P.occupiedGraphDomain h) ∩
      (s ×ˢ (univ : Set ℝ))) ≤
        ∫⁻ x in s, ENNReal.ofReal |g x - h x| := by
  rw [← volume_closedGraphBand hg hh hs]
  exact measure_mono
    (P.occupiedGraphDomain_symmDiff_inter_prod_subset_closedGraphBand g h s)

theorem volume_occupiedGraphDomain_symmDiff_inter_prod_le_of_uniform
    (P : GraphPatch) {g h : ℝ → ℝ} {s : Set ℝ}
    (hg : Measurable g) (hh : Measurable h) (hs : MeasurableSet s)
    {δ : ℝ} (hbound : ∀ x ∈ s, |g x - h x| ≤ δ) :
    volume ((P.occupiedGraphDomain g ∆ P.occupiedGraphDomain h) ∩
      (s ×ˢ (univ : Set ℝ))) ≤ ENNReal.ofReal δ * volume s := by
  refine (P.volume_occupiedGraphDomain_symmDiff_inter_prod_le hg hh hs).trans ?_
  rw [← setLIntegral_const]
  exact setLIntegral_mono measurable_const fun x hx =>
    ENNReal.ofReal_le_ofReal (hbound x hx)

theorem volume_local_occupiedGraphDomain_symmDiff_le_of_uniform
    (P : GraphPatch) {g h : ℝ → ℝ}
    (hg : Measurable g) (hh : Measurable h) {δ : ℝ}
    (hbound : ∀ x ∈ Icc P.a P.b, |g x - h x| ≤ δ) :
    volume ((P.occupiedGraphDomain g ∆ P.occupiedGraphDomain h) ∩
      (Icc P.a P.b ×ˢ (univ : Set ℝ))) ≤
        ENNReal.ofReal δ * ENNReal.ofReal (P.b - P.a) := by
  simpa only [Real.volume_Icc] using
    P.volume_occupiedGraphDomain_symmDiff_inter_prod_le_of_uniform
      hg hh measurableSet_Icc hbound

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVRelaxation

/-- One vertical fiber of a planar set. -/
def verticalSection (S : Set PlanePoint) (x : ℝ) : Set ℝ :=
  Prod.mk x ⁻¹' S

/-- The source vertical line at horizontal coordinate `x`. -/
def verticalLine (x : ℝ) : Set PlanePoint := {p | p.1 = x}

/-- The Euclidean realization of one source vertical line. -/
def euclideanVerticalEmbedding (x : ℝ) : ℝ → EuclideanPlane :=
  fun y => planeEuclideanHomeomorph (x, y)

lemma isometry_euclideanVerticalEmbedding (x : ℝ) :
    Isometry (euclideanVerticalEmbedding x) := by
  apply Isometry.of_dist_eq
  intro y z
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  norm_num [euclideanVerticalEmbedding, Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow]
  rw [Real.sqrt_sq_eq_abs]

/-- A vertical seam's Euclidean `H¹` mass is exactly the volume of its
one-dimensional source section. -/
theorem hausdorffMeasure_verticalLine_inter (S : Set PlanePoint) (x : ℝ) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (verticalLine x ∩ S)) =
      volume (verticalSection S x) := by
  have himage :
      planeEuclideanHomeomorph '' (verticalLine x ∩ S) =
        euclideanVerticalEmbedding x '' verticalSection S x := by
    ext q
    constructor
    · rintro ⟨⟨px, py⟩, ⟨hpx, hpS⟩, rfl⟩
      change px = x at hpx
      subst px
      exact ⟨py, hpS, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(x, y), ⟨rfl, hy⟩, rfl⟩
  rw [himage]
  calc
    (μH[1] : Measure EuclideanPlane)
        (euclideanVerticalEmbedding x '' verticalSection S x) =
      (μH[1] : Measure ℝ) (verticalSection S x) :=
        (isometry_euclideanVerticalEmbedding x).hausdorffMeasure_image
          (Or.inl (by norm_num)) _
    _ = volume (verticalSection S x) := by rw [hausdorffMeasure_real]

/-- One-dimensional mismatch on a vertical seam. -/
def verticalSliceVolume (S : Set PlanePoint) (x : ℝ) : ENNReal :=
  volume (verticalSection S x)

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

/-- For either occupied side, vertical symmetric-difference mass is exactly
the height mismatch of the two boundary graphs. -/
theorem verticalSliceVolume_occupiedGraphDomain_symmDiff
    (P : GraphPatch) (g h : ℝ → ℝ) (x : ℝ) :
    verticalSliceVolume (P.occupiedGraphDomain g ∆
      P.occupiedGraphDomain h) x = ENNReal.ofReal |g x - h x| := by
  cases hside : P.side with
  | below =>
      rw [verticalSliceVolume]
      rw [show verticalSection (P.occupiedGraphDomain g ∆
            P.occupiedGraphDomain h) x =
          Ico (min (g x) (h x)) (max (g x) (h x)) by
        ext y
        rcases le_total (g x) (h x) with hgh | hhg
        · simp [verticalSection, occupiedGraphDomain, hside, symmDiff_def,
            hgh]; grind
        · simp [verticalSection, occupiedGraphDomain, hside, symmDiff_def,
            hhg]; grind]
      rw [Real.volume_Ico, max_sub_min_eq_abs]
      exact congrArg ENNReal.ofReal (abs_sub_comm (h x) (g x))
  | above =>
      rw [verticalSliceVolume]
      rw [show verticalSection (P.occupiedGraphDomain g ∆
            P.occupiedGraphDomain h) x =
          Ioc (min (g x) (h x)) (max (g x) (h x)) by
        ext y
        rcases le_total (g x) (h x) with hgh | hhg
        · simp [verticalSection, occupiedGraphDomain, hside, symmDiff_def,
            hgh]; grind
        · simp [verticalSection, occupiedGraphDomain, hside, symmDiff_def,
            hhg]; grind]
      rw [Real.volume_Ioc, max_sub_min_eq_abs]
      exact congrArg ENNReal.ofReal (abs_sub_comm (h x) (g x))

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVRelaxation

lemma measurable_verticalSliceVolume {S : Set PlanePoint}
    (hS : MeasurableSet S) :
    Measurable (verticalSliceVolume S) :=
  measurable_measure_prodMk_left hS

/-- Planar volume is the integral of the vertical slice volumes. -/
lemma volume_eq_lintegral_verticalSliceVolume {S : Set PlanePoint}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ x : ℝ, verticalSliceVolume S x := by
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  rfl

/-- In every nonempty horizontal collar, some vertical seam has mismatch no
larger than the collar average. -/
theorem exists_verticalSliceVolume_le_average
    {S : Set PlanePoint} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b,
      verticalSliceVolume S x ≤ volume S / ENNReal.ofReal (b - a) := by
  have hmeas : AEMeasurable (verticalSliceVolume S)
      (volume.restrict (Ioo a b)) :=
    (measurable_verticalSliceVolume hS).aemeasurable
  have hvol0 : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab))
  have hvolTop : volume (Ioo a b) ≠ ⊤ := measure_Ioo_lt_top.ne
  obtain ⟨x, hx, hxle⟩ := exists_le_setLAverage hvol0 hvolTop hmeas
  refine ⟨x, hx, hxle.trans ?_⟩
  rw [setLAverage_eq, Real.volume_Ioo]
  gcongr
  calc
    (∫⁻ y in Ioo a b, verticalSliceVolume S y) ≤
        ∫⁻ y, verticalSliceVolume S y :=
      setLIntegral_le_lintegral _ _
    _ = volume S := (volume_eq_lintegral_verticalSliceVolume hS).symm

/-- Applied to a symmetric difference, seam mismatch is controlled directly by
literal characteristic-function distance. -/
theorem exists_verticalSeam_disagreement_le
    {U E : Set PlanePoint} (hU : MeasurableSet U) (hE : MeasurableSet E)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b,
      volume (verticalSection (U ∆ E) x) ≤
        characteristicDistance U E / ENNReal.ofReal (b - a) := by
  simpa only [verticalSliceVolume, characteristicDistance] using
    exists_verticalSliceVolume_le_average (hU.symmDiff hE) hab

/-- Along every literal smooth recovery sequence, one can select a seam in any
fixed positive-width collar whose one-dimensional mismatch vanishes. -/
theorem SmoothSequence.exists_verticalSeams_tendsto_zero
    {E : Set PlanePoint} (hE : MeasurableSet E) (A : SmoothSequence)
    (hconv : A.ConvergesTo E) {a b : ℝ} (hab : a < b) :
    ∃ x : ℕ → ℝ,
      (∀ n, x n ∈ Ioo a b) ∧
      Tendsto (fun n =>
        volume (verticalSection (A.carrier n ∆ E) (x n)))
        atTop (𝓝 0) := by
  have hchoose : ∀ n : ℕ, ∃ x ∈ Ioo a b,
      volume (verticalSection (A.carrier n ∆ E) x) ≤
        characteristicDistance (A.carrier n) E /
          ENNReal.ofReal (b - a) := by
    intro n
    exact exists_verticalSeam_disagreement_le
      (A.smooth n).isOpen.measurableSet hE hab
  choose x hx hbound using hchoose
  refine ⟨x, hx, ?_⟩
  have hright : Tendsto
      (fun n => characteristicDistance (A.carrier n) E /
        ENNReal.ofReal (b - a)) atTop (𝓝 0) := by
    rw [show (fun n => characteristicDistance (A.carrier n) E /
        ENNReal.ofReal (b - a)) =
      fun n => (ENNReal.ofReal (b - a))⁻¹ *
        characteristicDistance (A.carrier n) E by
          funext n
          rw [ENNReal.div_eq_inv_mul]]
    simpa using ENNReal.Tendsto.const_mul hconv
      (Or.inr (ENNReal.inv_ne_top.2
        (ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab)))))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hright (fun _ => bot_le) hbound

/-- The two endpoint collars needed for graph cut-and-paste can be selected
simultaneously; the sum of their seam mismatches still vanishes. -/
theorem SmoothSequence.exists_two_verticalSeams_tendsto_zero
    {E : Set PlanePoint} (hE : MeasurableSet E) (A : SmoothSequence)
    (hconv : A.ConvergesTo E)
    {a₀ a₁ b₁ b₀ : ℝ} (ha : a₀ < a₁) (hb : b₁ < b₀) :
    ∃ (left right : ℕ → ℝ),
      (∀ n, left n ∈ Ioo a₀ a₁) ∧
      (∀ n, right n ∈ Ioo b₁ b₀) ∧
      Tendsto (fun n =>
        volume (verticalSection (A.carrier n ∆ E) (left n)) +
          volume (verticalSection (A.carrier n ∆ E) (right n)))
        atTop (𝓝 0) := by
  obtain ⟨left, hleft, hleft0⟩ :=
    A.exists_verticalSeams_tendsto_zero hE hconv ha
  obtain ⟨right, hright, hright0⟩ :=
    A.exists_verticalSeams_tendsto_zero hE hconv hb
  exact ⟨left, right, hleft, hright, by
    simpa using hleft0.add hright0⟩

/-- The two selected mismatch seams have vanishing total Euclidean length. -/
theorem SmoothSequence.exists_two_verticalSeamLengths_tendsto_zero
    {E : Set PlanePoint} (hE : MeasurableSet E) (A : SmoothSequence)
    (hconv : A.ConvergesTo E)
    {a₀ a₁ b₁ b₀ : ℝ} (ha : a₀ < a₁) (hb : b₁ < b₀) :
    ∃ (left right : ℕ → ℝ),
      (∀ n, left n ∈ Ioo a₀ a₁) ∧
      (∀ n, right n ∈ Ioo b₁ b₀) ∧
      Tendsto (fun n =>
        (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              (verticalLine (left n) ∩ (A.carrier n ∆ E))) +
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              (verticalLine (right n) ∩ (A.carrier n ∆ E))))
        atTop (𝓝 0) := by
  obtain ⟨left, right, hleft, hright, hzero⟩ :=
    A.exists_two_verticalSeams_tendsto_zero hE hconv ha hb
  refine ⟨left, right, hleft, hright, ?_⟩
  simpa only [hausdorffMeasure_verticalLine_inter] using hzero

/-- Replace a set inside a window while retaining another set outside.  This is
the raw set operation underlying local graph cut-and-paste; smooth seam repair
is a separate geometric step. -/
def spliceIn (outside inside window : Set PlanePoint) : Set PlanePoint :=
  (outside \ window) ∪ (inside ∩ window)

lemma spliceIn_inter_window (U G W : Set PlanePoint) :
    spliceIn U G W ∩ W = G ∩ W := by
  ext p
  by_cases hpW : p ∈ W <;> simp [spliceIn, hpW]

lemma spliceIn_inter_compl (U G W : Set PlanePoint) :
    spliceIn U G W ∩ Wᶜ = U ∩ Wᶜ := by
  ext p
  by_cases hpW : p ∈ W <;> simp [spliceIn, hpW]

/-- A raw splice has exactly the inserted local cost on an open window. -/
theorem smoothCostOn_spliceIn_eq_inside
    (lam : ℝ) (U G : Set PlanePoint) {W : Set PlanePoint}
    (hW : IsOpen W) :
    smoothCostOn lam (spliceIn U G W) W = smoothCostOn lam G W :=
  smoothCostOn_eq_of_inter_open_eq lam hW (spliceIn_inter_window U G W)

/-- A raw splice retains exactly the outside local cost when the replacement
window is closed. -/
theorem smoothCostOn_spliceIn_eq_outside
    (lam : ℝ) (U G : Set PlanePoint) {W : Set PlanePoint}
    (hW : IsClosed W) :
    smoothCostOn lam (spliceIn U G W) Wᶜ = smoothCostOn lam U Wᶜ :=
  smoothCostOn_eq_of_inter_open_eq lam hW.isOpen_compl
    (spliceIn_inter_compl U G W)

lemma spliceIn_eq_open_union_of_agree_near_frontier
    {U G W N : Set PlanePoint} (hfrontier : frontier W ⊆ N)
    (hlocal : U ∩ N = G ∩ N) :
    spliceIn U G W =
      (G ∩ interior W) ∪ (U ∩ interior Wᶜ) ∪ (U ∩ N) := by
  ext p
  change ((p ∈ U ∧ p ∉ W) ∨ (p ∈ G ∧ p ∈ W)) ↔
    ((p ∈ G ∧ p ∈ interior W) ∨
      (p ∈ U ∧ p ∈ interior Wᶜ)) ∨ (p ∈ U ∧ p ∈ N)
  have hintW : p ∈ interior W → p ∈ W := fun hp => interior_subset hp
  have hintWc : p ∈ interior Wᶜ → p ∉ W :=
    fun hp => interior_subset hp
  by_cases hpN : p ∈ N
  · have hmem : p ∈ U ↔ p ∈ G := by
      have hp := Set.ext_iff.mp hlocal p
      simpa only [mem_inter_iff, hpN, and_true] using hp
    tauto
  · have hpFrontier : p ∉ frontier W := fun hp => hpN (hfrontier hp)
    by_cases hpW : p ∈ W
    · have hpInt : p ∈ interior W := by
        by_contra hpNotInt
        exact hpFrontier
          ((mem_frontier_iff_notMem_interior hpW).2 hpNotInt)
      tauto
    · have hpWc : p ∈ Wᶜ := hpW
      have hpFrontierc : p ∉ frontier Wᶜ := by
        simpa only [frontier_compl] using hpFrontier
      have hpIntc : p ∈ interior Wᶜ := by
        by_contra hpNotIntc
        exact hpFrontierc
          ((mem_frontier_iff_notMem_interior hpWc).2 hpNotIntc)
      tauto

lemma spliceIn_inter_interior (U G W : Set PlanePoint) :
    spliceIn U G W ∩ interior W = G ∩ interior W := by
  ext p
  change (((p ∈ U ∧ p ∉ W) ∨ (p ∈ G ∧ p ∈ W)) ∧
    p ∈ interior W) ↔ p ∈ G ∧ p ∈ interior W
  have hintW : p ∈ interior W → p ∈ W := fun hp => interior_subset hp
  tauto

lemma spliceIn_inter_interior_compl (U G W : Set PlanePoint) :
    spliceIn U G W ∩ interior Wᶜ = U ∩ interior Wᶜ := by
  ext p
  change (((p ∈ U ∧ p ∉ W) ∨ (p ∈ G ∧ p ∈ W)) ∧
    p ∈ interior Wᶜ) ↔ p ∈ U ∧ p ∈ interior Wᶜ
  have hintWc : p ∈ interior Wᶜ → p ∉ W :=
    fun hp => interior_subset hp
  tauto

lemma spliceIn_inter_eq_of_agree
    {U G W N : Set PlanePoint} (hlocal : U ∩ N = G ∩ N) :
    spliceIn U G W ∩ N = U ∩ N := by
  ext p
  change (((p ∈ U ∧ p ∉ W) ∨ (p ∈ G ∧ p ∈ W)) ∧ p ∈ N) ↔
    p ∈ U ∧ p ∈ N
  have hmem (hpN : p ∈ N) : p ∈ U ↔ p ∈ G := by
    have hp := Set.ext_iff.mp hlocal p
    simpa only [mem_inter_iff, hpN, and_true] using hp
  by_cases hpN : p ∈ N
  · have := hmem hpN
    tauto
  · tauto

/-- A splice of smooth domains is smooth when the domains agree on an open
collar containing the entire cutting frontier. -/
theorem IsSmoothDomain.spliceIn_of_agree_near_frontier
    {U G W N : Set PlanePoint} (hU : IsSmoothDomain U)
    (hG : IsSmoothDomain G) (hN : IsOpen N)
    (hfrontier : frontier W ⊆ N) (hlocal : U ∩ N = G ∩ N) :
    IsSmoothDomain (spliceIn U G W) := by
  have hrepr := spliceIn_eq_open_union_of_agree_near_frontier
    hfrontier hlocal
  apply IsSmoothDomain.of_locally_eq
  · rw [hrepr]
    exact ((hG.isOpen.inter isOpen_interior).union
      (hU.isOpen.inter isOpen_interior)).union (hU.isOpen.inter hN)
  · intro p hp
    by_cases hpN : p ∈ N
    · exact ⟨U, N, hU, hN, hpN,
        spliceIn_inter_eq_of_agree hlocal⟩
    · have hpNotFrontier : p ∉ frontier W :=
        fun hpW => hpN (hfrontier hpW)
      have hpOutside : p ∈ (frontier W)ᶜ := hpNotFrontier
      rw [compl_frontier_eq_union_interior] at hpOutside
      rcases hpOutside with hpInt | hpIntc
      · exact ⟨G, interior W, hG, isOpen_interior, hpInt,
          spliceIn_inter_interior U G W⟩
      · exact ⟨U, interior Wᶜ, hU, isOpen_interior, hpIntc,
          spliceIn_inter_interior_compl U G W⟩

/-- For a closed cutting window, its exterior together with any neighborhood
of its frontier covers the complete complement of its interior. -/
lemma compl_interior_subset_interior_compl_union
    {W N : Set PlanePoint} (hW : IsClosed W)
    (hfrontier : frontier W ⊆ N) :
    (interior W)ᶜ ⊆ interior Wᶜ ∪ N := by
  intro p hp
  by_cases hpW : p ∈ W
  · exact Or.inr (hfrontier
      ((mem_frontier_iff_notMem_interior hpW).2 hp))
  · left
    rw [hW.isOpen_compl.interior_eq]
    exact hpW

/-- Under collar agreement, the raw splice has exactly the old complete
frontier on the closed complement of the cutting interior.  Thus no cutting
face is silently discarded: every boundary point of the window is charged to
the common collar model. -/
theorem smoothCostOn_spliceIn_eq_compl_interior_of_agree_near_frontier
    (lam : ℝ) {U G W N : Set PlanePoint}
    (hW : IsClosed W) (hN : IsOpen N)
    (hfrontier : frontier W ⊆ N) (hlocal : U ∩ N = G ∩ N) :
    smoothCostOn lam (spliceIn U G W) (interior W)ᶜ =
      smoothCostOn lam U (interior W)ᶜ := by
  let O := interior Wᶜ ∪ N
  have hO : IsOpen O := isOpen_interior.union hN
  have hcompl : (interior W)ᶜ ⊆ O :=
    compl_interior_subset_interior_compl_union hW hfrontier
  have hlocalO : spliceIn U G W ∩ O = U ∩ O := by
    ext p
    have hInt := Set.ext_iff.mp
      (spliceIn_inter_interior_compl U G W) p
    have hNear := Set.ext_iff.mp
      (spliceIn_inter_eq_of_agree (W := W) hlocal) p
    simp only [O, mem_inter_iff, mem_union] at hInt hNear ⊢
    tauto
  have hfrontO :
      frontier (spliceIn U G W) ∩ O = frontier U ∩ O :=
    frontier_inter_eq_of_inter_open_eq hO hlocalO
  apply smoothCostOn_eq_of_frontier_inter_eq lam
    isOpen_interior.measurableSet.compl
  calc
    frontier (spliceIn U G W) ∩ (interior W)ᶜ =
        (frontier (spliceIn U G W) ∩ O) ∩ (interior W)ᶜ := by
      ext p
      simp only [mem_inter_iff]
      constructor
      · exact fun hp => ⟨⟨hp.1, hcompl hp.2⟩, hp.2⟩
      · exact fun hp => ⟨hp.1.1, hp.2⟩
    _ = (frontier U ∩ O) ∩ (interior W)ᶜ := by rw [hfrontO]
    _ = frontier U ∩ (interior W)ᶜ := by
      ext p
      simp only [mem_inter_iff]
      constructor
      · exact fun hp => ⟨hp.1.1, hp.2⟩
      · exact fun hp => ⟨⟨hp.1, hcompl hp.2⟩, hp.2⟩

/-- Exact complete-frontier cost decomposition for a collar-compatible
splice.  The inserted model pays inside the cutting interior and the unchanged
domain pays everywhere else, including the whole artificial cutting locus. -/
theorem smoothCost_spliceIn_eq_inside_add_outside
    (lam : ℝ) {U G W N : Set PlanePoint}
    (hW : IsClosed W) (hN : IsOpen N)
    (hfrontier : frontier W ⊆ N) (hlocal : U ∩ N = G ∩ N) :
    smoothCost lam (spliceIn U G W) =
      smoothCostOn lam G (interior W) +
        smoothCostOn lam U (interior W)ᶜ := by
  rw [← smoothCostOn_add_compl lam (spliceIn U G W)
    isOpen_interior.measurableSet]
  exact congrArg₂ (· + ·)
    (smoothCostOn_eq_of_inter_open_eq lam isOpen_interior
      (spliceIn_inter_interior U G W))
    (smoothCostOn_spliceIn_eq_compl_interior_of_agree_near_frontier
      lam hW hN hfrontier hlocal)

/-- Additive one-term cost comparison for a genuine collar-compatible splice.
The hypotheses expose exactly the two remaining numerical obligations: recover
the removed old local cost and bound the inserted local cost.  The unchanged
exterior cancels without extended subtraction. -/
theorem smoothCost_spliceIn_add_le_of_agree_near_frontier
    (lam : ℝ) {U G W N : Set PlanePoint}
    (hW : IsClosed W) (hN : IsOpen N)
    (hfrontier : frontier W ⊆ N) (hlocal : U ∩ N = G ∩ N)
    (oldCost newCost : ENNReal)
    (hold : oldCost ≤ smoothCostOn lam U (interior W))
    (hnew : smoothCostOn lam G (interior W) ≤ newCost) :
    smoothCost lam (spliceIn U G W) + oldCost ≤
      smoothCost lam U + newCost := by
  rw [smoothCost_spliceIn_eq_inside_add_outside
    lam hW hN hfrontier hlocal]
  rw [← smoothCostOn_add_compl lam U isOpen_interior.measurableSet]
  calc
    (smoothCostOn lam G (interior W) +
          smoothCostOn lam U (interior W)ᶜ) + oldCost =
        smoothCostOn lam G (interior W) + oldCost +
          smoothCostOn lam U (interior W)ᶜ := by ac_rfl
    _ ≤ newCost + smoothCostOn lam U (interior W) +
          smoothCostOn lam U (interior W)ᶜ :=
      add_le_add (add_le_add hnew hold) le_rfl
    _ = (smoothCostOn lam U (interior W) +
          smoothCostOn lam U (interior W)ᶜ) + newCost := by ac_rfl

lemma spliceIn_symmDiff_subset (U G F W : Set PlanePoint) :
    spliceIn U G W ∆ F ⊆
      ((U ∆ F) \ W) ∪ ((G ∆ F) ∩ W) := by
  intro p hp
  by_cases hpW : p ∈ W <;>
    simp_all [spliceIn, Set.mem_symmDiff]

lemma symmDiff_outside_subset_of_symmDiff_subset
    {E F W U : Set PlanePoint} (hEF : E ∆ F ⊆ W) :
    (U ∆ F) \ W ⊆ (U ∆ E) \ W := by
  intro p hp
  have hmem : p ∈ E ↔ p ∈ F := by
    constructor
    · intro hpE
      by_contra hpF
      exact hp.2 (hEF (by
        simp only [Set.mem_symmDiff]
        exact Or.inl ⟨hpE, hpF⟩))
    · intro hpF
      by_contra hpE
      exact hp.2 (hEF (by
        simp only [Set.mem_symmDiff]
        exact Or.inr ⟨hpF, hpE⟩))
  simpa only [Set.mem_symmDiff, Set.mem_sdiff, hmem] using hp

/-- Raw cut-and-paste changes the target mismatch only through the retained
outside mismatch and inserted inside mismatch. -/
theorem characteristicDistance_spliceIn_le
    {E F U G W : Set PlanePoint} (hEF : E ∆ F ⊆ W) :
    characteristicDistance (spliceIn U G W) F ≤
      characteristicDistance U E + volume ((G ∆ F) ∩ W) := by
  unfold characteristicDistance
  calc
    volume (spliceIn U G W ∆ F) ≤
        volume (((U ∆ F) \ W) ∪ ((G ∆ F) ∩ W)) :=
      measure_mono (spliceIn_symmDiff_subset U G F W)
    _ ≤ volume ((U ∆ F) \ W) + volume ((G ∆ F) ∩ W) :=
      measure_union_le _ _
    _ ≤ volume (U ∆ E) + volume ((G ∆ F) ∩ W) :=
      add_le_add
        (measure_mono
          ((symmDiff_outside_subset_of_symmDiff_subset hEF).trans
            sdiff_subset))
        le_rfl

/-- Consequently, raw cut-and-paste preserves `L¹` convergence whenever the
old and new targets differ only inside the replacement window. -/
theorem tendsto_characteristicDistance_spliceIn_zero
    {E F W : Set PlanePoint} {U G : ℕ → Set PlanePoint}
    (hEF : E ∆ F ⊆ W)
    (hU : Tendsto (fun n => characteristicDistance (U n) E)
      atTop (𝓝 0))
    (hG : Tendsto (fun n => volume ((G n ∆ F) ∩ W))
      atTop (𝓝 0)) :
    Tendsto (fun n => characteristicDistance (spliceIn (U n) (G n) W) F)
      atTop (𝓝 0) := by
  have hsum : Tendsto
      (fun n => characteristicDistance (U n) E +
        volume ((G n ∆ F) ∩ W)) atTop (𝓝 0) := by
    simpa using hU.add hG
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => bot_le)
      (fun n => characteristicDistance_spliceIn_le hEF)

/-- Lift an exact additive transfer on every literal smooth recovery sequence
through the `sInf` defining the relaxation.  This is valid even when the source
has no admissible sequence: the shifted source infimum is then `⊤`. -/
theorem relaxedPerimeter_add_le_of_smoothSequence_transfer
    {lam : ℝ} {E F : Set PlanePoint}
    (hF : NullMeasurableSet F volume) (oldCost newCost : ENNReal)
    (htransfer : ∀ A : SmoothSequence, A.ConvergesTo E →
      ∃ B : SmoothSequence, B.ConvergesTo F ∧
        B.cost lam + oldCost ≤ A.cost lam + newCost) :
    relaxedPerimeter lam F + oldCost ≤
      relaxedPerimeter lam E + newCost := by
  unfold relaxedPerimeter
  nth_rewrite 2 [ENNReal.sInf_add]
  refine le_iInf fun c => le_iInf fun hc => ?_
  obtain ⟨A, _hE, hAconv, rfl⟩ := hc
  obtain ⟨B, hBconv, hBcost⟩ := htransfer A hAconv
  have hBmem :
      B.cost lam ∈ {c : ENNReal | ∃ A : SmoothSequence,
        NullMeasurableSet F volume ∧ A.ConvergesTo F ∧ A.cost lam = c} :=
    ⟨B, hF, hBconv, rfl⟩
  exact (add_le_add_left (sInf_le hBmem) oldCost).trans hBcost


/-- A termwise additive surgery estimate with a vanishing error passes to the
actual extended liminf costs.  No finiteness assumption is needed: the argument
uses only monotonicity of `liminf`, constant-addition, and the exact
`ENNReal` zero-error limit, so it never subtracts an infinite cost. -/
theorem SmoothSequence.cost_add_le_of_pointwise_add_allowance
    {lam : ℝ} (B A : SmoothSequence) (oldCost newCost : ENNReal)
    {allowance : ℕ → ENNReal}
    (hallowance : Tendsto allowance atTop (𝓝 0))
    (hpoint : ∀ n,
      smoothCost lam (B.carrier n) + oldCost ≤
        smoothCost lam (A.carrier n) + newCost + allowance n) :
    B.cost lam + oldCost ≤ A.cost lam + newCost := by
  unfold SmoothSequence.cost
  calc
    liminf (fun n => smoothCost lam (B.carrier n)) atTop + oldCost =
        liminf (fun n =>
          smoothCost lam (B.carrier n) + oldCost) atTop := by
      rw [liminf_add_const atTop
        (fun n => smoothCost lam (B.carrier n)) oldCost
        (by isBoundedDefault) (by isBoundedDefault)]
    _ ≤ liminf (fun n =>
          (smoothCost lam (A.carrier n) + newCost) + allowance n) atTop := by
      exact liminf_le_liminf (Eventually.of_forall hpoint)
    _ = liminf (fun n =>
          smoothCost lam (A.carrier n) + newCost) atTop :=
      ENNReal.liminf_add_of_right_tendsto_zero hallowance _
    _ = liminf (fun n => smoothCost lam (A.carrier n)) atTop + newCost := by
      rw [liminf_add_const atTop
        (fun n => smoothCost lam (A.carrier n)) newCost
        (by isBoundedDefault) (by isBoundedDefault)]


/-- Every interior point of a `C²` graph supplies a nonzero localized
projection payoff that survives the liminf of any genuine smooth recovery
sequence.  The rigid box lies in the protected constant-density tube, and the
construction handles both occupied-side orientations through `tangentFrame`.

This is the pointwise building block for the still-required finite exhaustion
of the complete old graph length. -/
theorem SmoothSequence.exists_graphTangentPatch_payoff_le_liminf_smoothCostOn
    {lam : ℝ} {E : Set PlanePoint} (hlam : 1 < lam)
    (A : SmoothSequence) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E)
    (P : CMVTwoPatchGraphVariation.GraphPatch) (T : P.Tube)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo P.a P.b)
    (hlocal : ∀ q ∈ P.graphTube T,
      q ∈ P.occupiedGraphDomain P.graph ↔ q ∈ E) :
    ∃ r > 0, ∃ Q : RigidProjectionPatch lam E,
      Q.window ⊆ P.graphTube T ∧
      Q.payoff =
        ENNReal.ofReal (P.zone.weight lam) * ENNReal.ofReal (2 * r) ∧
      0 < Q.payoff ∧
      Q.payoff ≤
        liminf (fun n => smoothCostOn lam (A.carrier n) (P.graphTube T))
          atTop := by
  obtain ⟨r, hr, htangent, hwindow⟩ :=
    P.exists_tangentProjectionBox_in_graphTube T hx₀
  cases hside : P.side with
  | below =>
      simp only [CMVTwoPatchGraphVariation.GraphPatch.tangentFrame,
        hside] at hwindow
      let Q₀ := subgraphTangentPatch lam (P.zone.weight lam) P.graph
        x₀ (-r) r r hr
        (tangentBox_residual_lt_of_bound P.graph x₀ (deriv P.graph x₀)
          r r (1 / 4 : ℝ) hr (by norm_num) _
          (abs_graphTangentFrame_fst_sub_le
            x₀ (P.graph x₀) (deriv P.graph x₀)) htangent (by nlinarith))
        (by
          intro q hq
          have hqtube : q ∈ P.graphTube T := hwindow hq
          have hz := P.closedGraphTube_in_zone T
            (P.graphTube_subset_closedGraphTube T hqtube)
          rw [P.zone.stripDensity_eq_weight hz])
      let Q : RigidProjectionPatch lam E :=
        Q₀.changeCarrierOnWindow (by
          intro q hq
          have hqtube : q ∈ P.graphTube T := by
            apply hwindow
            simpa [Q₀, RigidProjectionPatch.window,
              subgraphTangentPatch] using hq
          simpa [CMVTwoPatchGraphVariation.GraphPatch.occupiedGraphDomain,
            hside] using hlocal q hqtube)
      have hQwindow : Q.window ⊆ P.graphTube T := by
        intro q hq
        apply hwindow
        simpa [Q, Q₀, RigidProjectionPatch.window,
          RigidProjectionPatch.changeCarrierOnWindow,
          subgraphTangentPatch] using hq
      have hQpayoff :
          Q.payoff =
            ENNReal.ofReal (P.zone.weight lam) * ENNReal.ofReal (2 * r) := by
        simp only [Q, Q₀, RigidProjectionPatch.payoff,
          RigidProjectionPatch.changeCarrierOnWindow,
          subgraphTangentPatch]
        congr 1
        ring
      have hQpos : 0 < Q.payoff := by
        simp only [Q, Q₀, RigidProjectionPatch.payoff,
          RigidProjectionPatch.changeCarrierOnWindow,
          subgraphTangentPatch]
        rw [ENNReal.mul_pos_iff]
        exact ⟨ENNReal.ofReal_pos.2 (P.zone.weight_pos hlam),
          ENNReal.ofReal_pos.2 (by linarith)⟩
      refine ⟨r, hr, Q, hQwindow, hQpayoff, hQpos, ?_⟩
      have hsum :=
        A.finset_sum_payoff_le_liminf_smoothCostOn hconv
          ({()} : Finset Unit) (fun _ => Q)
          (by simp [Set.Pairwise])
          (W := P.graphTube T)
          (by
            intro i hi
            simpa only using hQwindow)
          hE
      simpa only [Finset.sum_singleton] using hsum
  | above =>
      simp only [CMVTwoPatchGraphVariation.GraphPatch.tangentFrame,
        hside] at hwindow
      let Q₀ := supergraphTangentPatch lam (P.zone.weight lam) P.graph
        x₀ (-r) r r hr
        (tangentBox_residual_lt_of_bound P.graph x₀ (deriv P.graph x₀)
          r r (1 / 4 : ℝ) hr (by norm_num) _
          (abs_supergraphTangentFrame_fst_sub_le
            x₀ (P.graph x₀) (deriv P.graph x₀)) htangent (by nlinarith))
        (by
          intro q hq
          have hqtube : q ∈ P.graphTube T := hwindow hq
          have hz := P.closedGraphTube_in_zone T
            (P.graphTube_subset_closedGraphTube T hqtube)
          rw [P.zone.stripDensity_eq_weight hz])
      let Q : RigidProjectionPatch lam E :=
        Q₀.changeCarrierOnWindow (by
          intro q hq
          have hqtube : q ∈ P.graphTube T := by
            apply hwindow
            simpa [Q₀, RigidProjectionPatch.window,
              supergraphTangentPatch] using hq
          simpa [CMVTwoPatchGraphVariation.GraphPatch.occupiedGraphDomain,
            hside] using hlocal q hqtube)
      have hQwindow : Q.window ⊆ P.graphTube T := by
        intro q hq
        apply hwindow
        simpa [Q, Q₀, RigidProjectionPatch.window,
          RigidProjectionPatch.changeCarrierOnWindow,
          supergraphTangentPatch] using hq
      have hQpayoff :
          Q.payoff =
            ENNReal.ofReal (P.zone.weight lam) * ENNReal.ofReal (2 * r) := by
        simp only [Q, Q₀, RigidProjectionPatch.payoff,
          RigidProjectionPatch.changeCarrierOnWindow,
          supergraphTangentPatch]
        congr 1
        ring
      have hQpos : 0 < Q.payoff := by
        simp only [Q, Q₀, RigidProjectionPatch.payoff,
          RigidProjectionPatch.changeCarrierOnWindow,
          supergraphTangentPatch]
        rw [ENNReal.mul_pos_iff]
        exact ⟨ENNReal.ofReal_pos.2 (P.zone.weight_pos hlam),
          ENNReal.ofReal_pos.2 (by linarith)⟩
      refine ⟨r, hr, Q, hQwindow, hQpayoff, hQpos, ?_⟩
      have hsum :=
        A.finset_sum_payoff_le_liminf_smoothCostOn hconv
          ({()} : Finset Unit) (fun _ => Q)
          (by simp [Set.Pairwise])
          (W := P.graphTube T)
          (by
            intro i hi
            simpa only using hQwindow)
          hE
      simpa only [Finset.sum_singleton] using hsum

/-- Interior points on both graph pieces of an actual two-patch carrier yield
two nonzero projection charges in disjoint protected tubes.  Their sum survives
the localized liminf of every smooth recovery sequence; no boundary charge is
counted twice. -/
theorem SmoothSequence.exists_actualTwoPatch_tangent_payoffs_le_liminf
    {lam : ℝ} (hlam : 1 < lam)
    (D : CMVTwoPatchGraphVariation.ActualTwoPatchData)
    (A : SmoothSequence) (hconv : A.ConvergesTo D.actualCarrier)
    {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Ioo D.patches.first.a D.patches.first.b)
    (hx₂ : x₂ ∈ Ioo D.patches.second.a D.patches.second.b) :
    ∃ r₁ > 0, ∃ r₂ > 0,
    ∃ (Q₁ Q₂ : RigidProjectionPatch lam D.actualCarrier),
      Q₁.window ⊆ D.patches.first.graphTube D.firstTube ∧
      Q₂.window ⊆ D.patches.second.graphTube D.secondTube ∧
      Q₁.payoff = ENNReal.ofReal (D.patches.first.zone.weight lam) *
        ENNReal.ofReal (2 * r₁) ∧
      Q₂.payoff = ENNReal.ofReal (D.patches.second.zone.weight lam) *
        ENNReal.ofReal (2 * r₂) ∧
      0 < Q₁.payoff ∧
      0 < Q₂.payoff ∧
      Q₁.payoff + Q₂.payoff ≤
        liminf (fun n => smoothCostOn lam (A.carrier n)
          (D.patches.first.graphTube D.firstTube ∪
            D.patches.second.graphTube D.secondTube)) atTop := by
  have hlocal₁ : ∀ q ∈ D.patches.first.graphTube D.firstTube,
      q ∈ D.patches.first.occupiedGraphDomain D.patches.first.graph ↔
        q ∈ D.actualCarrier := by
    intro q hq
    exact ((D.mem_actualCarrier_iff_mem_firstCarrier_of_mem_graphTube hq).trans
      (D.patches.first.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        D.firstTube hq)).symm
  have hlocal₂ : ∀ q ∈ D.patches.second.graphTube D.secondTube,
      q ∈ D.patches.second.occupiedGraphDomain D.patches.second.graph ↔
        q ∈ D.actualCarrier := by
    intro q hq
    exact ((D.mem_actualCarrier_iff_mem_secondCarrier_of_mem_graphTube hq).trans
      (D.patches.second.mem_carrier_iff_mem_occupiedGraphDomain_of_mem_graphTube
        D.secondTube hq)).symm
  obtain ⟨r₁, hr₁, Q₁, hQ₁, hpay₁, hpos₁, _⟩ :=
    A.exists_graphTangentPatch_payoff_le_liminf_smoothCostOn
      hlam hconv D.measurableSet_actualCarrier D.patches.first D.firstTube
        hx₁ hlocal₁
  obtain ⟨r₂, hr₂, Q₂, hQ₂, hpay₂, hpos₂, _⟩ :=
    A.exists_graphTangentPatch_payoff_le_liminf_smoothCostOn
      hlam hconv D.measurableSet_actualCarrier D.patches.second D.secondTube
        hx₂ hlocal₂
  let Q : Bool → RigidProjectionPatch lam D.actualCarrier :=
    fun i => cond i Q₁ Q₂
  have htubes :
      Disjoint (D.patches.first.graphTube D.firstTube)
        (D.patches.second.graphTube D.secondTube) :=
    (D.patches.closedGraphTubes_disjoint D.firstTube D.secondTube).mono
      (D.patches.first.graphTube_subset_closedGraphTube D.firstTube)
      (D.patches.second.graphTube_subset_closedGraphTube D.secondTube)
  have hpair : Set.Pairwise (↑(Finset.univ : Finset Bool))
      (Function.onFun Disjoint fun i => (Q i).window) := by
    intro i hi j hj hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · simpa only [Function.onFun, Q, cond_false, cond_true] using
        htubes.symm.mono hQ₂ hQ₁
    · simpa only [Function.onFun, Q, cond_false, cond_true] using
        htubes.mono hQ₁ hQ₂
    · exact (hij rfl).elim
  have hsub : ∀ i ∈ (Finset.univ : Finset Bool), (Q i).window ⊆
      D.patches.first.graphTube D.firstTube ∪
        D.patches.second.graphTube D.secondTube := by
    intro i hi
    cases i
    · exact hQ₂.trans subset_union_right
    · exact hQ₁.trans subset_union_left
  have hsum :=
    A.finset_sum_payoff_le_liminf_smoothCostOn hconv
      (Finset.univ : Finset Bool) Q hpair hsub
      D.measurableSet_actualCarrier
  refine ⟨r₁, hr₁, r₂, hr₂, Q₁, Q₂, hQ₁, hQ₂,
    hpay₁, hpay₂, hpos₁, hpos₂, ?_⟩
  simpa [Q, add_comm] using hsum
/-- Lift a termwise smooth surgery with vanishing seam/smoothing allowance
through both the sequence `liminf` and the literal `sInf` relaxation.

The premise asks for actual smooth modified domains and their global
characteristic convergence.  It does not ask for a sequence-level cost bound:
that bound is derived here from the pointwise complete-frontier estimates, with
the allowance removed before the infimum comparison. -/
theorem relaxedPerimeter_add_le_of_termwise_smoothSequence_transfer
    {lam : ℝ} {E F : Set PlanePoint}
    (hF : NullMeasurableSet F volume) (oldCost newCost : ENNReal)
    (htransfer : ∀ A : SmoothSequence, A.ConvergesTo E →
      ∃ (B : SmoothSequence) (allowance : ℕ → ENNReal),
        B.ConvergesTo F ∧
        Tendsto allowance atTop (𝓝 0) ∧
        ∀ n,
          smoothCost lam (B.carrier n) + oldCost ≤
            smoothCost lam (A.carrier n) + newCost + allowance n) :
    relaxedPerimeter lam F + oldCost ≤
      relaxedPerimeter lam E + newCost := by
  apply relaxedPerimeter_add_le_of_smoothSequence_transfer
    hF oldCost newCost
  intro A hA
  obtain ⟨B, allowance, hB, hallowance, hpoint⟩ := htransfer A hA
  exact ⟨B, hB,
    B.cost_add_le_of_pointwise_add_allowance A oldCost newCost
      hallowance hpoint⟩
end CMVRelaxation
namespace CMVRelaxation

/-- Uniform midpoint sums approximate a continuous interval integrand from below,
up to an arbitrary positive additive error. -/
theorem exists_midpoint_sum_add_ge_intervalIntegral
    {f : ℝ → ℝ} {a b η σ : ℝ} (hf : Continuous f)
    (hab : a < b) (hη : 0 < η) (hσ : 0 < σ) :
    ∃ N : ℕ, 0 < N ∧
      let d := (b - a) / (N : ℝ)
      d < σ ∧
        ∫ x in a..b, f x ≤
          (∑ i : Fin N, f (a + ((i : ℝ) + 1 / 2) * d) * d) + η := by
  let ε := η / (2 * (b - a))
  have hε : 0 < ε := div_pos hη (mul_pos (by norm_num) (sub_pos.mpr hab))
  have huc : UniformContinuousOn f (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hclose⟩ := huc ε hε
  obtain ⟨N0 : ℕ, hN0⟩ :=
    exists_nat_gt (max ((b - a) / δ) ((b - a) / σ))
  let N := max N0 1
  have hN : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N0 1)
  have hNreal : 0 < (N : ℝ) := by positivity
  let d := (b - a) / (N : ℝ)
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNreal
  have hdδ : d < δ := by
    have hfrac : (b - a) / δ < (N : ℝ) :=
      (lt_of_le_of_lt (le_max_left _ _) hN0).trans_le
        (by exact_mod_cast le_max_left N0 1)
    rw [div_lt_iff₀ hNreal]
    rw [div_lt_iff₀ hδ] at hfrac
    simpa only [d, mul_comm] using hfrac
  let p : ℕ → ℝ := fun k => a + (k : ℝ) * d
  have hdσ : d < σ := by
    have hfrac : (b - a) / σ < (N : ℝ) :=
      (lt_of_le_of_lt (le_max_right _ _) hN0).trans_le
        (by exact_mod_cast le_max_left N0 1)
    rw [div_lt_iff₀ hNreal]
    rw [div_lt_iff₀ hσ] at hfrac
    simpa only [d, mul_comm] using hfrac
  let m : Fin N → ℝ := fun i => a + ((i : ℝ) + 1 / 2) * d
  have hp0 : p 0 = a := by simp [p]
  have hpN : p N = b := by
    dsimp [p, d]
    field_simp [hNreal.ne']
    ring_nf
  have hpmono : Monotone p := by
    intro i j hij
    dsimp [p]
    gcongr
  have hcell (i : Fin N) :
      ∫ x in p i.1..p (i.1 + 1), f x ≤ f (m i) * d + ε * d := by
    have hiN : i.1 < N := i.2
    have hpile : p i.1 ≤ p (i.1 + 1) := hpmono (Nat.le_succ _)
    have hpimem : p i.1 ∈ Icc a b := by
      constructor
      · simpa only [← hp0] using hpmono (Nat.zero_le i.1)
      · rw [← hpN]
        exact hpmono (Nat.le_of_lt hiN)
    have hpnextmem : p (i.1 + 1) ∈ Icc a b := by
      constructor
      · rw [← hp0]
        exact hpmono (Nat.zero_le _)
      · rw [← hpN]
        exact hpmono (Nat.succ_le_iff.mpr hiN)
    have hm_between : m i ∈ Icc (p i.1) (p (i.1 + 1)) := by
      have hm_eq : m i = (p i.1 + p (i.1 + 1)) / 2 := by
        dsimp [m, p]
        push_cast
        ring
      rw [hm_eq]
      constructor <;> linarith
    have hmmem : m i ∈ Icc a b :=
      ⟨hpimem.1.trans hm_between.1, hm_between.2.trans hpnextmem.2⟩
    have hpoint : ∀ x ∈ Icc (p i.1) (p (i.1 + 1)), f x ≤ f (m i) + ε := by
      intro x hx
      have hxmem : x ∈ Icc a b := ⟨hpimem.1.trans hx.1, hx.2.trans hpnextmem.2⟩
      have hdist : dist x (m i) < δ := by
        rw [Real.dist_eq]
        have hxm : |x - m i| ≤ d := by
          rw [abs_le]
          have hstep : p (i.1 + 1) - p i.1 = d := by
            dsimp [p]
            push_cast
            ring
          constructor <;> linarith [hx.1, hx.2, hm_between.1, hm_between.2]
        exact hxm.trans_lt (by nlinarith [hdδ])
      have hc := hclose x hxmem (m i) hmmem hdist
      rw [Real.dist_eq] at hc
      linarith [le_abs_self (f x - f (m i))]
    calc
      ∫ x in p i.1..p (i.1 + 1), f x ≤
          ∫ _x in p i.1..p (i.1 + 1), (f (m i) + ε) :=
        intervalIntegral.integral_mono_on hpile
          (hf.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) hpoint
      _ = (f (m i) + ε) * d := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        dsimp [p]
        push_cast
        ring
      _ = f (m i) * d + ε * d := by ring
  refine ⟨N, hN, ?_⟩
  dsimp only
  refine ⟨hdσ, ?_⟩
  change ∫ x in a..b, f x ≤ (∑ i : Fin N, f (m i) * d) + η
  rw [← hp0, ← hpN, ← intervalIntegral.sum_integral_adjacent_intervals
    (f := f) (a := p) (n := N) (fun k hk => hf.intervalIntegrable _ _)]
  calc
    ∑ k ∈ Finset.range N, ∫ x in p k..p (k + 1), f x ≤
        ∑ k ∈ Finset.range N,
          (f (a + ((k : ℝ) + 1 / 2) * d) * d + ε * d) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [m] using hcell ⟨k, Finset.mem_range.mp hk⟩
    _ = (∑ i : Fin N, f (m i) * d) + (N : ℝ) * (ε * d) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_range]
      rw [← Fin.sum_univ_eq_sum_range]
    _ ≤ (∑ i : Fin N, f (m i) * d) + η := by
      gcongr
      dsimp [ε, d]
      have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
      field_simp [hNreal.ne', hba]
      nlinarith [sub_pos.mpr hab]


/-- The source-horizontal component of a tangent box uses the reciprocal graph
speed; retaining this factor permits adjacent tangent windows to fill an
arbitrary graph without overlapping in source coordinates. -/
theorem abs_graphTangentFrame_fst_sub_le_div_speed
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    |(euclideanRigidMap (graphTangentFrame x₀ y₀ slope) p).1 - x₀| ≤
      |p.1| / Real.sqrt (1 + slope ^ 2) + |p.2| := by
  rw [euclideanRigidMap_graphTangentFrame]
  have hspeed : 0 < Real.sqrt (1 + slope ^ 2) := by positivity
  calc
    |x₀ + p.1 * Real.cos (Real.arctan slope) -
          p.2 * Real.sin (Real.arctan slope) - x₀| =
        |p.1 * Real.cos (Real.arctan slope) -
          p.2 * Real.sin (Real.arctan slope)| := by ring_nf
    _ ≤ |p.1 * Real.cos (Real.arctan slope)| +
          |p.2 * Real.sin (Real.arctan slope)| := abs_sub _ _
    _ = |p.1| * |Real.cos (Real.arctan slope)| +
          |p.2| * |Real.sin (Real.arctan slope)| := by
      rw [abs_mul, abs_mul]
    _ = |p.1| / Real.sqrt (1 + slope ^ 2) +
          |p.2| * |Real.sin (Real.arctan slope)| := by
      rw [Real.cos_arctan, abs_of_pos (one_div_pos.mpr hspeed)]
      ring
    _ ≤ |p.1| / Real.sqrt (1 + slope ^ 2) + |p.2| := by
      have hs : |p.2| * |Real.sin (Real.arctan slope)| ≤ |p.2| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
          (abs_nonneg p.2)
      exact add_le_add le_rfl (by simpa only [mul_one] using hs)

/-- Reversing the occupied normal preserves the sharp source-horizontal
projection estimate. -/
theorem abs_supergraphTangentFrame_fst_sub_le_div_speed
    (x₀ y₀ slope : ℝ) (p : PlanePoint) :
    |(euclideanRigidMap (supergraphTangentFrame x₀ y₀ slope) p).1 - x₀| ≤
      |p.1| / Real.sqrt (1 + slope ^ 2) + |p.2| := by
  rw [euclideanRigidMap_supergraphTangentFrame]
  simpa only [abs_neg] using
    abs_graphTangentFrame_fst_sub_le_div_speed
      x₀ y₀ slope (-p.1, -p.2)

/-- Tangent residual control with the exact reciprocal-speed horizontal
excursion of a rotated box. -/
theorem tangentBox_residual_lt_of_bound_div_speed
    (f : ℝ → ℝ) (x₀ slope h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (R : PlanePoint → PlanePoint)
    (hR : ∀ p, |(R p).1 - x₀| ≤
      |p.1| / Real.sqrt (1 + slope ^ 2) + |p.2|)
    (htangent : ∀ x,
      |x - x₀| ≤ h / Real.sqrt (1 + slope ^ 2) + 2 * rho →
        |f x - f x₀ - slope * (x - x₀)| ≤ ε * |x - x₀|)
    (hsmall : ε * (h / Real.sqrt (1 + slope ^ 2) + 2 * rho) < rho) :
    ∀ p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
      |f (R p).1 - f x₀ - slope * ((R p).1 - x₀)| <
        rho * Real.sqrt (1 + slope ^ 2) := by
  intro p hp
  have hp₁ : |p.1| ≤ h := abs_le.mpr ⟨hp.1.1, hp.1.2⟩
  have hp₂ : |p.2| ≤ 2 * rho := by
    rw [abs_le]
    constructor <;> nlinarith [hp.2.1, hp.2.2]
  have hspeed : 0 < Real.sqrt (1 + slope ^ 2) := by positivity
  have hdx : |(R p).1 - x₀| ≤
      h / Real.sqrt (1 + slope ^ 2) + 2 * rho :=
    (hR p).trans (add_le_add
      (div_le_div_of_nonneg_right hp₁ hspeed.le) hp₂)
  have hres := htangent (R p).1 hdx
  have hresrho :
      |f (R p).1 - f x₀ - slope * ((R p).1 - x₀)| < rho :=
    hres.trans_lt ((mul_le_mul_of_nonneg_left hdx hε).trans_lt hsmall)
  have hone : 1 ≤ Real.sqrt (1 + slope ^ 2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + slope ^ 2 by positivity),
      Real.sqrt_nonneg (1 + slope ^ 2)]
  exact hresrho.trans_le (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hrho.le)

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

private theorem coordinateProjectionBox_subset_graphTube_div_speed
    (P : GraphPatch) (T : P.Tube) (R : PlanePoint → PlanePoint)
    (x₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (hfst : ∀ p, |(R p).1 - x₀| ≤
      |p.1| / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + |p.2|)
    (hnormal : ∀ p,
      |(R p).2 - P.graph x₀ -
          deriv P.graph x₀ * ((R p).1 - x₀)| =
        |p.2| * Real.sqrt (1 + (deriv P.graph x₀) ^ 2))
    (htangent : ∀ x,
      |x - x₀| ≤ h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε *
      (h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho) < rho)
    (hleft : h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho <
      x₀ - P.a)
    (hright : h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho <
      P.b - x₀)
    (htube : 3 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) <
      T.radius) :
    R '' projectionBox (-h) h 0 rho ⊆ P.graphTube T := by
  rintro _ ⟨p, hp, rfl⟩
  change p.1 ∈ Icc (-h) h ∧
    p.2 ∈ Icc (0 - 2 * rho) (0 + 2 * rho) at hp
  have hpfull : p ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho) := by
    exact ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hp₁ : |p.1| ≤ h := abs_le.mpr ⟨hp.1.1, hp.1.2⟩
  have hp₂ : |p.2| ≤ 2 * rho :=
    abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hspeed : 0 < Real.sqrt (1 + (deriv P.graph x₀) ^ 2) := by positivity
  have hdx : |(R p).1 - x₀| ≤ h / Real.sqrt
      (1 + (deriv P.graph x₀) ^ 2) + 2 * rho :=
    (hfst p).trans (add_le_add
      (div_le_div_of_nonneg_right hp₁ hspeed.le) hp₂)
  refine ⟨?_, ?_⟩
  · rw [mem_Ioc]
    have hb := abs_le.mp hdx
    constructor <;> linarith
  · have hres0 := htangent (R p).1 hdx
    have hres : |P.graph (R p).1 - P.graph x₀ -
        deriv P.graph x₀ * ((R p).1 - x₀)| < rho := by
      exact hres0.trans_lt ((mul_le_mul_of_nonneg_left hdx hε).trans_lt hsmall)
    let normal := (R p).2 - P.graph x₀ -
      deriv P.graph x₀ * ((R p).1 - x₀)
    let residual := P.graph (R p).1 - P.graph x₀ -
      deriv P.graph x₀ * ((R p).1 - x₀)
    have hnormal' : |normal| =
        |p.2| * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) := hnormal p
    have hres' : |residual| <
        rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) :=
      hres.trans_le (by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left
            (show 1 ≤ Real.sqrt (1 + (deriv P.graph x₀) ^ 2) by
              nlinarith [Real.sq_sqrt
                (show 0 ≤ 1 + (deriv P.graph x₀) ^ 2 by positivity),
                Real.sqrt_nonneg (1 + (deriv P.graph x₀) ^ 2)])
            hrho.le)
    have hdecomp : (R p).2 - P.graph (R p).1 = normal - residual := by
      dsimp [normal, residual]
      ring
    rw [hdecomp]
    calc
      |normal - residual| ≤ |normal| + |residual| := abs_sub _ _
      _ = |p.2| * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) +
          |residual| := by rw [hnormal']
      _ < 2 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) +
          rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) :=
        add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_right hp₂ hspeed.le) hres'
      _ = 3 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) := by ring
      _ < T.radius := htube

/-- Sharp source-horizontal tangent boxes use graph-speed-scaled tangential
width.  Unlike the coarse box lemma, this form can place adjacent windows in
disjoint source-coordinate cells while retaining their full arclength payoff. -/
theorem tangentProjectionBox_subset_graphTube_div_speed
    (P : GraphPatch) (T : P.Tube) (x₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ x,
      |x - x₀| ≤ h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε *
      (h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho) < rho)
    (hleft : h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho <
      x₀ - P.a)
    (hright : h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho <
      P.b - x₀)
    (htube : 3 * rho * Real.sqrt (1 + (deriv P.graph x₀) ^ 2) <
      T.radius) :
    rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      P.graphTube T := by
  cases hside : P.side with
  | below =>
      simp only [tangentFrame, hside, rigidProjectionBox]
      apply coordinateProjectionBox_subset_graphTube_div_speed P T _ x₀ h rho ε
        hrho hε
          (abs_graphTangentFrame_fst_sub_le_div_speed
            x₀ (P.graph x₀) (deriv P.graph x₀))
      · intro p
        rw [graphTangentFrame_normal_displacement, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      · exact htangent
      · exact hsmall
      · exact hleft
      · exact hright
      · exact htube
  | above =>
      simp only [tangentFrame, hside, rigidProjectionBox]
      apply coordinateProjectionBox_subset_graphTube_div_speed P T _ x₀ h rho ε
        hrho hε
          (abs_supergraphTangentFrame_fst_sub_le_div_speed
            x₀ (P.graph x₀) (deriv P.graph x₀))
      · intro p
        rw [supergraphTangentFrame_normal_displacement, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg _), abs_neg]
      · exact htangent
      · exact hsmall
      · exact hleft
      · exact hright
      · exact htube


/-- A sharp tangent box fits inside a prescribed open source-coordinate
cell.  This is the geometric disjointness input for finite graph meshes. -/
theorem tangentProjectionBox_subset_fst_Ioo
    (P : GraphPatch) (x₀ l r h rho : ℝ)
    (hfit : h / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + 2 * rho <
      min (x₀ - l) (r - x₀)) :
    rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      {q : PlanePoint | q.1 ∈ Ioo l r} := by
  rintro _ ⟨p, hp, rfl⟩
  change p.1 ∈ Icc (-h) h ∧
    p.2 ∈ Icc (0 - 2 * rho) (0 + 2 * rho) at hp
  have hp₁ : |p.1| ≤ h := abs_le.mpr hp.1
  have hp₂ : |p.2| ≤ 2 * rho := by
    rw [abs_le]
    constructor <;> nlinarith [hp.2.1, hp.2.2]
  have hspeed : 0 < Real.sqrt (1 + (deriv P.graph x₀) ^ 2) := by positivity
  have hframe : |(euclideanRigidMap (P.tangentFrame x₀) p).1 - x₀| ≤
      |p.1| / Real.sqrt (1 + (deriv P.graph x₀) ^ 2) + |p.2| := by
    cases hside : P.side with
    | below =>
        simpa only [tangentFrame, hside] using
          abs_graphTangentFrame_fst_sub_le_div_speed
            x₀ (P.graph x₀) (deriv P.graph x₀) p
    | above =>
        simpa only [tangentFrame, hside] using
          abs_supergraphTangentFrame_fst_sub_le_div_speed
            x₀ (P.graph x₀) (deriv P.graph x₀) p
  have hx := hframe.trans (add_le_add
    (div_le_div_of_nonneg_right hp₁ hspeed.le) hp₂)
  change (euclideanRigidMap (P.tangentFrame x₀) p).1 ∈ Ioo l r
  rw [mem_Ioo]
  rw [lt_min_iff] at hfit
  rcases abs_le.mp hx with ⟨hxL, hxR⟩
  constructor <;> linarith


@[simp] theorem tangentRigidProjectionPatch_window
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} {E : Set PlanePoint}
    (x₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho)
    (hwindow : rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      P.graphTube T)
    (hlocal : ∀ q ∈ P.graphTube T,
      q ∈ P.occupiedGraphDomain P.graph ↔ q ∈ E) :
    (P.tangentRigidProjectionPatch (lam := lam) (E := E)
      T x₀ h rho ε hrho hε htangent hsmall hwindow hlocal).window =
      rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho := by
  rcases P with
    ⟨a, b, base, graph, lowerBound, upperBound, zone, side,
      a_lt_b, graph_contDiff, base_order_graph, lowerBound_le_base,
      base_le_upperBound, graph_bounds, carrier_in_zone⟩
  cases side <;>
    simp [tangentRigidProjectionPatch, tangentFrame,
      RigidProjectionPatch.window, subgraphTangentPatch,
      supergraphTangentPatch, RigidProjectionPatch.changeCarrierOnWindow]

@[simp] theorem tangentRigidProjectionPatch_payoff
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} {E : Set PlanePoint}
    (x₀ h rho ε : ℝ)
    (hrho : 0 < rho) (hε : 0 ≤ ε)
    (htangent : ∀ x, |x - x₀| ≤ h + 2 * rho →
      |P.graph x - P.graph x₀ - deriv P.graph x₀ * (x - x₀)| ≤
        ε * |x - x₀|)
    (hsmall : ε * (h + 2 * rho) < rho)
    (hwindow : rigidProjectionBox (P.tangentFrame x₀) (-h) h 0 rho ⊆
      P.graphTube T)
    (hlocal : ∀ q ∈ P.graphTube T,
      q ∈ P.occupiedGraphDomain P.graph ↔ q ∈ E) :
    (P.tangentRigidProjectionPatch (lam := lam) (E := E)
      T x₀ h rho ε hrho hε htangent hsmall hwindow hlocal).payoff =
      ENNReal.ofReal (P.zone.weight lam) *
        ENNReal.ofReal (h - (-h)) := by
  rcases P with
    ⟨a, b, base, graph, lowerBound, upperBound, zone, side,
      a_lt_b, graph_contDiff, base_order_graph, lowerBound_le_base,
      base_le_upperBound, graph_bounds, carrier_in_zone⟩
  cases side <;>
    simp [tangentRigidProjectionPatch,
      RigidProjectionPatch.payoff, subgraphTangentPatch,
      supergraphTangentPatch, RigidProjectionPatch.changeCarrierOnWindow]

set_option maxHeartbeats 800000 in
-- The uniform tangent, mesh geometry, and payoff aggregation proof exceeds
-- Lean's default elaboration budget when checked as one dependent theorem.
/-- A finite equal-source mesh of complete tangent windows exhausts the
weighted length of an arbitrary `C²` graph patch from below.  The windows are
pairwise disjoint and remain inside the patch's constant-density tube. -/
theorem exists_pairwiseDisjoint_tangentPatches_payoff_ge
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} (hlam : 1 < lam)
    {E : Set PlanePoint}
    (hlocal : ∀ q ∈ P.graphTube T,
      q ∈ P.occupiedGraphDomain P.graph ↔ q ∈ E)
    {η : ℝ} (hη : 0 < η) :
    ∃ (N : ℕ) (Q : Fin N → RigidProjectionPatch lam E),
      0 < N ∧
      Set.Pairwise (Set.univ : Set (Fin N))
        (Function.onFun Disjoint fun i => (Q i).window) ∧
      (∀ i, (Q i).window ⊆ P.graphTube T) ∧
      ENNReal.ofReal
          (weightedGraphLength lam P (0 : ℝ → ℝ) 0 - η) ≤
        ∑ i, (Q i).payoff := by
  let F : ℝ → ℝ := fun x =>
    Real.sqrt (1 + (deriv P.graph x) ^ 2)
  let w := P.zone.weight lam
  have hF : Continuous F :=
    (continuous_const.add
      ((P.graph_contDiff.continuous_deriv (by norm_num)).pow 2)).sqrt
  have hw : 0 < w := P.zone.weight_pos hlam
  obtain ⟨M₀, hM₀⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hF.continuousOn)
  let M := max 1 M₀
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hFM : ∀ x ∈ Icc P.a P.b, F x ≤ M := by
    intro x hx
    exact (hM₀ _ (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  let κ := min (1 / 2 : ℝ)
    (η / (4 * w * M * (P.b - P.a)))
  have hκ : 0 < κ := by
    dsimp [κ]
    exact lt_min (by norm_num)
      (div_pos hη (mul_pos (mul_pos (by positivity) hM)
        (sub_pos.mpr P.a_lt_b)))
  have hκhalf : κ ≤ 1 / 2 := min_le_left _ _
  have hκ1 : κ < 1 := hκhalf.trans_lt (by norm_num)
  let ε := κ / (256 * M ^ 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  obtain ⟨δ, hδ, hrem⟩ :=
    exists_uniform_tangent_remainder_on_Icc (a := P.a - 1)
      (b := P.b + 1) P.graph
      (P.graph_contDiff.of_le (by norm_num)) hε
  let err := η / (4 * w)
  have herr : 0 < err := by
    dsimp [err]
    positivity
  let σ := min (δ / M) (min (1 / M) T.radius)
  have hσ : 0 < σ := by
    dsimp [σ]
    exact lt_min (div_pos hδ hM)
      (lt_min (div_pos zero_lt_one hM) T.radius_pos)
  obtain ⟨N, hN, hdσ, hRiemann⟩ :=
    exists_midpoint_sum_add_ge_intervalIntegral hF P.a_lt_b herr hσ
  let d := (P.b - P.a) / (N : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos (sub_pos.mpr P.a_lt_b) (by exact_mod_cast hN)
  have hdδ : d < δ / M := hdσ.trans_le (min_le_left _ _)
  have hd1 : d < 1 / M :=
    hdσ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdT : d < T.radius :=
    hdσ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hMdδ : M * d < δ := by
    apply (lt_div_iff₀' (show 0 < M by positivity)).mp
    simpa only [mul_comm] using hdδ
  have hMd1 : M * d < 1 := by
    apply (lt_div_iff₀' (show 0 < M by positivity)).mp
    simpa only [mul_comm] using hd1
  let edge : ℕ → ℝ := fun k => P.a + (k : ℝ) * d
  let x₀ : Fin N → ℝ := fun i => edge i + d / 2
  let speed : Fin N → ℝ := fun i => F (x₀ i)
  let h : Fin N → ℝ := fun i => (1 - κ) * speed i * d / 2
  let rho : ℝ := κ * d / (64 * M)
  have hNd : (N : ℝ) * d = P.b - P.a := by
    dsimp [d]
    field_simp
  have hedgeN : edge N = P.b := by
    dsimp [edge]
    rw [hNd]
    ring
  have hx₀_mem (i : Fin N) : x₀ i ∈ Ioo P.a P.b := by
    have hi : (i : ℕ) + 1 ≤ N := i.isLt
    have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
    have hiN : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hi
    dsimp [x₀, edge]
    constructor
    · nlinarith
    · rw [← hedgeN]
      dsimp [edge]
      nlinarith
  have hspeed_pos (i : Fin N) : 0 < speed i := by
    dsimp [speed, F]
    positivity
  have hspeed_le (i : Fin N) : speed i ≤ M :=
    hFM _ ⟨(hx₀_mem i).1.le, (hx₀_mem i).2.le⟩
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  have hh (i : Fin N) : 0 < h i := by
    dsimp [h]
    positivity
  have hsharp (i : Fin N) :
      h i / speed i + 2 * rho < d / 2 := by
    have hquot : h i / speed i = (1 - κ) * d / 2 := by
      dsimp [h]
      field_simp [ne_of_gt (hspeed_pos i)]
    have hcoef : 1 / (32 * M) < (1 / 2 : ℝ) := by
      rw [div_lt_iff₀ (by positivity : 0 < 32 * M)]
      nlinarith
    have hkrho : 2 * rho < κ * d / 2 := by
      calc
        2 * rho = (κ * d) * (1 / (32 * M)) := by
          dsimp [rho]
          field_simp
          ring
        _ < (κ * d) * (1 / 2) :=
          mul_lt_mul_of_pos_left hcoef (mul_pos hκ hd)
        _ = κ * d / 2 := by ring
    rw [hquot]
    nlinarith
  have hcoarse (i : Fin N) : h i + 2 * rho < M * d := by
    have hrewrite : speed i * (h i / speed i) = h i := by
      field_simp [ne_of_gt (hspeed_pos i)]
    calc
      h i + 2 * rho =
          speed i * (h i / speed i) + 2 * rho := by rw [hrewrite]
      _ ≤ M * (h i / speed i) + M * (2 * rho) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hspeed_le i)
            (div_nonneg (hh i).le (hspeed_pos i).le)
        · exact (le_mul_of_one_le_left (mul_nonneg (by norm_num) hrho.le) hM1)
      _ = M * (h i / speed i + 2 * rho) := by ring
      _ < M * (d / 2) := mul_lt_mul_of_pos_left (hsharp i) hM
      _ < M * d := by nlinarith
  have hspeed_one (i : Fin N) : 1 ≤ speed i := by
    dsimp [speed, F]
    nlinarith [Real.sq_sqrt
      (show 0 ≤ 1 + (deriv P.graph (x₀ i)) ^ 2 by positivity),
      Real.sqrt_nonneg (1 + (deriv P.graph (x₀ i)) ^ 2)]
  have hsharp_le_coarse (i : Fin N) :
      h i / speed i + 2 * rho ≤ h i + 2 * rho := by
    gcongr
    exact (div_le_self (hh i).le (hspeed_one i))
  have htangent (i : Fin N) : ∀ x,
      |x - x₀ i| ≤ h i + 2 * rho →
      |P.graph x - P.graph (x₀ i) -
          deriv P.graph (x₀ i) * (x - x₀ i)| ≤
        ε * |x - x₀ i| := by
    intro x hx
    apply hrem (x₀ i)
    · exact ⟨by nlinarith [(hx₀_mem i).1], by nlinarith [(hx₀_mem i).2]⟩
    · rw [abs_le] at hx
      constructor <;>
        nlinarith [hcoarse i, hMd1, (hx₀_mem i).1, (hx₀_mem i).2]
    · exact hx.trans_lt ((hcoarse i).trans hMdδ)
  have hsmall (i : Fin N) : ε * (h i + 2 * rho) < rho := by
    calc
      ε * (h i + 2 * rho) < ε * (M * d) :=
        mul_lt_mul_of_pos_left (hcoarse i) hε
      _ < rho := by
        have heq : rho = 4 * (ε * (M * d)) := by
          dsimp [ε, rho]
          field_simp
          ring
        rw [heq]
        nlinarith [mul_pos hε (mul_pos hM hd)]
  have hwindow (i : Fin N) :
      rigidProjectionBox (P.tangentFrame (x₀ i))
          (-(h i)) (h i) 0 rho ⊆ P.graphTube T := by
    apply P.tangentProjectionBox_subset_graphTube_div_speed
      T (x₀ i) (h i) rho ε hrho hε.le
    · intro x hx
      exact htangent i x ((hsharp_le_coarse i).trans' hx)
    · exact (mul_le_mul_of_nonneg_left (hsharp_le_coarse i) hε.le).trans_lt
        (hsmall i)
    · dsimp [x₀, edge]
      have hi0 : (0 : ℝ) ≤ (i : ℕ) := by positivity
      nlinarith [hsharp i]
    · have hi : ((i : ℕ) : ℝ) + 1 ≤ N := by
        exact_mod_cast i.isLt
      dsimp [x₀, edge]
      nlinarith [hsharp i, hNd]
    · calc
        3 * rho * speed i ≤ 3 * rho * M := by
          exact mul_le_mul_of_nonneg_left (hspeed_le i)
            (mul_nonneg (by norm_num) hrho.le)
        _ = 3 * κ * d / 64 := by
          dsimp [rho]
          field_simp
        _ < d := by nlinarith [hκhalf, hd]
        _ < T.radius := hdT
  let Q : Fin N → RigidProjectionPatch lam E := fun i =>
    P.tangentRigidProjectionPatch T (x₀ i) (h i) rho ε
      hrho hε.le (htangent i) (hsmall i) (hwindow i) hlocal
  have hcell (i : Fin N) : (Q i).window ⊆
      {q : PlanePoint | q.1 ∈ Ioo (edge i) (edge ((i : ℕ) + 1))} := by
    dsimp [Q]
    rw [tangentRigidProjectionPatch_window]
    apply P.tangentProjectionBox_subset_fst_Ioo
    rw [lt_min_iff]
    dsimp [x₀, edge]
    norm_num only [Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [hsharp i]
  have hpair : Set.Pairwise (Set.univ : Set (Fin N))
      (Function.onFun Disjoint fun i => (Q i).window) := by
    intro i _ j _ hij
    change Disjoint (Q i).window (Q j).window
    rw [Set.disjoint_left]
    intro q hqi hqj
    have hi := hcell i hqi
    have hj := hcell j hqj
    change q.1 ∈ Ioo (edge i) (edge ((i : ℕ) + 1)) at hi
    change q.1 ∈ Ioo (edge j) (edge ((j : ℕ) + 1)) at hj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji'
    · have hijle : (i : ℕ) + 1 ≤ (j : ℕ) :=
        Nat.succ_le_iff.mpr hij'
      have hijleR : (((i : ℕ) + 1 : ℕ) : ℝ) ≤ (j : ℕ) := by
        exact_mod_cast hijle
      have hedge : edge ((i : ℕ) + 1) ≤ edge j := by
        dsimp [edge]
        simpa only [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_right hijleR hd.le) P.a
      linarith [hi.2, hj.1, hedge]
    · have hjile : (j : ℕ) + 1 ≤ (i : ℕ) :=
        Nat.succ_le_iff.mpr hji'
      have hjileR : (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (i : ℕ) := by
        exact_mod_cast hjile
      have hedge : edge ((j : ℕ) + 1) ≤ edge i := by
        dsimp [edge]
        simpa only [add_comm] using
          add_le_add_left
            (mul_le_mul_of_nonneg_right hjileR hd.le) P.a
      linarith [hj.2, hi.1, hedge]
  let S := ∑ i : Fin N, speed i * d
  have hRiemann' :
      ∫ x in P.a..P.b, F x ≤ S + err := by
    calc
      ∫ x in P.a..P.b, F x ≤
          (∑ i : Fin N,
            F (P.a + ((i : ℝ) + 1 / 2) * d) * d) + err := by
        simpa only [d] using hRiemann
      _ = S + err := by
        congr 1
        dsimp [S, speed, x₀, edge]
        apply Finset.sum_congr rfl
        intro i _
        congr 2
        ring
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hspeed_pos i).le hd.le
  have hSle : S ≤ M * (P.b - P.a) := by
    calc
      S ≤ ∑ _i : Fin N, M * d := by
        dsimp [S]
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hspeed_le i) hd.le
      _ = (N : ℝ) * (M * d) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = M * (P.b - P.a) := by
        rw [← hNd]
        ring
  have hκbound : κ ≤ η / (4 * w * M * (P.b - P.a)) :=
    min_le_right _ _
  have hden : 0 < 4 * w * M * (P.b - P.a) :=
    mul_pos (mul_pos (by positivity) hM) (sub_pos.mpr P.a_lt_b)
  have hκden : κ * (4 * w * M * (P.b - P.a)) ≤ η :=
    (le_div_iff₀ hden).mp hκbound
  have hκloss : w * κ * S ≤ η / 4 := by
    calc
      w * κ * S ≤ w * κ * (M * (P.b - P.a)) :=
        mul_le_mul_of_nonneg_left hSle
          (mul_nonneg hw.le hκ.le)
      _ = (κ * (4 * w * M * (P.b - P.a))) / 4 := by ring
      _ ≤ η / 4 := div_le_div_of_nonneg_right hκden (by norm_num)
  have hwerr : w * err = η / 4 := by
    dsimp [err]
    field_simp
  have hreal :
      w * (∫ x in P.a..P.b, F x) - η ≤
        w * (1 - κ) * S := by
    have hwR := mul_le_mul_of_nonneg_left hRiemann' hw.le
    rw [mul_add, hwerr] at hwR
    have hrewrite : w * (1 - κ) * S = w * S - w * κ * S := by ring
    rw [hrewrite]
    nlinarith
  have hweight :
      weightedGraphLength lam P (0 : ℝ → ℝ) 0 =
        w * ∫ x in P.a..P.b, F x := by
    rw [weightedGraphLength_eq_weight lam P]
    · have hvaried :
          P.variedGraph (0 : ℝ → ℝ) 0 = P.graph := by
        funext x
        simp [variedGraph]
      rw [hvaried]
    · intro x hx
      exact T.closed_tube_in_zone x ⟨hx.1.le, hx.2⟩
        (P.variedGraph (0 : ℝ → ℝ) 0 x) (by
          simpa [variedGraph] using T.radius_pos.le)
  have hpay :
      (∑ i : Fin N, (Q i).payoff) =
        ENNReal.ofReal (w * (1 - κ) * S) := by
    calc
      (∑ i : Fin N, (Q i).payoff) =
          ∑ i : Fin N,
            ENNReal.ofReal (w * (1 - κ) * (speed i * d)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [Q]
        rw [tangentRigidProjectionPatch_payoff]
        rw [← ENNReal.ofReal_mul hw.le]
        congr 1
        dsimp [h]
        ring
      _ = ENNReal.ofReal
          (∑ i : Fin N, w * (1 - κ) * (speed i * d)) := by
        symm
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        positivity
      _ = ENNReal.ofReal (w * (1 - κ) * S) := by
        congr 1
        dsimp [S]
        rw [Finset.mul_sum]
  refine ⟨N, Q, hN, hpair, ?_, ?_⟩
  · intro i
    dsimp [Q]
    rw [tangentRigidProjectionPatch_window]
    exact hwindow i
  · rw [hpay]
    apply ENNReal.ofReal_le_ofReal
    rw [hweight]
    exact hreal

/-- The finite graph mesh is the complete local lower-bound input consumed by
every smooth recovery sequence. -/
theorem weightedGraphLength_le_liminf_smoothCostOn_add
    (P : GraphPatch) (T : P.Tube) {lam : ℝ} (hlam : 1 < lam)
    {E : Set PlanePoint}
    (hlocal : ∀ q ∈ P.graphTube T,
      q ∈ P.occupiedGraphDomain P.graph ↔ q ∈ E)
    (hE : MeasurableSet E) (A : SmoothSequence)
    (hconv : A.ConvergesTo E) {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal
        (weightedGraphLength lam P (0 : ℝ → ℝ) 0 - η) ≤
      liminf
        (fun n => smoothCostOn lam (A.carrier n) (P.graphTube T)) atTop := by
  obtain ⟨N, Q, hN, hpair, hwindow, hpay⟩ :=
    P.exists_pairwiseDisjoint_tangentPatches_payoff_ge
      T hlam hlocal hη
  have hpair' : Set.Pairwise (↑(Finset.univ : Finset (Fin N)))
      (Function.onFun Disjoint fun i => (Q i).window) := by
    simpa only [Finset.coe_univ] using hpair
  have hsum := A.finset_sum_payoff_le_liminf_smoothCostOn hconv
    (Finset.univ : Finset (Fin N)) Q hpair'
    (fun i _ => hwindow i) hE
  exact hpay.trans (by simpa using hsum)
end CMVTwoPatchGraphVariation.GraphPatch


namespace CMVRelaxation

/-! ## Same-approximant cancellation and finite-cost reindexing -/

/-- Reindex a smooth sequence without changing its smooth-domain witnesses. -/
def SmoothSequence.reindex (A : SmoothSequence) (φ : ℕ → ℕ) :
    SmoothSequence where
  carrier n := A.carrier (φ n)
  smooth n := A.smooth (φ n)

@[simp] theorem SmoothSequence.reindex_carrier
    (A : SmoothSequence) (φ : ℕ → ℕ) (n : ℕ) :
    (A.reindex φ).carrier n = A.carrier (φ n) := rfl

/-- A cofinal reindexing preserves global characteristic convergence. -/
theorem SmoothSequence.convergesTo_reindex
    {E : Set PlanePoint} (A : SmoothSequence) (φ : ℕ → ℕ)
    (hconv : A.ConvergesTo E) (hφ : Tendsto φ atTop atTop) :
    (A.reindex φ).ConvergesTo E := by
  exact hconv.comp hφ

/-- If the reindexed pointwise costs realize the original liminf, then the
reindexed sequence has exactly the original extended cost. -/
theorem SmoothSequence.cost_reindex_eq_of_tendsto
    {lam : ℝ} (A : SmoothSequence) (φ : ℕ → ℕ)
    (hcost : Tendsto
      (fun n => smoothCost lam (A.carrier (φ n)))
      atTop (𝓝 (A.cost lam))) :
    (A.reindex φ).cost lam = A.cost lam := by
  unfold SmoothSequence.cost
  exact hcost.liminf_eq

/-- Every finite-liminf recovery sequence has a cofinal reindexing whose
pointwise complete-frontier costs are all finite and converge to exactly the
original liminf.  This is the safe branch for geometric cutting: no discarded
subsequence can lower or raise the source sequence cost. -/
theorem SmoothSequence.exists_finiteCost_reindex_of_cost_lt_top
    {lam : ℝ} {E : Set PlanePoint} (A : SmoothSequence)
    (hconv : A.ConvergesTo E) (hcostTop : A.cost lam < ⊤) :
    ∃ B : SmoothSequence,
      B.ConvergesTo E ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      ∀ n, smoothCost lam (B.carrier n) < ⊤ := by
  obtain ⟨φ, hcostφ, hφ⟩ :=
    exists_seq_tendsto_liminf (f := (atTop : Filter ℕ))
      (u := fun n => smoothCost lam (A.carrier n))
  have hevent : ∀ᶠ n in atTop,
      smoothCost lam (A.carrier (φ n)) < ⊤ :=
    hcostφ.eventually (Iio_mem_nhds hcostTop)
  obtain ⟨ψ, hψ, hfinite⟩ :=
    extraction_of_eventually_atTop hevent
  let φ' : ℕ → ℕ := φ ∘ ψ
  let B : SmoothSequence := A.reindex φ'
  have hφ' : Tendsto φ' atTop atTop := by
    exact hφ.comp hψ.tendsto_atTop
  have hcost' :
      Tendsto (fun n => smoothCost lam (A.carrier (φ' n)))
        atTop (𝓝 (A.cost lam)) := by
    change Tendsto
      (((fun n => smoothCost lam (A.carrier n)) ∘ φ) ∘ ψ)
      atTop (𝓝 (liminf (fun n => smoothCost lam (A.carrier n)) atTop))
    exact hcostφ.comp hψ.tendsto_atTop
  refine ⟨B, A.convergesTo_reindex φ' hconv hφ', ?_, ?_, ?_⟩
  · simpa only [B, SmoothSequence.reindex_carrier] using hcost'
  · exact A.cost_reindex_eq_of_tendsto φ' hcost'
  · intro n
    simpa only [B, SmoothSequence.reindex_carrier, φ', Function.comp_apply] using
      hfinite n

/-- If the relaxed infimum is finite, then every finite positive allowance
admits a near-minimizing recovery sequence whose individual complete-frontier
costs are all finite and converge to that sequence's unchanged liminf.  This
is the usable input for termwise cutting: neither the infimum witness nor the
liminf subsequence introduces a hidden loss. -/
theorem exists_nearMinimizing_finiteCost_smoothSequence
    {lam : ℝ} {E : Set PlanePoint} {δ : ENNReal}
    (hrelTop : relaxedPerimeter lam E < ⊤)
    (hδ : δ ≠ 0) (hδTop : δ < ⊤) :
    ∃ B : SmoothSequence,
      NullMeasurableSet E volume ∧
      B.ConvergesTo E ∧
      B.cost lam < relaxedPerimeter lam E + δ ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (B.cost lam)) ∧
      ∀ n, smoothCost lam (B.carrier n) < ⊤ := by
  have hsInfLt :
      relaxedPerimeter lam E < relaxedPerimeter lam E + δ :=
    ENNReal.lt_add_right (ne_of_lt hrelTop) hδ
  unfold relaxedPerimeter at hsInfLt
  rw [sInf_lt_iff] at hsInfLt
  obtain ⟨_, ⟨A, hE, hconv, rfl⟩, hnear⟩ := hsInfLt
  change A.cost lam < relaxedPerimeter lam E + δ at hnear
  have hcostTop : A.cost lam < ⊤ :=
    hnear.trans ((ENNReal.add_lt_top).2 ⟨hrelTop, hδTop⟩)
  obtain ⟨B, hBconv, hBtend, hBeq, hBfinite⟩ :=
    A.exists_finiteCost_reindex_of_cost_lt_top hconv hcostTop
  refine ⟨B, hE, hBconv, ?_, ?_, hBfinite⟩
  · simpa only [hBeq] using hnear
  · simpa only [hBeq] using hBtend


/-- A finite projection family cancels against the local cost of the same
smooth approximant.  The unchanged complementary cost remains on both sides;
no localized liminfs or extended subtraction are used. -/
theorem RigidProjectionPatch.finset_sum_payoff_add_compl_le_smoothCost_add_error
    {lam : ℝ} {E : Set PlanePoint} {ι : Type*}
    (s : Finset ι) (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    {W : Set PlanePoint} (hW : MeasurableSet W)
    (hsub : ∀ i ∈ s, (P i).window ⊆ W)
    (hE : MeasurableSet E) {U : Set PlanePoint} (hU : IsOpen U) :
    (∑ i ∈ s, (P i).payoff) + smoothCostOn lam U Wᶜ ≤
      smoothCost lam U +
        (∑ i ∈ s, (P i).errorCoefficient) *
          characteristicDistance U E := by
  have hlocal :=
    RigidProjectionPatch.finset_sum_payoff_le_smoothCostOn_add_error
      s P hpair hsub hE hU
  calc
    (∑ i ∈ s, (P i).payoff) + smoothCostOn lam U Wᶜ ≤
        (smoothCostOn lam U W +
          (∑ i ∈ s, (P i).errorCoefficient) *
            characteristicDistance U E) +
          smoothCostOn lam U Wᶜ :=
      add_le_add hlocal le_rfl
    _ = (smoothCostOn lam U W + smoothCostOn lam U Wᶜ) +
          (∑ i ∈ s, (P i).errorCoefficient) *
            characteristicDistance U E := by
      ac_rfl
    _ = smoothCost lam U +
          (∑ i ∈ s, (P i).errorCoefficient) *
            characteristicDistance U E := by
      rw [smoothCostOn_add_compl lam U hW]

/-- Once a genuine repaired smooth sequence is bounded by the old complementary
cost plus the inserted local cost and a vanishing geometric allowance, the
finite old-graph projection payoff cancels against that same approximant.
The projection error vanishes by the original global `L¹` convergence. -/
theorem SmoothSequence.cost_add_finset_payoff_le_of_outside_repair
    {lam : ℝ} {E : Set PlanePoint} (A B : SmoothSequence)
    (hconv : A.ConvergesTo E)
    {ι : Type*} (s : Finset ι)
    (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    {W : Set PlanePoint} (hW : MeasurableSet W)
    (hsub : ∀ i ∈ s, (P i).window ⊆ W)
    (hE : MeasurableSet E) (newCost : ENNReal)
    {seam : ℕ → ENNReal} (hseam : Tendsto seam atTop (𝓝 0))
    (hrepair : ∀ n,
      smoothCost lam (B.carrier n) ≤
        smoothCostOn lam (A.carrier n) Wᶜ + newCost + seam n) :
    B.cost lam + ∑ i ∈ s, (P i).payoff ≤
      A.cost lam + newCost := by
  let C : ENNReal := ∑ i ∈ s, (P i).errorCoefficient
  have hC : C ≠ ⊤ := by
    dsimp only [C]
    apply ENNReal.sum_ne_top.2
    intro i hi
    rw [RigidProjectionPatch.errorCoefficient]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top
      (ENNReal.ofReal_pos.2 (P i).rho_pos).ne'
  have herr : Tendsto
      (fun n => C * characteristicDistance (A.carrier n) E)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hconv (Or.inr hC)
  have hallowance : Tendsto
      (fun n => seam n +
        C * characteristicDistance (A.carrier n) E)
      atTop (𝓝 0) := by
    simpa using hseam.add herr
  apply B.cost_add_le_of_pointwise_add_allowance A
    (∑ i ∈ s, (P i).payoff) newCost hallowance
  intro n
  have hcancel :=
    RigidProjectionPatch.finset_sum_payoff_add_compl_le_smoothCost_add_error
      s P hpair hW hsub hE (A.smooth n).isOpen
  calc
    smoothCost lam (B.carrier n) + ∑ i ∈ s, (P i).payoff ≤
        (smoothCostOn lam (A.carrier n) Wᶜ + newCost + seam n) +
          ∑ i ∈ s, (P i).payoff :=
      add_le_add (hrepair n) le_rfl
    _ = ((∑ i ∈ s, (P i).payoff) +
          smoothCostOn lam (A.carrier n) Wᶜ) + newCost + seam n := by
      ac_rfl
    _ ≤ (smoothCost lam (A.carrier n) +
          C * characteristicDistance (A.carrier n) E) +
          newCost + seam n := by
      gcongr
    _ = smoothCost lam (A.carrier n) + newCost +
          (seam n + C * characteristicDistance (A.carrier n) E) := by
      ac_rfl


/-- The complete artificial cutting trace of a raw splice.  Besides input
frontiers on the cut, it retains every cutting point where the two membership
labels disagree. -/
def spliceCutTrace (U G W : Set PlanePoint) : Set PlanePoint :=
  frontier W ∩ (frontier U ∪ frontier G ∪ (U ∆ G))

/-- Canonical open representative of a raw splice.  Taking the interior keeps
the actual local gluing behavior on a cut face: unlike the union of the two
strict-side pieces, it does not create a slit where both inputs occupy a
neighborhood of the face. -/
def openSpliceIn (U G W : Set PlanePoint) : Set PlanePoint :=
  interior (spliceIn U G W)

theorem isOpen_openSpliceIn (U G W : Set PlanePoint) :
    IsOpen (openSpliceIn U G W) :=
  isOpen_interior

lemma openSpliceIn_subset_spliceIn (U G W : Set PlanePoint) :
    openSpliceIn U G W ⊆ spliceIn U G W :=
  interior_subset

/-- When both input carriers are open, every raw-splice point lost by passing
to the canonical open representative lies on the cutting frontier. -/
theorem spliceIn_diff_openSpliceIn_subset_frontier
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G) :
    spliceIn U G W \ openSpliceIn U G W ⊆ frontier W := by
  intro p hp
  by_contra hpFrontier
  have hpRegion : p ∈ interior W ∪ interior Wᶜ := by
    have hpCompl : p ∈ (frontier W)ᶜ := hpFrontier
    rwa [compl_frontier_eq_union_interior] at hpCompl
  rcases hpRegion with hpInside | hpOutside
  · apply hp.2
    have hlocal : G ∩ interior W ⊆ spliceIn U G W := by
      intro q hq
      exact ((Set.ext_iff.mp
        (spliceIn_inter_interior U G W) q).mpr hq).1
    have hpG : p ∈ G :=
      ((Set.ext_iff.mp (spliceIn_inter_interior U G W) p).mp
        ⟨hp.1, hpInside⟩).1
    exact interior_maximal hlocal (hG.inter isOpen_interior)
      ⟨hpG, hpInside⟩
  · apply hp.2
    have hlocal : U ∩ interior Wᶜ ⊆ spliceIn U G W := by
      intro q hq
      exact ((Set.ext_iff.mp
        (spliceIn_inter_interior_compl U G W) q).mpr hq).1
    have hpU : p ∈ U :=
      ((Set.ext_iff.mp (spliceIn_inter_interior_compl U G W) p).mp
        ⟨hp.1, hpOutside⟩).1
    exact interior_maximal hlocal (hU.inter isOpen_interior)
      ⟨hpU, hpOutside⟩

/-- A regular-closed cutting window makes the raw splice dense in its
canonical open representative.  This is the topology needed to preserve the
complete frontier while repairing a non-open closed-window splice. -/
theorem spliceIn_subset_closure_openSpliceIn
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W) :
    spliceIn U G W ⊆ closure (openSpliceIn U G W) := by
  have hOutside :
      U ∩ Wᶜ ⊆ openSpliceIn U G W := by
    intro p hp
    change p ∈ interior (spliceIn U G W)
    exact interior_maximal (s := spliceIn U G W) (t := U ∩ Wᶜ)
      (fun _ hq => Or.inl hq) (hU.inter hW.isOpen_compl) hp
  have hInside :
      G ∩ interior W ⊆ openSpliceIn U G W := by
    intro p hp
    change p ∈ interior (spliceIn U G W)
    exact interior_maximal (s := spliceIn U G W) (t := G ∩ interior W)
      (fun _ hq => Or.inr ⟨hq.1, interior_subset hq.2⟩)
      (hG.inter isOpen_interior) hp
  intro p hp
  rcases hp with hpOutside | hpInside
  · exact subset_closure (hOutside ⟨hpOutside.1, hpOutside.2⟩)
  · rcases hpInside with ⟨hpG, hpW⟩
    by_cases hpInterior : p ∈ interior W
    · exact subset_closure (hInside ⟨hpG, hpInterior⟩)
    · have hpClosure : p ∈ closure (interior W) := by
        rw [hregular]
        exact hpW
      have hpLocal : p ∈ closure (interior W ∩ G) :=
        hG.closure_inter ⟨hpClosure, hpG⟩
      apply closure_mono _ hpLocal
      intro q hq
      exact hInside ⟨hq.2, hq.1⟩

theorem closure_openSpliceIn_eq_closure_spliceIn
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W) :
    closure (openSpliceIn U G W) = closure (spliceIn U G W) := by
  apply Subset.antisymm
  · exact closure_mono (openSpliceIn_subset_spliceIn U G W)
  · exact closure_minimal
      (spliceIn_subset_closure_openSpliceIn hU hG hW hregular)
      isClosed_closure

/-- Passing from a closed-window raw splice to its canonical open
representative preserves the complete topological frontier exactly. -/
theorem frontier_openSpliceIn_eq_frontier_spliceIn
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W) :
    frontier (openSpliceIn U G W) = frontier (spliceIn U G W) := by
  rw [frontier, frontier,
    closure_openSpliceIn_eq_closure_spliceIn hU hG hW hregular]
  simp only [openSpliceIn, interior_interior]

/-- The canonical open representative differs from the literal splice only on
the cutting frontier.  In particular, a planar-null cutting frontier makes the
two representatives equal almost everywhere. -/
theorem openSpliceIn_ae_eq_spliceIn
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hfrontier : volume (frontier W) = 0) :
    openSpliceIn U G W =ᵐ[volume] spliceIn U G W := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpOpen, hpNotSplice⟩
      exact (hpNotSplice (openSpliceIn_subset_spliceIn U G W hpOpen)).elim
    · exact measure_empty
  · exact measure_mono_null
      (spliceIn_diff_openSpliceIn_subset_frontier hU hG) hfrontier

/-- Replacing a planar-null-frontier raw splice by its canonical open
representative leaves every characteristic-function distance unchanged. -/
theorem characteristicDistance_openSpliceIn_eq_spliceIn
    {U G W F : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hfrontier : volume (frontier W) = 0) :
    characteristicDistance (openSpliceIn U G W) F =
      characteristicDistance (spliceIn U G W) F := by
  unfold characteristicDistance
  exact measure_congr
    ((openSpliceIn_ae_eq_spliceIn hU hG hfrontier).symmDiff (ae_eq_refl F))



/-- Full topological frontier accounting for raw cut-and-paste.  Away from the
cutting frontier, locality gives the old or inserted frontier exactly.  On the
cutting frontier, a new boundary can occur only at an input frontier or where
the two input membership labels disagree. -/
theorem frontier_spliceIn_subset_piecewise (U G W : Set PlanePoint) :
    frontier (spliceIn U G W) ⊆
      (frontier U ∩ interior Wᶜ) ∪
        (frontier G ∩ interior W) ∪ spliceCutTrace U G W := by
  intro p hp
  by_cases hpW : p ∈ frontier W
  · refine Or.inr ⟨hpW, ?_⟩
    by_cases hpInputs : p ∈ frontier U ∪ frontier G
    · exact Or.inl hpInputs
    · refine Or.inr ?_
      by_contra hpDiff
      have hpNotU : p ∉ frontier U := fun h => hpInputs (Or.inl h)
      have hpNotG : p ∉ frontier G := fun h => hpInputs (Or.inr h)
      have hlabels : p ∈ U ↔ p ∈ G := by
        simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hpDiff
        exact ⟨hpDiff.1, hpDiff.2⟩
      have hpU : p ∈ interior U ∪ interior Uᶜ := by
        have : p ∈ (frontier U)ᶜ := hpNotU
        rwa [compl_frontier_eq_union_interior] at this
      have hpG : p ∈ interior G ∪ interior Gᶜ := by
        have : p ∈ (frontier G)ᶜ := hpNotG
        rwa [compl_frontier_eq_union_interior] at this
      rcases hpU with hpUint | hpUcint
      · rcases hpG with hpGint | hpGcint
        · have hopen : IsOpen (interior U ∩ interior G) :=
            isOpen_interior.inter isOpen_interior
          have hsub :
              interior U ∩ interior G ⊆ spliceIn U G W := by
            intro q hq
            by_cases hqW : q ∈ W
            · exact Or.inr ⟨interior_subset hq.2, hqW⟩
            · exact Or.inl ⟨interior_subset hq.1, hqW⟩
          have hpInt : p ∈ interior (spliceIn U G W) :=
            interior_maximal hsub hopen ⟨hpUint, hpGint⟩
          exact Set.disjoint_left.1 disjoint_interior_frontier hpInt hp
        · exact (interior_subset hpGcint)
            (hlabels.mp (interior_subset hpUint))
      · rcases hpG with hpGint | hpGcint
        · exact (interior_subset hpUcint)
            (hlabels.mpr (interior_subset hpGint))
        · have hopen : IsOpen (interior Uᶜ ∩ interior Gᶜ) :=
            isOpen_interior.inter isOpen_interior
          have hsub :
              interior Uᶜ ∩ interior Gᶜ ⊆ (spliceIn U G W)ᶜ := by
            intro q hq hqSplice
            rcases hqSplice with hqOutside | hqInside
            · exact (interior_subset hq.1) hqOutside.1
            · exact (interior_subset hq.2) hqInside.1
          have hpInt : p ∈ interior (spliceIn U G W)ᶜ :=
            interior_maximal hsub hopen ⟨hpUcint, hpGcint⟩
          have hpFrontier : p ∈ frontier (spliceIn U G W)ᶜ := by
            simpa only [frontier_compl] using hp
          exact Set.disjoint_left.1 disjoint_interior_frontier hpInt hpFrontier
  · have hpRegion : p ∈ interior W ∪ interior Wᶜ := by
      have : p ∈ (frontier W)ᶜ := hpW
      rwa [compl_frontier_eq_union_interior] at this
    rcases hpRegion with hpInside | hpOutside
    · have hfrontier :
          frontier (spliceIn U G W) ∩ interior W =
            frontier G ∩ interior W :=
        frontier_inter_eq_of_inter_open_eq isOpen_interior
          (spliceIn_inter_interior U G W)
      have hpG : p ∈ frontier G ∩ interior W := by
        rw [← hfrontier]
        exact ⟨hp, hpInside⟩
      exact Or.inl (Or.inr hpG)
    · have hfrontier :
          frontier (spliceIn U G W) ∩ interior Wᶜ =
            frontier U ∩ interior Wᶜ :=
        frontier_inter_eq_of_inter_open_eq isOpen_interior
          (spliceIn_inter_interior_compl U G W)
      have hpU : p ∈ frontier U ∩ interior Wᶜ := by
        rw [← hfrontier]
        exact ⟨hp, hpOutside⟩
      exact Or.inl (Or.inl hpU)

/-- Density-weighted Euclidean one-dimensional cost of an arbitrary coordinate trace. -/
def weightedTraceCost (lam : ℝ) (S : Set PlanePoint) : ENNReal :=
  ∫⁻ z in planeEuclideanHomeomorph '' S,
    ENNReal.ofReal (euclideanStripDensity lam z)
      ∂(μH[1] : Measure EuclideanPlane)

lemma smoothCost_eq_weightedTraceCost_frontier (lam : ℝ) (U : Set PlanePoint) :
    smoothCost lam U = weightedTraceCost lam (frontier U) := by
  unfold weightedTraceCost smoothCost FrontierMeasure
  change
    (∫⁻ p, (ENNReal.ofReal ∘ StripDensity lam) p
      ∂Measure.map planeEuclideanHomeomorph.symm
        ((μH[1] : Measure EuclideanPlane).restrict
          (frontier (planeEuclideanHomeomorph '' U)))) = _
  rw [MeasureTheory.lintegral_map
    (ENNReal.continuous_ofReal.measurable.comp (measurable_stripDensity lam))
    planeEuclideanHomeomorph.symm.continuous.measurable]
  rw [← planeEuclideanHomeomorph.image_frontier]
  rfl

theorem smoothCost_openSpliceIn_eq_smoothCost_spliceIn
    (lam : ℝ) {U G W : Set PlanePoint}
    (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W) :
    smoothCost lam (openSpliceIn U G W) =
      smoothCost lam (spliceIn U G W) := by
  rw [smoothCost_eq_weightedTraceCost_frontier,
    smoothCost_eq_weightedTraceCost_frontier,
    frontier_openSpliceIn_eq_frontier_spliceIn hU hG hW hregular]

lemma smoothCostOn_eq_weightedTraceCost_frontier_inter
    (lam : ℝ) (U : Set PlanePoint) {W : Set PlanePoint}
    (hW : MeasurableSet W) :
    smoothCostOn lam U W = weightedTraceCost lam (frontier U ∩ W) := by
  unfold smoothCostOn weightedTraceCost FrontierMeasure
  change
    (∫⁻ p in W, (ENNReal.ofReal ∘ StripDensity lam) p
      ∂Measure.map planeEuclideanHomeomorph.symm
        ((μH[1] : Measure EuclideanPlane).restrict
          (frontier (planeEuclideanHomeomorph '' U)))) = _
  rw [MeasureTheory.setLIntegral_map hW
    (ENNReal.continuous_ofReal.measurable.comp (measurable_stripDensity lam))
    planeEuclideanHomeomorph.symm.continuous.measurable]
  change
    (∫⁻ z, ENNReal.ofReal (euclideanStripDensity lam z)
      ∂((μH[1] : Measure EuclideanPlane).restrict
        (frontier (planeEuclideanHomeomorph '' U))).restrict
          (planeEuclideanHomeomorph.symm ⁻¹' W)) =
      ∫⁻ z, ENNReal.ofReal (euclideanStripDensity lam z)
        ∂(μH[1] : Measure EuclideanPlane).restrict
          (planeEuclideanHomeomorph '' (frontier U ∩ W))
  rw [Measure.restrict_restrict
      (planeEuclideanHomeomorph.symm.continuous.measurable hW),
    planeEuclideanHomeomorph.preimage_symm,
    Set.image_inter planeEuclideanHomeomorph.injective,
    planeEuclideanHomeomorph.image_frontier, inter_comm]

lemma weightedTraceCost_mono (lam : ℝ) {S T : Set PlanePoint} (hST : S ⊆ T) :
    weightedTraceCost lam S ≤ weightedTraceCost lam T := by
  unfold weightedTraceCost
  exact MeasureTheory.lintegral_mono_set (image_mono hST)

lemma weightedTraceCost_union_le (lam : ℝ) (S T : Set PlanePoint) :
    weightedTraceCost lam (S ∪ T) ≤
      weightedTraceCost lam S + weightedTraceCost lam T := by
  unfold weightedTraceCost
  rw [image_union]
  exact MeasureTheory.lintegral_union_le _ _ _

lemma weightedTraceCost_iUnion_three_le (lam : ℝ)
    (A B C : Set PlanePoint) :
    weightedTraceCost lam (A ∪ B ∪ C) ≤
      weightedTraceCost lam A + weightedTraceCost lam B +
        weightedTraceCost lam C := by
  calc
    weightedTraceCost lam (A ∪ B ∪ C) ≤
        weightedTraceCost lam (A ∪ B) + weightedTraceCost lam C :=
      weightedTraceCost_union_le lam (A ∪ B) C
    _ ≤ (weightedTraceCost lam A + weightedTraceCost lam B) +
        weightedTraceCost lam C :=
      add_le_add (weightedTraceCost_union_le lam A B) le_rfl

lemma weightedTraceCost_le_const_mul_hausdorff
    (lam : ℝ) (S : Set PlanePoint) (C : ENNReal)
    (hbound : ∀ z ∈ planeEuclideanHomeomorph '' S,
      ENNReal.ofReal (euclideanStripDensity lam z) ≤ C) :
    weightedTraceCost lam S ≤
      C * (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' S) := by
  unfold weightedTraceCost
  calc
    (∫⁻ z in planeEuclideanHomeomorph '' S,
        ENNReal.ofReal (euclideanStripDensity lam z)
        ∂(μH[1] : Measure EuclideanPlane)) ≤
      ∫⁻ _z in planeEuclideanHomeomorph '' S, C
        ∂(μH[1] : Measure EuclideanPlane) := by
          apply MeasureTheory.setLIntegral_mono measurable_const
          exact hbound
    _ = C * (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' S) := by simp

lemma weightedTraceCost_le_density_mul_hausdorff
    {lam : ℝ} (hlam : 1 < lam) (S : Set PlanePoint) :
    weightedTraceCost lam S ≤
      ENNReal.ofReal lam * (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' S) := by
  apply weightedTraceCost_le_const_mul_hausdorff lam S (ENNReal.ofReal lam)
  intro z hz
  apply ENNReal.ofReal_le_ofReal
  unfold euclideanStripDensity StripDensity
  split_ifs <;> linarith

/-- Finite localized weighted cost implies finite localized complete-frontier
measure because the strip density is everywhere at least one. -/
theorem frontierMeasure_ne_top_of_smoothCostOn_ne_top
    {lam : ℝ} (hlam : 1 < lam) (U K : Set PlanePoint)
    (hK : MeasurableSet K) (hcost : smoothCostOn lam U K ≠ ⊤) :
    FrontierMeasure U K ≠ ⊤ := by
  have hlower : ∀ p ∈ K, (1 : ℝ) ≤ StripDensity lam p := by
    intro p _hp
    unfold StripDensity
    split_ifs <;> linarith
  have hle : FrontierMeasure U K ≤ smoothCostOn lam U K := by
    unfold smoothCostOn
    simpa only [ENNReal.ofReal_one, one_mul] using
      ofReal_mul_frontierMeasure_le_setLIntegral hK lam 1 hlower
  intro htop
  rw [htop] at hle
  exact hcost (top_unique hle)

/-- A vertical cut through a constant-density CMV plane costs at most `lam`
times its one-dimensional membership mismatch. -/
theorem weightedTraceCost_verticalLine_inter_le
    {lam : ℝ} (hlam : 1 < lam) (S : Set PlanePoint) (x : ℝ) :
    weightedTraceCost lam (verticalLine x ∩ S) ≤
      ENNReal.ofReal lam * volume (verticalSection S x) := by
  simpa only [hausdorffMeasure_verticalLine_inter] using
    weightedTraceCost_le_density_mul_hausdorff hlam (verticalLine x ∩ S)

/-- The averaging seam selector can simultaneously avoid any prescribed
countable set of horizontal coordinates. -/
theorem exists_verticalSliceVolume_le_average_avoiding
    {S : Set PlanePoint} (hS : MeasurableSet S) (B : Set ℝ)
    (hB : B.Countable) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, x ∉ B ∧
      verticalSliceVolume S x ≤ volume S / ENNReal.ofReal (b - a) := by
  let J : Set ℝ := Ioo a b \ B
  have hJ : MeasurableSet J :=
    isOpen_Ioo.measurableSet.diff hB.measurableSet
  have hvolJ : volume J = volume (Ioo a b) := by
    exact measure_sdiff_null (s := Ioo a b) (hB.measure_zero volume)
  have hvol0 : volume J ≠ 0 := by
    rw [hvolJ, Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab))
  have hvolTop : volume J ≠ ⊤ := by
    rw [hvolJ]
    exact measure_Ioo_lt_top.ne
  have hmeas : AEMeasurable (verticalSliceVolume S)
      (volume.restrict J) :=
    (measurable_verticalSliceVolume hS).aemeasurable
  obtain ⟨x, hx, hxle⟩ :=
    exists_le_setLAverage hvol0 hvolTop hmeas
  refine ⟨x, hx.1, hx.2, hxle.trans ?_⟩
  rw [setLAverage_eq, hvolJ, Real.volume_Ioo]
  gcongr
  calc
    (∫⁻ y in J, verticalSliceVolume S y) ≤
        ∫⁻ y, verticalSliceVolume S y :=
      setLIntegral_le_lintegral _ _
    _ = volume S := (volume_eq_lintegral_verticalSliceVolume hS).symm

/-- Vertical averaging can avoid an arbitrary volume-null exceptional set,
not merely a countable set. -/
theorem exists_verticalSliceVolume_le_average_avoiding_null
    {S : Set PlanePoint} (hS : MeasurableSet S) (B : Set ℝ)
    (hB : volume B = 0) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, x ∉ B ∧
      verticalSliceVolume S x ≤ volume S / ENNReal.ofReal (b - a) := by
  let Bm : Set ℝ := toMeasurable volume B
  let J : Set ℝ := Ioo a b \ Bm
  have hBm : MeasurableSet Bm := measurableSet_toMeasurable volume B
  have hvolBm : volume Bm = 0 := by
    simpa only [Bm, measure_toMeasurable] using hB
  have hJ : MeasurableSet J :=
    isOpen_Ioo.measurableSet.diff hBm
  have hvolJ : volume J = volume (Ioo a b) :=
    measure_sdiff_null (s := Ioo a b) hvolBm
  have hvol0 : volume J ≠ 0 := by
    rw [hvolJ, Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab))
  have hvolTop : volume J ≠ ⊤ := by
    rw [hvolJ]
    exact measure_Ioo_lt_top.ne
  have hmeas : AEMeasurable (verticalSliceVolume S)
      (volume.restrict J) :=
    (measurable_verticalSliceVolume hS).aemeasurable
  obtain ⟨x, hx, hxle⟩ :=
    exists_le_setLAverage hvol0 hvolTop hmeas
  refine ⟨x, hx.1, ?_, hxle.trans ?_⟩
  · exact fun hxB => hx.2 (subset_toMeasurable volume B hxB)
  · rw [setLAverage_eq, hvolJ, Real.volume_Ioo]
    gcongr
    calc
      (∫⁻ y in J, verticalSliceVolume S y) ≤
          ∫⁻ y, verticalSliceVolume S y :=
        setLIntegral_le_lintegral _ _
      _ = volume S := (volume_eq_lintegral_verticalSliceVolume hS).symm

lemma measurableSet_verticalLine (x : ℝ) : MeasurableSet (verticalLine x) := by
  exact (isClosed_singleton.preimage continuous_fst).measurableSet

/-- In a finite-frontier-measure window, only countably many vertical fibers
carry positive old-frontier mass. -/
theorem countable_pos_frontierMeasure_verticalLine_inter
    (U K : Set PlanePoint) (hK : MeasurableSet K)
    (hfinite : FrontierMeasure U K ≠ ⊤) :
    {x : ℝ | 0 < FrontierMeasure U (verticalLine x ∩ K)}.Countable := by
  let A : ℝ → Set PlanePoint := fun x => verticalLine x ∩ K
  have hmeas : ∀ x, MeasurableSet (A x) := fun x =>
    (measurableSet_verticalLine x).inter hK
  have hdisjoint : Pairwise (Disjoint on A) := by
    intro x y hxy
    change Disjoint (A x) (A y)
    rw [Set.disjoint_left]
    intro p hpx hpy
    apply hxy
    exact hpx.1.symm.trans hpy.1
  have hunion : (⋃ x, A x) = K := by
    ext p
    simp only [mem_iUnion, A, mem_inter_iff]
    constructor
    · rintro ⟨_x, _hpx, hpK⟩
      exact hpK
    · intro hpK
      exact ⟨p.1, rfl, hpK⟩
  have hunionFinite : FrontierMeasure U (⋃ x, A x) ≠ ⊤ := by
    rw [hunion]
    exact hfinite
  simpa only [A] using
    Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
      (FrontierMeasure U) hmeas hdisjoint hunionFinite

/-- A frontier-null measurable trace has zero density-weighted cost. -/
theorem weightedTraceCost_frontier_inter_eq_zero
    (lam : ℝ) (U Q : Set PlanePoint) (hQ : MeasurableSet Q)
    (hzero : FrontierMeasure U Q = 0) :
    weightedTraceCost lam (frontier U ∩ Q) = 0 := by
  rw [← smoothCostOn_eq_weightedTraceCost_frontier_inter lam U hQ]
  exact setLIntegral_measure_zero Q _ hzero

/-- Select one low-mismatch vertical cut avoiding every positive-frontier
fiber of two inputs in a finite-measure localization window. -/
theorem exists_verticalSliceVolume_le_average_frontier_null
    (U G K S : Set PlanePoint) (hK : MeasurableSet K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b,
      FrontierMeasure U (verticalLine x ∩ K) = 0 ∧
      FrontierMeasure G (verticalLine x ∩ K) = 0 ∧
      verticalSliceVolume S x ≤ volume S / ENNReal.ofReal (b - a) := by
  let BU : Set ℝ :=
    {x | 0 < FrontierMeasure U (verticalLine x ∩ K)}
  let BG : Set ℝ :=
    {x | 0 < FrontierMeasure G (verticalLine x ∩ K)}
  have hBU : BU.Countable := by
    exact countable_pos_frontierMeasure_verticalLine_inter U K hK hfiniteU
  have hBG : BG.Countable := by
    exact countable_pos_frontierMeasure_verticalLine_inter G K hK hfiniteG
  obtain ⟨x, hx, hxgood, hxbound⟩ :=
    exists_verticalSliceVolume_le_average_avoiding
      hS (BU ∪ BG) (hBU.union hBG) hab
  refine ⟨x, hx, ?_, ?_, hxbound⟩
  · apply bot_unique
    rw [← not_lt]
    intro hxpos
    apply hxgood
    exact Or.inl hxpos
  · apply bot_unique
    rw [← not_lt]
    intro hxpos
    apply hxgood
    exact Or.inr hxpos
/-- One horizontal fiber of a planar set. -/
def horizontalSection (S : Set PlanePoint) (y : ℝ) : Set ℝ :=
  (fun x => (x, y)) ⁻¹' S

/-- The source horizontal line at vertical coordinate `y`. -/
def horizontalLine (y : ℝ) : Set PlanePoint := {p | p.2 = y}

/-- The Euclidean realization of one source horizontal line. -/
def euclideanHorizontalEmbedding (y : ℝ) : ℝ → EuclideanPlane :=
  fun x => planeEuclideanHomeomorph (x, y)

lemma isometry_euclideanHorizontalEmbedding (y : ℝ) :
    Isometry (euclideanHorizontalEmbedding y) := by
  apply Isometry.of_dist_eq
  intro x z
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  norm_num [euclideanHorizontalEmbedding, Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs]

theorem hausdorffMeasure_horizontalLine_inter (S : Set PlanePoint) (y : ℝ) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (horizontalLine y ∩ S)) =
      volume (horizontalSection S y) := by
  have himage :
      planeEuclideanHomeomorph '' (horizontalLine y ∩ S) =
        euclideanHorizontalEmbedding y '' horizontalSection S y := by
    ext q
    constructor
    · rintro ⟨⟨px, py⟩, ⟨hpy, hpS⟩, rfl⟩
      change py = y at hpy
      subst py
      exact ⟨px, hpS, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(x, y), ⟨rfl, hx⟩, rfl⟩
  rw [himage]
  calc
    (μH[1] : Measure EuclideanPlane)
        (euclideanHorizontalEmbedding y '' horizontalSection S y) =
      (μH[1] : Measure ℝ) (horizontalSection S y) :=
        (isometry_euclideanHorizontalEmbedding y).hausdorffMeasure_image
          (Or.inl (by norm_num)) _
    _ = volume (horizontalSection S y) := by rw [hausdorffMeasure_real]

def horizontalSliceVolume (S : Set PlanePoint) (y : ℝ) : ENNReal :=
  volume (horizontalSection S y)

lemma measurable_horizontalSliceVolume {S : Set PlanePoint}
    (hS : MeasurableSet S) :
    Measurable (horizontalSliceVolume S) :=
  measurable_measure_prodMk_right hS

lemma volume_eq_lintegral_horizontalSliceVolume {S : Set PlanePoint}
    (hS : MeasurableSet S) :
    volume S = ∫⁻ y : ℝ, horizontalSliceVolume S y := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl

theorem exists_horizontalSliceVolume_le_average
    {S : Set PlanePoint} (hS : MeasurableSet S) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      horizontalSliceVolume S y ≤ volume S / ENNReal.ofReal (b - a) := by
  have hmeas : AEMeasurable (horizontalSliceVolume S)
      (volume.restrict (Ioo a b)) :=
    (measurable_horizontalSliceVolume hS).aemeasurable
  have hvol0 : volume (Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab))
  have hvolTop : volume (Ioo a b) ≠ ⊤ := measure_Ioo_lt_top.ne
  obtain ⟨y, hy, hyle⟩ := exists_le_setLAverage hvol0 hvolTop hmeas
  refine ⟨y, hy, hyle.trans ?_⟩
  rw [setLAverage_eq, Real.volume_Ioo]
  gcongr
  calc
    (∫⁻ z in Ioo a b, horizontalSliceVolume S z) ≤
        ∫⁻ z, horizontalSliceVolume S z :=
      setLIntegral_le_lintegral _ _
    _ = volume S := (volume_eq_lintegral_horizontalSliceVolume hS).symm

/-- Horizontal averaging with a prescribed countable exceptional set removed. -/
theorem exists_horizontalSliceVolume_le_average_avoiding
    {S : Set PlanePoint} (hS : MeasurableSet S) (B : Set ℝ)
    (hB : B.Countable) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, y ∉ B ∧
      horizontalSliceVolume S y ≤ volume S / ENNReal.ofReal (b - a) := by
  let J : Set ℝ := Ioo a b \ B
  have hJ : MeasurableSet J :=
    isOpen_Ioo.measurableSet.diff hB.measurableSet
  have hvolJ : volume J = volume (Ioo a b) := by
    exact measure_sdiff_null (s := Ioo a b) (hB.measure_zero volume)
  have hvol0 : volume J ≠ 0 := by
    rw [hvolJ, Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab))
  have hvolTop : volume J ≠ ⊤ := by
    rw [hvolJ]
    exact measure_Ioo_lt_top.ne
  have hmeas : AEMeasurable (horizontalSliceVolume S)
      (volume.restrict J) :=
    (measurable_horizontalSliceVolume hS).aemeasurable
  obtain ⟨y, hy, hyle⟩ :=
    exists_le_setLAverage hvol0 hvolTop hmeas
  refine ⟨y, hy.1, hy.2, hyle.trans ?_⟩
  rw [setLAverage_eq, hvolJ, Real.volume_Ioo]
  gcongr
  calc
    (∫⁻ z in J, horizontalSliceVolume S z) ≤
        ∫⁻ z, horizontalSliceVolume S z :=
      setLIntegral_le_lintegral _ _
    _ = volume S := (volume_eq_lintegral_horizontalSliceVolume hS).symm

/-- Horizontal averaging can avoid an arbitrary volume-null exceptional set,
not merely a countable set. -/
theorem exists_horizontalSliceVolume_le_average_avoiding_null
    {S : Set PlanePoint} (hS : MeasurableSet S) (B : Set ℝ)
    (hB : volume B = 0) {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, y ∉ B ∧
      horizontalSliceVolume S y ≤ volume S / ENNReal.ofReal (b - a) := by
  let Bm : Set ℝ := toMeasurable volume B
  let J : Set ℝ := Ioo a b \ Bm
  have hBm : MeasurableSet Bm := measurableSet_toMeasurable volume B
  have hvolBm : volume Bm = 0 := by
    simpa only [Bm, measure_toMeasurable] using hB
  have hJ : MeasurableSet J :=
    isOpen_Ioo.measurableSet.diff hBm
  have hvolJ : volume J = volume (Ioo a b) :=
    measure_sdiff_null (s := Ioo a b) hvolBm
  have hvol0 : volume J ≠ 0 := by
    rw [hvolJ, Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.2 (sub_pos.mpr hab))
  have hvolTop : volume J ≠ ⊤ := by
    rw [hvolJ]
    exact measure_Ioo_lt_top.ne
  have hmeas : AEMeasurable (horizontalSliceVolume S)
      (volume.restrict J) :=
    (measurable_horizontalSliceVolume hS).aemeasurable
  obtain ⟨y, hy, hyle⟩ :=
    exists_le_setLAverage hvol0 hvolTop hmeas
  refine ⟨y, hy.1, ?_, hyle.trans ?_⟩
  · exact fun hyB => hy.2 (subset_toMeasurable volume B hyB)
  · rw [setLAverage_eq, hvolJ, Real.volume_Ioo]
    gcongr
    calc
      (∫⁻ z in J, horizontalSliceVolume S z) ≤
          ∫⁻ z, horizontalSliceVolume S z :=
        setLIntegral_le_lintegral _ _
      _ = volume S := (volume_eq_lintegral_horizontalSliceVolume hS).symm

lemma measurableSet_horizontalLine (y : ℝ) :
    MeasurableSet (horizontalLine y) := by
  exact (isClosed_singleton.preimage continuous_snd).measurableSet

/-- In a finite-frontier-measure window, only countably many horizontal
fibers carry positive old-frontier mass. -/
theorem countable_pos_frontierMeasure_horizontalLine_inter
    (U K : Set PlanePoint) (hK : MeasurableSet K)
    (hfinite : FrontierMeasure U K ≠ ⊤) :
    {y : ℝ | 0 < FrontierMeasure U (horizontalLine y ∩ K)}.Countable := by
  let A : ℝ → Set PlanePoint := fun y => horizontalLine y ∩ K
  have hmeas : ∀ y, MeasurableSet (A y) := fun y =>
    (measurableSet_horizontalLine y).inter hK
  have hdisjoint : Pairwise (Disjoint on A) := by
    intro x y hxy
    change Disjoint (A x) (A y)
    rw [Set.disjoint_left]
    intro p hpx hpy
    apply hxy
    exact hpx.1.symm.trans hpy.1
  have hunion : (⋃ y, A y) = K := by
    ext p
    simp only [mem_iUnion, A, mem_inter_iff]
    constructor
    · rintro ⟨_y, _hpy, hpK⟩
      exact hpK
    · intro hpK
      exact ⟨p.2, rfl, hpK⟩
  have hunionFinite : FrontierMeasure U (⋃ y, A y) ≠ ⊤ := by
    rw [hunion]
    exact hfinite
  simpa only [A] using
    Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
      (FrontierMeasure U) hmeas hdisjoint hunionFinite

/-- Select one low-mismatch horizontal cut avoiding every positive-frontier
fiber of two inputs in a finite-measure localization window. -/
theorem exists_horizontalSliceVolume_le_average_frontier_null
    (U G K S : Set PlanePoint) (hK : MeasurableSet K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      FrontierMeasure U (horizontalLine y ∩ K) = 0 ∧
      FrontierMeasure G (horizontalLine y ∩ K) = 0 ∧
      horizontalSliceVolume S y ≤ volume S / ENNReal.ofReal (b - a) := by
  let BU : Set ℝ :=
    {y | 0 < FrontierMeasure U (horizontalLine y ∩ K)}
  let BG : Set ℝ :=
    {y | 0 < FrontierMeasure G (horizontalLine y ∩ K)}
  have hBU : BU.Countable := by
    exact countable_pos_frontierMeasure_horizontalLine_inter U K hK hfiniteU
  have hBG : BG.Countable := by
    exact countable_pos_frontierMeasure_horizontalLine_inter G K hK hfiniteG
  obtain ⟨y, hy, hygood, hybound⟩ :=
    exists_horizontalSliceVolume_le_average_avoiding
      hS (BU ∪ BG) (hBU.union hBG) hab
  refine ⟨y, hy, ?_, ?_, hybound⟩
  · apply bot_unique
    rw [← not_lt]
    intro hypos
    apply hygood
    exact Or.inl hypos
  · apply bot_unique
    rw [← not_lt]
    intro hypos
    apply hygood
    exact Or.inr hypos
theorem weightedTraceCost_horizontalLine_inter_le
    {lam : ℝ} (hlam : 1 < lam) (S : Set PlanePoint) (y : ℝ) :
    weightedTraceCost lam (horizontalLine y ∩ S) ≤
      ENNReal.ofReal lam * volume (horizontalSection S y) := by
  simpa only [hausdorffMeasure_horizontalLine_inter] using
    weightedTraceCost_le_density_mul_hausdorff hlam (horizontalLine y ∩ S)

/-- If both localized input frontiers are null on a vertical fiber, the full
three-part cut trace there is paid entirely by the membership mismatch. -/
theorem weightedTraceCost_verticalCutInputsOn_le_of_frontier_null
    {lam : ℝ} (hlam : 1 < lam) (U G K : Set PlanePoint) (x : ℝ)
    (hK : MeasurableSet K)
    (hzeroU : FrontierMeasure U (verticalLine x ∩ K) = 0)
    (hzeroG : FrontierMeasure G (verticalLine x ∩ K) = 0) :
    weightedTraceCost lam
        ((verticalLine x ∩ K) ∩
          (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
      ENNReal.ofReal lam *
        verticalSliceVolume (K ∩ (U ∆ G)) x := by
  let Q := verticalLine x ∩ K
  have hQ : MeasurableSet Q := (measurableSet_verticalLine x).inter hK
  have hsubset :
      Q ∩ (frontier U ∪ frontier G ∪ (U ∆ G)) ⊆
        (frontier U ∩ Q) ∪ (frontier G ∩ Q) ∪
          (verticalLine x ∩ (K ∩ (U ∆ G))) := by
    intro p hp
    rcases hp with ⟨hpQ, hpFront | hpDiff⟩
    · rcases hpFront with hpU | hpG
      · exact Or.inl (Or.inl ⟨hpU, hpQ⟩)
      · exact Or.inl (Or.inr ⟨hpG, hpQ⟩)
    · exact Or.inr ⟨hpQ.1, hpQ.2, hpDiff⟩
  have hcostU : weightedTraceCost lam (frontier U ∩ Q) = 0 :=
    weightedTraceCost_frontier_inter_eq_zero lam U Q hQ hzeroU
  have hcostG : weightedTraceCost lam (frontier G ∩ Q) = 0 :=
    weightedTraceCost_frontier_inter_eq_zero lam G Q hQ hzeroG
  calc
    weightedTraceCost lam
        (Q ∩ (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
      weightedTraceCost lam
        ((frontier U ∩ Q) ∪ (frontier G ∩ Q) ∪
          (verticalLine x ∩ (K ∩ (U ∆ G)))) :=
      weightedTraceCost_mono lam hsubset
    _ ≤ weightedTraceCost lam (frontier U ∩ Q) +
          weightedTraceCost lam (frontier G ∩ Q) +
            weightedTraceCost lam
              (verticalLine x ∩ (K ∩ (U ∆ G))) :=
      weightedTraceCost_iUnion_three_le lam _ _ _
    _ ≤ ENNReal.ofReal lam *
          verticalSliceVolume (K ∩ (U ∆ G)) x := by
      rw [hcostU, hcostG, zero_add, zero_add]
      exact weightedTraceCost_verticalLine_inter_le
        hlam (K ∩ (U ∆ G)) x

/-- A finite localized frontier admits a vertical cut whose entire raw trace
is bounded by the averaged localized mismatch. -/
theorem exists_verticalCutInputsOn_le_average
    {lam : ℝ} (hlam : 1 < lam) (U G K : Set PlanePoint)
    (hU : MeasurableSet U) (hG : MeasurableSet G)
    (hK : MeasurableSet K)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b,
      weightedTraceCost lam
          ((verticalLine x ∩ K) ∩
            (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
        ENNReal.ofReal lam *
          (volume (K ∩ (U ∆ G)) / ENNReal.ofReal (b - a)) := by
  have hS : MeasurableSet (K ∩ (U ∆ G)) :=
    hK.inter (hU.symmDiff hG)
  obtain ⟨x, hx, hzeroU, hzeroG, hxbound⟩ :=
    exists_verticalSliceVolume_le_average_frontier_null
      U G K (K ∩ (U ∆ G)) hK hS hfiniteU hfiniteG hab
  refine ⟨x, hx, ?_⟩
  exact (weightedTraceCost_verticalCutInputsOn_le_of_frontier_null
    hlam U G K x hK hzeroU hzeroG).trans
      (by simpa only [mul_comm] using
        mul_le_mul_left hxbound (ENNReal.ofReal lam))

/-- Horizontal analogue of the localized frontier-null cut estimate. -/
theorem weightedTraceCost_horizontalCutInputsOn_le_of_frontier_null
    {lam : ℝ} (hlam : 1 < lam) (U G K : Set PlanePoint) (y : ℝ)
    (hK : MeasurableSet K)
    (hzeroU : FrontierMeasure U (horizontalLine y ∩ K) = 0)
    (hzeroG : FrontierMeasure G (horizontalLine y ∩ K) = 0) :
    weightedTraceCost lam
        ((horizontalLine y ∩ K) ∩
          (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
      ENNReal.ofReal lam *
        horizontalSliceVolume (K ∩ (U ∆ G)) y := by
  let Q := horizontalLine y ∩ K
  have hQ : MeasurableSet Q := (measurableSet_horizontalLine y).inter hK
  have hsubset :
      Q ∩ (frontier U ∪ frontier G ∪ (U ∆ G)) ⊆
        (frontier U ∩ Q) ∪ (frontier G ∩ Q) ∪
          (horizontalLine y ∩ (K ∩ (U ∆ G))) := by
    intro p hp
    rcases hp with ⟨hpQ, hpFront | hpDiff⟩
    · rcases hpFront with hpU | hpG
      · exact Or.inl (Or.inl ⟨hpU, hpQ⟩)
      · exact Or.inl (Or.inr ⟨hpG, hpQ⟩)
    · exact Or.inr ⟨hpQ.1, hpQ.2, hpDiff⟩
  have hcostU : weightedTraceCost lam (frontier U ∩ Q) = 0 :=
    weightedTraceCost_frontier_inter_eq_zero lam U Q hQ hzeroU
  have hcostG : weightedTraceCost lam (frontier G ∩ Q) = 0 :=
    weightedTraceCost_frontier_inter_eq_zero lam G Q hQ hzeroG
  calc
    weightedTraceCost lam
        (Q ∩ (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
      weightedTraceCost lam
        ((frontier U ∩ Q) ∪ (frontier G ∩ Q) ∪
          (horizontalLine y ∩ (K ∩ (U ∆ G)))) :=
      weightedTraceCost_mono lam hsubset
    _ ≤ weightedTraceCost lam (frontier U ∩ Q) +
          weightedTraceCost lam (frontier G ∩ Q) +
            weightedTraceCost lam
              (horizontalLine y ∩ (K ∩ (U ∆ G))) :=
      weightedTraceCost_iUnion_three_le lam _ _ _
    _ ≤ ENNReal.ofReal lam *
          horizontalSliceVolume (K ∩ (U ∆ G)) y := by
      rw [hcostU, hcostG, zero_add, zero_add]
      exact weightedTraceCost_horizontalLine_inter_le
        hlam (K ∩ (U ∆ G)) y

/-- A finite localized frontier admits a horizontal cut whose entire raw trace
is bounded by the averaged localized mismatch. -/
theorem exists_horizontalCutInputsOn_le_average
    {lam : ℝ} (hlam : 1 < lam) (U G K : Set PlanePoint)
    (hU : MeasurableSet U) (hG : MeasurableSet G)
    (hK : MeasurableSet K)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      weightedTraceCost lam
          ((horizontalLine y ∩ K) ∩
            (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
        ENNReal.ofReal lam *
          (volume (K ∩ (U ∆ G)) / ENNReal.ofReal (b - a)) := by
  have hS : MeasurableSet (K ∩ (U ∆ G)) :=
    hK.inter (hU.symmDiff hG)
  obtain ⟨y, hy, hzeroU, hzeroG, hybound⟩ :=
    exists_horizontalSliceVolume_le_average_frontier_null
      U G K (K ∩ (U ∆ G)) hK hS hfiniteU hfiniteG hab
  refine ⟨y, hy, ?_⟩
  exact (weightedTraceCost_horizontalCutInputsOn_le_of_frontier_null
    hlam U G K y hK hzeroU hzeroG).trans
      (by simpa only [mul_comm] using
        mul_le_mul_left hybound (ENNReal.ofReal lam))
lemma weightedTraceCost_iUnion_four_le (lam : ℝ)
    (A B C D : Set PlanePoint) :
    weightedTraceCost lam (A ∪ B ∪ C ∪ D) ≤
      weightedTraceCost lam A + weightedTraceCost lam B +
        weightedTraceCost lam C + weightedTraceCost lam D := by
  calc
    weightedTraceCost lam (A ∪ B ∪ C ∪ D) ≤
        weightedTraceCost lam (A ∪ B ∪ C) +
          weightedTraceCost lam D :=
      weightedTraceCost_union_le lam (A ∪ B ∪ C) D
    _ ≤ (weightedTraceCost lam A + weightedTraceCost lam B +
          weightedTraceCost lam C) + weightedTraceCost lam D :=
      add_le_add (weightedTraceCost_iUnion_three_le lam A B C) le_rfl

/-- Compact rectangular cutting window with four explicitly charged faces. -/
def closedCutRectangle (l r d u : ℝ) : Set PlanePoint :=
  Icc l r ×ˢ Icc d u

theorem frontier_closedCutRectangle_subset_lines
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u) :
    frontier (closedCutRectangle l r d u) ⊆
      verticalLine l ∪ verticalLine r ∪ horizontalLine d ∪ horizontalLine u := by
  rw [closedCutRectangle, frontier_prod_eq, closure_Icc, closure_Icc,
    frontier_Icc hlr.le, frontier_Icc hdu.le]
  intro p hp
  simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff] at hp ⊢
  rcases hp with hpHorizontal | hpVertical
  · rcases hpHorizontal.2 with hpD | hpU
    · exact Or.inl (Or.inr hpD)
    · exact Or.inr hpU
  · rcases hpVertical.1 with hpL | hpR
    · exact Or.inl (Or.inl (Or.inl hpL))
    · exact Or.inl (Or.inl (Or.inr hpR))

/-- A nondegenerate closed rectangular window is the closure of its interior,
which is the regular-closed hypothesis needed by `openSpliceIn`. -/
theorem closure_interior_closedCutRectangle
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u) :
    closure (interior (closedCutRectangle l r d u)) =
      closedCutRectangle l r d u := by
  rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc,
    closure_prod_eq, closure_Ioo hlr.ne, closure_Ioo hdu.ne]

/-- Every nondegenerate rectangular cutting frontier is planar-null. -/
theorem volume_frontier_closedCutRectangle
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u) :
    volume (frontier (closedCutRectangle l r d u)) = 0 := by
  apply measure_mono_null
    (frontier_closedCutRectangle_subset_lines hlr hdu)
  exact measure_union_null
    (measure_union_null
      (measure_union_null (volume_verticalLine l) (volume_verticalLine r))
      (volume_horizontalLine d))
    (volume_horizontalLine u)

lemma measurableSet_closedCutRectangle (l r d u : ℝ) :
    MeasurableSet (closedCutRectangle l r d u) :=
  (measurableSet_Icc.prod measurableSet_Icc)

/-- Four independent positive-width collars contain a rectangular cut whose
complete raw trace is bounded solely by averaged localized mismatch. Positive
old/new frontier fibers are avoided using countability, not a collar
agreement or a hidden transversality assumption. -/
theorem exists_closedCutRectangle_spliceCutTrace_le_averages
    {lam : ℝ} (hlam : 1 < lam) (U G : Set PlanePoint)
    (hU : MeasurableSet U) (hG : MeasurableSet G)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU :
      FrontierMeasure U (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG :
      FrontierMeasure G (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤) :
    ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
      ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
        weightedTraceCost lam
            (spliceCutTrace U G (closedCutRectangle l r d u)) ≤
          ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ b₁ c₀ d₁ ∩ (U ∆ G)) /
                ENNReal.ofReal (a₁ - a₀)) +
            ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ b₁ c₀ d₁ ∩ (U ∆ G)) /
                ENNReal.ofReal (b₁ - b₀)) +
              ENNReal.ofReal lam *
                (volume (closedCutRectangle a₀ b₁ c₀ d₁ ∩ (U ∆ G)) /
                  ENNReal.ofReal (c₁ - c₀)) +
                ENNReal.ofReal lam *
                  (volume (closedCutRectangle a₀ b₁ c₀ d₁ ∩ (U ∆ G)) /
                    ENNReal.ofReal (d₁ - d₀)) := by
  let K := closedCutRectangle a₀ b₁ c₀ d₁
  have hK : MeasurableSet K :=
    measurableSet_closedCutRectangle a₀ b₁ c₀ d₁
  obtain ⟨l, hl, hlcost⟩ :=
    exists_verticalCutInputsOn_le_average
      hlam U G K hU hG hK hfiniteU hfiniteG ha
  obtain ⟨r, hr, hrcost⟩ :=
    exists_verticalCutInputsOn_le_average
      hlam U G K hU hG hK hfiniteU hfiniteG hb
  obtain ⟨d, hdmem, hdcost⟩ :=
    exists_horizontalCutInputsOn_le_average
      hlam U G K hU hG hK hfiniteU hfiniteG hc
  obtain ⟨u, humem, hucost⟩ :=
    exists_horizontalCutInputsOn_le_average
      hlam U G K hU hG hK hfiniteU hfiniteG hd
  refine ⟨l, hl, r, hr, d, hdmem, u, humem, ?_⟩
  have hlr : l < r := hl.2.trans (hab.trans hr.1)
  have hdu : d < u := hdmem.2.trans (hcd.trans humem.1)
  have hwindowSubset : closedCutRectangle l r d u ⊆ K := by
    intro p hp
    rcases hp with ⟨hpx, hpy⟩
    exact ⟨⟨hl.1.le.trans hpx.1, hpx.2.trans hr.2.le⟩,
      ⟨hdmem.1.le.trans hpy.1, hpy.2.trans humem.2.le⟩⟩
  let T := frontier U ∪ frontier G ∪ (U ∆ G)
  have hsubset :
      spliceCutTrace U G (closedCutRectangle l r d u) ⊆
        (((verticalLine l ∩ K) ∩ T) ∪
          ((verticalLine r ∩ K) ∩ T)) ∪
            ((horizontalLine d ∩ K) ∩ T) ∪
              ((horizontalLine u ∩ K) ∩ T) := by
    intro p hp
    rcases hp with ⟨hpBoundary, hpT⟩
    have hpWindow : p ∈ closedCutRectangle l r d u :=
      ((isClosed_Icc.prod isClosed_Icc).frontier_subset hpBoundary)
    have hpK : p ∈ K := hwindowSubset hpWindow
    have hlines :=
      frontier_closedCutRectangle_subset_lines hlr hdu hpBoundary
    rcases hlines with ((hpL | hpR) | hpD) | hpU
    · exact Or.inl (Or.inl (Or.inl ⟨⟨hpL, hpK⟩, hpT⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨hpR, hpK⟩, hpT⟩))
    · exact Or.inl (Or.inr ⟨⟨hpD, hpK⟩, hpT⟩)
    · exact Or.inr ⟨⟨hpU, hpK⟩, hpT⟩
  calc
    weightedTraceCost lam
        (spliceCutTrace U G (closedCutRectangle l r d u)) ≤
      weightedTraceCost lam ((verticalLine l ∩ K) ∩ T) +
        weightedTraceCost lam ((verticalLine r ∩ K) ∩ T) +
          weightedTraceCost lam ((horizontalLine d ∩ K) ∩ T) +
            weightedTraceCost lam ((horizontalLine u ∩ K) ∩ T) :=
      (weightedTraceCost_mono lam hsubset).trans
        (weightedTraceCost_iUnion_four_le lam _ _ _ _)
    _ ≤ ENNReal.ofReal lam *
            (volume (K ∩ (U ∆ G)) / ENNReal.ofReal (a₁ - a₀)) +
          ENNReal.ofReal lam *
            (volume (K ∩ (U ∆ G)) / ENNReal.ofReal (b₁ - b₀)) +
            ENNReal.ofReal lam *
              (volume (K ∩ (U ∆ G)) / ENNReal.ofReal (c₁ - c₀)) +
              ENNReal.ofReal lam *
                (volume (K ∩ (U ∆ G)) / ENNReal.ofReal (d₁ - d₀)) :=
      add_le_add (add_le_add (add_le_add hlcost hrcost) hdcost) hucost
    _ = _ := rfl
/-- Quantitative complete-frontier bound for the literal raw splice. -/
theorem smoothCost_spliceIn_le_piecewise (lam : ℝ) (U G W : Set PlanePoint) :
    smoothCost lam (spliceIn U G W) ≤
      weightedTraceCost lam (frontier U ∩ interior Wᶜ) +
        weightedTraceCost lam (frontier G ∩ interior W) +
          weightedTraceCost lam (spliceCutTrace U G W) := by
  rw [smoothCost_eq_weightedTraceCost_frontier]
  exact (weightedTraceCost_mono lam
    (frontier_spliceIn_subset_piecewise U G W)).trans
      (weightedTraceCost_iUnion_three_le lam _ _ _)

/-- The raw splice pays the unchanged and inserted local costs plus exactly
the complete cutting trace; no cutting frontier is omitted. -/
theorem smoothCost_spliceIn_le_outside_add_inside_add_cutTrace
    (lam : ℝ) (U G W : Set PlanePoint) :
    smoothCost lam (spliceIn U G W) ≤
      smoothCostOn lam U (interior Wᶜ) +
        smoothCostOn lam G (interior W) +
          weightedTraceCost lam (spliceCutTrace U G W) := by
  rw [smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam U isOpen_interior.measurableSet,
    smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam G isOpen_interior.measurableSet]
  exact smoothCost_spliceIn_le_piecewise lam U G W

/-- The canonical open representative inherits the complete raw-splice cost
bound with no loss. -/
theorem smoothCost_openSpliceIn_le_outside_add_inside_add_cutTrace
    (lam : ℝ) {U G W : Set PlanePoint}
    (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W) :
    smoothCost lam (openSpliceIn U G W) ≤
      smoothCostOn lam U (interior Wᶜ) +
        smoothCostOn lam G (interior W) +
          weightedTraceCost lam (spliceCutTrace U G W) := by
  rw [smoothCost_openSpliceIn_eq_smoothCost_spliceIn
    lam hU hG hW hregular]
  exact smoothCost_spliceIn_le_outside_add_inside_add_cutTrace lam U G W
lemma smoothCostOn_mono (lam : ℝ) (U : Set PlanePoint)
    {W Z : Set PlanePoint} (hWZ : W ⊆ Z) :
    smoothCostOn lam U W ≤ smoothCostOn lam U Z := by
  unfold smoothCostOn
  exact MeasureTheory.lintegral_mono_set hWZ

/-- Four independently localized collars select a rectangular cut whose full
cut trace is controlled only by mismatch in the corresponding face collar. -/
theorem exists_closedCutRectangle_spliceCutTrace_le_collar_averages
    {lam : ℝ} (hlam : 1 < lam) (U G : Set PlanePoint)
    (hU : MeasurableSet U) (hG : MeasurableSet G)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU :
      FrontierMeasure U (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG :
      FrontierMeasure G (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤) :
    ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
      ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
        weightedTraceCost lam
            (spliceCutTrace U G (closedCutRectangle l r d u)) ≤
          ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U ∆ G)) /
                ENNReal.ofReal (a₁ - a₀)) +
            ENNReal.ofReal lam *
              (volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U ∆ G)) /
                ENNReal.ofReal (b₁ - b₀)) +
              ENNReal.ofReal lam *
                (volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U ∆ G)) /
                  ENNReal.ofReal (c₁ - c₀)) +
                ENNReal.ofReal lam *
                  (volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U ∆ G)) /
                    ENNReal.ofReal (d₁ - d₀)) := by
  let K := closedCutRectangle a₀ b₁ c₀ d₁
  let KL := closedCutRectangle a₀ a₁ c₀ d₁
  let KR := closedCutRectangle b₀ b₁ c₀ d₁
  let KD := closedCutRectangle a₀ b₁ c₀ c₁
  let KU := closedCutRectangle a₀ b₁ d₀ d₁
  have hKL : MeasurableSet KL := measurableSet_closedCutRectangle _ _ _ _
  have hKR : MeasurableSet KR := measurableSet_closedCutRectangle _ _ _ _
  have hKD : MeasurableSet KD := measurableSet_closedCutRectangle _ _ _ _
  have hKU : MeasurableSet KU := measurableSet_closedCutRectangle _ _ _ _
  have hKLK : KL ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨⟨hx.1, (hx.2.trans hab.le).trans hb.le⟩, hy⟩
  have hKRK : KR ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨⟨ha.le.trans (hab.le.trans hx.1), hx.2⟩, hy⟩
  have hKDK : KD ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨hx, ⟨hy.1, (hy.2.trans hcd.le).trans hd.le⟩⟩
  have hKUK : KU ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨hx, ⟨hc.le.trans (hcd.le.trans hy.1), hy.2⟩⟩
  have hfinite (M : Set PlanePoint) (hMK : M ⊆ K) :
      FrontierMeasure U M ≠ ⊤ ∧ FrontierMeasure G M ≠ ⊤ := by
    constructor
    · exact ne_top_of_le_ne_top hfiniteU (measure_mono hMK)
    · exact ne_top_of_le_ne_top hfiniteG (measure_mono hMK)
  obtain ⟨l, hl, hlcost⟩ :=
    exists_verticalCutInputsOn_le_average hlam U G KL hU hG hKL
      (hfinite KL hKLK).1 (hfinite KL hKLK).2 ha
  obtain ⟨r, hr, hrcost⟩ :=
    exists_verticalCutInputsOn_le_average hlam U G KR hU hG hKR
      (hfinite KR hKRK).1 (hfinite KR hKRK).2 hb
  obtain ⟨d, hdmem, hdcost⟩ :=
    exists_horizontalCutInputsOn_le_average hlam U G KD hU hG hKD
      (hfinite KD hKDK).1 (hfinite KD hKDK).2 hc
  obtain ⟨u, humem, hucost⟩ :=
    exists_horizontalCutInputsOn_le_average hlam U G KU hU hG hKU
      (hfinite KU hKUK).1 (hfinite KU hKUK).2 hd
  refine ⟨l, hl, r, hr, d, hdmem, u, humem, ?_⟩
  have hlr : l < r := hl.2.trans (hab.trans hr.1)
  have hdu : d < u := hdmem.2.trans (hcd.trans humem.1)
  let T := frontier U ∪ frontier G ∪ (U ∆ G)
  have hsubset :
      spliceCutTrace U G (closedCutRectangle l r d u) ⊆
        (((verticalLine l ∩ KL) ∩ T) ∪
          ((verticalLine r ∩ KR) ∩ T)) ∪
            ((horizontalLine d ∩ KD) ∩ T) ∪
              ((horizontalLine u ∩ KU) ∩ T) := by
    intro p hp
    rcases hp with ⟨hpBoundary, hpT⟩
    have hpWindow : p ∈ closedCutRectangle l r d u :=
      ((isClosed_Icc.prod isClosed_Icc).frontier_subset hpBoundary)
    have hlines := frontier_closedCutRectangle_subset_lines hlr hdu hpBoundary
    rcases hlines with ((hpL | hpR) | hpD) | hpU
    · have hpKL : p ∈ KL := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.1 = l at hpL
        exact ⟨⟨by linarith [hl.1], by linarith [hl.2]⟩,
          ⟨by linarith [hdmem.1], by linarith [humem.2]⟩⟩
      exact Or.inl (Or.inl (Or.inl ⟨⟨hpL, hpKL⟩, hpT⟩))
    · have hpKR : p ∈ KR := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.1 = r at hpR
        exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩,
          ⟨by linarith [hdmem.1], by linarith [humem.2]⟩⟩
      exact Or.inl (Or.inl (Or.inr ⟨⟨hpR, hpKR⟩, hpT⟩))
    · have hpKD : p ∈ KD := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.2 = d at hpD
        exact ⟨⟨by linarith [hl.1], by linarith [hr.2]⟩,
          ⟨by linarith [hdmem.1], by linarith [hdmem.2]⟩⟩
      exact Or.inl (Or.inr ⟨⟨hpD, hpKD⟩, hpT⟩)
    · have hpKU : p ∈ KU := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.2 = u at hpU
        exact ⟨⟨by linarith [hl.1], by linarith [hr.2]⟩,
          ⟨by linarith [humem.1], by linarith [humem.2]⟩⟩
      exact Or.inr ⟨⟨hpU, hpKU⟩, hpT⟩
  calc
    weightedTraceCost lam
        (spliceCutTrace U G (closedCutRectangle l r d u)) ≤
      weightedTraceCost lam ((verticalLine l ∩ KL) ∩ T) +
        weightedTraceCost lam ((verticalLine r ∩ KR) ∩ T) +
          weightedTraceCost lam ((horizontalLine d ∩ KD) ∩ T) +
            weightedTraceCost lam ((horizontalLine u ∩ KU) ∩ T) :=
      (weightedTraceCost_mono lam hsubset).trans
        (weightedTraceCost_iUnion_four_le lam _ _ _ _)
    _ ≤ _ := add_le_add (add_le_add (add_le_add hlcost hrcost) hdcost) hucost


/-- Global characteristic-function convergence localizes to every fixed set. -/
theorem tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
    {U : ℕ → Set PlanePoint} {E K : Set PlanePoint}
    (hU : Tendsto (fun n => characteristicDistance (U n) E)
      atTop (𝓝 0)) :
    Tendsto (fun n => volume (K ∩ (U n ∆ E))) atTop (𝓝 0) := by
  have hle : ∀ n, volume (K ∩ (U n ∆ E)) ≤
      characteristicDistance (U n) E := by
    intro n
    exact measure_mono inter_subset_right
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hU (fun _ => bot_le) hle

/-- If two target sets agree on a fixed collar, independent local convergence
to those targets forces the approximants' mutual mismatch to vanish there. -/
theorem tendsto_volume_inter_symmDiff_zero_of_local_agreement
    {U G : ℕ → Set PlanePoint} {E F K : Set PlanePoint}
    (hU : Tendsto (fun n => volume (K ∩ (U n ∆ E)))
      atTop (𝓝 0))
    (hG : Tendsto (fun n => volume (K ∩ (G n ∆ F)))
      atTop (𝓝 0))
    (hEF : E ∩ K = F ∩ K) :
    Tendsto (fun n => volume (K ∩ (U n ∆ G n)))
      atTop (𝓝 0) := by
  have hsubset : ∀ n, K ∩ (U n ∆ G n) ⊆
      (K ∩ (U n ∆ E)) ∪ (K ∩ (G n ∆ F)) := by
    intro n p hp
    have hpEF : p ∈ E ↔ p ∈ F := by
      constructor
      · intro hpE
        have hpEK : p ∈ E ∩ K := ⟨hpE, hp.1⟩
        rw [hEF] at hpEK
        exact hpEK.1
      · intro hpF
        have hpFK : p ∈ F ∩ K := ⟨hpF, hp.1⟩
        rw [← hEF] at hpFK
        exact hpFK.1
    simp only [mem_union, mem_inter_iff, mem_symmDiff] at hp ⊢
    tauto
  have hle : ∀ n, volume (K ∩ (U n ∆ G n)) ≤
      volume (K ∩ (U n ∆ E)) + volume (K ∩ (G n ∆ F)) := by
    intro n
    exact (measure_mono (hsubset n)).trans (measure_union_le _ _)
  have hsum : Tendsto
      (fun n => volume (K ∩ (U n ∆ E)) +
        volume (K ∩ (G n ∆ F))) atTop (𝓝 0) := by
    simpa using hU.add hG
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => bot_le) hle


/-- The four collar averages select a sequence of complete rectangular splice
traces with vanishing weighted cost. No regular-cut assumption is supplied. -/
theorem exists_closedCutRectangle_spliceCutTrace_tendsto_zero
    {lam : ℝ} (hlam : 1 < lam) (U G : ℕ → Set PlanePoint)
    (hU : ∀ n, MeasurableSet (U n)) (hG : ∀ n, MeasurableSet (G n))
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU : ∀ n,
      FrontierMeasure (U n) (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : ∀ n,
      FrontierMeasure (G n) (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hleft : Tendsto (fun n =>
      volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0))
    (hright : Tendsto (fun n =>
      volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0))
    (hlower : Tendsto (fun n =>
      volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0))
    (hupper : Tendsto (fun n =>
      volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U n ∆ G n)))
      atTop (𝓝 0)) :
    ∃ l r d u : ℕ → ℝ,
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (spliceCutTrace (U n) (G n)
            (closedCutRectangle (l n) (r n) (d n) (u n))))
        atTop (𝓝 0) := by
  have hselect : ∀ n, ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
      ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
        weightedTraceCost lam
            (spliceCutTrace (U n) (G n) (closedCutRectangle l r d u)) ≤
          ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U n ∆ G n)) /
                ENNReal.ofReal (a₁ - a₀)) +
            ENNReal.ofReal lam *
              (volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U n ∆ G n)) /
                ENNReal.ofReal (b₁ - b₀)) +
              ENNReal.ofReal lam *
                (volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U n ∆ G n)) /
                  ENNReal.ofReal (c₁ - c₀)) +
                ENNReal.ofReal lam *
                  (volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U n ∆ G n)) /
                    ENNReal.ofReal (d₁ - d₀)) := by
    intro n
    exact exists_closedCutRectangle_spliceCutTrace_le_collar_averages
      hlam (U n) (G n) (hU n) (hG n) ha hab hb hc hcd hd
        (hfiniteU n) (hfiniteG n)
  choose l hl r hr d hdmem u humem hcost using hselect
  refine ⟨l, r, d, u, hl, hr, hdmem, humem, ?_⟩
  have tendsto_div : ∀ {f : ℕ → ENNReal} {w : ℝ},
      0 < w → Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => f n / ENNReal.ofReal w) atTop (𝓝 0) := by
    intro f w hw hf
    rw [show (fun n => f n / ENNReal.ofReal w) =
      fun n => (ENNReal.ofReal w)⁻¹ * f n by
        funext n
        rw [ENNReal.div_eq_inv_mul]]
    simpa using ENNReal.Tendsto.const_mul hf
      (Or.inr (ENNReal.inv_ne_top.2
        (ne_of_gt (ENNReal.ofReal_pos.2 hw))))
  have tendsto_scaled : ∀ {f : ℕ → ENNReal} {w : ℝ},
      0 < w → Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => ENNReal.ofReal lam *
        (f n / ENNReal.ofReal w)) atTop (𝓝 0) := by
    intro f w hw hf
    simpa using ENNReal.Tendsto.const_mul (tendsto_div hw hf)
      (Or.inr ENNReal.ofReal_ne_top)
  have hleft' := tendsto_scaled (sub_pos.mpr ha) hleft
  have hright' := tendsto_scaled (sub_pos.mpr hb) hright
  have hlower' := tendsto_scaled (sub_pos.mpr hc) hlower
  have hupper' := tendsto_scaled (sub_pos.mpr hd) hupper
  have hbudget : Tendsto (fun n =>
      ENNReal.ofReal lam *
          (volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U n ∆ G n)) /
            ENNReal.ofReal (a₁ - a₀)) +
        ENNReal.ofReal lam *
          (volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U n ∆ G n)) /
            ENNReal.ofReal (b₁ - b₀)) +
          ENNReal.ofReal lam *
            (volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U n ∆ G n)) /
              ENNReal.ofReal (c₁ - c₀)) +
            ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U n ∆ G n)) /
                ENNReal.ofReal (d₁ - d₀))) atTop (𝓝 0) := by
    simpa using ((hleft'.add hright').add hlower').add hupper'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbudget (fun _ => bot_le) hcost


/-- A replacement supported strictly inside the four collar bands gives the
vanishing complete rectangular seam directly from global convergence of the
old and replacement approximants. -/
theorem exists_closedCutRectangle_spliceCutTrace_tendsto_zero_of_core_support
    {lam : ℝ} (hlam : 1 < lam) (U G : ℕ → Set PlanePoint)
    {E F : Set PlanePoint}
    (hU : ∀ n, MeasurableSet (U n)) (hG : ∀ n, MeasurableSet (G n))
    (hUconv : Tendsto (fun n => characteristicDistance (U n) E)
      atTop (𝓝 0))
    (hGconv : Tendsto (fun n => characteristicDistance (G n) F)
      atTop (𝓝 0))
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hEF : E ∆ F ⊆ Ioo a₁ b₀ ×ˢ Ioo c₁ d₀)
    (hfiniteU : ∀ n,
      FrontierMeasure (U n) (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : ∀ n,
      FrontierMeasure (G n) (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤) :
    ∃ l r d u : ℕ → ℝ,
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (spliceCutTrace (U n) (G n)
            (closedCutRectangle (l n) (r n) (d n) (u n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        characteristicDistance
          (spliceIn (U n) (G n)
            (closedCutRectangle (l n) (r n) (d n) (u n))) F)
        atTop (𝓝 0) ∧
      ∀ n, smoothCost lam
          (spliceIn (U n) (G n)
            (closedCutRectangle (l n) (r n) (d n) (u n))) ≤
        smoothCostOn lam (U n)
            (Ioo a₁ b₀ ×ˢ Ioo c₁ d₀)ᶜ +
          smoothCostOn lam (G n)
            (closedCutRectangle a₀ b₁ c₀ d₁) +
          weightedTraceCost lam
            (spliceCutTrace (U n) (G n)
              (closedCutRectangle (l n) (r n) (d n) (u n))) := by
  let KL := closedCutRectangle a₀ a₁ c₀ d₁
  let KR := closedCutRectangle b₀ b₁ c₀ d₁
  let KD := closedCutRectangle a₀ b₁ c₀ c₁
  let KU := closedCutRectangle a₀ b₁ d₀ d₁
  let C : Set PlanePoint := Ioo a₁ b₀ ×ˢ Ioo c₁ d₀
  have hagree : ∀ K : Set PlanePoint, Disjoint K C → E ∩ K = F ∩ K := by
    intro K hKC
    ext p
    constructor
    · rintro ⟨hpE, hpK⟩
      refine ⟨?_, hpK⟩
      by_contra hpF
      exact (Set.disjoint_left.1 hKC hpK)
        (hEF (Or.inl ⟨hpE, hpF⟩))
    · rintro ⟨hpF, hpK⟩
      refine ⟨?_, hpK⟩
      by_contra hpE
      exact (Set.disjoint_left.1 hKC hpK)
        (hEF (Or.inr ⟨hpF, hpE⟩))
  have hKLC : Disjoint KL C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpx.2) hpxC.1)
  have hKRC : Disjoint KR C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpx.1) hpxC.2)
  have hKDC : Disjoint KD C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpy.2) hpyC.1)
  have hKUC : Disjoint KU C := Set.disjoint_left.2 (by
    rintro p ⟨hpx, hpy⟩ ⟨hpxC, hpyC⟩
    exact (not_lt_of_ge hpy.1) hpyC.2)
  have hleft := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KL) hUconv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KL) hGconv)
    (hagree KL hKLC)
  have hright := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KR) hUconv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KR) hGconv)
    (hagree KR hKRC)
  have hlower := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KD) hUconv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KD) hGconv)
    (hagree KD hKDC)
  have hupper := tendsto_volume_inter_symmDiff_zero_of_local_agreement
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KU) hUconv)
    (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance
      (K := KU) hGconv)
    (hagree KU hKUC)
  obtain ⟨l, r, d, u, hl, hr, hdmem, humem, hseam⟩ :=
    exists_closedCutRectangle_spliceCutTrace_tendsto_zero
      hlam U G hU hG ha hab hb hc hcd hd hfiniteU hfiniteG
        hleft hright hlower hupper
  have hCW : ∀ n, Ioo a₁ b₀ ×ˢ Ioo c₁ d₀ ⊆
      closedCutRectangle (l n) (r n) (d n) (u n) := by
    intro n p hp
    rcases hp with ⟨hpx, hpy⟩
    rcases hpx with ⟨hpxl, hpxr⟩
    rcases hpy with ⟨hpyd, hpyu⟩
    exact ⟨⟨by linarith [(hl n).2], by linarith [(hr n).1]⟩,
      ⟨by linarith [(hdmem n).2], by linarith [(humem n).1]⟩⟩
  have hWK : ∀ n, closedCutRectangle (l n) (r n) (d n) (u n) ⊆
      closedCutRectangle a₀ b₁ c₀ d₁ := by
    intro n p hp
    rcases hp with ⟨hpx, hpy⟩
    rcases hpx with ⟨hpxl, hpxr⟩
    rcases hpy with ⟨hpyd, hpyu⟩
    exact ⟨⟨by linarith [(hl n).1], by linarith [(hr n).2]⟩,
      ⟨by linarith [(hdmem n).1], by linarith [(humem n).2]⟩⟩
  have hEFW : ∀ n, E ∆ F ⊆
      closedCutRectangle (l n) (r n) (d n) (u n) :=
    fun n => hEF.trans (hCW n)
  have hdist_le : ∀ n,
      characteristicDistance
          (spliceIn (U n) (G n)
            (closedCutRectangle (l n) (r n) (d n) (u n))) F ≤
        characteristicDistance (U n) E +
          characteristicDistance (G n) F := by
    intro n
    refine (characteristicDistance_spliceIn_le (hEFW n)).trans ?_
    apply add_le_add le_rfl
    unfold characteristicDistance
    exact measure_mono inter_subset_left
  have hdist_sum : Tendsto (fun n =>
      characteristicDistance (U n) E +
        characteristicDistance (G n) F) atTop (𝓝 0) := by
    simpa using hUconv.add hGconv
  have hdist := tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hdist_sum (fun _ => bot_le) hdist_le
  refine ⟨l, r, d, u, hl, hr, hdmem, humem, hseam, hdist, ?_⟩
  intro n
  have hout :
      interior (closedCutRectangle (l n) (r n) (d n) (u n))ᶜ ⊆
        (Ioo a₁ b₀ ×ˢ Ioo c₁ d₀)ᶜ := by
    intro p hpW hpC
    exact (interior_subset hpW) (hCW n hpC)
  have hin :
      interior (closedCutRectangle (l n) (r n) (d n) (u n)) ⊆
        closedCutRectangle a₀ b₁ c₀ d₁ :=
    fun _ hp => hWK n (interior_subset hp)
  exact
    (smoothCost_spliceIn_le_outside_add_inside_add_cutTrace
      lam (U n) (G n)
        (closedCutRectangle (l n) (r n) (d n) (u n))).trans
      (add_le_add
        (add_le_add
          (smoothCostOn_mono lam (U n) hout)
          (smoothCostOn_mono lam (G n) hin))
        le_rfl)

/-- A continuous repaired defining function only has to pay for its zero set
inside the closed repair window; exact exterior agreement restores the old
domain's exterior smooth cost. -/
lemma smoothCost_sublevel_le_outside_add_zeroSet
    (lam : ℝ) {g : PlanePoint → ℝ} (hg : Continuous g)
    {U Q : Set PlanePoint} (hQ : IsClosed Q)
    (heq : {p | g p < 0} ∩ Qᶜ = U ∩ Qᶜ) :
    smoothCost lam {p | g p < 0} ≤
      smoothCostOn lam U Qᶜ +
        weightedTraceCost lam ({p | g p = 0} ∩ Q) := by
  rw [← smoothCostOn_add_compl lam {p | g p < 0} hQ.measurableSet]
  have hout :
      smoothCostOn lam {p | g p < 0} Qᶜ =
        smoothCostOn lam U Qᶜ :=
    smoothCostOn_eq_of_inter_open_eq lam hQ.isOpen_compl heq
  have hin :
      smoothCostOn lam {p | g p < 0} Q ≤
        weightedTraceCost lam ({p | g p = 0} ∩ Q) := by
    rw [smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam _ hQ.measurableSet]
    apply weightedTraceCost_mono
    intro p hp
    exact ⟨frontier_lt_subset_eq hg continuous_const hp.1, hp.2⟩
  rw [hout]
  exact (add_le_add hin le_rfl).trans_eq (add_comm _ _)

/-- Parameter that would make `f` and a bounded arctangent perturbation have a
critical zero at `p`. The target has dimension three while `p` has dimension
two. -/
def boundedBadJet (f : PlanePoint → ℝ) (p : PlanePoint) :
    PlanePoint × ℝ :=
  let df := fderiv ℝ f p
  let a := (1 + p.1 ^ 2) * df (1, 0)
  let b := (1 + p.2 ^ 2) * df (0, 1)
  ((a, b), f p - a * Real.arctan p.1 - b * Real.arctan p.2)

/-- Subtract a bounded three-parameter smooth function. -/
def boundedPerturb (f : PlanePoint → ℝ) (c : PlanePoint × ℝ)
    (p : PlanePoint) : ℝ :=
  f p - c.1.1 * Real.arctan p.1 -
    c.1.2 * Real.arctan p.2 - c.2

lemma contDiff_boundedBadJet {f : PlanePoint → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (boundedBadJet f) := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2
  let a : PlanePoint → ℝ :=
    fun p => (1 + p.1 ^ 2) * fderiv ℝ f p (1, 0)
  let b : PlanePoint → ℝ :=
    fun p => (1 + p.2 ^ 2) * fderiv ℝ f p (0, 1)
  have ha : ContDiff ℝ ∞ a := by
    dsimp [a]
    fun_prop
  have hb : ContDiff ℝ ∞ b := by
    dsimp [b]
    fun_prop
  have hax :
      ContDiff ℝ ∞ (fun p : PlanePoint => Real.arctan p.1) :=
    Real.contDiff_arctan.comp contDiff_fst
  have hay :
      ContDiff ℝ ∞ (fun p : PlanePoint => Real.arctan p.2) :=
    Real.contDiff_arctan.comp contDiff_snd
  change ContDiff ℝ ∞ (fun p => ((a p, b p),
    f p - a p * Real.arctan p.1 - b p * Real.arctan p.2))
  exact (ha.prodMk hb).prodMk
    ((hf.sub (ha.mul hax)).sub (hb.mul hay))

/-- Regular bounded-perturbation parameters are dense by dimension lowering
`2 < 3`. -/
theorem dense_regularBoundedParameters {f : PlanePoint → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    Dense (Set.range (boundedBadJet f))ᶜ := by
  apply (contDiff_boundedBadJet hf).of_le (by simp)
    |>.dense_compl_range_of_finrank_lt_finrank
  norm_num [PlanePoint]

lemma boundedPerturb_regular {f : PlanePoint → ℝ}
    (hf : ContDiff ℝ ∞ f) {c : PlanePoint × ℝ}
    (hc : c ∉ Set.range (boundedBadJet f)) :
    ∀ p, boundedPerturb f c p = 0 →
      fderiv ℝ (boundedPerturb f c) p ≠ 0 := by
  intro p hp hzero
  let D : PlanePoint →L[ℝ] ℝ :=
    fderiv ℝ f p -
      c.1.1 • (1 + p.1 ^ 2)⁻¹ •
        ContinuousLinearMap.fst ℝ ℝ ℝ -
      c.1.2 • (1 + p.2 ^ 2)⁻¹ •
        ContinuousLinearMap.snd ℝ ℝ ℝ
  have hder : HasFDerivAt (boundedPerturb f c) D p := by
    unfold boundedPerturb
    simpa [D] using
      (((hf.differentiable (by simp) p).hasFDerivAt.sub
        (((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).arctan).const_mul
          c.1.1)).sub
        (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).arctan).const_mul
          c.1.2)).sub_const c.2
  have hD : D = 0 := hder.fderiv.symm.trans hzero
  have hx := congrArg
    (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hD
  have hy := congrArg
    (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hD
  have hx' :
      fderiv ℝ f p (1, 0) - c.1.1 / (1 + p.1 ^ 2) = 0 := by
    simpa [D, div_eq_mul_inv] using hx
  have hy' :
      fderiv ℝ f p (0, 1) - c.1.2 / (1 + p.2 ^ 2) = 0 := by
    simpa [D, div_eq_mul_inv] using hy
  have hdenx : 1 + p.1 ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg p.1]
  have hdeny : 1 + p.2 ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg p.2]
  have hxeq :
      (1 + p.1 ^ 2) * fderiv ℝ f p (1, 0) = c.1.1 := by
    field_simp [hdenx] at hx'
    linarith
  have hyeq :
      (1 + p.2 ^ 2) * fderiv ℝ f p (0, 1) = c.1.2 := by
    field_simp [hdeny] at hy'
    linarith
  apply hc
  refine ⟨p, ?_⟩
  apply Prod.ext
  · exact Prod.ext hxeq hyeq
  · dsimp only [boundedBadJet]
    rw [hxeq, hyeq]
    unfold boundedPerturb at hp
    linarith

/-- The bounded perturbation is uniformly controlled by its parameter norm. -/
lemma abs_boundedPerturb_sub_le (f : PlanePoint → ℝ)
    (c : PlanePoint × ℝ) (p : PlanePoint) :
    |boundedPerturb f c p - f p| ≤ (Real.pi + 1) * ‖c‖ := by
  have hatanx : |Real.arctan p.1| ≤ Real.pi / 2 :=
    le_of_lt (abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan p.1,
      Real.arctan_lt_pi_div_two p.1⟩)
  have hatany : |Real.arctan p.2| ≤ Real.pi / 2 :=
    le_of_lt (abs_lt.2 ⟨Real.neg_pi_div_two_lt_arctan p.2,
      Real.arctan_lt_pi_div_two p.2⟩)
  have hc11 : |c.1.1| ≤ ‖c‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_fst_le c.1).trans (norm_fst_le c)
  have hc12 : |c.1.2| ≤ ‖c‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_snd_le c.1).trans (norm_fst_le c)
  have hc2 : |c.2| ≤ ‖c‖ := by
    simpa [Real.norm_eq_abs] using norm_snd_le c
  rw [show boundedPerturb f c p - f p =
      -c.1.1 * Real.arctan p.1 -
        c.1.2 * Real.arctan p.2 - c.2 by
    unfold boundedPerturb
    ring]
  calc
    |-c.1.1 * Real.arctan p.1 -
        c.1.2 * Real.arctan p.2 - c.2| ≤
        (|c.1.1| * |Real.arctan p.1| +
          |c.1.2| * |Real.arctan p.2|) + |c.2| := by
      refine (abs_sub _ _).trans ?_
      apply add_le_add
      · calc
          |-c.1.1 * Real.arctan p.1 -
              c.1.2 * Real.arctan p.2| ≤
              |-c.1.1 * Real.arctan p.1| +
                |c.1.2 * Real.arctan p.2| := abs_sub _ _
          _ = |c.1.1| * |Real.arctan p.1| +
              |c.1.2| * |Real.arctan p.2| := by
            simp only [abs_mul, abs_neg]
      · exact le_rfl
    _ ≤ ‖c‖ * (Real.pi / 2) +
        ‖c‖ * (Real.pi / 2) + ‖c‖ := by
      exact add_le_add
        (add_le_add
          (mul_le_mul hc11 hatanx (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul hc12 hatany (abs_nonneg _) (norm_nonneg _)))
        hc2
    _ = (Real.pi + 1) * ‖c‖ := by
      ring


/-- A globally smooth function with no critical zero defines a literal smooth
domain in the relaxation's local one-sided sense. -/
theorem isSmoothDomain_sublevel_of_regular {g : PlanePoint → ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hreg : ∀ p, g p = 0 → fderiv ℝ g p ≠ 0) :
    IsSmoothDomain {p | g p < 0} := by
  constructor
  · exact isOpen_lt hg.continuous continuous_const
  · intro p hp
    have hp0 : g p = 0 :=
      frontier_lt_subset_eq hg.continuous continuous_const hp
    refine ⟨Set.univ, g, fderiv ℝ g p, isOpen_univ,
      Set.mem_univ p, hg.contDiffOn, hp0,
      (hg.differentiable (by simp) p).hasFDerivAt,
      hreg p hp0, ?_⟩
    ext q
    simp

/-- Every smooth scalar function admits a uniformly small bounded
regularization whose strict sublevel is a genuine smooth domain. -/
theorem exists_smoothDomain_boundedPerturb
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : PlanePoint × ℝ,
      (∀ p, |boundedPerturb f c p - f p| < ε) ∧
      IsSmoothDomain {p | boundedPerturb f c p < 0} := by
  have hpi : 0 < Real.pi + 1 := by
    positivity
  obtain ⟨c, hc, hdist⟩ :=
    (dense_regularBoundedParameters hf).exists_dist_lt
      0 (div_pos hε hpi)
  have hnorm : ‖c‖ < ε / (Real.pi + 1) := by
    simpa only [dist_zero_left] using hdist
  refine ⟨c, ?_, isSmoothDomain_sublevel_of_regular ?_
    (boundedPerturb_regular hf hc)⟩
  · intro p
    calc
      |boundedPerturb f c p - f p| ≤
          (Real.pi + 1) * ‖c‖ :=
        abs_boundedPerturb_sub_le f c p
      _ < (Real.pi + 1) * (ε / (Real.pi + 1)) :=
        mul_lt_mul_of_pos_left hnorm hpi
      _ = ε := by
        field_simp [ne_of_gt hpi]
  · have hax :
        ContDiff ℝ ∞ (fun p : PlanePoint => Real.arctan p.1) :=
      Real.contDiff_arctan.comp contDiff_fst
    have hay :
        ContDiff ℝ ∞ (fun p : PlanePoint => Real.arctan p.2) :=
      Real.contDiff_arctan.comp contDiff_snd
    unfold boundedPerturb
    exact ((hf.sub (contDiff_const.mul hax)).sub
      (contDiff_const.mul hay)).sub contDiff_const

/-- The critical values of a differentiable real function have zero volume
whenever a derivative is supplied and vanishes on the selected source set. -/
theorem volume_image_critical_eq_zero
    {s : Set ℝ} {f f' : ℝ → ℝ}
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hzero : ∀ x ∈ s, f' x = 0) :
    volume (f '' s) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => ContinuousLinearMap.toSpanSingleton ℝ (f' x))
  · intro x hx
    exact (hf' x hx).hasFDerivWithinAt
  · intro x hx
    rw [ContinuousLinearMap.det_toSpanSingleton, hzero x hx]

/-- A compact piece of the frontier of a smooth domain has a genuinely finite
atlas by local regular defining-function neighborhoods. -/
theorem IsSmoothDomain.exists_finite_regular_boundary_cover
    {U K : Set PlanePoint} (hU : IsSmoothDomain U) (hK : IsCompact K) :
    ∃ (t : Finset {p : PlanePoint // p ∈ frontier U ∩ K})
      (V : t → Set PlanePoint)
      (g : t → PlanePoint → ℝ)
      (D : t → PlanePoint →L[ℝ] ℝ),
      (∀ p : t,
        IsOpen (V p) ∧ (p.1 : PlanePoint) ∈ V p ∧
        ContDiffOn ℝ ∞ (g p) (V p) ∧ g p p.1 = 0 ∧
        HasFDerivAt (g p) (D p) p.1 ∧ D p ≠ 0 ∧
        U ∩ V p = V p ∩ {q | g p q < 0}) ∧
      frontier U ∩ K ⊆ ⋃ p : t, V p := by
  classical
  have hcert : ∀ p : {p : PlanePoint // p ∈ frontier U ∩ K},
      ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
          (D : PlanePoint →L[ℝ] ℝ),
        IsOpen V ∧ (p : PlanePoint) ∈ V ∧ ContDiffOn ℝ ∞ g V ∧
        g p = 0 ∧ HasFDerivAt g D p ∧ D ≠ 0 ∧
        U ∩ V = V ∩ {q | g q < 0} := by
    intro p
    exact hU.regular_boundary p p.property.1
  choose V g D hcert using hcert
  have hcompact : IsCompact (frontier U ∩ K) :=
    hK.inter_left isClosed_frontier
  have hcover : frontier U ∩ K ⊆ ⋃ p, V p := by
    intro p hp
    exact mem_iUnion.2 ⟨⟨p, hp⟩, (hcert ⟨p, hp⟩).2.1⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover V
    (fun p ↦ (hcert p).1) hcover
  refine ⟨t, fun p ↦ V p.1, fun p ↦ g p.1, fun p ↦ D p.1,
    fun p ↦ hcert p.1, ?_⟩
  simpa only [Set.iUnion_subtype] using ht

theorem exists_contDiff_cutoff_one_nhds_closed
    {S Q : Set PlanePoint} (hS : IsClosed S) (hQ : IsOpen Q)
    (hSQ : S ⊆ Q) :
    ∃ χ : PlanePoint → ℝ, ContDiff ℝ ∞ χ ∧
      (∀ᶠ p in 𝓝ˢ Qᶜ, χ p = 0) ∧
      (∀ᶠ p in 𝓝ˢ S, χ p = 1) ∧
      ∀ p, χ p ∈ Icc (0 : ℝ) 1 := by
  have hdisj : Disjoint Qᶜ S := Set.disjoint_left.2 (by
    intro p hpQ hpS
    exact hpQ (hSQ hpS))
  obtain ⟨χ, hχ0, hχ1, hχrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed
      (𝓘(ℝ, PlanePoint)) hQ.isClosed_compl hS hdisj (n := (⊤ : ℕ∞))
  refine ⟨χ, ?_, hχ0, hχ1, hχrange⟩
  exact contMDiff_iff_contDiff.mp χ.prop

/-- A bounded perturbation localized by a scalar cutoff. -/
def localizedBoundedPerturb (f χ : PlanePoint → ℝ) (c : PlanePoint × ℝ)
    (p : PlanePoint) : ℝ :=
  f p + χ p * (boundedPerturb f c p - f p)

lemma contDiff_boundedPerturb {f : PlanePoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (c : PlanePoint × ℝ) :
    ContDiff ℝ ∞ (boundedPerturb f c) := by
  have hax : ContDiff ℝ ∞ (fun p : PlanePoint => Real.arctan p.1) :=
    Real.contDiff_arctan.comp contDiff_fst
  have hay : ContDiff ℝ ∞ (fun p : PlanePoint => Real.arctan p.2) :=
    Real.contDiff_arctan.comp contDiff_snd
  unfold boundedPerturb
  exact ((hf.sub (contDiff_const.mul hax)).sub
    (contDiff_const.mul hay)).sub contDiff_const

lemma contDiff_localizedBoundedPerturb {f χ : PlanePoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hχ : ContDiff ℝ ∞ χ)
    (c : PlanePoint × ℝ) :
    ContDiff ℝ ∞ (localizedBoundedPerturb f χ c) := by
  unfold localizedBoundedPerturb
  exact hf.add (hχ.mul ((contDiff_boundedPerturb hf c).sub hf))

lemma abs_localizedBoundedPerturb_sub_le
    (f χ : PlanePoint → ℝ) (c : PlanePoint × ℝ)
    (hχ : ∀ p, χ p ∈ Icc (0 : ℝ) 1) (p : PlanePoint) :
    |localizedBoundedPerturb f χ c p - f p| ≤
      (Real.pi + 1) * ‖c‖ := by
  have hχabs : |χ p| ≤ 1 := by
    rw [abs_of_nonneg (hχ p).1]
    exact (hχ p).2
  rw [localizedBoundedPerturb, add_sub_cancel_left, abs_mul]
  calc
    |χ p| * |boundedPerturb f c p - f p| ≤
        1 * ((Real.pi + 1) * ‖c‖) :=
      mul_le_mul hχabs (abs_boundedPerturb_sub_le f c p)
        (abs_nonneg _) (by positivity)
    _ = (Real.pi + 1) * ‖c‖ := one_mul _

/-- A smooth defining function can be regularized inside a prescribed open
window while its strict sublevel remains literally unchanged outside.  The
closed set `S` contains every point where the defining function is small enough
for a new zero to occur. -/
theorem exists_smoothDomain_localizedBoundedPerturb
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {S Q : Set PlanePoint} (hS : IsClosed S) (hQ : IsOpen Q)
    (hSQ : S ⊆ Q) {ε : ℝ} (hε : 0 < ε)
    (hlarge : ∀ p ∉ S, ε ≤ |f p|) :
    ∃ (χ : PlanePoint → ℝ) (c : PlanePoint × ℝ),
      ContDiff ℝ ∞ χ ∧
      (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, |localizedBoundedPerturb f χ c p - f p| < ε) ∧
      IsSmoothDomain {p | localizedBoundedPerturb f χ c p < 0} ∧
      {p | localizedBoundedPerturb f χ c p < 0} ∩ Qᶜ =
        {p | f p < 0} ∩ Qᶜ := by
  obtain ⟨χ, hχsmooth, hχzero, hχone, hχrange⟩ :=
    exists_contDiff_cutoff_one_nhds_closed hS hQ hSQ
  have hpi : 0 < Real.pi + 1 := by positivity
  obtain ⟨c, hc, hdist⟩ :=
    (dense_regularBoundedParameters hf).exists_dist_lt
      0 (div_pos hε hpi)
  have hnorm : ‖c‖ < ε / (Real.pi + 1) := by
    simpa only [dist_zero_left] using hdist
  have hclose : ∀ p,
      |localizedBoundedPerturb f χ c p - f p| < ε := by
    intro p
    calc
      |localizedBoundedPerturb f χ c p - f p| ≤
          (Real.pi + 1) * ‖c‖ :=
        abs_localizedBoundedPerturb_sub_le f χ c hχrange p
      _ < (Real.pi + 1) * (ε / (Real.pi + 1)) :=
        mul_lt_mul_of_pos_left hnorm hpi
      _ = ε := by field_simp [ne_of_gt hpi]
  have hregular : ∀ p,
      localizedBoundedPerturb f χ c p = 0 →
        fderiv ℝ (localizedBoundedPerturb f χ c) p ≠ 0 := by
    intro p hpzero
    have hpS : p ∈ S := by
      by_contra hpnot
      have habsf : |f p| =
          |localizedBoundedPerturb f χ c p - f p| := by
        rw [hpzero, zero_sub, abs_neg]
      linarith [hlarge p hpnot, hclose p]
    have hχlocal : χ =ᶠ[𝓝 p] fun _ => (1 : ℝ) :=
      hχone.filter_mono (nhds_le_nhdsSet hpS)
    have heq : localizedBoundedPerturb f χ c =ᶠ[𝓝 p]
        boundedPerturb f c := by
      filter_upwards [hχlocal] with q hq
      simp [localizedBoundedPerturb, hq]
    have hzeroBounded : boundedPerturb f c p = 0 := by
      rw [← heq.eq_of_nhds, hpzero]
    rw [heq.fderiv_eq]
    exact boundedPerturb_regular hf hc p hzeroBounded
  refine ⟨χ, c, hχsmooth, hχrange, hclose,
    isSmoothDomain_sublevel_of_regular
      (contDiff_localizedBoundedPerturb hf hχsmooth c) hregular, ?_⟩
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hpQ⟩
    have hχp : χ p = 0 := hχzero.self_of_nhdsSet p hpQ
    exact ⟨by simpa [localizedBoundedPerturb, hχp] using hp, hpQ⟩
  · rintro ⟨hp, hpQ⟩
    have hχp : χ p = 0 := hχzero.self_of_nhdsSet p hpQ
    exact ⟨by simpa [localizedBoundedPerturb, hχp] using hp, hpQ⟩


/-- Uniformly shrinking localized regularizations form a genuine smooth
sequence.  The only measure hypothesis is nullity of the original zero level;
no collar agreement or smooth-sequence transfer is assumed. -/
theorem exists_localizedSmoothSequence_sublevel
    {f : PlanePoint → ℝ} (hf : ContDiff ℝ ∞ f)
    {Q : Set PlanePoint} (hQ : IsOpen Q)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hεanti : Antitone ε) (hεzero : Tendsto ε atTop (𝓝 0))
    (hband : {p | |f p| ≤ ε 0} ⊆ Q)
    (hbandFinite : volume {p | |f p| ≤ ε 0} ≠ ⊤)
    (hzero : volume {p | f p = 0} = 0) :
    ∃ (A : SmoothSequence) (g : ℕ → PlanePoint → ℝ),
      A.ConvergesTo {p | f p < 0} ∧
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n, A.carrier n = {p | g n p < 0}) ∧
      (∀ n, A.carrier n ∩ Qᶜ = {p | f p < 0} ∩ Qᶜ) ∧
      ∀ n, (A.carrier n ∆ {p | f p < 0}) ⊆
        {p | |f p| ≤ ε n} := by
  let S : ℕ → Set PlanePoint := fun n => {p | |f p| ≤ ε n}
  have hSclosed : ∀ n, IsClosed (S n) := by
    intro n
    exact isClosed_le hf.continuous.abs continuous_const
  have hSsub : ∀ n, S n ⊆ Q := by
    intro n p hp
    apply hband
    exact hp.trans (hεanti (Nat.zero_le n))
  have hlarge : ∀ n p, p ∉ S n → ε n ≤ |f p| := by
    intro n p hp
    exact (le_of_lt (not_le.mp hp))
  have hexists : ∀ n, ∃ (χ : PlanePoint → ℝ) (c : PlanePoint × ℝ),
      ContDiff ℝ ∞ χ ∧
      (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, |localizedBoundedPerturb f χ c p - f p| < ε n) ∧
      IsSmoothDomain {p | localizedBoundedPerturb f χ c p < 0} ∧
      {p | localizedBoundedPerturb f χ c p < 0} ∩ Qᶜ =
        {p | f p < 0} ∩ Qᶜ := by
    intro n
    exact exists_smoothDomain_localizedBoundedPerturb hf
      (hSclosed n) hQ (hSsub n) (hεpos n) (hlarge n)
  choose χ c hχsmooth hχrange hclose hsmooth hexterior using hexists
  let g : ℕ → PlanePoint → ℝ :=
    fun n => localizedBoundedPerturb f (χ n) (c n)
  let A : SmoothSequence :=
    { carrier := fun n => {p | g n p < 0}
      smooth := fun n => by
        dsimp only [g]
        exact hsmooth n }
  have hsubset : ∀ n, (A.carrier n ∆ {p | f p < 0}) ⊆ S n := by
    intro n p hp
    change (g n p < 0 ∧ ¬f p < 0) ∨
      (f p < 0 ∧ ¬g n p < 0) at hp
    change |f p| ≤ ε n
    have hclosen := hclose n p
    change |g n p - f p| < ε n at hclosen
    rcases hp with ⟨hgp, hfp⟩ | ⟨hfp, hgp⟩
    · rw [abs_of_nonneg (le_of_not_gt hfp)]
      linarith [neg_le_abs (g n p - f p)]
    · rw [abs_of_neg hfp]
      linarith [le_abs_self (g n p - f p)]
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => (hSclosed n).measurableSet
  have hSanti : Antitone S := by
    intro m n hmn p hp
    exact hp.trans (hεanti hmn)
  have hSinter : ⋂ n, S n = {p | f p = 0} := by
    ext p
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro hp
      have habsle : |f p| ≤ 0 :=
        ge_of_tendsto hεzero (Filter.Eventually.of_forall hp)
      exact abs_eq_zero.mp (le_antisymm habsle (abs_nonneg _))
    · intro hp n
      change |f p| ≤ ε n
      rw [hp, abs_zero]
      exact (hεpos n).le
  have hSvolume : Tendsto (fun n => volume (S n)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop
      (μ := volume) (fun n => (hSmeas n).nullMeasurableSet)
      hSanti ⟨0, hbandFinite⟩
    rw [hSinter, hzero] at hlim
    change Tendsto (fun n => volume (S n)) atTop (𝓝 0) at hlim
    exact hlim
  have hdist : Tendsto (fun n =>
      characteristicDistance (A.carrier n) {p | f p < 0})
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hSvolume (fun _ => bot_le)
    intro n
    exact measure_mono (hsubset n)
  refine ⟨A, g, hdist, ?_, ?_, ?_, hsubset⟩
  · intro n
    dsimp only [g]
    exact contDiff_localizedBoundedPerturb hf (hχsmooth n) (c n)
  · intro n
    rfl
  · intro n
    change {p | localizedBoundedPerturb f (χ n) (c n) p < 0} ∩ Qᶜ =
      {p | f p < 0} ∩ Qᶜ
    exact hexterior n


/-- A compact fiber of a real `C¹` map is finite when the derivative is
nonzero at every point of that fiber. -/
theorem finite_compact_fiber_of_hasDerivAt_ne
    {f f' : ℝ → ℝ} {K : Set ℝ} {y : ℝ}
    (hK : IsCompact K) (hf : ContinuousOn f K)
    (hderiv : ∀ x ∈ K, HasDerivAt f (f' x) x)
    (hreg : ∀ x ∈ K, f x = y → f' x ≠ 0) :
    (K ∩ f ⁻¹' {y}).Finite := by
  have hclosed : IsClosed (K ∩ f ⁻¹' {y}) :=
    hf.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  apply (hK.of_isClosed_subset hclosed inter_subset_left).finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  have hxy : f x = y := by simpa using hx.2
  have hevent : ∀ᶠ z in 𝓝[≠] x, f z ≠ y :=
    (hderiv x hx.1).eventually_ne (hreg x hx.1 hxy)
  rw [eventually_nhdsWithin_iff] at hevent
  rcases mem_nhds_iff.mp hevent with ⟨u, hu, huopen, hxu⟩
  refine ⟨u, huopen, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨hzu, hzK, hzy⟩
    by_cases hzx : z = x
    · exact hzx
    · exact False.elim ((hu hzu hzx) hzy)
  · rintro rfl
    exact ⟨hxu, hx.1, hxy⟩

/-- Outside the critical-value image, every compact fiber of a real `C¹` map
is finite.  The exceptional set of nonfinite compact fibers therefore has
Lebesgue measure zero. -/
theorem volume_setOf_not_finite_compact_fiber_eq_zero
    {f f' : ℝ → ℝ} {K : Set ℝ} (hK : IsCompact K)
    (hf : ContinuousOn f K)
    (hderiv : ∀ x ∈ K, HasDerivAt f (f' x) x) :
    volume {y | ¬ (K ∩ f ⁻¹' {y}).Finite} = 0 := by
  let C : Set ℝ := {x | x ∈ K ∧ f' x = 0}
  have hcritical : volume (f '' C) = 0 := by
    apply volume_image_critical_eq_zero
    · intro x hx
      exact (hderiv x hx.1).hasDerivWithinAt
    · intro x hx
      exact hx.2
  apply measure_mono_null (t := f '' C) ?_ hcritical
  intro y hy
  by_contra hycritical
  apply hy
  apply finite_compact_fiber_of_hasDerivAt_ne hK hf hderiv
  intro x hxK hxy hxzero
  apply hycritical
  exact ⟨x, ⟨hxK, hxzero⟩, hxy⟩


/-- Exact exterior preservation converts a localized regular sublevel into the
old exterior cost plus the complete weighted zero trace in the closed repair
region. -/
theorem smoothCost_localizedSublevel_le
    (lam : ℝ) {g : PlanePoint → ℝ} (hg : Continuous g)
    {Q U : Set PlanePoint}
    (heq : {p | g p < 0} ∩ Qᶜ = U ∩ Qᶜ) :
    smoothCost lam {p | g p < 0} ≤
      smoothCostOn lam U (closure Q)ᶜ +
        weightedTraceCost lam ({p | g p = 0} ∩ closure Q) := by
  apply smoothCost_sublevel_le_outside_add_zeroSet lam hg isClosed_closure
  ext p
  simp only [mem_inter_iff, mem_ofPred_eq]
  have hpiff :
      (g p < 0 ∧ p ∈ Qᶜ) ↔ (p ∈ U ∧ p ∈ Qᶜ) := by
    exact Set.ext_iff.mp heq p
  constructor
  · rintro ⟨hgp, hpclosure⟩
    have hpQ : p ∈ Qᶜ := fun hp => hpclosure (subset_closure hp)
    exact ⟨(hpiff.mp ⟨hgp, hpQ⟩).1, hpclosure⟩
  · rintro ⟨hpU, hpclosure⟩
    have hpQ : p ∈ Qᶜ := fun hp => hpclosure (subset_closure hp)
    exact ⟨(hpiff.mpr ⟨hpU, hpQ⟩).1, hpclosure⟩

end CMVRelaxation

namespace CMVRelaxation

/-- The complex-coordinate realization of a graph, with the horizontal
coordinate placed in the imaginary component to match `tangentComplexEquiv`. -/
def complexGraph (g : ℝ → ℝ) : ℝ → ℂ :=
  (Complex.ofRealCLM ∘ g) + fun x => x • Complex.I

@[simp] lemma complexGraph_re (g : ℝ → ℝ) (x : ℝ) :
    (complexGraph g x).re = g x := by simp [complexGraph]

@[simp] lemma complexGraph_im (g : ℝ → ℝ) (x : ℝ) :
    (complexGraph g x).im = x := by simp [complexGraph]

lemma hasDerivAt_complexGraph {g : ℝ → ℝ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (complexGraph g)
      (Complex.ofRealCLM (deriv g x) + (1 : ℝ) • Complex.I) x :=
  (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hg.hasDerivAt).add
    ((hasDerivAt_id x).smul_const Complex.I)

lemma norm_complexGraph_deriv {g : ℝ → ℝ} {x : ℝ} :
    ‖Complex.ofRealCLM (deriv g x) + (1 : ℝ) • Complex.I‖ =
      Real.sqrt (1 + (deriv g x) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma lipschitzOnWith_complexGraph_Icc
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ)) :
    LipschitzOnWith K (complexGraph g) (Icc a b) := by
  refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x => Complex.ofRealCLM (deriv g x) +
      (1 : ℝ) • Complex.I) (convex_Icc a b) ?_ ?_
  · intro x hx
    exact (hasDerivAt_complexGraph (hg x)).hasDerivWithinAt
  · intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, norm_complexGraph_deriv]
    exact hK x hx

/-- The Euclidean `L²` realization of a graph. -/
def euclideanGraph (g : ℝ → ℝ) (x : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (x, g x)

lemma euclideanGraph_eq (g : ℝ → ℝ) :
    euclideanGraph g = tangentComplexEquiv.symm ∘ complexGraph g := by
  funext x
  apply tangentComplexEquiv.injective
  apply Complex.ext <;> simp [euclideanGraph]

lemma lipschitzOnWith_euclideanGraph_Icc
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ)) :
    LipschitzOnWith K (euclideanGraph g) (Icc a b) := by
  rw [euclideanGraph_eq]
  simpa only [one_mul] using
    LipschitzWith.comp_lipschitzOnWith
      tangentComplexEquiv.symm.isometry.lipschitz
      (lipschitzOnWith_complexGraph_Icc hg hK)

/-- A derivative bound by the Euclidean graph speed bounds the literal
one-dimensional Hausdorff measure of the graph segment. -/
theorem hausdorffMeasure_euclideanGraph_Icc_le
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ)) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, g x)) '' Icc a b)) ≤
      (K : ENNReal) * ENNReal.ofReal (b - a) := by
  rw [image_image]
  change (μH[1] : Measure EuclideanPlane)
      (euclideanGraph g '' Icc a b) ≤ _
  simpa [ENNReal.rpow_one, hausdorffMeasure_real, Real.volume_Icc] using
    (lipschitzOnWith_euclideanGraph_Icc hg hK).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num)

open CMVTwoPatchGraphVariation

/-- Weighted trace cost is subadditive over a fixed finite trace family. -/
lemma weightedTraceCost_iUnion_fin_le
    (lam : ℝ) {N : ℕ} (S : Fin N → Set PlanePoint) :
    weightedTraceCost lam (⋃ i, S i) ≤
      ∑ i, weightedTraceCost lam (S i) := by
  unfold weightedTraceCost
  rw [image_iUnion]
  simpa using
    (MeasureTheory.lintegral_iUnion_le
      (μ := (μH[1] : Measure EuclideanPlane))
      (fun i => planeEuclideanHomeomorph '' S i)
      (fun z => ENNReal.ofReal (euclideanStripDensity lam z)))

/-- A fixed finite family of traces has vanishing total weighted cost when
each member does. -/
theorem tendsto_weightedTraceCost_iUnion_fin_zero
    (lam : ℝ) {N : ℕ} {S : ℕ → Fin N → Set PlanePoint}
    (hS : ∀ i, Tendsto (fun n => weightedTraceCost lam (S n i))
      atTop (𝓝 0)) :
    Tendsto (fun n => weightedTraceCost lam (⋃ i, S n i))
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n =>
      ∑ i, weightedTraceCost lam (S n i)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun i _ => hS i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum ?_ ?_
  · intro n
    exact bot_le
  · intro n
    exact weightedTraceCost_iUnion_fin_le lam (S n)

/-- A graph segment inside one protected tube has a direct weighted `H¹`
upper bound. This is the quantitative estimate used for explicit short
connectors in a finite-junction splice repair. -/
theorem weightedTraceCost_graph_Icc_le
    {lam : ℝ} (P : GraphPatch) (T : P.Tube)
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hsub : Icc a b ⊆ Icc P.a P.b)
    (hclose : ∀ x ∈ Icc a b,
      |g x - P.graph x| < T.radius)
    (hK : ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ)) :
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc a b) ≤
      ENNReal.ofReal (P.zone.weight lam) * (K : ENNReal) *
        ENNReal.ofReal (b - a) := by
  calc
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc a b) ≤
        ENNReal.ofReal (P.zone.weight lam) *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              ((fun x : ℝ => (x, g x)) '' Icc a b)) := by
      apply weightedTraceCost_le_const_mul_hausdorff
      rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change ENNReal.ofReal (StripDensity lam (x, g x)) ≤
        ENNReal.ofReal (P.zone.weight lam)
      rw [P.zone.stripDensity_eq_weight
        (T.closed_tube_in_zone x (hsub hx) (g x) (hclose x hx).le)]
    _ ≤ ENNReal.ofReal (P.zone.weight lam) *
          ((K : ENNReal) * ENNReal.ofReal (b - a)) := by
      gcongr
      exact hausdorffMeasure_euclideanGraph_Icc_le hg hK
    _ = _ := by rw [mul_assoc]

/-- Uniformly Lipschitz graph connectors in one protected density tube have
vanishing weighted `H¹` cost when their horizontal widths vanish. -/
theorem tendsto_weightedTraceCost_graph_Icc_zero
    {lam : ℝ} (P : GraphPatch) (T : P.Tube)
    {g : ℕ → ℝ → ℝ} {a b : ℕ → ℝ} {K : NNReal}
    (hg : ∀ n, Differentiable ℝ (g n))
    (hsub : ∀ n, Icc (a n) (b n) ⊆ Icc P.a P.b)
    (hclose : ∀ n, ∀ x ∈ Icc (a n) (b n),
      |g n x - P.graph x| < T.radius)
    (hK : ∀ n, ∀ x ∈ Icc (a n) (b n),
      Real.sqrt (1 + (deriv (g n) x) ^ 2) ≤ (K : ℝ))
    (hwidth : Tendsto (fun n => ENNReal.ofReal (b n - a n))
      atTop (𝓝 0)) :
    Tendsto (fun n =>
      weightedTraceCost lam
        ((fun x : ℝ => (x, g n x)) '' Icc (a n) (b n)))
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun n =>
      (ENNReal.ofReal (P.zone.weight lam) * (K : ENNReal)) *
        ENNReal.ofReal (b n - a n)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hwidth
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.coe_ne_top))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper ?_ ?_
  · intro n
    exact bot_le
  · intro n
    exact weightedTraceCost_graph_Icc_le P T (hg n)
      (hsub n) (hclose n) (hK n)

/-- A raw splice with a `C∞` occupied graph domain pays the unchanged
exterior, the inserted graph's literal weighted `H¹` trace, and the complete
cut trace. -/
theorem smoothCost_spliceIn_occupiedGraphDomain_le
    (lam : ℝ) (U : Set PlanePoint)
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (W : Set PlanePoint) :
    smoothCost lam (spliceIn U (P.occupiedGraphDomain g) W) ≤
      smoothCostOn lam U (interior Wᶜ) +
        weightedTraceCost lam
          (((fun x : ℝ => (x, g x)) '' univ) ∩ interior W) +
        weightedTraceCost lam
          (spliceCutTrace U (P.occupiedGraphDomain g) W) := by
  calc
    smoothCost lam (spliceIn U (P.occupiedGraphDomain g) W) ≤
        smoothCostOn lam U (interior Wᶜ) +
          smoothCostOn lam (P.occupiedGraphDomain g) (interior W) +
          weightedTraceCost lam
            (spliceCutTrace U (P.occupiedGraphDomain g) W) :=
      smoothCost_spliceIn_le_outside_add_inside_add_cutTrace
        lam U (P.occupiedGraphDomain g) W
    _ = _ := by
      rw [smoothCostOn_eq_weightedTraceCost_frontier_inter
            lam (P.occupiedGraphDomain g) measurableSet_interior,
          P.frontier_occupiedGraphDomain hg.continuous]

/-- The same raw-splice estimate with the inserted graph trace bounded by a
protected-tube Lipschitz constant. -/
theorem smoothCost_spliceIn_occupiedGraphDomain_le_of_graph_bound
    (lam : ℝ) (U : Set PlanePoint)
    (P : GraphPatch) (T : P.Tube)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {a b : ℝ} {K : NNReal} (W : Set PlanePoint)
    (hW : ∀ p ∈ interior W, p.1 ∈ Icc a b)
    (hsub : Icc a b ⊆ Icc P.a P.b)
    (hclose : ∀ x ∈ Icc a b,
      |g x - P.graph x| < T.radius)
    (hK : ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ)) :
    smoothCost lam (spliceIn U (P.occupiedGraphDomain g) W) ≤
      smoothCostOn lam U (interior Wᶜ) +
        ENNReal.ofReal (P.zone.weight lam) * (K : ENNReal) *
          ENNReal.ofReal (b - a) +
        weightedTraceCost lam
          (spliceCutTrace U (P.occupiedGraphDomain g) W) := by
  refine (smoothCost_spliceIn_occupiedGraphDomain_le
    lam U P hg W).trans ?_
  gcongr
  refine (weightedTraceCost_mono lam ?_).trans
    (weightedTraceCost_graph_Icc_le P T
      (hg.differentiable (by simp)) hsub hclose hK)
  rintro p ⟨⟨x, _, rfl⟩, hpW⟩
  exact ⟨x, hW (x, g x) hpW, rfl⟩

end CMVRelaxation

namespace CMVRelaxation

/-- A finite adjacent-interval cover of an ordered endpoint interval. -/
lemma Icc_subset_singleton_union_iUnion_adjacent
    (p : ℕ → ℝ) (n : ℕ) :
    Icc (p 0) (p n) ⊆
      {p 0} ∪ ⋃ i ∈ Finset.range n, Icc (p i) (p (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine (Icc_subset_Icc_union_Icc (b := p n)).trans ?_
      intro x hx
      rcases hx with hx | hx
      · rcases ih hx with hx0 | hxcells
        · exact Or.inl hx0
        · right
          simp only [mem_iUnion, Finset.mem_range] at hxcells ⊢
          rcases hxcells with ⟨i, hi, hxi⟩
          exact ⟨i, hi.trans (Nat.lt_succ_self n), hxi⟩
      · right
        simp only [mem_iUnion, Finset.mem_range]
        exact ⟨n, ⟨Nat.lt_succ_self n,
          by simpa only [Nat.succ_eq_add_one] using hx⟩⟩

/-- An arbitrarily sharp upper bound for the Euclidean `H¹` of a `C¹` graph,
obtained by a uniform partition and local Lipschitz estimates. -/
theorem hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral_add
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {a b η : ℝ} (hab : a < b) (hη : 0 < η) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, g x)) '' Icc a b)) ≤
      ENNReal.ofReal
        ((∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2)) + η) := by
  let F : ℝ → ℝ := fun x => Real.sqrt (1 + (deriv g x) ^ 2)
  have hderiv : Continuous (deriv g) :=
    hg.continuous_deriv (by norm_num)
  have hF : Continuous F :=
    (continuous_const.add (hderiv.pow 2)).sqrt
  let ε := η / (4 * (b - a))
  have hε : 0 < ε :=
    div_pos hη (mul_pos (by norm_num) (sub_pos.mpr hab))
  have huc : UniformContinuousOn F (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hcloseF⟩ := huc ε hε
  obtain ⟨N, hN, hdδ, hmidneg⟩ :=
    exists_midpoint_sum_add_ge_intervalIntegral
      hF.neg hab (half_pos hη) hδ
  let d := (b - a) / (N : ℝ)
  let p : ℕ → ℝ := fun k => a + (k : ℝ) * d
  let m : Fin N → ℝ := fun i => a + ((i : ℝ) + 1 / 2) * d
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd : 0 < d := div_pos (sub_pos.mpr hab) hNreal
  have hp0 : p 0 = a := by simp [p]
  have hpN : p N = b := by
    dsimp [p, d]
    field_simp [hNreal.ne']
    ring_nf
  have hpmono : Monotone p := by
    intro i j hij
    dsimp [p]
    gcongr
  have hm_between (i : Fin N) :
      m i ∈ Icc (p i.1) (p (i.1 + 1)) := by
    have hm_eq : m i = (p i.1 + p (i.1 + 1)) / 2 := by
      dsimp [m, p]
      push_cast
      ring
    rw [hm_eq]
    constructor <;> linarith [hpmono (Nat.le_succ i.1)]
  have hcell_mem (i : Fin N) :
      Icc (p i.1) (p (i.1 + 1)) ⊆ Icc a b := by
    intro x hx
    constructor
    · rw [← hp0]
      exact (hpmono (Nat.zero_le i.1)).trans hx.1
    · rw [← hpN]
      exact hx.2.trans (hpmono (Nat.succ_le_iff.mpr i.2))
  have hmmem (i : Fin N) : m i ∈ Icc a b :=
    hcell_mem i (hm_between i)
  have hspeed (i : Fin N) :
      ∀ x ∈ Icc (p i.1) (p (i.1 + 1)), F x ≤ F (m i) + ε := by
    intro x hx
    have hdist : dist x (m i) < δ := by
      rw [Real.dist_eq]
      have hxm : |x - m i| ≤ d := by
        rw [abs_le]
        have hstep : p (i.1 + 1) - p i.1 = d := by
          dsimp [p]
          push_cast
          ring
        constructor <;>
          linarith [hx.1, hx.2, (hm_between i).1, (hm_between i).2]
      exact hxm.trans_lt hdδ
    have hc := hcloseF x (hcell_mem i hx) (m i) (hmmem i) hdist
    rw [Real.dist_eq] at hc
    linarith [le_abs_self (F x - F (m i))]
  let K : Fin N → NNReal :=
    fun i => Real.toNNReal (F (m i) + ε)
  have hKcoe (i : Fin N) : (K i : ℝ) = F (m i) + ε := by
    dsimp [K]
    exact max_eq_left (add_nonneg (Real.sqrt_nonneg _) hε.le)
  have hcellMeasure (i : Fin N) :
      (μH[1] : Measure EuclideanPlane)
          (euclideanGraph g '' Icc (p i.1) (p (i.1 + 1))) ≤
        (K i : ENNReal) * ENNReal.ofReal d := by
    have hstep : p (i.1 + 1) - p i.1 = d := by
      dsimp [p]
      push_cast
      ring
    change (μH[1] : Measure EuclideanPlane)
      ((fun x : ℝ => planeEuclideanHomeomorph (x, g x)) ''
        Icc (p i.1) (p (i.1 + 1))) ≤ _
    rw [← hstep]
    have hmeasure := hausdorffMeasure_euclideanGraph_Icc_le
      (a := p i.1) (b := p (i.1 + 1)) (K := K i)
      (hg.differentiable (by norm_num))
      (fun x hx => by
        rw [hKcoe]
        exact hspeed i x hx)
    rw [image_image] at hmeasure
    simpa only [Function.comp_apply] using hmeasure
  have hcover :
      euclideanGraph g '' Icc a b ⊆
        {euclideanGraph g a} ∪
          ⋃ i ∈ Finset.range N,
            euclideanGraph g '' Icc (p i) (p (i + 1)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxp : x ∈ Icc (p 0) (p N) := by
      rwa [hp0, hpN]
    rcases Icc_subset_singleton_union_iUnion_adjacent p N hxp with
      hx0 | hxcells
    · left
      rw [mem_singleton_iff] at hx0 ⊢
      rw [hx0, hp0]
    · right
      simp only [mem_iUnion, Finset.mem_range] at hxcells ⊢
      rcases hxcells with ⟨i, hi, hxi⟩
      exact ⟨i, hi, x, hxi, rfl⟩
  have hKofReal (i : Fin N) :
      (K i : ENNReal) = ENNReal.ofReal (F (m i) + ε) := by
    rw [← ENNReal.ofReal_coe_nnreal, hKcoe]
  have hsumENN :
      ∑ i : Fin N, (K i : ENNReal) * ENNReal.ofReal d =
        ENNReal.ofReal (∑ i : Fin N, (F (m i) + ε) * d) := by
    symm
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i _
      rw [ENNReal.ofReal_mul
        (add_nonneg (Real.sqrt_nonneg _) hε.le), ← hKofReal]
    · intro i _
      exact mul_nonneg (add_nonneg (Real.sqrt_nonneg _) hε.le) hd.le
  have hmid :
      (∑ i : Fin N, F (m i) * d) ≤
        (∫ x in a..b, F x) + η / 2 := by
    change (∫ x in a..b, -F x) ≤
      (∑ i : Fin N, -F (m i) * d) + η / 2 at hmidneg
    rw [intervalIntegral.integral_neg] at hmidneg
    have hsumneg : (∑ i : Fin N, -F (m i) * d) =
        -(∑ i : Fin N, F (m i) * d) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
    rw [hsumneg] at hmidneg
    linarith
  have hsumExpand :
      (∑ i : Fin N, (F (m i) + ε) * d) =
        (∑ i : Fin N, F (m i) * d) + (N : ℝ) * (ε * d) := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hNeps : (N : ℝ) * (ε * d) = η / 4 := by
    dsimp [ε, d]
    field_simp [hNreal.ne', (sub_pos.mpr hab).ne']
  have hsumReal :
      (∑ i : Fin N, (F (m i) + ε) * d) ≤
        (∫ x in a..b, F x) + η := by
    rw [hsumExpand, hNeps]
    linarith
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  rw [image_image]
  change (μH[1] : Measure EuclideanPlane)
      (euclideanGraph g '' Icc a b) ≤ _
  calc
    (μH[1] : Measure EuclideanPlane)
        (euclideanGraph g '' Icc a b) ≤
        (μH[1] : Measure EuclideanPlane)
          ({euclideanGraph g a} ∪
            ⋃ i ∈ Finset.range N,
              euclideanGraph g '' Icc (p i) (p (i + 1))) :=
      measure_mono hcover
    _ ≤ (μH[1] : Measure EuclideanPlane) {euclideanGraph g a} +
          (μH[1] : Measure EuclideanPlane)
            (⋃ i ∈ Finset.range N,
              euclideanGraph g '' Icc (p i) (p (i + 1))) :=
      measure_union_le _ _
    _ ≤ ∑ i ∈ Finset.range N,
          (μH[1] : Measure EuclideanPlane)
            (euclideanGraph g '' Icc (p i) (p (i + 1))) := by
      simpa using
        (MeasureTheory.measure_biUnion_finset_le
          (μ := (μH[1] : Measure EuclideanPlane))
          (Finset.range N)
          (fun i => euclideanGraph g '' Icc (p i) (p (i + 1))))
    _ = ∑ i : Fin N,
          (μH[1] : Measure EuclideanPlane)
            (euclideanGraph g '' Icc (p i.1) (p (i.1 + 1))) :=
      (Fin.sum_univ_eq_sum_range (fun i =>
        (μH[1] : Measure EuclideanPlane)
          (euclideanGraph g '' Icc (p i) (p (i + 1)))) N).symm
    _ ≤ ∑ i : Fin N, (K i : ENNReal) * ENNReal.ofReal d := by
      exact Finset.sum_le_sum fun i _ => hcellMeasure i
    _ = ENNReal.ofReal (∑ i : Fin N, (F (m i) + ε) * d) :=
      hsumENN
    _ ≤ ENNReal.ofReal ((∫ x in a..b, F x) + η) :=
      ENNReal.ofReal_le_ofReal hsumReal
    _ = _ := rfl

/-- The literal Euclidean `H¹` of a `C¹` graph is bounded by its graph-speed
integral. -/
theorem hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {a b : ℝ} (hab : a ≤ b) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, g x)) '' Icc a b)) ≤
      ENNReal.ofReal
        (∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2)) := by
  rcases hab.eq_or_lt with rfl | hab
  · let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
      Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
    simp
  · have hInt : 0 ≤
        ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) :=
      intervalIntegral.integral_nonneg hab.le
        (fun x _ => Real.sqrt_nonneg _)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    have happrox :=
      hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral_add
        hg hab hεreal
    rw [ENNReal.ofReal_add hInt hεreal.le,
      ENNReal.ofReal_coe_nnreal] at happrox
    exact happrox

open CMVTwoPatchGraphVariation

/-- In a protected constant-density tube, literal weighted graph trace is
bounded sharply by the weighted graph-speed integral. -/
theorem weightedTraceCost_graph_Icc_le_intervalIntegral
    {lam : ℝ} (hlam : 1 < lam)
    (P : GraphPatch) (T : P.Tube)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hclose : ∀ x ∈ Icc P.a P.b,
      |g x - P.graph x| < T.radius) :
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc P.a P.b) ≤
      ENNReal.ofReal
        (P.zone.weight lam *
          ∫ x in P.a..P.b,
            Real.sqrt (1 + (deriv g x) ^ 2)) := by
  have hweight : 0 ≤ P.zone.weight lam :=
    (P.zone.weight_pos hlam).le
  calc
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc P.a P.b) ≤
        ENNReal.ofReal (P.zone.weight lam) *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              ((fun x : ℝ => (x, g x)) '' Icc P.a P.b)) := by
      apply weightedTraceCost_le_const_mul_hausdorff
      rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change ENNReal.ofReal (StripDensity lam (x, g x)) ≤
        ENNReal.ofReal (P.zone.weight lam)
      rw [P.zone.stripDensity_eq_weight
        (T.closed_tube_in_zone x hx (g x) (hclose x hx).le)]
    _ ≤ ENNReal.ofReal (P.zone.weight lam) *
          ENNReal.ofReal
            (∫ x in P.a..P.b,
              Real.sqrt (1 + (deriv g x) ^ 2)) := by
      gcongr
      exact hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral
        hg P.a_lt_b.le
    _ = _ := (ENNReal.ofReal_mul hweight).symm

/-- For a varied graph staying in a protected tube, the weighted trace is
bounded by the exact graph functional used by the two-patch variation. -/
theorem weightedTraceCost_variedGraph_Icc_le_weightedGraphLength
    {lam : ℝ} (hlam : 1 < lam)
    (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hg : ContDiff ℝ 1 (P.variedGraph v t))
    (hclose : ∀ x ∈ Icc P.a P.b,
      |P.variedGraph v t x - P.graph x| < T.radius) :
    weightedTraceCost lam
        ((fun x : ℝ => (x, P.variedGraph v t x)) ''
          Icc P.a P.b) ≤
      ENNReal.ofReal (weightedGraphLength lam P v t) := by
  rw [weightedGraphLength_eq_weight]
  · exact weightedTraceCost_graph_Icc_le_intervalIntegral
      hlam P T hg hclose
  · intro x hx
    exact T.closed_tube_in_zone x ⟨hx.1.le, hx.2⟩
      (P.variedGraph v t x) (hclose x ⟨hx.1.le, hx.2⟩).le

/-- A raw splice by a smooth varied graph pays the exact two-patch graph
functional, plus the unchanged exterior and the complete cut trace. -/
theorem smoothCost_spliceIn_variedGraph_le_weightedGraphLength
    {lam : ℝ} (hlam : 1 < lam) (U : Set PlanePoint)
    (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} {t : ℝ}
    (hg : ContDiff ℝ ∞ (P.variedGraph v t))
    (hclose : ∀ x ∈ Icc P.a P.b,
      |P.variedGraph v t x - P.graph x| < T.radius)
    (W : Set PlanePoint)
    (hW : ∀ p ∈ interior W, p.1 ∈ Icc P.a P.b) :
    smoothCost lam
        (spliceIn U (P.occupiedGraphDomain (P.variedGraph v t)) W) ≤
      smoothCostOn lam U (interior Wᶜ) +
        ENNReal.ofReal (weightedGraphLength lam P v t) +
        weightedTraceCost lam
          (spliceCutTrace U
            (P.occupiedGraphDomain (P.variedGraph v t)) W) := by
  refine (smoothCost_spliceIn_occupiedGraphDomain_le
    lam U P hg W).trans ?_
  gcongr
  refine (weightedTraceCost_mono lam ?_).trans
    (weightedTraceCost_variedGraph_Icc_le_weightedGraphLength
      hlam P T (hg.of_le (by simp)) hclose)
  rintro p ⟨⟨x, _, rfl⟩, hpW⟩
  exact ⟨x, hW (x, P.variedGraph v t x) hpW, rfl⟩

end CMVRelaxation

namespace CMVRelaxation

open CMVTwoPatchGraphVariation

/-- A selected density-local `C∞` graph gives a raw splice whose inserted
trace pays at most the varied graph functional plus the prescribed allowance. -/
theorem exists_smoothGraph_splice_cost_le_weightedGraphLength_add
    {lam : ℝ} (hlam : 1 < lam) (U : Set PlanePoint)
    (P : GraphPatch) (T : P.Tube)
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (t : ℝ)
    (hshift : ∀ x ∈ Icc P.a P.b, |t * v x| ≤ T.radius / 2)
    {η : ℝ} (hη : 0 < η) (W : Set PlanePoint)
    (hW : ∀ p ∈ interior W, p.1 ∈ Icc P.a P.b) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧
      g P.a = P.variedGraph v t P.a ∧
      (∀ x ∈ Icc P.a P.b, |g x - P.graph x| < T.radius) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g x)) ∧
      smoothCost lam (spliceIn U (P.occupiedGraphDomain g) W) ≤
        smoothCostOn lam U (interior Wᶜ) +
          ENNReal.ofReal (weightedGraphLength lam P v t + η) +
          weightedTraceCost lam
            (spliceCutTrace U (P.occupiedGraphDomain g) W) := by
  obtain ⟨g, hg, hga, hclose, hzone, hlength⟩ :=
    P.exists_smoothGraph_in_tube_weightedLength_lt
      T hlam hv t hshift hη
  refine ⟨g, hg, hga, hclose, hzone, ?_⟩
  have hcostReal :
      P.zone.weight lam *
          (∫ x in P.a..P.b,
            Real.sqrt (1 + (deriv g x) ^ 2)) ≤
        weightedGraphLength lam P v t + η := by
    linarith [le_abs_self
      (P.zone.weight lam *
          (∫ x in P.a..P.b,
            Real.sqrt (1 + (deriv g x) ^ 2)) -
        weightedGraphLength lam P v t)]
  refine (smoothCost_spliceIn_occupiedGraphDomain_le
    lam U P hg W).trans ?_
  gcongr
  refine (weightedTraceCost_mono lam
    (T := (fun x : ℝ => (x, g x)) '' Icc P.a P.b) ?_).trans ?_
  · rintro p ⟨⟨x, _, rfl⟩, hpW⟩
    exact ⟨x, hW (x, g x) hpW, rfl⟩
  · exact (weightedTraceCost_graph_Icc_le_intervalIntegral
      hlam P T (hg.of_le (by simp)) hclose).trans
      (ENNReal.ofReal_le_ofReal hcostReal)

end CMVRelaxation

namespace CMVRelaxation

open CMVTwoPatchGraphVariation

/-- A finite family of protected `C¹` connector graphs contributes at most
the sum of its exact weighted graph-speed budgets beyond an unchanged trace. -/
theorem weightedTraceCost_union_iUnion_graph_Icc_le_intervalIntegrals
    {lam : ℝ} (hlam : 1 < lam)
    (P : GraphPatch) (T : P.Tube) (S : Set PlanePoint)
    {N : ℕ} (g : Fin N → ℝ → ℝ)
    (hg : ∀ i, ContDiff ℝ 1 (g i))
    (hclose : ∀ i, ∀ x ∈ Icc P.a P.b,
      |g i x - P.graph x| < T.radius) :
    weightedTraceCost lam
        (S ∪ ⋃ i,
          (fun x : ℝ => (x, g i x)) '' Icc P.a P.b) ≤
      weightedTraceCost lam S +
        ∑ i, ENNReal.ofReal
          (P.zone.weight lam *
            ∫ x in P.a..P.b,
              Real.sqrt (1 + (deriv (g i) x) ^ 2)) := by
  refine (weightedTraceCost_union_le lam S _).trans
    (add_le_add le_rfl ?_)
  refine (weightedTraceCost_iUnion_fin_le lam
    (fun i => (fun x : ℝ => (x, g i x)) '' Icc P.a P.b)).trans ?_
  exact Finset.sum_le_sum fun i _ =>
    weightedTraceCost_graph_Icc_le_intervalIntegral
      hlam P T (hg i) (hclose i)

end CMVRelaxation
namespace CMVRelaxation

/-- A point of the frontier of a strict sublevel has value zero under only
pointwise continuity at that point. -/
lemma eq_zero_of_mem_frontier_lt_of_continuousAt
    {g : PlanePoint → ℝ} {p : PlanePoint}
    (hg : ContinuousAt g p) (hp : p ∈ frontier {q | g q < 0}) :
    g p = 0 := by
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 < g p := lt_of_not_ge hnot
    have hnhds : {q : PlanePoint | 0 < g q} ∈ 𝓝 p :=
      hg (Ioi_mem_nhds hpos)
    have hpint : p ∈ interior ({q : PlanePoint | g q < 0}ᶜ) := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset hnhds fun q hq hqneg => by
        change 0 < g q at hq
        change g q < 0 at hqneg
        exact (not_lt_of_ge hq.le) hqneg
    have hpfront : p ∈ frontier ({q : PlanePoint | g q < 0}ᶜ) := by
      simpa only [frontier_compl] using hp
    exact Set.disjoint_left.1 disjoint_interior_frontier hpint hpfront
  · by_contra hnot
    have hneg : g p < 0 := lt_of_not_ge hnot
    have hnhds : {q : PlanePoint | g q < 0} ∈ 𝓝 p :=
      hg (Iio_mem_nhds hneg)
    have hpint : p ∈ interior {q : PlanePoint | g q < 0} := by
      rw [mem_interior_iff_mem_nhds]
      exact hnhds
    exact Set.disjoint_left.1 disjoint_interior_frontier hpint hp

/-- A nonzero real-valued linear functional on the coordinate plane is
nonzero on at least one coordinate vector. -/
lemma continuousLinearMap_ne_zero_has_coordinate
    (D : PlanePoint →L[ℝ] ℝ) (hD : D ≠ 0) :
    D (1, 0) ≠ 0 ∨ D (0, 1) ≠ 0 := by
  by_cases hx : D (1, 0) ≠ 0
  · exact Or.inl hx
  · right
    intro hy
    apply hD
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    calc
      D (x, y) = D (x • (1, 0) + y • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = x • D (1, 0) + y • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = 0 := by rw [not_ne_iff.mp hx, hy]; simp


/-- The full defining-function data asserting that a smooth boundary is
transverse to a selected vertical line. -/
def IsVerticalRegularBoundaryValue
    (U K : Set PlanePoint) (x : ℝ) : Prop :=
  ∀ p ∈ frontier U ∩ K ∩ verticalLine x,
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧ D (0, 1) ≠ 0 ∧
      U ∩ V = V ∩ {q | g q < 0}

/-- Horizontal analogue of `IsVerticalRegularBoundaryValue`. -/
def IsHorizontalRegularBoundaryValue
    (U K : Set PlanePoint) (y : ℝ) : Prop :=
  ∀ p ∈ frontier U ∩ K ∩ horizontalLine y,
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧ D (1, 0) ≠ 0 ∧
      U ∩ V = V ∩ {q | g q < 0}

private lemma scalarCLM_isInvertible_of_apply_one_ne_zero
    (A : ℝ →L[ℝ] ℝ) (hA : A 1 ≠ 0) : A.IsInvertible := by
  let B : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (A 1)⁻¹
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := B)
  · apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      B, ContinuousLinearMap.toSpanSingleton_apply_one]
    calc
      A (A 1)⁻¹ = A ((A 1)⁻¹ • (1 : ℝ)) := by simp
      _ = (A 1)⁻¹ • A 1 := A.map_smul _ _
      _ = 1 := by simpa [smul_eq_mul] using inv_mul_cancel₀ hA
  · apply ContinuousLinearMap.ext_ring
    simp [B, ContinuousLinearMap.comp_apply, hA]

/-- A defining function that is `C∞` on one fixed open neighborhood and
transverse to the second coordinate has a global `C∞` implicit graph
representative agreeing with its zero set near the base point.

The extra globalization is essential: `ContDiffAt ℝ ∞` alone permits the
neighborhood to shrink with the derivative order, while the graph-switch
repairs require one genuinely smooth graph. -/
theorem exists_contDiff_infty_implicitGraph_of_contDiffOn
    {f : PlanePoint → ℝ} {u : PlanePoint} {V : Set PlanePoint}
    (hV : IsOpen V) (huV : u ∈ V) (hf : ContDiffOn ℝ ∞ f V)
    (htrans : fderiv ℝ f u (0, 1) ≠ 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ φ u.1 = u.2 ∧
      ∀ᶠ q in 𝓝 u, f q = f u ↔ φ q.1 = q.2 := by
  have hfu : ContDiffAt ℝ ∞ f u := hf.contDiffAt (hV.mem_nhds huV)
  have hfu1 : ContDiffAt ℝ 1 f u := hfu.of_le (by simp)
  have htransContinuous :
      ContinuousAt (fun q => fderiv ℝ f q (0, 1)) u :=
    (hfu1.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have htransEventually :
      ∀ᶠ q in 𝓝 u, fderiv ℝ f q (0, 1) ≠ 0 := by
    exact htransContinuous.eventually_ne htrans
  rw [_root_.eventually_nhds_iff] at htransEventually
  obtain ⟨W, hWtrans, hWopen, huW⟩ := htransEventually
  let Q : Set PlanePoint := V ∩ W
  have hQopen : IsOpen Q := hV.inter hWopen
  have huQ : u ∈ Q := ⟨huV, huW⟩
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hAone : A 1 ≠ 0 := by
    simpa [A, ContinuousLinearMap.comp_apply] using htrans
  have hAinv : A.IsInvertible :=
    scalarCLM_isInvertible_of_apply_one_ne_zero A hAone
  let data :=
    (hfu.hasStrictFDerivAt (by simp)).implicitFunctionDataOfProdDomain hAinv
  let e : OpenPartialHomeomorph PlanePoint PlanePoint :=
    data.toOpenPartialHomeomorph.restrOpen Q hQopen
  have huSource : u ∈ e.source := by
    change u ∈ data.toOpenPartialHomeomorph.source ∩ Q
    exact ⟨by
      simpa only [data, HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain] using
        data.pt_mem_toOpenPartialHomeomorph_source, huQ⟩
  have he_apply (q : PlanePoint) : e q = (f q, q.1) := by
    rfl
  let I : Set ℝ := {x | (f u, x) ∈ e.target}
  have hIopen : IsOpen I := by
    exact e.open_target.preimage
      (continuous_const.prodMk continuous_id)
  have huI : u.1 ∈ I := by
    change (f u, u.1) ∈ e.target
    simpa only [he_apply] using e.map_source huSource
  let φ₀ : ℝ → ℝ := fun x => (e.symm (f u, x)).2
  have hφ₀On : ContDiffOn ℝ ∞ φ₀ I := by
    intro x hx
    have hqSource : e.symm (f u, x) ∈ e.source := e.map_target hx
    let q : PlanePoint := e.symm (f u, x)
    have hqQ : q ∈ Q := by
      change q ∈ data.toOpenPartialHomeomorph.source ∩ Q at hqSource
      exact hqSource.2
    have hqV : q ∈ V := hqQ.1
    have hqTrans : fderiv ℝ f q (0, 1) ≠ 0 := hWtrans q hqQ.2
    have hfq : ContDiffAt ℝ ∞ f q := hf.contDiffAt (hV.mem_nhds hqV)
    let Aq : ℝ →L[ℝ] ℝ :=
      fderiv ℝ f q ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
    have hAqone : Aq 1 ≠ 0 := by
      simpa [Aq, ContinuousLinearMap.comp_apply] using hqTrans
    have hAqinv : Aq.IsInvertible :=
      scalarCLM_isInvertible_of_apply_one_ne_zero Aq hAqone
    let dataq :=
      (hfq.hasStrictFDerivAt (by simp)).implicitFunctionDataOfProdDomain hAqinv
    have hmapInv :
        (fderiv ℝ (fun z : PlanePoint => (f z, z.1)) q).IsInvertible := by
      have hdataInv := dataq.isInvertible_fderiv_prodFun
      change
        (fderiv ℝ (fun z : PlanePoint => (f z, z.1)) q).IsInvertible at hdataInv
      exact hdataInv
    obtain ⟨L, hL⟩ := hmapInv
    have hmapSmooth :
        ContDiffAt ℝ ∞ (fun z : PlanePoint => (f z, z.1)) q :=
      hfq.prodMk contDiffAt_fst
    have hmapDeriv :
        HasFDerivAt (fun z : PlanePoint => (f z, z.1))
          (L : PlanePoint →L[ℝ] PlanePoint) q := by
      have hderiv :=
        hmapSmooth.differentiableAt (by simp) |>.hasFDerivAt
      simpa only [hL] using hderiv
    have he_fun :
        (e : PlanePoint → PlanePoint) = fun z : PlanePoint => (f z, z.1) :=
      funext he_apply
    have heSmooth : ContDiffAt ℝ ∞ (e : PlanePoint → PlanePoint) q := by
      rw [he_fun]
      exact hmapSmooth
    have heDeriv :
        HasFDerivAt (e : PlanePoint → PlanePoint)
          (L : PlanePoint →L[ℝ] PlanePoint) q := by
      rw [he_fun]
      exact hmapDeriv
    have heSymm :
        ContDiffAt ℝ ∞ (e.symm : PlanePoint → PlanePoint) (f u, x) := by
      simpa only [q] using e.contDiffAt_symm hx heDeriv heSmooth
    have hline :
        ContDiffAt ℝ ∞ (fun y : ℝ => ((f u, y) : PlanePoint)) x :=
      contDiffAt_const.prodMk contDiffAt_id
    exact (heSymm.comp x hline).snd.contDiffWithinAt
  obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.mp hIopen u.1 huI
  let bump : ContDiffBump u.1 :=
    ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbumpSupport : tsupport (bump : ℝ → ℝ) ⊆ I := by
    rw [bump.tsupport_eq]
    intro x hx
    apply hrI
    rw [Metric.mem_ball, Real.dist_eq]
    have hx' : |x - u.1| ≤ r / 2 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, bump] using hx
    linarith
  let φ : ℝ → ℝ := fun x => u.2 + bump x * (φ₀ x - u.2)
  have hlocalProduct : ContDiff ℝ ∞
      (fun x => bump x * (φ₀ x - u.2)) := by
    rw [← contMDiff_iff_contDiff]
    apply contMDiff_of_tsupport
    intro x hx
    have hxbump : x ∈ tsupport (bump : ℝ → ℝ) :=
      tsupport_mul_subset_left hx
    have hxI : x ∈ I := hbumpSupport hxbump
    rw [contMDiffAt_iff_contDiffAt]
    exact bump.contDiff.contDiffAt.mul <|
      (hφ₀On.contDiffAt (hIopen.mem_nhds hxI)).sub contDiffAt_const
  have hφ : ContDiff ℝ ∞ φ := by
    exact contDiff_const.add hlocalProduct
  have hφeq :
      ∀ᶠ x in 𝓝 u.1, φ x = φ₀ x := by
    filter_upwards [Metric.closedBall_mem_nhds u.1
      (show 0 < r / 4 by positivity)] with x hx
    have hbumpOne : bump x = 1 := by
      apply bump.one_of_mem_closedBall
      simpa only [bump] using hx
    simp only [φ, hbumpOne, one_mul]
    ring
  have hlocalZero :
      ∀ᶠ q in 𝓝 u, f q = f u ↔ φ₀ q.1 = q.2 := by
    have hsource : e.source ∈ 𝓝 u :=
      e.open_source.mem_nhds huSource
    have hcoord : Prod.fst ⁻¹' I ∈ 𝓝 u :=
      continuousAt_fst (hIopen.mem_nhds huI)
    filter_upwards [hsource, hcoord] with q hqSource hqI
    constructor
    · intro hq
      have heq : e q = (f u, q.1) := by
        rw [he_apply, hq]
      have hinv := e.left_inv hqSource
      rw [heq] at hinv
      exact congrArg Prod.snd hinv
    · intro hq
      have hyTarget : (f u, q.1) ∈ e.target := hqI
      have hright := e.right_inv hyTarget
      have hfirst :
          (e.symm (f u, q.1)).1 = q.1 := by
        have := congrArg Prod.snd hright
        simpa only [he_apply] using this
      have hpoint : e.symm (f u, q.1) = q := by
        apply Prod.ext
        · exact hfirst
        · exact hq
      have := congrArg Prod.fst hright
      rw [hpoint] at this
      simpa only [he_apply] using this
  have hφGraph :
      ∀ᶠ q in 𝓝 u, φ q.1 = φ₀ q.1 :=
    continuousAt_fst.tendsto.eventually hφeq
  refine ⟨φ, hφ, ?_, ?_⟩
  · rw [hφeq.self_of_nhds]
    have hsourcePoint := e.left_inv huSource
    have heq : e u = (f u, u.1) := he_apply u
    rw [heq] at hsourcePoint
    exact congrArg Prod.snd hsourcePoint
  · filter_upwards [hlocalZero, hφGraph] with q hq hgraph
    rw [hgraph]
    exact hq

/-- A vertically regular boundary point has a global `C∞` graph representative
for its local zero set; the defining function retains the exact occupied
negative side. -/
theorem local_oriented_smooth_graph_of_vertical_regular
    {U K : Set PlanePoint} {x : ℝ}
    (h : IsVerticalRegularBoundaryValue U K x)
    {p : PlanePoint} (hp : p ∈ frontier U ∩ K ∩ verticalLine x) :
    ∃ (g : PlanePoint → ℝ) (φ : ℝ → ℝ),
      ContDiffAt ℝ ∞ g p ∧ fderiv ℝ g p (0, 1) ≠ 0 ∧
      ContDiff ℝ ∞ φ ∧ φ p.1 = p.2 ∧
      ∀ᶠ q in 𝓝 p,
        (q ∈ U ↔ g q < 0) ∧ (g q = 0 ↔ φ q.1 = q.2) := by
  rcases h p hp with
    ⟨V, g, D, hV, hpV, hg, hgp, hD, _hDne, hDy, hUV⟩
  have hgat : ContDiffAt ℝ ∞ g p := hg.contDiffAt (hV.mem_nhds hpV)
  have htrans : fderiv ℝ g p (0, 1) ≠ 0 := by
    simpa only [hD.fderiv] using hDy
  obtain ⟨φ, hφ, hφp, hzero⟩ :=
    exists_contDiff_infty_implicitGraph_of_contDiffOn hV hpV hg htrans
  refine ⟨g, φ, hgat, htrans, hφ, hφp, ?_⟩
  filter_upwards [hV.mem_nhds hpV, hzero] with q hqV hqzero
  constructor
  · simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, hqV,
      and_true, true_and] using Set.ext_iff.mp hUV q
  · simpa only [hgp] using hqzero

/-- A horizontally regular boundary point has a global `C∞` graph
representative after exchanging the coordinate roles. -/
theorem local_oriented_smooth_graph_of_horizontal_regular
    {U K : Set PlanePoint} {y : ℝ}
    (h : IsHorizontalRegularBoundaryValue U K y)
    {p : PlanePoint} (hp : p ∈ frontier U ∩ K ∩ horizontalLine y) :
    ∃ (g : PlanePoint → ℝ) (φ : ℝ → ℝ),
      ContDiffAt ℝ ∞ g p ∧ fderiv ℝ g p (1, 0) ≠ 0 ∧
      ContDiff ℝ ∞ φ ∧ φ p.2 = p.1 ∧
      ∀ᶠ q in 𝓝 p,
        (q ∈ U ↔ g q < 0) ∧ (g q = 0 ↔ φ q.2 = q.1) := by
  rcases h p hp with
    ⟨V, g, D, hV, hpV, hg, hgp, hD, _hDne, hDx, hUV⟩
  have hgat : ContDiffAt ℝ ∞ g p := hg.contDiffAt (hV.mem_nhds hpV)
  have htrans : fderiv ℝ g p (1, 0) ≠ 0 := by
    simpa only [hD.fderiv] using hDx
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  let u : PlanePoint := (p.2, p.1)
  let Vs : Set PlanePoint := e ⁻¹' V
  let gs : PlanePoint → ℝ := g ∘ e
  have hVsOpen : IsOpen Vs := hV.preimage e.continuous
  have huVs : u ∈ Vs := by
    change e u ∈ V
    simpa [e, u] using hpV
  have hgsOn : ContDiffOn ℝ ∞ gs Vs := by
    exact hg.comp e.contDiff.contDiffOn (fun _ hq => hq)
  have hgsderiv :
      HasFDerivAt gs (D ∘L (e : PlanePoint →L[ℝ] PlanePoint)) u := by
    simpa [gs, e, u] using hD.comp u e.hasFDerivAt
  have hgsTrans : fderiv ℝ gs u (0, 1) ≠ 0 := by
    simpa [hgsderiv.fderiv, e, u,
      ContinuousLinearMap.comp_apply] using hDx
  obtain ⟨φ, hφ, hφu, hzeroSwap⟩ :=
    exists_contDiff_infty_implicitGraph_of_contDiffOn
      hVsOpen huVs hgsOn hgsTrans
  have hzero :
      ∀ᶠ q in 𝓝 p, g q = g p ↔ φ q.2 = q.1 := by
    have hs := e.continuousAt.tendsto.eventually hzeroSwap
    simpa [gs, e, u] using hs
  refine ⟨g, φ, hgat, htrans, hφ, by simpa only [u] using hφu, ?_⟩
  filter_upwards [hV.mem_nhds hpV, hzero] with q hqV hqzero
  constructor
  · simpa only [Set.mem_inter_iff, Set.mem_ofPred_eq, hqV,
      and_true, true_and] using Set.ext_iff.mp hUV q
  · simpa only [hgp] using hqzero

/-- Local certificate that a vertical line meets a boundary transversely. -/
def IsVerticalTransverseCut
    (U K : Set PlanePoint) (x : ℝ) : Prop :=
  ∀ p ∈ frontier U ∩ K ∩ verticalLine x,
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ) (g' : ℝ),
      IsOpen V ∧ p ∈ V ∧
      (∀ q ∈ frontier U ∩ V, g q = 0) ∧
      HasDerivAt (fun y : ℝ => g (x, y)) g' p.2 ∧ g' ≠ 0

/-- Local certificate that a horizontal line meets a boundary transversely. -/
def IsHorizontalTransverseCut
    (U K : Set PlanePoint) (y : ℝ) : Prop :=
  ∀ p ∈ frontier U ∩ K ∩ horizontalLine y,
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ) (g' : ℝ),
      IsOpen V ∧ p ∈ V ∧
      (∀ q ∈ frontier U ∩ V, g q = 0) ∧
      HasDerivAt (fun x : ℝ => g (x, y)) g' p.1 ∧ g' ≠ 0

/-- A regular defining-function certificate supplies the local vertical
transversality predicate used by finite-junction cutting. -/
theorem IsVerticalRegularBoundaryValue.isVerticalTransverseCut
    {U K : Set PlanePoint} {x : ℝ}
    (h : IsVerticalRegularBoundaryValue U K x) :
    IsVerticalTransverseCut U K x := by
  intro p hp
  rcases h p hp with
    ⟨V, g, D, hV, hpV, hg, _hgp, hderiv, _hD, hvertical, hlocal⟩
  have hslice : HasDerivAt (fun y : ℝ => g (x, y)) (D (0, 1)) p.2 := by
    have hpath : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) p.2 := by
      convert (hasDerivAt_const p.2 x).prodMk (hasDerivAt_id p.2) using 1
      all_goals simp
    have hpx : p.1 = x := hp.2
    have hpEq : p = (x, p.2) := Prod.ext hpx rfl
    rw [hpEq] at hderiv
    exact hderiv.comp_hasDerivAt p.2 hpath
  refine ⟨V, g, D (0, 1), hV, hpV, ?_, hslice, hvertical⟩
  intro q hq
  have hlocal' : U ∩ V = {z | g z < 0} ∩ V := by
    rw [hlocal, inter_comm]
  have hfrontier :
      frontier U ∩ V = frontier {z | g z < 0} ∩ V :=
    frontier_inter_eq_of_inter_open_eq hV hlocal'
  have hqfront : q ∈ frontier {z | g z < 0} := by
    have hq' : q ∈ frontier {z | g z < 0} ∩ V := by
      rw [← hfrontier]
      exact hq
    exact hq'.1
  have hgq : ContinuousAt g q :=
    (hg.continuousOn q hq.2).continuousAt (hV.mem_nhds hq.2)
  exact eq_zero_of_mem_frontier_lt_of_continuousAt hgq hqfront

/-- A regular defining-function certificate supplies the local horizontal
transversality predicate used by finite-junction cutting. -/
theorem IsHorizontalRegularBoundaryValue.isHorizontalTransverseCut
    {U K : Set PlanePoint} {y : ℝ}
    (h : IsHorizontalRegularBoundaryValue U K y) :
    IsHorizontalTransverseCut U K y := by
  intro p hp
  rcases h p hp with
    ⟨V, g, D, hV, hpV, hg, _hgp, hderiv, _hD, hhorizontal, hlocal⟩
  have hslice : HasDerivAt (fun x : ℝ => g (x, y)) (D (1, 0)) p.1 := by
    have hpath : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) p.1 := by
      convert (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 y) using 1
      all_goals simp
    have hpy : p.2 = y := hp.2
    have hpEq : p = (p.1, y) := Prod.ext rfl hpy
    rw [hpEq] at hderiv
    exact hderiv.comp_hasDerivAt p.1 hpath
  refine ⟨V, g, D (1, 0), hV, hpV, ?_, hslice, hhorizontal⟩
  intro q hq
  have hlocal' : U ∩ V = {z | g z < 0} ∩ V := by
    rw [hlocal, inter_comm]
  have hfrontier :
      frontier U ∩ V = frontier {z | g z < 0} ∩ V :=
    frontier_inter_eq_of_inter_open_eq hV hlocal'
  have hqfront : q ∈ frontier {z | g z < 0} := by
    have hq' : q ∈ frontier {z | g z < 0} ∩ V := by
      rw [← hfrontier]
      exact hq
    exact hq'.1
  have hgq : ContinuousAt g q :=
    (hg.continuousOn q hq.2).continuousAt (hV.mem_nhds hq.2)
  exact eq_zero_of_mem_frontier_lt_of_continuousAt hgq hqfront

/-- A transverse vertical cut has only finitely many boundary crossings in a
compact localization window. -/
theorem finite_frontier_inter_compact_verticalLine_of_transverse
    {U K : Set PlanePoint} {x : ℝ} (hK : IsCompact K)
    (htrans : IsVerticalTransverseCut U K x) :
    (frontier U ∩ K ∩ verticalLine x).Finite := by
  let S : Set PlanePoint := frontier U ∩ K ∩ verticalLine x
  have hScompact : IsCompact S := by
    exact (hK.inter_left isClosed_frontier).inter_right
      (isClosed_singleton.preimage continuous_fst)
  apply hScompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  rcases htrans p hp with
    ⟨V, g, g', hV, hpV, hzero, hderiv, hg'⟩
  have hevent : ∀ᶠ z in 𝓝[≠] p.2, g (x, z) ≠ 0 :=
    hderiv.eventually_ne hg'
  rw [eventually_nhdsWithin_iff] at hevent
  rcases mem_nhds_iff.mp hevent with ⟨J, hJ, hJopen, hpJ⟩
  let O : Set PlanePoint := V ∩ Prod.snd ⁻¹' J
  have hOopen : IsOpen O := hV.inter (hJopen.preimage continuous_snd)
  refine ⟨O, hOopen, ?_⟩
  ext q
  constructor
  · rintro ⟨hqO, hqS⟩
    by_cases hqp : q = p
    · exact hqp
    have hqx : q.1 = x := hqS.2
    have hpx : p.1 = x := hp.2
    have hqy : q.2 ≠ p.2 := by
      intro hqy
      apply hqp
      exact Prod.ext (hqx.trans hp.2.symm) hqy
    have hqzero : g q = 0 := hzero q ⟨hqS.1.1, hqO.1⟩
    have hqne : g (x, q.2) ≠ 0 := hJ hqO.2 hqy
    apply False.elim
    apply hqne
    rw [← hqx]
    exact hqzero
  · rintro rfl
    exact ⟨⟨hpV, hpJ⟩, hp⟩

/-- A transverse horizontal cut has only finitely many boundary crossings in a
compact localization window. -/
theorem finite_frontier_inter_compact_horizontalLine_of_transverse
    {U K : Set PlanePoint} {y : ℝ} (hK : IsCompact K)
    (htrans : IsHorizontalTransverseCut U K y) :
    (frontier U ∩ K ∩ horizontalLine y).Finite := by
  let S : Set PlanePoint := frontier U ∩ K ∩ horizontalLine y
  have hScompact : IsCompact S := by
    exact (hK.inter_left isClosed_frontier).inter_right
      (isClosed_singleton.preimage continuous_snd)
  apply hScompact.finite
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  rcases htrans p hp with
    ⟨V, g, g', hV, hpV, hzero, hderiv, hg'⟩
  have hevent : ∀ᶠ z in 𝓝[≠] p.1, g (z, y) ≠ 0 :=
    hderiv.eventually_ne hg'
  rw [eventually_nhdsWithin_iff] at hevent
  rcases mem_nhds_iff.mp hevent with ⟨J, hJ, hJopen, hpJ⟩
  let O : Set PlanePoint := V ∩ Prod.fst ⁻¹' J
  have hOopen : IsOpen O := hV.inter (hJopen.preimage continuous_fst)
  refine ⟨O, hOopen, ?_⟩
  ext q
  constructor
  · rintro ⟨hqO, hqS⟩
    by_cases hqp : q = p
    · exact hqp
    have hqy : q.2 = y := hqS.2
    have hpy : p.2 = y := hp.2
    have hqx : q.1 ≠ p.1 := by
      intro hqx
      apply hqp
      exact Prod.ext hqx (hqy.trans hpy.symm)
    have hqzero : g q = 0 := hzero q ⟨hqS.1.1, hqO.1⟩
    have hqne : g (q.1, y) ≠ 0 := hJ hqO.2 hqx
    apply False.elim
    apply hqne
    rw [← hqy]
    exact hqzero
  · rintro rfl
    exact ⟨⟨hpV, hpJ⟩, hp⟩

end CMVRelaxation

namespace CMVRelaxation

/-- Exceptional vertical coordinates where the compact boundary fiber is not
finite. -/
def badVerticalCuts (U K : Set PlanePoint) : Set ℝ :=
  {x | ¬(frontier U ∩ K ∩ verticalLine x).Finite}

/-- Exceptional horizontal coordinates where the compact boundary fiber is
not finite. -/
def badHorizontalCuts (U K : Set PlanePoint) : Set ℝ :=
  {y | ¬(frontier U ∩ K ∩ horizontalLine y).Finite}

/-- A low-mismatch vertical cut can simultaneously avoid both positive
frontier fibers and every nonfinite compact boundary fiber once the latter
exceptional coordinates are known to be null. -/
theorem exists_verticalSliceVolume_le_average_frontier_null_finite
    (U G K S : Set PlanePoint) (hK : MeasurableSet K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    (hbadU : volume (badVerticalCuts U K) = 0)
    (hbadG : volume (badVerticalCuts G K) = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b,
      FrontierMeasure U (verticalLine x ∩ K) = 0 ∧
      FrontierMeasure G (verticalLine x ∩ K) = 0 ∧
      (frontier U ∩ K ∩ verticalLine x).Finite ∧
      (frontier G ∩ K ∩ verticalLine x).Finite ∧
      verticalSliceVolume S x ≤ volume S / ENNReal.ofReal (b - a) := by
  let BU : Set ℝ :=
    {x | 0 < FrontierMeasure U (verticalLine x ∩ K)}
  let BG : Set ℝ :=
    {x | 0 < FrontierMeasure G (verticalLine x ∩ K)}
  have hBU : BU.Countable :=
    countable_pos_frontierMeasure_verticalLine_inter U K hK hfiniteU
  have hBG : BG.Countable :=
    countable_pos_frontierMeasure_verticalLine_inter G K hK hfiniteG
  let B : Set ℝ := badVerticalCuts U K ∪ badVerticalCuts G K ∪ BU ∪ BG
  have hB : volume B = 0 := by
    exact measure_union_null
      (measure_union_null
        (measure_union_null hbadU hbadG) (hBU.measure_zero volume))
      (hBG.measure_zero volume)
  obtain ⟨x, hx, hxgood, hxbound⟩ :=
    exists_verticalSliceVolume_le_average_avoiding_null hS B hB hab
  have hxBU : x ∉ BU := fun hxBU => hxgood (by
    exact Or.inl (Or.inr hxBU))
  have hxBG : x ∉ BG := fun hxBG => hxgood (Or.inr hxBG)
  have hxBadU : x ∉ badVerticalCuts U K := fun hxBadU => hxgood (by
    exact Or.inl (Or.inl (Or.inl hxBadU)))
  have hxBadG : x ∉ badVerticalCuts G K := fun hxBadG => hxgood (by
    exact Or.inl (Or.inl (Or.inr hxBadG)))
  refine ⟨x, hx, ?_, ?_, ?_, ?_, hxbound⟩
  · apply bot_unique
    rw [← not_lt]
    exact hxBU
  · apply bot_unique
    rw [← not_lt]
    exact hxBG
  · simpa only [badVerticalCuts, mem_ofPred_eq, not_not] using hxBadU
  · simpa only [badVerticalCuts, mem_ofPred_eq, not_not] using hxBadG

/-- Horizontal analogue of
`exists_verticalSliceVolume_le_average_frontier_null_finite`. -/
theorem exists_horizontalSliceVolume_le_average_frontier_null_finite
    (U G K S : Set PlanePoint) (hK : MeasurableSet K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    (hbadU : volume (badHorizontalCuts U K) = 0)
    (hbadG : volume (badHorizontalCuts G K) = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      FrontierMeasure U (horizontalLine y ∩ K) = 0 ∧
      FrontierMeasure G (horizontalLine y ∩ K) = 0 ∧
      (frontier U ∩ K ∩ horizontalLine y).Finite ∧
      (frontier G ∩ K ∩ horizontalLine y).Finite ∧
      horizontalSliceVolume S y ≤ volume S / ENNReal.ofReal (b - a) := by
  let BU : Set ℝ :=
    {y | 0 < FrontierMeasure U (horizontalLine y ∩ K)}
  let BG : Set ℝ :=
    {y | 0 < FrontierMeasure G (horizontalLine y ∩ K)}
  have hBU : BU.Countable :=
    countable_pos_frontierMeasure_horizontalLine_inter U K hK hfiniteU
  have hBG : BG.Countable :=
    countable_pos_frontierMeasure_horizontalLine_inter G K hK hfiniteG
  let B : Set ℝ := badHorizontalCuts U K ∪ badHorizontalCuts G K ∪ BU ∪ BG
  have hB : volume B = 0 := by
    exact measure_union_null
      (measure_union_null
        (measure_union_null hbadU hbadG) (hBU.measure_zero volume))
      (hBG.measure_zero volume)
  obtain ⟨y, hy, hygood, hybound⟩ :=
    exists_horizontalSliceVolume_le_average_avoiding_null hS B hB hab
  have hyBU : y ∉ BU := fun hyBU => hygood (by
    exact Or.inl (Or.inr hyBU))
  have hyBG : y ∉ BG := fun hyBG => hygood (Or.inr hyBG)
  have hyBadU : y ∉ badHorizontalCuts U K := fun hyBadU => hygood (by
    exact Or.inl (Or.inl (Or.inl hyBadU)))
  have hyBadG : y ∉ badHorizontalCuts G K := fun hyBadG => hygood (by
    exact Or.inl (Or.inl (Or.inr hyBadG)))
  refine ⟨y, hy, ?_, ?_, ?_, ?_, hybound⟩
  · apply bot_unique
    rw [← not_lt]
    exact hyBU
  · apply bot_unique
    rw [← not_lt]
    exact hyBG
  · simpa only [badHorizontalCuts, mem_ofPred_eq, not_not] using hyBadU
  · simpa only [badHorizontalCuts, mem_ofPred_eq, not_not] using hyBadG

end CMVRelaxation
namespace CMVRelaxation

/-- A low-mismatch vertical coordinate can simultaneously be chosen as a
regular value of every member of a countable family of compact `C¹` traces.
Consequently every selected compact fiber is finite.  The extra null set
allows callers to avoid positive frontier-mass coordinates in the same
selection. -/
theorem exists_verticalSliceVolume_le_average_regular_fibers_avoiding
    {ι : Type*} [Countable ι] {S : Set PlanePoint}
    (hS : MeasurableSet S) (f f' : ι → ℝ → ℝ) (K : ι → Set ℝ)
    (hK : ∀ i, IsCompact (K i))
    (hf : ∀ i, ContinuousOn (f i) (K i))
    (hdf : ∀ i x, x ∈ K i → HasDerivAt (f i) (f' i x) x)
    (B₀ : Set ℝ) (hB₀ : volume B₀ = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, y ∉ B₀ ∧
      (∀ i x, x ∈ K i → f i x = y → f' i x ≠ 0) ∧
      (∀ i, (K i ∩ f i ⁻¹' {y}).Finite) ∧
      verticalSliceVolume S y ≤
        volume S / ENNReal.ofReal (b - a) := by
  let C : ι → Set ℝ := fun i => {x | x ∈ K i ∧ f' i x = 0}
  let B : Set ℝ := B₀ ∪ ⋃ i, f i '' C i
  have hcritical : ∀ i, volume (f i '' C i) = 0 := by
    intro i
    apply volume_image_critical_eq_zero
    · intro x hx
      exact (hdf i x hx.1).hasDerivWithinAt
    · intro x hx
      exact hx.2
  have hB : volume B = 0 := by
    exact measure_union_null hB₀ (
      measure_iUnion_null hcritical)
  obtain ⟨y, hy, hyB, hybound⟩ :=
    exists_verticalSliceVolume_le_average_avoiding_null hS B hB hab
  have hyB₀ : y ∉ B₀ := fun hyB₀ => hyB (Or.inl hyB₀)
  have hyregular :
      ∀ i x, x ∈ K i → f i x = y → f' i x ≠ 0 := by
    intro i x hxK hxy hxzero
    apply hyB
    exact Or.inr (mem_iUnion.2
      ⟨i, ⟨x, ⟨hxK, hxzero⟩, hxy⟩⟩)
  refine ⟨y, hy, hyB₀, hyregular, ?_, hybound⟩
  intro i
  exact finite_compact_fiber_of_hasDerivAt_ne
    (hK i) (hf i) (hdf i) (hyregular i)

/-- Horizontal analogue of
`exists_verticalSliceVolume_le_average_regular_fibers_avoiding`. -/
theorem exists_horizontalSliceVolume_le_average_regular_fibers_avoiding
    {ι : Type*} [Countable ι] {S : Set PlanePoint}
    (hS : MeasurableSet S) (f f' : ι → ℝ → ℝ) (K : ι → Set ℝ)
    (hK : ∀ i, IsCompact (K i))
    (hf : ∀ i, ContinuousOn (f i) (K i))
    (hdf : ∀ i x, x ∈ K i → HasDerivAt (f i) (f' i x) x)
    (B₀ : Set ℝ) (hB₀ : volume B₀ = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, x ∉ B₀ ∧
      (∀ i y, y ∈ K i → f i y = x → f' i y ≠ 0) ∧
      (∀ i, (K i ∩ f i ⁻¹' {x}).Finite) ∧
      horizontalSliceVolume S x ≤
        volume S / ENNReal.ofReal (b - a) := by
  let C : ι → Set ℝ := fun i => {y | y ∈ K i ∧ f' i y = 0}
  let B : Set ℝ := B₀ ∪ ⋃ i, f i '' C i
  have hcritical : ∀ i, volume (f i '' C i) = 0 := by
    intro i
    apply volume_image_critical_eq_zero
    · intro y hy
      exact (hdf i y hy.1).hasDerivWithinAt
    · intro y hy
      exact hy.2
  have hB : volume B = 0 := by
    exact measure_union_null hB₀
      (measure_iUnion_null hcritical)
  obtain ⟨x, hx, hxB, hxbound⟩ :=
    exists_horizontalSliceVolume_le_average_avoiding_null hS B hB hab
  have hxB₀ : x ∉ B₀ := fun hxB₀ => hxB (Or.inl hxB₀)
  have hxregular :
      ∀ i y, y ∈ K i → f i y = x → f' i y ≠ 0 := by
    intro i y hyK hyx hyzero
    apply hxB
    exact Or.inr (mem_iUnion.2
      ⟨i, ⟨y, ⟨hyK, hyzero⟩, hyx⟩⟩)
  refine ⟨x, hx, hxB₀, hxregular, ?_, hxbound⟩
  intro i
  exact finite_compact_fiber_of_hasDerivAt_ne
    (hK i) (hf i) (hdf i) (hxregular i)

/-- A low-mismatch vertical cut can be selected simultaneously outside the
nonregular-value sets of both smooth inputs and outside their positive
frontier-mass fibers.  The resulting intersections with the compact window
are genuinely transverse and finite. -/
theorem exists_verticalSliceVolume_le_average_frontier_null_regular_finite
    (U G K S : Set PlanePoint) (hK : IsCompact K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    (hregularU :
      volume {x | ¬ IsVerticalRegularBoundaryValue U K x} = 0)
    (hregularG :
      volume {x | ¬ IsVerticalRegularBoundaryValue G K x} = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b,
      IsVerticalRegularBoundaryValue U K x ∧
      IsVerticalRegularBoundaryValue G K x ∧
      FrontierMeasure U (verticalLine x ∩ K) = 0 ∧
      FrontierMeasure G (verticalLine x ∩ K) = 0 ∧
      (frontier U ∩ K ∩ verticalLine x).Finite ∧
      (frontier G ∩ K ∩ verticalLine x).Finite ∧
      verticalSliceVolume S x ≤
        volume S / ENNReal.ofReal (b - a) := by
  let RU : Set ℝ := {x | ¬ IsVerticalRegularBoundaryValue U K x}
  let RG : Set ℝ := {x | ¬ IsVerticalRegularBoundaryValue G K x}
  let BU : Set ℝ :=
    {x | 0 < FrontierMeasure U (verticalLine x ∩ K)}
  let BG : Set ℝ :=
    {x | 0 < FrontierMeasure G (verticalLine x ∩ K)}
  have hBU : BU.Countable :=
    countable_pos_frontierMeasure_verticalLine_inter
      U K hK.measurableSet hfiniteU
  have hBG : BG.Countable :=
    countable_pos_frontierMeasure_verticalLine_inter
      G K hK.measurableSet hfiniteG
  let B : Set ℝ := RU ∪ RG ∪ BU ∪ BG
  have hB : volume B = 0 := by
    exact measure_union_null
      (measure_union_null
        (measure_union_null hregularU hregularG)
        (hBU.measure_zero volume))
      (hBG.measure_zero volume)
  obtain ⟨x, hx, hxgood, hxbound⟩ :=
    exists_verticalSliceVolume_le_average_avoiding_null hS B hB hab
  have hxRU : x ∉ RU := fun hxRU =>
    hxgood (Or.inl (Or.inl (Or.inl hxRU)))
  have hxRG : x ∉ RG := fun hxRG =>
    hxgood (Or.inl (Or.inl (Or.inr hxRG)))
  have hxBU : x ∉ BU := fun hxBU =>
    hxgood (Or.inl (Or.inr hxBU))
  have hxBG : x ∉ BG := fun hxBG => hxgood (Or.inr hxBG)
  have hxregularU : IsVerticalRegularBoundaryValue U K x := by
    simpa only [RU, Set.mem_ofPred_eq, not_not] using hxRU
  have hxregularG : IsVerticalRegularBoundaryValue G K x := by
    simpa only [RG, Set.mem_ofPred_eq, not_not] using hxRG
  refine ⟨x, hx, hxregularU, hxregularG, ?_, ?_, ?_, ?_, hxbound⟩
  · apply bot_unique
    rw [← not_lt]
    exact hxBU
  · apply bot_unique
    rw [← not_lt]
    exact hxBG
  · exact finite_frontier_inter_compact_verticalLine_of_transverse
      hK hxregularU.isVerticalTransverseCut
  · exact finite_frontier_inter_compact_verticalLine_of_transverse
      hK hxregularG.isVerticalTransverseCut

/-- A horizontal low-mismatch cut may simultaneously avoid an arbitrary
prescribed null set.  This is the dependency-aware selector needed after the
two vertical faces have been chosen: their finitely many boundary heights can
be excluded without changing any averaged cut estimate. -/
theorem exists_horizontalSliceVolume_le_average_frontier_null_regular_finite_avoiding
    (U G K S : Set PlanePoint) (hK : IsCompact K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    (hregularU :
      volume {y | ¬ IsHorizontalRegularBoundaryValue U K y} = 0)
    (hregularG :
      volume {y | ¬ IsHorizontalRegularBoundaryValue G K y} = 0)
    (B₀ : Set ℝ) (hB₀ : volume B₀ = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b, y ∉ B₀ ∧
      IsHorizontalRegularBoundaryValue U K y ∧
      IsHorizontalRegularBoundaryValue G K y ∧
      FrontierMeasure U (horizontalLine y ∩ K) = 0 ∧
      FrontierMeasure G (horizontalLine y ∩ K) = 0 ∧
      (frontier U ∩ K ∩ horizontalLine y).Finite ∧
      (frontier G ∩ K ∩ horizontalLine y).Finite ∧
      horizontalSliceVolume S y ≤
        volume S / ENNReal.ofReal (b - a) := by
  let RU : Set ℝ := {y | ¬ IsHorizontalRegularBoundaryValue U K y}
  let RG : Set ℝ := {y | ¬ IsHorizontalRegularBoundaryValue G K y}
  let BU : Set ℝ :=
    {y | 0 < FrontierMeasure U (horizontalLine y ∩ K)}
  let BG : Set ℝ :=
    {y | 0 < FrontierMeasure G (horizontalLine y ∩ K)}
  have hBU : BU.Countable :=
    countable_pos_frontierMeasure_horizontalLine_inter
      U K hK.measurableSet hfiniteU
  have hBG : BG.Countable :=
    countable_pos_frontierMeasure_horizontalLine_inter
      G K hK.measurableSet hfiniteG
  let B : Set ℝ := B₀ ∪ RU ∪ RG ∪ BU ∪ BG
  have hB : volume B = 0 := by
    exact measure_union_null
      (measure_union_null
        (measure_union_null
          (measure_union_null hB₀ hregularU) hregularG)
          (hBU.measure_zero volume))
        (hBG.measure_zero volume)
  obtain ⟨y, hy, hygood, hybound⟩ :=
    exists_horizontalSliceVolume_le_average_avoiding_null hS B hB hab
  have hyB₀ : y ∉ B₀ := fun hyB₀ =>
    hygood (Or.inl (Or.inl (Or.inl (Or.inl hyB₀))))
  have hyRU : y ∉ RU := fun hyRU =>
    hygood (Or.inl (Or.inl (Or.inl (Or.inr hyRU))))
  have hyRG : y ∉ RG := fun hyRG =>
    hygood (Or.inl (Or.inl (Or.inr hyRG)))
  have hyBU : y ∉ BU := fun hyBU =>
    hygood (Or.inl (Or.inr hyBU))
  have hyBG : y ∉ BG := fun hyBG => hygood (Or.inr hyBG)
  have hyregularU : IsHorizontalRegularBoundaryValue U K y := by
    simpa only [RU, Set.mem_ofPred_eq, not_not] using hyRU
  have hyregularG : IsHorizontalRegularBoundaryValue G K y := by
    simpa only [RG, Set.mem_ofPred_eq, not_not] using hyRG
  refine ⟨y, hy, hyB₀, hyregularU, hyregularG, ?_, ?_, ?_, ?_, hybound⟩
  · apply bot_unique
    rw [← not_lt]
    exact hyBU
  · apply bot_unique
    rw [← not_lt]
    exact hyBG
  · exact finite_frontier_inter_compact_horizontalLine_of_transverse
      hK hyregularU.isHorizontalTransverseCut
  · exact finite_frontier_inter_compact_horizontalLine_of_transverse
      hK hyregularG.isHorizontalTransverseCut

/-- Horizontal analogue of
`exists_verticalSliceVolume_le_average_frontier_null_regular_finite`. -/
theorem exists_horizontalSliceVolume_le_average_frontier_null_regular_finite
    (U G K S : Set PlanePoint) (hK : IsCompact K)
    (hS : MeasurableSet S)
    (hfiniteU : FrontierMeasure U K ≠ ⊤)
    (hfiniteG : FrontierMeasure G K ≠ ⊤)
    (hregularU :
      volume {y | ¬ IsHorizontalRegularBoundaryValue U K y} = 0)
    (hregularG :
      volume {y | ¬ IsHorizontalRegularBoundaryValue G K y} = 0)
    {a b : ℝ} (hab : a < b) :
    ∃ y ∈ Ioo a b,
      IsHorizontalRegularBoundaryValue U K y ∧
      IsHorizontalRegularBoundaryValue G K y ∧
      FrontierMeasure U (horizontalLine y ∩ K) = 0 ∧
      FrontierMeasure G (horizontalLine y ∩ K) = 0 ∧
      (frontier U ∩ K ∩ horizontalLine y).Finite ∧
      (frontier G ∩ K ∩ horizontalLine y).Finite ∧
      horizontalSliceVolume S y ≤
        volume S / ENNReal.ofReal (b - a) := by
  obtain ⟨y, hy, _hyAvoid, hyregularU, hyregularG, hyzeroU, hyzeroG,
      hyfiniteU, hyfiniteG, hybound⟩ :=
    exists_horizontalSliceVolume_le_average_frontier_null_regular_finite_avoiding
      U G K S hK hS hfiniteU hfiniteG hregularU hregularG
        ∅ measure_empty hab
  exact ⟨y, hy, hyregularU, hyregularG, hyzeroU, hyzeroG,
    hyfiniteU, hyfiniteG, hybound⟩


end CMVRelaxation
namespace CMVTwoPatchGraphVariation.GraphPatch

/-- Every vertical coordinate is a regular boundary value of a smooth occupied
graph side, independently of the compact localization window. -/
theorem isVerticalRegularBoundaryValue_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (K : Set PlanePoint) (x : ℝ) :
    CMVRelaxation.IsVerticalRegularBoundaryValue
      (P.occupiedGraphDomain g) K x := by
  intro p hp
  have hpgraph :
      p ∈ (fun z : ℝ => (z, g z)) '' Set.univ := by
    rw [← P.frontier_occupiedGraphDomain hg.continuous]
    exact hp.1.1
  rcases hpgraph with ⟨z, _hz, rfl⟩
  cases hside : P.side with
  | below =>
      let F : PlanePoint → ℝ := fun q => q.2 - g q.1
      let D : PlanePoint →L[ℝ] ℝ :=
        ContinuousLinearMap.snd ℝ ℝ ℝ -
          (ContinuousLinearMap.toSpanSingleton ℝ (deriv g z)).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ)
      have hgderiv : HasDerivAt g (deriv g z) z :=
        (hg.differentiable (by simp) z).hasDerivAt
      have hFderiv : HasFDerivAt F D (z, g z) := by
        change HasFDerivAt
          ((fun q : PlanePoint => q.2) - g ∘ Prod.fst) D (z, g z)
        simpa [D] using (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, g z))).sub
          (hgderiv.hasFDerivAt.comp (z, g z)
            (hasFDerivAt_fst (𝕜 := ℝ) (p := (z, g z))))
      have hDvertical : D (0, 1) ≠ 0 := by
        norm_num [D]
      have hDne : D ≠ 0 := by
        intro hD
        apply hDvertical
        simpa using congrArg
          (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hD
      refine ⟨Set.univ, F, D, isOpen_univ, Set.mem_univ _, ?_,
        by simp [F], hFderiv, hDne, hDvertical, ?_⟩
      · exact (contDiff_snd.sub (hg.comp contDiff_fst)).contDiffOn
      · ext q
        simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_true,
          Set.mem_ofPred_eq, occupiedGraphDomain, hside, F]
        constructor <;> intro h <;> linarith
  | above =>
      let F : PlanePoint → ℝ := fun q => g q.1 - q.2
      let D : PlanePoint →L[ℝ] ℝ :=
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv g z)).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ) -
          ContinuousLinearMap.snd ℝ ℝ ℝ
      have hgderiv : HasDerivAt g (deriv g z) z :=
        (hg.differentiable (by simp) z).hasDerivAt
      have hFderiv : HasFDerivAt F D (z, g z) := by
        change HasFDerivAt
          (g ∘ Prod.fst - fun q : PlanePoint => q.2) D (z, g z)
        simpa [D] using
          (hgderiv.hasFDerivAt.comp (z, g z)
            (hasFDerivAt_fst (𝕜 := ℝ) (p := (z, g z)))).sub
              (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, g z)))
      have hDvertical : D (0, 1) ≠ 0 := by
        norm_num [D]
      have hDne : D ≠ 0 := by
        intro hD
        apply hDvertical
        simpa using congrArg
          (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hD
      refine ⟨Set.univ, F, D, isOpen_univ, Set.mem_univ _, ?_,
        by simp [F], hFderiv, hDne, hDvertical, ?_⟩
      · exact ((hg.comp contDiff_fst).sub contDiff_snd).contDiffOn
      · ext q
        simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_true,
          Set.mem_ofPred_eq, occupiedGraphDomain, hside, F]
        constructor <;> intro h <;> linarith

/-- Away from critical values of the graph function, a horizontal coordinate
is a regular boundary value of either occupied side. -/
theorem isHorizontalRegularBoundaryValue_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (K : Set PlanePoint) {y : ℝ}
    (hy : y ∉ g '' {x | deriv g x = 0}) :
    CMVRelaxation.IsHorizontalRegularBoundaryValue
      (P.occupiedGraphDomain g) K y := by
  intro p hp
  have hpgraph :
      p ∈ (fun z : ℝ => (z, g z)) '' Set.univ := by
    rw [← P.frontier_occupiedGraphDomain hg.continuous]
    exact hp.1.1
  rcases hpgraph with ⟨z, _hz, rfl⟩
  have hgy : g z = y := hp.2
  have hderiv : deriv g z ≠ 0 := by
    intro hz
    exact hy ⟨z, hz, hgy⟩
  cases hside : P.side with
  | below =>
      let F : PlanePoint → ℝ := fun q => q.2 - g q.1
      let D : PlanePoint →L[ℝ] ℝ :=
        ContinuousLinearMap.snd ℝ ℝ ℝ -
          (ContinuousLinearMap.toSpanSingleton ℝ (deriv g z)).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ)
      have hgderiv : HasDerivAt g (deriv g z) z :=
        (hg.differentiable (by simp) z).hasDerivAt
      have hFderiv : HasFDerivAt F D (z, g z) := by
        change HasFDerivAt
          ((fun q : PlanePoint => q.2) - g ∘ Prod.fst) D (z, g z)
        simpa [D] using (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, g z))).sub
          (hgderiv.hasFDerivAt.comp (z, g z)
            (hasFDerivAt_fst (𝕜 := ℝ) (p := (z, g z))))
      have hDhorizontal : D (1, 0) ≠ 0 := by
        simpa [D] using neg_ne_zero.mpr hderiv
      have hDne : D ≠ 0 := by
        intro hD
        apply hDhorizontal
        simpa using congrArg
          (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hD
      refine ⟨Set.univ, F, D, isOpen_univ, Set.mem_univ _, ?_,
        by simp [F], hFderiv, hDne, hDhorizontal, ?_⟩
      · exact (contDiff_snd.sub (hg.comp contDiff_fst)).contDiffOn
      · ext q
        simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_true,
          Set.mem_ofPred_eq, occupiedGraphDomain, hside, F]
        constructor <;> intro h <;> linarith
  | above =>
      let F : PlanePoint → ℝ := fun q => g q.1 - q.2
      let D : PlanePoint →L[ℝ] ℝ :=
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv g z)).comp
            (ContinuousLinearMap.fst ℝ ℝ ℝ) -
          ContinuousLinearMap.snd ℝ ℝ ℝ
      have hgderiv : HasDerivAt g (deriv g z) z :=
        (hg.differentiable (by simp) z).hasDerivAt
      have hFderiv : HasFDerivAt F D (z, g z) := by
        change HasFDerivAt
          (g ∘ Prod.fst - fun q : PlanePoint => q.2) D (z, g z)
        simpa [D] using
          (hgderiv.hasFDerivAt.comp (z, g z)
            (hasFDerivAt_fst (𝕜 := ℝ) (p := (z, g z)))).sub
              (hasFDerivAt_snd (𝕜 := ℝ) (p := (z, g z)))
      have hDhorizontal : D (1, 0) ≠ 0 := by
        simpa [D] using hderiv
      have hDne : D ≠ 0 := by
        intro hD
        apply hDhorizontal
        simpa using congrArg
          (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hD
      refine ⟨Set.univ, F, D, isOpen_univ, Set.mem_univ _, ?_,
        by simp [F], hFderiv, hDne, hDhorizontal, ?_⟩
      · exact ((hg.comp contDiff_fst).sub contDiff_snd).contDiffOn
      · ext q
        simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_true,
          Set.mem_ofPred_eq, occupiedGraphDomain, hside, F]
        constructor <;> intro h <;> linarith

/-- Horizontal nonregular values of a smooth occupied graph side form a null
set, uniformly for every localization window. -/
theorem volume_setOf_not_isHorizontalRegularBoundaryValue_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (K : Set PlanePoint) :
    volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue
        (P.occupiedGraphDomain g) K y} = 0 := by
  let C : Set ℝ := {x | deriv g x = 0}
  have hcritical : volume (g '' C) = 0 := by
    apply CMVRelaxation.volume_image_critical_eq_zero
    · intro x _hx
      exact (hg.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt
    · intro x hx
      exact hx
  apply measure_mono_null (t := g '' C) ?_ hcritical
  intro y hy
  by_contra hyimage
  exact hy (P.isHorizontalRegularBoundaryValue_occupiedGraphDomain
    hg K hyimage)

/-- A smooth occupied graph side has no vertically nonregular coordinate. -/
theorem volume_setOf_not_isVerticalRegularBoundaryValue_occupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (K : Set PlanePoint) :
    volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue
        (P.occupiedGraphDomain g) K x} = 0 := by
  rw [show {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue
        (P.occupiedGraphDomain g) K x} = ∅ by
    ext x
    constructor
    · intro hx
      exact False.elim (hx
        (P.isVerticalRegularBoundaryValue_occupiedGraphDomain hg K x))
    · intro hx
      exact False.elim hx]
  exact measure_empty

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVRelaxation

/-- A closed rectangular cut window is compact. -/
lemma isCompact_closedCutRectangle (l r d u : ℝ) :
    IsCompact (closedCutRectangle l r d u) :=
  isCompact_Icc.prod isCompact_Icc

/-- Four compact collars yield one rectangular cut whose four faces are
simultaneously regular, transverse, finite on both input frontiers, null for
both localized frontier measures, and charged only by the averaged membership
mismatch.  The exceptional-coordinate hypotheses are stated separately for
each collar so this theorem can consume independently constructed local
boundary atlases. -/
theorem exists_closedCutRectangle_regular_finite_spliceCutTrace_le_collar_averages
    {lam : ℝ} (hlam : 1 < lam) (U G : Set PlanePoint)
    (hU : MeasurableSet U) (hG : MeasurableSet G)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU :
      FrontierMeasure U (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG :
      FrontierMeasure G (closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hregularUL : volume {x |
      ¬ IsVerticalRegularBoundaryValue U
        (closedCutRectangle a₀ a₁ c₀ d₁) x} = 0)
    (hregularGL : volume {x |
      ¬ IsVerticalRegularBoundaryValue G
        (closedCutRectangle a₀ a₁ c₀ d₁) x} = 0)
    (hregularUR : volume {x |
      ¬ IsVerticalRegularBoundaryValue U
        (closedCutRectangle b₀ b₁ c₀ d₁) x} = 0)
    (hregularGR : volume {x |
      ¬ IsVerticalRegularBoundaryValue G
        (closedCutRectangle b₀ b₁ c₀ d₁) x} = 0)
    (hregularUD : volume {y |
      ¬ IsHorizontalRegularBoundaryValue U
        (closedCutRectangle a₀ b₁ c₀ c₁) y} = 0)
    (hregularGD : volume {y |
      ¬ IsHorizontalRegularBoundaryValue G
        (closedCutRectangle a₀ b₁ c₀ c₁) y} = 0)
    (hregularUU : volume {y |
      ¬ IsHorizontalRegularBoundaryValue U
        (closedCutRectangle a₀ b₁ d₀ d₁) y} = 0)
    (hregularGU : volume {y |
      ¬ IsHorizontalRegularBoundaryValue G
        (closedCutRectangle a₀ b₁ d₀ d₁) y} = 0) :
    ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
      ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
        IsVerticalRegularBoundaryValue U
            (closedCutRectangle a₀ a₁ c₀ d₁) l ∧
        IsVerticalRegularBoundaryValue G
            (closedCutRectangle a₀ a₁ c₀ d₁) l ∧
        IsVerticalRegularBoundaryValue U
            (closedCutRectangle b₀ b₁ c₀ d₁) r ∧
        IsVerticalRegularBoundaryValue G
            (closedCutRectangle b₀ b₁ c₀ d₁) r ∧
        IsHorizontalRegularBoundaryValue U
            (closedCutRectangle a₀ b₁ c₀ c₁) d ∧
        IsHorizontalRegularBoundaryValue G
            (closedCutRectangle a₀ b₁ c₀ c₁) d ∧
        IsHorizontalRegularBoundaryValue U
            (closedCutRectangle a₀ b₁ d₀ d₁) u ∧
        IsHorizontalRegularBoundaryValue G
            (closedCutRectangle a₀ b₁ d₀ d₁) u ∧
        FrontierMeasure U
            (verticalLine l ∩ closedCutRectangle a₀ a₁ c₀ d₁) = 0 ∧
        FrontierMeasure G
            (verticalLine l ∩ closedCutRectangle a₀ a₁ c₀ d₁) = 0 ∧
        FrontierMeasure U
            (verticalLine r ∩ closedCutRectangle b₀ b₁ c₀ d₁) = 0 ∧
        FrontierMeasure G
            (verticalLine r ∩ closedCutRectangle b₀ b₁ c₀ d₁) = 0 ∧
        FrontierMeasure U
            (horizontalLine d ∩ closedCutRectangle a₀ b₁ c₀ c₁) = 0 ∧
        FrontierMeasure G
            (horizontalLine d ∩ closedCutRectangle a₀ b₁ c₀ c₁) = 0 ∧
        FrontierMeasure U
            (horizontalLine u ∩ closedCutRectangle a₀ b₁ d₀ d₁) = 0 ∧
        FrontierMeasure G
            (horizontalLine u ∩ closedCutRectangle a₀ b₁ d₀ d₁) = 0 ∧
        (frontier U ∩ closedCutRectangle a₀ a₁ c₀ d₁ ∩
            verticalLine l).Finite ∧
        (frontier G ∩ closedCutRectangle a₀ a₁ c₀ d₁ ∩
            verticalLine l).Finite ∧
        (frontier U ∩ closedCutRectangle b₀ b₁ c₀ d₁ ∩
            verticalLine r).Finite ∧
        (frontier G ∩ closedCutRectangle b₀ b₁ c₀ d₁ ∩
            verticalLine r).Finite ∧
        (frontier U ∩ closedCutRectangle a₀ b₁ c₀ c₁ ∩
            horizontalLine d).Finite ∧
        (frontier G ∩ closedCutRectangle a₀ b₁ c₀ c₁ ∩
            horizontalLine d).Finite ∧
        (frontier U ∩ closedCutRectangle a₀ b₁ d₀ d₁ ∩
            horizontalLine u).Finite ∧
        (frontier G ∩ closedCutRectangle a₀ b₁ d₀ d₁ ∩
            horizontalLine u).Finite ∧
        (∀ p ∈
            ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint),
          p ∉ frontier U ∧ p ∉ frontier G) ∧
        weightedTraceCost lam
            (spliceCutTrace U G (closedCutRectangle l r d u)) ≤
          ENNReal.ofReal lam *
              (volume (closedCutRectangle a₀ a₁ c₀ d₁ ∩ (U ∆ G)) /
                ENNReal.ofReal (a₁ - a₀)) +
            ENNReal.ofReal lam *
              (volume (closedCutRectangle b₀ b₁ c₀ d₁ ∩ (U ∆ G)) /
                ENNReal.ofReal (b₁ - b₀)) +
              ENNReal.ofReal lam *
                (volume (closedCutRectangle a₀ b₁ c₀ c₁ ∩ (U ∆ G)) /
                  ENNReal.ofReal (c₁ - c₀)) +
                ENNReal.ofReal lam *
                  (volume (closedCutRectangle a₀ b₁ d₀ d₁ ∩ (U ∆ G)) /
                    ENNReal.ofReal (d₁ - d₀)) := by
  let K := closedCutRectangle a₀ b₁ c₀ d₁
  let KL := closedCutRectangle a₀ a₁ c₀ d₁
  let KR := closedCutRectangle b₀ b₁ c₀ d₁
  let KD := closedCutRectangle a₀ b₁ c₀ c₁
  let KU := closedCutRectangle a₀ b₁ d₀ d₁
  have hKL : IsCompact KL := isCompact_closedCutRectangle _ _ _ _
  have hKR : IsCompact KR := isCompact_closedCutRectangle _ _ _ _
  have hKD : IsCompact KD := isCompact_closedCutRectangle _ _ _ _
  have hKU : IsCompact KU := isCompact_closedCutRectangle _ _ _ _
  have hKLK : KL ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨⟨hx.1, (hx.2.trans hab.le).trans hb.le⟩, hy⟩
  have hKRK : KR ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨⟨ha.le.trans (hab.le.trans hx.1), hx.2⟩, hy⟩
  have hKDK : KD ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨hx, ⟨hy.1, (hy.2.trans hcd.le).trans hd.le⟩⟩
  have hKUK : KU ⊆ K := by
    rintro p ⟨hx, hy⟩
    exact ⟨hx, ⟨hc.le.trans (hcd.le.trans hy.1), hy.2⟩⟩
  have hfinite (M : Set PlanePoint) (hMK : M ⊆ K) :
      FrontierMeasure U M ≠ ⊤ ∧ FrontierMeasure G M ≠ ⊤ := by
    constructor
    · exact ne_top_of_le_ne_top hfiniteU (measure_mono hMK)
    · exact ne_top_of_le_ne_top hfiniteG (measure_mono hMK)
  have hSL : MeasurableSet (KL ∩ (U ∆ G)) :=
    hKL.measurableSet.inter (hU.symmDiff hG)
  have hSR : MeasurableSet (KR ∩ (U ∆ G)) :=
    hKR.measurableSet.inter (hU.symmDiff hG)
  have hSD : MeasurableSet (KD ∩ (U ∆ G)) :=
    hKD.measurableSet.inter (hU.symmDiff hG)
  have hSU : MeasurableSet (KU ∩ (U ∆ G)) :=
    hKU.measurableSet.inter (hU.symmDiff hG)
  obtain ⟨l, hl, hlregU, hlregG, hlzeroU, hlzeroG,
      hlfiniteU, hlfiniteG, hlvolume⟩ :=
    exists_verticalSliceVolume_le_average_frontier_null_regular_finite
      U G KL (KL ∩ (U ∆ G)) hKL hSL
        (hfinite KL hKLK).1 (hfinite KL hKLK).2
        (by simpa only [KL] using hregularUL)
        (by simpa only [KL] using hregularGL) ha
  obtain ⟨r, hr, hrregU, hrregG, hrzeroU, hrzeroG,
      hrfiniteU, hrfiniteG, hrvolume⟩ :=
    exists_verticalSliceVolume_le_average_frontier_null_regular_finite
      U G KR (KR ∩ (U ∆ G)) hKR hSR
        (hfinite KR hKRK).1 (hfinite KR hKRK).2
        (by simpa only [KR] using hregularUR)
        (by simpa only [KR] using hregularGR) hb
  let C : Set PlanePoint :=
    ((frontier U ∩ KL ∩ verticalLine l) ∪
      (frontier G ∩ KL ∩ verticalLine l)) ∪
    ((frontier U ∩ KR ∩ verticalLine r) ∪
      (frontier G ∩ KR ∩ verticalLine r))
  have hCfinite : C.Finite := by
    simpa only [C] using
      (hlfiniteU.union hlfiniteG).union (hrfiniteU.union hrfiniteG)
  let B₀ : Set ℝ := Prod.snd '' C
  have hB₀finite : B₀.Finite := by
    exact hCfinite.image Prod.snd
  have hB₀ : volume B₀ = 0 :=
    hB₀finite.measure_zero volume
  obtain ⟨d, hdmem, hdavoid, hdregU, hdregG, hdzeroU, hdzeroG,
      hdfiniteU, hdfiniteG, hdvolume⟩ :=
    exists_horizontalSliceVolume_le_average_frontier_null_regular_finite_avoiding
      U G KD (KD ∩ (U ∆ G)) hKD hSD
        (hfinite KD hKDK).1 (hfinite KD hKDK).2
        (by simpa only [KD] using hregularUD)
        (by simpa only [KD] using hregularGD) B₀ hB₀ hc
  obtain ⟨u, humem, huavoid, huregU, huregG, huzeroU, huzeroG,
      hufiniteU, hufiniteG, huvolume⟩ :=
    exists_horizontalSliceVolume_le_average_frontier_null_regular_finite_avoiding
      U G KU (KU ∩ (U ∆ G)) hKU hSU
        (hfinite KU hKUK).1 (hfinite KU hKUK).2
        (by simpa only [KU] using hregularUU)
        (by simpa only [KU] using hregularGU) B₀ hB₀ hd
  have hdRange : d ∈ Icc c₀ d₁ :=
    ⟨hdmem.1.le, (hdmem.2.trans (hcd.trans hd)).le⟩
  have huRange : u ∈ Icc c₀ d₁ :=
    ⟨((hc.trans hcd).trans humem.1).le, humem.2.le⟩
  have hleftBad {y : ℝ} (hy : y ∈ Icc c₀ d₁)
      (hfront : (l, y) ∈ frontier U ∪ frontier G) : y ∈ B₀ := by
    change y ∈ Prod.snd '' C
    refine ⟨(l, y), ?_, rfl⟩
    have hpKL : (l, y) ∈ KL := by
      change l ∈ Icc a₀ a₁ ∧ y ∈ Icc c₀ d₁
      exact ⟨⟨hl.1.le, hl.2.le⟩, hy⟩
    rcases hfront with hfront | hfront
    · exact Or.inl (Or.inl ⟨⟨hfront, hpKL⟩, rfl⟩)
    · exact Or.inl (Or.inr ⟨⟨hfront, hpKL⟩, rfl⟩)
  have hrightBad {y : ℝ} (hy : y ∈ Icc c₀ d₁)
      (hfront : (r, y) ∈ frontier U ∪ frontier G) : y ∈ B₀ := by
    change y ∈ Prod.snd '' C
    refine ⟨(r, y), ?_, rfl⟩
    have hpKR : (r, y) ∈ KR := by
      change r ∈ Icc b₀ b₁ ∧ y ∈ Icc c₀ d₁
      exact ⟨⟨hr.1.le, hr.2.le⟩, hy⟩
    rcases hfront with hfront | hfront
    · exact Or.inr (Or.inl ⟨⟨hfront, hpKR⟩, rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨hfront, hpKR⟩, rfl⟩)
  have hcornerAvoid :
      ∀ p ∈ ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint),
        p ∉ frontier U ∧ p ∉ frontier G := by
    intro p hp
    simp only [mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · constructor
      · intro hp
        exact hdavoid (hleftBad hdRange (Or.inl hp))
      · intro hp
        exact hdavoid (hleftBad hdRange (Or.inr hp))
    · constructor
      · intro hp
        exact huavoid (hleftBad huRange (Or.inl hp))
      · intro hp
        exact huavoid (hleftBad huRange (Or.inr hp))
    · constructor
      · intro hp
        exact hdavoid (hrightBad hdRange (Or.inl hp))
      · intro hp
        exact hdavoid (hrightBad hdRange (Or.inr hp))
    · constructor
      · intro hp
        exact huavoid (hrightBad huRange (Or.inl hp))
      · intro hp
        exact huavoid (hrightBad huRange (Or.inr hp))
  have hlcost :
      weightedTraceCost lam
          ((verticalLine l ∩ KL) ∩
            (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
        ENNReal.ofReal lam *
          (volume (KL ∩ (U ∆ G)) / ENNReal.ofReal (a₁ - a₀)) :=
    (weightedTraceCost_verticalCutInputsOn_le_of_frontier_null
      hlam U G KL l hKL.measurableSet hlzeroU hlzeroG).trans
        (by simpa only [mul_comm] using
          mul_le_mul_left hlvolume (ENNReal.ofReal lam))
  have hrcost :
      weightedTraceCost lam
          ((verticalLine r ∩ KR) ∩
            (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
        ENNReal.ofReal lam *
          (volume (KR ∩ (U ∆ G)) / ENNReal.ofReal (b₁ - b₀)) :=
    (weightedTraceCost_verticalCutInputsOn_le_of_frontier_null
      hlam U G KR r hKR.measurableSet hrzeroU hrzeroG).trans
        (by simpa only [mul_comm] using
          mul_le_mul_left hrvolume (ENNReal.ofReal lam))
  have hdcost :
      weightedTraceCost lam
          ((horizontalLine d ∩ KD) ∩
            (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
        ENNReal.ofReal lam *
          (volume (KD ∩ (U ∆ G)) / ENNReal.ofReal (c₁ - c₀)) :=
    (weightedTraceCost_horizontalCutInputsOn_le_of_frontier_null
      hlam U G KD d hKD.measurableSet hdzeroU hdzeroG).trans
        (by simpa only [mul_comm] using
          mul_le_mul_left hdvolume (ENNReal.ofReal lam))
  have hucost :
      weightedTraceCost lam
          ((horizontalLine u ∩ KU) ∩
            (frontier U ∪ frontier G ∪ (U ∆ G))) ≤
        ENNReal.ofReal lam *
          (volume (KU ∩ (U ∆ G)) / ENNReal.ofReal (d₁ - d₀)) :=
    (weightedTraceCost_horizontalCutInputsOn_le_of_frontier_null
      hlam U G KU u hKU.measurableSet huzeroU huzeroG).trans
        (by simpa only [mul_comm] using
          mul_le_mul_left huvolume (ENNReal.ofReal lam))
  refine ⟨l, hl, r, hr, d, hdmem, u, humem,
    hlregU, hlregG, hrregU, hrregG, hdregU, hdregG, huregU, huregG,
    hlzeroU, hlzeroG, hrzeroU, hrzeroG,
    hdzeroU, hdzeroG, huzeroU, huzeroG,
    hlfiniteU, hlfiniteG, hrfiniteU, hrfiniteG,
    hdfiniteU, hdfiniteG, hufiniteU, hufiniteG, hcornerAvoid, ?_⟩
  have hlr : l < r := hl.2.trans (hab.trans hr.1)
  have hdu : d < u := hdmem.2.trans (hcd.trans humem.1)
  let T := frontier U ∪ frontier G ∪ (U ∆ G)
  have hsubset :
      spliceCutTrace U G (closedCutRectangle l r d u) ⊆
        (((verticalLine l ∩ KL) ∩ T) ∪
          ((verticalLine r ∩ KR) ∩ T)) ∪
            ((horizontalLine d ∩ KD) ∩ T) ∪
              ((horizontalLine u ∩ KU) ∩ T) := by
    intro p hp
    rcases hp with ⟨hpBoundary, hpT⟩
    have hpWindow : p ∈ closedCutRectangle l r d u :=
      ((isClosed_Icc.prod isClosed_Icc).frontier_subset hpBoundary)
    have hlines :=
      frontier_closedCutRectangle_subset_lines hlr hdu hpBoundary
    rcases hlines with ((hpL | hpR) | hpD) | hpU
    · have hpKL : p ∈ KL := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.1 = l at hpL
        exact ⟨⟨by linarith [hl.1], by linarith [hl.2]⟩,
          ⟨by linarith [hdmem.1], by linarith [humem.2]⟩⟩
      exact Or.inl (Or.inl (Or.inl ⟨⟨hpL, hpKL⟩, hpT⟩))
    · have hpKR : p ∈ KR := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.1 = r at hpR
        exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩,
          ⟨by linarith [hdmem.1], by linarith [humem.2]⟩⟩
      exact Or.inl (Or.inl (Or.inr ⟨⟨hpR, hpKR⟩, hpT⟩))
    · have hpKD : p ∈ KD := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.2 = d at hpD
        exact ⟨⟨by linarith [hl.1], by linarith [hr.2]⟩,
          ⟨by linarith [hdmem.1], by linarith [hdmem.2]⟩⟩
      exact Or.inl (Or.inr ⟨⟨hpD, hpKD⟩, hpT⟩)
    · have hpKU : p ∈ KU := by
        rcases hpWindow with ⟨hpx, hpy⟩
        rcases hpx with ⟨hpxl, hpxr⟩
        rcases hpy with ⟨hpyd, hpyu⟩
        change p.2 = u at hpU
        exact ⟨⟨by linarith [hl.1], by linarith [hr.2]⟩,
          ⟨by linarith [humem.1], by linarith [humem.2]⟩⟩
      exact Or.inr ⟨⟨hpU, hpKU⟩, hpT⟩
  calc
    weightedTraceCost lam
        (spliceCutTrace U G (closedCutRectangle l r d u)) ≤
      weightedTraceCost lam ((verticalLine l ∩ KL) ∩ T) +
        weightedTraceCost lam ((verticalLine r ∩ KR) ∩ T) +
          weightedTraceCost lam ((horizontalLine d ∩ KD) ∩ T) +
            weightedTraceCost lam ((horizontalLine u ∩ KU) ∩ T) :=
      (weightedTraceCost_mono lam hsubset).trans
        (weightedTraceCost_iUnion_four_le lam _ _ _ _)
    _ ≤ _ := by
      simpa only [KL, KR, KD, KU] using
        add_le_add (add_le_add (add_le_add hlcost hrcost) hdcost) hucost


/-- A selected vertical splice face has regular local defining functions,
zero localized frontier mass, and finitely many crossings for both inputs. -/
def IsRegularFiniteVerticalSpliceCut
    (U G K : Set PlanePoint) (x : ℝ) : Prop :=
  IsVerticalRegularBoundaryValue U K x ∧
  IsVerticalRegularBoundaryValue G K x ∧
  FrontierMeasure U (verticalLine x ∩ K) = 0 ∧
  FrontierMeasure G (verticalLine x ∩ K) = 0 ∧
  (frontier U ∩ K ∩ verticalLine x).Finite ∧
  (frontier G ∩ K ∩ verticalLine x).Finite

/-- Horizontal analogue of `IsRegularFiniteVerticalSpliceCut`. -/
def IsRegularFiniteHorizontalSpliceCut
    (U G K : Set PlanePoint) (y : ℝ) : Prop :=
  IsHorizontalRegularBoundaryValue U K y ∧
  IsHorizontalRegularBoundaryValue G K y ∧
  FrontierMeasure U (horizontalLine y ∩ K) = 0 ∧
  FrontierMeasure G (horizontalLine y ∩ K) = 0 ∧
  (frontier U ∩ K ∩ horizontalLine y).Finite ∧
  (frontier G ∩ K ∩ horizontalLine y).Finite

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

/-- The smooth occupied graph discharges its own four exceptional-coordinate
sets.  Thus an arbitrary old approximant needs only its four coordinate-nullity
certificates to obtain actual regular finite splice faces and the sharp
four-collar mismatch budget. -/
theorem exists_regularFinite_closedCutRectangle_spliceCutTrace_le_collar_averages_against
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (U : Set PlanePoint) (hU : MeasurableSet U)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU : FrontierMeasure U
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : FrontierMeasure (P.occupiedGraphDomain g)
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hregUL : volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue U
        (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) x} = 0)
    (hregUR : volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue U
        (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) x} = 0)
    (hregUD : volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue U
        (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) y} = 0)
    (hregUU : volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue U
        (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) y} = 0) :
    ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
      ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
        CMVRelaxation.IsRegularFiniteVerticalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) l ∧
        CMVRelaxation.IsRegularFiniteVerticalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) r ∧
        CMVRelaxation.IsRegularFiniteHorizontalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) d ∧
        CMVRelaxation.IsRegularFiniteHorizontalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) u ∧
        (∀ p ∈
            ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint),
          p ∉ frontier U ∧
            p ∉ frontier (P.occupiedGraphDomain g)) ∧
        CMVRelaxation.weightedTraceCost lam
            (CMVRelaxation.spliceCutTrace U (P.occupiedGraphDomain g)
              (CMVRelaxation.closedCutRectangle l r d u)) ≤
          ENNReal.ofReal lam *
              (volume (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁ ∩
                  (U ∆ P.occupiedGraphDomain g)) /
                ENNReal.ofReal (a₁ - a₀)) +
            ENNReal.ofReal lam *
              (volume (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁ ∩
                  (U ∆ P.occupiedGraphDomain g)) /
                ENNReal.ofReal (b₁ - b₀)) +
              ENNReal.ofReal lam *
                (volume (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁ ∩
                    (U ∆ P.occupiedGraphDomain g)) /
                  ENNReal.ofReal (c₁ - c₀)) +
                ENNReal.ofReal lam *
                  (volume (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁ ∩
                      (U ∆ P.occupiedGraphDomain g)) /
                    ENNReal.ofReal (d₁ - d₀)) := by
  let G := P.occupiedGraphDomain g
  have hG : MeasurableSet G :=
    (P.isOpen_occupiedGraphDomain hg.continuous).measurableSet
  have hregGL : volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue G
        (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) x} = 0 := by
    exact P.volume_setOf_not_isVerticalRegularBoundaryValue_occupiedGraphDomain
      hg _
  have hregGR : volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue G
        (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) x} = 0 := by
    exact P.volume_setOf_not_isVerticalRegularBoundaryValue_occupiedGraphDomain
      hg _
  have hregGD : volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue G
        (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) y} = 0 := by
    exact P.volume_setOf_not_isHorizontalRegularBoundaryValue_occupiedGraphDomain
      hg _
  have hregGU : volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue G
        (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) y} = 0 := by
    exact P.volume_setOf_not_isHorizontalRegularBoundaryValue_occupiedGraphDomain
      hg _
  rcases CMVRelaxation.exists_closedCutRectangle_regular_finite_spliceCutTrace_le_collar_averages
      hlam U G hU hG ha hab hb hc hcd hd hfiniteU hfiniteG
        hregUL hregGL hregUR hregGR hregUD hregGD hregUU hregGU with
    ⟨l, hl, r, hr, d, hdmem, u, humem,
      hlregU, hlregG, hrregU, hrregG,
      hdregU, hdregG, huregU, huregG,
      hlzeroU, hlzeroG, hrzeroU, hrzeroG,
      hdzeroU, hdzeroG, huzeroU, huzeroG,
      hlfiniteU, hlfiniteG, hrfiniteU, hrfiniteG,
      hdfiniteU, hdfiniteG, hufiniteU, hufiniteG,
      hcornerAvoid, hcost⟩
  refine ⟨l, hl, r, hr, d, hdmem, u, humem,
    ?_, ?_, ?_, ?_, hcornerAvoid, ?_⟩
  · exact ⟨hlregU, hlregG, hlzeroU, hlzeroG, hlfiniteU, hlfiniteG⟩
  · exact ⟨hrregU, hrregG, hrzeroU, hrzeroG, hrfiniteU, hrfiniteG⟩
  · exact ⟨hdregU, hdregG, hdzeroU, hdzeroG, hdfiniteU, hdfiniteG⟩
  · exact ⟨huregU, huregG, huzeroU, huzeroG, hufiniteU, hufiniteG⟩
  · exact hcost


/-- Termwise regular finite four-face cuts against smooth occupied graphs can
be chosen so that their complete weighted splice trace tends to zero whenever
the four localized mismatches do. -/
theorem exists_regularFinite_closedCutRectangle_spliceCutTrace_tendsto_zero_against
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    (g : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (U : ℕ → Set PlanePoint) (hU : ∀ n, MeasurableSet (U n))
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU : ∀ n, FrontierMeasure (U n)
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : ∀ n, FrontierMeasure (P.occupiedGraphDomain (g n))
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hregUL : ∀ n, volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) x} = 0)
    (hregUR : ∀ n, volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) x} = 0)
    (hregUD : ∀ n, volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) y} = 0)
    (hregUU : ∀ n, volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) y} = 0)
    (hleft : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0))
    (hright : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0))
    (hlower : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0))
    (hupper : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0)) :
    ∃ l r d u : ℕ → ℝ,
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteVerticalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) (l n)) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteVerticalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) (r n)) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteHorizontalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) (d n)) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteHorizontalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) (u n)) ∧
      (∀ n, ∀ p ∈
          ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
            Set PlanePoint),
        p ∉ frontier (U n) ∧
          p ∉ frontier (P.occupiedGraphDomain (g n))) ∧
      Tendsto (fun n =>
        CMVRelaxation.weightedTraceCost lam
          (CMVRelaxation.spliceCutTrace (U n)
            (P.occupiedGraphDomain (g n))
            (CMVRelaxation.closedCutRectangle
              (l n) (r n) (d n) (u n)))) atTop (𝓝 0) := by
  have hselect : ∀ n,
      ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
        ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
          CMVRelaxation.IsRegularFiniteVerticalSpliceCut (U n)
              (P.occupiedGraphDomain (g n))
              (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) l ∧
          CMVRelaxation.IsRegularFiniteVerticalSpliceCut (U n)
              (P.occupiedGraphDomain (g n))
              (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) r ∧
          CMVRelaxation.IsRegularFiniteHorizontalSpliceCut (U n)
              (P.occupiedGraphDomain (g n))
              (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) d ∧
          CMVRelaxation.IsRegularFiniteHorizontalSpliceCut (U n)
              (P.occupiedGraphDomain (g n))
              (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) u ∧
          (∀ p ∈
              ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint),
            p ∉ frontier (U n) ∧
              p ∉ frontier (P.occupiedGraphDomain (g n))) ∧
          CMVRelaxation.weightedTraceCost lam
              (CMVRelaxation.spliceCutTrace (U n)
                (P.occupiedGraphDomain (g n))
                (CMVRelaxation.closedCutRectangle l r d u)) ≤
            ENNReal.ofReal lam *
                (volume (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁ ∩
                    (U n ∆ P.occupiedGraphDomain (g n))) /
                  ENNReal.ofReal (a₁ - a₀)) +
              ENNReal.ofReal lam *
                (volume (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁ ∩
                    (U n ∆ P.occupiedGraphDomain (g n))) /
                  ENNReal.ofReal (b₁ - b₀)) +
                ENNReal.ofReal lam *
                  (volume (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁ ∩
                      (U n ∆ P.occupiedGraphDomain (g n))) /
                    ENNReal.ofReal (c₁ - c₀)) +
                  ENNReal.ofReal lam *
                    (volume (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁ ∩
                        (U n ∆ P.occupiedGraphDomain (g n))) /
                      ENNReal.ofReal (d₁ - d₀)) := by
    intro n
    exact P.exists_regularFinite_closedCutRectangle_spliceCutTrace_le_collar_averages_against
      hlam (hg n) (U n) (hU n) ha hab hb hc hcd hd
        (hfiniteU n) (hfiniteG n)
        (hregUL n) (hregUR n) (hregUD n) (hregUU n)
  choose l hl r hr d hdmem u humem
    hlregular hrregular hdregular huregular hcornerAvoid hcost using hselect
  refine ⟨l, r, d, u, hl, hr, hdmem, humem,
    hlregular, hrregular, hdregular, huregular, hcornerAvoid, ?_⟩
  have tendsto_div : ∀ {f : ℕ → ENNReal} {w : ℝ},
      0 < w → Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => f n / ENNReal.ofReal w) atTop (𝓝 0) := by
    intro f w hw hf
    rw [show (fun n => f n / ENNReal.ofReal w) =
      fun n => (ENNReal.ofReal w)⁻¹ * f n by
        funext n
        rw [ENNReal.div_eq_inv_mul]]
    simpa using ENNReal.Tendsto.const_mul hf
      (Or.inr (ENNReal.inv_ne_top.2
        (ne_of_gt (ENNReal.ofReal_pos.2 hw))))
  have tendsto_scaled : ∀ {f : ℕ → ENNReal} {w : ℝ},
      0 < w → Tendsto f atTop (𝓝 0) →
      Tendsto (fun n => ENNReal.ofReal lam *
        (f n / ENNReal.ofReal w)) atTop (𝓝 0) := by
    intro f w hw hf
    simpa using ENNReal.Tendsto.const_mul (tendsto_div hw hf)
      (Or.inr ENNReal.ofReal_ne_top)
  have hleft' := tendsto_scaled (sub_pos.mpr ha) hleft
  have hright' := tendsto_scaled (sub_pos.mpr hb) hright
  have hlower' := tendsto_scaled (sub_pos.mpr hc) hlower
  have hupper' := tendsto_scaled (sub_pos.mpr hd) hupper
  have hbudget : Tendsto (fun n =>
      ENNReal.ofReal lam *
          (volume (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁ ∩
              (U n ∆ P.occupiedGraphDomain (g n))) /
            ENNReal.ofReal (a₁ - a₀)) +
        ENNReal.ofReal lam *
          (volume (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁ ∩
              (U n ∆ P.occupiedGraphDomain (g n))) /
            ENNReal.ofReal (b₁ - b₀)) +
          ENNReal.ofReal lam *
            (volume (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁ ∩
                (U n ∆ P.occupiedGraphDomain (g n))) /
              ENNReal.ofReal (c₁ - c₀)) +
            ENNReal.ofReal lam *
              (volume (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁ ∩
                  (U n ∆ P.occupiedGraphDomain (g n))) /
                ENNReal.ofReal (d₁ - d₀))) atTop (𝓝 0) := by
    simpa using ((hleft'.add hright').add hlower').add hupper'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbudget (fun _ => bot_le) hcost

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVRelaxation

/-- Pointwise vertical regularity, separated from the quantification over a
chosen cut fiber. -/
private def IsVerticalRegularBoundaryPoint
    (U : Set PlanePoint) (p : PlanePoint) : Prop :=
  ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
      (D : PlanePoint →L[ℝ] ℝ),
    IsOpen V ∧ p ∈ V ∧ ContDiffOn ℝ ∞ g V ∧ g p = 0 ∧
    HasFDerivAt g D p ∧ D ≠ 0 ∧ D (0, 1) ≠ 0 ∧
    U ∩ V = V ∩ {q | g q < 0}

private lemma clm_real_isInvertible_of_apply_one_ne_zero
    (A : ℝ →L[ℝ] ℝ) (hA : A 1 ≠ 0) : A.IsInvertible := by
  let B : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (A 1)⁻¹
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := B)
  · apply ContinuousLinearMap.ext_ring
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      B, ContinuousLinearMap.toSpanSingleton_apply_one]
    calc
      A (A 1)⁻¹ = A ((A 1)⁻¹ • (1 : ℝ)) := by simp
      _ = (A 1)⁻¹ • A 1 := A.map_smul _ _
      _ = 1 := by simpa [smul_eq_mul] using inv_mul_cancel₀ hA
  · apply ContinuousLinearMap.ext_ring
    simp [B, ContinuousLinearMap.comp_apply, hA]

/-- Around any point of a smooth boundary, vertical regularity fails only
above a one-dimensional critical-value set of measure zero. -/
private lemma IsSmoothDomain.local_vertical_regular_outside_null
    {U : Set PlanePoint} (hU : IsSmoothDomain U)
    {p : PlanePoint} (hp : p ∈ frontier U) :
    ∃ (W : Set PlanePoint) (B : Set ℝ),
      IsOpen W ∧ p ∈ W ∧ volume B = 0 ∧
      ∀ q ∈ frontier U ∩ W, q.1 ∉ B →
        IsVerticalRegularBoundaryPoint U q := by
  rcases hU.regular_boundary p hp with
    ⟨V, g, D, hV, hpV, hg, hgp, hderiv, hD, hlocal⟩
  have hgat : ContDiffAt ℝ ∞ g p := hg.contDiffAt (hV.mem_nhds hpV)
  have hgat1 : ContDiffAt ℝ 1 g p := hgat.of_le (by simp)
  have hfderiv : fderiv ℝ g p = D := hderiv.fderiv
  have hzero_on_frontier : ∀ q ∈ frontier U ∩ V, g q = 0 := by
    intro q hq
    have hlocal' : U ∩ V = {z | g z < 0} ∩ V := by
      rw [hlocal, inter_comm]
    have hfrontier : frontier U ∩ V = frontier {z | g z < 0} ∩ V :=
      frontier_inter_eq_of_inter_open_eq hV hlocal'
    have hqfront : q ∈ frontier {z | g z < 0} := by
      exact (hfrontier ▸ hq).1
    have hgq : ContinuousAt g q :=
      (hg.continuousOn q hq.2).continuousAt (hV.mem_nhds hq.2)
    exact eq_zero_of_mem_frontier_lt_of_continuousAt hgq hqfront
  by_cases hDy : D (0, 1) ≠ 0
  · have hcont : ContinuousAt (fun q => fderiv ℝ g q (0, 1)) p :=
      (hgat1.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
    have hne : ∀ᶠ q in 𝓝 p, fderiv ℝ g q (0, 1) ≠ 0 := by
      apply hcont.eventually_ne
      simpa [hfderiv] using hDy
    have hev : ∀ᶠ q in 𝓝 p,
        q ∈ V ∧ fderiv ℝ g q (0, 1) ≠ 0 := by
      filter_upwards [hV.mem_nhds hpV, hne] with q hqV hqne
      exact ⟨hqV, hqne⟩
    rw [eventually_nhds_iff] at hev
    rcases hev with ⟨W, hW, hWopen, hpW⟩
    refine ⟨W, ∅, hWopen, hpW, measure_empty, ?_⟩
    intro q hq _
    have hqdata := hW q hq.2
    have hqV : q ∈ V := hqdata.1
    have hqdiff : ContDiffAt ℝ 1 g q :=
      (hg.contDiffAt (hV.mem_nhds hqV)).of_le (by simp)
    let Dq : PlanePoint →L[ℝ] ℝ := fderiv ℝ g q
    refine ⟨V, g, Dq, hV, hqV, hg,
      hzero_on_frontier q ⟨hq.1, hqV⟩,
      hqdiff.differentiableAt one_ne_zero |>.hasFDerivAt,
      ?_, ?_, hlocal⟩
    · intro hDq
      exact hqdata.2 (by simp [Dq, hDq])
    · exact hqdata.2
  · have hDx : D (1, 0) ≠ 0 := by
      have hDy0 : D (0, 1) = 0 := not_ne_iff.mp hDy
      intro hDx0
      apply hD
      apply ContinuousLinearMap.ext
      intro z
      rw [show z = z.1 • ((1, 0) : PlanePoint) +
        z.2 • ((0, 1) : PlanePoint) by ext <;> simp]
      rw [D.map_add, D.map_smul, D.map_smul, hDx0, hDy0]
      simp
    let e : PlanePoint ≃L[ℝ] PlanePoint :=
      ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    let u : PlanePoint := (p.2, p.1)
    let gs : PlanePoint → ℝ := g ∘ e
    have hgsderiv :
        HasFDerivAt gs (D ∘L (e : PlanePoint →L[ℝ] PlanePoint)) u := by
      simpa [gs, e, u] using hderiv.comp u e.hasFDerivAt
    have hgs : ContDiffAt ℝ 1 gs u := by
      simpa [gs, e, u] using hgat1.comp u e.contDiff.contDiffAt
    let A : ℝ →L[ℝ] ℝ :=
      fderiv ℝ gs u ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
    have hAone : A 1 ≠ 0 := by
      simpa [A, hgsderiv.fderiv, e, u,
        ContinuousLinearMap.comp_apply] using hDx
    have hAinv : A.IsInvertible :=
      clm_real_isInvertible_of_apply_one_ne_zero A hAone
    let φ : ℝ → ℝ := hgs.implicitFunction one_ne_zero hAinv
    have hφat : ContDiffAt ℝ 1 φ p.2 := by
      simpa [φ, u] using
        hgs.contDiffAt_implicitFunction one_ne_zero hAinv
    obtain ⟨J, hJnhds, hφJ⟩ :=
      hφat.contDiffOn (m := 1) le_rfl (by simp)
    have hident_event : ∀ᶠ y in 𝓝 p.2, g (φ y, y) = 0 := by
      have h := hgs.eventually_apply_implicitFunction one_ne_zero hAinv
      simpa [φ, gs, e, u, hgp] using h
    have hzero_event_swap :=
      hgs.eventually_apply_eq_iff_implicitFunction one_ne_zero hAinv
    have hzero_event :
        ∀ᶠ q in 𝓝 p, g q = 0 ↔ φ q.2 = q.1 := by
      have h := e.symm.continuousAt.tendsto.eventually hzero_event_swap
      simpa [φ, gs, e, u, hgp] using h
    have hcontDx :
        ContinuousAt (fun q => fderiv ℝ g q (1, 0)) p :=
      (hgat1.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
    have hDx_event :
        ∀ᶠ q in 𝓝 p, fderiv ℝ g q (1, 0) ≠ 0 := by
      apply hcontDx.eventually_ne
      simpa [hfderiv] using hDx
    rw [eventually_nhds_iff] at hident_event
    rcases hident_event with ⟨I, hI, hIopen, hpI⟩
    have hJI : J ∩ I ∈ 𝓝 p.2 :=
      inter_mem hJnhds (hIopen.mem_nhds hpI)
    rcases mem_nhds_iff.mp hJI with ⟨J0, hJ0JI, hJ0open, hpJ0⟩
    have hJ0J : J0 ⊆ J := fun y hy => (hJ0JI hy).1
    have hJ0I : J0 ⊆ I := fun y hy => (hJ0JI hy).2
    have hφJ0 : ContDiffOn ℝ 1 φ J0 := hφJ.mono hJ0J
    let C : Set ℝ := {y | y ∈ J0 ∧ deriv φ y = 0}
    let B : Set ℝ := φ '' C
    have hBnull : volume B = 0 := by
      apply volume_image_critical_eq_zero
        (s := C) (f := φ) (f' := deriv φ)
      · intro y hy
        exact ((hφJ0.differentiableOn one_ne_zero) y hy.1).differentiableAt
          (hJ0open.mem_nhds hy.1) |>.hasDerivAt.hasDerivWithinAt
      · intro y hy
        exact hy.2
    have hJ0_event : ∀ᶠ q in 𝓝 p, q.2 ∈ J0 :=
      continuousAt_snd.tendsto (hJ0open.mem_nhds hpJ0)
    have hV_event : ∀ᶠ q in 𝓝 p, q ∈ V := hV.mem_nhds hpV
    have hconditions : ∀ᶠ q in 𝓝 p,
        q ∈ V ∧ q.2 ∈ J0 ∧ (g q = 0 ↔ φ q.2 = q.1) ∧
          fderiv ℝ g q (1, 0) ≠ 0 := by
      filter_upwards [hV_event, hJ0_event, hzero_event, hDx_event] with
        q hqV hqJ hqzero hqDx
      exact ⟨hqV, hqJ, hqzero, hqDx⟩
    rw [eventually_nhds_iff] at hconditions
    rcases hconditions with ⟨W, hW, hWopen, hpW⟩
    refine ⟨W, B, hWopen, hpW, hBnull, ?_⟩
    intro q hq hqB
    have hqdata := hW q hq.2
    have hqV : q ∈ V := hqdata.1
    have hgq : g q = 0 := hzero_on_frontier q ⟨hq.1, hqV⟩
    have hφq : φ q.2 = q.1 := hqdata.2.2.1.mp hgq
    have hqdiff : ContDiffAt ℝ 1 g q :=
      (hg.contDiffAt (hV.mem_nhds hqV)).of_le (by simp)
    let Dq : PlanePoint →L[ℝ] ℝ := fderiv ℝ g q
    have hDqx : Dq (1, 0) ≠ 0 := hqdata.2.2.2
    have hDqy : Dq (0, 1) ≠ 0 := by
      intro hDqy0
      have hφdiff : HasDerivAt φ (deriv φ q.2) q.2 :=
        ((hφJ0.differentiableOn one_ne_zero) q.2 hqdata.2.1).differentiableAt
          (hJ0open.mem_nhds hqdata.2.1) |>.hasDerivAt
      have hpath : HasDerivAt (fun y : ℝ => (φ y, y))
          (deriv φ q.2, 1) q.2 := by
        convert hφdiff.prodMk (hasDerivAt_id q.2) using 1
        all_goals simp
      have hcomp : HasDerivAt (fun y : ℝ => g (φ y, y))
          (Dq (deriv φ q.2, 1)) q.2 := by
        have hpoint : (φ q.2, q.2) = q := Prod.ext hφq rfl
        have hgpath : HasFDerivAt g Dq (φ q.2, q.2) := by
          rw [hpoint]
          exact hqdiff.differentiableAt one_ne_zero |>.hasFDerivAt
        have hfull := HasFDerivAt.comp
          (f := fun y : ℝ => (φ y, y))
          q.2 hgpath hpath.hasFDerivAt
        simpa [Function.comp_def] using hfull.hasDerivAt
      have heq :
          (fun y : ℝ => g (φ y, y)) =ᶠ[𝓝 q.2] fun _ => 0 := by
        filter_upwards [hJ0open.mem_nhds hqdata.2.1] with y hy
        exact hI y (hJ0I hy)
      have hcomp0 :
          HasDerivAt (fun y : ℝ => g (φ y, y)) 0 q.2 := by
        exact (hasDerivAt_const q.2 (0 : ℝ)).congr_of_eventuallyEq heq
      have hz : Dq (deriv φ q.2, 1) = 0 := hcomp.unique hcomp0
      have hlin : Dq (deriv φ q.2, 1) =
          deriv φ q.2 * Dq (1, 0) + Dq (0, 1) := by
        calc
          Dq (deriv φ q.2, 1) =
              Dq (deriv φ q.2 • ((1, 0) : PlanePoint) +
                ((0, 1) : PlanePoint)) := by
            congr 1
            all_goals ext <;> simp
          _ = deriv φ q.2 * Dq (1, 0) + Dq (0, 1) := by
            rw [map_add, map_smul]
            simp [smul_eq_mul]
      rw [hlin, hDqy0, add_zero] at hz
      have hφzero : deriv φ q.2 = 0 :=
        (mul_eq_zero.mp hz).resolve_right hDqx
      apply hqB
      exact ⟨q.2, ⟨hqdata.2.1, hφzero⟩, hφq⟩
    refine ⟨V, g, Dq, hV, hqV, hg, hgq,
      hqdiff.differentiableAt one_ne_zero |>.hasFDerivAt,
      ?_, hDqy, hlocal⟩
    intro hDq
    exact hDqx (by simp [Dq, hDq])

/-- For an arbitrary smooth domain, vertically nonregular boundary
coordinates on a compact window form a Lebesgue-null set. -/
theorem IsSmoothDomain.volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
    {U K : Set PlanePoint} (hU : IsSmoothDomain U) (hK : IsCompact K) :
    volume {x | ¬ IsVerticalRegularBoundaryValue U K x} = 0 := by
  classical
  let S := {p : PlanePoint // p ∈ frontier U ∩ K}
  have hlocal : ∀ p : S,
      ∃ (W : Set PlanePoint) (B : Set ℝ),
        IsOpen W ∧ (p : PlanePoint) ∈ W ∧ volume B = 0 ∧
        ∀ q ∈ frontier U ∩ W, q.1 ∉ B →
          IsVerticalRegularBoundaryPoint U q := by
    intro p
    exact hU.local_vertical_regular_outside_null p.property.1
  choose W B hWopen hpW hBnull hgood using hlocal
  have hcompact : IsCompact (frontier U ∩ K) :=
    hK.inter_left isClosed_frontier
  have hcover : frontier U ∩ K ⊆ ⋃ p : S, W p := by
    intro q hq
    exact mem_iUnion.2 ⟨⟨q, hq⟩, hpW ⟨q, hq⟩⟩
  obtain ⟨t, ht⟩ :=
    hcompact.elim_finite_subcover W hWopen hcover
  let T := {p : S // p ∈ t}
  let E : Set ℝ := ⋃ p : T, B p.1
  have hEnull : volume E = 0 := by
    apply measure_iUnion_null
    intro p
    exact hBnull p.1
  apply measure_mono_null (t := E) ?_ hEnull
  intro x hx
  by_contra hxE
  apply hx
  intro q hq
  have hqSK : q ∈ frontier U ∩ K := hq.1
  have hqcover : q ∈ ⋃ p, ⋃ (_ : p ∈ t), W p := ht hqSK
  simp only [mem_iUnion] at hqcover
  rcases hqcover with ⟨p, hp_t, hqW⟩
  have hxB : x ∉ B p := by
    intro hxBp
    apply hxE
    exact mem_iUnion.2 ⟨⟨p, hp_t⟩, hxBp⟩
  have hqx : q.1 = x := hq.2
  have hregq : IsVerticalRegularBoundaryPoint U q := by
    apply hgood p q ⟨hq.1.1, hqW⟩
    simpa [hqx] using hxB
  exact hregq

/-- Coordinate exchange preserves the literal smooth-domain contract. -/
theorem IsSmoothDomain.coordinateSwap_preimage
    {U : Set PlanePoint} (hU : IsSmoothDomain U) :
    let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
    IsSmoothDomain (e ⁻¹' U) := by
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  change IsSmoothDomain (e ⁻¹' U)
  constructor
  · exact hU.isOpen.preimage e.continuous
  · intro p hp
    have hep : e p ∈ frontier U :=
      e.continuous.frontier_preimage_subset U hp
    rcases hU.regular_boundary (e p) hep with
      ⟨V, g, D, hV, hepV, hg, hgep, hderiv, hD, hlocal⟩
    let V' : Set PlanePoint := e ⁻¹' V
    let g' : PlanePoint → ℝ := g ∘ e
    let D' : PlanePoint →L[ℝ] ℝ :=
      D ∘L (e : PlanePoint →L[ℝ] PlanePoint)
    refine ⟨V', g', D', hV.preimage e.continuous, hepV,
      ?_, hgep, ?_, ?_, ?_⟩
    · exact hg.comp e.contDiff.contDiffOn (fun _ hx => hx)
    · simpa [g', D'] using hderiv.comp p e.hasFDerivAt
    · intro hD'
      apply hD
      apply ContinuousLinearMap.ext
      intro z
      obtain ⟨w, rfl⟩ := e.surjective z
      simpa [D'] using
        congrArg (fun A : PlanePoint →L[ℝ] ℝ => A w) hD'
    · ext q
      simp only [V', g', mem_inter_iff, mem_preimage, mem_ofPred_eq,
        Function.comp_apply]
      exact Set.ext_iff.mp hlocal (e q)

private lemma verticalRegular_swap_implies_horizontalRegular
    {U K : Set PlanePoint} {y : ℝ}
    (h : let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
      IsVerticalRegularBoundaryValue (e ⁻¹' U) (e ⁻¹' K) y) :
    IsHorizontalRegularBoundaryValue U K y := by
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  change IsVerticalRegularBoundaryValue (e ⁻¹' U) (e ⁻¹' K) y at h
  intro p hp
  have hee (q : PlanePoint) : e (e q) = q := by
    ext <;> simp [e]
  have hefront : e p ∈ frontier (e ⁻¹' U) := by
    change e p ∈ frontier (e.toHomeomorph ⁻¹' U)
    rw [← e.toHomeomorph.preimage_frontier]
    change e (e p) ∈ frontier U
    simpa [hee] using hp.1.1
  have heK : e p ∈ e ⁻¹' K := by
    change e (e p) ∈ K
    simpa [hee] using hp.1.2
  have heline : e p ∈ verticalLine y := by
    change (e p).1 = y
    have hpy : p.2 = y := hp.2
    simpa [e] using hpy
  rcases h (e p) ⟨⟨hefront, heK⟩, heline⟩ with
    ⟨V, g, D, hV, hepV, hg, hgep, hderiv, hD, hDy, hlocal⟩
  let V' : Set PlanePoint := e ⁻¹' V
  let g' : PlanePoint → ℝ := g ∘ e
  let D' : PlanePoint →L[ℝ] ℝ :=
    D ∘L (e : PlanePoint →L[ℝ] PlanePoint)
  refine ⟨V', g', D', hV.preimage e.continuous, hepV,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hg.comp e.contDiff.contDiffOn (fun _ hx => hx)
  · simpa [g', hee] using hgep
  · simpa [g', D'] using hderiv.comp p e.hasFDerivAt
  · intro hD'
    apply hD
    apply ContinuousLinearMap.ext
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    simpa [D'] using
      congrArg (fun A : PlanePoint →L[ℝ] ℝ => A w) hD'
  · simpa [D', e] using hDy
  · ext q
    simp only [V', g', mem_inter_iff, mem_preimage, mem_ofPred_eq,
      Function.comp_apply]
    exact Set.ext_iff.mp hlocal (e q)

/-- For an arbitrary smooth domain, horizontally nonregular boundary
coordinates on a compact window form a Lebesgue-null set. -/
theorem IsSmoothDomain.volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
    {U K : Set PlanePoint} (hU : IsSmoothDomain U) (hK : IsCompact K) :
    volume {y | ¬ IsHorizontalRegularBoundaryValue U K y} = 0 := by
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  have hUs : IsSmoothDomain (e ⁻¹' U) := by
    simpa [e] using hU.coordinateSwap_preimage
  have hKs : IsCompact (e ⁻¹' K) :=
    e.toHomeomorph.isCompact_preimage.mpr hK
  have hnull :
      volume {y |
        ¬ IsVerticalRegularBoundaryValue (e ⁻¹' U) (e ⁻¹' K) y} = 0 :=
    hUs.volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero hKs
  apply measure_mono_null (t :=
    {y | ¬ IsVerticalRegularBoundaryValue
      (e ⁻¹' U) (e ⁻¹' K) y}) ?_ hnull
  intro y hy hys
  apply hy
  apply verticalRegular_swap_implies_horizontalRegular
  simpa [e] using hys

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

/-- A literal smooth old approximant and a smooth occupied graph yield four
simultaneously regular, frontier-null, finite-crossing splice cuts with the
complete four-collar averaged trace bound.  No exceptional-coordinate atlas
is required from the caller. -/
theorem exists_regularFinite_spliceCuts_le_collar_averages_against
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (U : Set PlanePoint) (hU : CMVRelaxation.IsSmoothDomain U)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU : FrontierMeasure U
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : FrontierMeasure (P.occupiedGraphDomain g)
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤) :
    ∃ l ∈ Ioo a₀ a₁, ∃ r ∈ Ioo b₀ b₁,
      ∃ d ∈ Ioo c₀ c₁, ∃ u ∈ Ioo d₀ d₁,
        CMVRelaxation.IsRegularFiniteVerticalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) l ∧
        CMVRelaxation.IsRegularFiniteVerticalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) r ∧
        CMVRelaxation.IsRegularFiniteHorizontalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) d ∧
        CMVRelaxation.IsRegularFiniteHorizontalSpliceCut U
            (P.occupiedGraphDomain g)
            (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) u ∧
        (∀ p ∈
            ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint),
          p ∉ frontier U ∧
            p ∉ frontier (P.occupiedGraphDomain g)) ∧
        CMVRelaxation.weightedTraceCost lam
            (CMVRelaxation.spliceCutTrace U (P.occupiedGraphDomain g)
              (CMVRelaxation.closedCutRectangle l r d u)) ≤
          ENNReal.ofReal lam *
              (volume (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁ ∩
                  (U ∆ P.occupiedGraphDomain g)) /
                ENNReal.ofReal (a₁ - a₀)) +
            ENNReal.ofReal lam *
              (volume (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁ ∩
                  (U ∆ P.occupiedGraphDomain g)) /
                ENNReal.ofReal (b₁ - b₀)) +
              ENNReal.ofReal lam *
                (volume (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁ ∩
                    (U ∆ P.occupiedGraphDomain g)) /
                  ENNReal.ofReal (c₁ - c₀)) +
                ENNReal.ofReal lam *
                  (volume (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁ ∩
                      (U ∆ P.occupiedGraphDomain g)) /
                    ENNReal.ofReal (d₁ - d₀)) := by
  have hregUL := hU.volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
    (CMVRelaxation.isCompact_closedCutRectangle a₀ a₁ c₀ d₁)
  have hregUR := hU.volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
    (CMVRelaxation.isCompact_closedCutRectangle b₀ b₁ c₀ d₁)
  have hregUD := hU.volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
    (CMVRelaxation.isCompact_closedCutRectangle a₀ b₁ c₀ c₁)
  have hregUU := hU.volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
    (CMVRelaxation.isCompact_closedCutRectangle a₀ b₁ d₀ d₁)
  exact
    P.exists_regularFinite_closedCutRectangle_spliceCutTrace_le_collar_averages_against
      hlam hg U hU.isOpen.measurableSet ha hab hb hc hcd hd
        hfiniteU hfiniteG hregUL hregUR hregUD hregUU

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVTwoPatchGraphVariation.GraphPatch

/-- Sequence form of the arbitrary-smooth-domain bridge: the four selected
regular finite splice cuts have complete trace cost tending to zero whenever
the four collar mismatches do. -/
theorem exists_regularFinite_spliceCuts_tendsto_zero_against
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    (g : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (U : ℕ → Set PlanePoint)
    (hU : ∀ n, CMVRelaxation.IsSmoothDomain (U n))
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hfiniteU : ∀ n, FrontierMeasure (U n)
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hfiniteG : ∀ n, FrontierMeasure (P.occupiedGraphDomain (g n))
      (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ d₁) ≠ ⊤)
    (hleft : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0))
    (hright : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0))
    (hlower : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0))
    (hupper : Tendsto (fun n =>
      volume (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁ ∩
        (U n ∆ P.occupiedGraphDomain (g n)))) atTop (𝓝 0)) :
    ∃ l r d u : ℕ → ℝ,
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteVerticalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) (l n)) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteVerticalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) (r n)) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteHorizontalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) (d n)) ∧
      (∀ n, CMVRelaxation.IsRegularFiniteHorizontalSpliceCut (U n)
        (P.occupiedGraphDomain (g n))
        (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) (u n)) ∧
      (∀ n, ∀ p ∈
          ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
            Set PlanePoint),
        p ∉ frontier (U n) ∧
          p ∉ frontier (P.occupiedGraphDomain (g n))) ∧
      Tendsto (fun n =>
        CMVRelaxation.weightedTraceCost lam
          (CMVRelaxation.spliceCutTrace (U n)
            (P.occupiedGraphDomain (g n))
            (CMVRelaxation.closedCutRectangle
              (l n) (r n) (d n) (u n)))) atTop (𝓝 0) := by
  have hmeas : ∀ n, MeasurableSet (U n) :=
    fun n => (hU n).isOpen.measurableSet
  have hregUL : ∀ n, volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle a₀ a₁ c₀ d₁) x} = 0 :=
    fun n => (hU n).volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
      (CMVRelaxation.isCompact_closedCutRectangle a₀ a₁ c₀ d₁)
  have hregUR : ∀ n, volume {x |
      ¬ CMVRelaxation.IsVerticalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle b₀ b₁ c₀ d₁) x} = 0 :=
    fun n => (hU n).volume_setOf_not_isVerticalRegularBoundaryValue_eq_zero
      (CMVRelaxation.isCompact_closedCutRectangle b₀ b₁ c₀ d₁)
  have hregUD : ∀ n, volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle a₀ b₁ c₀ c₁) y} = 0 :=
    fun n => (hU n).volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
      (CMVRelaxation.isCompact_closedCutRectangle a₀ b₁ c₀ c₁)
  have hregUU : ∀ n, volume {y |
      ¬ CMVRelaxation.IsHorizontalRegularBoundaryValue (U n)
        (CMVRelaxation.closedCutRectangle a₀ b₁ d₀ d₁) y} = 0 :=
    fun n => (hU n).volume_setOf_not_isHorizontalRegularBoundaryValue_eq_zero
      (CMVRelaxation.isCompact_closedCutRectangle a₀ b₁ d₀ d₁)
  exact
    P.exists_regularFinite_closedCutRectangle_spliceCutTrace_tendsto_zero_against
      hlam g hg U hmeas ha hab hb hc hcd hd hfiniteU hfiniteG
        hregUL hregUR hregUD hregUU hleft hright hlower hupper

end CMVTwoPatchGraphVariation.GraphPatch


namespace CMVRelaxation

/-! ## Finite-cost recovery cuts against actual graph approximants -/

/-- A finite complete smooth cost gives finite complete-frontier measure on
every measurable localization.  This is the finite-cost branch needed by the
splice selectors; no separate local frontier-finiteness witness is required. -/
theorem frontierMeasure_ne_top_of_smoothCost_ne_top
    {lam : ℝ} (hlam : 1 < lam) (U K : Set PlanePoint)
    (hK : MeasurableSet K) (hcost : smoothCost lam U ≠ ⊤) :
    FrontierMeasure U K ≠ ⊤ := by
  apply frontierMeasure_ne_top_of_smoothCostOn_ne_top
    hlam U K hK
  exact ne_top_of_le_ne_top hcost (by
    unfold smoothCostOn smoothCost
    exact setLIntegral_le_lintegral K _)

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

/-- The complete frontier of a smooth occupied graph has finite measure in
every closed coordinate rectangle.  Only the horizontal projection matters;
the graph may be unbounded globally. -/
theorem frontierMeasure_occupiedGraphDomain_closedCutRectangle_ne_top
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {a b c d : ℝ} (hab : a ≤ b) :
    FrontierMeasure (P.occupiedGraphDomain g)
      (closedCutRectangle a b c d) ≠ ⊤ := by
  rw [frontierMeasure_apply_eq_euclidean _ _
    (isCompact_closedCutRectangle a b c d).measurableSet,
    P.frontier_occupiedGraphDomain hg.continuous]
  have hsub :
      planeEuclideanHomeomorph ''
          (((fun x : ℝ => (x, g x)) '' univ) ∩
            closedCutRectangle a b c d) ⊆
        planeEuclideanHomeomorph ''
          ((fun x : ℝ => (x, g x)) '' Icc a b) := by
    rintro _ ⟨_, ⟨⟨x, _hx, rfl⟩, hp⟩, rfl⟩
    exact ⟨(x, g x), ⟨x, hp.1, rfl⟩, rfl⟩
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top <|
    (measure_mono hsub).trans <|
      hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral
        (hg.of_le (by simp)) hab

/-- Uniform graph convergence controls the mismatch on every fixed subset of
the corresponding compact vertical strip. -/
theorem tendsto_volume_inter_occupiedGraphDomain_symmDiff_zero_of_uniform
    (P : GraphPatch) {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hg : ∀ n, Measurable (g n)) (hf : Measurable f)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ n, ∀ x ∈ Icc P.a P.b, |g n x - f x| ≤ ε n)
    (K : Set PlanePoint)
    (hK : K ⊆ Icc P.a P.b ×ˢ (univ : Set ℝ)) :
    Tendsto (fun n =>
      volume (K ∩ (P.occupiedGraphDomain (g n) ∆
        P.occupiedGraphDomain f))) atTop (𝓝 0) := by
  have hle : ∀ n,
      volume (K ∩ (P.occupiedGraphDomain (g n) ∆
          P.occupiedGraphDomain f)) ≤
        ENNReal.ofReal (ε n) * volume (Icc P.a P.b) := by
    intro n
    calc
      volume (K ∩ (P.occupiedGraphDomain (g n) ∆
          P.occupiedGraphDomain f)) ≤
          volume ((P.occupiedGraphDomain (g n) ∆
            P.occupiedGraphDomain f) ∩
              (Icc P.a P.b ×ˢ (univ : Set ℝ))) := by
        apply measure_mono
        intro p hp
        exact ⟨hp.2, hK hp.1⟩
      _ ≤ ENNReal.ofReal (ε n) * volume (Icc P.a P.b) :=
        P.volume_occupiedGraphDomain_symmDiff_inter_prod_le_of_uniform
          (hg n) hf measurableSet_Icc (hclose n)
  have hofReal :
      Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hε
  have hupper :
      Tendsto (fun n =>
        ENNReal.ofReal (ε n) * volume (Icc P.a P.b))
        atTop (𝓝 0) := by
    simpa [mul_comm] using
      ENNReal.Tendsto.const_mul hofReal
        (Or.inr (measure_Icc_lt_top :
          volume (Icc P.a P.b) < ⊤).ne)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => bot_le) hle

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

/-- Starting from an arbitrary finite-liminf smooth recovery sequence, choose
the actual finite-cost reindexing and all four regular finite splice faces
against a uniformly convergent sequence of smooth occupied graphs.

The old-domain and graph-domain frontier-finiteness hypotheses and all four
collar mismatch limits are derived internally.  The only local assumptions are
the limiting carrier's four exact graph-chart identities. -/
theorem exists_finiteCost_regularFinite_spliceCuts_tendsto_zero_against
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {E : Set PlanePoint} (A : SmoothSequence) (hA : A.ConvergesTo E)
    (hAcost : A.cost lam < ⊤)
    (g : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ ∞ (g n))
    (f : ℝ → ℝ) (hf : Measurable f)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ n, ∀ x ∈ Icc P.a P.b, |g n x - f x| ≤ ε n)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hPa : P.a ≤ a₀) (hbP : b₁ ≤ P.b)
    (hlocalL : E ∩ closedCutRectangle a₀ a₁ c₀ d₁ =
      P.occupiedGraphDomain f ∩ closedCutRectangle a₀ a₁ c₀ d₁)
    (hlocalR : E ∩ closedCutRectangle b₀ b₁ c₀ d₁ =
      P.occupiedGraphDomain f ∩ closedCutRectangle b₀ b₁ c₀ d₁)
    (hlocalD : E ∩ closedCutRectangle a₀ b₁ c₀ c₁ =
      P.occupiedGraphDomain f ∩ closedCutRectangle a₀ b₁ c₀ c₁)
    (hlocalU : E ∩ closedCutRectangle a₀ b₁ d₀ d₁ =
      P.occupiedGraphDomain f ∩ closedCutRectangle a₀ b₁ d₀ d₁) :
    ∃ (B : SmoothSequence) (l r d u : ℕ → ℝ),
      B.ConvergesTo E ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      (∀ n, smoothCost lam (B.carrier n) < ⊤) ∧
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle a₀ a₁ c₀ d₁) (l n)) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle b₀ b₁ c₀ d₁) (r n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle a₀ b₁ c₀ c₁) (d n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle a₀ b₁ d₀ d₁) (u n)) ∧
      (∀ n, ∀ p ∈
          ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
            Set PlanePoint),
        p ∉ frontier (B.carrier n) ∧
          p ∉ frontier (P.occupiedGraphDomain (g n))) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (spliceCutTrace (B.carrier n)
            (P.occupiedGraphDomain (g n))
            (closedCutRectangle (l n) (r n) (d n) (u n))))
        atTop (𝓝 0) := by
  obtain ⟨B, hBconv, hBcost, hBcostEq, hBfinite⟩ :=
    A.exists_finiteCost_reindex_of_cost_lt_top hA hAcost
  let K := closedCutRectangle a₀ b₁ c₀ d₁
  let KL := closedCutRectangle a₀ a₁ c₀ d₁
  let KR := closedCutRectangle b₀ b₁ c₀ d₁
  let KD := closedCutRectangle a₀ b₁ c₀ c₁
  let KU := closedCutRectangle a₀ b₁ d₀ d₁
  have hfiniteB : ∀ n, FrontierMeasure (B.carrier n) K ≠ ⊤ := by
    intro n
    exact frontierMeasure_ne_top_of_smoothCost_ne_top
      hlam (B.carrier n) K
        (isCompact_closedCutRectangle a₀ b₁ c₀ d₁).measurableSet
        (ne_of_lt (hBfinite n))
  have hfiniteG : ∀ n,
      FrontierMeasure (P.occupiedGraphDomain (g n)) K ≠ ⊤ := by
    intro n
    exact P.frontierMeasure_occupiedGraphDomain_closedCutRectangle_ne_top
      (hg n) ((ha.trans (hab.trans (hb))).le)
  have hstrip : ∀ {a b c d : ℝ}, a₀ ≤ a → b ≤ b₁ →
      closedCutRectangle a b c d ⊆
        Icc P.a P.b ×ˢ (univ : Set ℝ) := by
    intro a b c d hleft hright p hp
    exact ⟨⟨hPa.trans (hleft.trans hp.1.1),
      hp.1.2.trans (hright.trans hbP)⟩, Set.mem_univ p.2⟩
  have hgraphLocal : ∀ Q : Set PlanePoint,
      Q ⊆ Icc P.a P.b ×ˢ (univ : Set ℝ) →
      Tendsto (fun n =>
        volume (Q ∩ (P.occupiedGraphDomain (g n) ∆
          P.occupiedGraphDomain f))) atTop (𝓝 0) := by
    intro Q hQ
    exact P.tendsto_volume_inter_occupiedGraphDomain_symmDiff_zero_of_uniform
      (fun n => (hg n).continuous.measurable) hf hε hclose Q hQ
  have hleft :
      Tendsto (fun n =>
        volume (KL ∩ (B.carrier n ∆ P.occupiedGraphDomain (g n))))
        atTop (𝓝 0) := by
    apply tendsto_volume_inter_symmDiff_zero_of_local_agreement
      (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance hBconv)
      (hgraphLocal KL (hstrip le_rfl (hab.le.trans hb.le)))
    simpa only [KL] using hlocalL
  have hright :
      Tendsto (fun n =>
        volume (KR ∩ (B.carrier n ∆ P.occupiedGraphDomain (g n))))
        atTop (𝓝 0) := by
    apply tendsto_volume_inter_symmDiff_zero_of_local_agreement
      (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance hBconv)
      (hgraphLocal KR (hstrip (ha.le.trans hab.le) le_rfl))
    simpa only [KR] using hlocalR
  have hlower :
      Tendsto (fun n =>
        volume (KD ∩ (B.carrier n ∆ P.occupiedGraphDomain (g n))))
        atTop (𝓝 0) := by
    apply tendsto_volume_inter_symmDiff_zero_of_local_agreement
      (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance hBconv)
      (hgraphLocal KD (hstrip le_rfl le_rfl))
    simpa only [KD] using hlocalD
  have hupper :
      Tendsto (fun n =>
        volume (KU ∩ (B.carrier n ∆ P.occupiedGraphDomain (g n))))
        atTop (𝓝 0) := by
    apply tendsto_volume_inter_symmDiff_zero_of_local_agreement
      (tendsto_volume_inter_symmDiff_zero_of_characteristicDistance hBconv)
      (hgraphLocal KU (hstrip le_rfl le_rfl))
    simpa only [KU] using hlocalU
  obtain ⟨l, r, d, u, hl, hr, hdmem, humem,
      hlreg, hrreg, hdreg, hureg, hcornerAvoid, hseam⟩ :=
    P.exists_regularFinite_spliceCuts_tendsto_zero_against
      hlam g hg B.carrier B.smooth ha hab hb hc hcd hd
        (by simpa only [K] using hfiniteB)
        (by simpa only [K] using hfiniteG)
        (by simpa only [KL] using hleft)
        (by simpa only [KR] using hright)
        (by simpa only [KD] using hlower)
        (by simpa only [KU] using hupper)
  exact ⟨B, l, r, d, u, hBconv, hBcost, hBcostEq, hBfinite,
    hl, hr, hdmem, humem, hlreg, hrreg, hdreg, hureg,
    hcornerAvoid, hseam⟩

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

/-- The preceding finite-cost selector can be fed by graph approximants
constructed from the actual `C²` primary variation.  The old and new smooth
graphs agree on endpoint collars, the new graph converges uniformly to the
literal varied graph, and its weighted graph length has the same vanishing
error. -/
theorem exists_common_smoothGraphs_finiteCost_regularFinite_spliceCuts
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch) (T : P.Tube)
    (V : PrimaryVariation P) (t : ℝ)
    (hshift : ∀ x ∈ Icc P.a P.b, |t * V x| ≤ T.radius / 2)
    {E : Set PlanePoint} (A : SmoothSequence) (hA : A.ConvergesTo E)
    (hAcost : A.cost lam < ⊤)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hPa : P.a ≤ a₀) (hbP : b₁ ≤ P.b)
    (hlocalL : E ∩ closedCutRectangle a₀ a₁ c₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ a₁ c₀ d₁)
    (hlocalR : E ∩ closedCutRectangle b₀ b₁ c₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle b₀ b₁ c₀ d₁)
    (hlocalD : E ∩ closedCutRectangle a₀ b₁ c₀ c₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ b₁ c₀ c₁)
    (hlocalU : E ∩ closedCutRectangle a₀ b₁ d₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ b₁ d₀ d₁) :
    ∃ (B : SmoothSequence) (g₀ g₁ : ℕ → ℝ → ℝ)
        (s₀ s₁ l r d u : ℕ → ℝ),
      B.ConvergesTo E ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      (∀ n, smoothCost lam (B.carrier n) < ⊤) ∧
      (∀ n, P.a < s₀ n ∧ s₀ n < s₁ n ∧ s₁ n < P.b) ∧
      (∀ n, ContDiff ℝ ∞ (g₀ n) ∧ ContDiff ℝ ∞ (g₁ n)) ∧
      (∀ n x, x ≤ s₀ n → g₁ n x = g₀ n x) ∧
      (∀ n x, s₁ n ≤ x → g₁ n x = g₀ n x) ∧
      (∀ n x, x ∈ Icc P.a P.b →
        |g₁ n x - P.variedGraph V t x| <
          1 / (n + 1 : ℝ)) ∧
      (∀ n x, x ∈ Icc P.a P.b →
        P.zone.Contains (x, g₁ n x)) ∧
      (∀ n,
        |P.zone.weight lam *
            (∫ x in P.a..P.b,
              Real.sqrt (1 + (deriv (g₁ n) x) ^ 2)) -
          weightedGraphLength lam P V t| <
            1 / (n + 1 : ℝ)) ∧
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g₁ n))
        (closedCutRectangle a₀ a₁ c₀ d₁) (l n)) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g₁ n))
        (closedCutRectangle b₀ b₁ c₀ d₁) (r n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g₁ n))
        (closedCutRectangle a₀ b₁ c₀ c₁) (d n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g₁ n))
        (closedCutRectangle a₀ b₁ d₀ d₁) (u n)) ∧
      (∀ n, ∀ p ∈
          ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
            Set PlanePoint),
        p ∉ frontier (B.carrier n) ∧
          p ∉ frontier (P.occupiedGraphDomain (g₁ n))) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (spliceCutTrace (B.carrier n)
            (P.occupiedGraphDomain (g₁ n))
            (closedCutRectangle (l n) (r n) (d n) (u n))))
        atTop (𝓝 0) := by
  have hsmooth : ∀ n : ℕ, ∃ (g₀ g₁ : ℝ → ℝ) (s₀ s₁ : ℝ),
      P.a < s₀ ∧ s₀ < s₁ ∧ s₁ < P.b ∧
      ContDiff ℝ ∞ g₀ ∧ ContDiff ℝ ∞ g₁ ∧
      (∀ x, x ≤ s₀ → g₁ x = g₀ x) ∧
      (∀ x, s₁ ≤ x → g₁ x = g₀ x) ∧
      (∀ x ∈ Icc P.a P.b, |g₀ x - P.graph x| < 1 / (n + 1 : ℝ)) ∧
      (∀ x ∈ Icc P.a P.b,
        |g₁ x - P.variedGraph V t x| < 1 / (n + 1 : ℝ)) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g₀ x)) ∧
      (∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g₁ x)) ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₀ x) ^ 2)) -
        weightedGraphLength lam P V 0| < 1 / (n + 1 : ℝ) ∧
      |P.zone.weight lam *
          (∫ x in P.a..P.b, Real.sqrt (1 + (deriv g₁ x) ^ 2)) -
        weightedGraphLength lam P V t| < 1 / (n + 1 : ℝ) := by
    intro n
    apply P.exists_common_smoothGraphs_in_tube_weightedLength_lt
      T hlam V t hshift
    exact one_div_pos.mpr (by positivity)
  choose g₀ g₁ s₀ s₁ hPas₀ hs₀s₁ hs₁b hg₀ hg₁ hleftEq hrightEq
    hclose₀ hclose₁ hzone₀ hzone₁ hlength₀ hlength₁ using hsmooth
  have hε :
      Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨B, l, r, d, u, hBconv, hBcost, hBcostEq, hBfinite,
      hl, hr, hdmem, humem, hlreg, hrreg, hdreg, hureg,
      hcornerAvoid, hseam⟩ :=
    P.exists_finiteCost_regularFinite_spliceCuts_tendsto_zero_against
      hlam A hA hAcost g₁ hg₁ (P.variedGraph V t)
        (P.graph_contDiff.add (contDiff_const.mul V.contDiff)).continuous.measurable
        (fun n : ℕ => 1 / (n + 1 : ℝ)) hε
        (fun n x hx => (hclose₁ n x hx).le)
        ha hab hb hc hcd hd hPa hbP hlocalL hlocalR hlocalD hlocalU
  exact ⟨B, g₀, g₁, s₀, s₁, l, r, d, u,
    hBconv, hBcost, hBcostEq, hBfinite,
    fun n => ⟨hPas₀ n, hs₀s₁ n, hs₁b n⟩,
    fun n => ⟨hg₀ n, hg₁ n⟩,
    hleftEq, hrightEq, hclose₁, hzone₁, hlength₁,
    hl, hr, hdmem, humem, hlreg, hrreg, hdreg, hureg,
    hcornerAvoid, hseam⟩

end CMVTwoPatchGraphVariation.GraphPatch

namespace CMVRelaxation

open CMVTwoPatchGraphVariation

/-- Direct constant-zone form of the sharp weighted graph-trace estimate. -/
theorem weightedTraceCost_graph_Icc_le_intervalIntegral_of_zone
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hzone : ∀ x ∈ Icc P.a P.b, P.zone.Contains (x, g x)) :
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc P.a P.b) ≤
      ENNReal.ofReal
        (P.zone.weight lam *
          ∫ x in P.a..P.b,
            Real.sqrt (1 + (deriv g x) ^ 2)) := by
  have hweight : 0 ≤ P.zone.weight lam :=
    (P.zone.weight_pos hlam).le
  calc
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc P.a P.b) ≤
        ENNReal.ofReal (P.zone.weight lam) *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              ((fun x : ℝ => (x, g x)) '' Icc P.a P.b)) := by
      apply weightedTraceCost_le_const_mul_hausdorff
      rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change ENNReal.ofReal (StripDensity lam (x, g x)) ≤
        ENNReal.ofReal (P.zone.weight lam)
      rw [P.zone.stripDensity_eq_weight (hzone x hx)]
    _ ≤ ENNReal.ofReal (P.zone.weight lam) *
          ENNReal.ofReal
            (∫ x in P.a..P.b,
              Real.sqrt (1 + (deriv g x) ^ 2)) := by
      gcongr
      exact hausdorffMeasure_euclideanGraph_Icc_le_intervalIntegral
        hg P.a_lt_b.le
    _ = _ := (ENNReal.ofReal_mul hweight).symm

end CMVRelaxation

namespace CMVTwoPatchGraphVariation.GraphPatch

open CMVRelaxation

/-- On the finite-cost branch, the actual smooth graph approximants and regular
finite cuts produce raw splices converging to the literal replacement carrier.
Their complete frontier cost is bounded by the unchanged old approximant
outside the fixed core, the exact varied graph functional, the reciprocal
smoothing allowance, and the complete vanishing cut trace.

The theorem also returns each raw splice's canonical open representative.  It
has exactly the same frontier cost and characteristic-function limit.  These
open representatives are not asserted to be smooth domains; finite-junction
rerounding remains necessary before they define a `SmoothSequence`. -/
theorem exists_finiteCost_regularFinite_rawSplices
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch) (T : P.Tube)
    (V : PrimaryVariation P) (t : ℝ)
    (hshift : ∀ x ∈ Icc P.a P.b, |t * V x| ≤ T.radius / 2)
    {E F : Set PlanePoint} (A : SmoothSequence) (hA : A.ConvergesTo E)
    (hAcost : A.cost lam < ⊤)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (ha : a₀ < a₁) (hab : a₁ < b₀) (hb : b₀ < b₁)
    (hc : c₀ < c₁) (hcd : c₁ < d₀) (hd : d₀ < d₁)
    (hPa : P.a ≤ a₀) (hbP : b₁ ≤ P.b)
    (hlocalL : E ∩ closedCutRectangle a₀ a₁ c₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ a₁ c₀ d₁)
    (hlocalR : E ∩ closedCutRectangle b₀ b₁ c₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle b₀ b₁ c₀ d₁)
    (hlocalD : E ∩ closedCutRectangle a₀ b₁ c₀ c₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ b₁ c₀ c₁)
    (hlocalU : E ∩ closedCutRectangle a₀ b₁ d₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ b₁ d₀ d₁)
    (hFlocal : F ∩ closedCutRectangle a₀ b₁ c₀ d₁ =
      P.occupiedGraphDomain (P.variedGraph V t) ∩
        closedCutRectangle a₀ b₁ c₀ d₁)
    (hEF : E ∆ F ⊆ Ioo a₁ b₀ ×ˢ Ioo c₁ d₀) :
    ∃ (B : SmoothSequence) (g : ℕ → ℝ → ℝ)
        (l r d u : ℕ → ℝ),
      B.ConvergesTo E ∧
      Tendsto (fun n => smoothCost lam (B.carrier n))
        atTop (𝓝 (A.cost lam)) ∧
      B.cost lam = A.cost lam ∧
      (∀ n, smoothCost lam (B.carrier n) < ⊤) ∧
      (∀ n, ContDiff ℝ ∞ (g n)) ∧
      (∀ n x, x ∈ Icc P.a P.b →
        |g n x - P.variedGraph V t x| < 1 / (n + 1 : ℝ)) ∧
      (∀ n x, x ∈ Icc P.a P.b → P.zone.Contains (x, g n x)) ∧
      (∀ n,
        |P.zone.weight lam *
            (∫ x in P.a..P.b,
              Real.sqrt (1 + (deriv (g n) x) ^ 2)) -
          weightedGraphLength lam P V t| < 1 / (n + 1 : ℝ)) ∧
      (∀ n, l n ∈ Ioo a₀ a₁) ∧
      (∀ n, r n ∈ Ioo b₀ b₁) ∧
      (∀ n, d n ∈ Ioo c₀ c₁) ∧
      (∀ n, u n ∈ Ioo d₀ d₁) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle a₀ a₁ c₀ d₁) (l n)) ∧
      (∀ n, IsRegularFiniteVerticalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle b₀ b₁ c₀ d₁) (r n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle a₀ b₁ c₀ c₁) (d n)) ∧
      (∀ n, IsRegularFiniteHorizontalSpliceCut (B.carrier n)
        (P.occupiedGraphDomain (g n))
        (closedCutRectangle a₀ b₁ d₀ d₁) (u n)) ∧
      (∀ n, ∀ p ∈
          ({(l n, d n), (l n, u n), (r n, d n), (r n, u n)} :
            Set PlanePoint),
        p ∉ frontier (B.carrier n) ∧
          p ∉ frontier (P.occupiedGraphDomain (g n))) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (spliceCutTrace (B.carrier n)
            (P.occupiedGraphDomain (g n))
            (closedCutRectangle (l n) (r n) (d n) (u n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        characteristicDistance
          (spliceIn (B.carrier n) (P.occupiedGraphDomain (g n))
            (closedCutRectangle (l n) (r n) (d n) (u n))) F)
        atTop (𝓝 0) ∧
      (∀ n,
        smoothCost lam
            (spliceIn (B.carrier n) (P.occupiedGraphDomain (g n))
              (closedCutRectangle (l n) (r n) (d n) (u n))) ≤
          smoothCostOn lam (B.carrier n)
              (Ioo a₁ b₀ ×ˢ Ioo c₁ d₀)ᶜ +
            ENNReal.ofReal
              (weightedGraphLength lam P V t + 1 / (n + 1 : ℝ)) +
            weightedTraceCost lam
              (spliceCutTrace (B.carrier n)
                (P.occupiedGraphDomain (g n))
                (closedCutRectangle (l n) (r n) (d n) (u n)))) ∧
      (∀ n, IsOpen
        (openSpliceIn (B.carrier n) (P.occupiedGraphDomain (g n))
          (closedCutRectangle (l n) (r n) (d n) (u n)))) ∧
      Tendsto (fun n =>
        characteristicDistance
          (openSpliceIn (B.carrier n) (P.occupiedGraphDomain (g n))
            (closedCutRectangle (l n) (r n) (d n) (u n))) F)
        atTop (𝓝 0) ∧
      ∀ n,
        smoothCost lam
            (openSpliceIn (B.carrier n) (P.occupiedGraphDomain (g n))
              (closedCutRectangle (l n) (r n) (d n) (u n))) ≤
          smoothCostOn lam (B.carrier n)
              (Ioo a₁ b₀ ×ˢ Ioo c₁ d₀)ᶜ +
            ENNReal.ofReal
              (weightedGraphLength lam P V t + 1 / (n + 1 : ℝ)) +
            weightedTraceCost lam
              (spliceCutTrace (B.carrier n)
                (P.occupiedGraphDomain (g n))
                (closedCutRectangle (l n) (r n) (d n) (u n))) := by
  obtain ⟨B, g₀, g, s₀, s₁, l, r, d, u,
      hBconv, hBcost, hBcostEq, hBfinite, horder, hgsmooth,
      hleftEq, hrightEq, hclose, hzone, hlength,
      hl, hr, hdmem, humem, hlreg, hrreg, hdreg, hureg,
      hcornerAvoid, hseam⟩ :=
    P.exists_common_smoothGraphs_finiteCost_regularFinite_spliceCuts
      hlam T V t hshift A hA hAcost ha hab hb hc hcd hd hPa hbP
        hlocalL hlocalR hlocalD hlocalU
  let C := Ioo a₁ b₀ ×ˢ Ioo c₁ d₀
  let K := closedCutRectangle a₀ b₁ c₀ d₁
  let W : ℕ → Set PlanePoint :=
    fun n => closedCutRectangle (l n) (r n) (d n) (u n)
  have hCsubW : ∀ n, C ⊆ W n := by
    intro n p hp
    rcases hp with ⟨⟨hpxl, hpxr⟩, ⟨hpyl, hpyr⟩⟩
    exact ⟨⟨by linarith [(hl n).2], by linarith [(hr n).1]⟩,
      ⟨by linarith [(hdmem n).2], by linarith [(humem n).1]⟩⟩
  have hWsubK : ∀ n, W n ⊆ K := by
    intro n p hp
    rcases hp with ⟨⟨hpxl, hpxr⟩, ⟨hpyl, hpyr⟩⟩
    exact ⟨⟨by linarith [(hl n).1], by linarith [(hr n).2]⟩,
      ⟨by linarith [(hdmem n).1], by linarith [(humem n).2]⟩⟩
  have hKstrip :
      K ⊆ Icc P.a P.b ×ˢ (univ : Set ℝ) := by
    intro p hp
    exact ⟨⟨hPa.trans hp.1.1, hp.1.2.trans hbP⟩, Set.mem_univ p.2⟩
  have hε :
      Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hgraphK :
      Tendsto (fun n =>
        volume (K ∩ (P.occupiedGraphDomain (g n) ∆
          P.occupiedGraphDomain (P.variedGraph V t)))) atTop (𝓝 0) := by
    exact P.tendsto_volume_inter_occupiedGraphDomain_symmDiff_zero_of_uniform
      (fun n => (hgsmooth n).2.continuous.measurable)
      (P.graph_contDiff.add
        (contDiff_const.mul V.contDiff)).continuous.measurable
      hε (fun n x hx => (hclose n x hx).le) K hKstrip
  have hgraphF :
      Tendsto (fun n =>
        volume ((P.occupiedGraphDomain (g n) ∆ F) ∩ W n))
        atTop (𝓝 0) := by
    have hle : ∀ n,
        volume ((P.occupiedGraphDomain (g n) ∆ F) ∩ W n) ≤
          volume (K ∩ (P.occupiedGraphDomain (g n) ∆
            P.occupiedGraphDomain (P.variedGraph V t))) := by
      intro n
      apply measure_mono
      intro p hp
      have hpK : p ∈ K := hWsubK n hp.2
      have hpFH :
          p ∈ F ↔ p ∈ P.occupiedGraphDomain (P.variedGraph V t) := by
        constructor
        · intro hpF
          have hpFK : p ∈ F ∩ K := ⟨hpF, hpK⟩
          rw [hFlocal] at hpFK
          exact hpFK.1
        · intro hpG
          have hpGK :
              p ∈ P.occupiedGraphDomain (P.variedGraph V t) ∩ K :=
            ⟨hpG, hpK⟩
          rw [← hFlocal] at hpGK
          exact hpGK.1
      refine ⟨hpK, ?_⟩
      have hpDiff := hp.1
      simp only [Set.mem_symmDiff] at hpDiff ⊢
      tauto
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hgraphK (fun _ => bot_le) hle
  have hrawConv :
      Tendsto (fun n =>
        characteristicDistance
          (spliceIn (B.carrier n) (P.occupiedGraphDomain (g n)) (W n)) F)
        atTop (𝓝 0) := by
    have hle : ∀ n,
        characteristicDistance
            (spliceIn (B.carrier n) (P.occupiedGraphDomain (g n)) (W n)) F ≤
          characteristicDistance (B.carrier n) E +
            volume ((P.occupiedGraphDomain (g n) ∆ F) ∩ W n) := by
      intro n
      exact characteristicDistance_spliceIn_le
        (hEF.trans (hCsubW n))
    have hsum :
        Tendsto (fun n =>
          characteristicDistance (B.carrier n) E +
            volume ((P.occupiedGraphDomain (g n) ∆ F) ∩ W n))
          atTop (𝓝 0) := by
      simpa using hBconv.add hgraphF
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hsum (fun _ => bot_le) hle
  have hrawCost : ∀ n,
      smoothCost lam
          (spliceIn (B.carrier n) (P.occupiedGraphDomain (g n)) (W n)) ≤
        smoothCostOn lam (B.carrier n) Cᶜ +
          ENNReal.ofReal
            (weightedGraphLength lam P V t + 1 / (n + 1 : ℝ)) +
          weightedTraceCost lam
            (spliceCutTrace (B.carrier n)
              (P.occupiedGraphDomain (g n)) (W n)) := by
    intro n
    have hout : interior (W n)ᶜ ⊆ Cᶜ := by
      intro p hpOutside hpC
      exact (interior_subset hpOutside) (hCsubW n hpC)
    have htraceSub :
        ((fun x : ℝ => (x, g n x)) '' univ) ∩ interior (W n) ⊆
          (fun x : ℝ => (x, g n x)) '' Icc P.a P.b := by
      rintro _ ⟨⟨x, _hx, rfl⟩, hpW⟩
      have hpK := hWsubK n (interior_subset hpW)
      exact ⟨x, ⟨hPa.trans hpK.1.1, hpK.1.2.trans hbP⟩, rfl⟩
    have hreal :
        P.zone.weight lam *
            (∫ x in P.a..P.b,
              Real.sqrt (1 + (deriv (g n) x) ^ 2)) ≤
          weightedGraphLength lam P V t + 1 / (n + 1 : ℝ) := by
      have hdiff :
          P.zone.weight lam *
                (∫ x in P.a..P.b,
                  Real.sqrt (1 + (deriv (g n) x) ^ 2)) -
              weightedGraphLength lam P V t <
            1 / (n + 1 : ℝ) :=
        lt_of_le_of_lt (le_abs_self _) (hlength n)
      linarith
    have htrace :
        weightedTraceCost lam
            (((fun x : ℝ => (x, g n x)) '' univ) ∩ interior (W n)) ≤
          ENNReal.ofReal
            (weightedGraphLength lam P V t + 1 / (n + 1 : ℝ)) := by
      exact (weightedTraceCost_mono lam htraceSub).trans <|
        (weightedTraceCost_graph_Icc_le_intervalIntegral_of_zone
          hlam P ((hgsmooth n).2.of_le (by simp)) (hzone n)).trans
            (ENNReal.ofReal_le_ofReal hreal)
    exact
      (smoothCost_spliceIn_occupiedGraphDomain_le
        lam (B.carrier n) P (hgsmooth n).2 (W n)).trans <|
          add_le_add (add_le_add
            (smoothCostOn_mono lam (B.carrier n) hout) htrace) le_rfl
  have hlr : ∀ n, l n < r n := by
    intro n
    exact (hl n).2.trans (hab.trans (hr n).1)
  have hdu : ∀ n, d n < u n := by
    intro n
    exact (hdmem n).2.trans (hcd.trans (humem n).1)
  have hopen : ∀ n,
      IsOpen
        (openSpliceIn (B.carrier n) (P.occupiedGraphDomain (g n)) (W n)) :=
    fun _ => isOpen_openSpliceIn _ _ _
  have hopenConv :
      Tendsto (fun n =>
        characteristicDistance
          (openSpliceIn (B.carrier n) (P.occupiedGraphDomain (g n)) (W n)) F)
        atTop (𝓝 0) := by
    have heq :
        (fun n =>
          characteristicDistance
            (openSpliceIn (B.carrier n)
              (P.occupiedGraphDomain (g n)) (W n)) F) =
        fun n =>
          characteristicDistance
            (spliceIn (B.carrier n)
              (P.occupiedGraphDomain (g n)) (W n)) F := by
      funext n
      exact characteristicDistance_openSpliceIn_eq_spliceIn
        (B.smooth n).isOpen
        (P.isOpen_occupiedGraphDomain (hgsmooth n).2.continuous)
        (by simpa only [W] using
          volume_frontier_closedCutRectangle (hlr n) (hdu n))
    rw [heq]
    exact hrawConv
  have hopenCost : ∀ n,
      smoothCost lam
          (openSpliceIn (B.carrier n) (P.occupiedGraphDomain (g n)) (W n)) ≤
        smoothCostOn lam (B.carrier n) Cᶜ +
          ENNReal.ofReal
            (weightedGraphLength lam P V t + 1 / (n + 1 : ℝ)) +
          weightedTraceCost lam
            (spliceCutTrace (B.carrier n)
              (P.occupiedGraphDomain (g n)) (W n)) := by
    intro n
    rw [smoothCost_openSpliceIn_eq_smoothCost_spliceIn
      lam (B.smooth n).isOpen
      (P.isOpen_occupiedGraphDomain (hgsmooth n).2.continuous)
      (by simpa only [W, closedCutRectangle] using
        (isClosed_Icc.prod isClosed_Icc :
          IsClosed (Icc (l n) (r n) ×ˢ Icc (d n) (u n))))
      (by simpa only [W] using
        closure_interior_closedCutRectangle (hlr n) (hdu n))]
    exact hrawCost n
  exact ⟨B, g, l, r, d, u, hBconv, hBcost, hBcostEq, hBfinite,
    fun n => (hgsmooth n).2, hclose, hzone, hlength,
    hl, hr, hdmem, humem, hlreg, hrreg, hdreg, hureg,
    hcornerAvoid, hseam, hrawConv, by simpa only [C, W] using hrawCost,
    by simpa only [W] using hopen,
    by simpa only [W] using hopenConv,
    by simpa only [C, W] using hopenCost⟩

end CMVTwoPatchGraphVariation.GraphPatch
