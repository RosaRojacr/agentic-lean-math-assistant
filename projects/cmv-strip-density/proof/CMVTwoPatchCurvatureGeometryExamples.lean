/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTwoPatchCurvatureGeometry

/-!
# Compiled applications of the graph-curvature bridge

These applications exercise regular increasing and decreasing parameter
changes, both occupied-side orientations, the two strip-density weights, a
zero-curvature affine graph, and two translated circular graph arcs with the
same nonzero curvature.
-/

open Set Real

noncomputable section
namespace CMVTwoPatchGraphVariation

namespace GraphPatch.Examples

/-- Increasing traversal of a below-occupied graph preserves the internally
oriented curvature constant. -/
theorem below_identity_preserves_orientedCurvature
    {P : GraphPatch} {K : ℝ} (hside : P.side = .below)
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      (P.reparameterizedTrace (RegularGraphParameterChange.identity P))
      (P.reparameterizedVelocity (RegularGraphParameterChange.identity P))
      (P.reparameterizedAcceleration (RegularGraphParameterChange.identity P))
      K P.a P.b := by
  simpa [RegularGraphParameterChange.identity, hside] using
    P.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
      (RegularGraphParameterChange.identity P) hK hKne

/-- Increasing traversal of an above-occupied graph reverses occupied-side
curvature orientation. -/
theorem above_identity_reverses_orientedCurvature
    {P : GraphPatch} {K : ℝ} (hside : P.side = .above)
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      (P.reparameterizedTrace (RegularGraphParameterChange.identity P))
      (P.reparameterizedVelocity (RegularGraphParameterChange.identity P))
      (P.reparameterizedAcceleration (RegularGraphParameterChange.identity P))
      (-K) P.a P.b := by
  simpa [RegularGraphParameterChange.identity, hside] using
    P.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
      (RegularGraphParameterChange.identity P) hK hKne

/-- Decreasing traversal of an above-occupied graph cancels the occupied-side
orientation reversal. -/
theorem above_reflection_preserves_orientedCurvature
    {P : GraphPatch} {K : ℝ} (hside : P.side = .above)
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      (P.reparameterizedTrace (RegularGraphParameterChange.reflection P))
      (P.reparameterizedVelocity (RegularGraphParameterChange.reflection P))
      (P.reparameterizedAcceleration (RegularGraphParameterChange.reflection P))
      K P.a P.b := by
  simpa [RegularGraphParameterChange.reflection, hside] using
    P.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
      (RegularGraphParameterChange.reflection P) hK hKne

/-- Decreasing traversal reverses the signed curvature of a below-occupied
horizontal graph. -/
theorem below_reflection_reverses_orientedCurvature
    {P : GraphPatch} {K : ℝ} (hside : P.side = .below)
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      (P.reparameterizedTrace (RegularGraphParameterChange.reflection P))
      (P.reparameterizedVelocity (RegularGraphParameterChange.reflection P))
      (P.reparameterizedAcceleration (RegularGraphParameterChange.reflection P))
      (-K) P.a P.b := by
  simpa [RegularGraphParameterChange.reflection, hside] using
    P.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
      (RegularGraphParameterChange.reflection P) hK hKne

end GraphPatch.Examples

namespace Examples

/-- The existing density-one, below-occupied affine patch exercises the
zero-curvature supporting-line branch. -/
theorem interior_affine_supportingLine (lam : ℝ) :
    (interiorPatch (-2) (-1) (by norm_num)).zone.weight lam = 1 ∧
      ∀ x ∈ Icc
        (interiorPatch (-2) (-1) (by norm_num)).a
        (interiorPatch (-2) (-1) (by norm_num)).b,
        (interiorPatch (-2) (-1) (by norm_num)).graph x =
          (interiorPatch (-2) (-1) (by norm_num)).graph
              (interiorPatch (-2) (-1) (by norm_num)).a +
            deriv (interiorPatch (-2) (-1) (by norm_num)).graph
                (interiorPatch (-2) (-1) (by norm_num)).a *
              (x - (interiorPatch (-2) (-1) (by norm_num)).a) := by
  constructor
  · rfl
  · apply
      (interiorPatch (-2) (-1) (by norm_num)
        ).graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    intro x _hx
    simp [GraphPatch.orientedGraphCurvature, GraphPatch.graphCurvature,
      interiorPatch]

/-- The existing above-occupied exterior affine patch exercises arbitrary
`lambda > 1`, the exterior density weight, and the opposite occupied side. -/
theorem exterior_affine_supportingLine
    {lam : ℝ} (hlam : 1 < lam) :
    (lowerExteriorPatch 1 2 (by norm_num)).zone.weight lam = lam ∧
      0 < (lowerExteriorPatch 1 2 (by norm_num)).zone.weight lam ∧
      ∀ x ∈ Icc
        (lowerExteriorPatch 1 2 (by norm_num)).a
        (lowerExteriorPatch 1 2 (by norm_num)).b,
        (lowerExteriorPatch 1 2 (by norm_num)).graph x =
          (lowerExteriorPatch 1 2 (by norm_num)).graph
              (lowerExteriorPatch 1 2 (by norm_num)).a +
            deriv (lowerExteriorPatch 1 2 (by norm_num)).graph
                (lowerExteriorPatch 1 2 (by norm_num)).a *
              (x - (lowerExteriorPatch 1 2 (by norm_num)).a) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact lt_trans zero_lt_one hlam
  · apply
      (lowerExteriorPatch 1 2 (by norm_num)
        ).graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    intro x _hx
    simp [GraphPatch.orientedGraphCurvature, GraphPatch.graphCurvature,
      lowerExteriorPatch]

end Examples

namespace CircularGraphExamples

/-- A radius-`r` lower circular arc, oriented with increasing horizontal
coordinate on `[-pi/3, pi/3]`. -/
def trace (center : PlanePoint) (r : ℝ) (t : ℝ) : PlanePoint :=
  (center.1 + r * sin t, center.2 - r * cos t)

/-- Actual coordinate velocity of `trace`. -/
def velocity (r : ℝ) (t : ℝ) : PlanePoint :=
  (r * cos t, r * sin t)

/-- Actual coordinate acceleration of `trace`. -/
def acceleration (r : ℝ) (t : ℝ) : PlanePoint :=
  (-r * sin t, r * cos t)

theorem speed_eq {r t : ℝ} (hr : 0 < r) :
    CMVCurvatureIntegration.euclideanSpeed (velocity r) t = r := by
  unfold CMVCurvatureIntegration.euclideanSpeed velocity
  have htrig := Real.sin_sq_add_cos_sq t
  have harg : (r * cos t) ^ 2 + (r * sin t) ^ 2 = r ^ 2 := by
    nlinarith
  rw [harg, Real.sqrt_sq_eq_abs, abs_of_pos hr]

/-- Each circular specimen is genuinely a regular horizontal graph arc: its
horizontal coordinate velocity stays positive on the closed interval. -/
theorem horizontalVelocity_pos {r t : ℝ} (hr : 0 < r)
    (ht : t ∈ Icc (-(π / 3)) (π / 3)) :
    0 < (velocity r t).1 := by
  unfold velocity
  have hthird : π / 3 < π / 2 := by
    nlinarith [Real.pi_pos]
  exact mul_pos hr (Real.cos_pos_of_mem_Ioo
    ⟨(neg_lt_neg hthird).trans_le ht.1, ht.2.trans_lt hthird⟩)

/-- A concrete circular graph arc instantiates the arbitrary-speed integration
interface with its actual velocity, acceleration, and curvature `1/r`. -/
theorem application (center : PlanePoint) {r : ℝ} (hr : 0 < r) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      (trace center r) (velocity r) (acceleration r)
      (1 / r) (-(π / 3)) (π / 3) := by
  refine {
    start_lt_finish := by nlinarith [Real.pi_pos]
    curvature_ne_zero := one_div_ne_zero hr.ne'
    trace_fst_continuous := ?_
    trace_snd_continuous := ?_
    velocity_fst_continuous := ?_
    velocity_snd_continuous := ?_
    trace_fst_derivative := ?_
    trace_snd_derivative := ?_
    velocity_fst_derivative := ?_
    velocity_snd_derivative := ?_
    positive_speed := ?_
    signed_curvature := ?_
  }
  · exact (continuous_const.add (continuous_const.mul Real.continuous_sin)).continuousOn
  · exact (continuous_const.sub (continuous_const.mul Real.continuous_cos)).continuousOn
  · exact (continuous_const.mul Real.continuous_cos).continuousOn
  · exact (continuous_const.mul Real.continuous_sin).continuousOn
  · intro t _ht
    change HasDerivAt (fun u => center.1 + r * sin u) (r * cos t) t
    have hraw := (hasDerivAt_const t center.1).add
      ((Real.hasDerivAt_sin t).const_mul r)
    have hderiv :
        HasDerivAt ((fun _ : ℝ => center.1) + fun y => r * sin y)
          (r * cos t) t := hraw.congr_deriv (by ring)
    apply hderiv.congr_of_eventuallyEq
    filter_upwards
    intro u
    rfl
  · intro t _ht
    change HasDerivAt (fun u => center.2 - r * cos u) (r * sin t) t
    have hraw := (hasDerivAt_const t center.2).sub
      ((Real.hasDerivAt_cos t).const_mul r)
    have hderiv :
        HasDerivAt ((fun _ : ℝ => center.2) - fun y => r * cos y)
          (r * sin t) t := hraw.congr_deriv (by ring)
    apply hderiv.congr_of_eventuallyEq
    filter_upwards
    intro u
    rfl
  · intro t _ht
    simpa only [velocity, acceleration] using
      ((Real.hasDerivAt_cos t).const_mul r).congr_deriv (by ring)
  · intro t _ht
    simpa only [velocity, acceleration] using
      (Real.hasDerivAt_sin t).const_mul r
  · intro t _ht
    rw [speed_eq hr]
    exact hr
  · intro t _ht
    rw [speed_eq hr]
    simp only [velocity, acceleration]
    have htrig := Real.sin_sq_add_cos_sq t
    field_simp [hr.ne']
    nlinarith

/-- Two independently translated circular graph arcs have the same derived
nonzero curvature and both feed the retained closed-circle implementation. -/
theorem equalCurvature_pair {r : ℝ} (hr : 0 < r) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
        (trace (0, 0) r) (velocity r) (acceleration r)
        (1 / r) (-(π / 3)) (π / 3) ∧
      CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
        (trace (3, 2) r) (velocity r) (acceleration r)
        (1 / r) (-(π / 3)) (π / 3) :=
  ⟨application (0, 0) hr, application (3, 2) hr⟩

end CircularGraphExamples
end CMVTwoPatchGraphVariation
