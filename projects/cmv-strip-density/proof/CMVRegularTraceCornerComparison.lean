/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVLiteralCornerShortening
import CMVLocalGraphSurgery
import Mathlib.Analysis.Calculus.Deriv.Slope
import CMVRegularParametricArclength

/-!
# Regular-trace nontransverse corner comparison

This module supplies the parameterization-invariant analytic and localization
layer needed to pass from literal polygonal corner cuts to regular boundary
traces.  It is source-located at Cañete--Miranda--Vittone, Proposition 2.14:
the regular-trace hypotheses preceding the proposition define endpoint
conormals intrinsically along the incident and interface pieces.  No contact
law, first variation, circle, common radius, finite component inventory, or
source-minimality transfer is assumed here.

A trace is differentiated as a planar vector.  Consequently horizontal and
vertical tangencies are both covered without dividing by either coordinate
derivative.  The open local competitor is the existing literal `openSpliceIn`;
all of its complete frontier is accounted for, including the cutting locus.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval ENNReal symmDiff ComplexConjugate

noncomputable section

namespace CMVRelaxation.RegularTraceCornerComparison

/-- Euclidean realization of a coordinate-plane vector. -/
def complexVector (v : PlanePoint) : ℂ := (v.1 : ℂ) + v.2 * Complex.I

@[simp] theorem complexVector_re (v : PlanePoint) : (complexVector v).re = v.1 := by
  simp [complexVector]

@[simp] theorem complexVector_im (v : PlanePoint) : (complexVector v).im = v.2 := by
  simp [complexVector]

@[simp] theorem complexVector_zero : complexVector (0, 0) = 0 := by
  simp [complexVector]

lemma complexVector_injective : Function.Injective complexVector := by
  intro v w h
  apply Prod.ext
  · simpa using congrArg Complex.re h
  · simpa using congrArg Complex.im h

/-- Euclidean speed, independent of a graph axis. -/
def euclideanSpeed (v : PlanePoint) : ℝ := ‖complexVector v‖

lemma euclideanSpeed_nonneg (v : PlanePoint) : 0 ≤ euclideanSpeed v := norm_nonneg _

lemma euclideanSpeed_pos {v : PlanePoint} (hv : v ≠ (0, 0)) :
    0 < euclideanSpeed v := by
  rw [euclideanSpeed, norm_pos_iff]
  exact fun h => hv (complexVector_injective (h.trans complexVector_zero.symm))

/-- Euclidean scalar product in source coordinates. -/
def planeInner (u v : PlanePoint) : ℝ := u.1 * v.1 + u.2 * v.2

/-- Unit tangent associated with a nonzero parameter velocity. -/
def unitTangent (v : PlanePoint) : PlanePoint :=
  (v.1 / euclideanSpeed v, v.2 / euclideanSpeed v)

/-- Whether the contact is the initial or terminal endpoint of an oriented
trace.  The conormal points out of the parameter interval. -/
inductive EndpointOrientation where
  | initial
  | terminal
  deriving DecidableEq

/-- Outward endpoint conormal of an oriented regular planar trace. -/
def endpointConormal (orientation : EndpointOrientation) (v : PlanePoint) : PlanePoint :=
  match orientation with
  | .initial => (- (unitTangent v).1, - (unitTangent v).2)
  | .terminal => unitTangent v

lemma planeInner_unitTangent_self {v : PlanePoint} (hv : v ≠ (0, 0)) :
    planeInner (unitTangent v) (unitTangent v) = 1 := by
  have hspos := euclideanSpeed_pos hv
  have hsne : euclideanSpeed v ≠ 0 := ne_of_gt hspos
  have hsquare : euclideanSpeed v ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
    rw [euclideanSpeed, complexVector, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  simp only [planeInner, unitTangent]
  field_simp [hsne]
  nlinarith

lemma endpointConormal_unit {orientation : EndpointOrientation}
    {v : PlanePoint} (hv : v ≠ (0, 0)) :
    planeInner (endpointConormal orientation v)
      (endpointConormal orientation v) = 1 := by
  cases orientation <;>
    simpa [endpointConormal, planeInner] using planeInner_unitTangent_self hv

/-- A `C¹` planar trace germ with a nonzero endpoint velocity.  The derivative
is stored in source coordinates, but the analytic trace is differentiated in
`ℂ`, whose norm is the Euclidean planar norm. -/
structure RegularEndpointTrace (junction : PlanePoint) where
  curve : ℝ → PlanePoint
  velocity : PlanePoint
  curve_zero : curve 0 = junction
  complex_contDiff : ContDiff ℝ 1 (fun t => complexVector (curve t))
  hasDerivAt_zero : HasDerivAt (fun t => complexVector (curve t))
    (complexVector velocity) 0
  velocity_ne : velocity ≠ (0, 0)

namespace RegularEndpointTrace

variable {junction : PlanePoint} (T : RegularEndpointTrace junction)
/-- The stored complex `C¹` regularity recovers `C¹` regularity of the source
coordinate trace. -/
theorem curve_contDiff : ContDiff ℝ 1 T.curve := by
  have hre : ContDiff ℝ 1
      (fun t => (complexVector (T.curve t)).re) :=
    Complex.reCLM.contDiff.comp T.complex_contDiff
  have him : ContDiff ℝ 1
      (fun t => (complexVector (T.curve t)).im) :=
    Complex.imCLM.contDiff.comp T.complex_contDiff
  simpa only [complexVector_re, complexVector_im] using hre.prodMk him

/-- In particular, every stored endpoint trace is continuous. -/
theorem curve_continuous : Continuous T.curve :=
  T.curve_contDiff.continuous


/-- Actual Euclidean speed of the parameterized trace. -/
def speed (t : ℝ) : ℝ := ‖deriv (fun u => complexVector (T.curve u)) t‖

/-- Parameterized Euclidean length from the junction to parameter `r`. -/
def arcLength (r : ℝ) : ℝ := ∫ t in 0..r, T.speed t

lemma deriv_complexCurve_zero :
    deriv (fun t => complexVector (T.curve t)) 0 = complexVector T.velocity :=
  T.hasDerivAt_zero.deriv

lemma speed_continuous : Continuous T.speed := by
  unfold speed
  exact (T.complex_contDiff.continuous_deriv (by norm_num)).norm
/-- The coordinate speed in the generic parametric arclength theorem is
exactly the complex-derivative speed stored for endpoint traces. -/
theorem euclideanParametricSpeed_curve_eq_speed (t : ℝ) :
    euclideanParametricSpeed T.curve t = T.speed t := by
  have hz : DifferentiableAt ℝ
      (fun u => complexVector (T.curve u)) t :=
    T.complex_contDiff.differentiable (by norm_num) t
  have hreDeriv :
      deriv (fun u => (T.curve u).1) t =
        (deriv (fun u => complexVector (T.curve u)) t).re := by
    have hcomp := Complex.reCLM.hasFDerivAt.comp t hz.hasFDerivAt
    have hderiv := hcomp.hasDerivAt.deriv
    have hfun :
        Complex.reCLM ∘ (fun u => complexVector (T.curve u)) =
          fun u => (T.curve u).1 := by
      funext u
      simp only [Function.comp_apply, Complex.reCLM_apply, complexVector_re]
    rw [hfun] at hderiv
    simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, deriv]
      using hderiv
  have himDeriv :
      deriv (fun u => (T.curve u).2) t =
        (deriv (fun u => complexVector (T.curve u)) t).im := by
    have hcomp := Complex.imCLM.hasFDerivAt.comp t hz.hasFDerivAt
    have hderiv := hcomp.hasDerivAt.deriv
    have hfun :
        Complex.imCLM ∘ (fun u => complexVector (T.curve u)) =
          fun u => (T.curve u).2 := by
      funext u
      simp only [Function.comp_apply, Complex.imCLM_apply, complexVector_im]
    rw [hfun] at hderiv
    simpa only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply, deriv]
      using hderiv
  unfold euclideanParametricSpeed speed
  rw [Complex.norm_def, Complex.normSq_apply, hreDeriv, himDeriv]
  congr 1
  ring


lemma speed_zero : T.speed 0 = euclideanSpeed T.velocity := by
  rw [speed, T.deriv_complexCurve_zero]
  rfl
/-- Nonzero endpoint velocity and `C¹` regularity derive a positive interval
on which the whole germ has nonvanishing speed. -/
theorem exists_speed_pos_radius :
    ∃ ρ > 0, ∀ t ∈ Icc 0 ρ, 0 < T.speed t := by
  have hzero : 0 < T.speed 0 := by
    rw [T.speed_zero]
    exact euclideanSpeed_pos T.velocity_ne
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < T.speed t :=
    T.speed_continuous.continuousAt.eventually (Ioi_mem_nhds hzero)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro t ht
  apply hball
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  linarith [ht.2]

/-- Exact Euclidean `H¹` mass of a regular injective half-open endpoint trace.
The right side is intrinsic parametric arclength, not a graph surrogate. -/
theorem hausdorffMeasure_curve_Ico_eq_arcLength_sub
    {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn T.curve (Icc a b))
    (hregular : ∀ t ∈ Icc a b, 0 < T.speed t) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (T.curve '' Ico a b)) =
      ENNReal.ofReal (T.arcLength b - T.arcLength a) := by
  rw [arcLength, arcLength,
    intervalIntegral.integral_interval_sub_left
      (T.speed_continuous.intervalIntegrable 0 b)
      (T.speed_continuous.intervalIntegrable 0 a)]
  simpa only [T.euclideanParametricSpeed_curve_eq_speed] using
    hausdorffMeasure_regularParametricCurve_Ico_eq_intervalIntegral_of_speed_pos
      T.curve_contDiff hab hinj
        (fun t ht => by
          rw [T.euclideanParametricSpeed_curve_eq_speed t]
          exact hregular t ht)


lemma arcLength_hasDerivAt_zero :
    HasDerivAt T.arcLength (euclideanSpeed T.velocity) 0 := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (T.speed_continuous.intervalIntegrable 0 0)
    T.speed_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    T.speed_continuous.continuousAt
  change HasDerivAt (fun r => ∫ t in 0..r, T.speed t)
    (euclideanSpeed T.velocity) 0
  simpa only [T.speed_zero] using h

/-- First-order length asymptotic for an arbitrary regular planar
parameterization. -/
theorem tendsto_arcLength_div :
    Tendsto (fun r => T.arcLength r / r) (𝓝[>] (0 : ℝ))
      (𝓝 (euclideanSpeed T.velocity)) := by
  have h := T.arcLength_hasDerivAt_zero.tendsto_slope_zero_right
  simpa [arcLength, div_eq_inv_mul] using h

/-- Actual Euclidean endpoint-to-endpoint shortcut length between two trace
germs on the same junction. -/
def shortcutLength (S : RegularEndpointTrace junction) (r : ℝ) : ℝ :=
  ‖complexVector (T.curve r) - complexVector (S.curve r)‖

/-- First-order chord asymptotic.  This uses the full vector derivatives and so
continues to apply when either coordinate derivative vanishes. -/
theorem tendsto_shortcutLength_div (S : RegularEndpointTrace junction) :
    Tendsto (fun r => T.shortcutLength S r / r) (𝓝[>] (0 : ℝ))
      (𝓝 ‖complexVector T.velocity - complexVector S.velocity‖) := by
  have hderiv : HasDerivAt
      (fun r => complexVector (T.curve r) - complexVector (S.curve r))
      (complexVector T.velocity - complexVector S.velocity) 0 :=
    T.hasDerivAt_zero.sub S.hasDerivAt_zero
  have hslope := hderiv.tendsto_slope_zero_right.norm
  apply hslope.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrpos : 0 < r := hr
  rw [zero_add, T.curve_zero, S.curve_zero, sub_self, sub_zero,
    shortcutLength, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hrpos, div_eq_inv_mul]

end RegularEndpointTrace

/-- First-order coefficient removed by joining the two moving endpoints with
one shortcut.  `incidentWeight`, `interfaceWeight`, and `shortcutWeight` are
literal density prices of the three traces. -/
def tangentGainCoefficient {junction : PlanePoint}
    (incident interface : RegularEndpointTrace junction)
    (incidentWeight interfaceWeight shortcutWeight : ℝ) : ℝ :=
  incidentWeight * euclideanSpeed incident.velocity +
    interfaceWeight * euclideanSpeed interface.velocity -
      shortcutWeight *
        ‖complexVector incident.velocity - complexVector interface.velocity‖

/-- Finite-scale weighted trace gain: removed incident and interface lengths
minus the inserted shortcut length. -/
def weightedTraceGain {junction : PlanePoint}
    (incident interface : RegularEndpointTrace junction)
    (incidentWeight interfaceWeight shortcutWeight r : ℝ) : ℝ :=
  incidentWeight * incident.arcLength r +
    interfaceWeight * interface.arcLength r -
      shortcutWeight * incident.shortcutLength interface r

/-- Complete first-order weighted-length asymptotic for regular endpoint
traces. -/
theorem tendsto_weightedTraceGain_div {junction : PlanePoint}
    (incident interface : RegularEndpointTrace junction)
    (incidentWeight interfaceWeight shortcutWeight : ℝ) :
    Tendsto
      (fun r => weightedTraceGain incident interface incidentWeight
        interfaceWeight shortcutWeight r / r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (tangentGainCoefficient incident interface incidentWeight
        interfaceWeight shortcutWeight)) := by
  have hi := incident.tendsto_arcLength_div.const_mul incidentWeight
  have hΓ := interface.tendsto_arcLength_div.const_mul interfaceWeight
  have hs := (incident.tendsto_shortcutLength_div interface).const_mul shortcutWeight
  convert (hi.add hΓ).sub hs using 1 <;>
    simp [weightedTraceGain, tangentGainCoefficient, sub_div, add_div,
      mul_div_assoc]

/-- A strictly positive tangent coefficient gives genuine shortening at every
sufficiently small positive scale. -/
theorem eventually_weightedTraceGain_pos {junction : PlanePoint}
    (incident interface : RegularEndpointTrace junction)
    (incidentWeight interfaceWeight shortcutWeight : ℝ)
    (hgain : 0 < tangentGainCoefficient incident interface incidentWeight
      interfaceWeight shortcutWeight) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      0 < weightedTraceGain incident interface incidentWeight
        interfaceWeight shortcutWeight r := by
  have hquot := (tendsto_weightedTraceGain_div incident interface
    incidentWeight interfaceWeight shortcutWeight).eventually
      (eventually_gt_nhds hgain)
  filter_upwards [hquot, self_mem_nhdsWithin] with r hquotient hr
  rcases (div_pos_iff.mp hquotient) with h | h
  · exact h.1
  · exact (not_lt_of_ge hr.le h.2).elim

lemma euclideanSpeed_horizontal_unit : euclideanSpeed (1, 0) = 1 := by
  norm_num [euclideanSpeed, complexVector]

lemma euclideanSpeed_vertical_unit : euclideanSpeed (0, 1) = 1 := by
  norm_num [euclideanSpeed, complexVector]

lemma rightAngle_velocity_difference_norm :
    ‖complexVector (0, 1) - complexVector (1, 0)‖ = Real.sqrt 2 := by
  rw [Complex.norm_def]
  congr 1
  norm_num [complexVector, Complex.normSq_apply]

/-- The regular-trace coefficient specializes to the strict exterior
`lambda = 2` right-angle gain from the literal predecessor gate. -/
theorem lambdaTwo_rightAngle_tangentGain_pos {junction : PlanePoint}
    (incident interface : RegularEndpointTrace junction)
    (hincident : incident.velocity = (0, 1))
    (hinterface : interface.velocity = (1, 0)) :
    0 < tangentGainCoefficient incident interface 2 1 2 := by
  rw [tangentGainCoefficient, hincident, hinterface,
    euclideanSpeed_vertical_unit, euclideanSpeed_horizontal_unit,
    rightAngle_velocity_difference_norm]
  linarith [LiteralCornerShortening.two_mul_sqrt_two_lt_three]

/-- The same right-angle cut also has a strict all-density-one tangent
coefficient. -/
theorem densityOne_rightAngle_tangentGain_pos {junction : PlanePoint}
    (incident interface : RegularEndpointTrace junction)
    (hincident : incident.velocity = (0, 1))
    (hinterface : interface.velocity = (1, 0)) :
    0 < tangentGainCoefficient incident interface 1 1 1 := by
  rw [tangentGainCoefficient, hincident, hinterface,
    euclideanSpeed_vertical_unit, euclideanSpeed_horizontal_unit,
    rightAngle_velocity_difference_norm]
  linarith [LiteralCornerShortening.sqrt_two_lt_two]

/-- The two physical strip interfaces, oriented toward the exterior phase. -/
inductive StripInterface where
  | upper
  | lower
  deriving DecidableEq

namespace StripInterface

/-- Source height of the selected interface. -/
def height : StripInterface → ℝ
  | .upper => 1
  | .lower => -1

/-- Unit normal pointing from the density-one strip to the exterior phase. -/
def exteriorNormal : StripInterface → PlanePoint
  | .upper => (0, 1)
  | .lower => (0, -1)

lemma exteriorNormal_unit (side : StripInterface) :
    planeInner side.exteriorNormal side.exteriorNormal = 1 := by
  cases side <;> norm_num [exteriorNormal, planeInner]

/-- One-sided displacement condition appearing before the contact inequality.
It is a geometric half-space condition, not an assumed force inequality. -/
def FeasibleExteriorDisplacement (side : StripInterface) (d : PlanePoint) : Prop :=
  0 < planeInner d side.exteriorNormal

lemma exteriorNormal_feasible (side : StripInterface) :
    side.FeasibleExteriorDisplacement side.exteriorNormal := by
  rw [FeasibleExteriorDisplacement, side.exteriorNormal_unit]
  norm_num

/-- A feasible displacement from the literal interface enters the exterior
constant-density phase at every positive scale. -/
theorem stripDensity_displaced_eq {lam r : ℝ} (side : StripInterface)
    {x : ℝ} {d : PlanePoint} (hd : side.FeasibleExteriorDisplacement d)
    (hr : 0 < r) :
    StripDensity lam (x + r * d.1, side.height + r * d.2) = lam := by
  cases side with
  | upper =>
      have hdy : 0 < d.2 := by simpa [FeasibleExteriorDisplacement,
        planeInner, exteriorNormal] using hd
      have hout : ¬|1 + r * d.2| ≤ 1 := by
        rw [abs_of_pos (by positivity)]
        nlinarith [mul_pos hr hdy]
      simp [height, StripDensity, hout]
  | lower =>
      have hdy : d.2 < 0 := by
        simpa [FeasibleExteriorDisplacement, planeInner, exteriorNormal] using hd
      have hneg : -1 + r * d.2 < 0 := by nlinarith [mul_neg_of_pos_of_neg hr hdy]
      have hout : ¬|-1 + r * d.2| ≤ 1 := by
        rw [abs_of_neg hneg]
        nlinarith [mul_neg_of_pos_of_neg hr hdy]
      simp [height, StripDensity, hout]

end StripInterface

/-- Source-regular incident and interface germs carried by one actual bounded
open representative.  Both parameterizations start at the contact, so their
outward endpoint conormals have `initial` orientation.  The hypotheses are
strictly local: no component count, global arc type, circle, radius, or contact
law is included. -/
structure ActualRegularTraceCorner (side : StripInterface) where
  representative : Set PlanePoint
  representative_isOpen : IsOpen representative
  representative_isBounded : Bornology.IsBounded representative
  junction : PlanePoint
  junction_on_interface : junction.2 = side.height
  radius : ℝ
  radius_pos : 0 < radius
  incident : RegularEndpointTrace junction
  interface : RegularEndpointTrace junction
  incident_on_frontier :
    incident.curve '' Icc 0 radius ⊆ frontier representative
  interface_on_frontier :
    interface.curve '' Icc 0 radius ⊆ frontier representative
  interface_on_strip :
    ∀ t ∈ Icc 0 radius, (interface.curve t).2 = side.height
  traces_meet_only_at_junction :
    (incident.curve '' Icc 0 radius) ∩
      (interface.curve '' Icc 0 radius) = {junction}

namespace ActualRegularTraceCorner

variable {side : StripInterface} (C : ActualRegularTraceCorner side)

/-- Intrinsic outward conormal of the incident trace at the contact. -/
def incidentConormal : PlanePoint :=
  endpointConormal .initial C.incident.velocity

/-- Intrinsic outward conormal of the interface trace at the contact. -/
def interfaceConormal : PlanePoint :=
  endpointConormal .initial C.interface.velocity

lemma incidentConormal_unit :
    planeInner C.incidentConormal C.incidentConormal = 1 :=
  endpointConormal_unit C.incident.velocity_ne

lemma interfaceConormal_unit :
    planeInner C.interfaceConormal C.interfaceConormal = 1 :=
  endpointConormal_unit C.interface.velocity_ne

/-- Every regular incident germ has a nonsingular horizontal-parameter or
vertical-parameter chart.  Only the nonzero coordinate is selected; neither
branch divides by the coordinate derivative that vanishes in the other
branch. -/
theorem incident_has_nonsingular_axis_chart :
    C.incident.velocity.1 ≠ 0 ∨ C.incident.velocity.2 ≠ 0 := by
  by_contra h
  push Not at h
  apply C.incident.velocity_ne
  ext <;> simp [h.1, h.2]

end ActualRegularTraceCorner

/-- Closed axis-aligned localization square. -/
def localizationSquare (center : PlanePoint) (radius : ℝ) : Set PlanePoint :=
  Icc (center.1 - radius) (center.1 + radius) ×ˢ
    Icc (center.2 - radius) (center.2 + radius)

lemma isClosed_localizationSquare (center : PlanePoint) (radius : ℝ) :
    IsClosed (localizationSquare center radius) :=
  isClosed_Icc.prod isClosed_Icc

lemma isBounded_localizationSquare (center : PlanePoint) (radius : ℝ) :
    Bornology.IsBounded (localizationSquare center radius) :=
  (isCompact_Icc.prod isCompact_Icc).isBounded

lemma volume_localizationSquare {center : PlanePoint} {radius : ℝ}
    (hradius : 0 ≤ radius) :
    volume (localizationSquare center radius) = ENNReal.ofReal (4 * radius ^ 2) := by
  rw [localizationSquare, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  rw [show center.1 + radius - (center.1 - radius) = 2 * radius by ring,
    show center.2 + radius - (center.2 - radius) = 2 * radius by ring,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * radius)]
  congr 1
  ring

/-- The actual open localized competitor.  The inserted local model is spliced
into the same bounded open representative rather than compared as a separate
whole specimen. -/
def localizedCompetitor (representative localModel window : Set PlanePoint) :
    Set PlanePoint :=
  openSpliceIn representative localModel window

lemma localizedCompetitor_isOpen (representative localModel window : Set PlanePoint) :
    IsOpen (localizedCompetitor representative localModel window) :=
  isOpen_openSpliceIn _ _ _

lemma spliceIn_subset_union (U G W : Set PlanePoint) :
    spliceIn U G W ⊆ U ∪ W := by
  intro p hp
  rcases hp with hp | hp
  · exact Or.inl hp.1
  · exact Or.inr hp.2

lemma localizedCompetitor_isBounded {U G W : Set PlanePoint}
    (hU : Bornology.IsBounded U) (hW : Bornology.IsBounded W) :
    Bornology.IsBounded (localizedCompetitor U G W) := by
  apply (hU.union hW).subset
  exact (openSpliceIn_subset_spliceIn U G W).trans (spliceIn_subset_union U G W)

/-- The canonical open splice differs from its source representative only
inside the literal closed localization window. -/
theorem localizedCompetitor_symmDiff_subset_window
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) :
    localizedCompetitor U G W ∆ U ⊆ W := by
  intro p hp
  by_cases hpW : p ∈ W
  · exact hpW
  have hpRaw : p ∈ spliceIn U G W ↔ p ∈ U := by
    change ((p ∈ U ∧ p ∉ W) ∨ (p ∈ G ∧ p ∈ W)) ↔ p ∈ U
    simp [hpW]
  have hpOpenRaw : p ∈ localizedCompetitor U G W ↔ p ∈ spliceIn U G W := by
    constructor
    · intro hpOpen
      exact openSpliceIn_subset_spliceIn U G W hpOpen
    · intro hpSplice
      by_contra hpOpen
      have hpFrontier := spliceIn_diff_openSpliceIn_subset_frontier hU hG
        ⟨hpSplice, hpOpen⟩
      exact hpW (hW.frontier_subset hpFrontier)
  rw [Set.mem_symmDiff, hpOpenRaw, hpRaw] at hp
  tauto

/-- Exact carrier and complete-frontier agreement outside the localization
window. -/
theorem localizedCompetitor_agrees_outside
    {U G W : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) :
    localizedCompetitor U G W ∩ Wᶜ = U ∩ Wᶜ ∧
      frontier (localizedCompetitor U G W) ∩ interior Wᶜ =
        frontier U ∩ interior Wᶜ := by
  have hcarrier : localizedCompetitor U G W ∩ Wᶜ = U ∩ Wᶜ := by
    ext p
    by_cases hpW : p ∈ W
    · simp [hpW]
    have hpRaw : p ∈ spliceIn U G W ↔ p ∈ U := by
      change ((p ∈ U ∧ p ∉ W) ∨ (p ∈ G ∧ p ∈ W)) ↔ p ∈ U
      simp [hpW]
    have hpOpenRaw : p ∈ localizedCompetitor U G W ↔ p ∈ spliceIn U G W := by
      constructor
      · intro hpOpen
        exact openSpliceIn_subset_spliceIn U G W hpOpen
      · intro hpSplice
        by_contra hpOpen
        have hpFrontier := spliceIn_diff_openSpliceIn_subset_frontier hU hG
          ⟨hpSplice, hpOpen⟩
        exact hpW (hW.frontier_subset hpFrontier)
    simp only [mem_inter_iff, mem_compl_iff]
    rw [hpOpenRaw, hpRaw]
  refine ⟨hcarrier, ?_⟩
  apply frontier_inter_eq_of_inter_open_eq isOpen_interior
  calc
    localizedCompetitor U G W ∩ interior Wᶜ =
        (localizedCompetitor U G W ∩ Wᶜ) ∩ interior Wᶜ := by
      ext p
      constructor
      · rintro ⟨hp, hpInt⟩
        exact ⟨⟨hp, interior_subset hpInt⟩, hpInt⟩
      · rintro ⟨⟨hp, _⟩, hpInt⟩
        exact ⟨hp, hpInt⟩
    _ = (U ∩ Wᶜ) ∩ interior Wᶜ := by rw [hcarrier]
    _ = U ∩ interior Wᶜ := by
      ext p
      constructor
      · rintro ⟨⟨hp, _⟩, hpInt⟩
        exact ⟨hp, hpInt⟩
      · rintro ⟨hp, hpInt⟩
        exact ⟨⟨hp, interior_subset hpInt⟩, hpInt⟩

/-- Full complete-frontier accounting for a collar-compatible local model.
The cutting boundary belongs to the unchanged term; no artificial trace is
silently dropped. -/
theorem localizedCompetitor_frontier_eq_piecewise
    {U G W N : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W)
    (hN : IsOpen N) (hfrontier : frontier W ⊆ N)
    (hlocal : U ∩ N = G ∩ N) :
    frontier (localizedCompetitor U G W) =
      (frontier G ∩ interior W) ∪
        (frontier U ∩ (interior W)ᶜ) := by
  rw [localizedCompetitor,
    frontier_openSpliceIn_eq_frontier_spliceIn hU hG hW hregular]
  have hins : frontier (spliceIn U G W) ∩ interior W =
      frontier G ∩ interior W :=
    frontier_inter_eq_of_inter_open_eq isOpen_interior
      (spliceIn_inter_interior U G W)
  have hout : frontier (spliceIn U G W) ∩ (interior W)ᶜ =
      frontier U ∩ (interior W)ᶜ := by
    let O := interior Wᶜ ∪ N
    have hO : IsOpen O := isOpen_interior.union hN
    have hcompl : (interior W)ᶜ ⊆ O :=
      compl_interior_subset_interior_compl_union hW hfrontier
    have hlocalO : spliceIn U G W ∩ O = U ∩ O := by
      ext p
      have hInt := Set.ext_iff.mp (spliceIn_inter_interior_compl U G W) p
      have hNear := Set.ext_iff.mp
        (spliceIn_inter_eq_of_agree (W := W) hlocal) p
      simp only [O, mem_inter_iff, mem_union] at hInt hNear ⊢
      tauto
    have hfrontO : frontier (spliceIn U G W) ∩ O = frontier U ∩ O :=
      frontier_inter_eq_of_inter_open_eq hO hlocalO
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
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpInt : p ∈ interior W
    · exact Or.inl ((Set.ext_iff.mp hins p).mp ⟨hp, hpInt⟩)
    · exact Or.inr ((Set.ext_iff.mp hout p).mp ⟨hp, hpInt⟩)
  · rintro p (hp | hp)
    · exact ((Set.ext_iff.mp hins p).mpr hp).1
    · exact ((Set.ext_iff.mp hout p).mpr hp).1

/-- Exact complete-cost split corresponding to the piecewise frontier
identity. -/
theorem localizedCompetitor_complete_cost
    (lam : ℝ) {U G W N : Set PlanePoint} (hU : IsOpen U) (hG : IsOpen G)
    (hW : IsClosed W) (hregular : closure (interior W) = W)
    (hN : IsOpen N) (hfrontier : frontier W ⊆ N)
    (hlocal : U ∩ N = G ∩ N) :
    smoothCost lam (localizedCompetitor U G W) =
      smoothCostOn lam G (interior W) +
        smoothCostOn lam U (interior W)ᶜ := by
  rw [localizedCompetitor,
    smoothCost_openSpliceIn_eq_smoothCost_spliceIn lam hU hG hW hregular,
    smoothCost_spliceIn_eq_inside_add_outside lam hW hN hfrontier hlocal]

/-- Strip density is bounded by the exterior weight when `1 ≤ lambda`. -/
lemma abs_stripDensity_le {lam : ℝ} (hlam : 1 ≤ lam) (p : PlanePoint) :
    |StripDensity lam p| ≤ lam := by
  have hlam_nonneg : 0 ≤ lam := zero_le_one.trans hlam
  by_cases hstrip : |p.2| ≤ 1
  · simp [StripDensity, hstrip, hlam]
  · simp [StripDensity, hstrip, abs_of_nonneg hlam_nonneg]

/-- An actual pair of measurable carriers that differs only inside a square of
radius `M*r` has quadratic weighted-area defect. -/
theorem weightedArea_defect_le_localizationSquare
    {lam M r : ℝ} {center : PlanePoint}
    (hlam : 1 ≤ lam) (hM : 0 ≤ M) (hr : 0 ≤ r)
    {E F : Set PlanePoint} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEbounded : Bornology.IsBounded E) (hFbounded : Bornology.IsBounded F)
    (hEF : E ∆ F ⊆ localizationSquare center (M * r)) :
    |WeightedArea lam E - WeightedArea lam F| ≤ 4 * lam * M ^ 2 * r ^ 2 := by
  have hfiniteSquare : volume (localizationSquare center (M * r)) < ⊤ := by
    rw [volume_localizationSquare (mul_nonneg hM hr)]
    exact ENNReal.ofReal_lt_top
  have hfiniteDiff : volume (E ∆ F) < ⊤ :=
    (measure_mono hEF).trans_lt hfiniteSquare
  have hIntE : IntegrableOn (StripDensity lam) E :=
    stripDensity_integrableOn_of_volume_ne_top lam hEbounded.measure_lt_top.ne
  have hIntF : IntegrableOn (StripDensity lam) F :=
    stripDensity_integrableOn_of_volume_ne_top lam hFbounded.measure_lt_top.ne
  rw [WeightedArea, WeightedArea, ← integral_indicator hE,
    ← integral_indicator hF,
    ← integral_sub (hIntE.integrable_indicator hE)
      (hIntF.integrable_indicator hF)]
  let d : PlanePoint → ℝ :=
    E.indicator (StripDensity lam) - F.indicator (StripDensity lam)
  have hdSupport : ∫ p, d p = ∫ p in E ∆ F, d p := by
    rw [← integral_indicator (hE.symmDiff hF)]
    apply integral_congr_ae
    filter_upwards with p
    simp only [d, Pi.sub_apply]
    by_cases hpE : p ∈ E <;> by_cases hpF : p ∈ F <;>
      simp [hpE, hpF, Set.mem_symmDiff]
  change |∫ p, d p| ≤ 4 * lam * M ^ 2 * r ^ 2
  rw [hdSupport]
  have hbound :
      ‖∫ p in E ∆ F, d p‖ ≤ lam * volume.real (E ∆ F) := by
    apply norm_setIntegral_le_of_norm_le_const (f := d) hfiniteDiff
    intro p hp
    rcases hp with hp | hp
    · rw [show d p = E.indicator (StripDensity lam) p -
          F.indicator (StripDensity lam) p by rfl,
        indicator_of_mem hp.1, indicator_of_notMem hp.2]
      simpa [Real.norm_eq_abs] using abs_stripDensity_le hlam p
    · rw [show d p = E.indicator (StripDensity lam) p -
          F.indicator (StripDensity lam) p by rfl,
        indicator_of_notMem hp.2, indicator_of_mem hp.1]
      simpa [Real.norm_eq_abs] using abs_stripDensity_le hlam p
  calc
    |∫ p in E ∆ F, d p| ≤ lam * volume.real (E ∆ F) := hbound
    _ ≤ lam * volume.real (localizationSquare center (M * r)) := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono hEF hfiniteSquare.ne) (zero_le_one.trans hlam)
    _ = 4 * lam * M ^ 2 * r ^ 2 := by
      rw [Measure.real, volume_localizationSquare (mul_nonneg hM hr),
        ENNReal.toReal_ofReal]
      · ring
      · positivity

/-- Quadratic area control for the constructed open competitor on the same
bounded open representative. -/
theorem localizedCompetitor_weightedArea_defect_le
    {lam M r : ℝ} {center : PlanePoint} {U G W : Set PlanePoint}
    (hlam : 1 ≤ lam) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hU : IsOpen U) (hG : IsOpen G) (hW : IsClosed W)
    (hUbounded : Bornology.IsBounded U) (hWbounded : Bornology.IsBounded W)
    (hlocalization : W ⊆ localizationSquare center (M * r)) :
    |WeightedArea lam (localizedCompetitor U G W) - WeightedArea lam U| ≤
      4 * lam * M ^ 2 * r ^ 2 := by
  apply weightedArea_defect_le_localizationSquare hlam hM hr
    (localizedCompetitor_isOpen U G W).measurableSet hU.measurableSet
    (localizedCompetitor_isBounded hUbounded hWbounded) hUbounded
  exact (localizedCompetitor_symmDiff_subset_window hU hG hW).trans hlocalization

end CMVRelaxation.RegularTraceCornerComparison
