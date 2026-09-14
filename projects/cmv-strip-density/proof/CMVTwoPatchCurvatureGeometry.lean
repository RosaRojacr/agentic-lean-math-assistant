/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTwoPatchStationarity
import CMVCurvatureIntegration

/-!
# From constrained graph stationarity to supporting geometry

This module connects the occupied-side graph curvature derived from exact-area
two-patch variations to the arbitrary-speed curvature integration interface.
Graph-functional local minimality remains an explicit hypothesis; no transfer
from relaxed source minimality is asserted here.
-/

open Set Function
open scoped Topology ContDiff

noncomputable section
namespace CMVTwoPatchGraphVariation

namespace GraphPatch

/-- The actual graph trace in increasing horizontal coordinate. -/
def graphTrace (P : GraphPatch) (x : ℝ) : PlanePoint :=
  (x, P.graph x)

/-- Actual coordinate velocity of the increasing graph trace. -/
def graphVelocity (P : GraphPatch) (x : ℝ) : PlanePoint :=
  (1, deriv P.graph x)

/-- Actual coordinate acceleration of the increasing graph trace. -/
def graphAcceleration (P : GraphPatch) (x : ℝ) : PlanePoint :=
  (0, deriv (deriv P.graph) x)

@[simp] theorem graphTrace_fst (P : GraphPatch) (x : ℝ) :
    (P.graphTrace x).1 = x := rfl

@[simp] theorem graphTrace_snd (P : GraphPatch) (x : ℝ) :
    (P.graphTrace x).2 = P.graph x := rfl

@[simp] theorem graphVelocity_fst (P : GraphPatch) (x : ℝ) :
    (P.graphVelocity x).1 = 1 := rfl

@[simp] theorem graphVelocity_snd (P : GraphPatch) (x : ℝ) :
    (P.graphVelocity x).2 = deriv P.graph x := rfl

@[simp] theorem graphAcceleration_fst (P : GraphPatch) (x : ℝ) :
    (P.graphAcceleration x).1 = 0 := rfl

@[simp] theorem graphAcceleration_snd (P : GraphPatch) (x : ℝ) :
    (P.graphAcceleration x).2 = deriv (deriv P.graph) x := rfl

/-- The Euclidean speed of a graph in horizontal coordinate is the literal
square-root graph-length density. -/
theorem euclideanSpeed_graphVelocity (P : GraphPatch) (x : ℝ) :
    CMVCurvatureIntegration.euclideanSpeed P.graphVelocity x =
      Real.sqrt (1 + (deriv P.graph x) ^ 2) := by
  simp [CMVCurvatureIntegration.euclideanSpeed, graphVelocity]

/-- Constant occupied-side curvature gives the signed traversal curvature
required by the arbitrary-speed integration interface.  The conversion factor
is exactly the occupied-side sign. -/
theorem arbitrarySpeedConstantCurvatureOn_graph
    (P : GraphPatch) {K : ℝ}
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      P.graphTrace P.graphVelocity P.graphAcceleration
      (P.side.areaSign * K) P.a P.b where
  start_lt_finish := P.a_lt_b
  curvature_ne_zero := mul_ne_zero P.side.areaSign_ne_zero hKne
  trace_fst_continuous := continuous_id.continuousOn
  trace_snd_continuous := P.graph_contDiff.continuous.continuousOn
  velocity_fst_continuous := continuous_const.continuousOn
  velocity_snd_continuous :=
    (P.graph_contDiff.continuous_deriv (by norm_num)).continuousOn
  trace_fst_derivative := by
    intro x _hx
    simpa [graphTrace] using hasDerivAt_id' x
  trace_snd_derivative := by
    intro x _hx
    simpa [graphTrace] using
      (P.graph_contDiff.differentiable (by norm_num) x).hasDerivAt
  velocity_fst_derivative := by
    intro x _hx
    simpa [graphVelocity, graphAcceleration] using
      (hasDerivAt_const x (1 : ℝ))
  velocity_snd_derivative := by
    intro x _hx
    simpa [graphVelocity, graphAcceleration] using
      (P.graph_deriv_contDiff.differentiable (by norm_num) x).hasDerivAt
  positive_speed := by
    intro x _hx
    rw [P.euclideanSpeed_graphVelocity]
    positivity
  signed_curvature := by
    intro x hx
    simp only [graphVelocity, graphAcceleration,
      CMVCurvatureIntegration.euclideanSpeed, one_pow, one_mul, mul_zero,
      sub_zero]
    change deriv (deriv P.graph) x =
      (P.side.areaSign * K) * Real.sqrt (1 + deriv P.graph x ^ 2) ^ 3
    have hroot : Real.sqrt (1 + (deriv P.graph x) ^ 2) ≠ 0 := by
      positivity
    have hcurv := hK x hx
    unfold orientedGraphCurvature graphCurvature at hcurv
    field_simp [hroot] at hcurv
    calc
      deriv (deriv P.graph) x =
          1 * deriv (deriv P.graph) x := by ring
      _ = (P.side.areaSign * P.side.areaSign) *
            deriv (deriv P.graph) x := by
              rw [P.side.areaSign_mul_self]
      _ = P.side.areaSign *
            (P.side.areaSign * deriv (deriv P.graph) x) := by ring
      _ = P.side.areaSign *
            (Real.sqrt (1 + deriv P.graph x ^ 2) ^ 3 * K) := by
              rw [hcurv]
      _ = (P.side.areaSign * K) *
            Real.sqrt (1 + deriv P.graph x ^ 2) ^ 3 := by ring

/-- Nonzero occupied-side curvature puts every closed graph point, including
both endpoints, on the supporting circle produced by the retained
arbitrary-speed implementation. -/
theorem closed_graph_circle_identity
    (P : GraphPatch) {K s x : ℝ}
    (hK : ∀ y ∈ Ioo P.a P.b, P.orientedGraphCurvature y = K)
    (hKne : K ≠ 0) (hs : s ∈ Icc P.a P.b) (hx : x ∈ Icc P.a P.b) :
    ((P.graphTrace x).1 -
        (CMVCurvatureIntegration.centerInvariant P.graphTrace
          (CMVCurvatureIntegration.normalizedTangent P.graphVelocity)
          (P.side.areaSign * K) s).1) ^ 2 +
      ((P.graphTrace x).2 -
        (CMVCurvatureIntegration.centerInvariant P.graphTrace
          (CMVCurvatureIntegration.normalizedTangent P.graphVelocity)
          (P.side.areaSign * K) s).2) ^ 2 =
        (1 / (P.side.areaSign * K)) ^ 2 :=
  (P.arbitrarySpeedConstantCurvatureOn_graph hK hKne).closed_circle_identity hs hx

/-- Zero occupied-side curvature gives one supporting affine line on the whole
closed graph interval.  Endpoint derivatives are not assumed. -/
theorem graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    (P : GraphPatch)
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = 0) :
    ∀ x ∈ Icc P.a P.b,
      P.graph x = P.graph P.a + deriv P.graph P.a * (x - P.a) := by
  have hsecond : ∀ x ∈ Ioo P.a P.b,
      HasDerivAt (deriv P.graph) 0 x := by
    intro x hx
    have hz := hK x hx
    have hden : Real.sqrt (1 + deriv P.graph x ^ 2) ^ 3 ≠ 0 := by
      positivity
    unfold orientedGraphCurvature graphCurvature at hz
    have hderiv : deriv (deriv P.graph) x = 0 := by
      have hfrac := (mul_eq_zero.mp hz).resolve_left P.side.areaSign_ne_zero
      exact (div_eq_zero_iff.mp hfrac).resolve_right hden
    exact (P.graph_deriv_contDiff.differentiable
      (by norm_num) x).hasDerivAt.congr_deriv hderiv
  have hslope : Set.EqOn (deriv P.graph)
      (fun _ => deriv P.graph P.a) (Icc P.a P.b) :=
    CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero P.a_lt_b
      (P.graph_deriv_contDiff.continuous.continuousOn) hsecond
  let affineResidual : ℝ → ℝ := fun x =>
    P.graph x - deriv P.graph P.a * x
  have hresidualDeriv : ∀ x ∈ Ioo P.a P.b,
      HasDerivAt affineResidual 0 x := by
    intro x hx
    have hraw :=
      (P.graph_contDiff.differentiable (by norm_num) x).hasDerivAt.sub
        ((hasDerivAt_id x).const_mul (deriv P.graph P.a))
    exact hraw.congr_deriv (by
      rw [hslope ⟨hx.1.le, hx.2.le⟩]
      ring)
  have hresidual : Set.EqOn affineResidual
      (fun _ => affineResidual P.a) (Icc P.a P.b) :=
    CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero P.a_lt_b
      ((P.graph_contDiff.continuous.sub
        (continuous_const.mul continuous_id)).continuousOn)
      hresidualDeriv
  intro x hx
  have heq := hresidual hx
  dsimp only [affineResidual] at heq
  linarith

end GraphPatch

/-- Direction of a regular graph reparameterization. -/
inductive TraversalDirection where
  | increasing
  | decreasing
  deriving DecidableEq

namespace TraversalDirection

/-- Sign relating parameter direction to increasing horizontal traversal. -/
def sign : TraversalDirection → ℝ
  | .increasing => 1
  | .decreasing => -1

@[simp] theorem sign_increasing : TraversalDirection.increasing.sign = (1 : ℝ) := rfl

@[simp] theorem sign_decreasing : TraversalDirection.decreasing.sign = (-1 : ℝ) := rfl

theorem sign_ne_zero (direction : TraversalDirection) : direction.sign ≠ 0 := by
  cases direction <;> norm_num [sign]

theorem sign_mul_self (direction : TraversalDirection) :
    direction.sign * direction.sign = (1 : ℝ) := by
  cases direction <;> norm_num [sign]

end TraversalDirection

/-- A regular `C²` increasing or decreasing parameter change whose closed and
open parameter intervals map into the corresponding graph intervals. -/
structure RegularGraphParameterChange (P : GraphPatch) where
  start : ℝ
  finish : ℝ
  parameter : ℝ → ℝ
  direction : TraversalDirection
  start_lt_finish : start < finish
  parameter_contDiff : ContDiff ℝ 2 parameter
  maps_closed : MapsTo parameter (Icc start finish) (Icc P.a P.b)
  maps_open : MapsTo parameter (Ioo start finish) (Ioo P.a P.b)
  derivative_sign : ∀ t ∈ Icc start finish,
    match direction with
    | .increasing => 0 < deriv parameter t
    | .decreasing => deriv parameter t < 0

namespace RegularGraphParameterChange

variable {P : GraphPatch}

lemma parameter_deriv_contDiff (R : RegularGraphParameterChange P) :
    ContDiff ℝ 1 (deriv R.parameter) :=
  (contDiff_succ_iff_deriv.mp R.parameter_contDiff).2.2

lemma parameter_deriv_ne_zero (R : RegularGraphParameterChange P)
    {t : ℝ} (ht : t ∈ Icc R.start R.finish) :
    deriv R.parameter t ≠ 0 := by
  cases hdirection : R.direction with
  | increasing =>
      exact ne_of_gt (by
        simpa only [hdirection] using R.derivative_sign t ht)
  | decreasing =>
      exact ne_of_lt (by
        simpa only [hdirection] using R.derivative_sign t ht)


/-- Increasing horizontal-coordinate parameterization of a graph patch. -/
def identity (P : GraphPatch) : RegularGraphParameterChange P where
  start := P.a
  finish := P.b
  parameter := id
  direction := .increasing
  start_lt_finish := P.a_lt_b
  parameter_contDiff := contDiff_id
  maps_closed := by
    intro x hx
    simpa only [id_eq] using hx
  maps_open := by
    intro x hx
    simpa only [id_eq] using hx
  derivative_sign := by
    intro t _ht
    simp only
    rw [(hasDerivAt_id t).deriv]
    norm_num

/-- The same horizontal interval traversed in the decreasing direction. -/
def reflection (P : GraphPatch) : RegularGraphParameterChange P where
  start := P.a
  finish := P.b
  parameter := fun t => P.a + P.b - t
  direction := .decreasing
  start_lt_finish := P.a_lt_b
  parameter_contDiff := by fun_prop
  maps_closed := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  maps_open := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  derivative_sign := by
    intro t _ht
    simp only
    have hderiv :
        HasDerivAt (fun u : ℝ => P.a + P.b - u) (-1) t := by
      simpa only [id_eq] using!
        (hasDerivAt_id t).const_sub (P.a + P.b)
    rw [hderiv.deriv]
    norm_num
end RegularGraphParameterChange

namespace GraphPatch

/-- A graph trace after an actual regular parameter change. -/
def reparameterizedTrace (P : GraphPatch)
    (R : RegularGraphParameterChange P) (t : ℝ) : PlanePoint :=
  P.graphTrace (R.parameter t)

/-- Actual first coordinate derivatives after a regular parameter change. -/
def reparameterizedVelocity (P : GraphPatch)
    (R : RegularGraphParameterChange P) (t : ℝ) : PlanePoint :=
  (deriv R.parameter t,
    deriv P.graph (R.parameter t) * deriv R.parameter t)

/-- Actual second coordinate derivatives after a regular parameter change. -/
def reparameterizedAcceleration (P : GraphPatch)
    (R : RegularGraphParameterChange P) (t : ℝ) : PlanePoint :=
  (deriv (deriv R.parameter) t,
    deriv (deriv P.graph) (R.parameter t) *
        (deriv R.parameter t) ^ 2 +
      deriv P.graph (R.parameter t) * deriv (deriv R.parameter) t)

/-- Speed scales by the absolute value of the actual parameter derivative. -/
theorem euclideanSpeed_reparameterizedVelocity
    (P : GraphPatch) (R : RegularGraphParameterChange P) (t : ℝ) :
    CMVCurvatureIntegration.euclideanSpeed
        (P.reparameterizedVelocity R) t =
      |deriv R.parameter t| *
        Real.sqrt (1 + (deriv P.graph (R.parameter t)) ^ 2) := by
  let speed := CMVCurvatureIntegration.euclideanSpeed
    (P.reparameterizedVelocity R) t
  let d := deriv R.parameter t
  let q := deriv P.graph (R.parameter t)
  let root := Real.sqrt (1 + q ^ 2)
  have hspeedSq :
      speed ^ 2 = d ^ 2 + (q * d) ^ 2 := by
    simpa only [speed, d, q, reparameterizedVelocity, Prod.fst, Prod.snd] using
      (CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn.speed_sq
        (velocity := P.reparameterizedVelocity R) t)
  have hrootSq : root ^ 2 = 1 + q ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have habsSq : |d| ^ 2 = d ^ 2 := sq_abs d
  have htargetSq : (|d| * root) ^ 2 = d ^ 2 + (q * d) ^ 2 := by
    rw [mul_pow, habsSq, hrootSq]
    ring
  have hspeedNonneg : 0 ≤ speed := by
    exact Real.sqrt_nonneg _
  have htargetNonneg : 0 ≤ |d| * root :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- The direction sign converts positive-speed orientation back to the signed
parameter derivative. -/
theorem signedEuclideanSpeed_reparameterizedVelocity
    (P : GraphPatch) (R : RegularGraphParameterChange P)
    {t : ℝ} (ht : t ∈ Icc R.start R.finish) :
    R.direction.sign *
        CMVCurvatureIntegration.euclideanSpeed
          (P.reparameterizedVelocity R) t =
      deriv R.parameter t *
        Real.sqrt (1 + (deriv P.graph (R.parameter t)) ^ 2) := by
  rw [P.euclideanSpeed_reparameterizedVelocity R t]
  cases hdirection : R.direction with
  | increasing =>
      have hd : 0 < deriv R.parameter t := by
        simpa only [hdirection] using R.derivative_sign t ht
      simp [abs_of_pos hd]
  | decreasing =>
      have hd : deriv R.parameter t < 0 := by
        simpa only [hdirection] using R.derivative_sign t ht
      rw [abs_of_neg hd]
      simp only [TraversalDirection.sign_decreasing]
      ring

/-- Regular increasing changes preserve traversal curvature; regular
decreasing changes reverse it.  Occupied-side orientation remains explicit. -/
theorem arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
    (P : GraphPatch) (R : RegularGraphParameterChange P) {K : ℝ}
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      (P.reparameterizedTrace R) (P.reparameterizedVelocity R)
      (P.reparameterizedAcceleration R)
      ((R.direction.sign * P.side.areaSign) * K) R.start R.finish := by
  refine {
    start_lt_finish := R.start_lt_finish
    curvature_ne_zero :=
      mul_ne_zero (mul_ne_zero R.direction.sign_ne_zero
        P.side.areaSign_ne_zero) hKne
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
  · simpa only [reparameterizedTrace, graphTrace] using
      R.parameter_contDiff.continuous.continuousOn
  · exact (P.graph_contDiff.continuous.comp
      R.parameter_contDiff.continuous).continuousOn
  · simpa only [reparameterizedVelocity] using
      (R.parameter_contDiff.continuous_deriv (by norm_num)).continuousOn
  · exact (((P.graph_contDiff.continuous_deriv (by norm_num)).comp
      R.parameter_contDiff.continuous).mul
        (R.parameter_contDiff.continuous_deriv (by norm_num))).continuousOn
  · intro t _ht
    simpa only [reparameterizedTrace, graphTrace, reparameterizedVelocity] using
      (R.parameter_contDiff.differentiable (by norm_num) t).hasDerivAt
  · intro t _ht
    have hparameter :=
      (R.parameter_contDiff.differentiable (by norm_num) t).hasDerivAt
    have hgraph :=
      (P.graph_contDiff.differentiable
        (by norm_num) (R.parameter t)).hasDerivAt
    simpa only [reparameterizedTrace, graphTrace, reparameterizedVelocity,
      Function.comp_def] using hgraph.comp t hparameter
  · intro t _ht
    simpa only [reparameterizedVelocity, reparameterizedAcceleration] using
      (R.parameter_deriv_contDiff.differentiable
        (by norm_num) t).hasDerivAt
  · intro t _ht
    have hparameter :=
      (R.parameter_contDiff.differentiable (by norm_num) t).hasDerivAt
    have hparameterDeriv :=
      (R.parameter_deriv_contDiff.differentiable
        (by norm_num) t).hasDerivAt
    have hgraphDeriv :=
      (P.graph_deriv_contDiff.differentiable
        (by norm_num) (R.parameter t)).hasDerivAt
    have hcomposed := hgraphDeriv.comp t hparameter
    change HasDerivAt
      (fun u => deriv P.graph (R.parameter u) * deriv R.parameter u)
      (deriv (deriv P.graph) (R.parameter t) *
          deriv R.parameter t ^ 2 +
        deriv P.graph (R.parameter t) *
          deriv (deriv R.parameter) t) t
    have hproduct := hcomposed.mul hparameterDeriv
    have heq :
        deriv (deriv P.graph) (R.parameter t) *
              deriv R.parameter t * deriv R.parameter t +
            (deriv P.graph ∘ R.parameter) t *
              deriv (deriv R.parameter) t =
          deriv (deriv P.graph) (R.parameter t) *
              deriv R.parameter t ^ 2 +
            deriv P.graph (R.parameter t) *
              deriv (deriv R.parameter) t := by
      simp only [Function.comp_apply]
      ring
    have hproduct' := hproduct.congr_deriv heq
    apply hproduct'.congr_of_eventuallyEq
    filter_upwards
    intro u
    rfl
  · intro t ht
    unfold CMVCurvatureIntegration.euclideanSpeed reparameterizedVelocity
    simp only
    have hd := R.parameter_deriv_ne_zero ht
    positivity
  · intro t ht
    have htIcc : t ∈ Icc R.start R.finish := ⟨ht.1.le, ht.2.le⟩
    have hx := R.maps_open ht
    have hcurv := hK (R.parameter t) hx
    have hroot :
        Real.sqrt (1 + deriv P.graph (R.parameter t) ^ 2) ≠ 0 := by
      positivity
    unfold orientedGraphCurvature graphCurvature at hcurv
    field_simp [hroot] at hcurv
    have hsecond :
        deriv (deriv P.graph) (R.parameter t) =
          P.side.areaSign *
            (Real.sqrt (1 + deriv P.graph (R.parameter t) ^ 2) ^ 3 * K) := by
      calc
        deriv (deriv P.graph) (R.parameter t) =
            (P.side.areaSign * P.side.areaSign) *
              deriv (deriv P.graph) (R.parameter t) := by
                rw [P.side.areaSign_mul_self, one_mul]
        _ = P.side.areaSign *
              (P.side.areaSign *
                deriv (deriv P.graph) (R.parameter t)) := by ring
        _ = P.side.areaSign *
              (Real.sqrt (1 + deriv P.graph (R.parameter t) ^ 2) ^ 3 * K) := by
                rw [hcurv]
    have hspeed :=
      P.signedEuclideanSpeed_reparameterizedVelocity R htIcc
    simp only [reparameterizedVelocity, reparameterizedAcceleration]
    calc
      deriv R.parameter t *
            (deriv (deriv P.graph) (R.parameter t) *
                deriv R.parameter t ^ 2 +
              deriv P.graph (R.parameter t) *
                deriv (deriv R.parameter) t) -
          (deriv P.graph (R.parameter t) * deriv R.parameter t) *
            deriv (deriv R.parameter) t =
          deriv R.parameter t ^ 3 *
            deriv (deriv P.graph) (R.parameter t) := by ring
      _ = deriv R.parameter t ^ 3 *
            (P.side.areaSign *
              (Real.sqrt (1 + deriv P.graph (R.parameter t) ^ 2) ^ 3 * K)) := by
              rw [hsecond]
      _ = P.side.areaSign * K *
            (deriv R.parameter t *
              Real.sqrt (1 + deriv P.graph (R.parameter t) ^ 2)) ^ 3 := by
              ring
      _ = P.side.areaSign * K *
            (R.direction.sign *
              CMVCurvatureIntegration.euclideanSpeed
                (P.reparameterizedVelocity R) t) ^ 3 := by
              rw [hspeed]
      _ = ((R.direction.sign * P.side.areaSign) * K) *
            CMVCurvatureIntegration.euclideanSpeed
              (P.reparameterizedVelocity R) t ^ 3 := by
              cases R.direction
              · simp [TraversalDirection.sign]
              · simp [TraversalDirection.sign]
                ring

/-- Every point of a regularly reparameterized closed graph interval satisfies
the supporting-circle identity delivered by the retained arbitrary-speed
integration theorem. -/
theorem closed_reparameterizedGraph_circle_identity
    (P : GraphPatch) (R : RegularGraphParameterChange P) {K s t : ℝ}
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) (hs : s ∈ Icc R.start R.finish)
    (ht : t ∈ Icc R.start R.finish) :
    ((P.reparameterizedTrace R t).1 -
        (CMVCurvatureIntegration.centerInvariant
          (P.reparameterizedTrace R)
          (CMVCurvatureIntegration.normalizedTangent
            (P.reparameterizedVelocity R))
          ((R.direction.sign * P.side.areaSign) * K) s).1) ^ 2 +
      ((P.reparameterizedTrace R t).2 -
        (CMVCurvatureIntegration.centerInvariant
          (P.reparameterizedTrace R)
          (CMVCurvatureIntegration.normalizedTangent
            (P.reparameterizedVelocity R))
          ((R.direction.sign * P.side.areaSign) * K) s).2) ^ 2 =
        (1 / ((R.direction.sign * P.side.areaSign) * K)) ^ 2 :=
  (P.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph R hK hKne
    ).closed_circle_identity hs ht

/-- Both regular parameter endpoints lie on the same derived supporting
circle; no endpoint acceleration is used. -/
theorem closed_reparameterizedGraph_endpoints_circle_identity
    (P : GraphPatch) (R : RegularGraphParameterChange P) {K : ℝ}
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K)
    (hKne : K ≠ 0) :
    (((P.reparameterizedTrace R R.start).1 -
        (CMVCurvatureIntegration.centerInvariant
          (P.reparameterizedTrace R)
          (CMVCurvatureIntegration.normalizedTangent
            (P.reparameterizedVelocity R))
          ((R.direction.sign * P.side.areaSign) * K) R.start).1) ^ 2 +
      ((P.reparameterizedTrace R R.start).2 -
        (CMVCurvatureIntegration.centerInvariant
          (P.reparameterizedTrace R)
          (CMVCurvatureIntegration.normalizedTangent
            (P.reparameterizedVelocity R))
          ((R.direction.sign * P.side.areaSign) * K) R.start).2) ^ 2 =
        (1 / ((R.direction.sign * P.side.areaSign) * K)) ^ 2) ∧
      (((P.reparameterizedTrace R R.finish).1 -
        (CMVCurvatureIntegration.centerInvariant
          (P.reparameterizedTrace R)
          (CMVCurvatureIntegration.normalizedTangent
            (P.reparameterizedVelocity R))
          ((R.direction.sign * P.side.areaSign) * K) R.start).1) ^ 2 +
      ((P.reparameterizedTrace R R.finish).2 -
        (CMVCurvatureIntegration.centerInvariant
          (P.reparameterizedTrace R)
          (CMVCurvatureIntegration.normalizedTangent
            (P.reparameterizedVelocity R))
          ((R.direction.sign * P.side.areaSign) * K) R.start).2) ^ 2 =
        (1 / ((R.direction.sign * P.side.areaSign) * K)) ^ 2) :=
  (P.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph R hK hKne
    ).closed_endpoints_circle_identity

/-- The zero-curvature supporting line is invariant under every admitted
increasing or decreasing parameter change. -/
theorem reparamTrace_mem_supportingLine_of_curvature_zero
    (P : GraphPatch) (R : RegularGraphParameterChange P)
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = 0) :
    ∀ t ∈ Icc R.start R.finish,
      (P.reparameterizedTrace R t).2 =
        P.graph P.a + deriv P.graph P.a *
          ((P.reparameterizedTrace R t).1 - P.a) := by
  intro t ht
  simpa only [reparameterizedTrace, graphTrace] using
    P.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero hK
      (R.parameter t) (R.maps_closed ht)

end GraphPatch

/-- The first reparameterized trace remains the literal graph piece certified
inside the actual carrier frontier. -/
theorem ActualTwoPatchData.first_reparameterizedTrace_mem_frontier
    (A : ActualTwoPatchData)
    (R : RegularGraphParameterChange A.patches.first) :
    ∀ t ∈ Ioo R.start R.finish,
      A.patches.first.reparameterizedTrace R t ∈ frontier A.actualCarrier := by
  intro t ht
  simpa only [GraphPatch.reparameterizedTrace, GraphPatch.graphTrace] using
    A.first_graph_frontier (R.parameter t) (R.maps_open ht)

/-- The second reparameterized trace remains the literal graph piece certified
inside the same actual carrier frontier. -/
theorem ActualTwoPatchData.second_reparameterizedTrace_mem_frontier
    (A : ActualTwoPatchData)
    (R : RegularGraphParameterChange A.patches.second) :
    ∀ t ∈ Ioo R.start R.finish,
      A.patches.second.reparameterizedTrace R t ∈ frontier A.actualCarrier := by
  intro t ht
  simpa only [GraphPatch.reparameterizedTrace, GraphPatch.graphTrace] using
    A.second_graph_frontier (R.parameter t) (R.maps_open ht)

/-- Conditional stationarity supplies, rather than assumes, one common
occupied-side curvature and the corresponding supporting geometry on both
actual graph patches.  The zero and nonzero branches are explicit. -/
theorem ActualTwoPatchData.exists_common_supportingGeometry
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hmin : A.IsBidirectionallyGraphMinimizing lam) :
    ∃ K : ℝ,
      (∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
        A.patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
        A.patches.second.orientedGraphCurvature x = K) ∧
      ((K = 0 ∧
          (∀ x ∈ Icc A.patches.first.a A.patches.first.b,
            A.patches.first.graph x = A.patches.first.graph A.patches.first.a +
              deriv A.patches.first.graph A.patches.first.a *
                (x - A.patches.first.a)) ∧
          (∀ x ∈ Icc A.patches.second.a A.patches.second.b,
            A.patches.second.graph x = A.patches.second.graph A.patches.second.a +
              deriv A.patches.second.graph A.patches.second.a *
                (x - A.patches.second.a))) ∨
        (K ≠ 0 ∧
          CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
            A.patches.first.graphTrace A.patches.first.graphVelocity
            A.patches.first.graphAcceleration
            (A.patches.first.side.areaSign * K)
            A.patches.first.a A.patches.first.b ∧
          CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
            A.patches.second.graphTrace A.patches.second.graphVelocity
            A.patches.second.graphAcceleration
            (A.patches.second.side.areaSign * K)
            A.patches.second.a A.patches.second.b)) := by
  rcases A.exists_common_orientedGraphCurvature hlam hmin with ⟨K, hK₁, hK₂⟩
  refine ⟨K, hK₁, hK₂, ?_⟩
  by_cases hzero : K = 0
  · left
    refine ⟨hzero, ?_, ?_⟩
    · apply A.patches.first.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
      intro x hx
      rw [hK₁ x hx, hzero]
    · apply A.patches.second.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
      intro x hx
      rw [hK₂ x hx, hzero]
  · right
    exact ⟨hzero,
      A.patches.first.arbitrarySpeedConstantCurvatureOn_graph hK₁ hzero,
      A.patches.second.arbitrarySpeedConstantCurvatureOn_graph hK₂ hzero⟩

/-- The stationarity-to-geometry consumer after independently chosen regular
parameter changes on the two actual graph patches.  The common occupied-side
curvature is derived internally.  Increasing and decreasing traversals convert
it by their direction and occupied-side signs; zero curvature instead yields
the corresponding closed supporting-line identities. -/
theorem ActualTwoPatchData.exists_common_reparameterizedSupportingGeometry
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hmin : A.IsBidirectionallyGraphMinimizing lam)
    (R₁ : RegularGraphParameterChange A.patches.first)
    (R₂ : RegularGraphParameterChange A.patches.second) :
    ∃ K : ℝ,
      (∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
        A.patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
        A.patches.second.orientedGraphCurvature x = K) ∧
      ((K = 0 ∧
          (∀ t ∈ Icc R₁.start R₁.finish,
            (A.patches.first.reparameterizedTrace R₁ t).2 =
              A.patches.first.graph A.patches.first.a +
                deriv A.patches.first.graph A.patches.first.a *
                  ((A.patches.first.reparameterizedTrace R₁ t).1 -
                    A.patches.first.a)) ∧
          (∀ t ∈ Icc R₂.start R₂.finish,
            (A.patches.second.reparameterizedTrace R₂ t).2 =
              A.patches.second.graph A.patches.second.a +
                deriv A.patches.second.graph A.patches.second.a *
                  ((A.patches.second.reparameterizedTrace R₂ t).1 -
                    A.patches.second.a))) ∨
        (K ≠ 0 ∧
          CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
            (A.patches.first.reparameterizedTrace R₁)
            (A.patches.first.reparameterizedVelocity R₁)
            (A.patches.first.reparameterizedAcceleration R₁)
            ((R₁.direction.sign * A.patches.first.side.areaSign) * K)
            R₁.start R₁.finish ∧
          CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
            (A.patches.second.reparameterizedTrace R₂)
            (A.patches.second.reparameterizedVelocity R₂)
            (A.patches.second.reparameterizedAcceleration R₂)
            ((R₂.direction.sign * A.patches.second.side.areaSign) * K)
            R₂.start R₂.finish)) := by
  rcases A.exists_common_orientedGraphCurvature hlam hmin with ⟨K, hK₁, hK₂⟩
  refine ⟨K, hK₁, hK₂, ?_⟩
  by_cases hzero : K = 0
  · left
    refine ⟨hzero, ?_, ?_⟩
    · apply
        A.patches.first.reparamTrace_mem_supportingLine_of_curvature_zero
          R₁
      intro x hx
      rw [hK₁ x hx, hzero]
    · apply
        A.patches.second.reparamTrace_mem_supportingLine_of_curvature_zero
          R₂
      intro x hx
      rw [hK₂ x hx, hzero]
  · right
    exact ⟨hzero,
      A.patches.first.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
        R₁ hK₁ hzero,
      A.patches.second.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
        R₂ hK₂ hzero⟩

/-! ## Finite actual graph collections -/

/-- Every regularly reparameterized member trace remains on the frontier of
the collection's literal ambient carrier. -/
theorem FiniteActualGraphCollection.member_reparameterizedTrace_mem_frontier
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : FiniteActualGraphCollection ι) (i : ι)
    (R : RegularGraphParameterChange (C.pair i).patches.first) :
    ∀ t ∈ Ioo R.start R.finish,
      (C.pair i).patches.first.reparameterizedTrace R t ∈
        frontier C.actualCarrier := by
  intro t ht
  simpa only [C.pair_actualCarrier i] using
    (C.pair i).first_reparameterizedTrace_mem_frontier R t ht

/-- The regularly reparameterized common anchor trace is also an actual
frontier piece.  Nonemptiness selects one stored pair whose second patch is
the anchor; the conclusion is independent of that selection. -/
theorem FiniteActualGraphCollection.anchor_reparameterizedTrace_mem_frontier
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : FiniteActualGraphCollection ι)
    (R : RegularGraphParameterChange C.anchor) :
    ∀ t ∈ Ioo R.start R.finish,
      C.anchor.reparameterizedTrace R t ∈ frontier C.actualCarrier := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  intro t ht
  have hmaps :
      R.parameter t ∈
        Ioo (C.pair i₀).patches.second.a
          (C.pair i₀).patches.second.b := by
    simpa only [C.pair_second i₀] using R.maps_open ht
  have hfrontier :=
    (C.pair i₀).second_graph_frontier (R.parameter t) hmaps
  simpa only [GraphPatch.reparameterizedTrace, GraphPatch.graphTrace,
    C.pair_second i₀, C.pair_actualCarrier i₀] using hfrontier

/-- Pairwise graph-functional stationarity against one common actual anchor
derives supporting geometry for every member and the anchor.  The common
occupied-side curvature is constructed internally.  Zero curvature gives
closed supporting lines; nonzero curvature gives the retained arbitrary-speed
circle interface on every literal graph trace. -/
theorem FiniteActualGraphCollection.exists_common_supportingGeometry
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam : ℝ} (hlam : 1 < lam)
    (C : FiniteActualGraphCollection ι)
    (hmin : ∀ i, (C.pair i).IsBidirectionallyGraphMinimizing lam) :
    ∃ K : ℝ,
      (∀ i, ∀ x ∈ Ioo (C.pair i).patches.first.a
          (C.pair i).patches.first.b,
        (C.pair i).patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo C.anchor.a C.anchor.b,
        C.anchor.orientedGraphCurvature x = K) ∧
      ((K = 0 ∧
          (∀ i, ∀ x ∈ Icc (C.pair i).patches.first.a
              (C.pair i).patches.first.b,
            (C.pair i).patches.first.graph x =
              (C.pair i).patches.first.graph
                  (C.pair i).patches.first.a +
                deriv (C.pair i).patches.first.graph
                    (C.pair i).patches.first.a *
                  (x - (C.pair i).patches.first.a)) ∧
          (∀ x ∈ Icc C.anchor.a C.anchor.b,
            C.anchor.graph x =
              C.anchor.graph C.anchor.a +
                deriv C.anchor.graph C.anchor.a * (x - C.anchor.a))) ∨
        (K ≠ 0 ∧
          (∀ i,
            CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
              (C.pair i).patches.first.graphTrace
              (C.pair i).patches.first.graphVelocity
              (C.pair i).patches.first.graphAcceleration
              ((C.pair i).patches.first.side.areaSign * K)
              (C.pair i).patches.first.a
              (C.pair i).patches.first.b) ∧
          CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
            C.anchor.graphTrace C.anchor.graphVelocity
            C.anchor.graphAcceleration
            (C.anchor.side.areaSign * K) C.anchor.a C.anchor.b)) := by
  rcases C.exists_common_orientedGraphCurvature hlam hmin with
    ⟨K, hmembers, hanchor⟩
  refine ⟨K, hmembers, hanchor, ?_⟩
  by_cases hzero : K = 0
  · left
    refine ⟨hzero, ?_, ?_⟩
    · intro i
      apply
        (C.pair i).patches.first
          |>.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
      intro x hx
      rw [hmembers i x hx, hzero]
    · apply C.anchor.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
      intro x hx
      rw [hanchor x hx, hzero]
  · right
    refine ⟨hzero, ?_, ?_⟩
    · intro i
      exact
        (C.pair i).patches.first.arbitrarySpeedConstantCurvatureOn_graph
          (hmembers i) hzero
    · exact C.anchor.arbitrarySpeedConstantCurvatureOn_graph hanchor hzero

/-- The finite-family stationarity consumer after independent regular
increasing or decreasing parameter changes.  Traversal direction and occupied
side both remain explicit in the signed curvature, while the zero branch gives
closed supporting-line identities on every reparameterized trace. -/
theorem FiniteActualGraphCollection.exists_common_reparameterizedSupportingGeometry
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam : ℝ} (hlam : 1 < lam)
    (C : FiniteActualGraphCollection ι)
    (hmin : ∀ i, (C.pair i).IsBidirectionallyGraphMinimizing lam)
    (R : ∀ i, RegularGraphParameterChange (C.pair i).patches.first)
    (Ranchor : RegularGraphParameterChange C.anchor) :
    ∃ K : ℝ,
      (∀ i, ∀ x ∈ Ioo (C.pair i).patches.first.a
          (C.pair i).patches.first.b,
        (C.pair i).patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo C.anchor.a C.anchor.b,
        C.anchor.orientedGraphCurvature x = K) ∧
      ((K = 0 ∧
          (∀ i, ∀ t ∈ Icc (R i).start (R i).finish,
            ((C.pair i).patches.first.reparameterizedTrace (R i) t).2 =
              (C.pair i).patches.first.graph
                  (C.pair i).patches.first.a +
                deriv (C.pair i).patches.first.graph
                    (C.pair i).patches.first.a *
                  (((C.pair i).patches.first.reparameterizedTrace
                      (R i) t).1 -
                    (C.pair i).patches.first.a)) ∧
          (∀ t ∈ Icc Ranchor.start Ranchor.finish,
            (C.anchor.reparameterizedTrace Ranchor t).2 =
              C.anchor.graph C.anchor.a +
                deriv C.anchor.graph C.anchor.a *
                  ((C.anchor.reparameterizedTrace Ranchor t).1 -
                    C.anchor.a))) ∨
        (K ≠ 0 ∧
          (∀ i,
            CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
              ((C.pair i).patches.first.reparameterizedTrace (R i))
              ((C.pair i).patches.first.reparameterizedVelocity (R i))
              ((C.pair i).patches.first.reparameterizedAcceleration (R i))
              (((R i).direction.sign *
                  (C.pair i).patches.first.side.areaSign) * K)
              (R i).start (R i).finish) ∧
          CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
            (C.anchor.reparameterizedTrace Ranchor)
            (C.anchor.reparameterizedVelocity Ranchor)
            (C.anchor.reparameterizedAcceleration Ranchor)
            ((Ranchor.direction.sign * C.anchor.side.areaSign) * K)
            Ranchor.start Ranchor.finish)) := by
  rcases C.exists_common_orientedGraphCurvature hlam hmin with
    ⟨K, hmembers, hanchor⟩
  refine ⟨K, hmembers, hanchor, ?_⟩
  by_cases hzero : K = 0
  · left
    refine ⟨hzero, ?_, ?_⟩
    · intro i
      apply
        (C.pair i).patches.first
          |>.reparamTrace_mem_supportingLine_of_curvature_zero (R i)
      intro x hx
      rw [hmembers i x hx, hzero]
    · apply
        C.anchor.reparamTrace_mem_supportingLine_of_curvature_zero Ranchor
      intro x hx
      rw [hanchor x hx, hzero]
  · right
    refine ⟨hzero, ?_, ?_⟩
    · intro i
      exact
        (C.pair i).patches.first
          |>.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
            (R i) (hmembers i) hzero
    · exact
        C.anchor.arbitrarySpeedConstantCurvatureOn_reparameterizedGraph
          Ranchor hanchor hzero

end CMVTwoPatchGraphVariation
