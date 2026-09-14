/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSourceBoundaryContinuation
import CMVTransverseContactMomentum
import CMVAELocalChartPreservation

/-!
# Mixed-coordinate support continuation

This module adds actual regular charts of the form `x = g(y)` to the existing
`y = f(x)` continuation API.  A mixed overlap is witnessed by the two literal
local frontier equations.  The inverse derivative relation is therefore
derived, not supplied.  Occupied-side compatibility records only which strict
side of each coordinate graph is occupied; it never supplies a circle, line,
center, or support equality.
-/

open Set Function Filter Real
open scoped Topology ContDiff

noncomputable section

namespace CMVTransverseContactVariation

open CMVTwoPatchGraphVariation

namespace HorizontalGraphPatch

/-- The actual graph trace `x = g(y)` in increasing second coordinate. -/
def graphTrace (P : HorizontalGraphPatch) (y : ℝ) : PlanePoint :=
  (P.graph y, y)

/-- Actual coordinate velocity of the increasing-`y` graph trace. -/
def graphVelocity (P : HorizontalGraphPatch) (y : ℝ) : PlanePoint :=
  (deriv P.graph y, 1)

/-- Actual coordinate acceleration of the increasing-`y` graph trace. -/
def graphAcceleration (P : HorizontalGraphPatch) (y : ℝ) : PlanePoint :=
  (deriv (deriv P.graph) y, 0)

/-- Curvature oriented by the occupied left/right side. -/
def orientedGraphCurvature (P : HorizontalGraphPatch) (y : ℝ) : ℝ :=
  P.side.areaSign * contactCurvature P y

/-- The genuine left/right open side of a horizontal graph.  Unlike the
bounded variation ribbon, this is the local carrier model used at an actual
frontier point. -/
def occupiedGraphDomain (P : HorizontalGraphPatch) : Set PlanePoint :=
  match P.side with
  | .below => {q | q.1 < P.graph q.2}
  | .above => {q | P.graph q.2 < q.1}

@[simp] theorem graphTrace_fst (P : HorizontalGraphPatch) (y : ℝ) :
    (P.graphTrace y).1 = P.graph y := rfl

@[simp] theorem graphTrace_snd (P : HorizontalGraphPatch) (y : ℝ) :
    (P.graphTrace y).2 = y := rfl

@[simp] theorem graphVelocity_fst (P : HorizontalGraphPatch) (y : ℝ) :
    (P.graphVelocity y).1 = deriv P.graph y := rfl

@[simp] theorem graphVelocity_snd (P : HorizontalGraphPatch) (y : ℝ) :
    (P.graphVelocity y).2 = 1 := rfl

/-- The physical graph speed is the usual square-root density. -/
theorem euclideanSpeed_graphVelocity (P : HorizontalGraphPatch) (y : ℝ) :
    CMVCurvatureIntegration.euclideanSpeed P.graphVelocity y =
      Real.sqrt (1 + deriv P.graph y ^ 2) := by
  unfold CMVCurvatureIntegration.euclideanSpeed graphVelocity
  congr 1
  ring

/-- Constant occupied-side curvature integrates along an `x = g(y)` chart.
Coordinate exchange reverses traversal curvature, hence the leading minus sign. -/
theorem arbitrarySpeedConstantCurvatureOn_graph
    (P : HorizontalGraphPatch) {K : ℝ}
    (hK : ∀ y ∈ Ioo P.a P.b, P.orientedGraphCurvature y = K)
    (hKne : K ≠ 0) :
    CMVCurvatureIntegration.ArbitrarySpeedConstantCurvatureOn
      P.graphTrace P.graphVelocity P.graphAcceleration
      (-(P.side.areaSign * K)) P.a P.b where
  start_lt_finish := P.a_lt_b
  curvature_ne_zero := neg_ne_zero.mpr
    (mul_ne_zero P.side.areaSign_ne_zero hKne)
  trace_fst_continuous := P.graph_contDiff.continuous.continuousOn
  trace_snd_continuous := continuous_id.continuousOn
  velocity_fst_continuous :=
    (P.graph_contDiff.continuous_deriv (by norm_num)).continuousOn
  velocity_snd_continuous := continuous_const.continuousOn
  trace_fst_derivative := by
    intro y _hy
    simpa [graphTrace, graphVelocity] using
      (P.graph_contDiff.differentiable (by norm_num) y).hasDerivAt
  trace_snd_derivative := by
    intro y _hy
    simpa [graphTrace, graphVelocity] using hasDerivAt_id' y
  velocity_fst_derivative := by
    intro y _hy
    have hd : ContDiff ℝ 1 (deriv P.graph) :=
      (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
    simpa [graphVelocity, graphAcceleration] using
      (hd.differentiable (by norm_num) y).hasDerivAt
  velocity_snd_derivative := by
    intro y _hy
    simpa [graphVelocity, graphAcceleration] using hasDerivAt_const y (1 : ℝ)
  positive_speed := by
    intro y _hy
    rw [P.euclideanSpeed_graphVelocity]
    positivity
  signed_curvature := by
    intro y hy
    have hroot : Real.sqrt (1 + deriv P.graph y ^ 2) ≠ 0 := by positivity
    have hcurv := hK y hy
    unfold orientedGraphCurvature contactCurvature at hcurv
    field_simp [hroot] at hcurv
    simp only [graphVelocity, graphAcceleration, mul_zero, one_mul,
      P.euclideanSpeed_graphVelocity]
    calc
      0 - deriv (deriv P.graph) y =
          -(P.side.areaSign *
            (P.side.areaSign * deriv (deriv P.graph) y)) := by
              rw [← mul_assoc, P.side.areaSign_mul_self, one_mul]
              ring
      _ = -(P.side.areaSign *
            (Real.sqrt (1 + deriv P.graph y ^ 2) ^ 3 * K)) := by
              rw [hcurv]
      _ = -(P.side.areaSign * K) *
            Real.sqrt (1 + deriv P.graph y ^ 2) ^ 3 := by ring

/-- Supporting center selected by a nonzero mixed-coordinate chart. -/
def supportingCenter (P : HorizontalGraphPatch) (K y : ℝ) : PlanePoint :=
  CMVCurvatureIntegration.centerInvariant P.graphTrace
    (CMVCurvatureIntegration.normalizedTangent P.graphVelocity)
    (-(P.side.areaSign * K)) y

/-- Literal supporting circle selected by a nonzero mixed-coordinate chart. -/
def supportingCircle (P : HorizontalGraphPatch) (K y : ℝ) : Set PlanePoint :=
  {p | (p.1 - (P.supportingCenter K y).1) ^ 2 +
      (p.2 - (P.supportingCenter K y).2) ^ 2 =
        (1 / (-(P.side.areaSign * K))) ^ 2}

/-- Every closed point of a constant nonzero-curvature horizontal graph lies
on the support selected at any closed anchor. -/
theorem closed_graph_circle_identity
    (P : HorizontalGraphPatch) {K s y : ℝ}
    (hK : ∀ z ∈ Ioo P.a P.b, P.orientedGraphCurvature z = K)
    (hKne : K ≠ 0) (hs : s ∈ Icc P.a P.b) (hy : y ∈ Icc P.a P.b) :
    P.graphTrace y ∈ P.supportingCircle K s := by
  exact (P.arbitrarySpeedConstantCurvatureOn_graph hK hKne).closed_circle_identity hs hy

/-- Affine support through an `x = g(y)` chart point. -/
def supportingLineAt (P : HorizontalGraphPatch) (y : ℝ) : Set PlanePoint :=
  {p | p.1 = P.graph y + deriv P.graph y * (p.2 - y)}

/-- Zero occupied-side curvature makes an `x = g(y)` chart affine on its whole
closed parameter interval. -/
theorem graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    (P : HorizontalGraphPatch)
    (hK : ∀ y ∈ Ioo P.a P.b, P.orientedGraphCurvature y = 0) :
    ∀ y ∈ Icc P.a P.b,
      P.graph y = P.graph P.a + deriv P.graph P.a * (y - P.a) := by
  have hsecond : ∀ y ∈ Ioo P.a P.b,
      HasDerivAt (deriv P.graph) 0 y := by
    intro y hy
    have hz := hK y hy
    have hden : Real.sqrt (1 + deriv P.graph y ^ 2) ^ 3 ≠ 0 := by positivity
    unfold orientedGraphCurvature contactCurvature at hz
    have hderiv : deriv (deriv P.graph) y = 0 := by
      have hfrac := (mul_eq_zero.mp hz).resolve_left P.side.areaSign_ne_zero
      exact (div_eq_zero_iff.mp hfrac).resolve_right hden
    have hd : ContDiff ℝ 1 (deriv P.graph) :=
      (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
    exact (hd.differentiable (by norm_num) y).hasDerivAt.congr_deriv hderiv
  have hderivContDiff : ContDiff ℝ 1 (deriv P.graph) :=
    (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
  have hslope : Set.EqOn (deriv P.graph)
      (fun _ => deriv P.graph P.a) (Icc P.a P.b) :=
    CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero P.a_lt_b
      hderivContDiff.continuous.continuousOn hsecond
  let affineResidual : ℝ → ℝ := fun y =>
    P.graph y - deriv P.graph P.a * y
  have hresidualDeriv : ∀ y ∈ Ioo P.a P.b,
      HasDerivAt affineResidual 0 y := by
    intro y hy
    have hraw :=
      (P.graph_contDiff.differentiable (by norm_num) y).hasDerivAt.sub
        ((hasDerivAt_id y).const_mul (deriv P.graph P.a))
    exact hraw.congr_deriv (by
      rw [hslope ⟨hy.1.le, hy.2.le⟩]
      ring)
  have hresidual : Set.EqOn affineResidual
      (fun _ => affineResidual P.a) (Icc P.a P.b) :=
    CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero P.a_lt_b
      ((P.graph_contDiff.continuous.sub
        (continuous_const.mul continuous_id)).continuousOn)
      hresidualDeriv
  intro y hy
  have h := hresidual hy
  change P.graph y - deriv P.graph P.a * y =
    P.graph P.a - deriv P.graph P.a * P.a at h
  linarith

/-- The complete closed zero-curvature trace lies on the line selected at any
closed anchor. -/
theorem closedTrace_subset_supportingLineAt
    (P : HorizontalGraphPatch)
    (hzero : ∀ y ∈ Ioo P.a P.b, P.orientedGraphCurvature y = 0)
    {s : ℝ} (hs : s ∈ Icc P.a P.b) :
    ∀ y ∈ Icc P.a P.b, P.graphTrace y ∈ P.supportingLineAt s := by
  intro y hy
  have hsline := P.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    hzero s hs
  have hyline := P.graph_eq_supportingLine_of_orientedGraphCurvature_eq_zero
    hzero y hy
  have hsecond : ∀ z ∈ Ioo P.a P.b,
      HasDerivAt (deriv P.graph) 0 z := by
    intro z hz
    have hcurv := hzero z hz
    have hden : Real.sqrt (1 + deriv P.graph z ^ 2) ^ 3 ≠ 0 := by positivity
    unfold orientedGraphCurvature contactCurvature at hcurv
    have hd : deriv (deriv P.graph) z = 0 := by
      have hfrac := (mul_eq_zero.mp hcurv).resolve_left P.side.areaSign_ne_zero
      exact (div_eq_zero_iff.mp hfrac).resolve_right hden
    have hderivContDiff : ContDiff ℝ 1 (deriv P.graph) :=
      (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
    exact (hderivContDiff.differentiable (by norm_num) z
      ).hasDerivAt.congr_deriv hd
  have hderivContDiff : ContDiff ℝ 1 (deriv P.graph) :=
    (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
  have hslope := CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero
    P.a_lt_b hderivContDiff.continuous.continuousOn hsecond
  have hslopeS : deriv P.graph s = deriv P.graph P.a := hslope hs
  change P.graph y = P.graph s + deriv P.graph s * (y - s)
  rw [hsline, hyline, hslopeS]
  ring

/-- A nonzero-curvature horizontal-coordinate chart selects the same circle
from every closed anchor parameter. -/
theorem supportingCircle_eq_of_anchors
    (P : HorizontalGraphPatch) {K s t : ℝ}
    (hK : K ≠ 0)
    (hcurv : ∀ z ∈ Ioo P.a P.b, P.orientedGraphCurvature z = K)
    (hs : s ∈ Icc P.a P.b) (ht : t ∈ Icc P.a P.b) :
    P.supportingCircle K s = P.supportingCircle K t := by
  have hregular := P.arbitrarySpeedConstantCurvatureOn_graph hcurv hK
  have hcenter : P.supportingCenter K s = P.supportingCenter K t :=
    hregular.center_invariant hs ht
  unfold supportingCircle
  rw [hcenter]

/-- Zero occupied curvature makes the first derivative constant on the whole
closed horizontal-coordinate chart interval. -/
theorem deriv_eq_of_orientedGraphCurvature_eq_zero
    (P : HorizontalGraphPatch)
    (hzero : ∀ z ∈ Ioo P.a P.b, P.orientedGraphCurvature z = 0)
    {s t : ℝ} (hs : s ∈ Icc P.a P.b) (ht : t ∈ Icc P.a P.b) :
    deriv P.graph s = deriv P.graph t := by
  have hsecond : ∀ z ∈ Ioo P.a P.b,
      HasDerivAt (deriv P.graph) 0 z := by
    intro z hz
    have hcurv := hzero z hz
    have hden : Real.sqrt (1 + deriv P.graph z ^ 2) ^ 3 ≠ 0 := by
      positivity
    unfold orientedGraphCurvature contactCurvature at hcurv
    have hderiv : deriv (deriv P.graph) z = 0 := by
      have hfrac :=
        (mul_eq_zero.mp hcurv).resolve_left P.side.areaSign_ne_zero
      exact (div_eq_zero_iff.mp hfrac).resolve_right hden
    have hd : ContDiff ℝ 1 (deriv P.graph) :=
      (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
    exact (hd.differentiable (by norm_num) z).hasDerivAt.congr_deriv hderiv
  have hderivContDiff : ContDiff ℝ 1 (deriv P.graph) :=
    (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2
  have hconstant := CMVCurvatureIntegration.eqOn_Icc_of_hasDerivAt_zero
    P.a_lt_b hderivContDiff.continuous.continuousOn hsecond
  exact (hconstant hs).trans (hconstant ht).symm

/-- A zero-curvature horizontal-coordinate chart selects the same affine line
from every closed anchor. -/
theorem supportingLineAt_eq_of_anchors
    (P : HorizontalGraphPatch)
    (hzero : ∀ z ∈ Ioo P.a P.b, P.orientedGraphCurvature z = 0)
    {s t : ℝ} (hs : s ∈ Icc P.a P.b) (ht : t ∈ Icc P.a P.b) :
    P.supportingLineAt s = P.supportingLineAt t := by
  have hslope := P.deriv_eq_of_orientedGraphCurvature_eq_zero hzero hs ht
  have hst := P.closedTrace_subset_supportingLineAt hzero ht s hs
  change P.graph s =
    P.graph t + deriv P.graph t * (s - t) at hst
  have haffine : ∀ z : ℝ,
      P.graph s + deriv P.graph s * (z - s) =
        P.graph t + deriv P.graph t * (z - t) := by
    intro z
    rw [hslope, hst]
    ring
  ext p
  change (p.1 = P.graph s + deriv P.graph s * (p.2 - s)) ↔
    (p.1 = P.graph t + deriv P.graph t * (p.2 - t))
  rw [haffine p.2]

end HorizontalGraphPatch
end CMVTransverseContactVariation

namespace CMVSourceBoundaryContinuation

open CMVTwoPatchGraphVariation
open CMVTransverseContactVariation

/-- A regular boundary chart written as `x = g(y)` on the actual carrier.
The local equation is only a frontier germ; it is not a supplied component
image or a selected CMV branch. -/
structure ActualRegularHorizontalGraphChart (carrier : Set PlanePoint) where
  patch : HorizontalGraphPatch
  neighborhood : Set PlanePoint
  neighborhood_open : IsOpen neighborhood
  local_frontier :
    frontier carrier ∩ neighborhood =
      patch.graphTrace '' Ioo patch.a patch.b

namespace ActualRegularHorizontalGraphChart

variable {carrier : Set PlanePoint}

/-- Every interior point of the mixed-coordinate chart is actual frontier. -/
theorem graphTrace_mem_frontier
    (A : ActualRegularHorizontalGraphChart carrier)
    {y : ℝ} (hy : y ∈ Ioo A.patch.a A.patch.b) :
    A.patch.graphTrace y ∈ frontier carrier := by
  have hmem : A.patch.graphTrace y ∈
      A.patch.graphTrace '' Ioo A.patch.a A.patch.b := ⟨y, hy, rfl⟩
  rw [← A.local_frontier] at hmem
  exact hmem.1

/-- Every interior point lies in its declared open chart neighborhood. -/
theorem graphTrace_mem_neighborhood
    (A : ActualRegularHorizontalGraphChart carrier)
    {y : ℝ} (hy : y ∈ Ioo A.patch.a A.patch.b) :
    A.patch.graphTrace y ∈ A.neighborhood := by
  have hmem : A.patch.graphTrace y ∈
      A.patch.graphTrace '' Ioo A.patch.a A.patch.b := ⟨y, hy, rfl⟩
  rw [← A.local_frontier] at hmem
  exact hmem.2

end ActualRegularHorizontalGraphChart

/-- Two `x = g(y)` charts overlap at one actual frontier point with the same
second coordinate.  No equality of graph functions or supporting geometry is
supplied. -/
structure ActualRegularHorizontalGraphChart.OverlapAt
    {carrier : Set PlanePoint}
    (A B : ActualRegularHorizontalGraphChart carrier) (y : ℝ) : Prop where
  left_interior : y ∈ Ioo A.patch.a A.patch.b
  right_interior : y ∈ Ioo B.patch.a B.patch.b
  point_eq : A.patch.graphTrace y = B.patch.graphTrace y

namespace ActualRegularHorizontalGraphChart

variable {carrier : Set PlanePoint}

/-- Exact local frontier equations force two overlapping horizontal-coordinate
charts to agree near their common second coordinate. -/
theorem eventuallyEq_graph_of_overlap
    (A B : ActualRegularHorizontalGraphChart carrier) {y : ℝ}
    (h : OverlapAt A B y) :
    A.patch.graph =ᶠ[𝓝 y] B.patch.graph := by
  have htraceContinuous : Continuous A.patch.graphTrace :=
    A.patch.graph_contDiff.continuous.prodMk continuous_id
  have hrightNeighborhood :
      A.patch.graphTrace y ∈ B.neighborhood := by
    rw [h.point_eq]
    exact B.graphTrace_mem_neighborhood h.right_interior
  have hnearNeighborhood :
      ∀ᶠ z in 𝓝 y, A.patch.graphTrace z ∈ B.neighborhood :=
    htraceContinuous.continuousAt
      (B.neighborhood_open.mem_nhds hrightNeighborhood)
  have hnearInterior : ∀ᶠ z in 𝓝 y, z ∈ Ioo A.patch.a A.patch.b :=
    isOpen_Ioo.mem_nhds h.left_interior
  filter_upwards [hnearNeighborhood, hnearInterior] with z hzNeighborhood hzInterior
  have hzFrontier : A.patch.graphTrace z ∈ frontier carrier :=
    A.graphTrace_mem_frontier hzInterior
  have hzRight : A.patch.graphTrace z ∈
      B.patch.graphTrace '' Ioo B.patch.a B.patch.b := by
    rw [← B.local_frontier]
    exact ⟨hzFrontier, hzNeighborhood⟩
  rcases hzRight with ⟨w, hwInterior, hwz⟩
  have hwzParameter : w = z := by
    have hsnd := congrArg Prod.snd hwz
    simpa only [HorizontalGraphPatch.graphTrace] using hsnd
  have hfst := congrArg Prod.fst hwz
  simpa only [HorizontalGraphPatch.graphTrace, hwzParameter] using hfst.symm

/-- Same-axis mixed-atlas charts have equal first derivatives at an actual
overlap. -/
theorem deriv_eq_of_overlap
    (A B : ActualRegularHorizontalGraphChart carrier) {y : ℝ}
    (h : OverlapAt A B y) :
    deriv A.patch.graph y = deriv B.patch.graph y :=
  (A.eventuallyEq_graph_of_overlap B h).deriv_eq

/-- The increasing-second-coordinate unit tangents agree at a same-axis
overlap. -/
theorem normalizedTangent_eq_of_overlap
    (A B : ActualRegularHorizontalGraphChart carrier) {y : ℝ}
    (h : OverlapAt A B y) :
    CMVCurvatureIntegration.normalizedTangent A.patch.graphVelocity y =
      CMVCurvatureIntegration.normalizedTangent B.patch.graphVelocity y := by
  have hvelocity : A.patch.graphVelocity y = B.patch.graphVelocity y := by
    apply Prod.ext
    · exact A.deriv_eq_of_overlap B h
    · rfl
  have hspeed :
      CMVCurvatureIntegration.euclideanSpeed A.patch.graphVelocity y =
        CMVCurvatureIntegration.euclideanSpeed B.patch.graphVelocity y := by
    unfold CMVCurvatureIntegration.euclideanSpeed
    rw [hvelocity]
  unfold CMVCurvatureIntegration.normalizedTangent
  rw [hvelocity, hspeed]

/-- Equal occupied-side labels and the actual overlap select one supporting
center for two `x = g(y)` charts. -/
theorem supportingCenter_eq_of_overlap
    (A B : ActualRegularHorizontalGraphChart carrier) {K y : ℝ}
    (h : OverlapAt A B y) (hside : A.patch.side = B.patch.side) :
    A.patch.supportingCenter K y = B.patch.supportingCenter K y := by
  unfold HorizontalGraphPatch.supportingCenter
    CMVCurvatureIntegration.centerInvariant
  rw [h.point_eq, A.normalizedTangent_eq_of_overlap B h, hside]

/-- Same-axis horizontal-coordinate charts select the same literal circle and
put both complete closed chart traces on it. -/
theorem unique_supportingCircle_of_overlap
    (A B : ActualRegularHorizontalGraphChart carrier) {K y : ℝ}
    (h : OverlapAt A B y) (hside : A.patch.side = B.patch.side)
    (hK : K ≠ 0)
    (hcurvA : ∀ z ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature z = K)
    (hcurvB : ∀ z ∈ Ioo B.patch.a B.patch.b,
      B.patch.orientedGraphCurvature z = K) :
    A.patch.supportingCircle K y = B.patch.supportingCircle K y ∧
      (∀ z ∈ Icc A.patch.a A.patch.b,
        A.patch.graphTrace z ∈ A.patch.supportingCircle K y) ∧
      (∀ z ∈ Icc B.patch.a B.patch.b,
        B.patch.graphTrace z ∈ B.patch.supportingCircle K y) := by
  have hcenter :=
    A.supportingCenter_eq_of_overlap B (K := K) h hside
  have hcircle :
      A.patch.supportingCircle K y = B.patch.supportingCircle K y := by
    unfold HorizontalGraphPatch.supportingCircle
    rw [hcenter, hside]
  refine ⟨hcircle, ?_, ?_⟩
  · intro z hz
    exact A.patch.closed_graph_circle_identity hcurvA hK
      ⟨h.left_interior.1.le, h.left_interior.2.le⟩ hz
  · intro z hz
    exact B.patch.closed_graph_circle_identity hcurvB hK
      ⟨h.right_interior.1.le, h.right_interior.2.le⟩ hz

/-- Same-axis zero-curvature horizontal-coordinate charts select the same
literal affine line; no occupied-side equality is needed. -/
theorem unique_supportingLine_of_overlap
    (A B : ActualRegularHorizontalGraphChart carrier) {y : ℝ}
    (h : OverlapAt A B y)
    (hzeroA : ∀ z ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature z = 0)
    (hzeroB : ∀ z ∈ Ioo B.patch.a B.patch.b,
      B.patch.orientedGraphCurvature z = 0) :
    A.patch.supportingLineAt y = B.patch.supportingLineAt y ∧
      (∀ z ∈ Icc A.patch.a A.patch.b,
        A.patch.graphTrace z ∈ A.patch.supportingLineAt y) ∧
      (∀ z ∈ Icc B.patch.a B.patch.b,
        B.patch.graphTrace z ∈ B.patch.supportingLineAt y) := by
  have hgraph : A.patch.graph y = B.patch.graph y := by
    exact congrArg Prod.fst h.point_eq
  have hderiv := A.deriv_eq_of_overlap B h
  have hline :
      A.patch.supportingLineAt y = B.patch.supportingLineAt y := by
    unfold HorizontalGraphPatch.supportingLineAt
    rw [hgraph, hderiv]
  refine ⟨hline, ?_, ?_⟩
  · exact A.patch.closedTrace_subset_supportingLineAt hzeroA
      ⟨h.left_interior.1.le, h.left_interior.2.le⟩
  · exact B.patch.closedTrace_subset_supportingLineAt hzeroB
      ⟨h.right_interior.1.le, h.right_interior.2.le⟩

end ActualRegularHorizontalGraphChart

namespace ActualRegularGraphChart

/-- Truthful occupied germs determine the same occupied-side label for two
overlapping `y = f(x)` charts.  The label is derived from actual carrier
membership rather than imposed by a global atlas field. -/
theorem side_eq_of_overlap_of_occupiedGerms
    {carrier : Set PlanePoint}
    (A B : ActualRegularGraphChart carrier) {x : ℝ}
    (h : OverlapAt A B x)
    (hA : ∀ᶠ q in 𝓝 (A.patch.graphTrace x),
      (q ∈ carrier ↔ q ∈ A.patch.occupiedGraphDomain A.patch.graph))
    (hB : ∀ᶠ q in 𝓝 (B.patch.graphTrace x),
      (q ∈ carrier ↔ q ∈ B.patch.occupiedGraphDomain B.patch.graph)) :
    A.patch.side = B.patch.side := by
  have hgraph : A.patch.graph x = B.patch.graph x :=
    congrArg Prod.snd h.point_eq
  let q : ℝ → PlanePoint := fun t => (x, A.patch.graph x + t)
  have hqA : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (A.patch.graphTrace x)) := by
    rw [show A.patch.graphTrace x = (x, A.patch.graph x) by rfl]
    have hfirst : ContinuousAt (fun _t : ℝ => x) 0 :=
      continuousAt_const
    have hsecond : ContinuousAt (fun t : ℝ => A.patch.graph x + t) 0 :=
      continuousAt_const.add continuousAt_id
    have hcontinuous := hfirst.prodMk hsecond
    simpa only [q, add_zero] using
      hcontinuous.mono_left nhdsWithin_le_nhds
  have hqB : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (B.patch.graphTrace x)) := by
    rw [← h.point_eq]
    exact hqA
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htA, htB, ht⟩ :=
    Filter.Eventually.exists
      ((hqA.eventually hA).and ((hqB.eventually hB).and hpos))
  cases hAside : A.patch.side <;> cases hBside : B.patch.side
  · rfl
  · exfalso
    have hBdomain : q t ∈ B.patch.occupiedGraphDomain B.patch.graph := by
      simp only [GraphPatch.occupiedGraphDomain, hBside, Set.mem_ofPred_eq, q]
      rw [← hgraph]
      linarith
    have hcarrier := htB.mpr hBdomain
    have hAdomain := htA.mp hcarrier
    simp only [GraphPatch.occupiedGraphDomain, hAside, Set.mem_ofPred_eq, q]
      at hAdomain
    linarith
  · exfalso
    have hAdomain : q t ∈ A.patch.occupiedGraphDomain A.patch.graph := by
      simp only [GraphPatch.occupiedGraphDomain, hAside, Set.mem_ofPred_eq, q]
      linarith
    have hcarrier := htA.mpr hAdomain
    have hBdomain := htB.mp hcarrier
    simp only [GraphPatch.occupiedGraphDomain, hBside, Set.mem_ofPred_eq, q]
      at hBdomain
    rw [← hgraph] at hBdomain
    linarith
  · rfl

end ActualRegularGraphChart

namespace ActualRegularHorizontalGraphChart

/-- Horizontal-coordinate analogue: actual occupied germs derive equality of
same-axis side labels. -/
theorem side_eq_of_overlap_of_occupiedGerms
    {carrier : Set PlanePoint}
    (A B : ActualRegularHorizontalGraphChart carrier) {y : ℝ}
    (h : OverlapAt A B y)
    (hA : ∀ᶠ q in 𝓝 (A.patch.graphTrace y),
      (q ∈ carrier ↔ q ∈ A.patch.occupiedGraphDomain))
    (hB : ∀ᶠ q in 𝓝 (B.patch.graphTrace y),
      (q ∈ carrier ↔ q ∈ B.patch.occupiedGraphDomain)) :
    A.patch.side = B.patch.side := by
  have hgraph : A.patch.graph y = B.patch.graph y :=
    congrArg Prod.fst h.point_eq
  let q : ℝ → PlanePoint := fun t => (A.patch.graph y + t, y)
  have hqA : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (A.patch.graphTrace y)) := by
    rw [show A.patch.graphTrace y = (A.patch.graph y, y) by rfl]
    have hfirst : ContinuousAt (fun t : ℝ => A.patch.graph y + t) 0 :=
      continuousAt_const.add continuousAt_id
    have hsecond : ContinuousAt (fun _t : ℝ => y) 0 :=
      continuousAt_const
    have hcontinuous := hfirst.prodMk hsecond
    simpa only [q, add_zero] using
      hcontinuous.mono_left nhdsWithin_le_nhds
  have hqB : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (B.patch.graphTrace y)) := by
    rw [← h.point_eq]
    exact hqA
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htA, htB, ht⟩ :=
    Filter.Eventually.exists
      ((hqA.eventually hA).and ((hqB.eventually hB).and hpos))
  cases hAside : A.patch.side <;> cases hBside : B.patch.side
  · rfl
  · exfalso
    have hBdomain : q t ∈ B.patch.occupiedGraphDomain := by
      simp only [HorizontalGraphPatch.occupiedGraphDomain, hBside,
        Set.mem_ofPred_eq, q]
      rw [← hgraph]
      linarith
    have hcarrier := htB.mpr hBdomain
    have hAdomain := htA.mp hcarrier
    simp only [HorizontalGraphPatch.occupiedGraphDomain, hAside,
      Set.mem_ofPred_eq, q] at hAdomain
    linarith
  · exfalso
    have hAdomain : q t ∈ A.patch.occupiedGraphDomain := by
      simp only [HorizontalGraphPatch.occupiedGraphDomain, hAside,
        Set.mem_ofPred_eq, q]
      linarith
    have hcarrier := htA.mpr hAdomain
    have hBdomain := htB.mp hcarrier
    simp only [HorizontalGraphPatch.occupiedGraphDomain, hBside,
      Set.mem_ofPred_eq, q] at hBdomain
    rw [← hgraph] at hBdomain
    linarith
  · rfl

end ActualRegularHorizontalGraphChart

/-- A genuine overlap between an existing `y = f(x)` chart and an `x = g(y)`
chart on the same actual frontier. -/
structure MixedOverlapAt {carrier : Set PlanePoint}
    (A : ActualRegularGraphChart carrier)
    (B : ActualRegularHorizontalGraphChart carrier) (x y : ℝ) : Prop where
  vertical_interior : x ∈ Ioo A.patch.a A.patch.b
  horizontal_interior : y ∈ Ioo B.patch.a B.patch.b
  point_eq : A.patch.graphTrace x = B.patch.graphTrace y
  vertical_occupied_side :
    ∀ᶠ q in 𝓝 (A.patch.graphTrace x),
      (q ∈ carrier ↔ q ∈ A.patch.occupiedGraphDomain A.patch.graph)
  horizontal_occupied_side :
    ∀ᶠ q in 𝓝 (B.patch.graphTrace y),
      (q ∈ carrier ↔ q ∈ B.patch.occupiedGraphDomain)

namespace MixedOverlapAt

variable {carrier : Set PlanePoint}
  {A : ActualRegularGraphChart carrier}
  {B : ActualRegularHorizontalGraphChart carrier}
  {x y : ℝ}

/-- The local frontier equations force the two graph functions to be local
inverses. -/
theorem eventuallyEq_comp_id
    (h : MixedOverlapAt A B x y) :
    (B.patch.graph ∘ A.patch.graph) =ᶠ[𝓝 x] id := by
  have htraceContinuous : Continuous A.patch.graphTrace :=
    continuous_id.prodMk A.patch.graph_contDiff.continuous
  have hBmem : A.patch.graphTrace x ∈ B.neighborhood := by
    rw [h.point_eq]
    exact B.graphTrace_mem_neighborhood h.horizontal_interior
  have hnearB : ∀ᶠ z in 𝓝 x, A.patch.graphTrace z ∈ B.neighborhood :=
    htraceContinuous.continuousAt (B.neighborhood_open.mem_nhds hBmem)
  have hnearA : ∀ᶠ z in 𝓝 x, z ∈ Ioo A.patch.a A.patch.b :=
    isOpen_Ioo.mem_nhds h.vertical_interior
  filter_upwards [hnearB, hnearA] with z hzB hzA
  have hzFrontier := A.graphTrace_mem_frontier hzA
  have hzImage : A.patch.graphTrace z ∈
      B.patch.graphTrace '' Ioo B.patch.a B.patch.b := by
    rw [← B.local_frontier]
    exact ⟨hzFrontier, hzB⟩
  rcases hzImage with ⟨w, hw, hzw⟩
  have hwEq : w = A.patch.graph z := by
    have := congrArg Prod.snd hzw
    simpa only [GraphPatch.graphTrace,
      HorizontalGraphPatch.graphTrace] using this
  have hxEq := congrArg Prod.fst hzw
  simpa only [Function.comp_apply, GraphPatch.graphTrace,
    HorizontalGraphPatch.graphTrace, hwEq, id_eq] using hxEq

/-- Consequently the two first derivatives are reciprocal; in particular a
coordinate change cannot be mistaken for an interface contact. -/
theorem deriv_mul_deriv_eq_one
    (h : MixedOverlapAt A B x y) :
    deriv B.patch.graph y * deriv A.patch.graph x = 1 := by
  have hyEq : A.patch.graph x = y := by
    exact congrArg Prod.snd h.point_eq
  have hA := (A.patch.graph_contDiff.differentiable (by norm_num) x).hasDerivAt
  have hB := (B.patch.graph_contDiff.differentiable (by norm_num) y).hasDerivAt
  have hcomp₀ : HasDerivAt (B.patch.graph ∘ A.patch.graph)
      (deriv B.patch.graph y * deriv A.patch.graph x) x := by
    have hB' : HasDerivAt B.patch.graph (deriv B.patch.graph y)
        (A.patch.graph x) := by simpa only [hyEq] using hB
    exact hB'.comp x hA
  have hid : HasDerivAt id
      (deriv B.patch.graph y * deriv A.patch.graph x) x :=
    hcomp₀.congr_of_eventuallyEq h.eventuallyEq_comp_id.symm
  simpa only [deriv_id] using hid.deriv.symm

/-- The actual occupied-side germs determine how the enum labels transform
under coordinate exchange.  Positive slope reverses the labels; negative
slope preserves them. -/
theorem occupiedSide_sign_compatibility
    (h : MixedOverlapAt A B x y) :
    (0 < deriv A.patch.graph x ∧
        B.patch.side.areaSign = -A.patch.side.areaSign) ∨
      (deriv A.patch.graph x < 0 ∧
        B.patch.side.areaSign = A.patch.side.areaSign) := by
  have hproduct := h.deriv_mul_deriv_eq_one
  have hmne : deriv A.patch.graph x ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at hproduct
    norm_num at hproduct
  have hfy : A.patch.graph x = y :=
    congrArg Prod.snd h.point_eq
  have hgy : B.patch.graph y = x :=
    congrArg Prod.fst h.point_eq |>.symm
  let q : ℝ → PlanePoint := fun t => (x + t, y)
  have hqA : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (A.patch.graphTrace x)) := by
    rw [show A.patch.graphTrace x = (x, y) by
      apply Prod.ext <;> simp [GraphPatch.graphTrace, hfy]]
    have hxcontinuous : ContinuousAt (fun t : ℝ => x + t) 0 :=
      continuousAt_const.add continuousAt_id
    have hycontinuous : ContinuousAt (fun _t : ℝ => y) 0 :=
      continuousAt_const
    have hcontinuous := hxcontinuous.prodMk hycontinuous
    simpa only [add_zero] using hcontinuous.mono_left nhdsWithin_le_nhds
  have hqB : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (B.patch.graphTrace y)) := by
    rw [← h.point_eq]
    exact hqA
  have hv := hqA.eventually h.vertical_occupied_side
  have hh := hqB.eventually h.horizontal_occupied_side
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  rcases lt_or_gt_of_ne hmne with hmneg | hmpos
  · right
    refine ⟨hmneg, ?_⟩
    have hslope :=
      (A.patch.graph_contDiff.differentiable (by norm_num) x).hasDerivAt
        |>.tendsto_slope_zero_right.eventually (Iio_mem_nhds hmneg)
    have hall := hv.and (hh.and (htpos.and hslope))
    rcases Filter.Eventually.exists hall with ⟨t, htV, htH, ht, htSlope⟩
    have hdiff : A.patch.graph (x + t) < A.patch.graph x := by
      rw [smul_eq_mul] at htSlope
      have hinv : 0 < t⁻¹ := inv_pos.mpr ht
      rcases mul_neg_iff.mp htSlope with hgood | hbad
      · exact sub_neg.mp hgood.2
      · exact (not_lt_of_ge hinv.le hbad.1).elim
    cases hAside : A.patch.side <;> cases hBside : B.patch.side
    · norm_num [OccupiedSide.areaSign]
    · exfalso
      have hiff : (y < A.patch.graph (x + t)) ↔
          B.patch.graph y < x + t := by
        simpa [q, GraphPatch.occupiedGraphDomain,
          HorizontalGraphPatch.occupiedGraphDomain, hAside, hBside] using
            htV.symm.trans htH
      have hcontra := hiff.mpr (by linarith [hgy])
      linarith [hdiff, hfy, hcontra]
    · exfalso
      have hiff : (A.patch.graph (x + t) < y) ↔
          x + t < B.patch.graph y := by
        simpa [q, GraphPatch.occupiedGraphDomain,
          HorizontalGraphPatch.occupiedGraphDomain, hAside, hBside] using
            htV.symm.trans htH
      exact (not_lt_of_ge (by linarith [hgy] : B.patch.graph y ≤ x + t))
        (hiff.mp (by linarith [hdiff, hfy]))
    · norm_num [OccupiedSide.areaSign]
  · left
    refine ⟨hmpos, ?_⟩
    have hslope :=
      (A.patch.graph_contDiff.differentiable (by norm_num) x).hasDerivAt
        |>.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hmpos)
    have hall := hv.and (hh.and (htpos.and hslope))
    rcases Filter.Eventually.exists hall with ⟨t, htV, htH, ht, htSlope⟩
    have hdiff : A.patch.graph x < A.patch.graph (x + t) := by
      rw [smul_eq_mul] at htSlope
      have hinv : 0 < t⁻¹ := inv_pos.mpr ht
      rcases mul_pos_iff.mp htSlope with hgood | hbad
      · exact sub_pos.mp hgood.2
      · exact (not_lt_of_ge hinv.le hbad.1).elim
    cases hAside : A.patch.side <;> cases hBside : B.patch.side
    · exfalso
      have hiff : (y < A.patch.graph (x + t)) ↔
          x + t < B.patch.graph y := by
        simpa [q, GraphPatch.occupiedGraphDomain,
          HorizontalGraphPatch.occupiedGraphDomain, hAside, hBside] using
            htV.symm.trans htH
      exact (not_lt_of_ge (by linarith [hgy] : B.patch.graph y ≤ x + t))
        (hiff.mp (by linarith [hdiff, hfy]))
    · norm_num [OccupiedSide.areaSign]
    · norm_num [OccupiedSide.areaSign]
    · exfalso
      have hiff : (A.patch.graph (x + t) < y) ↔
          B.patch.graph y < x + t := by
        simpa [q, GraphPatch.occupiedGraphDomain,
          HorizontalGraphPatch.occupiedGraphDomain, hAside, hBside] using
            htV.symm.trans htH
      have hcontra := hiff.mpr (by linarith [hgy])
      linarith [hdiff, hfy, hcontra]

/-- The two increasing coordinate traces have the same unit tangent at
positive `dy/dx` and opposite unit tangents at negative `dy/dx`.  This is
derived from the local inverse relation. -/
theorem normalizedTangent_compatibility
    (h : MixedOverlapAt A B x y) :
    (0 < deriv A.patch.graph x ∧
        CMVCurvatureIntegration.normalizedTangent
            B.patch.graphVelocity y =
          CMVCurvatureIntegration.normalizedTangent
            A.patch.graphVelocity x) ∨
      (deriv A.patch.graph x < 0 ∧
        CMVCurvatureIntegration.normalizedTangent
            B.patch.graphVelocity y =
          (-(CMVCurvatureIntegration.normalizedTangent
              A.patch.graphVelocity x).1,
            -(CMVCurvatureIntegration.normalizedTangent
              A.patch.graphVelocity x).2)) := by
  let m := deriv A.patch.graph x
  let n := deriv B.patch.graph y
  let sx := Real.sqrt (1 + m ^ 2)
  let sy := Real.sqrt (1 + n ^ 2)
  have hmn : n * m = 1 := by
    simpa only [m, n] using h.deriv_mul_deriv_eq_one
  have hmne : m ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at hmn
    norm_num at hmn
  have hsxSq : sx ^ 2 = 1 + m ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hsySq : sy ^ 2 = 1 + n ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hsxNonneg : 0 ≤ sx := Real.sqrt_nonneg _
  have hsyPos : 0 < sy := Real.sqrt_pos.2 (by positivity)
  rcases lt_or_gt_of_ne hmne with hmneg | hmpos
  · right
    refine ⟨hmneg, ?_⟩
    have hscaleNonneg : 0 ≤ (-m) * sy :=
      mul_nonneg (by linarith) hsyPos.le
    have hscaleSq : ((-m) * sy) ^ 2 = 1 + m ^ 2 := by
      rw [mul_pow, hsySq]
      have hmnSq := congrArg (fun z : ℝ => z ^ 2) hmn
      nlinarith
    have hsx : sx = (-m) * sy := by
      nlinarith
    unfold CMVCurvatureIntegration.normalizedTangent
    rw [A.patch.euclideanSpeed_graphVelocity,
      B.patch.euclideanSpeed_graphVelocity]
    change (n / sy, 1 / sy) = (-(1 / sx), -(m / sx))
    apply Prod.ext <;> dsimp
    · rw [hsx]
      field_simp [hmne, hsyPos.ne']
      nlinarith
    · rw [hsx]
      field_simp [hmne, hsyPos.ne']
  · left
    refine ⟨hmpos, ?_⟩
    have hscaleNonneg : 0 ≤ m * sy := mul_nonneg hmpos.le hsyPos.le
    have hscaleSq : (m * sy) ^ 2 = 1 + m ^ 2 := by
      rw [mul_pow, hsySq]
      have hmnSq := congrArg (fun z : ℝ => z ^ 2) hmn
      nlinarith
    have hsx : sx = m * sy := by
      nlinarith
    unfold CMVCurvatureIntegration.normalizedTangent
    rw [A.patch.euclideanSpeed_graphVelocity,
      B.patch.euclideanSpeed_graphVelocity]
    change (n / sy, 1 / sy) = (1 / sx, m / sx)
    apply Prod.ext <;> dsimp
    · rw [hsx]
      field_simp [hmne, hsyPos.ne']
      nlinarith
    · rw [hsx]
      field_simp [hmne, hsyPos.ne']

/-- The occupied-side curvature used by the two chart conventions agrees when
the coordinate traversal agrees and changes sign when it reverses. -/
theorem tangent_and_signedCurvature_compatibility
    (h : MixedOverlapAt A B x y) (K : ℝ) :
    (CMVCurvatureIntegration.normalizedTangent
          B.patch.graphVelocity y =
        CMVCurvatureIntegration.normalizedTangent
          A.patch.graphVelocity x ∧
      -(B.patch.side.areaSign * K) = A.patch.side.areaSign * K) ∨
    (CMVCurvatureIntegration.normalizedTangent
          B.patch.graphVelocity y =
        (-(CMVCurvatureIntegration.normalizedTangent
            A.patch.graphVelocity x).1,
          -(CMVCurvatureIntegration.normalizedTangent
            A.patch.graphVelocity x).2) ∧
      -(B.patch.side.areaSign * K) = -(A.patch.side.areaSign * K)) := by
  rcases h.normalizedTangent_compatibility with htangent | htangent
  · rcases h.occupiedSide_sign_compatibility with hside | hside
    · exact Or.inl ⟨htangent.2, by rw [hside.2]; ring⟩
    · linarith [htangent.1, hside.1]
  · rcases h.occupiedSide_sign_compatibility with hside | hside
    · linarith [htangent.1, hside.1]
    · exact Or.inr ⟨htangent.2, by rw [hside.2]⟩

/-- A mixed `y = f(x)` / `x = g(y)` overlap selects one supporting center.
The proof handles both same-direction and reversed-direction transitions. -/
theorem supportingCenter_eq_of_mixedOverlap
    (h : MixedOverlapAt A B x y) {K : ℝ} (hK : K ≠ 0) :
    A.patch.supportingCenter K x = B.patch.supportingCenter K y := by
  rcases h.tangent_and_signedCurvature_compatibility K with
    hsame | hreversed
  · unfold GraphPatch.supportingCenter
    unfold HorizontalGraphPatch.supportingCenter
    unfold CMVCurvatureIntegration.centerInvariant
    rw [h.point_eq, hsame.1, hsame.2]
  · unfold GraphPatch.supportingCenter
    unfold HorizontalGraphPatch.supportingCenter
    rw [hreversed.2]
    exact supportingCenter_eq_of_reversedContact
      (mul_ne_zero A.patch.side.areaSign_ne_zero hK)
      h.point_eq hreversed.1

/-- The mixed charts select the same literal circle, and each complete closed
chart trace lies on that circle. -/
theorem unique_supportingCircle_of_mixedOverlap
    (h : MixedOverlapAt A B x y) {K : ℝ} (hK : K ≠ 0)
    (hcurvA : ∀ z ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature z = K)
    (hcurvB : ∀ z ∈ Ioo B.patch.a B.patch.b,
      B.patch.orientedGraphCurvature z = K) :
    A.patch.supportingCircle K x = B.patch.supportingCircle K y ∧
      (∀ z ∈ Icc A.patch.a A.patch.b,
        A.patch.graphTrace z ∈ A.patch.supportingCircle K x) ∧
      (∀ z ∈ Icc B.patch.a B.patch.b,
        B.patch.graphTrace z ∈ B.patch.supportingCircle K y) := by
  have hcenter := h.supportingCenter_eq_of_mixedOverlap hK
  have hcircle :
      A.patch.supportingCircle K x = B.patch.supportingCircle K y := by
    ext p
    unfold GraphPatch.supportingCircle
    unfold HorizontalGraphPatch.supportingCircle
    simp only [Set.mem_ofPred_eq]
    rw [← hcenter]
    rcases h.tangent_and_signedCurvature_compatibility K with
      hsame | hreversed
    · rw [hsame.2]
    · rw [hreversed.2]
      simp only [one_div, inv_neg, neg_sq]
  refine ⟨hcircle, ?_, ?_⟩
  · intro z hz
    exact A.patch.closed_graph_circle_identity hcurvA hK
      ⟨h.vertical_interior.1.le, h.vertical_interior.2.le⟩ hz
  · intro z hz
    exact B.patch.closed_graph_circle_identity hcurvB hK
      ⟨h.horizontal_interior.1.le, h.horizontal_interior.2.le⟩ hz

/-- A mixed overlap selects one affine line in the zero-curvature case.
Occupied-side labels disappear completely from the statement and proof. -/
theorem unique_supportingLine_of_mixedOverlap
    (h : MixedOverlapAt A B x y)
    (hzeroA : ∀ z ∈ Ioo A.patch.a A.patch.b,
      A.patch.orientedGraphCurvature z = 0)
    (hzeroB : ∀ z ∈ Ioo B.patch.a B.patch.b,
      B.patch.orientedGraphCurvature z = 0) :
    A.patch.supportingLineAt x = B.patch.supportingLineAt y ∧
      (∀ z ∈ Icc A.patch.a A.patch.b,
        A.patch.graphTrace z ∈ A.patch.supportingLineAt x) ∧
      (∀ z ∈ Icc B.patch.a B.patch.b,
        B.patch.graphTrace z ∈ B.patch.supportingLineAt y) := by
  have hproduct := h.deriv_mul_deriv_eq_one
  have hmne : deriv A.patch.graph x ≠ 0 := by
    intro hm
    rw [hm, mul_zero] at hproduct
    norm_num at hproduct
  have hn :
      deriv B.patch.graph y = 1 / deriv A.patch.graph x := by
    apply (eq_div_iff hmne).2
    simpa only [one_mul] using hproduct
  have hfy : A.patch.graph x = y := by
    simpa only [GraphPatch.graphTrace,
      HorizontalGraphPatch.graphTrace] using congrArg Prod.snd h.point_eq
  have hgy : B.patch.graph y = x := by
    simpa only [GraphPatch.graphTrace,
      HorizontalGraphPatch.graphTrace] using congrArg Prod.fst h.point_eq.symm
  have hline :
      A.patch.supportingLineAt x = B.patch.supportingLineAt y := by
    ext p
    change
      (p.2 = A.patch.graph x + deriv A.patch.graph x * (p.1 - x)) ↔
      (p.1 = B.patch.graph y + deriv B.patch.graph y * (p.2 - y))
    rw [hfy, hgy, hn]
    constructor <;> intro hp
    · field_simp [hmne]
      nlinarith
    · field_simp [hmne] at hp
      nlinarith
  refine ⟨hline, ?_, ?_⟩
  · exact A.closedTrace_subset_supportingLineAt hzeroA
      ⟨h.vertical_interior.1.le, h.vertical_interior.2.le⟩
  · exact B.patch.closedTrace_subset_supportingLineAt hzeroB
      ⟨h.horizontal_interior.1.le, h.horizontal_interior.2.le⟩

end MixedOverlapAt

/-! ## A locus-indexed mixed-coordinate atlas -/

namespace MixedGraphAtlas

/-- One actual regular chart in either coordinate direction.  Curvature and
occupied-side truth are attached to the local frontier chart itself; no
supporting set, component image, or CMV branch is stored. -/
inductive RegularChart (carrier : Set PlanePoint) (K : ℝ) where
  | vertical
      (chart : ActualRegularGraphChart carrier)
      (curvature : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        chart.patch.orientedGraphCurvature z = K)
      (occupiedGerm : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        ∀ᶠ q in 𝓝 (chart.patch.graphTrace z),
          (q ∈ carrier ↔
            q ∈ chart.patch.occupiedGraphDomain chart.patch.graph))
  | horizontal
      (chart : ActualRegularHorizontalGraphChart carrier)
      (curvature : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        chart.patch.orientedGraphCurvature z = K)
      (occupiedGerm : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        ∀ᶠ q in 𝓝 (chart.patch.graphTrace z),
          (q ∈ carrier ↔ q ∈ chart.patch.occupiedGraphDomain))

namespace RegularChart

variable {carrier : Set PlanePoint} {K : ℝ}

def parameter : RegularChart carrier K → PlanePoint → ℝ
  | .vertical _ _ _, p => p.1
  | .horizontal _ _ _, p => p.2

def trace : RegularChart carrier K → ℝ → PlanePoint
  | .vertical A _ _, t => A.patch.graphTrace t
  | .horizontal A _ _, t => A.patch.graphTrace t

def parameterInterval : RegularChart carrier K → Set ℝ
  | .vertical A _ _ => Ioo A.patch.a A.patch.b
  | .horizontal A _ _ => Ioo A.patch.a A.patch.b

def neighborhood : RegularChart carrier K → Set PlanePoint
  | .vertical A _ _ => A.neighborhood
  | .horizontal A _ _ => A.neighborhood

theorem neighborhood_open (C : RegularChart carrier K) :
    IsOpen C.neighborhood := by
  cases C with
  | vertical A _ _ => exact A.neighborhood_open
  | horizontal A _ _ => exact A.neighborhood_open

theorem local_frontier (C : RegularChart carrier K) :
    frontier carrier ∩ C.neighborhood =
      C.trace '' C.parameterInterval := by
  cases C with
  | vertical A _ _ => exact A.local_frontier
  | horizontal A _ _ => exact A.local_frontier

theorem parameter_interior_and_trace_eq_of_mem
    (C : RegularChart carrier K) {p : PlanePoint}
    (hp : p ∈ frontier carrier ∩ C.neighborhood) :
    C.parameter p ∈ C.parameterInterval ∧
      C.trace (C.parameter p) = p := by
  rw [C.local_frontier] at hp
  rcases hp with ⟨t, ht, htp⟩
  cases C with
  | vertical A hcurv hoccupied =>
      have htEq : t = p.1 := by
        have hfst := congrArg Prod.fst htp
        simpa only [trace, GraphPatch.graphTrace] using hfst
      simpa only [parameter, parameterInterval, trace, ← htEq] using
        And.intro ht htp
  | horizontal A hcurv hoccupied =>
      have htEq : t = p.2 := by
        have hsnd := congrArg Prod.snd htp
        simpa only [trace, HorizontalGraphPatch.graphTrace] using hsnd
      simpa only [parameter, parameterInterval, trace, ← htEq] using
        And.intro ht htp

def supportAtParameter (C : RegularChart carrier K) (t : ℝ) :
    Set PlanePoint :=
  if K = 0 then
    match C with
    | .vertical A _ _ => A.patch.supportingLineAt t
    | .horizontal A _ _ => A.patch.supportingLineAt t
  else
    match C with
    | .vertical A _ _ => A.patch.supportingCircle K t
    | .horizontal A _ _ => A.patch.supportingCircle K t

def supportAt (C : RegularChart carrier K) (p : PlanePoint) :
    Set PlanePoint :=
  C.supportAtParameter (C.parameter p)

/-- One chart's support is independent of its closed anchor parameter. -/
theorem supportAtParameter_eq_of_anchors
    (C : RegularChart carrier K) {s t : ℝ}
    (hs : s ∈ closure C.parameterInterval)
    (ht : t ∈ closure C.parameterInterval) :
    C.supportAtParameter s = C.supportAtParameter t := by
  cases C with
  | vertical A hcurv hoccupied =>
      have hs' : s ∈ Icc A.patch.a A.patch.b := by
        simpa only [parameterInterval, closure_Ioo A.patch.a_lt_b.ne] using hs
      have ht' : t ∈ Icc A.patch.a A.patch.b := by
        simpa only [parameterInterval, closure_Ioo A.patch.a_lt_b.ne] using ht
      unfold supportAtParameter
      split_ifs with hzero
      · exact A.supportingLineAt_eq_of_anchors
          (fun z hz => by rw [hcurv z hz, hzero]) hs' ht'
      · exact A.supportingCircle_eq_of_anchors hzero hcurv hs' ht'
  | horizontal A hcurv hoccupied =>
      have hs' : s ∈ Icc A.patch.a A.patch.b := by
        simpa only [parameterInterval, closure_Ioo A.patch.a_lt_b.ne] using hs
      have ht' : t ∈ Icc A.patch.a A.patch.b := by
        simpa only [parameterInterval, closure_Ioo A.patch.a_lt_b.ne] using ht
      unfold supportAtParameter
      split_ifs with hzero
      · exact A.patch.supportingLineAt_eq_of_anchors
          (fun z hz => by rw [hcurv z hz, hzero]) hs' ht'
      · exact A.patch.supportingCircle_eq_of_anchors hzero hcurv hs' ht'

/-- Two actual mixed-atlas charts meeting at one frontier point select the
same support.  Same-axis occupied-side equality is derived from the two
truthful carrier germs; mixed-axis orientation changes use `MixedOverlapAt`. -/
theorem supportAtParameter_eq_of_actual_overlap
    (C D : RegularChart carrier K) {s t : ℝ}
    (hs : s ∈ C.parameterInterval) (ht : t ∈ D.parameterInterval)
    (hpoint : C.trace s = D.trace t) :
    C.supportAtParameter s = D.supportAtParameter t := by
  cases C with
  | vertical A hcurvA hoccupiedA =>
      cases D with
      | vertical B hcurvB hoccupiedB =>
          have hst : s = t := by
            have hfst := congrArg Prod.fst hpoint
            simpa only [trace, GraphPatch.graphTrace] using hfst
          subst t
          have hover : ActualRegularGraphChart.OverlapAt A B s :=
            ⟨hs, ht, hpoint⟩
          have hside := A.side_eq_of_overlap_of_occupiedGerms B hover
            (hoccupiedA s hs) (hoccupiedB s ht)
          unfold supportAtParameter
          split_ifs with hzero
          · exact (ActualRegularGraphChart.unique_supportingLine_of_overlap
              A B hover
              (fun z hz => by rw [hcurvA z hz, hzero])
              (fun z hz => by rw [hcurvB z hz, hzero])).1
          · exact (ActualRegularGraphChart.unique_supportingCircle_of_overlap
              A B hover hside hzero hcurvA hcurvB).1
      | horizontal B hcurvB hoccupiedB =>
          have hover : MixedOverlapAt A B s t :=
            ⟨hs, ht, hpoint, hoccupiedA s hs, hoccupiedB t ht⟩
          unfold supportAtParameter
          split_ifs with hzero
          · exact (hover.unique_supportingLine_of_mixedOverlap
              (fun z hz => by rw [hcurvA z hz, hzero])
              (fun z hz => by rw [hcurvB z hz, hzero])).1
          · exact (hover.unique_supportingCircle_of_mixedOverlap
              hzero hcurvA hcurvB).1
  | horizontal A hcurvA hoccupiedA =>
      cases D with
      | vertical B hcurvB hoccupiedB =>
          have hover : MixedOverlapAt B A t s :=
            ⟨ht, hs, hpoint.symm, hoccupiedB t ht, hoccupiedA s hs⟩
          unfold supportAtParameter
          split_ifs with hzero
          · exact (hover.unique_supportingLine_of_mixedOverlap
              (fun z hz => by rw [hcurvB z hz, hzero])
              (fun z hz => by rw [hcurvA z hz, hzero])).1.symm
          · exact (hover.unique_supportingCircle_of_mixedOverlap
              hzero hcurvB hcurvA).1.symm
      | horizontal B hcurvB hoccupiedB =>
          have hst : s = t := by
            have hsnd := congrArg Prod.snd hpoint
            simpa only [trace, HorizontalGraphPatch.graphTrace] using hsnd
          subst t
          have hover : ActualRegularHorizontalGraphChart.OverlapAt A B s :=
            ⟨hs, ht, hpoint⟩
          have hside := A.side_eq_of_overlap_of_occupiedGerms B hover
            (hoccupiedA s hs) (hoccupiedB s ht)
          unfold supportAtParameter
          split_ifs with hzero
          · exact
              (ActualRegularHorizontalGraphChart.unique_supportingLine_of_overlap
                A B hover
                (fun z hz => by rw [hcurvA z hz, hzero])
                (fun z hz => by rw [hcurvB z hz, hzero])).1
          · exact
              (ActualRegularHorizontalGraphChart.unique_supportingCircle_of_overlap
                A B hover hside hzero hcurvA hcurvB).1


/-- Each mixed regular chart is not only contained in its derived support:
near every interior base point, the support itself is exactly the actual graph
branch.  The sign cuts in the curved cases discard the opposite branch of the
same circle.  This is the local relative-openness input for maximal-component
saturation and keeps the affine and circular alternatives explicit. -/
theorem exists_open_supportAt_inter_subset_traceImage
    (C : RegularChart carrier K) (p : PlanePoint)
    (hp : C.parameter p ∈ C.parameterInterval)
    (hbase : C.trace (C.parameter p) = p) :
    ∃ W : Set PlanePoint, IsOpen W ∧ p ∈ W ∧
      C.supportAt p ∩ W ⊆ C.trace '' C.parameterInterval := by
  cases hC : C with
  | vertical A hcurv hoccupied =>
      simp only [hC, parameter, parameterInterval, trace] at hp hbase ⊢
      by_cases hK : K = 0
      · let W : Set PlanePoint :=
          A.neighborhood ∩ Prod.fst ⁻¹' Ioo A.patch.a A.patch.b
        refine ⟨W, A.neighborhood_open.inter
          (isOpen_Ioo.preimage continuous_fst), ?_, ?_⟩
        · refine ⟨?_, hp⟩
          rw [← hbase]
          exact A.graphTrace_mem_neighborhood hp
        · intro q hq
          have hqSupport := hq.1
          have hqParameter := hq.2.2
          have hgraphSupport := A.closedTrace_subset_supportingLineAt
            (fun z hz => by rw [hcurv z hz, hK])
            ⟨hp.1.le, hp.2.le⟩ q.1
            ⟨hqParameter.1.le, hqParameter.2.le⟩
          unfold supportAt supportAtParameter at hqSupport
          simp only [parameter, hK, ↓reduceIte] at hqSupport
          have hqEq : q = A.patch.graphTrace q.1 := by
            apply Prod.ext
            · rfl
            · exact hqSupport.trans hgraphSupport.symm
          exact ⟨q.1, hqParameter, hqEq.symm⟩
      · let center := A.patch.supportingCenter K p.1
        let d := A.patch.graph p.1 - center.2
        let W : Set PlanePoint :=
          A.neighborhood ∩
            (Prod.fst ⁻¹' Ioo A.patch.a A.patch.b ∩
              ({q | 0 < (q.2 - center.2) * d} ∩
                {q | 0 < (A.patch.graph q.1 - center.2) * d}))
        have hd : d ≠ 0 := by
          dsimp only [d, center]
          unfold GraphPatch.supportingCenter
            CMVCurvatureIntegration.centerInvariant
            CMVCurvatureIntegration.normalizedTangent
          simp only [GraphPatch.graphTrace, GraphPatch.graphVelocity,
            A.patch.euclideanSpeed_graphVelocity]
          have hsqrt : √(1 + deriv A.patch.graph p.1 ^ 2) ≠ 0 := by
            positivity
          have hterm : 1 / √(1 + deriv A.patch.graph p.1 ^ 2) /
              (A.patch.side.areaSign * K) ≠ 0 :=
            div_ne_zero (one_div_ne_zero hsqrt)
              (mul_ne_zero A.patch.side.areaSign_ne_zero hK)
          intro hzero
          apply hterm
          linarith
        have hWopen : IsOpen W := by
          apply A.neighborhood_open.inter
          apply (isOpen_Ioo.preimage continuous_fst).inter
          apply (isOpen_lt continuous_const
            ((continuous_snd.sub continuous_const).mul continuous_const)).inter
          exact isOpen_lt continuous_const
            ((((A.patch.graph_contDiff.continuous.comp continuous_fst).sub
              continuous_const).mul continuous_const))
        refine ⟨W, hWopen, ?_, ?_⟩
        · have hpNeighborhood : p ∈ A.neighborhood := by
            rw [← hbase]
            exact A.graphTrace_mem_neighborhood hp
          have hpy : p.2 = A.patch.graph p.1 := by
            have := congrArg Prod.snd hbase
            simpa only [GraphPatch.graphTrace] using this.symm
          refine ⟨hpNeighborhood, hp, ?_, ?_⟩
          · change 0 < (p.2 - center.2) * d
            rw [hpy]
            exact mul_self_pos.mpr hd
          · change 0 < (A.patch.graph p.1 - center.2) * d
            exact mul_self_pos.mpr hd
        · intro q hq
          have hqSupport := hq.1
          have hqParameter := hq.2.2.1
          have hqSign := hq.2.2.2.1
          have hgraphSign := hq.2.2.2.2
          have hgraphSupport := A.patch.closed_graph_circle_identity hcurv hK
            ⟨hp.1.le, hp.2.le⟩
            ⟨hqParameter.1.le, hqParameter.2.le⟩
          unfold supportAt supportAtParameter at hqSupport
          simp only [parameter, hK, ↓reduceIte] at hqSupport
          unfold GraphPatch.supportingCircle at hqSupport hgraphSupport
          simp only [GraphPatch.graphTrace] at hgraphSupport
          change (q.1 - center.1) ^ 2 + (q.2 - center.2) ^ 2 =
            (1 / (A.patch.side.areaSign * K)) ^ 2 at hqSupport
          change (q.1 - center.1) ^ 2 +
              (A.patch.graph q.1 - center.2) ^ 2 =
            (1 / (A.patch.side.areaSign * K)) ^ 2 at hgraphSupport
          change 0 < (q.2 - center.2) * d at hqSign
          change 0 < (A.patch.graph q.1 - center.2) * d at hgraphSign
          have hsquares :
              (q.2 - center.2) ^ 2 =
                (A.patch.graph q.1 - center.2) ^ 2 := by
            nlinarith [hqSupport, hgraphSupport]
          have hproduct : 0 <
              (q.2 - center.2) * (A.patch.graph q.1 - center.2) := by
            rcases lt_or_gt_of_ne hd with hdneg | hdpos
            · exact mul_pos_of_neg_of_neg (by nlinarith [hqSign])
                (by nlinarith [hgraphSign])
            · exact mul_pos (by nlinarith [hqSign])
                (by nlinarith [hgraphSign])
          have hqEqY : q.2 = A.patch.graph q.1 := by
            rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with heq | heq
            · linarith
            · nlinarith [hproduct]
          refine ⟨q.1, hqParameter, ?_⟩
          exact Prod.ext rfl hqEqY.symm
  | horizontal A hcurv hoccupied =>
      simp only [hC, parameter, parameterInterval, trace] at hp hbase ⊢
      by_cases hK : K = 0
      · let W : Set PlanePoint :=
          A.neighborhood ∩ Prod.snd ⁻¹' Ioo A.patch.a A.patch.b
        refine ⟨W, A.neighborhood_open.inter
          (isOpen_Ioo.preimage continuous_snd), ?_, ?_⟩
        · refine ⟨?_, hp⟩
          rw [← hbase]
          exact A.graphTrace_mem_neighborhood hp
        · intro q hq
          have hqSupport := hq.1
          have hqParameter := hq.2.2
          have hgraphSupport := A.patch.closedTrace_subset_supportingLineAt
            (fun z hz => by rw [hcurv z hz, hK])
            ⟨hp.1.le, hp.2.le⟩ q.2
            ⟨hqParameter.1.le, hqParameter.2.le⟩
          unfold supportAt supportAtParameter at hqSupport
          simp only [parameter, hK, ↓reduceIte] at hqSupport
          have hqEq : q = A.patch.graphTrace q.2 := by
            apply Prod.ext
            · exact hqSupport.trans hgraphSupport.symm
            · rfl
          exact ⟨q.2, hqParameter, hqEq.symm⟩
      · let center := A.patch.supportingCenter K p.2
        let d := A.patch.graph p.2 - center.1
        let W : Set PlanePoint :=
          A.neighborhood ∩
            (Prod.snd ⁻¹' Ioo A.patch.a A.patch.b ∩
              ({q | 0 < (q.1 - center.1) * d} ∩
                {q | 0 < (A.patch.graph q.2 - center.1) * d}))
        have hd : d ≠ 0 := by
          dsimp only [d, center]
          unfold HorizontalGraphPatch.supportingCenter
            CMVCurvatureIntegration.centerInvariant
            CMVCurvatureIntegration.normalizedTangent
          simp only [HorizontalGraphPatch.graphTrace,
            HorizontalGraphPatch.graphVelocity,
            A.patch.euclideanSpeed_graphVelocity]
          have hsqrt : √(1 + deriv A.patch.graph p.2 ^ 2) ≠ 0 := by
            positivity
          have hterm : 1 / √(1 + deriv A.patch.graph p.2 ^ 2) /
              (-(A.patch.side.areaSign * K)) ≠ 0 :=
            div_ne_zero (one_div_ne_zero hsqrt)
              (neg_ne_zero.mpr
                (mul_ne_zero A.patch.side.areaSign_ne_zero hK))
          intro hzero
          apply hterm
          linarith
        have hWopen : IsOpen W := by
          apply A.neighborhood_open.inter
          apply (isOpen_Ioo.preimage continuous_snd).inter
          apply (isOpen_lt continuous_const
            ((continuous_fst.sub continuous_const).mul continuous_const)).inter
          exact isOpen_lt continuous_const
            ((((A.patch.graph_contDiff.continuous.comp continuous_snd).sub
              continuous_const).mul continuous_const))
        refine ⟨W, hWopen, ?_, ?_⟩
        · have hpNeighborhood : p ∈ A.neighborhood := by
            rw [← hbase]
            exact A.graphTrace_mem_neighborhood hp
          have hpx : p.1 = A.patch.graph p.2 := by
            have := congrArg Prod.fst hbase
            simpa only [HorizontalGraphPatch.graphTrace] using this.symm
          refine ⟨hpNeighborhood, hp, ?_, ?_⟩
          · change 0 < (p.1 - center.1) * d
            rw [hpx]
            exact mul_self_pos.mpr hd
          · change 0 < (A.patch.graph p.2 - center.1) * d
            exact mul_self_pos.mpr hd
        · intro q hq
          have hqSupport := hq.1
          have hqParameter := hq.2.2.1
          have hqSign := hq.2.2.2.1
          have hgraphSign := hq.2.2.2.2
          have hgraphSupport := A.patch.closed_graph_circle_identity hcurv hK
            ⟨hp.1.le, hp.2.le⟩
            ⟨hqParameter.1.le, hqParameter.2.le⟩
          unfold supportAt supportAtParameter at hqSupport
          simp only [parameter, hK, ↓reduceIte] at hqSupport
          unfold HorizontalGraphPatch.supportingCircle at hqSupport hgraphSupport
          simp only [HorizontalGraphPatch.graphTrace] at hgraphSupport
          change (q.1 - center.1) ^ 2 + (q.2 - center.2) ^ 2 =
            (1 / (-(A.patch.side.areaSign * K))) ^ 2 at hqSupport
          change (A.patch.graph q.2 - center.1) ^ 2 +
              (q.2 - center.2) ^ 2 =
            (1 / (-(A.patch.side.areaSign * K))) ^ 2 at hgraphSupport
          change 0 < (q.1 - center.1) * d at hqSign
          change 0 < (A.patch.graph q.2 - center.1) * d at hgraphSign
          have hsquares :
              (q.1 - center.1) ^ 2 =
                (A.patch.graph q.2 - center.1) ^ 2 := by
            nlinarith [hqSupport, hgraphSupport]
          have hproduct : 0 <
              (q.1 - center.1) * (A.patch.graph q.2 - center.1) := by
            rcases lt_or_gt_of_ne hd with hdneg | hdpos
            · exact mul_pos_of_neg_of_neg (by nlinarith [hqSign])
                (by nlinarith [hgraphSign])
            · exact mul_pos (by nlinarith [hqSign])
                (by nlinarith [hgraphSign])
          have hqEqX : q.1 = A.patch.graph q.2 := by
            rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with heq | heq
            · linarith
            · nlinarith [hproduct]
          refine ⟨q.2, hqParameter, ?_⟩
          exact Prod.ext hqEqX.symm rfl
end RegularChart

/-- An unlabelled atlas covering one actual regular locus in both coordinate
directions.  It stores no support equality, finite chart count, component
image, endpoint order, or selected CMV configuration. -/
structure BranchNeutralMixedGraphAtlas
    (carrier locus : Set PlanePoint) (K : ℝ) where
  locus_subset_frontier : locus ⊆ frontier carrier
  chart : locus → RegularChart carrier K
  chart_window_subset_locus : ∀ p : locus,
    frontier carrier ∩ (chart p).neighborhood ⊆ locus
  base_interior : ∀ p : locus,
    (chart p).parameter p.1 ∈ (chart p).parameterInterval
  base_eq : ∀ p : locus,
    (chart p).trace ((chart p).parameter p.1) = p.1

namespace BranchNeutralMixedGraphAtlas

variable {carrier locus : Set PlanePoint} {K : ℝ}

def supportAt (A : BranchNeutralMixedGraphAtlas carrier locus K)
    (p : locus) : Set PlanePoint :=
  (A.chart p).supportAt p.1

/-- Every complete open trace of a selected chart belongs to the same actual
atlas locus. -/
theorem chartTrace_image_subset_locus
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    (A.chart p).trace '' (A.chart p).parameterInterval ⊆ locus := by
  intro q hq
  apply A.chart_window_subset_locus p
  rw [(A.chart p).local_frontier]
  exact hq

/-- A selected mixed chart trace is preconnected, independently of its
coordinate direction. -/
theorem chartTrace_image_isPreconnected
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    IsPreconnected
      ((A.chart p).trace '' (A.chart p).parameterInterval) := by
  cases hC : A.chart p with
  | vertical C hcurv hoccupied =>
      simp only [RegularChart.trace, RegularChart.parameterInterval]
      exact isPreconnected_Ioo.image _
        (continuous_id.prodMk C.patch.graph_contDiff.continuous).continuousOn
  | horizontal C hcurv hoccupied =>
      simp only [RegularChart.trace, RegularChart.parameterInterval]
      exact isPreconnected_Ioo.image _
        (C.patch.graph_contDiff.continuous.prodMk continuous_id).continuousOn

/-- The actual connected component is relatively open in its derived support:
near each base point, every support point belongs to the same component.  This
is stronger than one-way support containment and remains valid at switches
between the two graph coordinates. -/
theorem exists_open_supportAt_inter_subset_connectedComponentIn
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    ∃ W : Set PlanePoint, IsOpen W ∧ p.1 ∈ W ∧
      A.supportAt p ∩ W ⊆ connectedComponentIn locus p.1 := by
  rcases (A.chart p).exists_open_supportAt_inter_subset_traceImage p.1
      (A.base_interior p) (A.base_eq p) with
    ⟨W, hWopen, hpW, hWsupport⟩
  refine ⟨W, hWopen, hpW, ?_⟩
  intro q hq
  have hqTrace := hWsupport hq
  have hpTrace :
      p.1 ∈ (A.chart p).trace '' (A.chart p).parameterInterval :=
    ⟨(A.chart p).parameter p.1, A.base_interior p, A.base_eq p⟩
  exact (A.chartTrace_image_isPreconnected p).subset_connectedComponentIn
    hpTrace (A.chartTrace_image_subset_locus p) hqTrace

/-- Actual chart overlap and anchor invariance make the mixed support locally
constant on the topological locus. -/
theorem supportAt_eq_of_mem_neighborhood
    (A : BranchNeutralMixedGraphAtlas carrier locus K)
    (p q : locus) (hq : q.1 ∈ (A.chart p).neighborhood) :
    A.supportAt q = A.supportAt p := by
  have hqChart := (A.chart p).parameter_interior_and_trace_eq_of_mem
    ⟨A.locus_subset_frontier q.2, hq⟩
  have hover := RegularChart.supportAtParameter_eq_of_actual_overlap
    (A.chart q) (A.chart p) (A.base_interior q) hqChart.1
      ((A.base_eq q).trans hqChart.2.symm)
  have hqClosure :
      (A.chart p).parameter q.1 ∈
        closure (A.chart p).parameterInterval :=
    subset_closure hqChart.1
  have hpClosure :
      (A.chart p).parameter p.1 ∈
        closure (A.chart p).parameterInterval :=
    subset_closure (A.base_interior p)
  have hanchor := (A.chart p).supportAtParameter_eq_of_anchors
    hqClosure hpClosure
  exact hover.trans hanchor

/-- The support selected by actual mixed charts is locally constant, including
across coordinate switches and same-axis overlaps. -/
theorem supportAt_isLocallyConstant
    (A : BranchNeutralMixedGraphAtlas carrier locus K) :
    IsLocallyConstant A.supportAt := by
  rw [IsLocallyConstant.iff_exists_open]
  intro p
  let U : Set locus := Subtype.val ⁻¹' (A.chart p).neighborhood
  have hUopen : IsOpen U :=
    (A.chart p).neighborhood_open.preimage continuous_subtype_val
  have hpNeighborhood : p.1 ∈ (A.chart p).neighborhood := by
    have hpTrace :
        (A.chart p).trace ((A.chart p).parameter p.1) ∈
          (A.chart p).trace '' (A.chart p).parameterInterval :=
      ⟨(A.chart p).parameter p.1, A.base_interior p, rfl⟩
    rw [← (A.chart p).local_frontier] at hpTrace
    rw [A.base_eq p] at hpTrace
    exact hpTrace.2
  refine ⟨U, hUopen, hpNeighborhood, ?_⟩
  intro q hq
  exact A.supportAt_eq_of_mem_neighborhood p q hq

/-- Every mixed-atlas base point lies on its derived support. -/
theorem base_mem_supportAt
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    p.1 ∈ A.supportAt p := by
  have hbase := A.base_eq p
  have hinterior := A.base_interior p
  cases hC : A.chart p with
  | vertical C hcurv hoccupied =>
      simp only [hC, RegularChart.parameter, RegularChart.parameterInterval,
        RegularChart.trace] at hbase hinterior
      unfold supportAt RegularChart.supportAt
      simp only [hC, RegularChart.parameter]
      unfold RegularChart.supportAtParameter
      split_ifs with hzero
      · rw [← hbase]
        exact C.closedTrace_subset_supportingLineAt
          (fun z hz => by rw [hcurv z hz, hzero])
          ⟨hinterior.1.le, hinterior.2.le⟩ p.1.1
            ⟨hinterior.1.le, hinterior.2.le⟩
      · rw [← hbase]
        exact C.patch.closed_graph_circle_identity hcurv hzero
          ⟨hinterior.1.le, hinterior.2.le⟩
          ⟨hinterior.1.le, hinterior.2.le⟩
  | horizontal C hcurv hoccupied =>
      simp only [hC, RegularChart.parameter, RegularChart.parameterInterval,
        RegularChart.trace] at hbase hinterior
      unfold supportAt RegularChart.supportAt
      simp only [hC, RegularChart.parameter]
      unfold RegularChart.supportAtParameter
      split_ifs with hzero
      · rw [← hbase]
        exact C.patch.closedTrace_subset_supportingLineAt
          (fun z hz => by rw [hcurv z hz, hzero])
          ⟨hinterior.1.le, hinterior.2.le⟩ p.1.2
            ⟨hinterior.1.le, hinterior.2.le⟩
      · rw [← hbase]
        exact C.patch.closed_graph_circle_identity hcurv hzero
          ⟨hinterior.1.le, hinterior.2.le⟩
          ⟨hinterior.1.le, hinterior.2.le⟩


/-- Supporting circle or line agreement now propagates through actual
topological connected components of a mixed-coordinate locus; callers no
longer supply a `ReflTransGen` overlap chain. -/
theorem supportAt_eq_of_mem_connectedComponent
    (A : BranchNeutralMixedGraphAtlas carrier locus K)
    (p q : locus) (hq : q ∈ connectedComponent p) :
    A.supportAt q = A.supportAt p :=
  A.supportAt_isLocallyConstant.apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hq mem_connectedComponent
/-- One support contains the whole actual connected component of a mixed
atlas, including coordinate-tangency crossings. -/
theorem connectedComponent_subset_supportAt
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    ((↑) : locus → PlanePoint) '' connectedComponent p ⊆ A.supportAt p := by
  rintro _ ⟨q, hq, rfl⟩
  rw [← A.supportAt_eq_of_mem_connectedComponent p q hq]
  exact A.base_mem_supportAt q

/-- Ambient form of component support containment. -/
theorem connectedComponentIn_subset_supportAt
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    connectedComponentIn locus p.1 ⊆ A.supportAt p := by
  rw [connectedComponentIn_eq_image p.2]
  exact A.connectedComponent_subset_supportAt p

/-- Relative-openness form of local support saturation.  The actual component,
viewed inside its one derived support, is open; this rules out an interior
endpoint even when continuation changes graph coordinates. -/
theorem connectedComponentIn_isOpen_in_supportAt
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    IsOpen {q : A.supportAt p |
      q.1 ∈ connectedComponentIn locus p.1} := by
  rw [isOpen_iff_forall_mem_open]
  intro q hq
  have hqLocus : q.1 ∈ locus :=
    connectedComponentIn_subset locus p.1 hq
  let q' : locus := ⟨q.1, hqLocus⟩
  have hqSubtype : q' ∈ connectedComponent p := by
    rw [connectedComponentIn_eq_image p.2] at hq
    rcases hq with ⟨r, hr, hrq⟩
    have hrq' : r = q' := Subtype.ext hrq
    rwa [← hrq']
  have hsupportEq : A.supportAt q' = A.supportAt p :=
    A.supportAt_eq_of_mem_connectedComponent p q' hqSubtype
  rcases A.exists_open_supportAt_inter_subset_connectedComponentIn q' with
    ⟨W, hWopen, hqW, hWsubset⟩
  refine ⟨Subtype.val ⁻¹' W, ?_,
    hWopen.preimage continuous_subtype_val, hqW⟩
  intro r hr
  have hrSupportQ : r.1 ∈ A.supportAt q' := by
    rw [hsupportEq]
    exact r.2
  have hrComponentQ := hWsubset ⟨hrSupportQ, hr⟩
  have hcomponentEq : connectedComponentIn locus p.1 =
      connectedComponentIn locus q'.1 :=
    connectedComponentIn_eq hq
  rwa [hcomponentEq]

/-- Center of the literal nonzero-curvature support selected at a mixed-atlas
base point.  This is computed from its actual local chart. -/
def supportingCenterAt
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus) :
    PlanePoint :=
  match A.chart p with
  | .vertical C _ _ => C.patch.supportingCenter K p.1.1
  | .horizontal C _ _ => C.patch.supportingCenter K p.1.2

/-- In the nonzero branch, the mixed support is exactly one positive-radius
`circleValue` zero locus, independently of chart direction or occupied-side
label. -/
theorem supportAt_eq_circleValue_zero
    (A : BranchNeutralMixedGraphAtlas carrier locus K) (p : locus)
    (hK : K ≠ 0) :
    A.supportAt p =
      {q : PlanePoint |
        CMVFigureFour.circleValue (A.supportingCenterAt p) |1 / K| q = 0} := by
  unfold supportAt RegularChart.supportAt RegularChart.supportAtParameter
    supportingCenterAt
  rw [if_neg hK]
  cases A.chart p with
  | vertical C hcurv hoccupied =>
      simp only [RegularChart.parameter]
      have hradii :
          (1 / (C.patch.side.areaSign * K)) ^ 2 = (1 / K) ^ 2 := by
        field_simp [hK, C.patch.side.areaSign_ne_zero]
        nlinarith [C.patch.side.areaSign_mul_self]
      ext q
      simp only [GraphPatch.supportingCircle, Set.mem_ofPred_eq,
        CMVFigureFour.circleValue]
      rw [sq_abs, sub_eq_zero, hradii]
  | horizontal C hcurv hoccupied =>
      simp only [RegularChart.parameter]
      have hradii :
          (1 / (-(C.patch.side.areaSign * K))) ^ 2 = (1 / K) ^ 2 := by
        field_simp [hK, C.patch.side.areaSign_ne_zero]
        nlinarith [C.patch.side.areaSign_mul_self]
      ext q
      simp only [HorizontalGraphPatch.supportingCircle, Set.mem_ofPred_eq,
        CMVFigureFour.circleValue]
      rw [sq_abs, sub_eq_zero, hradii]

end BranchNeutralMixedGraphAtlas
end MixedGraphAtlas

/-! ## Propagation through a mixed-coordinate overlap component -/

namespace MixedChartComponent

variable {carrier : Set PlanePoint} {K : ℝ}

/-- A nonzero-curvature chart node carries only its actual chart, anchor, and
the common occupied curvature.  No center or support set is stored. -/
inductive CurvedChart (carrier : Set PlanePoint) (K : ℝ) where
  | vertical (chart : ActualRegularGraphChart carrier) (parameter : ℝ)
      (curvature : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        chart.patch.orientedGraphCurvature z = K)
  | horizontal (chart : ActualRegularHorizontalGraphChart carrier)
      (parameter : ℝ)
      (curvature : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        chart.patch.orientedGraphCurvature z = K)

def curvedSupport : CurvedChart carrier K → Set PlanePoint
  | .vertical A x _ => A.patch.supportingCircle K x
  | .horizontal B y _ => B.patch.supportingCircle K y

/-- Edges in the mixed overlap graph.  Both directions are constructors, so
its reflexive-transitive closure is the undirected overlap component. -/
inductive CurvedOverlap :
    CurvedChart carrier K → CurvedChart carrier K → Prop
  | vertical_vertical
      (A B : ActualRegularGraphChart carrier) (x : ℝ)
      (hcurvA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = K)
      (hcurvB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = K)
      (overlap : ActualRegularGraphChart.OverlapAt A B x)
      (sameSide : A.patch.side = B.patch.side) :
      CurvedOverlap (.vertical A x hcurvA) (.vertical B x hcurvB)
  | horizontal_horizontal
      (A B : ActualRegularHorizontalGraphChart carrier) (y : ℝ)
      (hcurvA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = K)
      (hcurvB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = K)
      (overlap : ActualRegularHorizontalGraphChart.OverlapAt A B y)
      (sameSide : A.patch.side = B.patch.side) :
      CurvedOverlap (.horizontal A y hcurvA) (.horizontal B y hcurvB)
  | vertical_horizontal
      (A : ActualRegularGraphChart carrier)
      (B : ActualRegularHorizontalGraphChart carrier) (x y : ℝ)
      (hcurvA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = K)
      (hcurvB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = K)
      (overlap : MixedOverlapAt A B x y) :
      CurvedOverlap (.vertical A x hcurvA) (.horizontal B y hcurvB)
  | horizontal_vertical
      (A : ActualRegularGraphChart carrier)
      (B : ActualRegularHorizontalGraphChart carrier) (x y : ℝ)
      (hcurvA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = K)
      (hcurvB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = K)
      (overlap : MixedOverlapAt A B x y) :
      CurvedOverlap (.horizontal B y hcurvB) (.vertical A x hcurvA)

theorem curvedSupport_eq_of_overlap
    {P Q : CurvedChart carrier K} (hK : K ≠ 0)
    (h : CurvedOverlap P Q) :
    curvedSupport P = curvedSupport Q := by
  cases h with
  | vertical_vertical A B x hcurvA hcurvB overlap sameSide =>
      exact (ActualRegularGraphChart.unique_supportingCircle_of_overlap
        A B overlap sameSide hK hcurvA hcurvB).1
  | horizontal_horizontal A B y hcurvA hcurvB overlap sameSide =>
      exact (ActualRegularHorizontalGraphChart.unique_supportingCircle_of_overlap
        A B overlap sameSide hK hcurvA hcurvB).1
  | vertical_horizontal A B x y hcurvA hcurvB overlap =>
      exact (overlap.unique_supportingCircle_of_mixedOverlap
        hK hcurvA hcurvB).1
  | horizontal_vertical A B x y hcurvA hcurvB overlap =>
      exact (overlap.unique_supportingCircle_of_mixedOverlap
        hK hcurvA hcurvB).1.symm

/-- The derived literal circle is constant on every mixed-coordinate overlap
component, including every negative-slope (orientation-reversing) edge. -/
theorem curvedSupport_eq_of_mem_component
    {P Q : CurvedChart carrier K} (hK : K ≠ 0)
    (h : Relation.ReflTransGen CurvedOverlap P Q) :
    curvedSupport P = curvedSupport Q := by
  induction h with
  | refl => rfl
  | tail _ hedge ih =>
      exact ih.trans (curvedSupport_eq_of_overlap hK hedge)

/-- A zero-curvature chart node; side labels remain present in its analytic
chart but not in the selected affine support. -/
inductive FlatChart (carrier : Set PlanePoint) where
  | vertical (chart : ActualRegularGraphChart carrier) (parameter : ℝ)
      (curvature : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        chart.patch.orientedGraphCurvature z = 0)
  | horizontal (chart : ActualRegularHorizontalGraphChart carrier)
      (parameter : ℝ)
      (curvature : ∀ z ∈ Ioo chart.patch.a chart.patch.b,
        chart.patch.orientedGraphCurvature z = 0)

def flatSupport : FlatChart carrier → Set PlanePoint
  | .vertical A x _ => A.patch.supportingLineAt x
  | .horizontal B y _ => B.patch.supportingLineAt y

inductive FlatOverlap : FlatChart carrier → FlatChart carrier → Prop
  | vertical_vertical
      (A B : ActualRegularGraphChart carrier) (x : ℝ)
      (hzeroA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = 0)
      (hzeroB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = 0)
      (overlap : ActualRegularGraphChart.OverlapAt A B x) :
      FlatOverlap (.vertical A x hzeroA) (.vertical B x hzeroB)
  | horizontal_horizontal
      (A B : ActualRegularHorizontalGraphChart carrier) (y : ℝ)
      (hzeroA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = 0)
      (hzeroB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = 0)
      (overlap : ActualRegularHorizontalGraphChart.OverlapAt A B y) :
      FlatOverlap (.horizontal A y hzeroA) (.horizontal B y hzeroB)
  | vertical_horizontal
      (A : ActualRegularGraphChart carrier)
      (B : ActualRegularHorizontalGraphChart carrier) (x y : ℝ)
      (hzeroA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = 0)
      (hzeroB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = 0)
      (overlap : MixedOverlapAt A B x y) :
      FlatOverlap (.vertical A x hzeroA) (.horizontal B y hzeroB)
  | horizontal_vertical
      (A : ActualRegularGraphChart carrier)
      (B : ActualRegularHorizontalGraphChart carrier) (x y : ℝ)
      (hzeroA : ∀ z ∈ Ioo A.patch.a A.patch.b,
        A.patch.orientedGraphCurvature z = 0)
      (hzeroB : ∀ z ∈ Ioo B.patch.a B.patch.b,
        B.patch.orientedGraphCurvature z = 0)
      (overlap : MixedOverlapAt A B x y) :
      FlatOverlap (.horizontal B y hzeroB) (.vertical A x hzeroA)

theorem flatSupport_eq_of_overlap
    {P Q : FlatChart carrier} (h : FlatOverlap P Q) :
    flatSupport P = flatSupport Q := by
  cases h with
  | vertical_vertical A B x hzeroA hzeroB overlap =>
      exact (ActualRegularGraphChart.unique_supportingLine_of_overlap
        A B overlap hzeroA hzeroB).1
  | horizontal_horizontal A B y hzeroA hzeroB overlap =>
      exact (ActualRegularHorizontalGraphChart.unique_supportingLine_of_overlap
        A B overlap hzeroA hzeroB).1
  | vertical_horizontal A B x y hzeroA hzeroB overlap =>
      exact (overlap.unique_supportingLine_of_mixedOverlap
        hzeroA hzeroB).1
  | horizontal_vertical A B x y hzeroA hzeroB overlap =>
      exact (overlap.unique_supportingLine_of_mixedOverlap
        hzeroA hzeroB).1.symm

/-- The derived affine line is constant on every zero-curvature mixed overlap
component, independently of occupied-side labels. -/
theorem flatSupport_eq_of_mem_component
    {P Q : FlatChart carrier}
    (h : Relation.ReflTransGen FlatOverlap P Q) :
    flatSupport P = flatSupport Q := by
  induction h with
  | refl => rfl
  | tail _ hedge ih =>
      exact ih.trans (flatSupport_eq_of_overlap hedge)

end MixedChartComponent

/-- Literal supporting circle of an arbitrary regular trace at one anchor. -/
def supportingCircleOfTrace
    (trace velocity : ℝ → PlanePoint) (curvature s : ℝ) : Set PlanePoint :=
  {p | (p.1 -
      (CMVCurvatureIntegration.centerInvariant trace
        (CMVCurvatureIntegration.normalizedTangent velocity) curvature s).1) ^ 2 +
    (p.2 -
      (CMVCurvatureIntegration.centerInvariant trace
        (CMVCurvatureIntegration.normalizedTangent velocity) curvature s).2) ^ 2 =
      (1 / curvature) ^ 2}

/-- Parameter reversal preserves the complete literal supporting circle, not
only its center. -/
theorem supportingCircleOfTrace_eq_of_reversedContact
    {trace₁ trace₂ velocity₁ velocity₂ : ℝ → PlanePoint}
    {curvature s t : ℝ} (hcurvature : curvature ≠ 0)
    (hpoint : trace₁ s = trace₂ t)
    (htangent :
      CMVCurvatureIntegration.normalizedTangent velocity₂ t =
        (-(CMVCurvatureIntegration.normalizedTangent velocity₁ s).1,
          -(CMVCurvatureIntegration.normalizedTangent velocity₁ s).2)) :
    supportingCircleOfTrace trace₁ velocity₁ curvature s =
      supportingCircleOfTrace trace₂ velocity₂ (-curvature) t := by
  have hcenter := supportingCenter_eq_of_reversedContact
    hcurvature hpoint htangent
  ext p
  simp only [supportingCircleOfTrace, Set.mem_ofPred_eq]
  rw [← hcenter]
  simp only [one_div, inv_neg, neg_sq]

/-- Literal tangent line of an arbitrary regular trace at one anchor. -/
def supportingLineOfTrace
    (trace velocity : ℝ → PlanePoint) (s : ℝ) : Set PlanePoint :=
  {p |
    (CMVCurvatureIntegration.normalizedTangent velocity s).1 *
        (p.2 - (trace s).2) -
      (CMVCurvatureIntegration.normalizedTangent velocity s).2 *
        (p.1 - (trace s).1) = 0}

/-- Parameter reversal also preserves flat support; no side or branch label
appears in the theorem. -/
theorem supportingLineOfTrace_eq_of_reversedContact
    {trace₁ trace₂ velocity₁ velocity₂ : ℝ → PlanePoint} {s t : ℝ}
    (hpoint : trace₁ s = trace₂ t)
    (htangent :
      CMVCurvatureIntegration.normalizedTangent velocity₂ t =
        (-(CMVCurvatureIntegration.normalizedTangent velocity₁ s).1,
          -(CMVCurvatureIntegration.normalizedTangent velocity₁ s).2)) :
    supportingLineOfTrace trace₁ velocity₁ s =
      supportingLineOfTrace trace₂ velocity₂ t := by
  ext p
  simp only [supportingLineOfTrace, Set.mem_ofPred_eq]
  rw [← hpoint, htangent]
  constructor <;> intro hp <;> nlinarith

namespace CurvedCarrierExample

/-- The independent open unit disk traverses one support through both
coordinate-tangency types: at `0` it is a `y = f(x)` chart, while at `π/2` it
must be written as `x = g(y)`.  No interface-contact premise is present. -/
theorem coordinateTangencies_share_support_without_interface :
    (velocity 0).2 = 0 ∧
    (velocity (π / 2)).1 = 0 ∧
    ∀ t ∈ Icc (0 : ℝ) (π / 2),
      trace t ∈ frontier carrier ∩
        supportingCircleOfTrace trace velocity 1 0 := by
  refine ⟨by norm_num [velocity], by simp [velocity], ?_⟩
  intro t ht
  refine ⟨trace_mem_frontier t, ?_⟩
  have hregular := regular 0 (π / 2) (by nlinarith [Real.pi_pos])
  have hcircle := hregular.closed_circle_identity
    (s := 0) (t := t) ⟨le_rfl, by nlinarith [Real.pi_pos]⟩ ht
  exact hcircle

end CurvedCarrierExample

namespace MixedChartExamples

open CMVRelaxation.LocalChartPreservation CMVFigureFour

/-- The independent open disk has both coordinate-axis graph germs, no contact
with the empty interface at either switching point, and one literal supporting
circle across the switch. -/
theorem openCircle_crosses_coordinateTangencies_without_contact :
    (∃ side : CMVRelaxation.FiniteJunctionRepair.SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .vertical side
        CurvedCarrierExample.carrier (0, 1)) ∧
    (∃ side : CMVRelaxation.FiniteJunctionRepair.SpliceGraphOccupiedSide,
      HasContinuousGraphGermOnSide .horizontal side
        CurvedCarrierExample.carrier (1, 0)) ∧
    ¬ InterfaceContactAt (∅ : Set PlanePoint)
      CurvedCarrierExample.trace (π / 2) ∧
    ¬ InterfaceContactAt (∅ : Set PlanePoint)
      CurvedCarrierExample.trace π ∧
    supportingCircleOfTrace CurvedCarrierExample.trace
        CurvedCarrierExample.velocity 1 (π / 2) =
      supportingCircleOfTrace CurvedCarrierExample.trace
        CurvedCarrierExample.velocity 1 π := by
  have hlocal (p : PlanePoint) :
      LocallyOneSided CurvedCarrierExample.carrier (0, 0) 1 p := by
    simpa only [CurvedCarrierExample.carrier,
      CMVFigureFour.FiniteCrossingExample.openUnitDisk] using
      CMVFigureFour.FiniteCrossingExample.openUnitDisk_locallyOneSided p
  refine ⟨exists_verticalGraphGerm_at_horizontal_circle_tangency
      (by norm_num) (by norm_num [circleValue]) (by norm_num) (hlocal (0, 1)),
    exists_horizontalGraphGerm_at_vertical_circle_tangency
      (by norm_num) (by norm_num [circleValue]) (by norm_num) (hlocal (1, 0)),
    by simp [InterfaceContactAt], by simp [InterfaceContactAt], ?_⟩
  have hcenter :=
    (CurvedCarrierExample.regular (π / 2) π
      (by nlinarith [Real.pi_pos])).center_invariant
        ⟨le_rfl, by nlinarith [Real.pi_pos]⟩
        ⟨by nlinarith [Real.pi_pos], le_rfl⟩
  unfold supportingCircleOfTrace
  rw [hcenter]

end MixedChartExamples

/-! ## Independent flat mixed-coordinate specimen -/

namespace FlatMixedChartExample

/-- Increasing-`x` parametrization of the oblique line `y = -x`. -/
def verticalTrace (t : ℝ) : PlanePoint := (t, -t)

def verticalVelocity (_t : ℝ) : PlanePoint := (1, -1)

/-- Increasing-`y` parametrization of the same line, hence reversed. -/
def horizontalTrace (t : ℝ) : PlanePoint := (-t, t)

def horizontalVelocity (_t : ℝ) : PlanePoint := (-1, 1)

theorem anchor_eq : verticalTrace 0 = horizontalTrace 0 := by
  norm_num [verticalTrace, horizontalTrace]

theorem normalizedTangent_reversed :
    CMVCurvatureIntegration.normalizedTangent horizontalVelocity 0 =
      (-(CMVCurvatureIntegration.normalizedTangent verticalVelocity 0).1,
        -(CMVCurvatureIntegration.normalizedTangent verticalVelocity 0).2) := by
  unfold CMVCurvatureIntegration.normalizedTangent
  unfold CMVCurvatureIntegration.euclideanSpeed
  norm_num [verticalVelocity, horizontalVelocity]
  constructor <;> ring

/-- The oblique zero-curvature line has one support across a genuine
`y = f(x)` to `x = g(y)` coordinate switch and parameter reversal. -/
theorem support_agreement :
    supportingLineOfTrace verticalTrace verticalVelocity 0 =
      supportingLineOfTrace horizontalTrace horizontalVelocity 0 :=
  supportingLineOfTrace_eq_of_reversedContact anchor_eq
    normalizedTangent_reversed

end FlatMixedChartExample

end CMVSourceBoundaryContinuation
