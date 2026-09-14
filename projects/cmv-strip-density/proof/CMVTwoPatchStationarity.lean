/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTwoPatchGraphVariation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

import Mathlib.MeasureTheory.Measure.OpenPos
/-!
# Constrained stationarity of two weighted graph patches

This module derives the Euler--Lagrange equation for the literal weighted
Euclidean graph-length functional from local minimality along the exact-area
compensated variations in `CMVTwoPatchGraphVariation`.  It remains conditional
on graph-functional local minimality; no transfer from relaxed source
minimality is asserted here.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Interval symmDiff

noncomputable section
namespace CMVTwoPatchGraphVariation

namespace PrimaryVariation

/-- A primary variation vanishes outside its declared open patch interval. -/
lemma eq_zero_of_not_mem_interval {P : GraphPatch}
    (V : PrimaryVariation P) {x : ℝ} (hx : x ∉ Ioo P.a P.b) : V x = 0 := by
  by_contra hne
  exact hx (V.tsupport_subset (subset_tsupport V hne))

end PrimaryVariation

namespace GraphPatch

/-- Horizontal graph momentum, whose derivative is the signed graph
curvature for upward normal orientation. -/
def graphMomentum (P : GraphPatch) (x : ℝ) : ℝ :=
  deriv P.graph x / Real.sqrt (1 + (deriv P.graph x) ^ 2)

/-- Signed curvature of the graph `(x, graph x)` for increasing `x` and upward
normal orientation. -/
def graphCurvature (P : GraphPatch) (x : ℝ) : ℝ :=
  deriv (deriv P.graph) x /
    Real.sqrt (1 + (deriv P.graph x) ^ 2) ^ 3

/-- Curvature oriented by the occupied side of the actual carrier. -/
def orientedGraphCurvature (P : GraphPatch) (x : ℝ) : ℝ :=
  P.side.areaSign * P.graphCurvature x

lemma graph_deriv_contDiff (P : GraphPatch) :
    ContDiff ℝ 1 (deriv P.graph) :=
  (contDiff_succ_iff_deriv.mp P.graph_contDiff).2.2

lemma graphMomentum_contDiff (P : GraphPatch) :
    ContDiff ℝ 1 P.graphMomentum := by
  unfold graphMomentum
  apply ContDiff.div
  · exact P.graph_deriv_contDiff
  · exact (contDiff_const.add (P.graph_deriv_contDiff.pow 2)).sqrt
      (by intro x; positivity)
  · intro x
    positivity

lemma graphCurvature_continuous (P : GraphPatch) :
    Continuous P.graphCurvature := by
  unfold graphCurvature
  apply Continuous.div
  · exact P.graph_deriv_contDiff.continuous_deriv (by norm_num)
  · exact ((continuous_const.add
      (P.graph_deriv_contDiff.continuous.pow 2)).sqrt.pow 3)
  · intro x
    positivity

lemma orientedGraphCurvature_continuous (P : GraphPatch) :
    Continuous P.orientedGraphCurvature :=
  continuous_const.mul P.graphCurvature_continuous

/-- The displayed graph-curvature formula is obtained by differentiating the
actual graph momentum. -/
theorem graphMomentum_hasDerivAt (P : GraphPatch) (x : ℝ) :
    HasDerivAt P.graphMomentum (P.graphCurvature x) x := by
  have hu : HasDerivAt (deriv P.graph) (deriv (deriv P.graph) x) x :=
    (P.graph_deriv_contDiff.differentiable (by norm_num) x).hasDerivAt
  have hinner : HasDerivAt (fun y : ℝ => 1 + (deriv P.graph y) ^ 2)
      (2 * deriv P.graph x * deriv (deriv P.graph) x) x := by
    simpa only [Pi.add_apply, Pi.pow_apply] using!
      ((hasDerivAt_const x 1).add (hu.pow 2)).congr_deriv (by norm_num)
  have hroot : Real.sqrt (1 + (deriv P.graph x) ^ 2) ≠ 0 := by
    positivity
  have hraw := hu.div (hinner.sqrt (by positivity)) hroot
  apply hraw.congr_deriv
  change
    (deriv (deriv P.graph) x * Real.sqrt (1 + deriv P.graph x ^ 2) -
        deriv P.graph x *
          (2 * deriv P.graph x * deriv (deriv P.graph) x /
            (2 * Real.sqrt (1 + deriv P.graph x ^ 2)))) /
        Real.sqrt (1 + deriv P.graph x ^ 2) ^ 2 =
      deriv (deriv P.graph) x /
        Real.sqrt (1 + deriv P.graph x ^ 2) ^ 3
  have hsq : Real.sqrt (1 + deriv P.graph x ^ 2) ^ 2 =
      1 + deriv P.graph x ^ 2 :=
    Real.sq_sqrt (by positivity)
  field_simp [hroot]
  rw [hsq]
  ring
/-- Integration by parts for a compactly supported vertical graph variation.
The endpoint term vanishes because the test field has closed support strictly
inside the patch interval. -/
theorem integral_graphMomentum_mul_deriv_eq_neg_curvature_mul
    (P : GraphPatch) (V : PrimaryVariation P) :
    (∫ x in P.a..P.b, P.graphMomentum x * deriv V x) =
      -(∫ x in P.a..P.b, P.graphCurvature x * V x) := by
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := P.a) (b := P.b)
    (u := P.graphMomentum) (v := fun x => V x)
    (u' := P.graphCurvature) (v' := deriv V)
    (fun x _ => P.graphMomentum_hasDerivAt x)
    (fun x _ => (V.contDiff.differentiable (by norm_num) x).hasDerivAt)
    (P.graphCurvature_continuous.intervalIntegrable P.a P.b)
    ((V.contDiff.continuous_deriv (by norm_num)).intervalIntegrable P.a P.b)
  have hVa : V P.a = 0 :=
    V.eq_zero_of_not_mem_interval (by simp)
  have hVb : V P.b = 0 :=
    V.eq_zero_of_not_mem_interval (by simp)
  simpa [hVa, hVb] using hparts

/-- The exact first-variation integrand from the graph-length derivative is the
negative curvature pairing after integration by parts. -/
theorem firstVariationIntegral_eq_neg_curvature_mul
    (P : GraphPatch) (V : PrimaryVariation P) :
    (∫ x in P.a..P.b,
      deriv P.graph x * deriv V x /
        Real.sqrt (1 + (deriv P.graph x) ^ 2)) =
      -(∫ x in P.a..P.b, P.graphCurvature x * V x) := by
  rw [← P.integral_graphMomentum_mul_deriv_eq_neg_curvature_mul V]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold graphMomentum
  ring

/-- The normalized bump averages the occupied-side oriented curvature on a
patch. -/
def curvatureAnchor (P : GraphPatch) : ℝ :=
  ∫ x in P.a..P.b,
    P.orientedGraphCurvature x * P.compensationBump x

end GraphPatch

/-- The internally generated compensation field, bundled as an admissible
primary variation on the second patch. -/
def compensatedSecondaryVariation (lam : ℝ) (P₁ P₂ : GraphPatch)
    (V : PrimaryVariation P₁) : PrimaryVariation P₂ where
  toFun := velocityTwo lam P₁ P₂ V
  contDiff := velocityTwo_contDiff lam P₁ P₂ V
  tsupport_subset := tsupport_velocityTwo_subset lam P₁ P₂ V

/-- The literal derivative of the two weighted graph-length integrals. -/
def constrainedFirstVariation (lam : ℝ) (D : TwoPatchData)
    (V : PrimaryVariation D.first) : ℝ :=
  D.first.zone.weight lam *
      (∫ x in D.first.a..D.first.b,
        deriv D.first.graph x * deriv V x /
          Real.sqrt (1 + (deriv D.first.graph x) ^ 2)) +
    D.second.zone.weight lam *
      (∫ x in D.second.a..D.second.b,
        deriv D.second.graph x *
            deriv (velocityTwo lam D.first D.second V) x /
          Real.sqrt (1 + (deriv D.second.graph x) ^ 2))

/-- The existing first-variation theorem, exposed with the named derivative
functional used by the stationarity argument. -/
theorem totalWeightedGraphLength_hasDerivAt_constrainedFirstVariation
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (V : PrimaryVariation A.patches.first) :
    HasDerivAt (totalWeightedGraphLength lam A.patches V)
      (constrainedFirstVariation lam A.patches V) 0 := by
  simpa only [constrainedFirstVariation] using
    (actualTwoPatch_checkpoint_with_firstVariation hlam A V).2


/-- Curvature residual tested by a primary variation.  The reference value is
constructed internally from the normalized compensation bump on patch two. -/
def stationarityResidual (D : TwoPatchData)
    (V : PrimaryVariation D.first) : ℝ :=
  ∫ x in D.first.a..D.first.b,
    V x *
      (D.first.orientedGraphCurvature x -
        D.second.curvatureAnchor)

/-- Exact factorization of the constrained first variation.  Both density
weights and both occupied-side signs enter through the area compensation; the
second density cancels only after using its proved positivity. -/
theorem constrainedFirstVariation_eq_neg_weighted_residual
    {lam : ℝ} (hlam : 1 < lam) (D : TwoPatchData)
    (V : PrimaryVariation D.first) :
    constrainedFirstVariation lam D V =
      -(D.first.zone.weight lam * D.first.side.areaSign) *
        stationarityResidual D V := by
  let V₂ : PrimaryVariation D.second :=
    compensatedSecondaryVariation lam D.first D.second V
  have hfirst :=
    D.first.firstVariationIntegral_eq_neg_curvature_mul V
  have hsecond :
      (∫ x in D.second.a..D.second.b,
        deriv D.second.graph x *
            deriv (velocityTwo lam D.first D.second V) x /
          Real.sqrt (1 + (deriv D.second.graph x) ^ 2)) =
        -(∫ x in D.second.a..D.second.b,
          D.second.graphCurvature x *
            velocityTwo lam D.first D.second V x) := by
    simpa only [V₂, compensatedSecondaryVariation] using
      D.second.firstVariationIntegral_eq_neg_curvature_mul V₂
  have hsecondary :
      (∫ x in D.second.a..D.second.b,
        D.second.graphCurvature x *
          velocityTwo lam D.first D.second V x) =
        compensationCoefficient lam D.first D.second V *
          (∫ x in D.second.a..D.second.b,
            D.second.graphCurvature x *
              D.second.compensationBump x) := by
    calc
      (∫ x in D.second.a..D.second.b,
          D.second.graphCurvature x *
            velocityTwo lam D.first D.second V x) =
          ∫ x in D.second.a..D.second.b,
            compensationCoefficient lam D.first D.second V *
              (D.second.graphCurvature x *
                D.second.compensationBump x) := by
            apply intervalIntegral.integral_congr
            intro x _hx
            simp only [velocityTwo]
            ring
      _ = compensationCoefficient lam D.first D.second V *
            (∫ x in D.second.a..D.second.b,
              D.second.graphCurvature x *
                D.second.compensationBump x) := by
          rw [intervalIntegral.integral_const_mul]
  have hanchor :
      D.second.curvatureAnchor =
        D.second.side.areaSign *
          (∫ x in D.second.a..D.second.b,
            D.second.graphCurvature x *
              D.second.compensationBump x) := by
    unfold GraphPatch.curvatureAnchor GraphPatch.orientedGraphCurvature
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hresidual :
      stationarityResidual D V =
        D.first.side.areaSign *
            (∫ x in D.first.a..D.first.b,
              D.first.graphCurvature x * V x) -
          D.second.curvatureAnchor *
            (∫ x in D.first.a..D.first.b, V x) := by
    unfold stationarityResidual GraphPatch.orientedGraphCurvature
    have hleft : IntervalIntegrable
        (fun x => V x *
          (D.first.side.areaSign * D.first.graphCurvature x))
        volume D.first.a D.first.b :=
      (V.continuous.mul
        (continuous_const.mul D.first.graphCurvature_continuous)
      ).intervalIntegrable _ _
    have hright : IntervalIntegrable
        (fun x => V x * D.second.curvatureAnchor)
        volume D.first.a D.first.b :=
      (V.continuous.mul continuous_const).intervalIntegrable _ _
    rw [show (fun x => V x *
        (D.first.side.areaSign * D.first.graphCurvature x -
          D.second.curvatureAnchor)) =
      fun x => V x *
          (D.first.side.areaSign * D.first.graphCurvature x) -
        V x * D.second.curvatureAnchor by
      funext x
      ring]
    rw [intervalIntegral.integral_sub hleft hright]
    congr 1
    · rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    · rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
  rw [constrainedFirstVariation, hfirst, hsecond, hsecondary,
    hresidual, hanchor]
  unfold compensationCoefficient
  field_simp [DensityZone.weight_ne_zero hlam,
    OccupiedSide.areaSign_ne_zero]
  have hs₁ := D.first.side.areaSign_mul_self
  have hs₂ := D.second.side.areaSign_mul_self
  ring_nf at hs₁ hs₂ ⊢
  rw [hs₁, hs₂]
  ring

/-- Conditional graph-functional local minimality along every internally
compensated exact-area variation based on the first patch. -/
def ActualTwoPatchData.IsForwardGraphMinimizing
    (A : ActualTwoPatchData) (lam : ℝ) : Prop :=
  ∀ V : PrimaryVariation A.patches.first,
    IsLocalMin (totalWeightedGraphLength lam A.patches V) 0

/-- Fermat's theorem turns local graph-functional minimality into constrained
stationarity of the actual weighted graph-length derivative.  Exact ambient
area preservation and locality are supplied for the same family by
`actualTwoPatch_checkpoint_with_firstVariation`. -/
theorem ActualTwoPatchData.constrainedFirstVariation_eq_zero
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hmin : A.IsForwardGraphMinimizing lam)
    (V : PrimaryVariation A.patches.first) :
    constrainedFirstVariation lam A.patches V = 0 :=
  (hmin V).hasDerivAt_eq_zero
    (totalWeightedGraphLength_hasDerivAt_constrainedFirstVariation
      hlam A V)

/-- Every smooth compactly supported test field on the first patch annihilates
the internally normalized oriented-curvature residual. -/
theorem ActualTwoPatchData.stationarityResidual_eq_zero
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hmin : A.IsForwardGraphMinimizing lam)
    (V : PrimaryVariation A.patches.first) :
    stationarityResidual A.patches V = 0 := by
  have hzero := A.constrainedFirstVariation_eq_zero hlam hmin V
  rw [constrainedFirstVariation_eq_neg_weighted_residual
    hlam A.patches V] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (neg_ne_zero.mpr <|
    mul_ne_zero
      (DensityZone.weight_ne_zero hlam)
      A.patches.first.side.areaSign_ne_zero)

/-- Bundle an arbitrary smooth compactly supported scalar test field whose
closed support lies in a graph patch. -/
def PrimaryVariation.ofSmoothCompact {P : GraphPatch}
    (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g)
    (hsupport : tsupport g ⊆ Ioo P.a P.b) :
    PrimaryVariation P where
  toFun := g
  contDiff := hg.of_le (by
    apply WithTop.coe_le_coe.mpr
    exact le_top)
  tsupport_subset := hsupport

/-- Smooth-test separation and continuity turn constrained stationarity into
the pointwise occupied-side curvature equation on the whole open graph patch. -/
theorem ActualTwoPatchData.orientedGraphCurvature_eq_anchor
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hmin : A.IsForwardGraphMinimizing lam) :
    ∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
      A.patches.first.orientedGraphCurvature x =
        A.patches.second.curvatureAnchor := by
  let q : ℝ → ℝ := fun x =>
    A.patches.first.orientedGraphCurvature x -
      A.patches.second.curvatureAnchor
  have hqcont : Continuous q :=
    A.patches.first.orientedGraphCurvature_continuous.sub continuous_const
  have hqloc : LocallyIntegrableOn q
      (Ioo A.patches.first.a A.patches.first.b) volume :=
    hqcont.continuousOn.locallyIntegrableOn measurableSet_Ioo
  have hae :
      ∀ᵐ x ∂volume,
        x ∈ Ioo A.patches.first.a A.patches.first.b → q x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hqloc
    intro g hg hcompact hsupport
    let V : PrimaryVariation A.patches.first :=
      PrimaryVariation.ofSmoothCompact g hg hsupport
    have htest := A.stationarityResidual_eq_zero hlam hmin V
    have hsupp :
        support (fun x => g x * q x) ⊆
          Ioc A.patches.first.a A.patches.first.b := by
      intro x hx
      have hgx : g x ≠ 0 := by
        intro hzero
        exact hx (by simp [hzero])
      exact Ioo_subset_Ioc_self
        (hsupport (subset_tsupport g hgx))
    change (∫ x in A.patches.first.a..A.patches.first.b,
      g x * q x) = 0 at htest
    rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp] at htest
    simpa only [smul_eq_mul] using htest
  have haeRestrict :
      q =ᵐ[volume.restrict
        (Ioo A.patches.first.a A.patches.first.b)] 0 := by
    change ∀ᵐ x ∂volume.restrict
      (Ioo A.patches.first.a A.patches.first.b), q x = 0
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hae
  have hpoint := MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume haeRestrict
    hqcont.continuousOn continuous_const.continuousOn
  intro x hx
  simpa only [q, Pi.zero_apply, sub_eq_zero] using hpoint hx

namespace TwoPatchData

/-- Reverse the roles of the two disjoint graph patches. -/
def swap (D : TwoPatchData) : TwoPatchData where
  first := D.second
  second := D.first
  horizontal_disjoint := D.horizontal_disjoint.symm

@[simp] theorem swap_first (D : TwoPatchData) : D.swap.first = D.second := rfl

@[simp] theorem swap_second (D : TwoPatchData) : D.swap.second = D.first := rfl

end TwoPatchData

namespace ActualTwoPatchData

/-- Reverse the primary and compensation patches while retaining the same
literal carrier and fixed remainder. -/
def swap (A : ActualTwoPatchData) : ActualTwoPatchData where
  patches := A.patches.swap
  firstTube := A.secondTube
  secondTube := A.firstTube
  actualCarrier := A.actualCarrier
  fixedCarrier := A.fixedCarrier
  actualCarrier_eq_fixed_union := by
    rw [A.actualCarrier_eq_fixed_union]
    simp only [TwoPatchData.swap_first, TwoPatchData.swap_second]
    rw [union_comm A.patches.first.carrier A.patches.second.carrier]
  measurableSet_actualCarrier := A.measurableSet_actualCarrier
  measurableSet_fixedCarrier := A.measurableSet_fixedCarrier
  actualCarrier_bounded := A.actualCarrier_bounded
  fixed_disjoint_patchCarriers := by
    simpa only [TwoPatchData.swap_first, TwoPatchData.swap_second,
      union_comm] using A.fixed_disjoint_patchCarriers
  fixed_disjoint_closedGraphTubes := by
    simpa only [TwoPatchData.swap_first, TwoPatchData.swap_second,
      union_comm] using A.fixed_disjoint_closedGraphTubes
  first_graph_frontier := A.second_graph_frontier
  second_graph_frontier := A.first_graph_frontier

@[simp] theorem swap_patches (A : ActualTwoPatchData) :
    A.swap.patches = A.patches.swap := rfl

@[simp] theorem swap_actualCarrier (A : ActualTwoPatchData) :
    A.swap.actualCarrier = A.actualCarrier := rfl

end ActualTwoPatchData

namespace GraphPatch

/-- A pointwise constant oriented curvature has the same internally normalized
bump average. -/
theorem curvatureAnchor_eq_of_eqOn (P : GraphPatch) {K : ℝ}
    (hK : ∀ x ∈ Ioo P.a P.b, P.orientedGraphCurvature x = K) :
    P.curvatureAnchor = K := by
  unfold curvatureAnchor
  calc
    (∫ x in P.a..P.b,
        P.orientedGraphCurvature x * P.compensationBump x) =
        ∫ x in P.a..P.b, K * P.compensationBump x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      by_cases hb : P.compensationBump x = 0
      · simp [hb]
      · change P.orientedGraphCurvature x * P.compensationBump x =
          K * P.compensationBump x
        rw [hK x (P.tsupport_compensationBump_subset
          (subset_tsupport P.compensationBump hb))]
    _ = K * ∫ x in P.a..P.b, P.compensationBump x := by
      rw [intervalIntegral.integral_const_mul]
    _ = K := by
      rw [P.intervalIntegral_compensationBump, mul_one]

end GraphPatch

/-- Local graph-functional minimality in both exact-area compensation
directions.  This is still a graph-level hypothesis, not a consequence of
relaxed source minimality. -/
def ActualTwoPatchData.IsBidirectionallyGraphMinimizing
    (A : ActualTwoPatchData) (lam : ℝ) : Prop :=
  A.IsForwardGraphMinimizing lam ∧
    A.swap.IsForwardGraphMinimizing lam

/-- Two-direction constrained stationarity forces one common oriented
curvature constant on both actual graph patches.  The constant is constructed
from the second patch's normalized bump, not supplied by the caller. -/
theorem ActualTwoPatchData.exists_common_orientedGraphCurvature
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hmin : A.IsBidirectionallyGraphMinimizing lam) :
    ∃ K : ℝ,
      (∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
        A.patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
        A.patches.second.orientedGraphCurvature x = K) := by
  have hfirst :=
    A.orientedGraphCurvature_eq_anchor hlam hmin.1
  have hsecond :
      ∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
        A.patches.second.orientedGraphCurvature x =
          A.patches.first.curvatureAnchor := by
    simpa only [ActualTwoPatchData.swap, TwoPatchData.swap] using
      A.swap.orientedGraphCurvature_eq_anchor hlam hmin.2
  have hfirstAnchor :
      A.patches.first.curvatureAnchor =
        A.patches.second.curvatureAnchor :=
    A.patches.first.curvatureAnchor_eq_of_eqOn hfirst
  refine ⟨A.patches.second.curvatureAnchor, hfirst, ?_⟩
  intro x hx
  exact (hsecond x hx).trans hfirstAnchor

/-- For constant oriented curvatures, the canonical normalized test direction
measures exactly their difference. -/
theorem stationarityResidual_normalizedPrimary_eq_sub
    (D : TwoPatchData) {K₁ K₂ : ℝ}
    (hK₁ : ∀ x ∈ Ioo D.first.a D.first.b,
      D.first.orientedGraphCurvature x = K₁)
    (hK₂ : ∀ x ∈ Ioo D.second.a D.second.b,
      D.second.orientedGraphCurvature x = K₂) :
    stationarityResidual D (Examples.normalizedPrimary D.first) =
      K₁ - K₂ := by
  have hanchor : D.second.curvatureAnchor = K₂ :=
    D.second.curvatureAnchor_eq_of_eqOn hK₂
  unfold stationarityResidual
  rw [hanchor]
  calc
    (∫ x in D.first.a..D.first.b,
        (Examples.normalizedPrimary D.first) x *
          (D.first.orientedGraphCurvature x - K₂)) =
        ∫ x in D.first.a..D.first.b,
          D.first.compensationBump x * (K₁ - K₂) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change D.first.compensationBump x *
          (D.first.orientedGraphCurvature x - K₂) =
        D.first.compensationBump x * (K₁ - K₂)
      by_cases hb : D.first.compensationBump x = 0
      · simp [hb]
      · rw [hK₁ x (D.first.tsupport_compensationBump_subset
          (subset_tsupport D.first.compensationBump hb))]
    _ = (K₁ - K₂) *
          ∫ x in D.first.a..D.first.b,
            D.first.compensationBump x := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    _ = K₁ - K₂ := by
      rw [D.first.intervalIntegral_compensationBump, mul_one]

/-- Unequal constant oriented curvatures give a nonzero derivative of the
literal weighted graph-length functional along the internally normalized,
exact-area compensated direction. -/
theorem constrainedFirstVariation_normalizedPrimary_ne_zero_of_ne
    {lam : ℝ} (hlam : 1 < lam) (D : TwoPatchData) {K₁ K₂ : ℝ}
    (hK₁ : ∀ x ∈ Ioo D.first.a D.first.b,
      D.first.orientedGraphCurvature x = K₁)
    (hK₂ : ∀ x ∈ Ioo D.second.a D.second.b,
      D.second.orientedGraphCurvature x = K₂)
    (hne : K₁ ≠ K₂) :
    constrainedFirstVariation lam D
      (Examples.normalizedPrimary D.first) ≠ 0 := by
  rw [constrainedFirstVariation_eq_neg_weighted_residual
      hlam D (Examples.normalizedPrimary D.first),
    stationarityResidual_normalizedPrimary_eq_sub D hK₁ hK₂]
  exact mul_ne_zero
    (neg_ne_zero.mpr <| mul_ne_zero
      (DensityZone.weight_ne_zero hlam)
      D.first.side.areaSign_ne_zero)
    (sub_ne_zero.mpr hne)

/-- Certified strict descent for unequal constant oriented curvatures.  The
witness changes the literal ambient carrier only in the two certified tubes,
preserves its actual weighted area exactly, and strictly lowers the explicit
sum of weighted Euclidean graph-length integrals. -/
theorem ActualTwoPatchData.exists_exactArea_graphLength_descent_of_ne
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    {K₁ K₂ : ℝ}
    (hK₁ : ∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
      A.patches.first.orientedGraphCurvature x = K₁)
    (hK₂ : ∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
      A.patches.second.orientedGraphCurvature x = K₂)
    (hne : K₁ ≠ K₂) :
    ∃ ε > 0, ∃ t : ℝ, |t| < ε ∧ t ≠ 0 ∧
      WeightedArea lam
          (A.variedCarrier lam (Examples.normalizedPrimary A.patches.first) t) =
        WeightedArea lam A.actualCarrier ∧
      (A.variedCarrier lam (Examples.normalizedPrimary A.patches.first) t ∆
          A.actualCarrier) ⊆
        (A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube) ∧
      totalWeightedGraphLength lam A.patches
          (Examples.normalizedPrimary A.patches.first) t <
        totalWeightedGraphLength lam A.patches
          (Examples.normalizedPrimary A.patches.first) 0 := by
  let V : PrimaryVariation A.patches.first :=
    Examples.normalizedPrimary A.patches.first
  have hderiv :
      HasDerivAt (totalWeightedGraphLength lam A.patches V)
        (constrainedFirstVariation lam A.patches V) 0 :=
    totalWeightedGraphLength_hasDerivAt_constrainedFirstVariation
      hlam A V
  have hderivNe : constrainedFirstVariation lam A.patches V ≠ 0 := by
    simpa only [V] using
      constrainedFirstVariation_normalizedPrimary_ne_zero_of_ne
        hlam A.patches hK₁ hK₂ hne
  have hnotmin :
      ¬ IsLocalMin (totalWeightedGraphLength lam A.patches V) 0 := by
    intro hmin
    exact hderivNe (hmin.hasDerivAt_eq_zero hderiv)
  rcases (actualTwoPatch_checkpoint_with_firstVariation hlam A V).1 with
    ⟨ε, hε, hlocal⟩
  have hexists :
      ∃ t : ℝ, |t| < ε ∧
        totalWeightedGraphLength lam A.patches V t <
          totalWeightedGraphLength lam A.patches V 0 := by
    by_contra hnone
    apply hnotmin
    change ∀ᶠ t in 𝓝 (0 : ℝ),
      totalWeightedGraphLength lam A.patches V 0 ≤
        totalWeightedGraphLength lam A.patches V t
    filter_upwards [ball_mem_nhds (0 : ℝ) hε] with t ht
    apply le_of_not_gt
    intro hdescend
    apply hnone
    exact ⟨t, by simpa [Real.dist_eq] using ht, hdescend⟩
  rcases hexists with ⟨t, ht, hdescend⟩
  rcases hlocal t ht with
    ⟨_hvalid₁, _hvalid₂, _htubes, _hzone₁, _hzone₂,
      _hfrontier₁, _hfrontier₂, _hmeasurable, _hintegrable,
      harea, hdiff, _houtside, _hgraph₁, _hgraph₂⟩
  refine ⟨ε, hε, t, ht, ?_, ?_, ?_, ?_⟩
  · intro htzero
    subst t
    exact (lt_irrefl _ hdescend)
  · simpa only [V] using harea
  · simpa only [V] using hdiff
  · simpa only [V] using hdescend

/-- A nonempty finite collection of actual graph pieces, each paired with one
common reference patch inside the same literal ambient carrier.  Every pair
retains its own disjoint certified tubes. -/
structure FiniteActualGraphCollection
    (ι : Type*) [Fintype ι] [Nonempty ι] where
  actualCarrier : Set PlanePoint
  anchor : GraphPatch
  pair : ι → ActualTwoPatchData
  pair_actualCarrier : ∀ i, (pair i).actualCarrier = actualCarrier
  pair_second : ∀ i, (pair i).patches.second = anchor

/-- Pairwise exact-area stationarity against one actual reference patch gives
one common oriented curvature constant on every member of a nonempty finite
collection and on the reference patch itself. -/
theorem FiniteActualGraphCollection.exists_common_orientedGraphCurvature
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {lam : ℝ} (hlam : 1 < lam)
    (C : FiniteActualGraphCollection ι)
    (hmin : ∀ i, (C.pair i).IsBidirectionallyGraphMinimizing lam) :
    ∃ K : ℝ,
      (∀ i, ∀ x ∈ Ioo (C.pair i).patches.first.a
          (C.pair i).patches.first.b,
        (C.pair i).patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo C.anchor.a C.anchor.b,
        C.anchor.orientedGraphCurvature x = K) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  rcases (C.pair i₀).exists_common_orientedGraphCurvature
      hlam (hmin i₀) with ⟨K, _hfirst₀, hanchor₀⟩
  have hanchor :
      ∀ x ∈ Ioo C.anchor.a C.anchor.b,
        C.anchor.orientedGraphCurvature x = K := by
    simpa only [C.pair_second i₀] using hanchor₀
  have hanchorAverage : C.anchor.curvatureAnchor = K :=
    C.anchor.curvatureAnchor_eq_of_eqOn hanchor
  refine ⟨K, ?_, hanchor⟩
  intro i x hx
  have hi := (C.pair i).orientedGraphCurvature_eq_anchor
    hlam (hmin i).1 x hx
  rw [C.pair_second i, hanchorAverage] at hi
  exact hi
end CMVTwoPatchGraphVariation
