/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTwoPatchCurvatureGeometryExamples
import CMVRelaxation

/-!
# Hypothesis contract for the stationarity-to-geometry pipeline

The proved pipeline starts from exact actual-carrier area compensation and the
literal weighted Euclidean graph-length derivative.  Its geometry consumer
retains bidirectional graph-functional local minimality as an explicit input.
The separate proposition below names, but does not prove, the missing transfer
from relaxed source minimality.
-/

open Set Function
open scoped Topology ContDiff symmDiff

noncomputable section
namespace CMVTwoPatchGraphVariation.HypothesisContract

/-- Exact actual-area preservation and the literal weighted graph-length first
variation are available for the same compensated local deformation. -/
theorem actualArea_and_weightedLengthFirstVariation
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (V : PrimaryVariation A.patches.first) {t : ℝ}
    (hvalid₁ : A.patches.first.ValidAt V t)
    (hvalid₂ : A.patches.second.ValidAt
      (velocityTwo lam A.patches.first A.patches.second V) t)
    (hdiff :
      A.patches.compensatedCarrier lam V t ∆
          A.patches.compensatedCarrier lam V 0 ⊆
        A.patches.first.closedGraphTube A.firstTube ∪
          A.patches.second.closedGraphTube A.secondTube) :
    WeightedArea lam (A.variedCarrier lam V t) =
        WeightedArea lam A.actualCarrier ∧
      HasDerivAt (totalWeightedGraphLength lam A.patches V)
        (constrainedFirstVariation lam A.patches V) 0 :=
  ⟨A.weightedArea_variedCarrier hlam V hvalid₁ hvalid₂ hdiff,
    totalWeightedGraphLength_hasDerivAt_constrainedFirstVariation hlam A V⟩

/-- Compiled public contract: graph-functional local minimality derives the
common curvature and then either two closed supporting lines or two
arbitrary-speed constant-curvature traces.  The caller supplies neither a
curvature equation nor circle membership. -/
theorem graphMinimality_to_reparameterizedGeometry
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
            R₂.start R₂.finish)) :=
  A.exists_common_reparameterizedSupportingGeometry hlam hmin R₁ R₂

/-- The precise missing bridge from relaxed source minimality of the literal
actual carrier to bidirectional graph-functional local minimality.  This file
does not provide a term of this proposition. -/
def MissingRelaxedMinimizerToGraphStationarity : Prop :=
  ∀ {lam : ℝ}, 1 < lam → ∀ A : ActualTwoPatchData,
    (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer A.actualCarrier →
      A.IsBidirectionallyGraphMinimizing lam

/-- A relaxed source minimizer reaches common graph curvature only when the
missing transfer is supplied explicitly. -/
theorem relaxedMinimizer_to_commonCurvature_of_transfer
    (htransfer : MissingRelaxedMinimizerToGraphStationarity)
    {lam : ℝ} (hlam : 1 < lam) (A : ActualTwoPatchData)
    (hsource : (CMVRelaxation.relaxedSourceSemantics lam).IsMinimizer
      A.actualCarrier) :
    ∃ K : ℝ,
      (∀ x ∈ Ioo A.patches.first.a A.patches.first.b,
        A.patches.first.orientedGraphCurvature x = K) ∧
      (∀ x ∈ Ioo A.patches.second.a A.patches.second.b,
        A.patches.second.orientedGraphCurvature x = K) :=
  A.exists_common_orientedGraphCurvature hlam
    (htransfer hlam A hsource)

end CMVTwoPatchGraphVariation.HypothesisContract
