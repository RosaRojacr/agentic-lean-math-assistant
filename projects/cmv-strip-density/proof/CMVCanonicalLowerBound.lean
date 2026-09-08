/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFourArcExhaustion

/-!
# Closed-curvature four-arc lower bound for the CMV relaxation

The candidate-level four-arc patch exhaustion supplies, for each positive
deficit, one finite error coefficient. Characteristic convergence removes that
coefficient at the sequence liminf. Removing the arbitrary deficit gives the
exact extended relaxed lower bound for every `0 < h ≤ 1`; regular canonical
profiles remain thin specializations.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff BigOperators

noncomputable section

namespace CMVRelaxation
namespace CandidateFourArc

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- A fixed positive patch-exhaustion deficit survives the sequence liminf,
while the corresponding finite characteristic-distance error vanishes. -/
theorem frontierCost_le_smoothSequence_cost_add_deficit
    (hlam : 1 < lam) (A : SmoothSequence)
    (hconv : A.ConvergesTo candidate.assembly.carrier)
    {eta : ℝ} (heta : 0 < eta) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier)) ≤
      A.cost lam + ENNReal.ofReal eta := by
  obtain ⟨Nu, Nd, Nr, Nl, Pu, Pd, Pr, Pl, _, _, _, _, _, _, _, _,
      hpair, herror, hpayoff, hcost⟩ :=
    exists_fourArc_patch_family_and_bound candidate hlam heta
  let P : PatchIndex Nu Nd Nr Nl →
      RigidProjectionPatch lam candidate.assembly.carrier :=
    combinedPatch candidate Pu Pd Pr Pl
  let C : ℝ≥0∞ := ∑ i, (P i).errorCoefficient
  have hpoint : ∀ n,
      ENNReal.ofReal
          (_root_.WeightedPerimeter lam
            (FrontierMeasure candidate.assembly.carrier)) ≤
        smoothCost lam (A.carrier n) +
          C * characteristicDistance
            (A.carrier n) candidate.assembly.carrier +
          ENNReal.ofReal eta := by
    intro n
    apply hpayoff.trans
    exact add_le_add (hcost (A.smooth n).isOpen) le_rfl
  exact A.cost_add_ge_of_pointwise_add_distance candidate.assembly.carrier
    (ENNReal.ofReal
      (_root_.WeightedPerimeter lam
        (FrontierMeasure candidate.assembly.carrier)))
    C (ENNReal.ofReal eta) hconv herror hpoint

/-- Every actual smooth sequence converging to a literal four-arc candidate
has cost at least the candidate's complete-frontier weighted perimeter. -/
theorem frontierCost_le_smoothSequence_cost
    (hlam : 1 < lam) (A : SmoothSequence)
    (hconv : A.ConvergesTo candidate.assembly.carrier) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier)) ≤
      A.cost lam := by
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  have heta : 0 < (epsilon : ℝ) := NNReal.coe_pos.2 hepsilon
  simpa only [ENNReal.ofReal_coe_nnreal] using
    frontierCost_le_smoothSequence_cost_add_deficit
      candidate hlam A hconv heta

/-- Every literal four-arc candidate, including `h = 1`, has extended relaxed
perimeter at least its actual complete-frontier weighted perimeter. -/
theorem frontierCost_le_relaxedPerimeter
    (hlam : 1 < lam) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure candidate.assembly.carrier)) ≤
      relaxedPerimeter lam candidate.assembly.carrier := by
  unfold relaxedPerimeter
  apply le_sInf
  intro c hc
  rcases hc with ⟨A, _, hconv, rfl⟩
  exact frontierCost_le_smoothSequence_cost candidate hlam A hconv

/-- Exact complete-frontier accounting at the closed-curvature endpoint: two
weighted exterior arcs and two unweighted semicircular side arcs. -/
theorem endpoint_frontierWeightedPerimeter
    {lam : ℝ} (hlam : 1 < lam) :
    _root_.WeightedPerimeter lam
        (FrontierMeasure (FourArcCandidate.endpoint hlam).assembly.carrier) =
      4 * lam * Real.arccos (1 / lam) + 2 * Real.pi := by
  rw [frontierWeightedPerimeter_eq_four_components]
  have hupper := FourArcCandidate.endpoint_upperCap_weightedArcLength hlam
  have hlower :
      lam * (FourArcCandidate.endpoint hlam).assembly.lowerCap.arcLength =
        2 * lam * Real.arccos (1 / lam) := by
    simpa only [show
      (FourArcCandidate.endpoint hlam).assembly.lowerCap.arcLength =
        (FourArcCandidate.endpoint hlam).assembly.upperCap.arcLength by rfl]
      using hupper
  have hside := FourArcCandidate.endpoint_rightSide_arcLength hlam
  rw [hupper, hlower, hside]
  ring

/-- The literal `h = 1` carrier satisfies the shared extended relaxed lower
bound for every admissible density. -/
theorem endpoint_frontierCost_le_relaxedPerimeter
    {lam : ℝ} (hlam : 1 < lam) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure
            (FourArcCandidate.endpoint hlam).assembly.carrier)) ≤
      relaxedPerimeter lam
        (FourArcCandidate.endpoint hlam).assembly.carrier :=
  frontierCost_le_relaxedPerimeter (FourArcCandidate.endpoint hlam) hlam

end CandidateFourArc

namespace CanonicalFourArc

variable {lam : ℝ} (profile : CanonicalTypeIVProfile lam)

/-- Regular canonical specialization of the shared candidate-level
fixed-deficit lower bound. -/
theorem frontierCost_le_smoothSequence_cost_add_deficit
    (A : SmoothSequence) (hconv : A.ConvergesTo profile.carrier)
    {eta : ℝ} (heta : 0 < eta) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure profile.carrier)) ≤
      A.cost lam + ENNReal.ofReal eta := by
  rw [profile.carrier_eq_candidate_assembly] at hconv ⊢
  exact CandidateFourArc.frontierCost_le_smoothSequence_cost_add_deficit
    profile.toCandidate profile.density_jump A hconv heta

/-- Regular canonical specialization of the shared candidate-level sequence
lower bound. -/
theorem frontierCost_le_smoothSequence_cost
    (A : SmoothSequence) (hconv : A.ConvergesTo profile.carrier) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure profile.carrier)) ≤
      A.cost lam := by
  rw [profile.carrier_eq_candidate_assembly] at hconv ⊢
  exact CandidateFourArc.frontierCost_le_smoothSequence_cost
    profile.toCandidate profile.density_jump A hconv

/-- Regular canonical specialization retained for profile recovery consumers. -/
theorem frontierCost_le_relaxedPerimeter :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure profile.carrier)) ≤
      relaxedPerimeter lam profile.carrier := by
  rw [profile.carrier_eq_candidate_assembly]
  exact CandidateFourArc.frontierCost_le_relaxedPerimeter
    profile.toCandidate profile.density_jump

end CanonicalFourArc
end CMVRelaxation
