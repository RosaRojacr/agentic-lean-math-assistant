/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFourArcExhaustion

/-!
# Finite-patch stability for the CMV relaxation

A finite projection-patch payoff anchored at one reference carrier remains a
lower bound at every arbitrary target, up to its fixed characteristic-distance
penalty. The target needs no geometric or recovery hypotheses.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff BigOperators

noncomputable section

namespace CMVRelaxation

/-- The global characteristic-function distance satisfies the extended triangle
inequality without measurability or finiteness assumptions. -/
theorem characteristicDistance_triangle (E F G : Set PlanePoint) :
    characteristicDistance E G ≤
      characteristicDistance E F + characteristicDistance F G := by
  exact measure_symmDiff_le E F G

/-- A fixed finite patch certificate anchored at `reference` transfers through
the literal relaxation to every target `E`. The same mismatch allowance is
retained through both the sequence liminf and the infimum over sequences. -/
theorem lowerBound_le_relaxedPerimeter_add_mismatch
    {lam : ℝ} {reference : Set PlanePoint}
    (target errorCoefficient : ℝ≥0∞)
    (herrorCoefficient : errorCoefficient ≠ ⊤)
    (hopen : ∀ {U : Set PlanePoint}, IsOpen U →
      target ≤ smoothCost lam U +
        errorCoefficient * characteristicDistance U reference)
    (E : Set PlanePoint) :
    target ≤ relaxedPerimeter lam E +
      errorCoefficient * characteristicDistance E reference := by
  unfold relaxedPerimeter
  rw [ENNReal.sInf_add]
  refine le_iInf fun c => le_iInf fun hc => ?_
  rcases hc with ⟨A, _, hconv, rfl⟩
  apply A.cost_add_ge_of_pointwise_add_distance E target errorCoefficient
    (errorCoefficient * characteristicDistance E reference) hconv
    herrorCoefficient
  intro n
  calc
    target ≤ smoothCost lam (A.carrier n) +
        errorCoefficient *
          characteristicDistance (A.carrier n) reference :=
      hopen (A.smooth n).isOpen
    _ ≤ smoothCost lam (A.carrier n) +
        errorCoefficient *
          (characteristicDistance (A.carrier n) E +
            characteristicDistance E reference) := by
      gcongr
      exact characteristicDistance_triangle (A.carrier n) E reference
    _ = smoothCost lam (A.carrier n) +
          errorCoefficient * characteristicDistance (A.carrier n) E +
        errorCoefficient * characteristicDistance E reference := by
      rw [mul_add]
      ac_rfl

namespace CandidateFourArc

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- Every literal four-arc candidate, including the closed endpoint `h = 1`,
has one finite patch coefficient at each positive deficit which controls the
relaxed perimeter of every arbitrary target. The coefficient is selected before
the target and before any approximating sequence. -/
theorem exists_frontierCost_le_relaxedPerimeter_add_mismatch_add_deficit
    (hlam : 1 < lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ errorCoefficient : ℝ≥0∞, errorCoefficient ≠ ⊤ ∧
      ∀ E : Set PlanePoint,
        ENNReal.ofReal
            (_root_.WeightedPerimeter lam
              (FrontierMeasure candidate.assembly.carrier)) ≤
          relaxedPerimeter lam E +
              errorCoefficient *
                characteristicDistance E candidate.assembly.carrier +
            ENNReal.ofReal eta := by
  obtain ⟨Nu, Nd, Nr, Nl, Pu, Pd, Pr, Pl, _, _, _, _, _, _, _, _, _,
      herror, hpayoff, hcost⟩ :=
    exists_fourArc_patch_family_and_bound candidate hlam heta
  let P : PatchIndex Nu Nd Nr Nl →
      RigidProjectionPatch lam candidate.assembly.carrier :=
    combinedPatch candidate Pu Pd Pr Pl
  let C : ℝ≥0∞ := ∑ i, (P i).errorCoefficient
  refine ⟨C, herror, ?_⟩
  intro E
  have htransfer :
      (∑ i : PatchIndex Nu Nd Nr Nl, (P i).payoff) ≤
        relaxedPerimeter lam E +
          C * characteristicDistance E candidate.assembly.carrier :=
    lowerBound_le_relaxedPerimeter_add_mismatch
      (∑ i : PatchIndex Nu Nd Nr Nl, (P i).payoff) C herror hcost E
  exact hpayoff.trans (add_le_add htransfer le_rfl)

/-- Concrete endpoint specialization of the arbitrary-target patch bound. -/
theorem endpoint_exists_frontierCost_le_relaxedPerimeter_add_mismatch_add_deficit
    {lam : ℝ} (hlam : 1 < lam) {eta : ℝ} (heta : 0 < eta) :
    ∃ errorCoefficient : ℝ≥0∞, errorCoefficient ≠ ⊤ ∧
      ∀ E : Set PlanePoint,
        ENNReal.ofReal
            (_root_.WeightedPerimeter lam
              (FrontierMeasure
                (FourArcCandidate.endpoint hlam).assembly.carrier)) ≤
          relaxedPerimeter lam E +
              errorCoefficient *
                characteristicDistance E
                  (FourArcCandidate.endpoint hlam).assembly.carrier +
            ENNReal.ofReal eta :=
  exists_frontierCost_le_relaxedPerimeter_add_mismatch_add_deficit
    (FourArcCandidate.endpoint hlam) hlam heta

end CandidateFourArc

namespace CanonicalFourArc

variable {lam : ℝ} (profile : CanonicalTypeIVProfile lam)

/-- Regular canonical specialization of the arbitrary-target patch bound. -/
theorem exists_frontierCost_le_relaxedPerimeter_add_mismatch_add_deficit
    {eta : ℝ} (heta : 0 < eta) :
    ∃ errorCoefficient : ℝ≥0∞, errorCoefficient ≠ ⊤ ∧
      ∀ E : Set PlanePoint,
        ENNReal.ofReal
            (_root_.WeightedPerimeter lam
              (FrontierMeasure profile.carrier)) ≤
          relaxedPerimeter lam E +
              errorCoefficient *
                characteristicDistance E profile.carrier +
            ENNReal.ofReal eta := by
  rw [profile.carrier_eq_candidate_assembly]
  exact
    CandidateFourArc.exists_frontierCost_le_relaxedPerimeter_add_mismatch_add_deficit
      profile.toCandidate profile.density_jump heta

end CanonicalFourArc
end CMVRelaxation
