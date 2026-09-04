/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CandidateExclusion
import MiddleFaceCells
import CompactCells1003To1023
import CMVSourceBridge

/-!
# Unconditional modeled cutoff at 51/50

This module composes the exact middle-face cells on `[51/50, 33/32]`, all 1,024
compact cells on `[33/32, 9/7]`, and the cap-replacement exclusion above
`1.2581840884`.
-/

noncomputable section

namespace CMVModeledCutoff

/-- Every modeled type-(iv) candidate at density at least `51/50` fails
weighted-perimeter minimality. -/
theorem candidate_not_isWeightedPerimeterMinimizer_from_51_50
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  by_cases hface : lam ≤ (33 / 32 : ℝ)
  · exact MiddleFaceCells.candidate_not_isWeightedPerimeterMinimizer_from_51_50
      hlower hface candidate hcandidate
  · by_cases hcompact : lam ≤ (9 / 7 : ℝ)
    · exact
        CompactCells1003To1023.boxes0To1023_candidate_not_isWeightedPerimeterMinimizer
          (not_le.mp hface).le hcompact candidate hcandidate
    · have hsplice : (1.2581840884 : ℝ) < 9 / 7 := by norm_num
      exact cmv_type_four_not_minimizing
        (le_trans hsplice.le (not_le.mp hcompact).le) candidate hcandidate

/-- A modeled type-(iv) weighted-perimeter minimizer can occur only below
`51/50`. -/
theorem type_four_minimizer_implies_lambda_lt_51_50
    {lam : ℝ}
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    lam < (51 / 50 : ℝ) := by
  by_contra hcutoff
  exact candidate_not_isWeightedPerimeterMinimizer_from_51_50
    (le_of_not_gt hcutoff) candidate hcandidate hmin

/-- The only remaining density range for a modeled type-(iv) minimizer is the
open near-one interval. -/
theorem type_four_minimizer_open_range_51_50
    {lam : ℝ}
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    1 < lam ∧ lam < (51 / 50 : ℝ) :=
  ⟨hcandidate.density_jump,
    type_four_minimizer_implies_lambda_lt_51_50 candidate hcandidate hmin⟩

/-- Under explicit source normalization and reduced-boundary compatibility,
every regular source type-(iv) minimizer is excluded at density at least
`51/50`.  The hypotheses isolate the two source-side facts not supplied by the
coordinate model. -/
theorem sourceCarrier_not_isMinimizer_from_51_50
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (source : SourcePerimeterSemantics lam)
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (normalization :
      source.NormalizationWitness sourceCarrier profile)
    (compatibility : source.CompatibleWithModel profile) :
    ¬ source.IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    source.candidate_isWeightedPerimeterMinimizer_of_sourceNormalization
      profile normalization compatibility hmin
  exact candidate_not_isWeightedPerimeterMinimizer_from_51_50
    hlower profile.toCandidate
      profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- A regular source type-(iv) minimizer satisfying the exact normalization and
boundary-semantics contracts can occur only in the open near-one interval. -/
theorem sourceCarrier_minimizer_open_range_51_50
    {lam : ℝ}
    (source : SourcePerimeterSemantics lam)
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (normalization :
      source.NormalizationWitness sourceCarrier profile)
    (compatibility : source.CompatibleWithModel profile)
    (hmin : source.IsMinimizer sourceCarrier) :
    1 < lam ∧ lam < (51 / 50 : ℝ) := by
  refine ⟨profile.density_jump, ?_⟩
  by_contra hcutoff
  exact sourceCarrier_not_isMinimizer_from_51_50
    (le_of_not_gt hcutoff) source sourceCarrier profile
      normalization compatibility hmin

/-- For canonical complete-frontier semantics, no external normalization or
boundary compatibility premise remains: a regular raw source profile can
minimize only below `51/50`. -/
theorem canonicalCarrier_minimizer_open_range_51_50
    {lam : ℝ}
    (profile : CanonicalTypeIVProfile lam)
    (hmin :
      (canonicalFrontierSemantics lam).IsMinimizer profile.carrier) :
    1 < lam ∧ lam < (51 / 50 : ℝ) := by
  have hcandidate :=
    (canonicalFrontierSemantics lam).candidate_isWeightedPerimeterMinimizer
      profile (canonicalFrontierSemantics.compatibleWithModel profile) hmin
  exact ⟨profile.density_jump,
    type_four_minimizer_implies_lambda_lt_51_50
      profile.toCandidate
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate⟩

end CMVModeledCutoff
