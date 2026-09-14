/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CandidateExclusion
import MiddleFaceCells
import CompactCells1003To1023

/-!
# Published modeled cutoff at 51/50

This publication-scoped module exposes only the exact 51/50 theorem and its imported
proof dependencies. Later and stronger project results are deliberately outside this
module's import closure.
-/

noncomputable section

namespace CMVPublishedCutoff51_50

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

end CMVPublishedCutoff51_50
