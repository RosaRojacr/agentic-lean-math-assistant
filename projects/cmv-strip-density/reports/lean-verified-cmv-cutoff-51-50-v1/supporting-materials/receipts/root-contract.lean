import CMVPublishedCutoff51_50

example : ∀ {lam : ℝ}, (51 / 50 : ℝ) ≤ lam → ∀ candidate : FourArcCandidate lam, candidate.SatisfiesCMVTypeIVHypotheses → ¬ candidate.IsWeightedPerimeterMinimizer := by
  exact CMVPublishedCutoff51_50.candidate_not_isWeightedPerimeterMinimizer_from_51_50
#print axioms CMVPublishedCutoff51_50.candidate_not_isWeightedPerimeterMinimizer_from_51_50
