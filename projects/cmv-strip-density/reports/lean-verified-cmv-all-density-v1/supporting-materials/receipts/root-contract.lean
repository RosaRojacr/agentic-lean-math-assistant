import UniversalStationaryPair

example : ∀ {lam : ℝ} (candidate : FourArcCandidate lam), 1 < lam → candidate.SatisfiesCMVTypeIVHypotheses → ¬ candidate.IsWeightedPerimeterMinimizer := by
  exact CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
#print axioms CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
