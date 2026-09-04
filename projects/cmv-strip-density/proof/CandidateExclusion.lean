/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import GeometricBridge

/-!
# Exclusion of CMV type-(iv) candidates

The minimizer comparison is instantiated with the genuine cap-replacement
region.  Its exact area equality and strict perimeter inequality were proved
from the geometric constructors in the imported bridge.
-/

noncomputable section

/-- Every explicitly modeled CMV type-(iv) candidate in the campaign density
range fails weighted-perimeter minimality. -/
theorem cmv_type_four_not_minimizing {lam : ℝ}
    (hlam : (1.2581840884 : ℝ) ≤ lam)
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    False := by
  have hsourceDomain : 1 < lam := hcandidate.density_jump
  have harea : candidate.capReplacementRegion.WeightedArea =
      candidate.WeightedArea :=
    candidate.cap_replacement_preserves_area
  have hminimal : candidate.WeightedPerimeter ≤
      candidate.capReplacementRegion.WeightedPerimeter :=
    hmin candidate.capReplacementRegion harea
  have himproves : candidate.capReplacementRegion.WeightedPerimeter <
      candidate.WeightedPerimeter :=
    candidate.cap_replacement_strictly_improves hlam
  exact (not_lt_of_ge hminimal) himproves

/-- A modeled CMV type-(iv) weighted-perimeter minimizer can occur only below
the certified improved cutoff. -/
theorem type_four_minimizer_implies_lambda_lt {lam : ℝ}
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    lam < (1.2581840884 : ℝ) := by
  by_contra hcutoff
  exact cmv_type_four_not_minimizing (le_of_not_gt hcutoff)
    candidate hcandidate hmin

/-- The parameter of any modeled CMV type-(iv) minimizer lies in the remaining
open interval. -/
theorem type_four_minimizer_open_range {lam : ℝ}
    (candidate : FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    1 < lam ∧ lam < (1.2581840884 : ℝ) :=
  ⟨hcandidate.density_jump,
    type_four_minimizer_implies_lambda_lt candidate hcandidate hmin⟩
