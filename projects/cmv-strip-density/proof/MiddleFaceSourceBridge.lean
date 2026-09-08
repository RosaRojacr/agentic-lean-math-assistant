/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSourceBridge
import MiddleFaceCells

/-!
# Source-profile bridge across the complete middle-face inventory

This module composes the raw-coordinate type-(iv) normalization and minimizer
quantifier transfer with both retained prototypes and all 113 middle-face cells
`B0000`--`B0112`, reaching the compact-certificate seam at `33 / 32`.
-/

noncomputable section

namespace MiddleFaceSourceBridge

/-- Under the explicit reduced-boundary compatibility and normalization
contracts, no arbitrary source representative of a regular type-(iv) profile
can minimize across the complete exact middle-face inventory. -/
theorem sourceCarrier_not_isMinimizer
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (hupper : lam ≤ (33 / 32 : ℝ))
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
  exact (MiddleFaceCells.candidate_not_isWeightedPerimeterMinimizer_from_51_50
    hlower hupper profile.toCandidate
    profile.toCandidate_satisfiesCMVTypeIVHypotheses) hcandidate

/-- Horizontal placement is no longer part of the normalization contract:
area and complete-frontier perimeter invariance are proved geometrically.
Only the source reduced-boundary/complete-frontier identification for the
placed representative remains explicit. -/
theorem sourceCarrier_not_isMinimizer_of_horizontalCongruence
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (hupper : lam ≤ (33 / 32 : ℝ))
    (source : SourcePerimeterSemantics lam)
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility : source.CompatibleWithModel profile)
    (sourceCarrier_perimeter_eq_frontier :
      source.perimeter sourceCarrier =
        _root_.WeightedPerimeter lam
          (FrontierMeasure sourceCarrier)) :
    ¬ source.IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    source.candidate_isWeightedPerimeterMinimizer_of_horizontalCongruence
      profile hcongruent compatibility
      sourceCarrier_perimeter_eq_frontier hmin
  exact (MiddleFaceCells.candidate_not_isWeightedPerimeterMinimizer_from_51_50
    hlower hupper profile.toCandidate
    profile.toCandidate_satisfiesCMVTypeIVHypotheses) hcandidate


/-- In the repository's canonical complete-frontier semantics, the normalized
raw `E₄` carrier is unconditionally non-minimizing on the same closed range. -/
theorem canonicalCarrier_not_isMinimizer
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (hupper : lam ≤ (33 / 32 : ℝ))
    (profile : CanonicalTypeIVProfile lam) :
    ¬ (canonicalFrontierSemantics lam).IsMinimizer profile.carrier := by
  intro hmin
  have hcandidate :=
    (canonicalFrontierSemantics lam).candidate_isWeightedPerimeterMinimizer
      profile (canonicalFrontierSemantics.compatibleWithModel profile) hmin
  exact (MiddleFaceCells.candidate_not_isWeightedPerimeterMinimizer_from_51_50
    hlower hupper profile.toCandidate
    profile.toCandidate_satisfiesCMVTypeIVHypotheses) hcandidate

/-- Every horizontal translate of the raw `E₄` carrier is unconditionally
non-minimizing in canonical complete-frontier semantics across the complete
middle-face inventory. -/
theorem horizontallyCongruentCarrier_not_isMinimizer
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (hupper : lam ≤ (33 / 32 : ℝ))
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier) :
    ¬ (canonicalFrontierSemantics lam).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_horizontalCongruence
    hlower hupper (canonicalFrontierSemantics lam)
    sourceCarrier profile hcongruent
    (canonicalFrontierSemantics.compatibleWithModel profile) rfl

end MiddleFaceSourceBridge
