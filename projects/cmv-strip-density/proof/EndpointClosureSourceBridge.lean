/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSourceBridge
import EndpointClosureCell

/-!
# Source-profile bridge for the endpoint-area fiber

This module composes the raw-coordinate type-(iv) normalization and minimizer
quantifier transfer with the branch-complete endpoint-area exclusion at
`lambda = 5 / 4`. The endpoint theorem exhausts both regular equal-area roots
and separately rules out the `h₄ = 1` branch.
-/

noncomputable section

namespace EndpointClosureSourceBridge

/-- Under the explicit reduced-boundary compatibility and normalization
contracts, no arbitrary source representative of a regular type-(iv) profile
with the type-(iii) endpoint area can minimize. -/
theorem sourceCarrier_not_isMinimizer
    (source : SourcePerimeterSemantics (5 / 4 : ℝ))
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile (5 / 4 : ℝ))
    (normalization :
      source.NormalizationWitness sourceCarrier profile)
    (compatibility : source.CompatibleWithModel profile)
    (harea :
      _root_.WeightedArea (5 / 4 : ℝ) sourceCarrier =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ source.IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    source.candidate_isWeightedPerimeterMinimizer_of_sourceNormalization
      profile normalization compatibility hmin
  have hcandidateArea :
      profile.toCandidate.WeightedArea =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := by
    calc
      profile.toCandidate.WeightedArea =
          _root_.WeightedArea (5 / 4 : ℝ) profile.carrier :=
        profile.weightedArea_eq_candidate.symm
      _ = _root_.WeightedArea (5 / 4 : ℝ) sourceCarrier :=
        normalization.weightedArea_eq.symm
      _ = LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := harea
  exact (EndpointClosureCell.endpoint_area_candidate_not_isWeightedPerimeterMinimizer
    profile.toCandidate
    profile.toCandidate_satisfiesCMVTypeIVHypotheses
    hcandidateArea) hcandidate

/-- Horizontal placement is no longer part of the normalization contract:
area and complete-frontier perimeter invariance are proved geometrically.
Only the source reduced-boundary/complete-frontier identification for the
placed representative remains explicit. -/
theorem sourceCarrier_not_isMinimizer_of_horizontalCongruence
    (source : SourcePerimeterSemantics (5 / 4 : ℝ))
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile (5 / 4 : ℝ))
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility : source.CompatibleWithModel profile)
    (sourceCarrier_perimeter_eq_frontier :
      source.perimeter sourceCarrier =
        _root_.WeightedPerimeter (5 / 4 : ℝ)
          (FrontierMeasure sourceCarrier))
    (harea :
      _root_.WeightedArea (5 / 4 : ℝ) sourceCarrier =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ source.IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    source.candidate_isWeightedPerimeterMinimizer_of_horizontalCongruence
      profile hcongruent compatibility
      sourceCarrier_perimeter_eq_frontier hmin
  have hcandidateArea :
      profile.toCandidate.WeightedArea =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := by
    calc
      profile.toCandidate.WeightedArea =
          _root_.WeightedArea (5 / 4 : ℝ) profile.carrier :=
        profile.weightedArea_eq_candidate.symm
      _ = _root_.WeightedArea (5 / 4 : ℝ) sourceCarrier :=
        (weightedArea_eq_of_horizontallyCongruent hcongruent).symm
      _ = LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := harea
  exact (EndpointClosureCell.endpoint_area_candidate_not_isWeightedPerimeterMinimizer
    profile.toCandidate
    profile.toCandidate_satisfiesCMVTypeIVHypotheses
    hcandidateArea) hcandidate

/-- In the repository's canonical complete-frontier semantics, the normalized
raw `E₄` carrier with the type-(iii) endpoint area is unconditionally
non-minimizing. -/
theorem canonicalCarrier_not_isMinimizer
    (profile : CanonicalTypeIVProfile (5 / 4 : ℝ))
    (harea :
      _root_.WeightedArea (5 / 4 : ℝ) profile.carrier =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ (canonicalFrontierSemantics (5 / 4 : ℝ)).IsMinimizer
        profile.carrier := by
  intro hmin
  have hcandidate :=
    (canonicalFrontierSemantics (5 / 4 : ℝ)).candidate_isWeightedPerimeterMinimizer
      profile (canonicalFrontierSemantics.compatibleWithModel profile) hmin
  have hcandidateArea :
      profile.toCandidate.WeightedArea =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 :=
    profile.weightedArea_eq_candidate.symm.trans harea
  exact (EndpointClosureCell.endpoint_area_candidate_not_isWeightedPerimeterMinimizer
    profile.toCandidate
    profile.toCandidate_satisfiesCMVTypeIVHypotheses
    hcandidateArea) hcandidate

/-- Every horizontal translate of a raw `E₄` carrier with the type-(iii)
endpoint area is unconditionally non-minimizing in canonical complete-frontier
semantics. -/
theorem horizontallyCongruentCarrier_not_isMinimizer
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile (5 / 4 : ℝ))
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (harea :
      _root_.WeightedArea (5 / 4 : ℝ) sourceCarrier =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ (canonicalFrontierSemantics (5 / 4 : ℝ)).IsMinimizer sourceCarrier :=
  sourceCarrier_not_isMinimizer_of_horizontalCongruence
    (canonicalFrontierSemantics (5 / 4 : ℝ))
    sourceCarrier profile hcongruent
    (canonicalFrontierSemantics.compatibleWithModel profile) rfl harea

end EndpointClosureSourceBridge
