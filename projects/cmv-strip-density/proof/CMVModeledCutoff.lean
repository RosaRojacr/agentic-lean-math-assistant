/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CandidateExclusion
import MiddleFaceCells
import CompactCells1003To1023
import CMVRelaxation
import CMVSourceSectionClassification
import UniversalStationaryPair

/-!
# Unconditional modeled cutoff at 51/50

This module composes the exact middle-face cells on `[51/50, 33/32]`, all 1,024
compact cells on `[33/32, 9/7]`, and the cap-replacement exclusion above
`1.2581840884`.
-/

noncomputable section

namespace CMVModeledCutoff

open MeasureTheory
open CMVRelaxation

/-- Every modeled type-(iv) candidate is excluded throughout the admissible
density range.  The candidate hypotheses supply `1 < lam`; source
classification and reduced-boundary compatibility are not asserted here. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ}
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      candidate hcandidate.density_jump hcandidate

/-- Explicit contiguous modeled coverage of the closed-upper near-one range
`1 < lam ≤ 1001 / 1000`.  This exposes the requested interval while retaining
the stronger all-density result above. -/
theorem candidate_not_isWeightedPerimeterMinimizer_through_1001_1000
    {lam : ℝ}
    (hlower : 1 < lam)
    (hupper : lam ≤ 1001 / 1000)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_through_1001_1000
      candidate hlower hupper hcandidate

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

/-- For the concrete relaxed source semantics, almost-everywhere horizontal
classification and model compatibility exclude a source minimizer above the
cutoff without a caller-supplied normalization witness. -/
theorem relaxedSourceCarrier_not_isMinimizer_from_51_50_of_aeHorizontalCongruence
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      AlmostEverywhereHorizontallyCongruent
        sourceCarrier profile.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        profile) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer
      sourceCarrier := by
  intro hmin
  have hcandidate :=
    relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_aeHorizontalCongruence
      profile hcongruent compatibility hmin
  exact candidate_not_isWeightedPerimeterMinimizer_from_51_50
    hlower profile.toCandidate
      profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- Exact horizontal classification has the same normalization-free concrete
source cutoff. -/
theorem relaxedSourceCarrier_not_isMinimizer_from_51_50_of_horizontalCongruence
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      HorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        profile) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer
      sourceCarrier := by
  intro hmin
  have hcandidate :=
    relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_horizontalCongruence
      profile hcongruent compatibility hmin
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

/-- Independent source radius/angle coordinates and an almost-everywhere
coordinate realization feed the normalization-free cutoff after the checked
principal-angle and carrier reduction. Reduced-boundary/model compatibility
remains explicit. -/
theorem relaxedSourceCarrier_not_isMinimizer_from_51_50_of_rawFourArcCoordinates
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsource : sourceCarrier =ᵐ[volume] raw.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular)) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  relaxedSourceCarrier_not_isMinimizer_from_51_50_of_aeHorizontalCongruence
    hlower sourceCarrier (raw.toCanonicalProfile hregular)
      (raw.almostEverywhereHorizontallyCongruent_profile_of_ae
        hregular hsource)
      compatibility

/-- CMV's interval-slice classification is sufficient for the concrete source
cutoff.  Null measurability is obtained from source minimality, while Fubini
reconstructs the planar representative; no planar congruence premise is
required. -/
theorem relaxedSourceCarrier_not_isMinimizer_from_51_50_of_horizontalSections
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsections :
      CMVSourceClassification.HasTypeIVHorizontalSections sourceCarrier raw)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular)) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  have hsourceNull : NullMeasurableSet sourceCarrier volume :=
    hmin.1.1.1
  exact
    relaxedSourceCarrier_not_isMinimizer_from_51_50_of_rawFourArcCoordinates
      hlower sourceCarrier raw hregular
        (CMVSourceClassification.sourceCarrier_ae_rawCarrier_of_horizontalSections
          raw hsourceNull hsections)
        compatibility hmin

/-- A relaxed source minimizer represented almost everywhere by independent
regular four-arc coordinates can occur only in the open near-one range. -/
theorem relaxedSourceCarrier_minimizer_open_range_51_50_of_rawFourArcCoordinates
    {lam : ℝ}
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsource : sourceCarrier =ᵐ[volume] raw.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular))
    (hmin : (relaxedSourceSemantics lam).IsMinimizer sourceCarrier) :
    1 < lam ∧ lam < (51 / 50 : ℝ) := by
  refine ⟨hregular.density_jump, ?_⟩
  by_contra hcutoff
  exact
    relaxedSourceCarrier_not_isMinimizer_from_51_50_of_rawFourArcCoordinates
      (le_of_not_gt hcutoff) sourceCarrier raw hregular hsource
        compatibility hmin

/-- A sectionwise-classified regular source minimizer can occur only in the
open near-one density range. -/
theorem relaxedSourceCarrier_minimizer_open_range_51_50_of_horizontalSections
    {lam : ℝ}
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsections :
      CMVSourceClassification.HasTypeIVHorizontalSections sourceCarrier raw)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular))
    (hmin : (relaxedSourceSemantics lam).IsMinimizer sourceCarrier) :
    1 < lam ∧ lam < (51 / 50 : ℝ) := by
  refine ⟨hregular.density_jump, ?_⟩
  by_contra hcutoff
  exact
    relaxedSourceCarrier_not_isMinimizer_from_51_50_of_horizontalSections
      (le_of_not_gt hcutoff) sourceCarrier raw hregular hsections
        compatibility hmin

/-- Any source carrier with an explicit canonical normalization and checked
model compatibility is excluded at every admissible density.  These two
source-side hypotheses remain explicit. -/
theorem sourceCarrier_not_isMinimizer
    {lam : ℝ}
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
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      profile.toCandidate profile.density_jump
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- Under canonical complete-frontier semantics, every regular canonical
type-(iv) carrier is excluded without a supplied normalization or compatibility
witness. -/
theorem canonicalCarrier_not_isMinimizer
    {lam : ℝ} (profile : CanonicalTypeIVProfile lam) :
    ¬ (canonicalFrontierSemantics lam).IsMinimizer profile.carrier := by
  intro hmin
  have hcandidate :=
    (canonicalFrontierSemantics lam).candidate_isWeightedPerimeterMinimizer
      profile (canonicalFrontierSemantics.compatibleWithModel profile) hmin
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      profile.toCandidate profile.density_jump
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- Almost-everywhere horizontal classification and explicit model
compatibility exclude a relaxed source carrier at every admissible density. -/
theorem relaxedSourceCarrier_not_isMinimizer_of_aeHorizontalCongruence
    {lam : ℝ}
    (sourceCarrier : Set PlanePoint)
    (profile : CanonicalTypeIVProfile lam)
    (hcongruent :
      AlmostEverywhereHorizontallyCongruent sourceCarrier profile.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel profile) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_aeHorizontalCongruence
      profile hcongruent compatibility hmin
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      profile.toCandidate profile.density_jump
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- Independent regular four-arc coordinates feed the all-density relaxed
source exclusion after almost-everywhere carrier identification. -/
theorem relaxedSourceCarrier_not_isMinimizer_of_rawFourArcCoordinates
    {lam : ℝ}
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsource : sourceCarrier =ᵐ[volume] raw.carrier)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular)) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  relaxedSourceCarrier_not_isMinimizer_of_aeHorizontalCongruence
    sourceCarrier (raw.toCanonicalProfile hregular)
      (raw.almostEverywhereHorizontallyCongruent_profile_of_ae hregular hsource)
      compatibility

/-- The checked Fubini reconstruction turns CMV's horizontal-section
classification into all-density relaxed source exclusion.  Universal
classification and model compatibility are still the exact open hypotheses. -/
theorem relaxedSourceCarrier_not_isMinimizer_of_horizontalSections
    {lam : ℝ}
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsections :
      CMVSourceClassification.HasTypeIVHorizontalSections sourceCarrier raw)
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular)) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  exact relaxedSourceCarrier_not_isMinimizer_of_rawFourArcCoordinates
    sourceCarrier raw hregular
      (CMVSourceClassification.sourceCarrier_ae_rawCarrier_of_horizontalSections
        raw hmin.1.1.1 hsections)
      compatibility hmin

/-- The source-native equality-case data now feed the all-density exclusion
without a caller-supplied planar equality. Universal classification still has
to derive centered interval slices and slice equimeasurability from source
minimality; reduced-boundary/model compatibility remains explicit. -/
theorem relaxedSourceCarrier_not_isMinimizer_of_centeredIntervals_of_measure_eq
    {lam : ℝ}
    (sourceCarrier : Set PlanePoint)
    (raw : CMVSourceClassification.RawFourArcCoordinates)
    (hregular : raw.SatisfiesRegularSnell lam)
    (hsource :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections
        raw.horizontalPlacement sourceCarrier)
    (hmeasure : ∀ᵐ y ∂(volume : Measure ℝ),
      volume (CMVSourceClassification.horizontalSection sourceCarrier y) =
        volume (CMVSourceClassification.horizontalSection raw.carrier y))
    (compatibility :
      (relaxedSourceSemantics lam).CompatibleWithModel
        (raw.toCanonicalProfile hregular)) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier :=
  relaxedSourceCarrier_not_isMinimizer_of_horizontalSections
    sourceCarrier raw hregular
      (CMVSourceClassification.hasTypeIVHorizontalSections_of_centeredIntervals_of_measure_eq
        raw hregular.toClosedGeometry hsource hmeasure)
      compatibility

end CMVModeledCutoff
