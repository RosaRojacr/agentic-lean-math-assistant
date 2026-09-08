/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVProfileSharpRecovery
import UniversalStationaryPair

/-!
# Relaxed source semantics for canonical type-IV profiles

Exact profilewise recovery makes every canonical carrier source-admissible and
identifies the real-valued relaxed perimeter with its complete-frontier
weighted perimeter.  Thus construction of `CompatibleWithModel` needs only its
unchanged arbitrary-competitor coverage proposition.
-/

open MeasureTheory
open scoped ENNReal MeasureTheory

noncomputable section

namespace CMVRelaxation.ProfileSourceSemantics

variable {lam : ℝ} (profile : CanonicalTypeIVProfile lam)

/-- The canonical complete-frontier weighted perimeter is nonnegative. -/
theorem frontierWeightedPerimeter_nonneg :
    0 ≤ _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier) := by
  unfold _root_.WeightedPerimeter
  apply integral_nonneg
  intro p
  unfold StripDensity
  split_ifs
  · norm_num
  · exact le_trans (by norm_num) profile.density_jump.le

/-- Exact profilewise recovery gives a genuinely finite extended relaxed
perimeter. -/
theorem relaxedPerimeter_lt_top_profile :
    relaxedPerimeter lam profile.carrier < ⊤ := by
  rw [ProfileSharpRecovery.relaxedPerimeter_eq_frontierCost_profile profile]
  exact ENNReal.ofReal_lt_top

/-- Every canonical type-IV carrier belongs to the concrete relaxed source
domain, including the independently required finite weighted area. -/
theorem isAdmissible_profile :
    (relaxedSourceSemantics lam).IsAdmissible profile.carrier := by
  rw [relaxedSourceSemantics_isAdmissible]
  constructor
  · constructor
    · rw [profile.carrier_eq_candidate_assembly]
      exact profile.toCandidate.assembly.isClosed_carrier.measurableSet.nullMeasurableSet
    · exact relaxedPerimeter_lt_top_profile profile
  · exact profile.integrableOn_carrier

/-- On every canonical type-IV carrier, the finite real source perimeter is
exactly the actual complete-frontier weighted perimeter. -/
theorem profile_perimeter_eq_frontier :
    (relaxedSourceSemantics lam).perimeter profile.carrier =
      _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier) := by
  change (relaxedPerimeter lam profile.carrier).toReal =
    _root_.WeightedPerimeter lam (FrontierMeasure profile.carrier)
  rw [ProfileSharpRecovery.relaxedPerimeter_eq_frontierCost_profile profile,
    ENNReal.toReal_ofReal (frontierWeightedPerimeter_nonneg profile)]

/-- Once arbitrary modeled competitors satisfy the existing coverage
proposition, exact profile recovery supplies the other
`CompatibleWithModel` field without any additional profile hypothesis. -/
theorem compatibleWithModel_of_model_covered
    (model_covered : ∀ competitor : AdmissibleCompetitor lam,
      (relaxedSourceSemantics lam).IsAdmissible competitor.carrier ∧
        (relaxedSourceSemantics lam).perimeter competitor.carrier ≤
          competitor.WeightedPerimeter) :
    (relaxedSourceSemantics lam).CompatibleWithModel profile := by
  exact ⟨profile_perimeter_eq_frontier profile, model_covered⟩

/-- A canonical source carrier cannot minimize at any admissible density once
only the unchanged arbitrary-competitor coverage proposition is supplied. -/
theorem profile_not_isMinimizer_of_model_covered
    (model_covered : ∀ competitor : AdmissibleCompetitor lam,
      (relaxedSourceSemantics lam).IsAdmissible competitor.carrier ∧
        (relaxedSourceSemantics lam).perimeter competitor.carrier ≤
          competitor.WeightedPerimeter) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer profile.carrier := by
  intro hmin
  have hcandidate :=
    (relaxedSourceSemantics lam).candidate_isWeightedPerimeterMinimizer
      profile (compatibleWithModel_of_model_covered profile model_covered) hmin
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      profile.toCandidate profile.density_jump
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- Exact horizontal classification feeds the all-density source exclusion
with only arbitrary-competitor model coverage left explicit. -/
theorem sourceCarrier_not_isMinimizer_of_horizontalCongruence_of_model_covered
    {sourceCarrier : Set PlanePoint}
    (hcongruent : HorizontallyCongruent sourceCarrier profile.carrier)
    (model_covered : ∀ competitor : AdmissibleCompetitor lam,
      (relaxedSourceSemantics lam).IsAdmissible competitor.carrier ∧
        (relaxedSourceSemantics lam).perimeter competitor.carrier ≤
          competitor.WeightedPerimeter) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_horizontalCongruence
      profile hcongruent
        (compatibleWithModel_of_model_covered profile model_covered) hmin
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      profile.toCandidate profile.density_jump
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

/-- Almost-everywhere horizontal classification has the same all-density
consumer and the same sole remaining model-coverage premise. -/
theorem sourceCarrier_not_isMinimizer_of_aeHorizontalCongruence_of_model_covered
    {sourceCarrier : Set PlanePoint}
    (hcongruent :
      AlmostEverywhereHorizontallyCongruent sourceCarrier profile.carrier)
    (model_covered : ∀ competitor : AdmissibleCompetitor lam,
      (relaxedSourceSemantics lam).IsAdmissible competitor.carrier ∧
        (relaxedSourceSemantics lam).perimeter competitor.carrier ≤
          competitor.WeightedPerimeter) :
    ¬ (relaxedSourceSemantics lam).IsMinimizer sourceCarrier := by
  intro hmin
  have hcandidate :=
    relaxedSourceSemantics_candidate_isWeightedPerimeterMinimizer_of_aeHorizontalCongruence
      profile hcongruent
        (compatibleWithModel_of_model_covered profile model_covered) hmin
  exact
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_density_gt_one
      profile.toCandidate profile.density_jump
        profile.toCandidate_satisfiesCMVTypeIVHypotheses hcandidate

end CMVRelaxation.ProfileSourceSemantics
