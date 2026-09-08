/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFourArcSharpRecovery

/-!
# Assumptions audit and unequal-radius recovery specimen

The specimen has strip radius `2` and exterior-cap radius `1`, so it exercises
the assembly theorem beyond the common-radius canonical family.
-/

open Set Filter MeasureTheory
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVRelaxation.FourArcSharpRecovery

/-- A strict four-arc assembly with chord one, strip curvature one half, and
exterior angle pi over six. -/
def unequalRadiusSpecimen : FourArcAssembly where
  core := {
    chord := 1
    curvature := 1 / 2
    chord_pos := by norm_num
    curvature_pos := by norm_num
    curvature_le_one := by norm_num }
  outerAngle := Real.pi / 6
  outerAngle_pos := by positivity
  outerAngle_lt_pi_div_two := by nlinarith [Real.pi_pos]

@[simp] theorem unequalRadiusSpecimen_core_radius :
    unequalRadiusSpecimen.core.radius = 2 := by
  norm_num [unequalRadiusSpecimen, StripCore.radius]

@[simp] theorem unequalRadiusSpecimen_exterior_radius :
    unequalRadiusSpecimen.upperCap.radius = 1 := by
  norm_num [unequalRadiusSpecimen, FourArcAssembly.upperCap,
    OneSidedCircularCap.radius, Real.sin_pi_div_six]

/-- The compiled recovery example is genuinely outside the common-radius
specialization. -/
theorem unequalRadiusSpecimen_radii_ne :
    unequalRadiusSpecimen.core.radius ≠
      unequalRadiusSpecimen.upperCap.radius := by
  norm_num

/-- Concrete smooth recovery at density two for unequal radii. -/
theorem unequalRadiusSpecimen_recovery :
    ∃ sequence : SmoothSequence,
      sequence.ConvergesTo unequalRadiusSpecimen.carrier ∧
      sequence.cost 2 ≤
        ENNReal.ofReal
          (_root_.WeightedPerimeter 2
            (FrontierMeasure unequalRadiusSpecimen.carrier)) := by
  let hcurvature : unequalRadiusSpecimen.core.curvature < 1 := by
    norm_num [unequalRadiusSpecimen]
  exact ⟨assemblyRecoverySequence unequalRadiusSpecimen hcurvature,
    assemblyRecoverySequence_converges unequalRadiusSpecimen hcurvature,
    assemblyRecoverySequence_cost_le unequalRadiusSpecimen hcurvature
      (by norm_num)⟩

/-- The same concrete unequal-radius carrier is an admissible relaxed source. -/
theorem unequalRadiusSpecimen_sourceAdmissible :
    (relaxedSourceSemantics 2).IsAdmissible unequalRadiusSpecimen.carrier := by
  exact assembly_sourceAdmissible unequalRadiusSpecimen
    (by norm_num [unequalRadiusSpecimen]) (by norm_num)

#print axioms FourArcSquaredRecovery.attachmentSquares
#print axioms FourArcSquaredRecovery.mem_source_iff_sq_le_targetQ
#print axioms FourArcSquaredRecovery.isSmoothDomain_domain
#print axioms FourArcSquaredRecovery.recoverySequence_converges
#print axioms extended_frontierCost_eq_smoothCost_source
#print axioms exists_sharp_smoothCost_domain_bound
#print axioms assemblyRecoverySequence_converges
#print axioms assemblyRecoverySequence_cost_le
#print axioms assembly_weightedArea_integrable
#print axioms assembly_relaxedPerimeter_le_frontierCost
#print axioms assembly_sourceAdmissible
#print axioms unequalRadiusSpecimen_radii_ne
#print axioms unequalRadiusSpecimen_recovery
#print axioms unequalRadiusSpecimen_sourceAdmissible

end CMVRelaxation.FourArcSharpRecovery
