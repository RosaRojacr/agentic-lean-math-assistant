/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourBoundaryRigiditySourceExclusion
import CMVFigureFourBilateralExamples

/-!
# Concrete applications of Figure-4 boundary rigidity

The strict-radius and radius-one bilateral sources exercise the boundary-only
reconstruction after nonzero horizontal placement.
-/

open Set MeasureTheory

noncomputable section

namespace CMVFigureFour.Examples

/-- Boundary-only reconstruction for every horizontal placement of the strict
`lambda = 2`, source-radius-two specimen. -/
theorem strictBilateralSourceAt_representative_eq_interior (t : ℝ) :
    (strictBilateralSourceAt t).representative =
      interior (strictBilateralSourceAt t).toRawFourArcCoordinates.carrier := by
  exact
    (strictBilateralSourceAt t).toSourceGeometry.representative_eq_interior_raw_carrier

/-- Boundary-only reconstruction for every horizontal placement of the exact
`lambda = 2`, source-radius-one specimen. -/
theorem endpointBilateralSourceAt_representative_eq_interior (t : ℝ) :
    (endpointBilateralSourceAt t).representative =
      interior (endpointBilateralSourceAt t).toRawFourArcCoordinates.carrier := by
  exact
    (endpointBilateralSourceAt t).toSourceGeometry.representative_eq_interior_raw_carrier

/-- A concrete nonzero placement exercises strict-radius reconstruction. -/
theorem strictBilateralSource_negThree_representative_eq_interior :
    (strictBilateralSourceAt (-3)).representative =
      interior
        (strictBilateralSourceAt (-3)).toRawFourArcCoordinates.carrier :=
  strictBilateralSourceAt_representative_eq_interior (-3)

/-- A concrete nonzero placement exercises the radius-one reconstruction. -/
theorem endpointBilateralSource_seven_representative_eq_interior :
    (endpointBilateralSourceAt 7).representative =
      interior
        (endpointBilateralSourceAt 7).toRawFourArcCoordinates.carrier :=
  endpointBilateralSourceAt_representative_eq_interior 7

/-- Source exclusion is invariant under every horizontal placement of the
strict-radius specimen. -/
theorem strictBilateralSourceAt_not_isMinimizer (t : ℝ) :
    ¬ (CMVRelaxation.relaxedSourceSemantics 2).IsMinimizer
      (strictBilateralSourceAt t).sourceCarrier :=
  (strictBilateralSourceAt t).sourceCarrier_not_isMinimizer

/-- Source exclusion is invariant under every horizontal placement of the
radius-one specimen. -/
theorem endpointBilateralSourceAt_not_isMinimizer (t : ℝ) :
    ¬ (CMVRelaxation.relaxedSourceSemantics 2).IsMinimizer
      (endpointBilateralSourceAt t).sourceCarrier :=
  (endpointBilateralSourceAt t).sourceCarrier_not_isMinimizer

/-- The nonzero strict-radius specimen reaches the source-facing all-density
exclusion with no premises beyond its frozen source geometry. -/
theorem strictBilateralSource_negThree_not_isMinimizer :
    ¬ (CMVRelaxation.relaxedSourceSemantics 2).IsMinimizer
      (strictBilateralSourceAt (-3)).sourceCarrier :=
  strictBilateralSourceAt_not_isMinimizer (-3)

/-- The same source-facing exclusion includes the exact radius-one specimen at
a nonzero placement. -/
theorem endpointBilateralSource_seven_not_isMinimizer :
    ¬ (CMVRelaxation.relaxedSourceSemantics 2).IsMinimizer
      (endpointBilateralSourceAt 7).sourceCarrier :=
  endpointBilateralSourceAt_not_isMinimizer 7

/-- An unbounded planar-null set used to verify that boundary rigidity requires
boundedness only of the stored open representative, not of the actual source. -/
def horizontalNullLine : Set PlanePoint := {p | p.2 = 0}

@[simp] theorem volume_horizontalNullLine :
    volume horizontalNullLine = 0 :=
  volume_horizontalLine 0

private theorem strictBilateralSourceAt_negThree_ae_unboundedModification :
    Set.union (strictBilateralSourceAt (-3)).sourceCarrier horizontalNullLine
        =ᵐ[volume]
      (strictBilateralSourceAt (-3)).representative := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · apply measure_mono_null
      (t := Set.union
        ((strictBilateralSourceAt (-3)).sourceCarrier \
          (strictBilateralSourceAt (-3)).representative)
        horizontalNullLine)
    · rintro p ⟨hp, hpNotRepresentative⟩
      rcases hp with hpSource | hpLine
      · exact Or.inl ⟨hpSource, hpNotRepresentative⟩
      · exact Or.inr hpLine
    · exact measure_union_null
        (MeasureTheory.ae_eq_set.mp
          (strictBilateralSourceAt (-3)).sourceRepresentative.source_ae_representative).1
        volume_horizontalNullLine
  · apply measure_mono_null
      (t := (strictBilateralSourceAt (-3)).representative \
        (strictBilateralSourceAt (-3)).sourceCarrier)
    · rintro p ⟨hpRepresentative, hpNotUnion⟩
      exact
        ⟨hpRepresentative, fun hpSource => hpNotUnion (Or.inl hpSource)⟩
    · exact
        (MeasureTheory.ae_eq_set.mp
          (strictBilateralSourceAt (-3)).sourceRepresentative.source_ae_representative).2

/-- The unbounded null modification belongs to the same planar measure class as
the original frozen bilateral source, without rebuilding the source signature. -/
theorem strictBilateralSourceAt_negThree_ae_sourceCarrier :
    Set.union (strictBilateralSourceAt (-3)).sourceCarrier horizontalNullLine
        =ᵐ[volume]
      (strictBilateralSourceAt (-3)).sourceCarrier :=
  strictBilateralSourceAt_negThree_ae_unboundedModification.trans
    (strictBilateralSourceAt (-3)).sourceRepresentative.source_ae_representative.symm

/-- The GMT-facing measure-class consumer excludes the unbounded modification
directly; no new bounded representative or geometric incidence value is needed. -/
theorem strictBilateralSourceAt_negThree_union_horizontalNullLine_not_isMinimizer :
    ¬ (CMVRelaxation.relaxedSourceSemantics 2).IsMinimizer
      (Set.union (strictBilateralSourceAt (-3)).sourceCarrier
        horizontalNullLine) :=
  (strictBilateralSourceAt (-3)).aeEquivalentCarrier_not_isMinimizer
    strictBilateralSourceAt_negThree_ae_sourceCarrier

/-- An actual Figure-4 source may be unbounded after a planar-null
modification while retaining the same bounded open representative and all
literal source geometry. -/
def strictBilateralSourceUnbounded : BilateralSourceIncidence 2 :=
  { strictBilateralSourceAt (-3) with
    sourceCarrier :=
      Set.union (strictBilateralSourceAt (-3)).sourceCarrier horizontalNullLine
    sourceRepresentative := {
      representative_open :=
        (strictBilateralSourceAt (-3)).sourceRepresentative.representative_open
      representative_bounded :=
        (strictBilateralSourceAt (-3)).sourceRepresentative.representative_bounded
      source_ae_representative :=
        strictBilateralSourceAt_negThree_ae_unboundedModification } }

/-- The modified actual source is genuinely unbounded. -/
theorem strictBilateralSourceUnbounded_sourceCarrier_not_bounded :
    ¬ Bornology.IsBounded strictBilateralSourceUnbounded.sourceCarrier := by
  intro hbounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  have hCnonneg : 0 ≤ C := by
    have hzero := hC ((0, 0) : PlanePoint) (by exact Or.inr rfl)
    simpa using hzero
  have hCplus : 0 ≤ C + 1 := by linarith
  have hlarge := hC ((C + 1, 0) : PlanePoint) (by exact Or.inr rfl)
  have hnorm : ‖((C + 1, 0) : PlanePoint)‖ = C + 1 := by
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hCplus, hCplus]
  rw [hnorm] at hlarge
  linarith

/-- Compiled contract: the unbounded null modification keeps the original
bounded representative, reaches the closed raw target almost everywhere, and
is excluded by the same public source theorem. -/
theorem strictBilateralSourceUnbounded_compiledContract :
    (¬ Bornology.IsBounded strictBilateralSourceUnbounded.sourceCarrier) ∧
      strictBilateralSourceUnbounded.representative =
        (strictBilateralSourceAt (-3)).representative ∧
      IsOpen strictBilateralSourceUnbounded.representative ∧
      Bornology.IsBounded strictBilateralSourceUnbounded.representative ∧
      strictBilateralSourceUnbounded.sourceCarrier =ᵐ[volume]
        strictBilateralSourceUnbounded.representative ∧
      strictBilateralSourceUnbounded.sourceCarrier =ᵐ[volume]
        strictBilateralSourceUnbounded.toRawFourArcCoordinates.carrier ∧
      ¬ (CMVRelaxation.relaxedSourceSemantics 2).IsMinimizer
        strictBilateralSourceUnbounded.sourceCarrier := by
  exact
    ⟨strictBilateralSourceUnbounded_sourceCarrier_not_bounded, rfl,
      strictBilateralSourceUnbounded.sourceRepresentative.representative_open,
      strictBilateralSourceUnbounded.sourceRepresentative.representative_bounded,
      strictBilateralSourceUnbounded.sourceRepresentative.source_ae_representative,
      strictBilateralSourceUnbounded.sourceCarrier_ae_raw_carrier,
      strictBilateralSourceUnbounded.sourceCarrier_not_isMinimizer⟩

end CMVFigureFour.Examples
