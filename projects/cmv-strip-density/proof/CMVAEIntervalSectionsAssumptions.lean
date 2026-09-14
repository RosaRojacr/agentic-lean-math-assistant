import CMVAEIntervalSections

open Set Filter MeasureTheory Bornology
open scoped ENNReal MeasureTheory Topology

namespace CMVRelaxation

#print axioms HasAEIntervalHorizontalSections
#print axioms ae_horizontalSection_congr_ae
#print axioms ordConnected_horizontalSection_aeOpenRepresentative
#print axioms IsOpen.eq_Ioo_sInf_sSup_of_nonempty_isBounded_ordConnected
#print axioms horizontalSection_eq_Ioo_selfEndpoints_aeOpenRepresentative
#print axioms horizontalSection_empty_or_Ioo_aeOpenRepresentative
#print axioms reflectAcrossVerticalAxis
#print axioms reflectAcrossVerticalAxis_involutive
#print axioms measurePreserving_reflectAcrossVerticalAxis
#print axioms aeOpenRepresentative_reflection_mem_iff
#print axioms horizontalSection_empty_or_centered_Ioo_aeOpenRepresentative

/-- Compiled hypothesis contract: the all-height conclusion consumes only an
explicit bounded open AE representative and AE existential interval fibers. -/
example {E U : Set PlanePoint}
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hEU : E =ᵐ[volume] U)
    (hsections : HasAEIntervalHorizontalSections E) :
    ∀ y : ℝ,
      CMVSourceClassification.horizontalSection (aeOpenRepresentative E) y = ∅ ∨
        ∃ a b : ℝ, a < b ∧
          CMVSourceClassification.horizontalSection
            (aeOpenRepresentative E) y = Ioo a b := by
  intro y
  exact horizontalSection_empty_or_Ioo_aeOpenRepresentative
    hUopen hEU hUbounded hsections y

/-- A common center appears in the pointwise conclusion only when the separate
AE-centered-section premise is supplied. -/
example {E U : Set PlanePoint} (axis : ℝ)
    (hUopen : IsOpen U) (hUbounded : Bornology.IsBounded U)
    (hEU : E =ᵐ[volume] U)
    (hcentered :
      CMVSourceClassification.HasCenteredHorizontalIntervalSections axis E) :
    ∀ y : ℝ,
      CMVSourceClassification.horizontalSection (aeOpenRepresentative E) y = ∅ ∨
        ∃ radius : ℝ, 0 < radius ∧
          CMVSourceClassification.horizontalSection
              (aeOpenRepresentative E) y =
            Ioo (axis - radius) (axis + radius) := by
  intro y
  exact horizontalSection_empty_or_centered_Ioo_aeOpenRepresentative
    axis hUopen hEU hUbounded hcentered y

end CMVRelaxation
