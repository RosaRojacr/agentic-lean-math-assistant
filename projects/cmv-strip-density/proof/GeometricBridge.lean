/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CapReplacement
import Certificate

/-!
# Area and perimeter bridge for the CMV cap substitution

All equalities in this file are consequences of the coordinate constructors.
Only `cap_replacement_strictly_improves` invokes the accepted analytic
certificate, after positivity of the normalized geometric cap area has been
proved.
-/

open Set
open Real

noncomputable section

namespace FourArcCandidate

variable {lam : ℝ} (candidate : FourArcCandidate lam)

/-- On the positive geometric branch, the accepted `arc` value is exactly the
old cap's normalized arc length. -/
theorem original_arc_eq_ell :
    arc candidate.capX = ell candidate.alpha := by
  rw [candidate.capX_eq_area, arc_eq,
    θOf_area ⟨candidate.alpha_pos,
      lt_trans candidate.alpha_lt_pi_div_two (by linarith [Real.pi_pos])⟩]

/-- Old exterior boundary cost, derived from the two cap arcs. -/
theorem old_exterior_perimeter :
    lam * (candidate.assembly.upperCap.arcLength +
      candidate.assembly.lowerCap.arcLength) =
    2 * lam * candidate.capChord * arc candidate.capX := by
  rw [candidate.original_arc_eq_ell]
  simp only [OneSidedCircularCap.arcLength, FourArcAssembly.upperCap,
    FourArcAssembly.lowerCap, assembly, stripCore]
  ring

/-- New exterior boundary cost: one doubled-area cap plus the exposed
interface segment. -/
theorem new_replaced_perimeter :
    lam * candidate.CapReplacement.upperCap.arcLength +
      candidate.CapReplacement.exposedLowerChord.euclideanLength =
    lam * candidate.capChord * arc (2 * candidate.capX) +
      candidate.capChord := by
  rw [candidate.replacement_cap_arc_length,
    candidate.exposed_lower_chord_length]
  ring

/-- The old exterior weighted area is `2 * lam * A`. -/
theorem old_exterior_area :
    lam * (candidate.assembly.upperCap.euclideanArea +
      candidate.assembly.lowerCap.euclideanArea) =
    2 * lam * candidate.capArea := by
  rw [candidate.upperCap_euclideanArea,
    candidate.lowerCap_euclideanArea]
  ring

/-- The new exterior weighted area is `lam * (2A)`. -/
theorem new_exterior_area :
    lam * candidate.CapReplacement.upperCap.euclideanArea =
    lam * (2 * candidate.capArea) := by
  rw [candidate.replacement_cap_area]

/-- The replacement retains the central region definitionally. -/
theorem retained_core_unchanged :
    candidate.CapReplacement.core.carrier = candidate.stripCore.carrier ∧
    candidate.CapReplacement.core.euclideanArea =
      candidate.stripCore.euclideanArea ∧
    candidate.CapReplacement.core.boundaryArcLength =
      candidate.stripCore.boundaryArcLength := by
  exact ⟨rfl, rfl, rfl⟩

/-- Area of the constructed replacement, component by component. -/
theorem replacement_weightedArea_components :
    candidate.capReplacementRegion.WeightedArea =
      candidate.stripCore.euclideanArea +
        lam * (2 * candidate.capArea) := by
  change candidate.CapReplacement.weightedArea lam =
    candidate.stripCore.euclideanArea + lam * (2 * candidate.capArea)
  rw [ReplacementAssembly.weightedArea_formula, capReplacement_core,
    candidate.replacement_cap_area]

/-- Exact weighted-area preservation.  The exposed chord contributes no planar
area; both sides retain the same central piece. -/
theorem cap_replacement_preserves_area :
    candidate.capReplacementRegion.WeightedArea =
      candidate.WeightedArea := by
  rw [candidate.replacement_weightedArea_components,
    candidate.weightedArea_components]
  ring

/-- Candidate perimeter rewritten in the Morgan cap normalization. -/
theorem candidate_perimeter_cap_components :
    candidate.WeightedPerimeter =
      candidate.stripCore.boundaryArcLength +
        2 * lam * candidate.capChord * arc candidate.capX := by
  rw [candidate.weightedPerimeter_components,
    candidate.original_arc_eq_ell]

/-- Replacement perimeter from its three retained/new boundary components. -/
theorem replacement_perimeter_cap_components :
    candidate.capReplacementRegion.WeightedPerimeter =
      candidate.stripCore.boundaryArcLength +
        lam * candidate.capChord * arc (2 * candidate.capX) +
        candidate.capChord := by
  change _root_.WeightedPerimeter lam
      (FrontierMeasure candidate.CapReplacement.carrier) =
    candidate.stripCore.boundaryArcLength +
      lam * candidate.capChord * arc (2 * candidate.capX) +
        candidate.capChord
  rw [← replacement_frontier_weightedPerimeter_eq,
    ReplacementAssembly.weightedPerimeter_formula, capReplacement_core,
    candidate.replacement_cap_arc_length,
    candidate.exposed_lower_chord_length]
  ring

/-- Exact signed perimeter-difference identity after cancellation of the
retained side arcs. -/
theorem cap_replacement_perimeter_difference :
    candidate.capReplacementRegion.WeightedPerimeter -
      candidate.WeightedPerimeter =
    candidate.capChord * (1 - lam * g candidate.capX) := by
  rw [candidate.replacement_perimeter_cap_components,
    candidate.candidate_perimeter_cap_components]
  rw [g]
  ring

/-- Equivalent opposite signed factorization, only after `lam ≠ 0`. -/
theorem candidate_minus_replacement_factored (hlam : lam ≠ 0) :
    candidate.WeightedPerimeter -
      candidate.capReplacementRegion.WeightedPerimeter =
    lam * candidate.capChord * (g candidate.capX - 1 / lam) := by
  calc
    candidate.WeightedPerimeter -
        candidate.capReplacementRegion.WeightedPerimeter =
      -(candidate.capReplacementRegion.WeightedPerimeter -
        candidate.WeightedPerimeter) := by ring
    _ = -(candidate.capChord * (1 - lam * g candidate.capX)) := by
      rw [candidate.cap_replacement_perimeter_difference]
    _ = lam * candidate.capChord * (g candidate.capX - 1 / lam) := by
      field_simp [hlam]
      ring

/-- The campaign threshold itself implies the positive density domain. -/
theorem density_pos_of_campaign_threshold
    (hlam : (1.2581840884 : ℝ) ≤ lam) : 0 < lam := by
  norm_num at hlam ⊢
  linarith

/-- This is the sole geometric use of the accepted optimized analytic theorem.
Strictness remains valid when `hlam` is equality. -/
theorem cap_replacement_strictly_improves
    (hlam : (1.2581840884 : ℝ) ≤ lam) :
    candidate.capReplacementRegion.WeightedPerimeter <
      candidate.WeightedPerimeter := by
  have hlam_pos : 0 < lam := density_pos_of_campaign_threshold hlam
  have hcomparison : 1 / lam < g candidate.capX :=
    cmv_comparison_bound_optimized hlam candidate.capX_pos
  have hscaled := mul_lt_mul_of_pos_left hcomparison hlam_pos
  have hunit : lam * (1 / lam) = 1 := by
    field_simp [ne_of_gt hlam_pos]
  rw [hunit] at hscaled
  have hfactor : 1 - lam * g candidate.capX < 0 := sub_neg.mpr hscaled
  have hdifference :
      candidate.capReplacementRegion.WeightedPerimeter -
        candidate.WeightedPerimeter < 0 := by
    rw [candidate.cap_replacement_perimeter_difference]
    exact mul_neg_of_pos_of_neg candidate.capChord_pos hfactor
  linarith

/-- Explicit receipt for the included non-strict threshold boundary. -/
theorem cap_replacement_strict_at_campaign_threshold
    {candidate : FourArcCandidate (1.2581840884 : ℝ)} :
    candidate.capReplacementRegion.WeightedPerimeter <
      candidate.WeightedPerimeter :=
  candidate.cap_replacement_strictly_improves le_rfl

end FourArcCandidate
