/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import EqualAreaEnvelope
import TypeThreeAssembly
import CandidateExclusion

/-!
# Geometric realization of the CMV scalar suffix model

This module identifies the scalar formulas used by `LeanSuffixAnalytic` with
the coordinate type-(iii) carrier and the genuine type-(iv) candidate.  The
last comparison is made through a `TypeThreeAssembly.ModeledCompetitorRealization`;
no scalar record is treated as an admissible competitor.
-/

open Real

noncomputable section

namespace CMVSuffixModel

private theorem sqrt_one_sub_div_sq {lam x : ℝ}
    (hlam : 0 < lam) (hrad : 0 ≤ lam ^ 2 - x ^ 2) :
    sqrt (1 - (x / lam) ^ 2) = sqrt (lam ^ 2 - x ^ 2) / lam := by
  calc
    sqrt (1 - (x / lam) ^ 2) =
        sqrt ((lam ^ 2 - x ^ 2) / lam ^ 2) := by
      congr 1
      field_simp [ne_of_gt hlam]
    _ = sqrt (lam ^ 2 - x ^ 2) / sqrt (lam ^ 2) := by
      rw [Real.sqrt_div hrad]
    _ = sqrt (lam ^ 2 - x ^ 2) / lam := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hlam]

namespace TypeThreeAssembly

variable {lam : ℝ} (a : _root_.TypeThreeAssembly lam)

/-- The angle term derived from the coordinate carrier is exactly the angle
term in the retained analytic type-(iii) formula. -/
theorem angleTerm_eq_typeThreeAngle :
    a.angleTerm = LeanSuffixAnalytic.typeThreeAngle lam a.h + π / 2 := by
  rw [_root_.TypeThreeAssembly.angleTerm,
    _root_.TypeThreeAssembly.outerAngle,
    _root_.TypeThreeAssembly.outerArgument,
    _root_.TypeThreeAssembly.innerAngle,
    LeanSuffixAnalytic.typeThreeAngle_add_halfPi]
  rfl

/-- The coordinate carrier's horizontal sine displacement is exactly the
radical displacement in the retained analytic type-(iii) formula. -/
theorem sineGap_eq_typeThreeDelta :
    a.sineGap = LeanSuffixAnalytic.typeThreeDelta lam a.h := by
  have hlam_pos : 0 < lam :=
    lt_trans (by norm_num : (0 : ℝ) < 1) a.density_jump
  have hshape := a.shapeParameter_mem
  have hminus : 0 < lam - a.shapeParameter := by
    linarith [hshape.2, a.density_jump]
  have hplus : 0 < lam + a.shapeParameter := by
    linarith [hshape.1, a.density_jump]
  have hrad : 0 ≤ lam ^ 2 - a.shapeParameter ^ 2 := by
    nlinarith [mul_pos hminus hplus]
  rw [_root_.TypeThreeAssembly.sineGap,
    _root_.TypeThreeAssembly.outerAngle,
    _root_.TypeThreeAssembly.innerAngle, Real.sin_arccos,
    Real.sin_arccos, _root_.TypeThreeAssembly.outerArgument,
    LeanSuffixAnalytic.typeThreeDelta]
  change sqrt (1 - (a.shapeParameter / lam) ^ 2) -
      sqrt (1 - a.shapeParameter ^ 2) =
    sqrt (lam ^ 2 - a.shapeParameter ^ 2) / lam -
      sqrt (1 - a.shapeParameter ^ 2)
  rw [sqrt_one_sub_div_sq hlam_pos hrad]

/-- Exact identification of CMV equation (26)'s area with the analytic
quantity used by the suffix theorem.  Its domain is the full regular
`0 < h₃ < 1` type-(iii) domain, across all three arc branches. -/
theorem scalarWeightedArea_eq_typeThreeArea :
    a.scalarWeightedArea = LeanSuffixAnalytic.typeThreeArea lam a.h := by
  rw [_root_.TypeThreeAssembly.scalarWeightedArea,
    LeanSuffixAnalytic.typeThreeArea,
    angleTerm_eq_typeThreeAngle a, sineGap_eq_typeThreeDelta a]
  rfl

/-- Exact identification of CMV equation (26)'s perimeter with the analytic
quantity used by the suffix theorem, on the full regular type-(iii) domain. -/
theorem scalarWeightedPerimeter_eq_typeThreePerimeter :
    a.scalarWeightedPerimeter =
      LeanSuffixAnalytic.typeThreePerimeter lam a.h := by
  rw [_root_.TypeThreeAssembly.scalarWeightedPerimeter,
    LeanSuffixAnalytic.typeThreePerimeter,
    angleTerm_eq_typeThreeAngle a, sineGap_eq_typeThreeDelta a]

end TypeThreeAssembly

namespace FourArcCandidate

variable {lam : ℝ} (candidate : _root_.FourArcCandidate lam)

private theorem sin_alpha_eq_typeFour_radial
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    sin candidate.alpha = sqrt (lam ^ 2 - candidate.h ^ 2) / lam := by
  have hlam_pos : 0 < lam :=
    lt_trans (by norm_num : (0 : ℝ) < 1) hcandidate.density_jump
  have hrad : 0 ≤ lam ^ 2 - candidate.h ^ 2 := by
    nlinarith [candidate.h_pos, candidate.h_le_one,
      hcandidate.density_jump, sq_nonneg (lam - candidate.h)]
  rw [candidate.alpha_eq_arccos hcandidate, Real.sin_arccos]
  exact sqrt_one_sub_div_sq hlam_pos hrad

private theorem cos_beta_eq_h : cos candidate.beta = candidate.h := by
  rw [_root_.FourArcCandidate.beta, Real.cos_pi_div_two_sub]
  exact Real.sin_arcsin (by linarith [candidate.h_pos]) candidate.h_le_one

private theorem weightedArea_eq_typeFourArea_all
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.WeightedArea =
      LeanSuffixAnalytic.typeFourArea lam candidate.h := by
  have hlam_pos : 0 < lam :=
    lt_trans (by norm_num : (0 : ℝ) < 1) hcandidate.density_jump
  rw [candidate.candidate_area_formula hcandidate,
    sin_alpha_eq_typeFour_radial candidate hcandidate,
    cos_beta_eq_h candidate,
    candidate.alpha_eq_arccos hcandidate]
  unfold LeanSuffixAnalytic.typeFourArea LeanSuffixAnalytic.typeFourAngle
    LeanSuffixAnalytic.typeFourDelta
  field_simp [ne_of_gt candidate.h_pos, ne_of_gt hlam_pos]
  ring_nf

private theorem weightedPerimeter_eq_typeFourPerimeter_all
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.WeightedPerimeter =
      LeanSuffixAnalytic.typeFourPerimeter lam candidate.h := by
  rw [candidate.candidate_perimeter_formula hcandidate,
    candidate.alpha_eq_arccos hcandidate]
  unfold LeanSuffixAnalytic.typeFourPerimeter LeanSuffixAnalytic.typeFourAngle
  field_simp [ne_of_gt candidate.h_pos]

/-- Exact type-(iv) area identification on the regular source domain
`0 < h₄ < 1`.  The strict upper bound is retained explicitly because analytic
fold arguments divide by `sqrt (1 - h₄²)`. -/
theorem regular_weightedArea_eq_typeFourArea
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (_hregular : candidate.h < 1) :
    candidate.WeightedArea =
      LeanSuffixAnalytic.typeFourArea lam candidate.h :=
  weightedArea_eq_typeFourArea_all candidate hcandidate

/-- Exact type-(iv) perimeter identification on the regular source domain. -/
theorem regular_weightedPerimeter_eq_typeFourPerimeter
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (_hregular : candidate.h < 1) :
    candidate.WeightedPerimeter =
      LeanSuffixAnalytic.typeFourPerimeter lam candidate.h :=
  weightedPerimeter_eq_typeFourPerimeter_all candidate hcandidate

/-- Exact type-(iv) area identification at the source endpoint `h₄ = 1`.
This is separate from the regular theorem and invokes no fold expression. -/
theorem endpoint_weightedArea_eq_typeFourArea
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (_hendpoint : candidate.h = 1) :
    candidate.WeightedArea =
      LeanSuffixAnalytic.typeFourArea lam candidate.h :=
  weightedArea_eq_typeFourArea_all candidate hcandidate

/-- Exact type-(iv) perimeter identification at `h₄ = 1`. -/
theorem endpoint_weightedPerimeter_eq_typeFourPerimeter
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (_hendpoint : candidate.h = 1) :
    candidate.WeightedPerimeter =
      LeanSuffixAnalytic.typeFourPerimeter lam candidate.h :=
  weightedPerimeter_eq_typeFourPerimeter_all candidate hcandidate

/-- Branch-complete formula identification.  The proof deliberately splits
the regular curvature from `h₄ = 1`, so later arguments cannot silently apply
a regular fold hypothesis at the endpoint. -/
theorem weightedArea_eq_typeFourArea
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.WeightedArea =
      LeanSuffixAnalytic.typeFourArea lam candidate.h := by
  rcases lt_or_eq_of_le candidate.h_le_one with hregular | hendpoint
  · exact regular_weightedArea_eq_typeFourArea candidate hcandidate hregular
  · exact endpoint_weightedArea_eq_typeFourArea candidate hcandidate hendpoint

/-- Branch-complete perimeter identification, with the same explicit regular
versus endpoint split as the area theorem. -/
theorem weightedPerimeter_eq_typeFourPerimeter
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    candidate.WeightedPerimeter =
      LeanSuffixAnalytic.typeFourPerimeter lam candidate.h := by
  rcases lt_or_eq_of_le candidate.h_le_one with hregular | hendpoint
  · exact regular_weightedPerimeter_eq_typeFourPerimeter candidate
      hcandidate hregular
  · exact endpoint_weightedPerimeter_eq_typeFourPerimeter candidate
      hcandidate hendpoint

/-- A scalar type-(iii) equal-area and strict-perimeter witness becomes a
counterexample to minimality through the canonical finite-perimeter
realization of its coordinate carrier.  The scalar `h₃` is required to lie in
the honest regular source domain. -/
theorem not_isWeightedPerimeterMinimizer_of_analytic_typeThree
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    {h₃ : ℝ} (hh₃ : 0 < h₃) (hh₃_one : h₃ < 1)
    (equalArea : LeanSuffixAnalytic.typeThreeArea lam h₃ =
      LeanSuffixAnalytic.typeFourArea lam candidate.h)
    (strictPerimeter : LeanSuffixAnalytic.typeThreePerimeter lam h₃ <
      LeanSuffixAnalytic.typeFourPerimeter lam candidate.h) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  let a : _root_.TypeThreeAssembly lam :=
    { h := h₃
      density_jump := hcandidate.density_jump
      h_pos := hh₃
      h_lt_one := hh₃_one }
  rcases a.hasModeledCompetitor with ⟨realization⟩
  apply candidate.not_isWeightedPerimeterMinimizer_of_typeThree a realization
  · rw [TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea a,
      weightedArea_eq_typeFourArea candidate hcandidate]
    exact equalArea
  · rw [TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter a,
      weightedPerimeter_eq_typeFourPerimeter candidate hcandidate]
    exact strictPerimeter

/-- A single certified stationary descending pair excludes every modeled
type-(iv) candidate at the same density, including the closure endpoint. -/
theorem not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (pair : LeanSuffixAnalytic.StationaryEqualAreaPair lam)
    (hfoldThree :
      LeanSuffixAnalytic.typeThreeFold lam pair.h₃ < 0)
    (hperimeter :
      LeanSuffixAnalytic.typeThreePerimeter lam pair.h₃ <
        LeanSuffixAnalytic.typeFourPerimeter lam pair.h₄) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases pair.allCurvature_typeThreeImprovement
      hcandidate.density_jump hfoldThree hperimeter
      candidate.h_pos candidate.h_le_one with
    ⟨h₃, hh₃, hh₃_one, hequal, hstrict⟩
  exact not_isWeightedPerimeterMinimizer_of_analytic_typeThree
    candidate hcandidate hh₃ hh₃_one hequal hstrict

end FourArcCandidate


/-- Honest candidate-level consumer for the retained suffix.  The two analytic
inputs are the explicit root-envelope existence theorem and the genuine
stationary fold-gap theorem; neither is an alias for candidate exclusion.
Given those separately proved inputs, the conclusion compares the candidate
with the canonical admissible type-(iii) region. -/
theorem not_isWeightedPerimeterMinimizer_on_retainedSuffix
    (hasEnvelope :
      LeanSuffixAnalytic.HasDescendingEqualAreaEnvelopeOnRetainedSuffix)
    (foldGapNegative : LeanSuffixAnalytic.RetainedFoldGapNegative)
    {lam : ℝ} (hlam : LeanSuffixAnalytic.InRetainedSuffix lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases LeanSuffixAnalytic.allCurvature_typeThreeImprovement
      hasEnvelope foldGapNegative hlam candidate.h_pos candidate.h_le_one with
    ⟨h₃, hh₃, hh₃_one, equalArea, strictPerimeter⟩
  exact FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree
    candidate hcandidate hh₃ hh₃_one equalArea strictPerimeter


/-- Conditional composition of the retained suffix with the existing
`1.2581840884` cap-replacement exclusion.  Once the two analytic interfaces are
supplied, no modeled type-(iv) minimizer can occur at or above `51/50`; the
type-(iii) geometric realization is now unconditional. -/
theorem type_four_minimizer_implies_lambda_lt_51_50
    (hasEnvelope :
      LeanSuffixAnalytic.HasDescendingEqualAreaEnvelopeOnRetainedSuffix)
    (foldGapNegative : LeanSuffixAnalytic.RetainedFoldGapNegative)
    {lam : ℝ}
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    lam < (51 / 50 : ℝ) := by
  by_contra hcutoff
  have hlower : (51 / 50 : ℝ) ≤ lam := le_of_not_gt hcutoff
  by_cases hupper : lam ≤ (9 / 7 : ℝ)
  · exact (not_isWeightedPerimeterMinimizer_on_retainedSuffix
      hasEnvelope foldGapNegative ⟨hlower, hupper⟩ candidate hcandidate) hmin
  · have h9 : (9 / 7 : ℝ) < lam := lt_of_not_ge hupper
    have hsplice : (1.2581840884 : ℝ) < 9 / 7 := by norm_num
    exact cmv_type_four_not_minimizing
      (le_trans hsplice.le h9.le) candidate hcandidate hmin

/-- Under the same explicit analytic interfaces, the only remaining parameter
range for a type-(iv) minimizer is the open near-one interval. -/
theorem type_four_minimizer_open_range_51_50
    (hasEnvelope :
      LeanSuffixAnalytic.HasDescendingEqualAreaEnvelopeOnRetainedSuffix)
    (foldGapNegative : LeanSuffixAnalytic.RetainedFoldGapNegative)
    {lam : ℝ}
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hmin : candidate.IsWeightedPerimeterMinimizer) :
    1 < lam ∧ lam < (51 / 50 : ℝ) :=
  ⟨hcandidate.density_jump,
    type_four_minimizer_implies_lambda_lt_51_50
      hasEnvelope foldGapNegative candidate hcandidate hmin⟩
end CMVSuffixModel
