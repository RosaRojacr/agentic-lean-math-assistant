/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import TypeFourStationaryRoot
import SameCurvatureArea
import CMVSuffixModel

/-!
# Universal stationary equal-area pair

A stationary type-(iv) area is bounded by its finite value at height `1`.
That endpoint lies strictly below the type-(iii) area at height `1 / 2`, while
the same-curvature type-(iii) area at the stationary height lies strictly below
the stationary type-(iv) area.  The intermediate value theorem therefore gives
an ordered equal-area type-(iii) height.  The checked same-curvature transfer
then supplies its fold, perimeter, and reduced-gap signs.
-/

open Real
open scoped Topology

noncomputable section

namespace LeanSuffixAnalytic

/-- The type-(iii) area at the finite half-height endpoint. -/
theorem typeThreeArea_half {lam : ℝ} (hlam : 1 < lam) :
    typeThreeArea lam (1 / 2 : ℝ) = 2 * π * (lam + 1) := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hsqrt : sqrt (lam ^ 2) = lam := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hlam_pos]
  simp [typeThreeArea, typeThreeAngle, typeThreeShape, typeThreeDelta,
    hsqrt, ne_of_gt hlam_pos, Real.arccos_zero]
  ring

/-- The finite type-(iv) closure area lies strictly below the type-(iii)
half-height area for every density above one. -/
theorem typeFourArea_one_lt_typeThreeArea_half {lam : ℝ} (hlam : 1 < lam) :
    typeFourArea lam 1 < typeThreeArea lam (1 / 2 : ℝ) := by
  have hlam_pos : 0 < lam := lt_trans (by norm_num) hlam
  have hrad : 0 ≤ lam ^ 2 - 1 := by nlinarith
  have hsqrt_le_lam : sqrt (lam ^ 2 - 1) ≤ lam := by
    apply (Real.sqrt_le_iff).2
    exact ⟨hlam_pos.le, by nlinarith⟩
  have hscaled_le : lam * arccos (1 / lam) ≤ lam * π :=
    mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) hlam_pos.le
  have hangle_le : typeFourAngle lam 1 ≤ lam * π + π / 2 := by
    unfold typeFourAngle
    rw [Real.arcsin_one]
    linarith
  have hdelta_le : typeFourDelta lam 1 ≤ 1 := by
    unfold typeFourDelta
    norm_num
    exact (div_le_one hlam_pos).2 hsqrt_le_lam
  rw [typeThreeArea_half hlam]
  unfold typeFourArea
  norm_num
  nlinarith [Real.pi_gt_three]

/-- Every regular stationary type-(iv) height admits a strictly lower,
equal-area type-(iii) height above `1 / 2`. -/
theorem stationaryEqualAreaPair_of_typeFourFold_zero
    {lam h₄ : ℝ} (hlam : 1 < lam)
    (hh₄ : h₄ ∈ Set.Ioo (0 : ℝ) 1) (hh₄_half : 1 / 2 < h₄)
    (hfold : typeFourFold lam h₄ = 0) :
    ∃ pair : StationaryEqualAreaPair lam,
      pair.h₃ < pair.h₄ ∧ pair.h₄ = h₄ := by
  have hfold_le_one : typeFourArea lam h₄ ≤ typeFourArea lam 1 :=
    typeFourArea_fold_le hlam hh₄ hfold ⟨by norm_num, le_rfl⟩
  have hleft : typeFourArea lam h₄ < typeThreeArea lam (1 / 2 : ℝ) :=
    hfold_le_one.trans_lt (typeFourArea_one_lt_typeThreeArea_half hlam)
  have hright : typeThreeArea lam h₄ < typeFourArea lam h₄ :=
    typeThreeArea_lt_typeFourArea hlam hh₄.1 hh₄.2.le
  have hhalf_le : (1 / 2 : ℝ) ≤ h₄ := hh₄_half.le
  have hcont : ContinuousOn (typeThreeArea lam) (Set.Icc (1 / 2 : ℝ) h₄) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)
    unfold typeThreeArea typeThreeAngle typeThreeDelta typeThreeShape
    fun_prop (disch := simp_all)
  have htarget : typeFourArea lam h₄ ∈ Set.Icc
      (typeThreeArea lam h₄) (typeThreeArea lam (1 / 2 : ℝ)) :=
    ⟨hright.le, hleft.le⟩
  rcases intermediate_value_Icc' hhalf_le hcont htarget with
    ⟨h₃, hh₃, hequal⟩
  have hh₃_half : (1 / 2 : ℝ) < h₃ := by
    apply lt_of_le_of_ne hh₃.1
    intro heq
    subst h₃
    linarith
  have hh₃_h₄ : h₃ < h₄ := by
    apply lt_of_le_of_ne hh₃.2
    intro heq
    subst h₃
    linarith
  let pair : StationaryEqualAreaPair lam :=
    { h₃ := h₃
      h₄ := h₄
      h₃_gt_half := hh₃_half
      h₃_lt_one := hh₃_h₄.trans hh₄.2
      h₄_pos := hh₄.1
      h₄_lt_one := hh₄.2
      equalArea := hequal
      stationary := hfold }
  exact ⟨pair, hh₃_h₄, rfl⟩

/-- Every density above one has an ordered stationary equal-area pair. -/
theorem stationaryEqualAreaPair_exists {lam : ℝ} (hlam : 1 < lam) :
    ∃ pair : StationaryEqualAreaPair lam, pair.h₃ < pair.h₄ := by
  rcases typeFourFold_zero_exists hlam with ⟨h₄, hh₄_left, hh₄_one, hfold⟩
  rcases stationaryEqualAreaPair_of_typeFourFold_zero hlam
      ⟨by linarith, hh₄_one⟩ (by linarith) hfold with ⟨pair, horder, -⟩
  exact ⟨pair, horder⟩

/-- Universal source-scalar improvement at a stationary equal-area pair:
negative type-(iii) fold, strict perimeter decrease, and negative reduced gap. -/
theorem stationaryEqualAreaPair_strictImprovement_exists
    {lam : ℝ} (hlam : 1 < lam) :
    ∃ pair : StationaryEqualAreaPair lam,
      typeThreeFold lam pair.h₃ < 0 ∧
      typeThreePerimeter lam pair.h₃ < typeFourPerimeter lam pair.h₄ ∧
      reducedFoldGap lam pair.h₃ pair.h₄ < 0 := by
  rcases stationaryEqualAreaPair_exists hlam with ⟨pair, horder⟩
  have hfoldThree : typeThreeFold lam pair.h₃ < 0 :=
    typeThreeFold_neg_of_equalArea_of_lt hlam
      ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
      ⟨pair.h₄_pos, pair.h₄_lt_one⟩ horder pair.equalArea
  have hperimeter :
      typeThreePerimeter lam pair.h₃ < typeFourPerimeter lam pair.h₄ :=
    typeThreePerimeter_lt_typeFourPerimeter_of_equalArea hlam
      pair.h₃_gt_half horder pair.h₄_lt_one pair.equalArea
  have hgap : reducedFoldGap lam pair.h₃ pair.h₄ < 0 :=
    (stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) pair.h₃_gt_half))
      (ne_of_gt pair.h₄_pos) pair.equalArea pair.stationary).1 hperimeter
  exact ⟨pair, hfoldThree, hperimeter, hgap⟩

end LeanSuffixAnalytic

namespace CMVSuffixModel.FourArcCandidate

variable {lam : ℝ} (candidate : _root_.FourArcCandidate lam)

/-- The universal stationary pair excludes every modeled type-(iv) candidate
at every density above one.  Source classification and model compatibility
remain separate obligations. -/
theorem not_isWeightedPerimeterMinimizer_of_density_gt_one
    (hlam : 1 < lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases
      LeanSuffixAnalytic.stationaryEqualAreaPair_strictImprovement_exists hlam with
    ⟨pair, hfoldThree, hperimeter, -⟩
  exact not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair candidate
    hcandidate pair hfoldThree hperimeter

/-- Explicit contiguous modeled exclusion through the previously retained
near-one endpoint.  The proof is a direct specialization of the stronger
all-density theorem. -/
theorem not_isWeightedPerimeterMinimizer_through_1001_1000
    (hlam : 1 < lam) (_hlam_upper : lam ≤ 1001 / 1000)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  not_isWeightedPerimeterMinimizer_of_density_gt_one candidate hlam hcandidate

/-- Candidate exclusion on the first complete closed slab retained by the
scale-local atlas pilot.  The stronger universal theorem makes the pilot's
numerical face certificates unnecessary for this modeled conclusion. -/
theorem not_isWeightedPerimeterMinimizer_on_atlas_seam_slab
    (hlam :
      lam - 1 ∈ Set.Icc
        (251 / 40326519148554080 : ℝ)
        (251 / 5040814893569260 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  apply not_isWeightedPerimeterMinimizer_of_density_gt_one candidate
  · have hdelta : (0 : ℝ) < 251 / 40326519148554080 := by norm_num
    linarith [hlam.1]
  · exact hcandidate

/-- Candidate exclusion on the remote complete closed slab retained by the
scale-local atlas pilot.  This is also a direct specialization of the
all-density modeled theorem. -/
theorem not_isWeightedPerimeterMinimizer_on_atlas_remote_slab
    (hlam : lam - 1 ∈ Set.Icc (1 / 1000 : ℝ) (1 / 500 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  apply not_isWeightedPerimeterMinimizer_of_density_gt_one candidate
  · have hdelta : (0 : ℝ) < 1 / 1000 := by norm_num
    linarith [hlam.1]
  · exact hcandidate

end CMVSuffixModel.FourArcCandidate
