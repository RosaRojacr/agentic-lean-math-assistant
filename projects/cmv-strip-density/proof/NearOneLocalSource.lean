/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalHeightOrder
import NearOneFirstCellGap

namespace NearOneLocalSource

open NearOneAnalyticSystem NearOneRegularizedThirdRow.NearOneRescaledFirstCell

/-- A scale-local certificate may use any positive principal chart, not the
cusp endpoint box. The source equations, polynomial height order, and cleared
gap sign give exactly the scalar conclusion consumed by `CMVSuffixModel`.
This transport theorem alone does not certify a density slab. -/
theorem stationaryEqualAreaPair_strictImprovement
    {s z a b lam : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hy0 : 0 < yCoord s z) (hy1 : yCoord s z < 1)
    (hw0 : 0 < wCoord s a) (hw1 : wCoord s a < 1)
    (hv0 : 0 < vCoord s z a b)
    (hlam : 1 < lam) (hdensity : density s z = lam)
    (hfold : sourceFoldResidual s z Real.pi = 0)
    (hcosine : sourceCosineResidual s z a b = 0)
    (harea : sourceAreaResidual s z a b Real.pi = 0)
    (hheight : 2 < (1 - s ^ 2) * (rCoord s a) ^ 2)
    (hgap : reducedGapNumeratorBar s z a b < 0) :
    ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair lam,
      LeanSuffixAnalytic.typeThreeFold lam pair.h₃ < 0 ∧
      LeanSuffixAnalytic.typeThreePerimeter lam pair.h₃ <
        LeanSuffixAnalytic.typeFourPerimeter lam pair.h₄ := by
  subst lam
  let pair := sourceResiduals_stationaryEqualAreaPair
    hs0 hs1 hy0 hy1 hw0 hw1 hv0 hlam hfold hcosine harea
  have hA : 0 < aCoord s z := by
    change 0 < s * aCoord s z at hy0
    exact (mul_pos_iff_of_pos_left hs0).mp hy0
  have hsSq : 0 < 1 - s ^ 2 := by nlinarith
  have hden : 0 < reducedGapDenominator s z a b := by
    unfold reducedGapDenominator
    positivity
  have hsourceGap : sourceReducedGap s z a b < 0 := by
    have hprod : reducedGapDenominator s z a b * sourceReducedGap s z a b < 0 := by
      rw [reducedGap_clearing_identity (ne_of_gt hs0) (ne_of_gt hA) (ne_of_gt hsSq)]
      exact mul_neg_of_pos_of_neg (sq_pos_of_pos hs0) hgap
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hden.le (le_of_not_gt hn))) hprod
  have hscalarGap : LeanSuffixAnalytic.reducedFoldGap
      (density s z) pair.h₃ pair.h₄ < 0 := by
    change LeanSuffixAnalytic.reducedFoldGap (density s z)
      ((1 + halfCos (wCoord s a)) / 2) (halfCos s) < 0
    rw [reducedFoldGap_eq_sourceReducedGap hs0 hy0 hy1 hw0 hv0 hlam hcosine]
    exact hsourceGap
  have horder : pair.h₃ < pair.h₄ :=
    (NearOneLocalHeightOrder.height_order_iff hs0 hs1).mpr hheight
  refine ⟨pair, ?_, ?_⟩
  · exact LeanSuffixAnalytic.typeThreeFold_neg_of_equalArea_of_lt
      hlam ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
        ⟨pair.h₄_pos, pair.h₄_lt_one⟩ horder pair.equalArea
  · exact (LeanSuffixAnalytic.stationaryEqualArea_typeThree_improves_iff
      (ne_of_gt (lt_trans (by norm_num) pair.h₃_gt_half))
      (ne_of_gt pair.h₄_pos) pair.equalArea pair.stationary).2 hscalarGap

end NearOneLocalSource
