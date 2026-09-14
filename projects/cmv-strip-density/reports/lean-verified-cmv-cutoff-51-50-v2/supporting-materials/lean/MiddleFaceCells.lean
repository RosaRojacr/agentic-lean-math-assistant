/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import ScalarSuffixCertificate
import RightPrototypeCell
import MiddleFaceCells0To19
import MiddleFaceCells20To31
import MiddleFaceCells32To43
import MiddleFaceCells44To55
import MiddleFaceCells56To67
import MiddleFaceCells68To79
import MiddleFaceCells80To91
import MiddleFaceCells92To103
import MiddleFaceCells104To112

/-!
# All middle-face cells

Branch-complete candidate exclusion over the closed union of all 113 exact
inventory bricks `B0000` through `B0112`, composed from balanced batch aggregates.
-/

noncomputable section

namespace MiddleFaceCells

/-- Every modeled type-(iv) candidate in the closed union of all middle-face
bricks `B0000` through `B0112` fails weighted-perimeter minimality. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ}
    (hlower : (102001 / 100000 : ℝ) ≤ lam)
    (hupper : lam ≤ (25781 / 25000 : ℝ))
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  by_cases hbatch₀ : lam ≤ (102201 / 100000 : ℝ)
  · exact
      MiddleFaceCells0To19.candidate_not_isWeightedPerimeterMinimizer
        hlower hbatch₀ candidate hcandidate
  · by_cases hbatch₁ : lam ≤ (102321 / 100000 : ℝ)
    · exact
        MiddleFaceCells20To31.candidate_not_isWeightedPerimeterMinimizer
          (not_le.mp hbatch₀).le hbatch₁ candidate hcandidate
    · by_cases hbatch₂ : lam ≤ (102441 / 100000 : ℝ)
      · exact
          MiddleFaceCells32To43.candidate_not_isWeightedPerimeterMinimizer
            (not_le.mp hbatch₁).le hbatch₂ candidate hcandidate
      · by_cases hbatch₃ : lam ≤ (102561 / 100000 : ℝ)
        · exact
            MiddleFaceCells44To55.candidate_not_isWeightedPerimeterMinimizer
              (not_le.mp hbatch₂).le hbatch₃ candidate hcandidate
        · by_cases hbatch₄ : lam ≤ (102681 / 100000 : ℝ)
          · exact
              MiddleFaceCells56To67.candidate_not_isWeightedPerimeterMinimizer
                (not_le.mp hbatch₃).le hbatch₄ candidate hcandidate
          · by_cases hbatch₅ : lam ≤ (102801 / 100000 : ℝ)
            · exact
                MiddleFaceCells68To79.candidate_not_isWeightedPerimeterMinimizer
                  (not_le.mp hbatch₄).le hbatch₅ candidate hcandidate
            · by_cases hbatch₆ : lam ≤ (102921 / 100000 : ℝ)
              · exact
                  MiddleFaceCells80To91.candidate_not_isWeightedPerimeterMinimizer
                    (not_le.mp hbatch₅).le hbatch₆ candidate hcandidate
              · by_cases hbatch₇ : lam ≤ (103041 / 100000 : ℝ)
                · exact
                    MiddleFaceCells92To103.candidate_not_isWeightedPerimeterMinimizer
                      (not_le.mp hbatch₆).le hbatch₇ candidate hcandidate
                · exact
                    MiddleFaceCells104To112.candidate_not_isWeightedPerimeterMinimizer
                      (not_le.mp hbatch₇).le hupper candidate hcandidate

/-- Every modeled type-(iv) candidate in both retained prototypes and all 113
middle-face bricks fails weighted-perimeter minimality. The closed interval
includes both exact prototype seams and reaches `33 / 32`. -/
theorem candidate_not_isWeightedPerimeterMinimizer_from_51_50
    {lam : ℝ}
    (hlower : (51 / 50 : ℝ) ≤ lam)
    (hupper : lam ≤ (33 / 32 : ℝ))
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  by_cases hp : lam ≤ (102001 / 100000 : ℝ)
  · have hcell :
        ScalarSuffixCertificate.FirstPrototypeCell.lamInterval.RealContains lam := by
      norm_num [ScalarSuffixCertificate.FirstPrototypeCell.lamInterval,
        ScalarSuffixCertificate.FirstPrototypeCell.brick,
        LeanSuffixReflective.QInterval.RealContains] at hlower hp ⊢
      exact ⟨hlower, hp⟩
    exact
      ScalarSuffixCertificate.FirstPrototypeCell.candidate_not_isWeightedPerimeterMinimizer
        hcell candidate hcandidate
  · by_cases hm : lam ≤ (25781 / 25000 : ℝ)
    · exact candidate_not_isWeightedPerimeterMinimizer (not_le.mp hp).le hm
        candidate hcandidate
    · have hcell : RightPrototypeCell.lamInterval.RealContains lam := by
        norm_num [RightPrototypeCell.lamInterval, RightPrototypeCell.brick,
          LeanSuffixReflective.QInterval.RealContains] at hm hupper ⊢
        exact ⟨hm.le, hupper⟩
      exact RightPrototypeCell.candidate_not_isWeightedPerimeterMinimizer
        hcell candidate hcandidate

end MiddleFaceCells
