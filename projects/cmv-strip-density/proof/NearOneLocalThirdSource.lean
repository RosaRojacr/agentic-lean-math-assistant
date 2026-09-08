/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalCoordinates
import NearOneLocalCentered

/-!
# Locally grouped complete third-source reconstruction

This module gives the emitted arithmetic a small source-side target.  Subsequent
proofs connect their staged CSE blocks to `sourceGroupedThird`; they do not
unfold the complete analytic source equation.
-/

namespace NearOneLocalThirdSource

open NearOneAnalyticSystem NearOneRegularizedThirdRow
open NearOneLocalCoordinates
noncomputable section

/-- The complete source-grouped third quantity before the final scale-local
`s^2` division.  Both arctangent corrections are the actual analytic functions;
no jet coefficient or remainder is frozen as a box constant. -/
def sourceGroupedThird (s p u v w : ℝ) : ℝ :=
  NearOneNormalizedFlow.H3hatPolynomial s
      (physicalZ s p u) (physicalA s p v) (physicalB s p w) p +
    areaAngleCorrectionBar s
      (physicalZ s p u) (physicalA s p v) (physicalB s p w) +
    (4 - 2 * physicalZ s p u * s / 3) *
      foldAngleCorrectionBar s (physicalZ s p u)

/-- The grouped expression is definitionally the genuine pole-free analytic
third row at the physical atlas coordinates. -/
theorem sourceGroupedThird_eq_regularizedThirdRow (s p u v w : ℝ) :
    sourceGroupedThird s p u v w =
      regularizedThirdRow s
        (physicalZ s p u) (physicalA s p v) (physicalB s p w) p := by
  rfl

/-- Complete source identity after the final scale-local division.  The three
source guards are established before this theorem is applied in a cell. -/
theorem sourceGroupedThird_div_sq_eq_complete_div_four
    (s p u v w : ℝ) (hs : s ≠ 0)
    (hy : 1 - yCoord s (physicalZ s p u) ^ 2 ≠ 0)
    (hdFour : 1 + s * yCoord s (physicalZ s p u) ≠ 0)
    (hdThree : 1 + wCoord s (physicalA s p v) *
      vCoord s (physicalZ s p u) (physicalA s p v) (physicalB s p w) ≠ 0) :
    sourceGroupedThird s p u v w / s ^ 2 =
      completeThirdRowNumerator s
        (physicalZ s p u) (physicalA s p v) (physicalB s p w) p / s ^ 4 := by
  rw [sourceGroupedThird_eq_regularizedThirdRow]
  exact NearOneLocalTranscription.regularizedThirdRow_div_sq_eq_complete_div_four
    s (physicalZ s p u) (physicalA s p v) (physicalB s p w) p
    hs hy hdFour hdThree

end

end NearOneLocalThirdSource
