/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneLocalThirdSource
import NearOneAtanRemainder

/-!
# Four-remainder source decomposition for the scale-local atlas

This module rewrites the actual grouped third source in terms of the four
`atanRemainder 3` values used by the source.  The remainder values stay as
independent scalar parameters until the final exact specialization; no analytic
remainder is frozen or expanded into a multivariate polynomial.
-/

namespace NearOneLocalFourRemainder

open NearOneAnalyticSystem NearOneRegularizedThirdRow
open NearOneLocalCoordinates NearOneLocalThirdSource
set_option maxRecDepth 10000
noncomputable section

/-- The type-(iv) principal-angle addition argument. -/
def fourIncrementArgument (s z : ℝ) : ℝ :=
  s ^ 2 * z / (1 + s * yCoord s z)

/-- The type-(iii) principal-angle addition argument. -/
def threeIncrementArgument (s z a b : ℝ) : ℝ :=
  s ^ 2 * eCoord s z a b /
    (1 + wCoord s a * vCoord s z a b)

/-- The exact low-order quotient with its order-three remainder exposed. -/
def atanQuotientWithRemainder (x remainder : ℝ) : ℝ :=
  1 - x ^ 2 / 3 + x ^ 4 / 5 + x ^ 6 * remainder

/-- The exact low-order square remainder with its order-three remainder exposed. -/
def atanSqRemainderWithRemainder (x remainder : ℝ) : ℝ :=
  -(1 / 3 : ℝ) + x ^ 2 / 5 + x ^ 4 * remainder

@[simp] theorem atanQuotientWithRemainder_actual (x : ℝ) :
    atanQuotientWithRemainder x (NearOneAtanRemainder.atanRemainder 3 x) =
      atanQuotient x := by
  exact (NearOneLocalTranscription.atanQuotient_eq_orderSix x).symm

@[simp] theorem atanSqRemainderWithRemainder_actual (x : ℝ) :
    atanSqRemainderWithRemainder x
        (NearOneAtanRemainder.atanRemainder 3 x) =
      atanQuotientSqRemainder x := by
  exact (NearOneLocalTranscription.atanQuotientSqRemainder_eq_orderFour x).symm

/-- Source type-(iv) angle increment with only its scalar remainder exposed. -/
def typeFourAngleIncrementWithRemainder (s z remainderFour : ℝ) : ℝ :=
  2 * z / (1 + s * yCoord s z) *
    atanQuotientWithRemainder (fourIncrementArgument s z) remainderFour

/-- Source type-(iii) angle increment with only its scalar remainder exposed. -/
def typeThreeAngleIncrementWithRemainder
    (s z a b remainderThree : ℝ) : ℝ :=
  2 * eCoord s z a b / (1 + wCoord s a * vCoord s z a b) *
    atanQuotientWithRemainder (threeIncrementArgument s z a b) remainderThree

/-- The normalized type-(iv) angle block, sharing the actual scale and
principal-angle remainders with the regularized area row. -/
def typeFourAngleBarWithRemainders
    (s z remainderScale remainderFour : ℝ) : ℝ :=
  2 * s * densityCubeQuotient s z *
      (s * atanQuotientWithRemainder s remainderScale) +
    density s z * typeFourAngleIncrementWithRemainder s z remainderFour

/-- The regularized type-(iv) angle block with its two remainders exposed. -/
def typeFourAngleBar2WithRemainders
    (s z remainderScale remainderFour : ℝ) : ℝ :=
  2 * densityCubeQuotient s z *
      atanQuotientWithRemainder s remainderScale +
    density s z *
      (2 * z / (1 + s * yCoord s z) *
        (s ^ 2 * z ^ 2 / (1 + s * yCoord s z) ^ 2 *
            atanSqRemainderWithRemainder (fourIncrementArgument s z)
              remainderFour -
          aCoord s z)) +
    2 * s * z * densityCubeQuotient s z

/-- The regularized type-(iii) angle block with its two remainders exposed. -/
def typeThreeAngleBar2WithRemainders
    (s z a b remainderLower remainderThree : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * rCoord s a *
      atanQuotientWithRemainder (wCoord s a) remainderLower +
    density s z *
      (2 * eCoord s z a b /
          (1 + wCoord s a * vCoord s z a b) *
        (s ^ 2 * eCoord s z a b ^ 2 /
              (1 + wCoord s a * vCoord s z a b) ^ 2 *
            atanSqRemainderWithRemainder
              (threeIncrementArgument s z a b) remainderThree -
          rCoord s a * (rCoord s a + s * eCoord s z a b))) +
    2 * s * eCoord s z a b * densityCubeQuotient s z

/-- Cancellation-free fold correction.  The positive quadratic denominators in
`foldDenominator * typeFourSineProductBar` have already cancelled exactly. -/
def foldCorrectionWithRemainders
    (s z remainderScale remainderFour : ℝ) : ℝ :=
  -8 * (1 + s ^ 2) * aCoord s z *
    typeFourAngleBarWithRemainders s z remainderScale remainderFour

/-- Cancellation-free area correction.  All `1+x^2` denominators have already
cancelled against `areaDenominator`; only the density and angle-addition
denominators remain. -/
def areaCorrectionWithRemainders
    (s z a b remainderScale remainderLower remainderFour remainderThree : ℝ) : ℝ :=
  4 * (1 + wCoord s a ^ 2) ^ 2 * (1 + yCoord s z ^ 2) *
      (1 + vCoord s z a b ^ 2) * (1 - s ^ 2) ^ 2 *
      typeThreeAngleBar2WithRemainders s z a b remainderLower remainderThree -
    8 * (1 + s ^ 2) ^ 2 * (1 + yCoord s z ^ 2) *
      (1 + vCoord s z a b ^ 2) *
      typeFourAngleBar2WithRemainders s z remainderScale remainderFour +
    16 * z * (NearOneNormalizedFlow.K a).eval s *
      (1 + yCoord s z ^ 2) * (1 + vCoord s z a b ^ 2)

/-- The complete local third source with exactly four scalar remainder slots:
`R3(s)`, `R3(W)`, `R3(q4)`, and `R3(q3)`, in that order. -/
def sourceGroupedThirdWithRemainders
    (s p u v w remainderScale remainderLower remainderFour remainderThree : ℝ) : ℝ :=
  let z := physicalZ s p u
  let a := physicalA s p v
  let b := physicalB s p w
  NearOneNormalizedFlow.H3hatPolynomial s z a b p +
    areaCorrectionWithRemainders s z a b
      remainderScale remainderLower remainderFour remainderThree +
    (4 - 2 * z * s / 3) *
      foldCorrectionWithRemainders s z remainderScale remainderFour

private theorem typeFourAngleBarWithRemainders_actual (s z : ℝ) :
    typeFourAngleBarWithRemainders s z
        (NearOneAtanRemainder.atanRemainder 3 s)
        (NearOneAtanRemainder.atanRemainder 3 (fourIncrementArgument s z)) =
      typeFourAngleBar s z := by
  simp only [typeFourAngleBarWithRemainders, typeFourAngleIncrementWithRemainder,
    atanQuotientWithRemainder_actual, fourIncrementArgument,
    typeFourAngleBar, typeFourAngleIncrement, mul_atanQuotient]

private theorem typeFourAngleBar2WithRemainders_actual (s z : ℝ) :
    typeFourAngleBar2WithRemainders s z
        (NearOneAtanRemainder.atanRemainder 3 s)
        (NearOneAtanRemainder.atanRemainder 3 (fourIncrementArgument s z)) =
      typeFourAngleBar2 s z := by
  simp only [typeFourAngleBar2WithRemainders, typeFourAngleBar2,
    typeFourAngleIncrementBar2, atanQuotientWithRemainder_actual,
    atanSqRemainderWithRemainder_actual, fourIncrementArgument]

private theorem typeThreeAngleBar2WithRemainders_actual (s z a b : ℝ) :
    typeThreeAngleBar2WithRemainders s z a b
        (NearOneAtanRemainder.atanRemainder 3 (wCoord s a))
        (NearOneAtanRemainder.atanRemainder 3
          (threeIncrementArgument s z a b)) =
      typeThreeAngleBar2 s z a b := by
  simp only [typeThreeAngleBar2WithRemainders, typeThreeAngleBar2,
    typeThreeAngleIncrementBar2, atanQuotientWithRemainder_actual,
    atanSqRemainderWithRemainder_actual, threeIncrementArgument]

private theorem foldCorrectionWithRemainders_actual (s z : ℝ) :
    foldCorrectionWithRemainders s z
        (NearOneAtanRemainder.atanRemainder 3 s)
        (NearOneAtanRemainder.atanRemainder 3 (fourIncrementArgument s z)) =
      foldAngleCorrectionBar s z := by
  rw [foldCorrectionWithRemainders, typeFourAngleBarWithRemainders_actual]
  simp only [foldAngleCorrectionBar, foldDenominator, typeFourSineProductBar]
  field_simp [show 1 + s ^ 2 ≠ 0 by positivity,
    show 1 + yCoord s z ^ 2 ≠ 0 by positivity]
  ring

private theorem areaCorrectionWithRemainders_actual (s z a b : ℝ) :
    areaCorrectionWithRemainders s z a b
        (NearOneAtanRemainder.atanRemainder 3 s)
        (NearOneAtanRemainder.atanRemainder 3 (wCoord s a))
        (NearOneAtanRemainder.atanRemainder 3 (fourIncrementArgument s z))
        (NearOneAtanRemainder.atanRemainder 3
          (threeIncrementArgument s z a b)) =
      areaAngleCorrectionBar s z a b := by
  rw [areaCorrectionWithRemainders, typeFourAngleBar2WithRemainders_actual,
    typeThreeAngleBar2WithRemainders_actual]
  simp only [areaAngleCorrectionBar, areaDenominator, areaPiWeight, halfCos]
  field_simp [show 1 + s ^ 2 ≠ 0 by positivity,
    show 1 + wCoord s a ^ 2 ≠ 0 by positivity]
  ring

/-- Exact source-to-four-remainder identity.  This is the analytic boundary for
the polynomial face replay; each displayed `atanRemainder 3` remains actual. -/
theorem sourceGroupedThird_eq_fourRemainderExpansion (s p u v w : ℝ) :
    sourceGroupedThird s p u v w =
      sourceGroupedThirdWithRemainders s p u v w
        (NearOneAtanRemainder.atanRemainder 3 s)
        (NearOneAtanRemainder.atanRemainder 3
          (wCoord s (physicalA s p v)))
        (NearOneAtanRemainder.atanRemainder 3
          (fourIncrementArgument s (physicalZ s p u)))
        (NearOneAtanRemainder.atanRemainder 3
          (threeIncrementArgument s (physicalZ s p u)
            (physicalA s p v) (physicalB s p w))) := by
  rw [sourceGroupedThird, sourceGroupedThirdWithRemainders]
  rw [areaCorrectionWithRemainders_actual, foldCorrectionWithRemainders_actual]

/-- Coefficient of the actual `R3(s)` slot. -/
def sourceScaleRemainderCoefficient (s p u v w : ℝ) : ℝ :=
  sourceGroupedThirdWithRemainders s p u v w 1 0 0 0 -
    sourceGroupedThirdWithRemainders s p u v w 0 0 0 0

/-- Coefficient of the actual `R3(W)` slot. -/
def sourceLowerRemainderCoefficient (s p u v w : ℝ) : ℝ :=
  sourceGroupedThirdWithRemainders s p u v w 0 1 0 0 -
    sourceGroupedThirdWithRemainders s p u v w 0 0 0 0

/-- Coefficient of the actual `R3(q4)` slot. -/
def sourceFourRemainderCoefficient (s p u v w : ℝ) : ℝ :=
  sourceGroupedThirdWithRemainders s p u v w 0 0 1 0 -
    sourceGroupedThirdWithRemainders s p u v w 0 0 0 0

/-- Coefficient of the actual `R3(q3)` slot. -/
def sourceThreeRemainderCoefficient (s p u v w : ℝ) : ℝ :=
  sourceGroupedThirdWithRemainders s p u v w 0 0 0 1 -
    sourceGroupedThirdWithRemainders s p u v w 0 0 0 0

/-- The parameterized source is jointly affine in the four remainder slots. -/
theorem sourceGroupedThirdWithRemainders_affine
    (s p u v w rScale rLower rFour rThree : ℝ) :
    sourceGroupedThirdWithRemainders s p u v w rScale rLower rFour rThree =
      sourceGroupedThirdWithRemainders s p u v w 0 0 0 0 +
        sourceScaleRemainderCoefficient s p u v w * rScale +
        sourceLowerRemainderCoefficient s p u v w * rLower +
        sourceFourRemainderCoefficient s p u v w * rFour +
        sourceThreeRemainderCoefficient s p u v w * rThree := by
  simp only [sourceScaleRemainderCoefficient, sourceLowerRemainderCoefficient,
    sourceFourRemainderCoefficient, sourceThreeRemainderCoefficient,
    sourceGroupedThirdWithRemainders, areaCorrectionWithRemainders,
    foldCorrectionWithRemainders, typeFourAngleBarWithRemainders,
    typeFourAngleBar2WithRemainders, typeThreeAngleBar2WithRemainders,
    typeFourAngleIncrementWithRemainder,
    atanQuotientWithRemainder, atanSqRemainderWithRemainder]
  ring_nf

/-- Exact midpoint-plus-error decomposition used by each face certificate. -/
theorem sourceGroupedThirdWithRemainders_centered
    (s p u v w mScale mLower mFour mThree
      eScale eLower eFour eThree : ℝ) :
    sourceGroupedThirdWithRemainders s p u v w
        (mScale + eScale) (mLower + eLower)
        (mFour + eFour) (mThree + eThree) =
      sourceGroupedThirdWithRemainders s p u v w
          mScale mLower mFour mThree +
        sourceScaleRemainderCoefficient s p u v w * eScale +
        sourceLowerRemainderCoefficient s p u v w * eLower +
        sourceFourRemainderCoefficient s p u v w * eFour +
        sourceThreeRemainderCoefficient s p u v w * eThree := by
  calc
    sourceGroupedThirdWithRemainders s p u v w
        (mScale + eScale) (mLower + eLower)
        (mFour + eFour) (mThree + eThree) =
      sourceGroupedThirdWithRemainders s p u v w 0 0 0 0 +
        sourceScaleRemainderCoefficient s p u v w * (mScale + eScale) +
        sourceLowerRemainderCoefficient s p u v w * (mLower + eLower) +
        sourceFourRemainderCoefficient s p u v w * (mFour + eFour) +
        sourceThreeRemainderCoefficient s p u v w * (mThree + eThree) :=
      sourceGroupedThirdWithRemainders_affine _ _ _ _ _ _ _ _ _
    _ = (sourceGroupedThirdWithRemainders s p u v w 0 0 0 0 +
          sourceScaleRemainderCoefficient s p u v w * mScale +
          sourceLowerRemainderCoefficient s p u v w * mLower +
          sourceFourRemainderCoefficient s p u v w * mFour +
          sourceThreeRemainderCoefficient s p u v w * mThree) +
        sourceScaleRemainderCoefficient s p u v w * eScale +
        sourceLowerRemainderCoefficient s p u v w * eLower +
        sourceFourRemainderCoefficient s p u v w * eFour +
        sourceThreeRemainderCoefficient s p u v w * eThree := by ring
    _ = _ := by
      rw [← sourceGroupedThirdWithRemainders_affine]

/-- Exact source-to-midpoint-plus-error identity.  The four error terms are the
actual analytic remainders minus arbitrary rational midpoints; no remainder is
replaced by a constant. -/
theorem sourceGroupedThird_eq_centeredRemainderExpansion
    (s p u v w mScale mLower mFour mThree : ℝ) :
    sourceGroupedThird s p u v w =
      sourceGroupedThirdWithRemainders s p u v w
          mScale mLower mFour mThree +
        sourceScaleRemainderCoefficient s p u v w *
          (NearOneAtanRemainder.atanRemainder 3 s - mScale) +
        sourceLowerRemainderCoefficient s p u v w *
          (NearOneAtanRemainder.atanRemainder 3
            (wCoord s (physicalA s p v)) - mLower) +
        sourceFourRemainderCoefficient s p u v w *
          (NearOneAtanRemainder.atanRemainder 3
            (fourIncrementArgument s (physicalZ s p u)) - mFour) +
        sourceThreeRemainderCoefficient s p u v w *
          (NearOneAtanRemainder.atanRemainder 3
            (threeIncrementArgument s (physicalZ s p u)
              (physicalA s p v) (physicalB s p w)) - mThree) := by
  rw [sourceGroupedThird_eq_fourRemainderExpansion]
  convert sourceGroupedThirdWithRemainders_centered
    s p u v w mScale mLower mFour mThree
    (NearOneAtanRemainder.atanRemainder 3 s - mScale)
    (NearOneAtanRemainder.atanRemainder 3
      (wCoord s (physicalA s p v)) - mLower)
    (NearOneAtanRemainder.atanRemainder 3
      (fourIncrementArgument s (physicalZ s p u)) - mFour)
    (NearOneAtanRemainder.atanRemainder 3
      (threeIncrementArgument s (physicalZ s p u)
        (physicalA s p v) (physicalB s p w)) - mThree) using 1
  all_goals ring_nf

/-- Common source clearing factor selected for every preconditioned row.  Its
nonconstant factors are exactly the density denominator and the seventh powers
of the two angle-addition denominators. -/
def sourceClearingFactor (s z a b : ℝ) : ℝ :=
  (1 + s ^ 2) * (1 - yCoord s z ^ 2) *
    (1 + s * yCoord s z) ^ 7 *
    (1 + wCoord s a * vCoord s z a b) ^ 7

/-- The selected common clearing factor is strictly positive under the three
source denominator certificates. -/
theorem sourceClearingFactor_pos {s z a b : ℝ}
    (hDensity : 0 < 1 - yCoord s z ^ 2)
    (hFour : 0 < 1 + s * yCoord s z)
    (hThree : 0 < 1 + wCoord s a * vCoord s z a b) :
    0 < sourceClearingFactor s z a b := by
  unfold sourceClearingFactor
  positivity

end

end NearOneLocalFourRemainder
