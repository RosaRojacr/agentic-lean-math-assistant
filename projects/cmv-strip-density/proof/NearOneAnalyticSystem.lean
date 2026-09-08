/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneNormalizedFlow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Honest analytic rows for the near-one half-angle chart

This module connects the half-angle analytic system to the polynomial pieces in
`NearOneNormalizedFlow`.  It keeps the removable angle quotients explicit.  In
particular, `NearOneNormalizedFlow.H1` and `NearOneNormalizedFlow.H3` are only
the algebraic parts of the complete cleared rows; the theorems below state the
missing angle corrections exactly.  `NearOneNormalizedFlow.H2` is the complete
cleared cosine row.
-/

namespace NearOneAnalyticSystem

open NearOneNormalizedFlow Polynomial Real

noncomputable section
set_option maxRecDepth 10000

/-- The removable quotient `arctan x / x`, with its continuous value at zero. -/
def atanQuotient (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.arctan x / x

@[simp] theorem mul_atanQuotient (x : ℝ) :
    x * atanQuotient x = Real.arctan x := by
  by_cases hx : x = 0
  · simp [atanQuotient, hx]
  · rw [atanQuotient, if_neg hx]
    field_simp

/-- Sine in tangent-half-angle coordinates. -/
def halfSin (x : ℝ) : ℝ := 2 * x / (1 + x ^ 2)

/-- Principal angle represented by a tangent-half-angle coordinate. -/
def halfAngle (x : ℝ) : ℝ := 2 * Real.arctan x

/-- Principal angle increment from tangent coordinates `p` to `q`. -/
def principalAngleIncrement (p q : ℝ) : ℝ :=
  let r := (q - p) / (1 + p * q)
  2 * r * atanQuotient r

/-- The quotient expression is the principal angle difference whenever the
usual arctangent addition guard holds. -/
theorem principalAngleIncrement_eq_sub (p q : ℝ)
    (hden : 1 + p * q ≠ 0)
    (hadd : p * ((q - p) / (1 + p * q)) < 1) :
    principalAngleIncrement p q = halfAngle q - halfAngle p := by
  let r := (q - p) / (1 + p * q)
  have hp : 1 + p ^ 2 ≠ 0 := by positivity
  have hrden : 1 - p * r ≠ 0 := by
    rw [show 1 - p * r = (1 + p ^ 2) / (1 + p * q) by
      dsimp [r]
      field_simp [hden]
      ring]
    exact div_ne_zero hp hden
  have hr : (p + r) / (1 - p * r) = q := by
    apply (div_eq_iff hrden).2
    dsimp [r]
    field_simp [hden]
    ring
  have ha := Real.arctan_add (x := p) (y := r) hadd
  rw [hr] at ha
  rw [principalAngleIncrement, halfAngle]
  change 2 * r * atanQuotient r =
    2 * Real.arctan q - 2 * Real.arctan p
  rw [mul_assoc, mul_atanQuotient]
  linarith
/-- Cosine in tangent-half-angle coordinates. -/
def halfCos (x : ℝ) : ℝ := (1 - x ^ 2) / (1 + x ^ 2)

/-- `A = 1 + s z`. -/
def aCoord (s z : ℝ) : ℝ := 1 + s * z

/-- `R = 2 + s a`. -/
def rCoord (s a : ℝ) : ℝ := 2 + s * a

/-- The undoubled third-angle increment `e = 6a - 2z + sb`. -/
def eCoord (s z a b : ℝ) : ℝ := 6 * a - 2 * z + s * b

/-- Type-(iv) upper tangent coordinate `Y = sA`. -/
def yCoord (s z : ℝ) : ℝ := s * aCoord s z

/-- Type-(iii) lower tangent coordinate `W = sR`. -/
def wCoord (s a : ℝ) : ℝ := s * rCoord s a

/-- Type-(iii) upper tangent coordinate `V = s(R + se)`. -/
def vCoord (s z a b : ℝ) : ℝ :=
  s * (rCoord s a + s * eCoord s z a b)

/-- Density obtained from the type-(iv) incidence equation. -/
def density (s z : ℝ) : ℝ := halfCos s / halfCos (yCoord s z)

/-- Cancellation-free expression for `(density s z - 1) / s³`. -/
def densityCubeQuotient (s z : ℝ) : ℝ :=
  2 * z * (2 + s * z) /
    ((1 + s ^ 2) * (1 - yCoord s z ^ 2))
private theorem one_add_sq_ne_zero (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity

/-- The rational density quotient is exactly `(lambda - 1) / s³` away from
the type-(iv) cosine denominator. -/
theorem density_sub_one_eq_cube_mul (s z : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0) :
    density s z - 1 = s ^ 3 * densityCubeQuotient s z := by
  rw [density, densityCubeQuotient, halfCos, halfCos]
  field_simp [one_add_sq_ne_zero, hy]
  simp [yCoord, aCoord]
  ring

/-- Principal type-(iv) angle increment divided by `s²`. -/
def typeFourAngleIncrement (s z : ℝ) : ℝ :=
  let q := s ^ 2 * z / (1 + s * yCoord s z)
  2 * z / (1 + s * yCoord s z) * atanQuotient q

/-- Principal type-(iii) angle increment divided by `s²`. -/
def typeThreeAngleIncrement (s z a b : ℝ) : ℝ :=
  let e := eCoord s z a b
  let q := s ^ 2 * e / (1 + wCoord s a * vCoord s z a b)
  2 * e / (1 + wCoord s a * vCoord s z a b) * atanQuotient q

/-- `(B₄ - pi/2) / s²`, expressed without division by `s`. -/
def typeFourAngleBar (s z : ℝ) : ℝ :=
  2 * s * densityCubeQuotient s z * Real.arctan s +
    density s z * typeFourAngleIncrement s z

/-- `(B₃ - pi) / s²`, expressed without division by `s`. -/
def typeThreeAngleBar (s z a b : ℝ) : ℝ :=
  2 * s * densityCubeQuotient s z * Real.arctan (wCoord s a) +
    density s z * typeThreeAngleIncrement s z a b

/-- The type-(iv) increment is exactly the principal angle increment divided by
`s²`; the identity remains meaningful at `s = 0`. -/
theorem sq_mul_typeFourAngleIncrement (s z : ℝ)
    (hden : 1 + s * yCoord s z ≠ 0) :
    s ^ 2 * typeFourAngleIncrement s z =
      principalAngleIncrement s (yCoord s z) := by
  have hdiff : yCoord s z - s = s ^ 2 * z := by
    simp [yCoord, aCoord]
    ring
  have hq : (yCoord s z - s) / (1 + s * yCoord s z) =
      s ^ 2 * z / (1 + s * yCoord s z) := by rw [hdiff]
  rw [principalAngleIncrement]
  simp only [hq, typeFourAngleIncrement]
  field_simp [hden]

/-- The type-(iii) increment is exactly the principal angle increment divided
by `s²`; the identity remains meaningful at `s = 0`. -/
theorem sq_mul_typeThreeAngleIncrement (s z a b : ℝ)
    (hden : 1 + wCoord s a * vCoord s z a b ≠ 0) :
    s ^ 2 * typeThreeAngleIncrement s z a b =
      principalAngleIncrement (wCoord s a) (vCoord s z a b) := by
  have hdiff : vCoord s z a b - wCoord s a =
      s ^ 2 * eCoord s z a b := by
    simp [vCoord, wCoord]
    ring
  have hq : (vCoord s z a b - wCoord s a) /
      (1 + wCoord s a * vCoord s z a b) =
      s ^ 2 * eCoord s z a b /
        (1 + wCoord s a * vCoord s z a b) := by rw [hdiff]
  rw [principalAngleIncrement]
  simp only [hq, typeThreeAngleIncrement]
  field_simp [hden]

/-- Source type-(iv) angle block in principal half-angle coordinates. -/
def sourceTypeFourAngleBlock (s z pi : ℝ) : ℝ :=
  density s z * halfAngle (yCoord s z) + pi / 2 - halfAngle s

/-- Source type-(iii) angle block in principal half-angle coordinates. -/
def sourceTypeThreeAngleBlock (s z a b pi : ℝ) : ℝ :=
  density s z * halfAngle (vCoord s z a b) + pi - halfAngle (wCoord s a)

/-- The cancellation-free type-(iv) angle bar reconstructs the source block. -/
theorem typeFourAngleBlock_eq_source (s z pi : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hden : 1 + s * yCoord s z ≠ 0)
    (hadd : s * ((yCoord s z - s) / (1 + s * yCoord s z)) < 1) :
    pi / 2 + s ^ 2 * typeFourAngleBar s z =
      sourceTypeFourAngleBlock s z pi := by
  have hinc := sq_mul_typeFourAngleIncrement s z hden
  rw [principalAngleIncrement_eq_sub s (yCoord s z) hden hadd] at hinc
  have hlam := density_sub_one_eq_cube_mul s z hy
  simp only [typeFourAngleBar, sourceTypeFourAngleBlock]
  rw [show s ^ 2 *
      (2 * s * densityCubeQuotient s z * Real.arctan s +
        density s z * typeFourAngleIncrement s z) =
      2 * s ^ 3 * densityCubeQuotient s z * Real.arctan s +
        density s z * (s ^ 2 * typeFourAngleIncrement s z) by ring, hinc]
  simp only [halfAngle]
  have hscaled := congrArg
    (fun x : ℝ => x * (2 * Real.arctan s)) hlam
  ring_nf at hscaled ⊢
  linarith

/-- The cancellation-free type-(iii) angle bar reconstructs the source block. -/
theorem typeThreeAngleBlock_eq_source (s z a b pi : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hden : 1 + wCoord s a * vCoord s z a b ≠ 0)
    (hadd : wCoord s a *
      ((vCoord s z a b - wCoord s a) /
        (1 + wCoord s a * vCoord s z a b)) < 1) :
    pi + s ^ 2 * typeThreeAngleBar s z a b =
      sourceTypeThreeAngleBlock s z a b pi := by
  have hinc := sq_mul_typeThreeAngleIncrement s z a b hden
  rw [principalAngleIncrement_eq_sub (wCoord s a) (vCoord s z a b)
    hden hadd] at hinc
  have hlam := density_sub_one_eq_cube_mul s z hy
  simp only [typeThreeAngleBar, sourceTypeThreeAngleBlock]
  rw [show s ^ 2 *
      (2 * s * densityCubeQuotient s z * Real.arctan (wCoord s a) +
        density s z * typeThreeAngleIncrement s z a b) =
      2 * s ^ 3 * densityCubeQuotient s z * Real.arctan (wCoord s a) +
        density s z * (s ^ 2 * typeThreeAngleIncrement s z a b) by ring, hinc]
  simp only [halfAngle]
  have hscaled := congrArg
    (fun x : ℝ => x * (2 * Real.arctan (wCoord s a))) hlam
  ring_nf at hscaled ⊢
  linarith
/-- The type-(iv) sine increment divided by `s²`. -/
def typeFourSineBar (s z : ℝ) : ℝ :=
  2 * z * (1 - s * yCoord s z) /
    ((1 + s ^ 2) * (1 + yCoord s z ^ 2))

/-- The type-(iii) sine increment divided by `s²`. -/
def typeThreeSineBar (s z a b : ℝ) : ℝ :=
  let e := eCoord s z a b
  2 * e * (1 - wCoord s a * vCoord s z a b) /
    ((1 + wCoord s a ^ 2) * (1 + vCoord s z a b ^ 2))

/-- The type-(iv) sine-product divided by `s²`. -/
def typeFourSineProductBar (s z : ℝ) : ℝ :=
  4 * aCoord s z / ((1 + s ^ 2) * (1 + yCoord s z ^ 2))
/-- The rational type-(iv) sine increment has the claimed removable factor. -/
theorem sq_mul_typeFourSineBar (s z : ℝ) :
    s ^ 2 * typeFourSineBar s z =
      halfSin (yCoord s z) - halfSin s := by
  simp [typeFourSineBar, halfSin, yCoord, aCoord]
  field_simp [one_add_sq_ne_zero]
  ring

/-- The rational type-(iii) sine increment has the claimed removable factor. -/
theorem sq_mul_typeThreeSineBar (s z a b : ℝ) :
    s ^ 2 * typeThreeSineBar s z a b =
      halfSin (vCoord s z a b) - halfSin (wCoord s a) := by
  simp [typeThreeSineBar, halfSin, vCoord, wCoord]
  field_simp [one_add_sq_ne_zero]
  ring

/-- The rational type-(iv) sine product has the claimed removable factor. -/
theorem sq_mul_typeFourSineProductBar (s z : ℝ) :
    s ^ 2 * typeFourSineProductBar s z =
      halfSin s * halfSin (yCoord s z) := by
  simp [typeFourSineProductBar, halfSin, yCoord, aCoord]
  field_simp [one_add_sq_ne_zero]
  ring

/-- Cancellation-free normalized type-(iv) fold row. -/
def foldRow (s z pi : ℝ) : ℝ :=
  halfCos s * typeFourSineBar s z -
    typeFourSineProductBar s z * (pi / 2 + s ^ 2 * typeFourAngleBar s z)

/-- Cancellation-free normalized cosine/incidence row, written over its one
common denominator. -/
def cosineRow (s z a b : ℝ) : ℝ :=
  let e := eCoord s z a b
  let d := (1 + s ^ 2) * (1 - yCoord s z ^ 2) *
    (1 + wCoord s a ^ 2) * (1 + vCoord s z a b ^ 2)
  (2 * e * (2 * rCoord s a + s * e) * (1 + s ^ 2) *
      (1 - yCoord s z ^ 2) -
    2 * z * (2 + s * z) * (1 - vCoord s z a b ^ 2) *
      (1 + wCoord s a ^ 2)) / d

/-- The exactly cancelled coefficient of `pi` in the normalized area row. -/
def areaPiWeight (s a : ℝ) : ℝ :=
  2 * (NearOneNormalizedFlow.K a).eval s /
    ((1 + s ^ 2) ^ 2 * (1 + wCoord s a ^ 2) ^ 2)
/-- The polynomial `K` is exactly the cancellation-free coefficient of `pi` in
the area row. -/
theorem sq_mul_areaPiWeight (s a : ℝ) :
    s ^ 2 * areaPiWeight s a =
      2 * halfCos s ^ 2 - (1 + halfCos (wCoord s a)) ^ 2 / 2 := by
  simp [areaPiWeight, NearOneNormalizedFlow.K, NearOneNormalizedFlow.R,
    halfCos, wCoord, rCoord]
  field_simp [one_add_sq_ne_zero]
  ring

/-- Cancellation-free normalized equal-area row. -/
def areaRow (s z a b pi : ℝ) : ℝ :=
  pi * areaPiWeight s a +
    2 * halfCos s ^ 2 *
      (typeThreeAngleBar s z a b +
        (halfCos (wCoord s a) + 2) * typeThreeSineBar s z a b) -
    (1 + halfCos (wCoord s a)) ^ 2 *
      (typeFourAngleBar s z + halfCos s * typeFourSineBar s z)
/-- Unnormalized source fold residual in principal half-angle coordinates. -/
def sourceFoldResidual (s z pi : ℝ) : ℝ :=
  halfCos s * (halfSin (yCoord s z) - halfSin s) -
    halfSin s * halfSin (yCoord s z) * sourceTypeFourAngleBlock s z pi

/-- Unnormalized source cosine/incidence residual. -/
def sourceCosineResidual (s z a b : ℝ) : ℝ :=
  halfCos (wCoord s a) * halfCos (yCoord s z) -
    halfCos s * halfCos (vCoord s z a b)

/-- Unnormalized source equal-area residual in principal half-angle
coordinates. -/
def sourceAreaResidual (s z a b pi : ℝ) : ℝ :=
  2 * halfCos s ^ 2 *
      (sourceTypeThreeAngleBlock s z a b pi +
        (halfCos (wCoord s a) + 2) *
          (halfSin (vCoord s z a b) - halfSin (wCoord s a))) -
    (1 + halfCos (wCoord s a)) ^ 2 *
      (sourceTypeFourAngleBlock s z pi +
        halfCos s * (halfSin (yCoord s z) - halfSin s))

/-- Positive algebraic multiplier used to clear the fold row. -/
def foldDenominator (s z : ℝ) : ℝ :=
  2 * (1 + s ^ 2) ^ 2 * (1 + yCoord s z ^ 2)

/-- Algebraic multiplier used to clear the cosine row. -/
def cosineDenominator (s z a b : ℝ) : ℝ :=
  2 * (1 + s ^ 2) * (1 - yCoord s z ^ 2) *
    (1 + wCoord s a ^ 2) * (1 + vCoord s z a b ^ 2)

/-- Positive algebraic multiplier used to clear the area row. -/
def areaDenominator (s z a b : ℝ) : ℝ :=
  2 * (1 + s ^ 2) ^ 2 * (1 + wCoord s a ^ 2) ^ 2 *
    (1 + yCoord s z ^ 2) * (1 + vCoord s z a b ^ 2)

/-- Complete fold numerator.  The subtracted term is the angle contribution
missing from the polynomial `NearOneNormalizedFlow.H1`. -/
def completeFoldNumerator (s z pi : ℝ) : ℝ :=
  (NearOneNormalizedFlow.H1 z pi).eval s -
    foldDenominator s z * typeFourSineProductBar s z * s ^ 2 *
      typeFourAngleBar s z

/-- Complete area numerator.  The displayed correction is the angle contribution
missing from `NearOneNormalizedFlow.areaNumerator`. -/
def completeAreaNumerator (s z a b pi : ℝ) : ℝ :=
  (NearOneNormalizedFlow.areaNumerator z a b pi).eval s +
    areaDenominator s z a b *
      (2 * halfCos s ^ 2 * typeThreeAngleBar s z a b -
        (1 + halfCos (wCoord s a)) ^ 2 * typeFourAngleBar s z -
        4 * halfCos s ^ 2 * (eCoord s z a b - 2 * z))

/-- Complete row-operated third numerator.  Its algebraic part is exactly
`NearOneNormalizedFlow.H3`. -/
def completeH3Numerator (s z a b pi : ℝ) : ℝ :=
  completeAreaNumerator s z a b pi +
    s * ((4 * a - 2 * z / 3 - pi) *
      (NearOneNormalizedFlow.H2 z a b).eval s +
      (2 / 3 : ℝ) * (pi - z) * completeFoldNumerator s z pi)


/-- Exact algebraic clearing of the constant-angle part of the fold row. -/
theorem H1_eval_eq_fold_algebraic (s z pi : ℝ) :
    (NearOneNormalizedFlow.H1 z pi).eval s =
      foldDenominator s z *
        (halfCos s * typeFourSineBar s z -
          typeFourSineProductBar s z * (pi / 2)) := by
  simp [NearOneNormalizedFlow.H1, NearOneNormalizedFlow.foldNumerator,
    NearOneNormalizedFlow.A, foldDenominator, halfCos, typeFourSineBar,
    typeFourSineProductBar, yCoord, aCoord]
  field_simp [one_add_sq_ne_zero]
  ring

/-- The complete fold numerator, not `H1` alone, clears the analytic fold row. -/
theorem completeFoldNumerator_eq (s z pi : ℝ) :
    completeFoldNumerator s z pi = foldDenominator s z * foldRow s z pi := by
  rw [completeFoldNumerator, H1_eval_eq_fold_algebraic]
  simp only [foldRow]
  ring

/-- Exact clearing of the cosine row by `NearOneNormalizedFlow.H2`. -/
theorem H2_eval_eq_cosineRow (s z a b : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0) :
    (NearOneNormalizedFlow.H2 z a b).eval s =
      cosineDenominator s z a b * cosineRow s z a b := by
  have hs : 1 + s ^ 2 ≠ 0 := one_add_sq_ne_zero s
  have hw : 1 + wCoord s a ^ 2 ≠ 0 :=
    one_add_sq_ne_zero (wCoord s a)
  have hv : 1 + vCoord s z a b ^ 2 ≠ 0 :=
    one_add_sq_ne_zero (vCoord s z a b)
  have hd : (1 + s ^ 2) * (1 - yCoord s z ^ 2) *
      (1 + wCoord s a ^ 2) * (1 + vCoord s z a b ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hs hy) hw) hv
  rw [cosineRow, cosineDenominator]
  field_simp [hd]
  simp [NearOneNormalizedFlow.H2, NearOneNormalizedFlow.cosineNumerator,
    NearOneNormalizedFlow.E, NearOneNormalizedFlow.R,
    yCoord, wCoord, vCoord, aCoord, rCoord, eCoord]
  ring

private def areaAlgebraicRow (s z a b pi : ℝ) : ℝ :=
  pi * areaPiWeight s a +
    2 * halfCos s ^ 2 * (halfCos (wCoord s a) + 2) *
      typeThreeSineBar s z a b -
    (1 + halfCos (wCoord s a)) ^ 2 * halfCos s *
      typeFourSineBar s z +
    4 * halfCos s ^ 2 * (eCoord s z a b - 2 * z)

/-- Exact clearing of the algebraic part of the area row. -/
theorem areaNumerator_eval_eq_algebraic (s z a b pi : ℝ) :
    (NearOneNormalizedFlow.areaNumerator z a b pi).eval s =
      areaDenominator s z a b * areaAlgebraicRow s z a b pi := by
  simp [NearOneNormalizedFlow.areaNumerator, NearOneNormalizedFlow.areaL,
    NearOneNormalizedFlow.areaZ, NearOneNormalizedFlow.areaX,
    NearOneNormalizedFlow.W, NearOneNormalizedFlow.U, NearOneNormalizedFlow.K,
    NearOneNormalizedFlow.B, NearOneNormalizedFlow.E, NearOneNormalizedFlow.R,
    NearOneNormalizedFlow.A, areaDenominator, areaAlgebraicRow, areaPiWeight,
    halfCos, typeThreeSineBar, typeFourSineBar, yCoord, wCoord, vCoord,
    aCoord, rCoord, eCoord]
  field_simp [one_add_sq_ne_zero]
  ring

/-- The complete area numerator, not `areaNumerator` alone, clears the analytic
area row. -/
theorem completeAreaNumerator_eq (s z a b pi : ℝ) :
    completeAreaNumerator s z a b pi =
      areaDenominator s z a b * areaRow s z a b pi := by
  rw [completeAreaNumerator, areaNumerator_eval_eq_algebraic]
  simp only [areaRow, areaAlgebraicRow]
  ring

/-- The algebraic part of the complete row-operated numerator is the existing
polynomial `H3`; all omitted angle terms remain explicit. -/
theorem completeH3Numerator_eq_H3_add_corrections (s z a b pi : ℝ) :
    completeH3Numerator s z a b pi =
      (NearOneNormalizedFlow.H3 z a b pi).eval s +
        (completeAreaNumerator s z a b pi -
          (NearOneNormalizedFlow.areaNumerator z a b pi).eval s) +
        s * ((2 / 3 : ℝ) * (pi - z) *
          (completeFoldNumerator s z pi -
            (NearOneNormalizedFlow.H1 z pi).eval s)) := by
  simp [completeH3Numerator, NearOneNormalizedFlow.H3,
    NearOneNormalizedFlow.qPrime, NearOneNormalizedFlow.H2,
    NearOneNormalizedFlow.H1]
  ring

/-- The fold clearing factor is strictly positive without an extra chart guard. -/
theorem foldDenominator_pos (s z : ℝ) : 0 < foldDenominator s z := by
  rw [foldDenominator]
  positivity

/-- The area clearing factor is strictly positive without an extra chart guard. -/
theorem areaDenominator_pos (s z a b : ℝ) : 0 < areaDenominator s z a b := by
  rw [areaDenominator]
  positivity

/-- The cosine clearing factor is positive on the explicit principal-cosine
guard `Y² < 1`. -/
theorem cosineDenominator_pos (s z a b : ℝ)
    (hy : yCoord s z ^ 2 < 1) : 0 < cosineDenominator s z a b := by
  rw [cosineDenominator]
  positivity

/-- Exact zero-set bridge for the analytic fold equation. -/
theorem foldRow_eq_zero_iff (s z pi : ℝ) :
    foldRow s z pi = 0 ↔ completeFoldNumerator s z pi = 0 := by
  rw [completeFoldNumerator_eq]
  exact (mul_eq_zero.trans (or_iff_right (ne_of_gt (foldDenominator_pos s z)))).symm

/-- Exact zero-set bridge for the analytic cosine equation. -/
theorem cosineRow_eq_zero_iff (s z a b : ℝ)
    (hy : yCoord s z ^ 2 < 1) :
    cosineRow s z a b = 0 ↔
      (NearOneNormalizedFlow.H2 z a b).eval s = 0 := by
  rw [H2_eval_eq_cosineRow s z a b (ne_of_gt (sub_pos.mpr hy))]
  exact (mul_eq_zero.trans
    (or_iff_right (ne_of_gt (cosineDenominator_pos s z a b hy)))).symm

/-- Exact zero-set bridge for the analytic area equation. -/
theorem areaRow_eq_zero_iff (s z a b pi : ℝ) :
    areaRow s z a b pi = 0 ↔ completeAreaNumerator s z a b pi = 0 := by
  rw [completeAreaNumerator_eq]
  exact (mul_eq_zero.trans (or_iff_right (ne_of_gt
    (areaDenominator_pos s z a b)))).symm

/-- On the first two equations, the complete row-operated numerator has the
same zero set as the analytic area row. -/
theorem areaRow_eq_zero_iff_completeH3
    (s z a b pi : ℝ)
    (hfold : foldRow s z pi = 0)
    (hcosine : (NearOneNormalizedFlow.H2 z a b).eval s = 0) :
    areaRow s z a b pi = 0 ↔ completeH3Numerator s z a b pi = 0 := by
  have hf : completeFoldNumerator s z pi = 0 :=
    (foldRow_eq_zero_iff s z pi).mp hfold
  simp [completeH3Numerator, hf, hcosine, areaRow_eq_zero_iff]

/-- The normalized fold row is exactly the source fold residual divided by the
removable factor `s²`. -/
theorem sq_mul_foldRow_eq_source (s z pi : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hden : 1 + s * yCoord s z ≠ 0)
    (hadd : s * ((yCoord s z - s) / (1 + s * yCoord s z)) < 1) :
    s ^ 2 * foldRow s z pi = sourceFoldResidual s z pi := by
  rw [sourceFoldResidual,
    ← typeFourAngleBlock_eq_source s z pi hy hden hadd,
    ← sq_mul_typeFourSineBar s z,
    ← sq_mul_typeFourSineProductBar s z]
  simp only [foldRow]
  ring

/-- The normalized cosine row is exactly the source incidence residual divided
by its removable factor. -/
theorem cube_mul_cosineRow_eq_source (s z a b : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0) :
    s ^ 3 * halfCos (yCoord s z) * cosineRow s z a b =
      sourceCosineResidual s z a b := by
  have hs : 1 + s ^ 2 ≠ 0 := one_add_sq_ne_zero s
  have hY : 1 + yCoord s z ^ 2 ≠ 0 :=
    one_add_sq_ne_zero (yCoord s z)
  have hW : 1 + wCoord s a ^ 2 ≠ 0 :=
    one_add_sq_ne_zero (wCoord s a)
  have hV : 1 + vCoord s z a b ^ 2 ≠ 0 :=
    one_add_sq_ne_zero (vCoord s z a b)
  have hd : (1 + s ^ 2) * (1 - yCoord s z ^ 2) *
      (1 + wCoord s a ^ 2) * (1 + vCoord s z a b ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hs hy) hW) hV
  rw [cosineRow, sourceCosineResidual]
  simp only [halfCos]
  field_simp [hd, hs, hy, hY, hW, hV]
  simp [yCoord, wCoord, vCoord, aCoord, rCoord, eCoord]
  ring

/-- The normalized area row is exactly the source equal-area residual divided
by the removable factor `s²`. -/
theorem sq_mul_areaRow_eq_source (s z a b pi : ℝ)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hdenFour : 1 + s * yCoord s z ≠ 0)
    (haddFour : s *
      ((yCoord s z - s) / (1 + s * yCoord s z)) < 1)
    (hdenThree : 1 + wCoord s a * vCoord s z a b ≠ 0)
    (haddThree : wCoord s a *
      ((vCoord s z a b - wCoord s a) /
        (1 + wCoord s a * vCoord s z a b)) < 1) :
    s ^ 2 * areaRow s z a b pi = sourceAreaResidual s z a b pi := by
  have hpi := sq_mul_areaPiWeight s a
  calc
    s ^ 2 * areaRow s z a b pi =
        pi * (s ^ 2 * areaPiWeight s a) +
          s ^ 2 * (2 * halfCos s ^ 2 *
            (typeThreeAngleBar s z a b +
              (halfCos (wCoord s a) + 2) * typeThreeSineBar s z a b) -
            (1 + halfCos (wCoord s a)) ^ 2 *
              (typeFourAngleBar s z +
                halfCos s * typeFourSineBar s z)) := by
      simp only [areaRow]
      ring
    _ = pi * (2 * halfCos s ^ 2 -
          (1 + halfCos (wCoord s a)) ^ 2 / 2) +
          s ^ 2 * (2 * halfCos s ^ 2 *
            (typeThreeAngleBar s z a b +
              (halfCos (wCoord s a) + 2) * typeThreeSineBar s z a b) -
            (1 + halfCos (wCoord s a)) ^ 2 *
              (typeFourAngleBar s z +
                halfCos s * typeFourSineBar s z)) := by rw [hpi]
    _ = sourceAreaResidual s z a b pi := by
      rw [sourceAreaResidual,
        ← typeThreeAngleBlock_eq_source s z a b pi hy hdenThree haddThree,
        ← typeFourAngleBlock_eq_source s z pi hy hdenFour haddFour,
        ← sq_mul_typeThreeSineBar s z a b,
        ← sq_mul_typeFourSineBar s z]
      ring

/-- Source fold equation iff the complete cleared fold numerator, for `s ≠ 0`. -/
theorem sourceFoldResidual_eq_zero_iff_complete
    (s z pi : ℝ) (hs : s ≠ 0)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hden : 1 + s * yCoord s z ≠ 0)
    (hadd : s * ((yCoord s z - s) / (1 + s * yCoord s z)) < 1) :
    sourceFoldResidual s z pi = 0 ↔ completeFoldNumerator s z pi = 0 := by
  have hrel := sq_mul_foldRow_eq_source s z pi hy hden hadd
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  constructor
  · intro h
    apply (foldRow_eq_zero_iff s z pi).mp
    exact (mul_eq_zero.mp (hrel.trans h)).resolve_left hs2
  · intro h
    rw [← hrel]
    exact mul_eq_zero_of_right _ ((foldRow_eq_zero_iff s z pi).mpr h)

/-- Source cosine equation iff the complete polynomial `H2`, for `s ≠ 0` on
the principal-cosine chart. -/
theorem sourceCosineResidual_eq_zero_iff_H2
    (s z a b : ℝ) (hs : s ≠ 0)
    (hy : yCoord s z ^ 2 < 1) :
    sourceCosineResidual s z a b = 0 ↔
      (NearOneNormalizedFlow.H2 z a b).eval s = 0 := by
  have hyne : 1 - yCoord s z ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hrel := cube_mul_cosineRow_eq_source s z a b hyne
  have hcosY : halfCos (yCoord s z) ≠ 0 := by
    rw [halfCos]
    exact div_ne_zero hyne (one_add_sq_ne_zero (yCoord s z))
  have hfactor : s ^ 3 * halfCos (yCoord s z) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 3 hs) hcosY
  constructor
  · intro h
    apply (cosineRow_eq_zero_iff s z a b hy).mp
    exact (mul_eq_zero.mp (hrel.trans h)).resolve_left hfactor
  · intro h
    rw [← hrel]
    exact mul_eq_zero_of_right _
      ((cosineRow_eq_zero_iff s z a b hy).mpr h)

/-- Source equal-area equation iff the complete cleared area numerator, for
`s ≠ 0`. -/
theorem sourceAreaResidual_eq_zero_iff_complete
    (s z a b pi : ℝ) (hs : s ≠ 0)
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hdenFour : 1 + s * yCoord s z ≠ 0)
    (haddFour : s *
      ((yCoord s z - s) / (1 + s * yCoord s z)) < 1)
    (hdenThree : 1 + wCoord s a * vCoord s z a b ≠ 0)
    (haddThree : wCoord s a *
      ((vCoord s z a b - wCoord s a) /
        (1 + wCoord s a * vCoord s z a b)) < 1) :
    sourceAreaResidual s z a b pi = 0 ↔
      completeAreaNumerator s z a b pi = 0 := by
  have hrel := sq_mul_areaRow_eq_source s z a b pi hy
    hdenFour haddFour hdenThree haddThree
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  constructor
  · intro h
    apply (areaRow_eq_zero_iff s z a b pi).mp
    exact (mul_eq_zero.mp (hrel.trans h)).resolve_left hs2
  · intro h
    rw [← hrel]
    exact mul_eq_zero_of_right _ ((areaRow_eq_zero_iff s z a b pi).mpr h)

/-- On the source fold and cosine equations, the source equal-area equation
clears to the complete `H3` numerator whose algebraic part is
`NearOneNormalizedFlow.H3`. -/
theorem sourceAreaResidual_eq_zero_iff_completeH3
    (s z a b pi : ℝ) (hs : s ≠ 0)
    (hy : yCoord s z ^ 2 < 1)
    (hdenFour : 1 + s * yCoord s z ≠ 0)
    (haddFour : s *
      ((yCoord s z - s) / (1 + s * yCoord s z)) < 1)
    (hdenThree : 1 + wCoord s a * vCoord s z a b ≠ 0)
    (haddThree : wCoord s a *
      ((vCoord s z a b - wCoord s a) /
        (1 + wCoord s a * vCoord s z a b)) < 1)
    (hfoldSource : sourceFoldResidual s z pi = 0)
    (hcosineSource : sourceCosineResidual s z a b = 0) :
    sourceAreaResidual s z a b pi = 0 ↔
      completeH3Numerator s z a b pi = 0 := by
  have hyne : 1 - yCoord s z ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hfoldRel := sq_mul_foldRow_eq_source s z pi hyne hdenFour haddFour
  have hcosRel := sourceCosineResidual_eq_zero_iff_H2 s z a b hs hy
  have hareaRel := sq_mul_areaRow_eq_source s z a b pi hyne
    hdenFour haddFour hdenThree haddThree
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  have hfold : foldRow s z pi = 0 :=
    (mul_eq_zero.mp (hfoldRel.trans hfoldSource)).resolve_left hs2
  have hcosine : (NearOneNormalizedFlow.H2 z a b).eval s = 0 :=
    hcosRel.mp hcosineSource
  have hrow := areaRow_eq_zero_iff_completeH3 s z a b pi hfold hcosine
  constructor
  · intro h
    apply hrow.mp
    exact (mul_eq_zero.mp (hareaRel.trans h)).resolve_left hs2
  · intro h
    rw [← hareaRel]
    exact mul_eq_zero_of_right _ (hrow.mpr h)

end

end NearOneAnalyticSystem
