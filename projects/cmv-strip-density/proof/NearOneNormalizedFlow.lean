/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic

/-!
# Cancellation-free near-one third row

This module formalizes an exact polynomial cancellation imported from the
retained near-one barrier calculation.  The variable `s` is represented by
`Polynomial.X`; `z`, `a`, `b`, and `pi` are coefficient parameters.  In
particular, the polynomial quotient is obtained with `Polynomial.divX`, not by
dividing a real-valued expression by `s ^ 2`.

`H2` is a complete cleared cosine row.  `H1`, `areaNumerator`, `H3`, and the
normalized quotient are only algebraic parts: the genuine analytic fold and
area rows also contain removable arctangent-quotient terms.  Their exact
corrections and source-equation bridges are proved in `NearOneAnalyticSystem`.
Nothing here asserts existence, uniqueness, or signs for the analytic branch.
-/

namespace NearOneNormalizedFlow

open Polynomial

noncomputable section
variable (z a b pi : ℝ)

private abbrev c (x : ℝ) : ℝ[X] := Polynomial.C x

/-- The polynomial `A = 1 + s z`. -/
def A (z : ℝ) : ℝ[X] := 1 + X * c z

/-- The polynomial `R = 2 + s a`. -/
def R (a : ℝ) : ℝ[X] := 2 + X * c a

/-- Twice the divided third-angle increment from the retained coordinates. -/
def E (z a b : ℝ) : ℝ[X] := 12 * c a - 4 * c z + 2 * X * c b

/-- The polynomial `B = 2 R + s E`. -/
def B (z a b : ℝ) : ℝ[X] := 2 * R a + X * E z a b

/-- Constant-angle algebraic part of the cleared first-row numerator. -/
def foldNumerator (z pi : ℝ) : ℝ[X] :=
  c z * (1 - X ^ 2) * (1 - X ^ 2 * A z) -
    c pi * A z * (1 + X ^ 2)

/-- Cleared second-row numerator. -/
def cosineNumerator (z a b : ℝ) : ℝ[X] :=
  4 * E z a b * R a - 8 * c z +
    X * (E z a b ^ 2 - 4 * c z ^ 2) +
    X ^ 4 * (-4 * E z a b * R a + 8 * R a ^ 4 * c z) +
    X ^ 5 * (-E z a b ^ 2 + 8 * E z a b * R a ^ 3 * c z -
      8 * E z a b * R a * c z + 4 * R a ^ 4 * c z ^ 2) +
    X ^ 6 * (2 * E z a b ^ 2 * R a ^ 2 * c z -
      2 * E z a b ^ 2 * c z + 4 * E z a b * R a ^ 3 * c z ^ 2 -
      4 * E z a b * R a * c z ^ 2) +
    X ^ 7 * (E z a b ^ 2 * R a ^ 2 * c z ^ 2 - E z a b ^ 2 * c z ^ 2)

/-- The auxiliary polynomial `K` in the cleared area row. -/
def K (a : ℝ) : ℝ[X] :=
  2 * R a ^ 2 - 4 +
    X ^ 2 * (R a ^ 4 - 4 * R a ^ 2) +
    2 * X ^ 4 * (R a ^ 2 - R a ^ 4) +
    X ^ 6 * R a ^ 4

/-- First positive denominator factor in the cleared area row. -/
def U (z : ℝ) : ℝ[X] := (1 - X ^ 2) ^ 2 * (1 + X ^ 2 * A z ^ 2)

/-- Second positive denominator factor in the cleared area row. -/
def W (z a b : ℝ) : ℝ[X] := (1 + X ^ 2 * R a ^ 2) ^ 2 * (4 + X ^ 2 * B z a b ^ 2)

/-- Auxiliary numerator in the cleared area row. -/
def areaX (z a b : ℝ) : ℝ[X] := (3 + X ^ 2 * R a ^ 2) * (2 - X ^ 2 * R a * B z a b)

/-- Auxiliary numerator in the cleared area row. -/
def areaZ (z : ℝ) : ℝ[X] := (1 - X ^ 2) * (1 - X ^ 2 * A z)

/-- The `K`-weighted denominator numerator. -/
def areaL (z a b : ℝ) : ℝ[X] :=
  (1 + X ^ 2 * A z ^ 2) * (4 + X ^ 2 * B z a b ^ 2) * K a

/-- Algebraic part of the cleared third row. -/
def areaNumerator (z a b pi : ℝ) : ℝ[X] :=
  c pi * areaL z a b +
    (E z a b - 4 * c z) * U z * W z a b +
    2 * E z a b * U z * areaX z a b -
    4 * c z * (4 + X ^ 2 * B z a b ^ 2) * areaZ z

/-- Coefficient of the cleared cosine row in the third-row elimination. -/
def qPrime (z a pi : ℝ) : ℝ[X] :=
  4 * c a - c (1 / 3) * (2 * c z + c pi)

/-- Algebraic numerator whose first two `s` coefficients cancel. -/
def thirdRowNumerator (z a b pi : ℝ) : ℝ[X] :=
  areaNumerator z a b pi - 2 * cosineNumerator z a b +
    16 * foldNumerator z pi +
    X * (qPrime z a pi * cosineNumerator z a b -
      c (8 / 3) * c z * foldNumerator z pi)

/-- Polynomial quotient of the algebraic numerator by `s²`.  `divX` shifts
coefficients and has no pole at `s = 0`. -/
def normalizedThirdRow (z a b pi : ℝ) : ℝ[X] :=
  (thirdRowNumerator z a b pi).divX.divX

/-- Algebraic part of the first cleared row in the normalized combination. -/
def H1 (z pi : ℝ) : ℝ[X] := 4 * foldNumerator z pi

/-- The second cleared row in the normalized row combination. -/
def H2 (z a b : ℝ) : ℝ[X] := cosineNumerator z a b

/-- Algebraic part of the third cleared row after the row operation. -/
def H3 (z a b pi : ℝ) : ℝ[X] :=
  areaNumerator z a b pi +
    X * ((qPrime z a pi - c (2 / 3) * c pi) * cosineNumerator z a b +
      c (8 / 3) * (c pi - c z) * foldNumerator z pi)

/-- Exact cancellation of the constant coefficient. -/
theorem thirdRowNumerator_coeff_zero :
    (thirdRowNumerator z a b pi).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero]
  simp [thirdRowNumerator, areaNumerator, areaL, areaZ, areaX, W, U, K,
    cosineNumerator, foldNumerator, qPrime, B, E, R, A]
  ring

/-- Exact cancellation of the linear coefficient. -/
theorem thirdRowNumerator_coeff_one :
    (thirdRowNumerator z a b pi).coeff 1 = 0 := by
  have hcoeff :
      (thirdRowNumerator z a b pi).derivative.coeff 0 =
        (thirdRowNumerator z a b pi).coeff 1 := by
    simpa using coeff_derivative (thirdRowNumerator z a b pi) 0
  rw [← hcoeff, coeff_zero_eq_eval_zero]
  simp [thirdRowNumerator, areaNumerator, areaL, areaZ, areaX, W, U, K,
    cosineNumerator, foldNumerator, qPrime, B, E, R, A, derivative_pow]
  ring

/-- Polynomial reconstruction after the exact `s²` cancellation. -/
theorem X_sq_mul_normalizedThirdRow :
    X ^ 2 * normalizedThirdRow z a b pi = thirdRowNumerator z a b pi := by
  have h0 := thirdRowNumerator_coeff_zero z a b pi
  have h1 := thirdRowNumerator_coeff_one z a b pi
  have hd0 : ((thirdRowNumerator z a b pi).divX).coeff 0 = 0 := by
    simpa [coeff_divX] using h1
  have hx1 :
      X * (thirdRowNumerator z a b pi).divX.divX =
        (thirdRowNumerator z a b pi).divX := by
    simpa [hd0] using X_mul_divX_add (thirdRowNumerator z a b pi).divX
  have hx0 :
      X * (thirdRowNumerator z a b pi).divX = thirdRowNumerator z a b pi := by
    simpa [h0] using X_mul_divX_add (thirdRowNumerator z a b pi)
  calc
    X ^ 2 * normalizedThirdRow z a b pi =
        X * (X * (thirdRowNumerator z a b pi).divX.divX) := by
      simp [normalizedThirdRow, pow_two, mul_assoc]
    _ = X * (thirdRowNumerator z a b pi).divX := by rw [hx1]
    _ = thirdRowNumerator z a b pi := hx0

/-- The algebraic rows reproduce the numerator used by the cancellation proof. -/
theorem thirdRowNumerator_eq_rowCombination :
    thirdRowNumerator z a b pi =
      H3 z a b pi - 2 * H2 z a b + 4 * H1 z pi +
        c (2 / 3) * c pi * X * (H2 z a b - H1 z pi) := by
  have hc : c (8 / 3) = 4 * c (2 / 3) := by
    ext (_ | n)
    · norm_num [c]
    · simp [c]
  simp [thirdRowNumerator, H3, H2, H1, hc]
  ring

/-- Kernel-checked normalized identity for the algebraic row parts. -/
theorem normalizedThirdRow_identity :
    X ^ 2 * normalizedThirdRow z a b pi =
      H3 z a b pi - 2 * H2 z a b + 4 * H1 z pi +
        c (2 / 3) * c pi * X * (H2 z a b - H1 z pi) := by
  rw [X_sq_mul_normalizedThirdRow, thirdRowNumerator_eq_rowCombination]

/-- Real evaluation of the algebraic polynomial quotient. -/
def H3hatPolynomial (s z a b pi : ℝ) : ℝ :=
  (normalizedThirdRow z a b pi).eval s

/-- Evaluated form of the algebraic identity, including the singular endpoint
`s = 0`. -/
theorem H3hatPolynomial_identity (s z a b pi : ℝ) :
    s ^ 2 * H3hatPolynomial s z a b pi =
      (H3 z a b pi).eval s - 2 * (H2 z a b).eval s +
        4 * (H1 z pi).eval s +
        (2 * pi / 3) * s * ((H2 z a b).eval s - (H1 z pi).eval s) := by
  have h := congrArg (Polynomial.eval s) (normalizedThirdRow_identity z a b pi)
  change s ^ 2 * (normalizedThirdRow z a b pi).eval s =
    (H3 z a b pi).eval s - 2 * (H2 z a b).eval s +
      4 * (H1 z pi).eval s +
      (2 * pi / 3) * s * ((H2 z a b).eval s - (H1 z pi).eval s)
  simp only [eval_mul, eval_pow, eval_X, eval_add, eval_sub, eval_ofNat, eval_C] at h
  ring_nf at h ⊢
  exact h

/-- The CMV specialization of the evaluated identity. -/
theorem H3hatPolynomial_pi_identity (s z a b : ℝ) :
    s ^ 2 * H3hatPolynomial s z a b Real.pi =
      (H3 z a b Real.pi).eval s - 2 * (H2 z a b).eval s +
        4 * (H1 z Real.pi).eval s +
        (2 * Real.pi / 3) * s *
          ((H2 z a b).eval s - (H1 z Real.pi).eval s) :=
  H3hatPolynomial_identity s z a b Real.pi

end

end NearOneNormalizedFlow
