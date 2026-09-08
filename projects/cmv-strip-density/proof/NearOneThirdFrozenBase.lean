/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneRescaledOrientedMap

/-!
# Exact cubic cancellation on the frozen third-row path

This module isolates the polynomial algebra needed to prove that the cleared
frozen-path error has an exact cubic factor. It deliberately excludes the
rational-evaluation bridges and all face-bound machinery.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

def frozenAlgA (Z : ℝ[X]) : ℝ[X] := 1 + X * Z
def frozenAlgR (A : ℝ[X]) : ℝ[X] := 2 + X * A
def frozenAlgE (Z A B : ℝ[X]) : ℝ[X] := 6 * A - 2 * Z + X * B
def frozenAlgDoubleE (Z A B : ℝ[X]) : ℝ[X] := 12 * A - 4 * Z + 2 * X * B
def frozenAlgDoubleB (Z A B : ℝ[X]) : ℝ[X] :=
  2 * frozenAlgR A + X * frozenAlgDoubleE Z A B

def frozenAlgFoldNumerator (Z : ℝ[X]) (p : ℝ) : ℝ[X] :=
  Z * (1 - X ^ 2) * (1 - X ^ 2 * frozenAlgA Z) -
    C p * frozenAlgA Z * (1 + X ^ 2)

def frozenAlgCosineNumerator (Z A B : ℝ[X]) : ℝ[X] :=
  let R := frozenAlgR A
  let E := frozenAlgDoubleE Z A B
  4 * E * R - 8 * Z +
    X * (E ^ 2 - 4 * Z ^ 2) +
    X ^ 4 * (-4 * E * R + 8 * R ^ 4 * Z) +
    X ^ 5 * (-E ^ 2 + 8 * E * R ^ 3 * Z - 8 * E * R * Z +
      4 * R ^ 4 * Z ^ 2) +
    X ^ 6 * (2 * E ^ 2 * R ^ 2 * Z - 2 * E ^ 2 * Z +
      4 * E * R ^ 3 * Z ^ 2 - 4 * E * R * Z ^ 2) +
    X ^ 7 * (E ^ 2 * R ^ 2 * Z ^ 2 - E ^ 2 * Z ^ 2)

def frozenAlgK (A : ℝ[X]) : ℝ[X] :=
  let R := frozenAlgR A
  2 * R ^ 2 - 4 + X ^ 2 * (R ^ 4 - 4 * R ^ 2) +
    2 * X ^ 4 * (R ^ 2 - R ^ 4) + X ^ 6 * R ^ 4

def frozenAlgU (Z : ℝ[X]) : ℝ[X] :=
  (1 - X ^ 2) ^ 2 * (1 + X ^ 2 * frozenAlgA Z ^ 2)

def frozenAlgW (Z A B : ℝ[X]) : ℝ[X] :=
  (1 + X ^ 2 * frozenAlgR A ^ 2) ^ 2 *
    (4 + X ^ 2 * frozenAlgDoubleB Z A B ^ 2)

def frozenAlgAreaX (Z A B : ℝ[X]) : ℝ[X] :=
  (3 + X ^ 2 * frozenAlgR A ^ 2) *
    (2 - X ^ 2 * frozenAlgR A * frozenAlgDoubleB Z A B)

def frozenAlgAreaZ (Z : ℝ[X]) : ℝ[X] :=
  (1 - X ^ 2) * (1 - X ^ 2 * frozenAlgA Z)

def frozenAlgAreaL (Z A B : ℝ[X]) : ℝ[X] :=
  (1 + X ^ 2 * frozenAlgA Z ^ 2) *
    (4 + X ^ 2 * frozenAlgDoubleB Z A B ^ 2) * frozenAlgK A

def frozenAlgAreaNumerator (Z A B : ℝ[X]) (p : ℝ) : ℝ[X] :=
  C p * frozenAlgAreaL Z A B +
    (frozenAlgDoubleE Z A B - 4 * Z) * frozenAlgU Z * frozenAlgW Z A B +
    2 * frozenAlgDoubleE Z A B * frozenAlgU Z * frozenAlgAreaX Z A B -
    4 * Z * (4 + X ^ 2 * frozenAlgDoubleB Z A B ^ 2) * frozenAlgAreaZ Z

def frozenAlgQPrime (Z A : ℝ[X]) (p : ℝ) : ℝ[X] :=
  4 * A - C (1 / 3 : ℝ) * (2 * Z + C p)

def frozenAlgThirdNumerator (Z A B : ℝ[X]) (p : ℝ) : ℝ[X] :=
  frozenAlgAreaNumerator Z A B p - 2 * frozenAlgCosineNumerator Z A B +
    16 * frozenAlgFoldNumerator Z p +
    X * (frozenAlgQPrime Z A p * frozenAlgCosineNumerator Z A B -
      C (8 / 3 : ℝ) * Z * frozenAlgFoldNumerator Z p)

def frozenH3PathNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  frozenAlgThirdNumerator (rescaledZPathPolynomial q)
    (rescaledAPathPolynomial q) (rescaledBPathPolynomial q) π

def frozenH3PathPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  (frozenH3PathNumerator q).divX.divX


def frozenPathA (q : Fin 3 → ℝ) : ℝ[X] :=
  frozenAlgA (rescaledZPathPolynomial q)
def frozenPathR (q : Fin 3 → ℝ) : ℝ[X] :=
  frozenAlgR (rescaledAPathPolynomial q)
def frozenPathE (q : Fin 3 → ℝ) : ℝ[X] :=
  frozenAlgE (rescaledZPathPolynomial q) (rescaledAPathPolynomial q)
    (rescaledBPathPolynomial q)
def frozenPathY (q : Fin 3 → ℝ) : ℝ[X] := X * frozenPathA q
def frozenPathW (q : Fin 3 → ℝ) : ℝ[X] := X * frozenPathR q
def frozenPathV (q : Fin 3 → ℝ) : ℝ[X] :=
  X * (frozenPathR q + X * frozenPathE q)
def frozenPathD4 (q : Fin 3 → ℝ) : ℝ[X] := 1 + X * frozenPathY q
def frozenPathD3 (q : Fin 3 → ℝ) : ℝ[X] :=
  1 + frozenPathW q * frozenPathV q
def frozenPathDensityDenominator (q : Fin 3 → ℝ) : ℝ[X] :=
  (1 + X ^ 2) * (1 - frozenPathY q ^ 2)
def frozenPathDensityNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  2 * rescaledZPathPolynomial q *
    (2 + X * rescaledZPathPolynomial q)
def frozenPathRhoNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  (1 - X ^ 2) * (1 + frozenPathY q ^ 2)

def frozenPathFourIncrementNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  2 * rescaledZPathPolynomial q *
    (-(X ^ 2 * rescaledZPathPolynomial q ^ 2) -
      3 * frozenPathA q * frozenPathD4 q ^ 2)

def frozenPathThreeIncrementNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  2 * frozenPathE q *
    (-(X ^ 2 * frozenPathE q ^ 2) -
      3 * frozenPathR q * (frozenPathR q + X * frozenPathE q) *
        frozenPathD3 q ^ 2)

def frozenPathFourBarNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  2 * frozenPathDensityNumerator q * (3 - X ^ 2) * frozenPathD4 q ^ 3 +
    frozenPathRhoNumerator q * frozenPathFourIncrementNumerator q +
    6 * X * rescaledZPathPolynomial q * frozenPathDensityNumerator q *
      frozenPathD4 q ^ 3

def frozenPathThreeBarNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  2 * frozenPathDensityNumerator q * frozenPathR q *
      (3 - frozenPathW q ^ 2) * frozenPathD3 q ^ 3 +
    frozenPathRhoNumerator q * frozenPathThreeIncrementNumerator q +
    6 * X * frozenPathE q * frozenPathDensityNumerator q *
      frozenPathD3 q ^ 3

def frozenPathCommonDenominator (q : Fin 3 → ℝ) : ℝ[X] :=
  3 * frozenPathDensityDenominator q * frozenPathD3 q ^ 3 *
    frozenPathD4 q ^ 3

def frozenPathThreeCoefficient (q : Fin 3 → ℝ) : ℝ[X] :=
  4 * (1 - X ^ 2) ^ 2 * (1 + frozenPathW q ^ 2) ^ 2 *
    (1 + frozenPathY q ^ 2) * (1 + frozenPathV q ^ 2)
def frozenPathFourCoefficient (q : Fin 3 → ℝ) : ℝ[X] :=
  -8 * (1 + X ^ 2) ^ 2 * (1 + frozenPathY q ^ 2) *
    (1 + frozenPathV q ^ 2)
def frozenPathPiCoefficient (q : Fin 3 → ℝ) : ℝ[X] :=
  16 * rescaledZPathPolynomial q * frozenAlgK (rescaledAPathPolynomial q) *
    (1 + frozenPathY q ^ 2) * (1 + frozenPathV q ^ 2)
def frozenPathFoldCoefficient (q : Fin 3 → ℝ) : ℝ[X] :=
  -(4 - C (2 / 3 : ℝ) * rescaledZPathPolynomial q * X) * 8 *
    frozenPathA q * (1 + X ^ 2)

def frozenPathCommonNumerator (q : Fin 3 → ℝ) : ℝ[X] :=
  frozenPathCommonDenominator q * frozenH3PathPolynomial q +
    frozenPathD4 q ^ 3 * frozenPathThreeCoefficient q *
      frozenPathThreeBarNumerator q +
    frozenPathD3 q ^ 3 * frozenPathFourCoefficient q *
      frozenPathFourBarNumerator q +
    frozenPathCommonDenominator q * frozenPathPiCoefficient q +
    frozenPathCommonDenominator q * frozenPathFoldCoefficient q *
      (2 * rescaledZPathPolynomial q) +
    frozenPathD3 q ^ 3 * frozenPathFoldCoefficient q * X ^ 2 *
      frozenPathFourBarNumerator q

def frozenEndpointQuadratic (q : Fin 3 → ℝ) : ℝ :=
  π * (1193 * π ^ 4 + 2748816 * π ^ 2 -
    31104 * q 2 - 146105856) / 7776

def frozenCommonCubic (q : Fin 3 → ℝ) : ℝ :=
  -(90263 * π ^ 7 - 27975264 * π ^ 5 - 54756 * π ^ 4 * q 0 +
      310608 * π ^ 4 * q 1 + 18144 * π ^ 3 * q 2 +
      1163718144 * π ^ 3 - 6082560 * π ^ 2 * q 0 -
      104758272 * π ^ 2 * q 1 - 7464960 * π * q 2 +
      557383680 * q 0 - 3583180800 * q 1) / (7776 * π)

theorem polynomial_coeff_via_derivative (p : ℝ[X]) (n : ℕ) :
    p.coeff n = (derivative^[n] p).eval 0 / (n.factorial : ℝ) := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]
  rw [eq_div_iff (by positivity)]
  ring


def frozenPathClearedError (q : Fin 3 → ℝ) : ℝ[X] :=
  frozenPathCommonNumerator q -
    frozenPathCommonDenominator q * X ^ 2 * C (frozenEndpointQuadratic q)


end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
