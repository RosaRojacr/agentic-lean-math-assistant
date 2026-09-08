/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdRowTwoJet
/-!
# Quadratically rescaled oriented near-one map

This module introduces the `u = s² q` rescaling of the tangent-centered,
sheared and oriented near-one root map.  Away from `s = 0` it is definitionally
the actual root map divided by `s²`; at the endpoint it has the exact candidate
value forced by the two-jet calculation.

The pole-free factorizations and continuity theorems below certify all three
rows.  The reconstruction and root-equivalence theorems cover the actual rows
away from the endpoint.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real
open Filter

noncomputable section
set_option maxRecDepth 10000

/-- The exact candidate value of the quadratically rescaled oriented map at
`s = 0`. -/
def rescaledOrientedNearOneEndpoint (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![2 * (q 0 - Real.pi ^ 3 - 7 * Real.pi),
    96 * q 1 + (2087 * Real.pi ^ 3 - 110880 * Real.pi) / 108,
    4 * Real.pi * q 2 +
      Real.pi * (146105856 - 2748816 * Real.pi ^ 2 -
        1193 * Real.pi ^ 4) / 7776]

/-- The kernel-checked exact endpoint seed. -/
def exactRescaledOrientedNearOneSeed : Fin 3 → ℝ :=
  ![Real.pi ^ 3 + 7 * Real.pi,
    (110880 * Real.pi - 2087 * Real.pi ^ 3) / 10368,
    (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 - 146105856) / 31104]

/-- The continuous endpoint extension of the actual `u = s² q` rescaling.
All three coordinates are proved continuous at `s = 0` for each fixed `q`
below; joint continuity of the polynomial second row is proved separately. -/
def rescaledOrientedNearOneMap (s : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if s = 0 then rescaledOrientedNearOneEndpoint q
  else fun i => orientedTangentCenteredRootMap s (fun j => s ^ 2 * q j) i / s ^ 2

@[simp] theorem rescaledOrientedNearOneMap_zero (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneMap 0 q = rescaledOrientedNearOneEndpoint q := by
  simp [rescaledOrientedNearOneMap]

/-- Away from the endpoint, multiplication by `s²` reconstructs every actual
oriented row exactly. -/
theorem rescaledOrientedNearOneMap_reconstruction {s : ℝ} (hs : s ≠ 0)
    (q : Fin 3 → ℝ) :
    (fun i => s ^ 2 * rescaledOrientedNearOneMap s q i) =
      orientedTangentCenteredRootMap s (fun j => s ^ 2 * q j) := by
  ext i
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  simp [rescaledOrientedNearOneMap, hs]
  exact mul_div_cancel₀ _ hs2

/-- For `s ≠ 0`, rescaling preserves exactly the complete three-row root set. -/
theorem rescaledOrientedNearOneMap_eq_zero_iff {s : ℝ} (hs : s ≠ 0)
    (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneMap s q = 0 ↔
      nearOneRootMap s Real.pi
        (tangentCenteredPoint s (fun j => s ^ 2 * q j)) = 0 := by
  rw [← orientedTangentCenteredRootMap_eq_zero_iff]
  constructor
  · intro h
    rw [← rescaledOrientedNearOneMap_reconstruction hs q, h]
    ext i
    simp
  · intro h
    ext i
    have hi := congrFun h i
    simp [rescaledOrientedNearOneMap, hs] at hi ⊢
    exact hi

/-- The displayed seed is an exact zero of the endpoint candidate. -/
theorem rescaledOrientedNearOneEndpoint_exactSeed :
    rescaledOrientedNearOneEndpoint exactRescaledOrientedNearOneSeed = 0 := by
  ext i
  fin_cases i <;>
    simp [rescaledOrientedNearOneEndpoint, exactRescaledOrientedNearOneSeed] <;>
    ring

@[simp] theorem rescaledOrientedNearOneMap_zero_exactSeed :
    rescaledOrientedNearOneMap 0 exactRescaledOrientedNearOneSeed = 0 := by
  rw [rescaledOrientedNearOneMap_zero,
    rescaledOrientedNearOneEndpoint_exactSeed]

/-- The affine endpoint system has exactly the displayed seed. -/
theorem rescaledOrientedNearOneEndpoint_eq_zero_iff (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneEndpoint q = 0 ↔
      q = exactRescaledOrientedNearOneSeed := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  constructor
  · intro h
    ext i
    fin_cases i
    · have hi := congrFun h (0 : Fin 3)
      simp [rescaledOrientedNearOneEndpoint] at hi
      simp [exactRescaledOrientedNearOneSeed]
      linarith
    · have hi := congrFun h (1 : Fin 3)
      simp [rescaledOrientedNearOneEndpoint] at hi
      simp [exactRescaledOrientedNearOneSeed]
      linarith
    · have hi := congrFun h (2 : Fin 3)
      simp [rescaledOrientedNearOneEndpoint] at hi
      simp [exactRescaledOrientedNearOneSeed]
      have h4pi : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) hpi
      calc
        q 2 = -(Real.pi * (146105856 - 2748816 * Real.pi ^ 2 -
            1193 * Real.pi ^ 4) / 7776) / (4 * Real.pi) := by
          apply (eq_div_iff h4pi).2
          linarith
        _ = (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 -
            146105856) / 31104 := by
          field_simp [hpi]
          ring
  · rintro rfl
    exact rescaledOrientedNearOneEndpoint_exactSeed

/-! ## The rescaled physical path -/

/-- First physical coordinate along the `u = s² q` chart. -/
def rescaledFirstPhysicalCoordinate (s q0 : ℝ) : ℝ :=
  Real.pi + s * Real.pi ^ 2 + s ^ 2 * q0

@[simp] theorem tangentCenteredPoint_rescaled_zeroCoord
    (s : ℝ) (q : Fin 3 → ℝ) :
    tangentCenteredPoint s (fun j => s ^ 2 * q j) 0 =
      rescaledFirstPhysicalCoordinate s (q 0) := by
  simp [tangentCenteredPoint, rescaledFirstPhysicalCoordinate,
    exactCuspPoint, exactCuspTangent, exactCuspShear,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ## Exact polynomial cancellation in the second row -/

/-- Exact polynomial path of the physical `z` coordinate along `u = s² q`. -/
def rescaledZPathPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  C Real.pi + C (Real.pi ^ 2) * X + C (q 0) * X ^ 2

/-- Exact polynomial path of the physical `a` coordinate along `u = s² q`. -/
def rescaledAPathPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  C (5 * Real.pi / 12) +
    C ((43 * Real.pi ^ 2 + 1056) / 144) * X +
    C (5 * q 0 / 12 + q 1) * X ^ 2

/-- Exact polynomial path of the physical `b` coordinate along `u = s² q`. -/
def rescaledBPathPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  C (-44 + 19 * Real.pi ^ 2 / 24) +
    C (Real.pi * (295 * Real.pi ^ 2 - 14256) / 216) * X +
    C ((109 * Real.pi ^ 2 - 5376) / (72 * Real.pi) * q 0 +
      (2880 - 7 * Real.pi ^ 2) / (6 * Real.pi) * q 1 + q 2) * X ^ 2

@[simp] theorem rescaledZPathPolynomial_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (rescaledZPathPolynomial q).eval s =
      tangentCenteredPoint s (fun j => s ^ 2 * q j) 0 := by
  simp [rescaledZPathPolynomial, tangentCenteredPoint, exactCuspPoint,
    exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

@[simp] theorem rescaledAPathPolynomial_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (rescaledAPathPolynomial q).eval s =
      tangentCenteredPoint s (fun j => s ^ 2 * q j) 1 := by
  simp [rescaledAPathPolynomial, tangentCenteredPoint, exactCuspPoint,
    exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

@[simp] theorem rescaledBPathPolynomial_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (rescaledBPathPolynomial q).eval s =
      tangentCenteredPoint s (fun j => s ^ 2 * q j) 2 := by
  simp [rescaledBPathPolynomial, tangentCenteredPoint, exactCuspPoint,
    exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  ring

/-- The complete cleared `H2` polynomial after lifting all three physical
coordinates to their exact `u = s² q` paths. -/
def rescaledH2PathPolynomial (q : Fin 3 → ℝ) : ℝ[X] :=
  let Z := rescaledZPathPolynomial q
  let A := rescaledAPathPolynomial q
  let B := rescaledBPathPolynomial q
  let R := 2 + X * A
  let E := 12 * A - 4 * Z + 2 * X * B
  4 * E * R - 8 * Z +
    X * (E ^ 2 - 4 * Z ^ 2) +
    X ^ 4 * (-4 * E * R + 8 * R ^ 4 * Z) +
    X ^ 5 * (-E ^ 2 + 8 * E * R ^ 3 * Z -
      8 * E * R * Z + 4 * R ^ 4 * Z ^ 2) +
    X ^ 6 * (2 * E ^ 2 * R ^ 2 * Z -
      2 * E ^ 2 * Z + 4 * E * R ^ 3 * Z ^ 2 -
      4 * E * R * Z ^ 2) +
    X ^ 7 * (E ^ 2 * R ^ 2 * Z ^ 2 - E ^ 2 * Z ^ 2)

/-- Evaluating the lifted polynomial gives the actual cleared cosine row along
the physical tangent-centered `u = s² q` path. -/
theorem rescaledH2PathPolynomial_eval_eq_actual (s : ℝ) (q : Fin 3 → ℝ) :
    (rescaledH2PathPolynomial q).eval s =
      (NearOneNormalizedFlow.H2
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 0)
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 1)
        (tangentCenteredPoint s (fun j => s ^ 2 * q j) 2)).eval s := by
  simp [rescaledH2PathPolynomial, NearOneNormalizedFlow.H2,
    NearOneNormalizedFlow.cosineNumerator, NearOneNormalizedFlow.E,
    NearOneNormalizedFlow.R]
  ring

/-- The lifted cosine polynomial has no constant term. -/
theorem rescaledH2PathPolynomial_coeff_zero (q : Fin 3 → ℝ) :
    (rescaledH2PathPolynomial q).coeff 0 = 0 := by
  simp [rescaledH2PathPolynomial, rescaledZPathPolynomial,
    rescaledAPathPolynomial, rescaledBPathPolynomial]
  ring

/-- The lifted cosine polynomial has no linear term. -/
theorem rescaledH2PathPolynomial_coeff_one (q : Fin 3 → ℝ) :
    (rescaledH2PathPolynomial q).coeff 1 = 0 := by
  let p := rescaledH2PathPolynomial q
  have hcoeff : p.derivative.coeff 0 = p.coeff 1 := by
    simpa using coeff_derivative p 0
  rw [← hcoeff, coeff_zero_eq_eval_zero]
  simp [p, rescaledH2PathPolynomial, rescaledZPathPolynomial,
    rescaledAPathPolynomial, rescaledBPathPolynomial, derivative_pow]
  ring

/-- Dividing twice by `X` exactly reconstructs the lifted cosine polynomial. -/
theorem X_sq_mul_rescaledH2PathPolynomial_divX_divX (q : Fin 3 → ℝ) :
    X ^ 2 * (rescaledH2PathPolynomial q).divX.divX =
      rescaledH2PathPolynomial q := by
  have h0 := rescaledH2PathPolynomial_coeff_zero q
  have h1 := rescaledH2PathPolynomial_coeff_one q
  have hd0 : ((rescaledH2PathPolynomial q).divX).coeff 0 = 0 := by
    simpa [coeff_divX] using h1
  have hx1 :
      X * (rescaledH2PathPolynomial q).divX.divX =
        (rescaledH2PathPolynomial q).divX := by
    simpa [hd0] using X_mul_divX_add (rescaledH2PathPolynomial q).divX
  have hx0 :
      X * (rescaledH2PathPolynomial q).divX =
        rescaledH2PathPolynomial q := by
    simpa [h0] using X_mul_divX_add (rescaledH2PathPolynomial q)
  calc
    X ^ 2 * (rescaledH2PathPolynomial q).divX.divX =
        X * (X * (rescaledH2PathPolynomial q).divX.divX) := by
          simp [pow_two, mul_assoc]
    _ = X * (rescaledH2PathPolynomial q).divX := by rw [hx1]
    _ = rescaledH2PathPolynomial q := hx0

/-- Pole-free second rescaled row obtained from exact double polynomial
division. -/
def poleFreeSecondRescaledRow (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  ((rescaledH2PathPolynomial q).divX.divX).eval s

/-- The pole-free second row has exactly the prescribed endpoint value. -/
@[simp] theorem poleFreeSecondRescaledRow_zero (q : Fin 3 → ℝ) :
    poleFreeSecondRescaledRow 0 q =
      96 * q 1 + (2087 * Real.pi ^ 3 - 110880 * Real.pi) / 108 := by
  let p := rescaledH2PathPolynomial q
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hcoeff : p.derivative.derivative.coeff 0 = 2 * p.coeff 2 := by
    rw [coeff_derivative, coeff_derivative]
    norm_num
    ring
  change p.divX.divX.eval 0 = _
  rw [← coeff_zero_eq_eval_zero, coeff_divX, coeff_divX]
  norm_num
  rw [← show p.derivative.derivative.coeff 0 / 2 = p.coeff 2 by
    rw [hcoeff]
    ring, coeff_zero_eq_eval_zero]
  simp [p, rescaledH2PathPolynomial, rescaledZPathPolynomial,
    rescaledAPathPolynomial, rescaledBPathPolynomial, derivative_pow]
  field_simp [hpi]
  ring

/-- The actual cleared cosine row has an exact `s²` factor along the rescaled
physical path. -/
theorem H2_rescaled_exact_factorization (s : ℝ) (q : Fin 3 → ℝ) :
    (NearOneNormalizedFlow.H2
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 0)
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 1)
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 2)).eval s =
        s ^ 2 * poleFreeSecondRescaledRow s q := by
  rw [← rescaledH2PathPolynomial_eval_eq_actual]
  have hrecon := X_sq_mul_rescaledH2PathPolynomial_divX_divX q
  have heval := congrArg (fun p : ℝ[X] => p.eval s) hrecon
  simpa only [eval_mul, eval_pow, eval_X, poleFreeSecondRescaledRow] using
    heval.symm

/-- The pole-free formula is the second coordinate of the actual piecewise
rescaled map, including at `s = 0`. -/
theorem rescaledOrientedNearOneMap_second_eq_poleFree
    (s : ℝ) (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneMap s q 1 = poleFreeSecondRescaledRow s q := by
  by_cases hs : s = 0
  · subst s
    simp [rescaledOrientedNearOneEndpoint]
  · have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    simp [rescaledOrientedNearOneMap, hs, orientedTangentCenteredRootMap,
      orientNearOneRows, nearOneRootMap]
    rw [← tangentCenteredPoint_rescaled_zeroCoord s q,
      H2_rescaled_exact_factorization]
    exact mul_div_cancel_left₀ _ hs2

/-- For fixed `q`, the pole-free second row is continuous at the endpoint. -/
theorem continuousAt_poleFreeSecondRescaledRow_zero (q : Fin 3 → ℝ) :
    ContinuousAt (fun s => poleFreeSecondRescaledRow s q) 0 := by
  unfold poleFreeSecondRescaledRow
  fun_prop

/-- The actual fixed-`q` second rescaled coordinate has the asserted continuous
extension at `s = 0`. -/
theorem continuousAt_rescaledOrientedNearOneMap_second_zero
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun s => rescaledOrientedNearOneMap s q 1) 0 := by
  rw [show (fun s => rescaledOrientedNearOneMap s q 1) =
      fun s => poleFreeSecondRescaledRow s q by
    funext s
    exact rescaledOrientedNearOneMap_second_eq_poleFree s q]
  exact continuousAt_poleFreeSecondRescaledRow_zero q

/-! ## Pole-free first row -/

/-- Polynomial left after removing the exact `s²` factor from the rational
part of the first row.  Its remaining analytic input is already pole-free. -/
def firstRescaledAlgebraicFactor (s q0 angle : ℝ) : ℝ :=
  -4 * angle * (1 + s ^ 2) *
      (1 + s * (Real.pi + s * Real.pi ^ 2 + s ^ 2 * q0)) +
    2 * (Real.pi ^ 4 * s ^ 5 - Real.pi ^ 4 * s ^ 3 +
      2 * Real.pi ^ 3 * s ^ 4 - 3 * Real.pi ^ 3 * s ^ 2 - Real.pi ^ 3 +
      2 * Real.pi ^ 2 * q0 * s ^ 6 - 2 * Real.pi ^ 2 * q0 * s ^ 4 +
      2 * Real.pi ^ 2 * s ^ 3 - 4 * Real.pi ^ 2 * s +
      2 * Real.pi * q0 * s ^ 5 - 3 * Real.pi * q0 * s ^ 3 -
        Real.pi * q0 * s +
      Real.pi * s ^ 2 - 3 * Real.pi + q0 ^ 2 * s ^ 7 - q0 ^ 2 * s ^ 5 +
      q0 * s ^ 4 - 2 * q0 * s ^ 2 + q0)

/-- A denominator-safe exact expression for the first rescaled row. -/
def poleFreeFirstRescaledRow (s q0 : ℝ) : ℝ :=
  firstRescaledAlgebraicFactor s q0
      (typeFourAngleBar s (rescaledFirstPhysicalCoordinate s q0)) /
    ((1 + s ^ 2) ^ 2 *
      (1 + yCoord s (rescaledFirstPhysicalCoordinate s q0) ^ 2))

/-- Exact first-row factorization along the rescaled chart, valid also at
`s = 0`. -/
theorem foldRow_rescaled_exact_factorization (s q0 : ℝ) :
    foldRow s (rescaledFirstPhysicalCoordinate s q0) Real.pi =
      s ^ 2 * poleFreeFirstRescaledRow s q0 := by
  have h1 : 1 + s ^ 2 ≠ 0 := by positivity
  have hy : 1 + yCoord s (rescaledFirstPhysicalCoordinate s q0) ^ 2 ≠ 0 := by
    positivity
  unfold poleFreeFirstRescaledRow firstRescaledAlgebraicFactor
  unfold foldRow halfCos typeFourSineBar typeFourSineProductBar
  field_simp [h1, hy]
  unfold rescaledFirstPhysicalCoordinate yCoord aCoord
  ring

@[simp] theorem poleFreeFirstRescaledRow_zero (q0 : ℝ) :
    poleFreeFirstRescaledRow 0 q0 =
      2 * (q0 - Real.pi ^ 3 - 7 * Real.pi) := by
  simp [poleFreeFirstRescaledRow, firstRescaledAlgebraicFactor,
    rescaledFirstPhysicalCoordinate, typeFourAngleBar,
    densityCubeQuotient, density, halfCos, typeFourAngleIncrement,
    yCoord, aCoord, atanQuotient]
  ring

private theorem continuousAt_typeFourAngleBar_rescaled
    (q0 : ℝ) :
    ContinuousAt (fun s => typeFourAngleBar s
      (rescaledFirstPhysicalCoordinate s q0)) 0 := by
  have hquot : ContinuousAt (fun s : ℝ => atanQuotient
      (s ^ 2 * rescaledFirstPhysicalCoordinate s q0 /
        (1 + s * yCoord s (rescaledFirstPhysicalCoordinate s q0)))) 0 :=
    continuous_atanQuotient.continuousAt.comp (by
      unfold rescaledFirstPhysicalCoordinate yCoord aCoord
      fun_prop (disch := norm_num))
  unfold typeFourAngleBar densityCubeQuotient density halfCos
    typeFourAngleIncrement yCoord aCoord rescaledFirstPhysicalCoordinate
  fun_prop (disch := first | exact hquot | norm_num)

/-- The pole-free first-row formula is continuous at the endpoint. -/
theorem continuousAt_poleFreeFirstRescaledRow_zero (q0 : ℝ) :
    ContinuousAt (fun s => poleFreeFirstRescaledRow s q0) 0 := by
  have hangle := continuousAt_typeFourAngleBar_rescaled q0
  have hz : ContinuousAt
      (fun s : ℝ => rescaledFirstPhysicalCoordinate s q0) 0 := by
    unfold rescaledFirstPhysicalCoordinate
    fun_prop
  have hy : ContinuousAt
      (fun s : ℝ => yCoord s (rescaledFirstPhysicalCoordinate s q0)) 0 := by
    unfold yCoord aCoord
    fun_prop (disch := exact hz)
  have hden : (1 + (0 : ℝ) ^ 2) ^ 2 *
      (1 + yCoord 0 (rescaledFirstPhysicalCoordinate 0 q0) ^ 2) ≠ 0 := by
    positivity
  unfold poleFreeFirstRescaledRow firstRescaledAlgebraicFactor
  fun_prop (disch := first | exact hangle | exact hz | exact hy | exact hden |
    norm_num)

/-- The first coordinate of the piecewise rescaled map is the genuine
pole-free extension of the actual first row. -/
theorem rescaledOrientedNearOneMap_first_eq_poleFree
    (s : ℝ) (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneMap s q 0 =
      poleFreeFirstRescaledRow s (q 0) := by
  by_cases hs : s = 0
  · subst s
    simp [rescaledOrientedNearOneEndpoint]
  · have hfactor := foldRow_rescaled_exact_factorization s (q 0)
    have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    simp [rescaledOrientedNearOneMap, hs, orientedTangentCenteredRootMap,
      orientNearOneRows, nearOneRootMap,
      tangentCenteredPoint_rescaled_zeroCoord] at hfactor ⊢
    apply (div_eq_iff hs2).2
    simpa [mul_comm] using hfactor

/-- Consequently the actual fixed-`q` first rescaled row has the asserted
continuous extension at `s = 0`. -/
theorem continuousAt_rescaledOrientedNearOneMap_first_zero
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun s => rescaledOrientedNearOneMap s q 0) 0 := by
  rw [show (fun s => rescaledOrientedNearOneMap s q 0) =
      fun s => poleFreeFirstRescaledRow s (q 0) by
    funext s
    exact rescaledOrientedNearOneMap_first_eq_poleFree s q]
  exact continuousAt_poleFreeFirstRescaledRow_zero (q 0)

/-! ## The actual third rescaled row -/

/-- The exact two-jet endpoint value before third-row orientation. -/
def poleFreeThirdRescaledRowEndpoint (q : Fin 3 → ℝ) : ℝ :=
  Real.pi * (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 -
    31104 * q 2 - 146105856) / 7776

/-- The totalized rescaled third row before orientation. Away from the endpoint
this is definitionally the actual regularized row divided by `s²`; at the
endpoint it is the exact two-jet coefficient. -/
def poleFreeThirdRescaledRow (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  if s = 0 then poleFreeThirdRescaledRowEndpoint q
  else
    regularizedThirdRow s
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 0)
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 1)
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 2) Real.pi / s ^ 2

@[simp] theorem poleFreeThirdRescaledRow_zero (q : Fin 3 → ℝ) :
    poleFreeThirdRescaledRow 0 q =
      Real.pi * (1193 * Real.pi ^ 4 + 2748816 * Real.pi ^ 2 -
        31104 * q 2 - 146105856) / 7776 := by
  simp [poleFreeThirdRescaledRow, poleFreeThirdRescaledRowEndpoint]

/-- Exact `s²` factorization of the regularized third row along the physical
quadratically rescaled tangent-centered path. -/
theorem regularizedThirdRow_rescaled_exact_factorization
    (s : ℝ) (q : Fin 3 → ℝ) :
    regularizedThirdRow s
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 0)
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 1)
      (tangentCenteredPoint s (fun j => s ^ 2 * q j) 2) Real.pi =
        s ^ 2 * poleFreeThirdRescaledRow s q := by
  by_cases hs : s = 0
  · subst s
    have hcusp := congrFun nearOneRootMap_exactCusp (2 : Fin 3)
    simp [nearOneRootMap, tangentCenteredPoint_zero,
      poleFreeThirdRescaledRow] at hcusp ⊢
    exact hcusp
  · simp [poleFreeThirdRescaledRow, hs]
    exact (mul_div_cancel₀ _ (pow_ne_zero 2 hs)).symm

/-- The genuine third-row two-jet gives continuity of its totalized quotient
by `s²` at the cusp. -/
theorem continuousAt_poleFreeThirdRescaledRow_zero
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun s => poleFreeThirdRescaledRow s q) 0 := by
  simpa [poleFreeThirdRescaledRow, poleFreeThirdRescaledRowEndpoint] using
    (regularizedThirdRow_physical_twoJet q).continuousAt_div_sq

/-- The totalized third rescaled row is jointly continuous in scale and
rescaled coordinates at the cusp. -/
theorem continuousAt_poleFreeThirdRescaledRow_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      poleFreeThirdRescaledRow p.1 p.2) (0, q) := by
  simpa only [poleFreeThirdRescaledRow,
    poleFreeThirdRescaledRowEndpoint] using
    continuousAt_regularizedThirdRow_physical_div_sq_joint q

/-- The third coordinate of the oriented rescaled map is exactly the negative
of the genuine pre-orientation rescaled third row, including at the endpoint. -/
theorem rescaledOrientedNearOneMap_third_eq_neg_poleFree
    (s : ℝ) (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneMap s q 2 = -poleFreeThirdRescaledRow s q := by
  by_cases hs : s = 0
  · subst s
    simp [rescaledOrientedNearOneEndpoint, poleFreeThirdRescaledRow,
      poleFreeThirdRescaledRowEndpoint]
    ring
  · simp [rescaledOrientedNearOneMap, hs, orientedTangentCenteredRootMap,
      orientNearOneRows, nearOneRootMap, poleFreeThirdRescaledRow]
    ring

/-- The third coordinate of the oriented rescaled map is continuous at the
cusp. -/
theorem continuousAt_rescaledOrientedNearOneMap_third_zero
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun s => rescaledOrientedNearOneMap s q 2) 0 := by
  rw [show (fun s => rescaledOrientedNearOneMap s q 2) =
      fun s => -poleFreeThirdRescaledRow s q by
    funext s
    exact rescaledOrientedNearOneMap_third_eq_neg_poleFree s q]
  exact (continuousAt_poleFreeThirdRescaledRow_zero q).neg

/-- The third coordinate of the oriented rescaled map is jointly continuous in
the scale and rescaled coordinates at every cusp endpoint. -/
theorem continuousAt_rescaledOrientedNearOneMap_third_joint
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 2) (0, q) := by
  rw [show (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 2) =
      fun p => -poleFreeThirdRescaledRow p.1 p.2 by
    funext p
    exact rescaledOrientedNearOneMap_third_eq_neg_poleFree p.1 p.2]
  exact (continuousAt_poleFreeThirdRescaledRow_joint q).neg

/-- The complete quadratically rescaled, oriented near-one map is continuous
at its cusp endpoint for every fixed rescaled coordinate `q`. -/
theorem continuousAt_rescaledOrientedNearOneMap_zero
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun s => rescaledOrientedNearOneMap s q) 0 := by
  rw [continuousAt_pi]
  intro i
  fin_cases i
  · exact continuousAt_rescaledOrientedNearOneMap_first_zero q
  · exact continuousAt_rescaledOrientedNearOneMap_second_zero q
  · exact continuousAt_rescaledOrientedNearOneMap_third_zero q


end

end NearOneRegularizedThirdRow
