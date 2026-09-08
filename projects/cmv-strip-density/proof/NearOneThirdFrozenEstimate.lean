/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenCubic
import NearOneThirdFaceBounds
import ScalarSuffixCertificate
import Mathlib.Analysis.Polynomial.Norm

/-!
# An explicit frozen third-row cell

This file clears every rational denominator in the frozen third row, represents
its endpoint path by one exact polynomial, and bounds the terms beyond its
cubic jet by coefficient estimates.  No numerical oracle is used.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

open scoped BigOperators

/-- A polynomial with a degree upper bound and a uniform absolute coefficient
bound.  These bounds compose without expanding the 12,000-term cleared
numerator. -/
private structure PolynomialBound (p : ℝ[X]) where
  degree : ℕ
  bound : ℝ
  degree_le : p.natDegree ≤ degree
  bound_nonneg : 0 ≤ bound
  coeff_abs_le : ∀ n, |p.coeff n| ≤ bound

namespace PolynomialBound

def C (c : ℝ) : PolynomialBound (Polynomial.C c) where
  degree := 0
  bound := |c|
  degree_le := by simp
  bound_nonneg := abs_nonneg c
  coeff_abs_le := by
    intro n
    by_cases h : n = 0
    · subst n
      simp
    · simp [Polynomial.coeff_C, h, abs_nonneg]

def X : PolynomialBound (Polynomial.X : ℝ[X]) where
  degree := 1
  bound := 1
  degree_le := by simp
  bound_nonneg := by norm_num
  coeff_abs_le := by
    intro n
    simp only [Polynomial.coeff_X]
    split <;> simp

def add {p q : ℝ[X]} (hp : PolynomialBound p) (hq : PolynomialBound q) :
    PolynomialBound (p + q) where
  degree := max hp.degree hq.degree
  bound := hp.bound + hq.bound
  degree_le := (Polynomial.natDegree_add_le p q).trans
    (max_le_max hp.degree_le hq.degree_le)
  bound_nonneg := add_nonneg hp.bound_nonneg hq.bound_nonneg
  coeff_abs_le := by
    intro n
    rw [Polynomial.coeff_add]
    exact (abs_add_le _ _).trans
      (add_le_add (hp.coeff_abs_le n) (hq.coeff_abs_le n))

def neg {p : ℝ[X]} (hp : PolynomialBound p) : PolynomialBound (-p) where
  degree := hp.degree
  bound := hp.bound
  degree_le := by simpa [Polynomial.natDegree_neg] using hp.degree_le
  bound_nonneg := hp.bound_nonneg
  coeff_abs_le := by
    intro n
    simpa using hp.coeff_abs_le n

def sub {p q : ℝ[X]} (hp : PolynomialBound p) (hq : PolynomialBound q) :
    PolynomialBound (p - q) where
  degree := max hp.degree hq.degree
  bound := hp.bound + hq.bound
  degree_le := (Polynomial.natDegree_sub_le p q).trans
    (max_le_max hp.degree_le hq.degree_le)
  bound_nonneg := add_nonneg hp.bound_nonneg hq.bound_nonneg
  coeff_abs_le := by
    intro n
    rw [Polynomial.coeff_sub]
    exact (abs_sub_le (p.coeff n) 0 (q.coeff n)).trans
      (by simpa using add_le_add (hp.coeff_abs_le n) (hq.coeff_abs_le n))

def mul {p q : ℝ[X]} (hp : PolynomialBound p) (hq : PolynomialBound q) :
    PolynomialBound (p * q) where
  degree := hp.degree + hq.degree
  bound := ((hp.degree + hq.degree + 1 : ℕ) : ℝ) * hp.bound * hq.bound
  degree_le := Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add hp.degree_le hq.degree_le)
  bound_nonneg := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) hp.bound_nonneg) hq.bound_nonneg
  coeff_abs_le := by
    intro n
    by_cases hn : n ≤ hp.degree + hq.degree
    · rw [Polynomial.coeff_mul]
      calc
        |∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            p.coeff x.1 * q.coeff x.2| ≤
            ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
              |p.coeff x.1 * q.coeff x.2| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x ∈ Finset.HasAntidiagonal.antidiagonal n,
              hp.bound * hq.bound := by
          apply Finset.sum_le_sum
          intro x hx
          rw [abs_mul]
          exact mul_le_mul (hp.coeff_abs_le x.1) (hq.coeff_abs_le x.2)
            (abs_nonneg _) hp.bound_nonneg
        _ = ((n + 1 : ℕ) : ℝ) * hp.bound * hq.bound := by
          simp [Finset.Nat.card_antidiagonal, nsmul_eq_mul, mul_assoc]
        _ ≤ ((hp.degree + hq.degree + 1 : ℕ) : ℝ) *
              hp.bound * hq.bound := by
          have hn' : ((n + 1 : ℕ) : ℝ) ≤
              ((hp.degree + hq.degree + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.add_le_add_right hn 1
          have hprod : 0 ≤ hp.bound * hq.bound :=
            mul_nonneg hp.bound_nonneg hq.bound_nonneg
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right hn' hprod
    · have hdeg : (p * q).natDegree < n :=
        lt_of_le_of_lt
          (Polynomial.natDegree_mul_le.trans
            (Nat.add_le_add hp.degree_le hq.degree_le))
          (Nat.lt_of_not_ge hn)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, abs_zero]
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) hp.bound_nonneg) hq.bound_nonneg

noncomputable def pow {p : ℝ[X]} (hp : PolynomialBound p) :
    (n : ℕ) → PolynomialBound (p ^ n)
  | 0 => by simpa using C 1
  | n + 1 => by simpa [pow_succ] using mul (pow hp n) hp

def divX {p : ℝ[X]} (hp : PolynomialBound p) : PolynomialBound p.divX where
  degree := hp.degree - 1
  bound := hp.bound
  degree_le := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_le_sub_right hp.degree_le 1
  bound_nonneg := hp.bound_nonneg
  coeff_abs_le := by
    intro n
    simpa only [Polynomial.coeff_divX] using hp.coeff_abs_le (n + 1)

theorem abs_eval_le {p : ℝ[X]} (hp : PolynomialBound p) {s : ℝ}
    (hs : |s| ≤ 1) :
    |p.eval s| ≤ (hp.degree + 1 : ℕ) * hp.bound := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp.degree_le)]
  calc
    |∑ i ∈ Finset.range (hp.degree + 1), p.coeff i * s ^ i| ≤
        ∑ i ∈ Finset.range (hp.degree + 1), |p.coeff i * s ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (hp.degree + 1), hp.bound := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow]
      have hpow : |s| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg s) hs
      simpa using mul_le_mul (hp.coeff_abs_le i) hpow
        (pow_nonneg (abs_nonneg s) i) hp.bound_nonneg
    _ = (hp.degree + 1 : ℕ) * hp.bound := by
      simp [nsmul_eq_mul]

end PolynomialBound

section FrozenPolynomial

set_option maxHeartbeats 0 in
private theorem frozenH3PathNumerator_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenH3PathNumerator q).eval s =
      (thirdRowNumerator (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) π).eval s := by
  simp [frozenH3PathNumerator, frozenAlgThirdNumerator,
    frozenAlgAreaNumerator, frozenAlgAreaL, frozenAlgAreaZ, frozenAlgAreaX,
    frozenAlgW, frozenAlgU, frozenAlgK, frozenAlgCosineNumerator,
    frozenAlgFoldNumerator, frozenAlgQPrime, frozenAlgDoubleB,
    frozenAlgDoubleE, frozenAlgR, frozenAlgA,
    thirdRowNumerator, areaNumerator, areaL, areaZ, areaX, W, U, K,
    cosineNumerator, foldNumerator, qPrime, B, E, R, A,
    thirdPhysicalZ, thirdPhysicalA, thirdPhysicalB]
  norm_num at ⊢
  ring

private theorem frozenH3PathPolynomial_eval {s : ℝ} (hs : s ≠ 0)
    (q : Fin 3 → ℝ) :
    (frozenH3PathPolynomial q).eval s =
      H3hatPolynomial s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) π := by
  have hpath := congrArg (Polynomial.eval s) (X_sq_mul_frozenH3PathPolynomial q)
  have horig := congrArg (Polynomial.eval s)
    (X_sq_mul_normalizedThirdRow (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q) π)
  simp only [eval_mul, eval_pow, eval_X] at hpath horig
  rw [frozenH3PathNumerator_eval] at hpath
  change s ^ 2 * (frozenH3PathPolynomial q).eval s = _ at hpath
  change s ^ 2 * H3hatPolynomial s (thirdPhysicalZ s q)
    (thirdPhysicalA s q) (thirdPhysicalB s q) π = _ at horig
  exact mul_left_cancel₀ (pow_ne_zero 2 hs) (hpath.trans horig.symm)


@[simp] private theorem frozenPathA_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathA q).eval s = aCoord s (thirdPhysicalZ s q) := by
  simp [frozenPathA, frozenAlgA, aCoord, thirdPhysicalZ]

@[simp] private theorem frozenPathR_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathR q).eval s = rCoord s (thirdPhysicalA s q) := by
  simp [frozenPathR, frozenAlgR, rCoord, thirdPhysicalA]

@[simp] private theorem frozenPathE_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathE q).eval s =
      eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) := by
  simp [frozenPathE, frozenAlgE, eCoord, thirdPhysicalZ,
    thirdPhysicalA, thirdPhysicalB]

@[simp] private theorem frozenPathY_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathY q).eval s = yCoord s (thirdPhysicalZ s q) := by
  simp [frozenPathY, yCoord]

@[simp] private theorem frozenPathW_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathW q).eval s = wCoord s (thirdPhysicalA s q) := by
  simp [frozenPathW, wCoord]

@[simp] private theorem frozenPathV_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathV q).eval s =
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) := by
  simp [frozenPathV, vCoord]

@[simp] private theorem frozenPathD4_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathD4 q).eval s =
      1 + s * yCoord s (thirdPhysicalZ s q) := by
  simp [frozenPathD4]

@[simp] private theorem frozenPathD3_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathD3 q).eval s =
      1 + wCoord s (thirdPhysicalA s q) *
        vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) := by
  simp [frozenPathD3]

@[simp] private theorem frozenPathDensityDenominator_eval
    (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathDensityDenominator q).eval s =
      (1 + s ^ 2) * (1 - yCoord s (thirdPhysicalZ s q) ^ 2) := by
  simp [frozenPathDensityDenominator]

@[simp] private theorem frozenPathCommonDenominator_eval
    (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenPathCommonDenominator q).eval s =
      3 * ((1 + s ^ 2) * (1 - yCoord s (thirdPhysicalZ s q) ^ 2)) *
        (1 + wCoord s (thirdPhysicalA s q) *
          vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q)) ^ 3 *
        (1 + s * yCoord s (thirdPhysicalZ s q)) ^ 3 := by
  simp [frozenPathCommonDenominator]

/-- The cleared frozen-row denominator stays uniformly away from zero on the
relaxed endpoint box. -/
theorem frozenPathCommonDenominator_lower_bound {s : ℝ}
    (q : Fin 3 → ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq : InEndpointBox q) :
    3 * (1 - (2 / 126334 : ℝ) ^ 2) ≤
      (frozenPathCommonDenominator q).eval s := by
  rcases explicit_third_path_geometry q hs0 hs hq with
    ⟨_hz0, _hz1, _ha0, _ha1, _hb, _hr0, _hr1, _he,
      hy0, hyByS, _hw0, _hw1, _hv0, _hv1, hd4, hd3⟩
  have hy1 : yCoord s (thirdPhysicalZ s q) ≤ 2 / 126334 := by
    nlinarith
  have hsum : 0 ≤ (2 / 126334 : ℝ) +
      yCoord s (thirdPhysicalZ s q) := by nlinarith
  have hySq : yCoord s (thirdPhysicalZ s q) ^ 2 ≤
      (2 / 126334 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hy1) hsum]
  have hyFactor :
      0 ≤ 1 - yCoord s (thirdPhysicalZ s q) ^ 2 := by nlinarith
  have hDensity : 1 - (2 / 126334 : ℝ) ^ 2 ≤
      (1 + s ^ 2) *
        (1 - yCoord s (thirdPhysicalZ s q) ^ 2) := by
    calc
      1 - (2 / 126334 : ℝ) ^ 2 ≤
          1 - yCoord s (thirdPhysicalZ s q) ^ 2 := by nlinarith
      _ = 1 * (1 - yCoord s (thirdPhysicalZ s q) ^ 2) := by ring
      _ ≤ (1 + s ^ 2) *
          (1 - yCoord s (thirdPhysicalZ s q) ^ 2) :=
        mul_le_mul_of_nonneg_right
          (by nlinarith [sq_nonneg s]) hyFactor
  have hd3pow : (1 : ℝ) ≤
      (1 + wCoord s (thirdPhysicalA s q) *
        vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q)) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd3 3
  have hd4pow : (1 : ℝ) ≤
      (1 + s * yCoord s (thirdPhysicalZ s q)) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd4 3
  have hDensity0 : 0 ≤
      (1 + s ^ 2) *
        (1 - yCoord s (thirdPhysicalZ s q) ^ 2) :=
    mul_nonneg (by positivity) hyFactor
  rw [frozenPathCommonDenominator_eval]
  calc
    3 * (1 - (2 / 126334 : ℝ) ^ 2) ≤
        3 * ((1 + s ^ 2) *
          (1 - yCoord s (thirdPhysicalZ s q) ^ 2)) :=
      mul_le_mul_of_nonneg_left hDensity (by norm_num)
    _ ≤ 3 * ((1 + s ^ 2) *
          (1 - yCoord s (thirdPhysicalZ s q) ^ 2)) *
        (1 + wCoord s (thirdPhysicalA s q) *
          vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q)) ^ 3 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hd3pow
          (mul_nonneg (by norm_num) hDensity0)
    _ ≤ 3 * ((1 + s ^ 2) *
          (1 - yCoord s (thirdPhysicalZ s q) ^ 2)) *
        (1 + wCoord s (thirdPhysicalA s q) *
          vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q)) ^ 3 *
        (1 + s * yCoord s (thirdPhysicalZ s q)) ^ 3 := by
      have hleft : 0 ≤ 3 * ((1 + s ^ 2) *
          (1 - yCoord s (thirdPhysicalZ s q) ^ 2)) *
        (1 + wCoord s (thirdPhysicalA s q) *
          vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q)) ^ 3 :=
        mul_nonneg (mul_nonneg (by norm_num) hDensity0) (by linarith)
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hd4pow hleft

set_option maxHeartbeats 0 in
private theorem frozenPathFourBarNumerator_eval {s : ℝ}
    (q : Fin 3 → ℝ)
    (hy : 1 - yCoord s (thirdPhysicalZ s q) ^ 2 ≠ 0)
    (hd : 1 + s * yCoord s (thirdPhysicalZ s q) ≠ 0) :
    (frozenPathFourBarNumerator q).eval s =
      (3 * frozenPathDensityDenominator q * frozenPathD4 q ^ 3).eval s *
        thirdFourBarFrozen s (thirdPhysicalZ s q) := by
  simp [frozenPathFourBarNumerator, frozenPathDensityNumerator,
    frozenPathRhoNumerator, frozenPathFourIncrementNumerator,
    thirdFourBarFrozen, thirdFourIncrementFrozen, densityCubeQuotient,
    density, halfCos, -tangentCenteredPoint_rescaled_zeroCoord]
  have hz : tangentCenteredPoint s (fun j => s ^ 2 * q j) 0 =
      thirdPhysicalZ s q := rfl
  rw [hz]
  field_simp [hy, hd, show 1 + s ^ 2 ≠ 0 by positivity]
  ring

set_option maxHeartbeats 0 in
private theorem frozenPathThreeBarNumerator_eval {s : ℝ}
    (q : Fin 3 → ℝ)
    (hy : 1 - yCoord s (thirdPhysicalZ s q) ^ 2 ≠ 0)
    (hd : 1 + wCoord s (thirdPhysicalA s q) *
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) ≠ 0) :
    (frozenPathThreeBarNumerator q).eval s =
      (3 * frozenPathDensityDenominator q * frozenPathD3 q ^ 3).eval s *
        thirdThreeBarFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) := by
  simp [frozenPathThreeBarNumerator, frozenPathDensityNumerator,
    frozenPathRhoNumerator, frozenPathThreeIncrementNumerator,
    thirdThreeBarFrozen, thirdThreeIncrementFrozen, densityCubeQuotient,
    density, halfCos, -tangentCenteredPoint_rescaled_zeroCoord]
  have hz : tangentCenteredPoint s (fun j => s ^ 2 * q j) 0 =
      thirdPhysicalZ s q := rfl
  rw [hz]
  field_simp [hy, hd, show 1 + s ^ 2 ≠ 0 by positivity]
  ring

@[simp] private theorem frozenAlgK_eval (s : ℝ) (q : Fin 3 → ℝ) :
    (frozenAlgK (rescaledAPathPolynomial q)).eval s =
      (NearOneNormalizedFlow.K (thirdPhysicalA s q)).eval s := by
  simp [frozenAlgK, frozenAlgR, NearOneNormalizedFlow.K,
    NearOneNormalizedFlow.R, thirdPhysicalA]
  ring

set_option maxHeartbeats 0 in
private theorem frozenPathCommonNumerator_eval {s : ℝ} (hs : s ≠ 0)
    (q : Fin 3 → ℝ)
    (hy : 1 - yCoord s (thirdPhysicalZ s q) ^ 2 ≠ 0)
    (hd4 : 1 + s * yCoord s (thirdPhysicalZ s q) ≠ 0)
    (hd3 : 1 + wCoord s (thirdPhysicalA s q) *
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) ≠ 0) :
    (frozenPathCommonNumerator q).eval s =
      (frozenPathCommonDenominator q).eval s *
        thirdRegularizedFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) := by
  rw [show (frozenPathCommonNumerator q).eval s =
      (frozenPathCommonDenominator q).eval s *
          (frozenH3PathPolynomial q).eval s +
        (frozenPathD4 q ^ 3).eval s *
          (frozenPathThreeCoefficient q).eval s *
            (frozenPathThreeBarNumerator q).eval s +
        (frozenPathD3 q ^ 3).eval s *
          (frozenPathFourCoefficient q).eval s *
            (frozenPathFourBarNumerator q).eval s +
        (frozenPathCommonDenominator q).eval s *
          (frozenPathPiCoefficient q).eval s +
        (frozenPathCommonDenominator q).eval s *
          (frozenPathFoldCoefficient q).eval s *
            (2 * rescaledZPathPolynomial q).eval s +
        (frozenPathD3 q ^ 3).eval s *
          (frozenPathFoldCoefficient q).eval s * (X ^ 2).eval s *
            (frozenPathFourBarNumerator q).eval s by
      simp [frozenPathCommonNumerator]]
  rw [frozenH3PathPolynomial_eval hs q,
    frozenPathThreeBarNumerator_eval q hy hd3,
    frozenPathFourBarNumerator_eval q hy hd4]
  simp [thirdRegularizedFrozen, frozenPathThreeCoefficient,
    frozenPathFourCoefficient, frozenPathPiCoefficient,
    frozenPathFoldCoefficient, areaDenominator, foldDenominator,
    typeFourSineProductBar, areaPiWeight, halfCos,
    -tangentCenteredPoint_rescaled_zeroCoord]
  have hz : tangentCenteredPoint s (fun j => s ^ 2 * q j) 0 =
      thirdPhysicalZ s q := rfl
  rw [hz]
  field_simp [show 1 + s ^ 2 ≠ 0 by positivity,
    show 1 + wCoord s (thirdPhysicalA s q) ^ 2 ≠ 0 by positivity,
    show 1 + yCoord s (thirdPhysicalZ s q) ^ 2 ≠ 0 by positivity]
  ring

/-- Evaluation of the exact cleared error is the common denominator times the
frozen-row approximation error. -/
theorem frozenPathClearedError_eval {s : ℝ} (hs : s ≠ 0)
    (q : Fin 3 → ℝ)
    (hy : 1 - yCoord s (thirdPhysicalZ s q) ^ 2 ≠ 0)
    (hd4 : 1 + s * yCoord s (thirdPhysicalZ s q) ≠ 0)
    (hd3 : 1 + wCoord s (thirdPhysicalA s q) *
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) ≠ 0) :
    (frozenPathClearedError q).eval s =
      (frozenPathCommonDenominator q).eval s *
        (thirdRegularizedFrozen s (thirdPhysicalZ s q)
            (thirdPhysicalA s q) (thirdPhysicalB s q) -
          s ^ 2 * frozenEndpointQuadratic q) := by
  rw [frozenPathClearedError, eval_sub, eval_mul,
    frozenPathCommonNumerator_eval hs q hy hd4 hd3]
  simp
  ring

/-- A scale-aware bound for the cubic quotient of the cleared error. The
cancellation-aware cubic coefficient estimate and sharpened fourth-order
majorant give a bound below 1.52 million on the common face radius. -/
def ExplicitThirdClearedErrorBound : Prop :=
  ∀ s, 0 < s → s ≤ 1 / 126334 →
    ∀ q, InEndpointBox q →
      |((frozenPathClearedError q).divX.divX.divX).eval s| ≤ 1515627

/-- The cleared-error quotient bound is sufficient for the rational frozen-row
estimate required by the six-face theorem. -/
theorem explicitThirdFrozenEstimate_of_cleared_error_bound
    (hquotient : ExplicitThirdClearedErrorBound) :
    ExplicitThirdFrozenEstimate := by
  intro s hspos hs q hq
  have hs0 : 0 ≤ s := hspos.le
  rcases explicit_third_path_geometry q hs0 hs hq with
    ⟨_hz0, _hz1, _ha0, _ha1, _hb, _hr0, _hr1, _he,
      hy0, hy1, _hw0, _hw1, _hv0, _hv1, hd4, hd3⟩
  have hyne :
      1 - yCoord s (thirdPhysicalZ s q) ^ 2 ≠ 0 := by
    have hySq :
        yCoord s (thirdPhysicalZ s q) ^ 2 <
          (1 : ℝ) := by nlinarith
    nlinarith
  have hd4ne :
      1 + s * yCoord s (thirdPhysicalZ s q) ≠ 0 := by
    nlinarith
  have hd3ne :
      1 + wCoord s (thirdPhysicalA s q) *
        vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) ≠ 0 := by
    nlinarith
  let D := (frozenPathCommonDenominator q).eval s
  let F := thirdRegularizedFrozen s (thirdPhysicalZ s q)
    (thirdPhysicalA s q) (thirdPhysicalB s q)
  let Q := frozenEndpointQuadratic q
  let T := ((frozenPathClearedError q).divX.divX.divX).eval s
  have hD :
      3 * (1 - (2 / 126334 : ℝ) ^ 2) ≤ D := by
    simpa [D] using frozenPathCommonDenominator_lower_bound q hs0 hs hq
  have hDpos : 0 < D := by
    have : (0 : ℝ) < 3 * (1 - (2 / 126334 : ℝ) ^ 2) := by norm_num
    exact this.trans_le hD
  have hcleared :
      (frozenPathClearedError q).eval s = D * (F - s ^ 2 * Q) := by
    simpa [D, F, Q] using
      frozenPathClearedError_eval hspos.ne' q hyne hd4ne hd3ne
  have hfactor := congrArg (Polynomial.eval s)
    (X_cube_mul_frozenPathClearedError_divX_divX_divX q)
  simp only [eval_mul, eval_pow, eval_X] at hfactor
  have hdiff : F - s ^ 2 * Q = s ^ 3 * T / D := by
    apply (eq_div_iff hDpos.ne').2
    calc
      (F - s ^ 2 * Q) * D = D * (F - s ^ 2 * Q) := by ring
      _ = (frozenPathClearedError q).eval s := hcleared.symm
      _ = s ^ 3 * T := by simpa only [T] using hfactor.symm
  have hT : |T| ≤ 1515627 := by
    simpa [T] using hquotient s hspos hs q hq
  have hsT : s * |T| ≤ (1515627 / 126334 : ℝ) := by
    have := mul_le_mul hs hT (abs_nonneg T) (by norm_num)
    norm_num at this ⊢
    exact this
  have hslack :
      (3999 / 1000 : ℝ) * (3 * (1 - (2 / 126334 : ℝ) ^ 2)) -
          1515627 / 126334 =
        366813 / 23198080750 := by
    norm_num
  have hslackpos : (0 : ℝ) < 366813 / 23198080750 := by norm_num
  have hcore : s * |T| < (3999 / 1000 : ℝ) * D := by
    nlinarith
  have hscaled :
      s ^ 3 * |T| < (3999 / 1000 : ℝ) * s ^ 2 * D := by
    have := mul_lt_mul_of_pos_left hcore (sq_pos_of_pos hspos)
    nlinarith
  change |F - s ^ 2 * Q| < (3999 / 1000 : ℝ) * s ^ 2
  rw [hdiff, abs_div, abs_mul, abs_pow, abs_of_pos hspos, abs_of_pos hDpos,
    div_lt_iff₀ hDpos]
  nlinarith


end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
