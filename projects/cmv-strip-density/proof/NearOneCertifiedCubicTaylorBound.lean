/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneCubicTaylorBound

/-!
A coefficient-certified wrapper for the compositional cubic Taylor bound.
-/

namespace NearOneRegularizedThirdRow
namespace NearOneRescaledFirstCell

open Polynomial

noncomputable section

/-- A cubic Taylor bound whose recorded cubic jet is the actual initial
coefficient segment of the polynomial. -/
structure CertifiedCubicTaylorBound (p : Polynomial ℝ)
    extends CubicTaylorBound p where
  c0_eq_coeff : c0 = p.coeff 0
  c1_eq_coeff : c1 = p.coeff 1
  c2_eq_coeff : c2 = p.coeff 2
  c3_eq_coeff : c3 = p.coeff 3

namespace CertifiedCubicTaylorBound

/-- The underlying (uncertified) Taylor bound. -/
abbrev bound {p : Polynomial ℝ} (P : CertifiedCubicTaylorBound p) :
    CubicTaylorBound p := P.toCubicTaylorBound

/-- A certified bound for a constant polynomial. -/
def const (a : ℝ) : CertifiedCubicTaylorBound (C a) where
  toCubicTaylorBound := CubicTaylorBound.const a
  c0_eq_coeff := by simp [CubicTaylorBound.const]
  c1_eq_coeff := by simp [CubicTaylorBound.const]
  c2_eq_coeff := by simp [CubicTaylorBound.const]
  c3_eq_coeff := by simp [CubicTaylorBound.const]

/-- A certified bound for the polynomial variable. -/
def X : CertifiedCubicTaylorBound (X : Polynomial ℝ) where
  toCubicTaylorBound := CubicTaylorBound.X
  c0_eq_coeff := by simp [CubicTaylorBound.X]
  c1_eq_coeff := by simp [CubicTaylorBound.X]
  c2_eq_coeff := by norm_num [CubicTaylorBound.X, coeff_X]
  c3_eq_coeff := by norm_num [CubicTaylorBound.X, coeff_X]

/-- Addition preserves coefficient certification. -/
def add {p q : Polynomial ℝ} (P : CertifiedCubicTaylorBound p)
    (Q : CertifiedCubicTaylorBound q) : CertifiedCubicTaylorBound (p + q) where
  toCubicTaylorBound := P.bound.add Q.bound
  c0_eq_coeff := by simp [CubicTaylorBound.add, P.c0_eq_coeff, Q.c0_eq_coeff]
  c1_eq_coeff := by simp [CubicTaylorBound.add, P.c1_eq_coeff, Q.c1_eq_coeff]
  c2_eq_coeff := by simp [CubicTaylorBound.add, P.c2_eq_coeff, Q.c2_eq_coeff]
  c3_eq_coeff := by simp [CubicTaylorBound.add, P.c3_eq_coeff, Q.c3_eq_coeff]

/-- Negation preserves coefficient certification. -/
def neg {p : Polynomial ℝ} (P : CertifiedCubicTaylorBound p) :
    CertifiedCubicTaylorBound (-p) where
  toCubicTaylorBound := P.bound.neg
  c0_eq_coeff := by simp [CubicTaylorBound.neg, P.c0_eq_coeff]
  c1_eq_coeff := by simp [CubicTaylorBound.neg, P.c1_eq_coeff]
  c2_eq_coeff := by simp [CubicTaylorBound.neg, P.c2_eq_coeff]
  c3_eq_coeff := by simp [CubicTaylorBound.neg, P.c3_eq_coeff]

/-- Subtraction preserves coefficient certification. -/
def sub {p q : Polynomial ℝ} (P : CertifiedCubicTaylorBound p)
    (Q : CertifiedCubicTaylorBound q) : CertifiedCubicTaylorBound (p - q) := by
  simpa [sub_eq_add_neg] using P.add Q.neg

/-- Multiplication preserves coefficient certification. -/
def mul {p q : Polynomial ℝ} (P : CertifiedCubicTaylorBound p)
    (Q : CertifiedCubicTaylorBound q) : CertifiedCubicTaylorBound (p * q) where
  toCubicTaylorBound := P.bound.mul Q.bound
  c0_eq_coeff := by
    simp only [CubicTaylorBound.mul, P.c0_eq_coeff, Q.c0_eq_coeff]
    exact (Polynomial.mul_coeff_zero p q).symm
  c1_eq_coeff := by
    simp only [CubicTaylorBound.mul, P.c0_eq_coeff, P.c1_eq_coeff,
      Q.c0_eq_coeff, Q.c1_eq_coeff]
    exact (Polynomial.mul_coeff_one p q).symm
  c2_eq_coeff := by
    simp only [CubicTaylorBound.mul, P.c0_eq_coeff, P.c1_eq_coeff, P.c2_eq_coeff,
      Q.c0_eq_coeff, Q.c1_eq_coeff, Q.c2_eq_coeff, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
  c3_eq_coeff := by
    simp only [CubicTaylorBound.mul, P.c0_eq_coeff, P.c1_eq_coeff, P.c2_eq_coeff,
      P.c3_eq_coeff, Q.c0_eq_coeff, Q.c1_eq_coeff, Q.c2_eq_coeff,
      Q.c3_eq_coeff, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]

/-- Natural powers, constructed compositionally from multiplication. -/
def pow {p : Polynomial ℝ} (P : CertifiedCubicTaylorBound p) :
    (n : ℕ) → CertifiedCubicTaylorBound (p ^ n)
  | 0 => const 1
  | n + 1 => (pow P n).mul P

/-- Replace all recorded majorants by specified larger nonnegative values. -/
def widen {p : Polynomial ℝ} (P : CertifiedCubicTaylorBound p)
    (b0 b1 b2 b3 remainder : ℝ)
    (hb0_nonneg : 0 ≤ b0) (hb1_nonneg : 0 ≤ b1)
    (hb2_nonneg : 0 ≤ b2) (hb3_nonneg : 0 ≤ b3)
    (hremainder_nonneg : 0 ≤ remainder)
    (hb0 : P.b0 ≤ b0) (hb1 : P.b1 ≤ b1)
    (hb2 : P.b2 ≤ b2) (hb3 : P.b3 ≤ b3)
    (hremainder : P.remainder ≤ remainder) : CertifiedCubicTaylorBound p where
  toCubicTaylorBound := {
    c0 := P.c0
    c1 := P.c1
    c2 := P.c2
    c3 := P.c3
    b0 := b0
    b1 := b1
    b2 := b2
    b3 := b3
    remainder := remainder
    b0_nonneg := hb0_nonneg
    b1_nonneg := hb1_nonneg
    b2_nonneg := hb2_nonneg
    b3_nonneg := hb3_nonneg
    remainder_nonneg := hremainder_nonneg
    abs_c0_le := P.abs_c0_le.trans hb0
    abs_c1_le := P.abs_c1_le.trans hb1
    abs_c2_le := P.abs_c2_le.trans hb2
    abs_c3_le := P.abs_c3_le.trans hb3
    remainder_bound := by
      intro s hs
      exact (P.remainder_bound s hs).trans
        (mul_le_mul_of_nonneg_right hremainder (by positivity)) }
  c0_eq_coeff := P.c0_eq_coeff
  c1_eq_coeff := P.c1_eq_coeff
  c2_eq_coeff := P.c2_eq_coeff
  c3_eq_coeff := P.c3_eq_coeff

private theorem eval_eq_cubic_add_tail (p : Polynomial ℝ) (s : ℝ) :
    p.eval s = p.coeff 0 + p.coeff 1 * s + p.coeff 2 * s ^ 2 +
      p.coeff 3 * s ^ 3 + s ^ 4 * p.divX.divX.divX.divX.eval s := by
  have h0 := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add p)
  have h1 := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add p.divX)
  have h2 := congrArg (Polynomial.eval s) (Polynomial.X_mul_divX_add p.divX.divX)
  have h3 := congrArg (Polynomial.eval s)
    (Polynomial.X_mul_divX_add p.divX.divX.divX)
  simp only [eval_add, eval_mul, eval_X, eval_C, coeff_divX] at h0 h1 h2 h3
  rw [← h0, ← h1, ← h2, ← h3]
  ring

/-- At the fixed radius, the fourth divided tail is bounded by the certified
remainder. -/
theorem abs_divX_four_eval_cubicTaylorRadius_le {p : Polynomial ℝ}
    (P : CertifiedCubicTaylorBound p) :
    |p.divX.divX.divX.divX.eval cubicTaylorRadius| ≤ P.remainder := by
  have hr : 0 < cubicTaylorRadius := by norm_num [cubicTaylorRadius]
  have h := P.remainder_bound cubicTaylorRadius (by
    rw [abs_of_pos hr])
  rw [P.c0_eq_coeff, P.c1_eq_coeff, P.c2_eq_coeff, P.c3_eq_coeff,
    eval_eq_cubic_add_tail] at h
  rw [show p.coeff 0 + p.coeff 1 * cubicTaylorRadius +
      p.coeff 2 * cubicTaylorRadius ^ 2 + p.coeff 3 * cubicTaylorRadius ^ 3 +
      cubicTaylorRadius ^ 4 * p.divX.divX.divX.divX.eval cubicTaylorRadius -
      (p.coeff 0 + p.coeff 1 * cubicTaylorRadius +
        p.coeff 2 * cubicTaylorRadius ^ 2 + p.coeff 3 * cubicTaylorRadius ^ 3) =
      cubicTaylorRadius ^ 4 * p.divX.divX.divX.divX.eval cubicTaylorRadius by ring] at h
  rw [abs_mul, abs_pow, abs_of_pos hr] at h
  have hr4 : 0 < cubicTaylorRadius ^ 4 := pow_pos hr 4
  nlinarith

end CertifiedCubicTaylorBound

end
end NearOneRescaledFirstCell
end NearOneRegularizedThirdRow
