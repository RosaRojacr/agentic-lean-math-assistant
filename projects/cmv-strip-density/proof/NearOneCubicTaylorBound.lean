/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib

/-!
A compositional, fixed-radius cubic Taylor majorant for real polynomials.
-/

namespace NearOneRegularizedThirdRow
namespace NearOneRescaledFirstCell

open Polynomial

noncomputable section

/-- The radius used by the near-one polynomial estimates. -/
def cubicTaylorRadius : ℝ := 1 / 1000000

@[simp] theorem cubicTaylorRadius_nonneg : 0 ≤ cubicTaylorRadius := by
  norm_num [cubicTaylorRadius]

/-- Exact cubic jet data, coefficient majorants, and a certified fourth-order
remainder for a real polynomial on the fixed near-one radius. -/
structure CubicTaylorBound (p : Polynomial ℝ) where
  c0 : ℝ
  c1 : ℝ
  c2 : ℝ
  c3 : ℝ
  b0 : ℝ
  b1 : ℝ
  b2 : ℝ
  b3 : ℝ
  remainder : ℝ
  b0_nonneg : 0 ≤ b0
  b1_nonneg : 0 ≤ b1
  b2_nonneg : 0 ≤ b2
  b3_nonneg : 0 ≤ b3
  remainder_nonneg : 0 ≤ remainder
  abs_c0_le : |c0| ≤ b0
  abs_c1_le : |c1| ≤ b1
  abs_c2_le : |c2| ≤ b2
  abs_c3_le : |c3| ≤ b3
  remainder_bound : ∀ s : ℝ, |s| ≤ cubicTaylorRadius →
    |p.eval s - (c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3)| ≤
      remainder * |s| ^ 4

namespace CubicTaylorBound

/-- The exact cubic jet represented by a bound. -/
def jet {p : Polynomial ℝ} (P : CubicTaylorBound p) (s : ℝ) : ℝ :=
  P.c0 + P.c1 * s + P.c2 * s ^ 2 + P.c3 * s ^ 3

/-- Radius-weighted norm of the coefficient majorants. -/
def jetNorm {p : Polynomial ℝ} (P : CubicTaylorBound p) : ℝ :=
  P.b0 + cubicTaylorRadius * P.b1 + cubicTaylorRadius ^ 2 * P.b2 +
    cubicTaylorRadius ^ 3 * P.b3

@[simp] theorem jetNorm_nonneg {p : Polynomial ℝ} (P : CubicTaylorBound p) :
    0 ≤ P.jetNorm := by
  unfold jetNorm
  exact add_nonneg
    (add_nonneg
      (add_nonneg P.b0_nonneg
        (mul_nonneg cubicTaylorRadius_nonneg P.b1_nonneg))
      (mul_nonneg (sq_nonneg cubicTaylorRadius) P.b2_nonneg))
    (mul_nonneg (pow_nonneg cubicTaylorRadius_nonneg 3) P.b3_nonneg)

/-- The radius-weighted degree-four-through-six tail of a product of cubic
jets. -/
def productJetTail {p q : Polynomial ℝ}
    (P : CubicTaylorBound p) (Q : CubicTaylorBound q) : ℝ :=
  (P.b1 * Q.b3 + P.b2 * Q.b2 + P.b3 * Q.b1) +
    cubicTaylorRadius * (P.b2 * Q.b3 + P.b3 * Q.b2) +
    cubicTaylorRadius ^ 2 * (P.b3 * Q.b3)

@[simp] theorem productJetTail_nonneg {p q : Polynomial ℝ}
    (P : CubicTaylorBound p) (Q : CubicTaylorBound q) :
    0 ≤ P.productJetTail Q := by
  unfold productJetTail
  have h4 : 0 ≤ P.b1 * Q.b3 + P.b2 * Q.b2 + P.b3 * Q.b1 :=
    add_nonneg
      (add_nonneg
        (mul_nonneg P.b1_nonneg Q.b3_nonneg)
        (mul_nonneg P.b2_nonneg Q.b2_nonneg))
      (mul_nonneg P.b3_nonneg Q.b1_nonneg)
  have h5 : 0 ≤ P.b2 * Q.b3 + P.b3 * Q.b2 :=
    add_nonneg
      (mul_nonneg P.b2_nonneg Q.b3_nonneg)
      (mul_nonneg P.b3_nonneg Q.b2_nonneg)
  have h6 : 0 ≤ P.b3 * Q.b3 := mul_nonneg P.b3_nonneg Q.b3_nonneg
  exact add_nonneg (add_nonneg h4 (mul_nonneg cubicTaylorRadius_nonneg h5))
    (mul_nonneg (sq_nonneg cubicTaylorRadius) h6)

/-- The product remainder: the truncated-jet tail, the two jet/remainder
cross terms, and the remainder/remainder term. -/
def productRemainder {p q : Polynomial ℝ}
    (P : CubicTaylorBound p) (Q : CubicTaylorBound q) : ℝ :=
  P.productJetTail Q + P.remainder * Q.jetNorm + P.jetNorm * Q.remainder +
    cubicTaylorRadius ^ 4 * P.remainder * Q.remainder

@[simp] theorem productRemainder_nonneg {p q : Polynomial ℝ}
    (P : CubicTaylorBound p) (Q : CubicTaylorBound q) :
    0 ≤ P.productRemainder Q := by
  unfold productRemainder
  exact add_nonneg
    (add_nonneg
      (add_nonneg (productJetTail_nonneg P Q)
        (mul_nonneg P.remainder_nonneg (jetNorm_nonneg Q)))
      (mul_nonneg (jetNorm_nonneg P) Q.remainder_nonneg))
    (mul_nonneg
      (mul_nonneg (by positivity) P.remainder_nonneg) Q.remainder_nonneg)

lemma abs_pow_le_radius_pow {s : ℝ} (hs : |s| ≤ cubicTaylorRadius) (n : ℕ) :
    |s| ^ n ≤ cubicTaylorRadius ^ n := by
  exact pow_le_pow_left₀ (abs_nonneg s) hs n

/-- A cubic jet is bounded by its radius-weighted coefficient norm. -/
theorem abs_jet_le_jetNorm {p : Polynomial ℝ} (P : CubicTaylorBound p)
    {s : ℝ} (hs : |s| ≤ cubicTaylorRadius) :
    |P.jet s| ≤ P.jetNorm := by
  have hs2 := abs_pow_le_radius_pow hs 2
  have hs3 := abs_pow_le_radius_pow hs 3
  have h0 : |P.c0| ≤ P.b0 := P.abs_c0_le
  have h1 : |P.c1 * s| ≤ P.b1 * cubicTaylorRadius := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c1_le hs (abs_nonneg s) P.b1_nonneg
  have h2 : |P.c2 * s ^ 2| ≤ P.b2 * cubicTaylorRadius ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul P.abs_c2_le hs2 (by positivity) P.b2_nonneg
  have h3 : |P.c3 * s ^ 3| ≤ P.b3 * cubicTaylorRadius ^ 3 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul P.abs_c3_le hs3 (by positivity) P.b3_nonneg
  calc
    |P.jet s| ≤ |P.c0 + P.c1 * s + P.c2 * s ^ 2| + |P.c3 * s ^ 3| := by
      unfold jet
      exact abs_add_le _ _
    _ ≤ (|P.c0 + P.c1 * s| + |P.c2 * s ^ 2|) + |P.c3 * s ^ 3| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (|P.c0| + |P.c1 * s|) + |P.c2 * s ^ 2| + |P.c3 * s ^ 3| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ P.b0 + P.b1 * cubicTaylorRadius + P.b2 * cubicTaylorRadius ^ 2 +
          P.b3 * cubicTaylorRadius ^ 3 := by gcongr
    _ = P.jetNorm := by unfold jetNorm; ring

/-- Constant-polynomial constructor. -/
def const (a : ℝ) : CubicTaylorBound (C a) where
  c0 := a
  c1 := 0
  c2 := 0
  c3 := 0
  b0 := |a|
  b1 := 0
  b2 := 0
  b3 := 0
  remainder := 0
  b0_nonneg := abs_nonneg a
  b1_nonneg := le_rfl
  b2_nonneg := le_rfl
  b3_nonneg := le_rfl
  remainder_nonneg := le_rfl
  abs_c0_le := le_rfl
  abs_c1_le := by simp
  abs_c2_le := by simp
  abs_c3_le := by simp
  remainder_bound := by simp

/-- The polynomial variable. -/
def X : CubicTaylorBound (X : Polynomial ℝ) where
  c0 := 0
  c1 := 1
  c2 := 0
  c3 := 0
  b0 := 0
  b1 := 1
  b2 := 0
  b3 := 0
  remainder := 0
  b0_nonneg := le_rfl
  b1_nonneg := by norm_num
  b2_nonneg := le_rfl
  b3_nonneg := le_rfl
  remainder_nonneg := le_rfl
  abs_c0_le := by simp
  abs_c1_le := by norm_num
  abs_c2_le := by simp
  abs_c3_le := by simp
  remainder_bound := by simp

/-- Direct constructor for an exact quadratic polynomial. -/
def quadratic (a b c : ℝ) :
    CubicTaylorBound (C a + C b * Polynomial.X + C c * Polynomial.X ^ 2) where
  c0 := a
  c1 := b
  c2 := c
  c3 := 0
  b0 := |a|
  b1 := |b|
  b2 := |c|
  b3 := 0
  remainder := 0
  b0_nonneg := abs_nonneg a
  b1_nonneg := abs_nonneg b
  b2_nonneg := abs_nonneg c
  b3_nonneg := le_rfl
  remainder_nonneg := le_rfl
  abs_c0_le := le_rfl
  abs_c1_le := le_rfl
  abs_c2_le := le_rfl
  abs_c3_le := by simp
  remainder_bound := by
    intro s hs
    simp

/-- Addition of certified cubic Taylor bounds. -/
def add {p q : Polynomial ℝ} (P : CubicTaylorBound p) (Q : CubicTaylorBound q) :
    CubicTaylorBound (p + q) where
  c0 := P.c0 + Q.c0
  c1 := P.c1 + Q.c1
  c2 := P.c2 + Q.c2
  c3 := P.c3 + Q.c3
  b0 := P.b0 + Q.b0
  b1 := P.b1 + Q.b1
  b2 := P.b2 + Q.b2
  b3 := P.b3 + Q.b3
  remainder := P.remainder + Q.remainder
  b0_nonneg := add_nonneg P.b0_nonneg Q.b0_nonneg
  b1_nonneg := add_nonneg P.b1_nonneg Q.b1_nonneg
  b2_nonneg := add_nonneg P.b2_nonneg Q.b2_nonneg
  b3_nonneg := add_nonneg P.b3_nonneg Q.b3_nonneg
  remainder_nonneg := add_nonneg P.remainder_nonneg Q.remainder_nonneg
  abs_c0_le := (abs_add_le _ _).trans (add_le_add P.abs_c0_le Q.abs_c0_le)
  abs_c1_le := (abs_add_le _ _).trans (add_le_add P.abs_c1_le Q.abs_c1_le)
  abs_c2_le := (abs_add_le _ _).trans (add_le_add P.abs_c2_le Q.abs_c2_le)
  abs_c3_le := (abs_add_le _ _).trans (add_le_add P.abs_c3_le Q.abs_c3_le)
  remainder_bound := by
    intro s hs
    have hP := P.remainder_bound s hs
    have hQ := Q.remainder_bound s hs
    rw [eval_add]
    rw [show p.eval s + q.eval s -
        ((P.c0 + Q.c0) + (P.c1 + Q.c1) * s +
          (P.c2 + Q.c2) * s ^ 2 + (P.c3 + Q.c3) * s ^ 3) =
        (p.eval s - P.jet s) + (q.eval s - Q.jet s) by
      unfold jet
      ring]
    exact (abs_add_le _ _).trans
      ((add_le_add hP hQ).trans_eq (by ring))

/-- Negation of a certified cubic Taylor bound. -/
def neg {p : Polynomial ℝ} (P : CubicTaylorBound p) :
    CubicTaylorBound (-p) where
  c0 := -P.c0
  c1 := -P.c1
  c2 := -P.c2
  c3 := -P.c3
  b0 := P.b0
  b1 := P.b1
  b2 := P.b2
  b3 := P.b3
  remainder := P.remainder
  b0_nonneg := P.b0_nonneg
  b1_nonneg := P.b1_nonneg
  b2_nonneg := P.b2_nonneg
  b3_nonneg := P.b3_nonneg
  remainder_nonneg := P.remainder_nonneg
  abs_c0_le := by simpa using P.abs_c0_le
  abs_c1_le := by simpa using P.abs_c1_le
  abs_c2_le := by simpa using P.abs_c2_le
  abs_c3_le := by simpa using P.abs_c3_le
  remainder_bound := by
    intro s hs
    rw [eval_neg]
    rw [show -p.eval s -
        (-P.c0 + -P.c1 * s + -P.c2 * s ^ 2 + -P.c3 * s ^ 3) =
        -(p.eval s - (P.c0 + P.c1 * s + P.c2 * s ^ 2 + P.c3 * s ^ 3)) by ring]
    rw [abs_neg]
    exact P.remainder_bound s hs

/-- Subtraction of certified cubic Taylor bounds. -/
def sub {p q : Polynomial ℝ} (P : CubicTaylorBound p) (Q : CubicTaylorBound q) :
    CubicTaylorBound (p - q) := by
  simpa [sub_eq_add_neg] using P.add Q.neg

lemma abs_product_jet_tail_le {p q : Polynomial ℝ}
    (P : CubicTaylorBound p) (Q : CubicTaylorBound q)
    {s : ℝ} (hs : |s| ≤ cubicTaylorRadius) :
    |(P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1) * s ^ 4 +
      (P.c2 * Q.c3 + P.c3 * Q.c2) * s ^ 5 +
      (P.c3 * Q.c3) * s ^ 6| ≤
      P.productJetTail Q * |s| ^ 4 := by
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have hR : 0 ≤ cubicTaylorRadius := cubicTaylorRadius_nonneg
  have hs5 : |s| ^ 5 ≤ cubicTaylorRadius * |s| ^ 4 := by
    calc
      |s| ^ 5 = |s| * |s| ^ 4 := by ring
      _ ≤ cubicTaylorRadius * |s| ^ 4 :=
        mul_le_mul_of_nonneg_right hs (by positivity)
  have hs6 : |s| ^ 6 ≤ cubicTaylorRadius ^ 2 * |s| ^ 4 := by
    have hsq : |s| ^ 2 ≤ cubicTaylorRadius ^ 2 := abs_pow_le_radius_pow hs 2
    calc
      |s| ^ 6 = |s| ^ 2 * |s| ^ 4 := by ring
      _ ≤ cubicTaylorRadius ^ 2 * |s| ^ 4 :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
  have h13 : |P.c1 * Q.c3| ≤ P.b1 * Q.b3 := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c1_le Q.abs_c3_le (abs_nonneg _) P.b1_nonneg
  have h22 : |P.c2 * Q.c2| ≤ P.b2 * Q.b2 := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c2_le Q.abs_c2_le (abs_nonneg _) P.b2_nonneg
  have h31 : |P.c3 * Q.c1| ≤ P.b3 * Q.b1 := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c3_le Q.abs_c1_le (abs_nonneg _) P.b3_nonneg
  have h23 : |P.c2 * Q.c3| ≤ P.b2 * Q.b3 := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c2_le Q.abs_c3_le (abs_nonneg _) P.b2_nonneg
  have h32 : |P.c3 * Q.c2| ≤ P.b3 * Q.b2 := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c3_le Q.abs_c2_le (abs_nonneg _) P.b3_nonneg
  have h33 : |P.c3 * Q.c3| ≤ P.b3 * Q.b3 := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c3_le Q.abs_c3_le (abs_nonneg _) P.b3_nonneg
  have h4 : |P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1| ≤
      P.b1 * Q.b3 + P.b2 * Q.b2 + P.b3 * Q.b1 := by
    calc
      |P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1| ≤
          |P.c1 * Q.c3| + |P.c2 * Q.c2| + |P.c3 * Q.c1| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add h13 h22) h31
  have h5 : |P.c2 * Q.c3 + P.c3 * Q.c2| ≤
      P.b2 * Q.b3 + P.b3 * Q.b2 :=
    (abs_add_le _ _).trans (add_le_add h23 h32)
  calc
    |(P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1) * s ^ 4 +
        (P.c2 * Q.c3 + P.c3 * Q.c2) * s ^ 5 +
        (P.c3 * Q.c3) * s ^ 6| ≤
        |P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1| * |s| ^ 4 +
        |P.c2 * Q.c3 + P.c3 * Q.c2| * |s| ^ 5 +
        |P.c3 * Q.c3| * |s| ^ 6 := by
      calc
        |(P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1) * s ^ 4 +
            (P.c2 * Q.c3 + P.c3 * Q.c2) * s ^ 5 +
            (P.c3 * Q.c3) * s ^ 6| ≤
            |(P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1) * s ^ 4 +
              (P.c2 * Q.c3 + P.c3 * Q.c2) * s ^ 5| +
              |(P.c3 * Q.c3) * s ^ 6| := abs_add_le _ _
        _ ≤ (|(P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1) * s ^ 4| +
              |(P.c2 * Q.c3 + P.c3 * Q.c2) * s ^ 5|) +
              |(P.c3 * Q.c3) * s ^ 6| := by
            gcongr
            exact abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
    _ ≤ (P.b1 * Q.b3 + P.b2 * Q.b2 + P.b3 * Q.b1) * |s| ^ 4 +
        (P.b2 * Q.b3 + P.b3 * Q.b2) *
          (cubicTaylorRadius * |s| ^ 4) +
        (P.b3 * Q.b3) * (cubicTaylorRadius ^ 2 * |s| ^ 4) := by
      have ht4 :
          |P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1| * |s| ^ 4 ≤
            (P.b1 * Q.b3 + P.b2 * Q.b2 + P.b3 * Q.b1) * |s| ^ 4 :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
      have ht5 :
          |P.c2 * Q.c3 + P.c3 * Q.c2| * |s| ^ 5 ≤
            (P.b2 * Q.b3 + P.b3 * Q.b2) *
              (cubicTaylorRadius * |s| ^ 4) := by
        exact (mul_le_mul_of_nonneg_right h5 (by positivity)).trans
          (mul_le_mul_of_nonneg_left hs5
            (add_nonneg
              (mul_nonneg P.b2_nonneg Q.b3_nonneg)
              (mul_nonneg P.b3_nonneg Q.b2_nonneg)))
      have ht6 :
          |P.c3 * Q.c3| * |s| ^ 6 ≤
            (P.b3 * Q.b3) * (cubicTaylorRadius ^ 2 * |s| ^ 4) := by
        exact (mul_le_mul_of_nonneg_right h33 (by positivity)).trans
          (mul_le_mul_of_nonneg_left hs6
            (mul_nonneg P.b3_nonneg Q.b3_nonneg))
      exact add_le_add (add_le_add ht4 ht5) ht6
    _ = P.productJetTail Q * |s| ^ 4 := by
      unfold productJetTail
      ring

/-- Multiplication of certified bounds. The returned remainder retains all
fixed-radius weights, rather than replacing the radius by one. -/
def mul {p q : Polynomial ℝ} (P : CubicTaylorBound p) (Q : CubicTaylorBound q) :
    CubicTaylorBound (p * q) where
  c0 := P.c0 * Q.c0
  c1 := P.c0 * Q.c1 + P.c1 * Q.c0
  c2 := P.c0 * Q.c2 + P.c1 * Q.c1 + P.c2 * Q.c0
  c3 := P.c0 * Q.c3 + P.c1 * Q.c2 + P.c2 * Q.c1 + P.c3 * Q.c0
  b0 := P.b0 * Q.b0
  b1 := P.b0 * Q.b1 + P.b1 * Q.b0
  b2 := P.b0 * Q.b2 + P.b1 * Q.b1 + P.b2 * Q.b0
  b3 := P.b0 * Q.b3 + P.b1 * Q.b2 + P.b2 * Q.b1 + P.b3 * Q.b0
  remainder := P.productRemainder Q
  b0_nonneg := mul_nonneg P.b0_nonneg Q.b0_nonneg
  b1_nonneg := add_nonneg
    (mul_nonneg P.b0_nonneg Q.b1_nonneg)
    (mul_nonneg P.b1_nonneg Q.b0_nonneg)
  b2_nonneg := add_nonneg
    (add_nonneg
      (mul_nonneg P.b0_nonneg Q.b2_nonneg)
      (mul_nonneg P.b1_nonneg Q.b1_nonneg))
    (mul_nonneg P.b2_nonneg Q.b0_nonneg)
  b3_nonneg := add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg P.b0_nonneg Q.b3_nonneg)
        (mul_nonneg P.b1_nonneg Q.b2_nonneg))
      (mul_nonneg P.b2_nonneg Q.b1_nonneg))
    (mul_nonneg P.b3_nonneg Q.b0_nonneg)
  remainder_nonneg := productRemainder_nonneg P Q
  abs_c0_le := by
    rw [abs_mul]
    exact mul_le_mul P.abs_c0_le Q.abs_c0_le (abs_nonneg _) P.b0_nonneg
  abs_c1_le := by
    have h01 : |P.c0 * Q.c1| ≤ P.b0 * Q.b1 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c0_le Q.abs_c1_le (abs_nonneg _) P.b0_nonneg
    have h10 : |P.c1 * Q.c0| ≤ P.b1 * Q.b0 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c1_le Q.abs_c0_le (abs_nonneg _) P.b1_nonneg
    exact (abs_add_le _ _).trans (add_le_add h01 h10)
  abs_c2_le := by
    have h02 : |P.c0 * Q.c2| ≤ P.b0 * Q.b2 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c0_le Q.abs_c2_le (abs_nonneg _) P.b0_nonneg
    have h11 : |P.c1 * Q.c1| ≤ P.b1 * Q.b1 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c1_le Q.abs_c1_le (abs_nonneg _) P.b1_nonneg
    have h20 : |P.c2 * Q.c0| ≤ P.b2 * Q.b0 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c2_le Q.abs_c0_le (abs_nonneg _) P.b2_nonneg
    exact (abs_add_le _ _).trans
      ((add_le_add (abs_add_le _ _) le_rfl).trans
        (add_le_add (add_le_add h02 h11) h20))
  abs_c3_le := by
    have h03 : |P.c0 * Q.c3| ≤ P.b0 * Q.b3 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c0_le Q.abs_c3_le (abs_nonneg _) P.b0_nonneg
    have h12 : |P.c1 * Q.c2| ≤ P.b1 * Q.b2 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c1_le Q.abs_c2_le (abs_nonneg _) P.b1_nonneg
    have h21 : |P.c2 * Q.c1| ≤ P.b2 * Q.b1 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c2_le Q.abs_c1_le (abs_nonneg _) P.b2_nonneg
    have h30 : |P.c3 * Q.c0| ≤ P.b3 * Q.b0 := by
      rw [abs_mul]
      exact mul_le_mul P.abs_c3_le Q.abs_c0_le (abs_nonneg _) P.b3_nonneg
    exact (abs_add_le _ _).trans
      ((add_le_add
        ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl).trans
        (add_le_add (add_le_add (add_le_add h03 h12) h21) h30))
  remainder_bound := by
    intro s hs
    have hP := P.remainder_bound s hs
    have hQ := Q.remainder_bound s hs
    have hPJ := P.abs_jet_le_jetNorm hs
    have hQJ := Q.abs_jet_le_jetNorm hs
    have hTail := P.abs_product_jet_tail_le Q hs
    have hs4 : |s| ^ 4 ≤ cubicTaylorRadius ^ 4 := abs_pow_le_radius_pow hs 4
    let ep := p.eval s - P.jet s
    let eq := q.eval s - Q.jet s
    let tail :=
      (P.c1 * Q.c3 + P.c2 * Q.c2 + P.c3 * Q.c1) * s ^ 4 +
      (P.c2 * Q.c3 + P.c3 * Q.c2) * s ^ 5 +
      (P.c3 * Q.c3) * s ^ 6
    have hidentity :
        (p * q).eval s -
          (P.c0 * Q.c0 + (P.c0 * Q.c1 + P.c1 * Q.c0) * s +
            (P.c0 * Q.c2 + P.c1 * Q.c1 + P.c2 * Q.c0) * s ^ 2 +
            (P.c0 * Q.c3 + P.c1 * Q.c2 + P.c2 * Q.c1 + P.c3 * Q.c0) * s ^ 3) =
          tail + ep * Q.jet s + P.jet s * eq + ep * eq := by
      simp only [eval_mul]
      dsimp [ep, eq, tail, jet]
      ring
    have hep : |ep| ≤ P.remainder * |s| ^ 4 := by
      simpa [ep, jet] using hP
    have heq : |eq| ≤ Q.remainder * |s| ^ 4 := by
      simpa [eq, jet] using hQ
    have htermP :
        |ep| * |Q.jet s| ≤ (P.remainder * |s| ^ 4) * Q.jetNorm :=
      mul_le_mul hep hQJ (abs_nonneg _) (mul_nonneg P.remainder_nonneg (by positivity))
    have htermQ :
        |P.jet s| * |eq| ≤ P.jetNorm * (Q.remainder * |s| ^ 4) :=
      mul_le_mul hPJ heq (abs_nonneg _) (jetNorm_nonneg P)
    have htermPQ :
        |ep| * |eq| ≤
          (P.remainder * |s| ^ 4) * (Q.remainder * |s| ^ 4) :=
      mul_le_mul hep heq (abs_nonneg _) (mul_nonneg P.remainder_nonneg (by positivity))
    have hcross :
        (P.remainder * |s| ^ 4) * (Q.remainder * |s| ^ 4) ≤
          (cubicTaylorRadius ^ 4 * P.remainder * Q.remainder) * |s| ^ 4 := by
      calc
        (P.remainder * |s| ^ 4) * (Q.remainder * |s| ^ 4) =
            (P.remainder * Q.remainder * |s| ^ 4) * |s| ^ 4 := by ring
        _ ≤ (P.remainder * Q.remainder * cubicTaylorRadius ^ 4) * |s| ^ 4 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs4
              (mul_nonneg P.remainder_nonneg Q.remainder_nonneg))
            (by positivity)
        _ = (cubicTaylorRadius ^ 4 * P.remainder * Q.remainder) * |s| ^ 4 := by
          ring
    rw [hidentity]
    calc
      |tail + ep * Q.jet s + P.jet s * eq + ep * eq| ≤
          |tail| + |ep| * |Q.jet s| + |P.jet s| * |eq| + |ep| * |eq| := by
        calc
          |tail + ep * Q.jet s + P.jet s * eq + ep * eq| ≤
              |tail + ep * Q.jet s + P.jet s * eq| + |ep * eq| :=
            abs_add_le _ _
          _ ≤ (|tail + ep * Q.jet s| + |P.jet s * eq|) + |ep * eq| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ ((|tail| + |ep * Q.jet s|) + |P.jet s * eq|) + |ep * eq| := by
            gcongr
            exact abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_mul]
      _ ≤ P.productJetTail Q * |s| ^ 4 +
          (P.remainder * |s| ^ 4) * Q.jetNorm +
          P.jetNorm * (Q.remainder * |s| ^ 4) +
          (P.remainder * |s| ^ 4) * (Q.remainder * |s| ^ 4) :=
        add_le_add (add_le_add (add_le_add hTail htermP) htermQ) htermPQ
      _ ≤ P.productJetTail Q * |s| ^ 4 +
          (P.remainder * |s| ^ 4) * Q.jetNorm +
          P.jetNorm * (Q.remainder * |s| ^ 4) +
          (cubicTaylorRadius ^ 4 * P.remainder * Q.remainder) * |s| ^ 4 :=
        add_le_add le_rfl hcross
      _ = P.productRemainder Q * |s| ^ 4 := by
        unfold productRemainder
        ring

/-- Natural powers, constructed compositionally from multiplication. -/
def pow {p : Polynomial ℝ} (P : CubicTaylorBound p) :
    (n : ℕ) → CubicTaylorBound (p ^ n)
  | 0 => by simpa using const 1
  | n + 1 => by simpa [pow_succ] using (pow P n).mul P

end CubicTaylorBound

end
end NearOneRescaledFirstCell
end NearOneRegularizedThirdRow
