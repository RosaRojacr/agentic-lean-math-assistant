/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Polynomial.Norm
import Mathlib.Algebra.Polynomial.Inductions

/-!
# Coefficientwise polynomial majorants

A `PolynomialMajorant p` records a polynomial with nonnegative coefficients
which bounds the absolute value of every coefficient of `p`.  The constructors
below preserve the full coefficientwise information, in particular the exact
convolution bound for multiplication.
-/

namespace NearOneRegularizedThirdRow
namespace NearOneRescaledFirstCell

open Polynomial
open scoped BigOperators

noncomputable section

/-- A polynomial with nonnegative coefficients which bounds `p`
coefficientwise in absolute value. -/
structure PolynomialMajorant (p : ℝ[X]) where
  majorant : ℝ[X]
  coeff_nonneg : ∀ n, 0 ≤ majorant.coeff n
  coeff_abs_le : ∀ n, |p.coeff n| ≤ majorant.coeff n

namespace PolynomialMajorant

/-- Build a polynomial majorant from explicit coefficientwise bounds. -/
def ofCoeffBounds {p q : ℝ[X]} (hq : ∀ n, 0 ≤ q.coeff n)
    (hpq : ∀ n, |p.coeff n| ≤ q.coeff n) : PolynomialMajorant p where
  majorant := q
  coeff_nonneg := hq
  coeff_abs_le := hpq

/-- Reindex a majorant along a polynomial identity without changing its
majorant polynomial. -/
def reindex {p q : ℝ[X]} (P : PolynomialMajorant p) (h : p = q) :
    PolynomialMajorant q where
  majorant := P.majorant
  coeff_nonneg := P.coeff_nonneg
  coeff_abs_le := by
    intro n
    rw [← h]
    exact P.coeff_abs_le n

@[simp] theorem reindex_majorant {p q : ℝ[X]} (P : PolynomialMajorant p)
    (h : p = q) : (P.reindex h).majorant = P.majorant := rfl

/-- The constant polynomial `|c|` majorizes the constant polynomial `c`. -/
def C (c : ℝ) : PolynomialMajorant (Polynomial.C c) where
  majorant := Polynomial.C |c|
  coeff_nonneg := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · simp [Polynomial.coeff_C, hn]
  coeff_abs_le := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · simp [Polynomial.coeff_C, hn]

/-- `X` is its own coefficientwise majorant. -/
def X : PolynomialMajorant (Polynomial.X : ℝ[X]) where
  majorant := Polynomial.X
  coeff_nonneg := by
    intro n
    simp only [Polynomial.coeff_X]
    split <;> simp
  coeff_abs_le := by
    intro n
    simp only [Polynomial.coeff_X]
    split <;> simp

/-- Coefficientwise majorants are closed under addition. -/
def add {p q : ℝ[X]} (hp : PolynomialMajorant p)
    (hq : PolynomialMajorant q) : PolynomialMajorant (p + q) where
  majorant := hp.majorant + hq.majorant
  coeff_nonneg := by
    intro n
    rw [Polynomial.coeff_add]
    exact add_nonneg (hp.coeff_nonneg n) (hq.coeff_nonneg n)
  coeff_abs_le := by
    intro n
    rw [Polynomial.coeff_add]
    exact (abs_add_le _ _).trans
      (add_le_add (hp.coeff_abs_le n) (hq.coeff_abs_le n))

/-- Negation does not change a coefficientwise majorant. -/
def neg {p : ℝ[X]} (hp : PolynomialMajorant p) : PolynomialMajorant (-p) where
  majorant := hp.majorant
  coeff_nonneg := hp.coeff_nonneg
  coeff_abs_le := by
    intro n
    simpa using hp.coeff_abs_le n

/-- A difference is majorized by the sum of the two majorants. -/
def sub {p q : ℝ[X]} (hp : PolynomialMajorant p)
    (hq : PolynomialMajorant q) : PolynomialMajorant (p - q) := by
  simpa [sub_eq_add_neg] using add hp (neg hq)

/-- Multiplication preserves the exact degreewise convolution of the two
majorants. -/
def mul {p q : ℝ[X]} (hp : PolynomialMajorant p)
    (hq : PolynomialMajorant q) : PolynomialMajorant (p * q) where
  majorant := hp.majorant * hq.majorant
  coeff_nonneg := by
    intro n
    rw [Polynomial.coeff_mul]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hp.coeff_nonneg x.1) (hq.coeff_nonneg x.2)
  coeff_abs_le := by
    intro n
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    calc
      |∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
          p.coeff x.1 * q.coeff x.2| ≤
          ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            |p.coeff x.1 * q.coeff x.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n,
            hp.majorant.coeff x.1 * hq.majorant.coeff x.2 := by
        apply Finset.sum_le_sum
        intro x _
        rw [abs_mul]
        exact mul_le_mul (hp.coeff_abs_le x.1) (hq.coeff_abs_le x.2)
          (abs_nonneg _) (hp.coeff_nonneg x.1)

/-- Natural powers are majorized by the corresponding powers of the
majorant. -/
def pow {p : ℝ[X]} (hp : PolynomialMajorant p) :
    (n : ℕ) → PolynomialMajorant (p ^ n)
  | 0 => by simpa using C 1
  | n + 1 => by simpa [pow_succ] using mul (pow hp n) hp

/-- Dividing by `X` shifts both coefficient sequences by one. -/
def divX {p : ℝ[X]} (hp : PolynomialMajorant p) :
    PolynomialMajorant p.divX where
  majorant := hp.majorant.divX
  coeff_nonneg := by
    intro n
    simpa only [Polynomial.coeff_divX] using hp.coeff_nonneg (n + 1)
  coeff_abs_le := by
    intro n
    simpa only [Polynomial.coeff_divX] using hp.coeff_abs_le (n + 1)

@[simp] theorem cast_majorant {p q : ℝ[X]} (h : p = q)
    (P : PolynomialMajorant p) :
    (cast (congrArg PolynomialMajorant h) P).majorant = P.majorant := by
  subst q
  rfl


@[simp] theorem C_majorant (c : ℝ) :
    (PolynomialMajorant.C c).majorant = Polynomial.C |c| := rfl

@[simp] theorem X_majorant :
    PolynomialMajorant.X.majorant = (Polynomial.X : ℝ[X]) := rfl

@[simp] theorem add_majorant {p q : ℝ[X]} (hp : PolynomialMajorant p)
    (hq : PolynomialMajorant q) :
    (hp.add hq).majorant = hp.majorant + hq.majorant := rfl

@[simp] theorem neg_majorant {p : ℝ[X]} (hp : PolynomialMajorant p) :
    hp.neg.majorant = hp.majorant := rfl

@[simp] theorem sub_majorant {p q : ℝ[X]} (hp : PolynomialMajorant p)
    (hq : PolynomialMajorant q) :
    (hp.sub hq).majorant = hp.majorant + hq.majorant := by
  simp [PolynomialMajorant.sub]

@[simp] theorem mul_majorant {p q : ℝ[X]} (hp : PolynomialMajorant p)
    (hq : PolynomialMajorant q) :
    (hp.mul hq).majorant = hp.majorant * hq.majorant := rfl

@[simp] theorem pow_majorant {p : ℝ[X]} (hp : PolynomialMajorant p) :
    ∀ n, (hp.pow n).majorant = hp.majorant ^ n
  | 0 => by simp [PolynomialMajorant.pow]
  | n + 1 => by
      simp [PolynomialMajorant.pow, pow_majorant hp n, pow_succ]

@[simp] theorem divX_majorant {p : ℝ[X]} (hp : PolynomialMajorant p) :
    hp.divX.majorant = hp.majorant.divX := rfl

/-- A polynomial with nonnegative coefficients is monotone on the nonnegative
real axis. -/
theorem eval_mono_of_coeff_nonneg (q : ℝ[X])
    (hq : ∀ n, 0 ≤ q.coeff n) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    q.eval x ≤ q.eval y := by
  rw [q.eval_eq_sum_range x, q.eval_eq_sum_range y]
  apply Finset.sum_le_sum
  intro n _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy n) (hq n)

/-- The recorded majorant is monotone on the nonnegative real axis. -/
theorem eval_mono {p : ℝ[X]} (hp : PolynomialMajorant p)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    hp.majorant.eval x ≤ hp.majorant.eval y :=
  eval_mono_of_coeff_nonneg hp.majorant hp.coeff_nonneg hx hxy

/-- Evaluating a polynomial is bounded by evaluating its coefficientwise
majorant at the absolute value of the argument. -/
theorem abs_eval_le_eval_abs {p : ℝ[X]} (hp : PolynomialMajorant p) (s : ℝ) :
    |p.eval s| ≤ hp.majorant.eval |s| := by
  let N := max p.natDegree hp.majorant.natDegree + 1
  have hpN : p.natDegree < N :=
    lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)
  have hmN : hp.majorant.natDegree < N :=
    lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)
  rw [p.eval_eq_sum_range' hpN s, hp.majorant.eval_eq_sum_range' hmN |s|]
  calc
    |∑ n ∈ Finset.range N, p.coeff n * s ^ n| ≤
        ∑ n ∈ Finset.range N, |p.coeff n * s ^ n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, hp.majorant.coeff n * |s| ^ n := by
      apply Finset.sum_le_sum
      intro n _
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hp.coeff_abs_le n) le_rfl
        (pow_nonneg (abs_nonneg s) n) (hp.coeff_nonneg n)

/-- Radius form of the evaluation bound. -/
theorem abs_eval_le_eval_of_abs_le {p : ℝ[X]} (hp : PolynomialMajorant p)
    {s r : ℝ} (hs : |s| ≤ r) :
    |p.eval s| ≤ hp.majorant.eval r :=
  (hp.abs_eval_le_eval_abs s).trans (hp.eval_mono (abs_nonneg s) hs)

end PolynomialMajorant

end
end NearOneRescaledFirstCell
end NearOneRegularizedThirdRow
