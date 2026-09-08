/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneRegularizedThirdRow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Exact arctangent integral remainders

Reusable exact recurrence and analytic bounds for the arctangent remainders used
by the scale-local near-one certificate evaluator.
-/

namespace NearOneAtanRemainder
open scoped Interval BigOperators
open Real

noncomputable section

/-- The signed integral remainder after the term of degree `2 * k - 2` in
`arctan x / x`. -/
def atanRemainder (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * ∫ t in (0 : ℝ)..1, t ^ (2 * k) / (1 + (x * t) ^ 2)

/-- The generic first remainder is the remainder already used by the corrected
near-one analytic system. -/
theorem atanRemainder_one (x : ℝ) :
    atanRemainder 1 x = NearOneRegularizedThirdRow.atanQuotientSqRemainder x := by
  simp [atanRemainder, NearOneRegularizedThirdRow.atanQuotientSqRemainder]

/-- One exact geometric-series step. -/
theorem atanRemainder_recurrence (k : ℕ) (x : ℝ) :
    atanRemainder k x =
      (-1 : ℝ) ^ k / (2 * k + 1 : ℕ) + x ^ 2 * atanRemainder (k + 1) x := by
  have hpow : (∫ t in (0 : ℝ)..1, t ^ (2 * k)) =
      (1 : ℝ) / (2 * k + 1 : ℕ) := by
    rw [integral_pow]
    norm_num
  rw [atanRemainder, atanRemainder, div_eq_mul_one_div, ← hpow]
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_const_mul]
  rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro t _
    have hden : 1 + (x * t) ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    rw [show (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) by ring]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop (disch := positivity)
  · apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    exact (continuous_id.pow _).div
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (fun t => by positivity)

/-- The integral remainder has its sharp denominator-free global magnitude
bound. -/
theorem abs_atanRemainder_le (k : ℕ) (x : ℝ) :
    |atanRemainder k x| ≤ (1 : ℝ) / (2 * (k : ℝ) + 1) := by
  rw [atanRemainder, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  calc
    ‖∫ t in (0 : ℝ)..1, t ^ (2 * k) / (1 + (x * t) ^ 2)‖ ≤
        ∫ t in (0 : ℝ)..1, t ^ (2 * k) :=
      intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (by
          filter_upwards with t ht
          have ht0 : 0 ≤ t := ht.1.le
          have hpow0 : 0 ≤ t ^ (2 * k) := pow_nonneg ht0 _
          have hden0 : 0 ≤ 1 + (x * t) ^ 2 := by positivity
          have hden1 : 1 ≤ 1 + (x * t) ^ 2 := by nlinarith [sq_nonneg (x * t)]
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpow0 hden0)]
          exact div_le_self hpow0 hden1)
        ((continuous_id.pow _).intervalIntegrable _ _)
    _ = (1 : ℝ) / (2 * (k : ℝ) + 1) := by
      rw [integral_pow]
      norm_num [Nat.cast_add, Nat.cast_mul]

/-- Exact finite expansion with an analytic tail. No Taylor term is discarded. -/
theorem atanRemainder_finite_expansion (k N : ℕ) (x : ℝ) :
    atanRemainder k x =
      (∑ j ∈ Finset.range N,
        (-1 : ℝ) ^ (k + j) * x ^ (2 * j) /
          (2 * (k + j) + 1 : ℕ)) +
        x ^ (2 * N) * atanRemainder (k + N) x := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [ih, atanRemainder_recurrence]
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_mul]
      have hpow : x ^ (2 * (N + 1)) = x ^ (2 * N) * x ^ 2 := by
        rw [show 2 * (N + 1) = 2 * N + 2 by omega, pow_add, pow_two]
      rw [hpow]
      simp only [Nat.add_assoc]
      ring

private theorem hasDerivAt_unsignedRemainderIntegral (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => ∫ t in (0 : ℝ)..1,
        t ^ (2 * k) / (1 + (y * t) ^ 2))
      (∫ t in (0 : ℝ)..1,
        (-2 * x * t ^ (2 * k + 2)) / (1 + (x * t) ^ 2) ^ 2) x := by
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y t : ℝ => t ^ (2 * k) / (1 + (y * t) ^ 2))
    (F' := fun y t : ℝ =>
      (-2 * y * t ^ (2 * k + 2)) / (1 + (y * t) ^ 2) ^ 2)
    (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
    (s := Metric.ball x 1)
    (bound := fun t : ℝ => 2 * (|x| + 1) * t ^ (2 * k + 2))
    (Metric.ball_mem_nhds x zero_lt_one) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with y
    exact Measurable.aestronglyMeasurable (by fun_prop (disch := positivity))
  · apply Continuous.intervalIntegrable
    exact (continuous_id.pow _).div
      (continuous_const.add ((continuous_const.mul continuous_id).pow 2))
      (fun t => by positivity)
  · exact Measurable.aestronglyMeasurable (by fun_prop (disch := positivity))
  · filter_upwards with t ht y hy
    have ht0 : 0 ≤ t := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht.1.le
    have hyAbs : |y| ≤ |x| + 1 := by
      have hyx : |y - x| < 1 := by simpa [Real.dist_eq] using hy
      calc
        |y| = |(y - x) + x| := by ring_nf
        _ ≤ |y - x| + |x| := abs_add_le _ _
        _ ≤ |x| + 1 := by linarith
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_neg]
    simp only [abs_pow, abs_of_nonneg ht0,
      abs_of_pos (show 0 < 1 + (y * t) ^ 2 by positivity),
      abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    calc
      2 * |y| * t ^ (2 * k + 2) / (1 + (y * t) ^ 2) ^ 2 ≤
          2 * |y| * t ^ (2 * k + 2) :=
        div_le_self (by positivity) (by nlinarith [sq_nonneg (y * t)])
      _ ≤ 2 * (|x| + 1) * t ^ (2 * k + 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hyAbs (by norm_num)) (by positivity)
  · apply Continuous.intervalIntegrable
    fun_prop
  · filter_upwards with t ht y hy
    have hden : 1 + (y * t) ^ 2 ≠ 0 := by positivity
    have hpow : t ^ (2 * k + 2) = t ^ (2 * k) * t ^ 2 := by
      rw [pow_add]
    rw [hpow]
    convert (hasDerivAt_const (x := y) (c := t ^ (2 * k))).div
      ((hasDerivAt_const (x := y) (c := (1 : ℝ))).add
        (((hasDerivAt_id' y).mul_const t).pow 2)) hden using 1
    all_goals first | rfl | (norm_num; ring)

/-- The exact derivative represented by a second compact integral. -/
def atanRemainderDerivative (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (k + 1) * 2 * x *
    ∫ t in (0 : ℝ)..1, t ^ (2 * k + 2) / (1 + (x * t) ^ 2) ^ 2

/-- Differentiability and the exact integral derivative used by generated AD
certificates. -/
theorem hasDerivAt_atanRemainder (k : ℕ) (x : ℝ) :
    HasDerivAt (atanRemainder k) (atanRemainderDerivative k x) x := by
  have h := (hasDerivAt_unsignedRemainderIntegral k x).const_mul ((-1 : ℝ) ^ k)
  have hint :
      (∫ t in (0 : ℝ)..1,
          (-2 * x * t ^ (2 * k + 2)) / (1 + (x * t) ^ 2) ^ 2) =
        -2 * x * ∫ t in (0 : ℝ)..1,
          t ^ (2 * k + 2) / (1 + (x * t) ^ 2) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hint] at h
  convert h using 1 <;>
    first
    | rfl
    | (unfold atanRemainderDerivative
       rw [show (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) by ring]
       ring)

/-- Global derivative bound used for the interval enclosure of every retained
remainder call. -/
theorem abs_atanRemainderDerivative_le (k : ℕ) (x : ℝ) :
    |atanRemainderDerivative k x| ≤
      2 * |x| / (2 * (k : ℝ) + 3) := by
  have hIntegral :
      |∫ t in (0 : ℝ)..1,
          t ^ (2 * k + 2) / (1 + (x * t) ^ 2) ^ 2| ≤
        (1 : ℝ) / (2 * (k : ℝ) + 3) := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in (0 : ℝ)..1,
          t ^ (2 * k + 2) / (1 + (x * t) ^ 2) ^ 2‖ ≤
          ∫ t in (0 : ℝ)..1, t ^ (2 * k + 2) :=
        intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
          (by
            filter_upwards with t ht
            have ht0 : 0 ≤ t := ht.1.le
            have hpow0 : 0 ≤ t ^ (2 * k + 2) := pow_nonneg ht0 _
            have hden0 : 0 ≤ (1 + (x * t) ^ 2) ^ 2 := by positivity
            have hden1 : 1 ≤ (1 + (x * t) ^ 2) ^ 2 := by
              nlinarith [sq_nonneg (x * t)]
            rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hpow0 hden0)]
            exact div_le_self hpow0 hden1)
          ((continuous_id.pow _).intervalIntegrable _ _)
      _ = (1 : ℝ) / (2 * (k : ℝ) + 3) := by
        rw [integral_pow]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
  rw [atanRemainderDerivative, abs_mul, abs_mul, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  calc
    2 * |x| *
        |∫ t in (0 : ℝ)..1,
          t ^ (2 * k + 2) / (1 + (x * t) ^ 2) ^ 2| ≤
        2 * |x| * ((1 : ℝ) / (2 * (k : ℝ) + 3)) :=
      mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = 2 * |x| / (2 * (k : ℝ) + 3) := by ring

/-- The derivative operator agrees with the exact integral derivative. -/
theorem abs_deriv_atanRemainder_le (k : ℕ) (x : ℝ) :
    |deriv (atanRemainder k) x| ≤
      2 * |x| / (2 * (k : ℝ) + 3) := by
  rw [(hasDerivAt_atanRemainder k x).deriv]
  exact abs_atanRemainderDerivative_le k x

/-- Uniform value error after `N` finite geometric-series steps. -/
theorem atanRemainder_tail_value_le (k N : ℕ) {x B : ℝ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |atanRemainder k x -
      ∑ j ∈ Finset.range N,
        (-1 : ℝ) ^ (k + j) * x ^ (2 * j) /
          (2 * (k + j) + 1 : ℕ)| ≤
      B ^ (2 * N) / (2 * ((k + N : ℕ) : ℝ) + 1) := by
  have heq :
      atanRemainder k x -
          ∑ j ∈ Finset.range N,
            (-1 : ℝ) ^ (k + j) * x ^ (2 * j) /
              (2 * (k + j) + 1 : ℕ) =
        x ^ (2 * N) * atanRemainder (k + N) x := by
    rw [atanRemainder_finite_expansion]
    ring
  rw [heq, abs_mul, abs_pow]
  calc
    |x| ^ (2 * N) * |atanRemainder (k + N) x| ≤
        B ^ (2 * N) *
          ((1 : ℝ) / (2 * ((k + N : ℕ) : ℝ) + 1)) := by
      exact mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg x) hx _)
        (abs_atanRemainder_le (k + N) x)
        (abs_nonneg _) (pow_nonneg hB _)
    _ = B ^ (2 * N) / (2 * ((k + N : ℕ) : ℝ) + 1) := by ring

/-- Uniform derivative error for the exact analytic tail. This is the pair of
terms consumed by the scale-local checker. -/
theorem atanRemainder_tail_deriv_le (k N : ℕ) {x B : ℝ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |deriv (fun y => y ^ (2 * N) * atanRemainder (k + N) y) x| ≤
      2 * N * B ^ (2 * N - 1) /
          (2 * ((k + N : ℕ) : ℝ) + 1) +
        2 * B ^ (2 * N + 1) /
          (2 * ((k + N : ℕ) : ℝ) + 3) := by
  change |deriv ((id ^ (2 * N)) * atanRemainder (k + N)) x| ≤ _
  have hderiv := ((hasDerivAt_id x).pow (2 * N)).mul
    (hasDerivAt_atanRemainder (k + N) x)
  rw [hderiv.deriv]
  simp only [id_eq, Pi.pow_apply, mul_one]
  have hfirst :
      |(2 * N : ℕ) * x ^ (2 * N - 1) * atanRemainder (k + N) x| ≤
        2 * N * B ^ (2 * N - 1) /
          (2 * ((k + N : ℕ) : ℝ) + 1) := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 * N : ℝ) * |x| ^ (2 * N - 1) *
          |atanRemainder (k + N) x| ≤
        (2 * N : ℝ) * B ^ (2 * N - 1) *
          ((1 : ℝ) / (2 * ((k + N : ℕ) : ℝ) + 1)) := by
        gcongr
        exact abs_atanRemainder_le (k + N) x
      _ = 2 * N * B ^ (2 * N - 1) /
          (2 * ((k + N : ℕ) : ℝ) + 1) := by ring
  have hsecond :
      |x ^ (2 * N) * atanRemainderDerivative (k + N) x| ≤
        2 * B ^ (2 * N + 1) /
          (2 * ((k + N : ℕ) : ℝ) + 3) := by
    rw [abs_mul, abs_pow]
    calc
      |x| ^ (2 * N) * |atanRemainderDerivative (k + N) x| ≤
        B ^ (2 * N) *
          (2 * |x| / (2 * ((k + N : ℕ) : ℝ) + 3)) := by
        exact mul_le_mul
          (pow_le_pow_left₀ (abs_nonneg x) hx _)
          (abs_atanRemainderDerivative_le (k + N) x)
          (abs_nonneg _) (pow_nonneg hB _)
      _ ≤ B ^ (2 * N) *
          (2 * B / (2 * ((k + N : ℕ) : ℝ) + 3)) := by
        gcongr
      _ = 2 * B ^ (2 * N + 1) /
          (2 * ((k + N : ℕ) : ℝ) + 3) := by
        rw [pow_succ]
        ring
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- The exact value-tail inequality at the retained checker orders `k = 3`,
`N = 20`. -/
theorem atanRemainder_three_tail_value_le {x B : ℝ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |atanRemainder 3 x -
      ∑ j ∈ Finset.range 20,
        (-1 : ℝ) ^ (3 + j) * x ^ (2 * j) /
          (2 * (3 + j) + 1 : ℕ)| ≤
      B ^ 40 / 47 := by
  have h := atanRemainder_tail_value_le 3 20 hB hx
  norm_num at h ⊢
  exact h

/-- The exact derivative-tail inequality at the retained checker orders
`k = 3`, `N = 20`. -/
theorem atanRemainder_three_tail_deriv_le {x B : ℝ}
    (hB : 0 ≤ B) (hx : |x| ≤ B) :
    |deriv (fun y => y ^ 40 * atanRemainder 23 y) x| ≤
      40 * B ^ 39 / 47 + 2 * B ^ 41 / 49 := by
  have h := atanRemainder_tail_deriv_le 3 20 hB hx
  norm_num at h ⊢
  exact h

end

end NearOneAtanRemainder
