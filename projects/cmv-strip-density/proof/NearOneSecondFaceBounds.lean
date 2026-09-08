/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneFirstFaceBounds

/-!
# Explicit second-row bounds for the near-one endpoint cell

This module expands the pole-free second row exactly and gives a
cancellation-aware rational perturbation estimate on the closed interval
`0 ≤ s ≤ 1 / 126334`.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open Filter
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section ExplicitSecondRowFaces

private def secondZ0 : ℝ := π
private def secondZ1 : ℝ := π ^ 2
private def secondZ2 (q : Fin 3 → ℝ) : ℝ := q 0

private def secondR0 : ℝ := 2
private def secondR1 : ℝ := 5 * π / 12
private def secondR2 : ℝ := (43 * π ^ 2 + 1056) / 144
private def secondR3 (q : Fin 3 → ℝ) : ℝ := (5 * q 0 + 12 * q 1) / 12

private def secondE0 : ℝ := π
private def secondE1 : ℝ := 7 * π ^ 2 / 6
private def secondE2 (q : Fin 3 → ℝ) : ℝ :=
  (295 * π ^ 3 - 14256 * π + 108 * q 0 + 1296 * q 1) / 108
private def secondE3 (q : Fin 3 → ℝ) : ℝ :=
  (109 * π ^ 2 * q 0 - 84 * π ^ 2 * q 1 + 72 * π * q 2 -
    5376 * q 0 + 34560 * q 1) / (36 * π)

private def secondC3 (q : Fin 3 → ℝ) : ℝ :=
  4 * (secondE0 * secondR3 q + secondE1 * secondR2 +
    secondE2 q * secondR1 + secondE3 q * secondR0) +
  2 * secondE0 * secondE2 q + secondE1 ^ 2 -
  8 * secondZ0 * secondZ2 q - 4 * secondZ1 ^ 2

private def secondC4 (q : Fin 3 → ℝ) : ℝ :=
  4 * (secondE1 * secondR3 q + secondE2 q * secondR2 +
    secondE3 q * secondR1) +
  2 * secondE0 * secondE3 q + 2 * secondE1 * secondE2 q -
  8 * secondZ1 * secondZ2 q

private def secondC5 (q : Fin 3 → ℝ) : ℝ :=
  4 * (secondE2 q * secondR3 q + secondE3 q * secondR2) +
  2 * secondE1 * secondE3 q + secondE2 q ^ 2 -
  4 * secondZ2 q ^ 2

private def secondC6 (q : Fin 3 → ℝ) : ℝ :=
  4 * secondE3 q * secondR3 q + 2 * secondE2 q * secondE3 q

private def secondC7 (q : Fin 3 → ℝ) : ℝ := secondE3 q ^ 2

private def secondBaseTail (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  secondC3 q + s * secondC4 q + s ^ 2 * secondC5 q +
    s ^ 3 * secondC6 q + s ^ 4 * secondC7 q

private def secondZ (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  secondZ0 + s * secondZ1 + s ^ 2 * secondZ2 q
private def secondR (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  secondR0 + s * secondR1 + s ^ 2 * secondR2 + s ^ 3 * secondR3 q
private def secondE (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  secondE0 + s * secondE1 + s ^ 2 * secondE2 q + s ^ 3 * secondE3 q

private def secondHighCore (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  let Z := secondZ s q
  let R := secondR s q
  let E := secondE s q
  (-4 * E * R + 8 * R ^ 4 * Z) +
  s * (-E ^ 2 + 8 * E * R ^ 3 * Z - 8 * E * R * Z +
    4 * R ^ 4 * Z ^ 2) +
  s ^ 2 * (2 * E ^ 2 * R ^ 2 * Z - 2 * E ^ 2 * Z +
    4 * E * R ^ 3 * Z ^ 2 - 4 * E * R * Z ^ 2) +
  s ^ 3 * (E ^ 2 * R ^ 2 * Z ^ 2 - E ^ 2 * Z ^ 2)

set_option maxHeartbeats 0 in
private lemma poleFreeSecondRescaledRow_expansion (s : ℝ) (q : Fin 3 → ℝ) :
    poleFreeSecondRescaledRow s q =
      poleFreeSecondRescaledRow 0 q + s * secondBaseTail s q +
        s ^ 2 * secondHighCore s q := by
  by_cases hs : s = 0
  · subst s
    simp
  · have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
    have hfac := H2_rescaled_exact_factorization s q
    rw [← rescaledH2PathPolynomial_eval_eq_actual] at hfac
    have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
    have hpoly :
        (rescaledH2PathPolynomial q).eval s =
          s ^ 2 * (poleFreeSecondRescaledRow 0 q +
            s * secondBaseTail s q + s ^ 2 * secondHighCore s q) := by
      rw [poleFreeSecondRescaledRow_zero]
      simp [rescaledH2PathPolynomial, rescaledZPathPolynomial,
        rescaledAPathPolynomial, rescaledBPathPolynomial,
        secondBaseTail, secondHighCore, secondZ, secondR, secondE,
        secondC3, secondC4, secondC5, secondC6, secondC7,
        secondZ0, secondZ1, secondZ2, secondR0, secondR1, secondR2,
        secondR3, secondE0, secondE1, secondE2, secondE3]
      field_simp [hpi]
      ring
    rw [hpoly] at hfac
    exact (mul_left_cancel₀ hs2 hfac.symm)

private lemma endpoint_coordinate_abs_bounds (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    |q 0| ≤ 54 ∧ |q 1| ≤ 28 ∧ |q 2| ≤ 3822 := by
  have hq0 := hq (0 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  have hq2 := hq (2 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at hq2
  constructor
  · rw [abs_of_nonneg (by linarith)]
    exact hq0.2
  constructor
  · rw [abs_of_nonneg (by linarith)]
    exact hq1.2
  · rw [abs_of_nonpos (by linarith)]
    linarith

private lemma second_basic_coefficient_bounds (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    |secondZ0| ≤ 4 ∧ |secondZ1| ≤ 16 ∧ |secondZ2 q| ≤ 54 ∧
    |secondR0| ≤ 2 ∧ |secondR1| ≤ 2 ∧ |secondR2| ≤ 13 ∧
    |secondR3 q| ≤ 51 ∧ |secondE0| ≤ 4 ∧ |secondE1| ≤ 19 ∧
    |secondE2 q| ≤ 2000 ∧ |secondE3 q| ≤ 100000 := by
  rcases endpoint_coordinate_abs_bounds q hq with ⟨hq0abs, hq1abs, hq2abs⟩
  have hq0 := hq (0 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  have hq2 := hq (2 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at hq2
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hpi3 : 3 ≤ π := Real.pi_gt_three.le
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
  have hpi2lo : 0 ≤ π ^ 2 := sq_nonneg π
  have hpi2hi : π ^ 2 ≤ 16 := by nlinarith [sq_nonneg (π - 4)]
  have hpi3lo : 0 ≤ π ^ 3 := by positivity
  have hpi3hi : π ^ 3 ≤ 64 := by
    calc
      π ^ 3 ≤ 4 ^ 3 := pow_le_pow_left₀ hpi0 hpi4 3
      _ = 64 := by norm_num
  have hpq0lo : 0 ≤ π ^ 2 * q 0 := mul_nonneg hpi2lo (by linarith)
  have hpq0hi : π ^ 2 * q 0 ≤ 16 * 54 :=
    mul_le_mul hpi2hi hq0.2 (by linarith) (by norm_num)
  have hpq1lo : 0 ≤ π ^ 2 * q 1 := mul_nonneg hpi2lo (by linarith)
  have hpq1hi : π ^ 2 * q 1 ≤ 16 * 28 :=
    mul_le_mul hpi2hi hq1.2 (by linarith) (by norm_num)
  have hpq2lo : -4 * 3822 ≤ π * q 2 := by
    calc
      -4 * 3822 = 4 * (-3822) := by ring
      _ ≤ π * (-3822) :=
        mul_le_mul_of_nonpos_right hpi4 (by norm_num)
      _ ≤ π * q 2 := mul_le_mul_of_nonneg_left hq2.1 hpi0
  have hpq2hi : π * q 2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpi0 (by linarith)
  have hden : 0 < 36 * π := by positivity
  have he3numlo :
      -2000000 ≤
        109 * π ^ 2 * q 0 - 84 * π ^ 2 * q 1 + 72 * π * q 2 -
          5376 * q 0 + 34560 * q 1 := by
    nlinarith
  have he3numhi :
      109 * π ^ 2 * q 0 - 84 * π ^ 2 * q 1 + 72 * π * q 2 -
          5376 * q 0 + 34560 * q 1 ≤ 2000000 := by
    nlinarith
  repeat' apply And.intro
  · unfold secondZ0
    rw [abs_of_nonneg hpi0]
    exact hpi4
  · unfold secondZ1
    rw [abs_of_nonneg hpi2lo]
    exact hpi2hi
  · simpa [secondZ2] using hq0abs
  · norm_num [secondR0]
  · unfold secondR1
    rw [abs_of_nonneg (by positivity)]
    norm_num
    nlinarith
  · unfold secondR2
    rw [abs_of_nonneg (by positivity)]
    norm_num
    nlinarith
  · unfold secondR3
    rw [abs_of_nonneg (by norm_num; linarith)]
    norm_num
    nlinarith
  · simpa [secondE0] using (show |π| ≤ 4 by
      rw [abs_of_nonneg hpi0]
      exact hpi4)
  · unfold secondE1
    rw [abs_of_nonneg (by positivity)]
    norm_num
    nlinarith
  · unfold secondE2
    rw [abs_le]
    constructor <;> norm_num <;> nlinarith
  · unfold secondE3
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hden]
      nlinarith
    · rw [div_le_iff₀ hden]
      nlinarith

set_option maxHeartbeats 0 in
private lemma secondC3_cancellation_bound (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    |secondC3 q| ≤ 166112 := by
  rcases endpoint_coordinate_abs_bounds q hq with ⟨hq0, hq1, hq2⟩
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hpi3 : 3 ≤ π := Real.pi_gt_three.le
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
  have hpi2lo : 0 ≤ π ^ 2 := sq_nonneg π
  have hpi2hi : π ^ 2 ≤ 16 := by nlinarith [sq_nonneg (π - 4)]
  have hmul (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
      (hA : 0 ≤ A) : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hA
  have hidentity :
      secondC3 q =
        π ^ 2 * (5683 * π ^ 2 - 291456) / 648 +
        (2 * (97 * π ^ 2 - 5376) / (9 * π)) * q 0 +
        (8 * (11 * π ^ 2 + 2880) / (3 * π)) * q 1 +
        16 * q 2 := by
    unfold secondC3 secondE0 secondE1 secondE2 secondE3 secondR0
      secondR1 secondR2 secondR3 secondZ0 secondZ1 secondZ2
    field_simp [ne_of_gt Real.pi_pos]
    ring
  have hinnerConstLo : -291456 ≤ 5683 * π ^ 2 - 291456 := by nlinarith
  have hinnerConstHi : 5683 * π ^ 2 - 291456 ≤ 0 := by nlinarith
  have hp2abs : |π ^ 2| ≤ 16 := by
    rw [abs_of_nonneg hpi2lo]
    exact hpi2hi
  have hinnerConstAbs : |5683 * π ^ 2 - 291456| ≤ 291456 := by
    rw [abs_of_nonpos hinnerConstHi]
    nlinarith
  have hconstProduct := hmul (π ^ 2) (5683 * π ^ 2 - 291456)
    16 291456 hp2abs hinnerConstAbs (by norm_num)
  have hconst :
      |π ^ 2 * (5683 * π ^ 2 - 291456) / 648| ≤ 7200 := by
    rw [abs_div]
    norm_num at hconstProduct ⊢
    nlinarith
  have hden9 : 0 < 9 * π := by positivity
  have hc0lo : -400 ≤ 2 * (97 * π ^ 2 - 5376) / (9 * π) := by
    rw [le_div_iff₀ hden9]
    nlinarith
  have hc0hi : 2 * (97 * π ^ 2 - 5376) / (9 * π) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hden9.le
  have hc0abs : |2 * (97 * π ^ 2 - 5376) / (9 * π)| ≤ 400 := by
    rw [abs_le]
    exact ⟨hc0lo, hc0hi.trans (by norm_num)⟩
  have hc0q0 := hmul (2 * (97 * π ^ 2 - 5376) / (9 * π)) (q 0)
    400 54 hc0abs hq0 (by norm_num)
  have hden3 : 0 < 3 * π := by positivity
  have hc1lo : 0 ≤ 8 * (11 * π ^ 2 + 2880) / (3 * π) := by positivity
  have hc1hi : 8 * (11 * π ^ 2 + 2880) / (3 * π) ≤ 2720 := by
    rw [div_le_iff₀ hden3]
    nlinarith
  have hc1abs : |8 * (11 * π ^ 2 + 2880) / (3 * π)| ≤ 2720 := by
    rw [abs_of_nonneg hc1lo]
    exact hc1hi
  have hc1q1 := hmul (8 * (11 * π ^ 2 + 2880) / (3 * π)) (q 1)
    2720 28 hc1abs hq1 (by norm_num)
  have h16q2 := hmul 16 (q 2) 16 3822 (by norm_num) hq2 (by norm_num)
  rw [hidentity]
  calc
    |π ^ 2 * (5683 * π ^ 2 - 291456) / 648 +
          (2 * (97 * π ^ 2 - 5376) / (9 * π)) * q 0 +
          (8 * (11 * π ^ 2 + 2880) / (3 * π)) * q 1 +
          16 * q 2| ≤
        |π ^ 2 * (5683 * π ^ 2 - 291456) / 648| +
          |(2 * (97 * π ^ 2 - 5376) / (9 * π)) * q 0| +
          |(8 * (11 * π ^ 2 + 2880) / (3 * π)) * q 1| +
          |16 * q 2| := by
            have h₁ := abs_add_le
              (π ^ 2 * (5683 * π ^ 2 - 291456) / 648)
              ((2 * (97 * π ^ 2 - 5376) / (9 * π)) * q 0)
            have h₂ := abs_add_le
              (π ^ 2 * (5683 * π ^ 2 - 291456) / 648 +
                (2 * (97 * π ^ 2 - 5376) / (9 * π)) * q 0)
              ((8 * (11 * π ^ 2 + 2880) / (3 * π)) * q 1)
            have h₃ := abs_add_le
              (π ^ 2 * (5683 * π ^ 2 - 291456) / 648 +
                (2 * (97 * π ^ 2 - 5376) / (9 * π)) * q 0 +
                (8 * (11 * π ^ 2 + 2880) / (3 * π)) * q 1)
              (16 * q 2)
            linarith
    _ ≤ 166112 := by nlinarith

set_option maxHeartbeats 0 in
private lemma second_tail_coefficient_bounds (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    |secondC4 q| ≤ 1790788 ∧ |secondC5 q| ≤ 13419664 ∧
    |secondC6 q| ≤ 420400000 ∧ |secondC7 q| ≤ 10000000000 := by
  rcases second_basic_coefficient_bounds q hq with
    ⟨_hz0, hz1, hz2, _hr0, hr1, hr2, hr3, he0, he1, he2, he3⟩
  have hmul (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
      (hA : 0 ≤ A) : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hA
  have he1r3 := hmul secondE1 (secondR3 q) 19 51 he1 hr3 (by norm_num)
  have he2r2 := hmul (secondE2 q) secondR2 2000 13 he2 hr2 (by norm_num)
  have he3r1 := hmul (secondE3 q) secondR1 100000 2 he3 hr1 (by norm_num)
  have he0e3 := hmul secondE0 (secondE3 q) 4 100000 he0 he3 (by norm_num)
  have he1e2 := hmul secondE1 (secondE2 q) 19 2000 he1 he2 (by norm_num)
  have hz1z2 := hmul secondZ1 (secondZ2 q) 16 54 hz1 hz2 (by norm_num)
  have he2r3 := hmul (secondE2 q) (secondR3 q) 2000 51 he2 hr3 (by norm_num)
  have he3r2 := hmul (secondE3 q) secondR2 100000 13 he3 hr2 (by norm_num)
  have he1e3 := hmul secondE1 (secondE3 q) 19 100000 he1 he3 (by norm_num)
  have he2sq : |secondE2 q ^ 2| ≤ 2000 ^ 2 := by
    simpa [pow_two] using
      hmul (secondE2 q) (secondE2 q) 2000 2000 he2 he2 (by norm_num)
  have hz2sq : |secondZ2 q ^ 2| ≤ 54 ^ 2 := by
    simpa [pow_two] using
      hmul (secondZ2 q) (secondZ2 q) 54 54 hz2 hz2 (by norm_num)
  have he3r3 := hmul (secondE3 q) (secondR3 q) 100000 51 he3 hr3 (by norm_num)
  have he2e3 := hmul (secondE2 q) (secondE3 q) 2000 100000 he2 he3
    (by norm_num)
  have he3sq : |secondE3 q ^ 2| ≤ 100000 ^ 2 := by
    simpa [pow_two] using
      hmul (secondE3 q) (secondE3 q) 100000 100000 he3 he3 (by norm_num)
  rcases abs_le.mp he1r3 with ⟨he1r3lo, he1r3hi⟩
  rcases abs_le.mp he2r2 with ⟨he2r2lo, he2r2hi⟩
  rcases abs_le.mp he3r1 with ⟨he3r1lo, he3r1hi⟩
  rcases abs_le.mp he0e3 with ⟨he0e3lo, he0e3hi⟩
  rcases abs_le.mp he1e2 with ⟨he1e2lo, he1e2hi⟩
  rcases abs_le.mp hz1z2 with ⟨hz1z2lo, hz1z2hi⟩
  rcases abs_le.mp he2r3 with ⟨he2r3lo, he2r3hi⟩
  rcases abs_le.mp he3r2 with ⟨he3r2lo, he3r2hi⟩
  rcases abs_le.mp he1e3 with ⟨he1e3lo, he1e3hi⟩
  rcases abs_le.mp he2sq with ⟨he2sqlo, he2sqhi⟩
  rcases abs_le.mp hz2sq with ⟨hz2sqlo, hz2sqhi⟩
  rcases abs_le.mp he3r3 with ⟨he3r3lo, he3r3hi⟩
  rcases abs_le.mp he2e3 with ⟨he2e3lo, he2e3hi⟩
  rcases abs_le.mp he3sq with ⟨he3sqlo, he3sqhi⟩
  repeat' apply And.intro
  · rw [abs_le]
    constructor <;> unfold secondC4 <;> norm_num at * <;> nlinarith
  · rw [abs_le]
    constructor <;> unfold secondC5 <;> norm_num at * <;> nlinarith
  · rw [abs_le]
    constructor <;> unfold secondC6 <;> norm_num at * <;> nlinarith
  · rw [secondC7, abs_of_nonneg (sq_nonneg _)]
    norm_num at he3sq ⊢
    exact he3sq

set_option maxHeartbeats 0 in
private lemma second_base_and_path_bounds {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) (hq : InEndpointBox q) :
    |secondBaseTail s q| ≤ 166200 ∧ |secondZ s q| ≤ 5 ∧
      |secondR s q| ≤ 3 ∧ |secondE s q| ≤ 5 := by
  rcases second_basic_coefficient_bounds q hq with
    ⟨hz0, hz1, hz2, hr0, hr1, hr2, hr3, he0, he1, he2, he3⟩
  rcases second_tail_coefficient_bounds q hq with
    ⟨hc4, hc5, hc6, hc7⟩
  have hc3 := secondC3_cancellation_bound q hq
  have hs1 : s ≤ 1 := by linarith
  have hspow (n : ℕ) (hn : 1 ≤ n) : s ^ n ≤ s := by
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          simp
        · rw [pow_succ]
          calc
            s ^ n * s ≤ s * 1 :=
              mul_le_mul (ih (Nat.one_le_iff_ne_zero.mpr hn0)) hs1 hs0 hs0
            _ = s := by ring
  have habspow (n : ℕ) (hn : 1 ≤ n) : |s ^ n| ≤ s := by
    rw [abs_of_nonneg (by positivity)]
    exact hspow n hn
  have hmul (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
      (hA : 0 ≤ A) : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hA
  have hsabs : |s| ≤ s := by rw [abs_of_nonneg hs0]
  have hs2abs : |s ^ 2| ≤ s ^ 2 := by rw [abs_of_nonneg (sq_nonneg s)]
  have hs3abs : |s ^ 3| ≤ s ^ 3 := by rw [abs_of_nonneg (by positivity)]
  have hs4abs : |s ^ 4| ≤ s ^ 4 := by rw [abs_of_nonneg (by positivity)]
  have hsc4 := hmul s (secondC4 q) s 1790788 hsabs hc4 hs0
  have hs2c5 := hmul (s ^ 2) (secondC5 q) (s ^ 2) 13419664
    hs2abs hc5 (sq_nonneg s)
  have hs3c6 := hmul (s ^ 3) (secondC6 q) (s ^ 3) 420400000
    hs3abs hc6 (by positivity)
  have hs4c7 := hmul (s ^ 4) (secondC7 q) (s ^ 4) 10000000000
    hs4abs hc7 (by positivity)
  have hsc4' : |s * secondC4 q| ≤ 15 := hsc4.trans (by
    norm_num at hs ⊢
    nlinarith)
  have hs2R : s ^ 2 ≤ (1 / 126334 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have hs3R : s ^ 3 ≤ (1 / 126334 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hs0 hs 3
  have hs4R : s ^ 4 ≤ (1 / 126334 : ℝ) ^ 4 :=
    pow_le_pow_left₀ hs0 hs 4
  have hs2c5' : |s ^ 2 * secondC5 q| ≤ 1 := hs2c5.trans (by
    calc
      s ^ 2 * 13419664 ≤ (1 / 126334 : ℝ) ^ 2 * 13419664 :=
        mul_le_mul_of_nonneg_right hs2R (by norm_num)
      _ ≤ 1 := by norm_num)
  have hs3c6' : |s ^ 3 * secondC6 q| ≤ 1 := hs3c6.trans (by
    calc
      s ^ 3 * 420400000 ≤ (1 / 126334 : ℝ) ^ 3 * 420400000 :=
        mul_le_mul_of_nonneg_right hs3R (by norm_num)
      _ ≤ 1 := by norm_num)
  have hs4c7' : |s ^ 4 * secondC7 q| ≤ 1 := hs4c7.trans (by
    calc
      s ^ 4 * 10000000000 ≤ (1 / 126334 : ℝ) ^ 4 * 10000000000 :=
        mul_le_mul_of_nonneg_right hs4R (by norm_num)
      _ ≤ 1 := by norm_num)
  have hsz1 := hmul s secondZ1 s 16 hsabs hz1 hs0
  have hs2z2 := hmul (s ^ 2) (secondZ2 q) s 54
    (habspow 2 (by norm_num)) hz2 hs0
  have hsr1 := hmul s secondR1 s 2 hsabs hr1 hs0
  have hs2r2 := hmul (s ^ 2) secondR2 s 13
    (habspow 2 (by norm_num)) hr2 hs0
  have hs3r3 := hmul (s ^ 3) (secondR3 q) s 51
    (habspow 3 (by norm_num)) hr3 hs0
  have hse1 := hmul s secondE1 s 19 hsabs he1 hs0
  have hs2e2 := hmul (s ^ 2) (secondE2 q) s 2000
    (habspow 2 (by norm_num)) he2 hs0
  have hs3e3 := hmul (s ^ 3) (secondE3 q) s 100000
    (habspow 3 (by norm_num)) he3 hs0
  rcases abs_le.mp hc3 with ⟨hc3lo, hc3hi⟩
  rcases abs_le.mp hsc4' with ⟨hsc4lo, hsc4hi⟩
  rcases abs_le.mp hs2c5' with ⟨hs2c5lo, hs2c5hi⟩
  rcases abs_le.mp hs3c6' with ⟨hs3c6lo, hs3c6hi⟩
  rcases abs_le.mp hs4c7' with ⟨hs4c7lo, hs4c7hi⟩
  rcases abs_le.mp hz0 with ⟨hz0lo, hz0hi⟩
  rcases abs_le.mp hsz1 with ⟨hsz1lo, hsz1hi⟩
  rcases abs_le.mp hs2z2 with ⟨hs2z2lo, hs2z2hi⟩
  rcases abs_le.mp hr0 with ⟨hr0lo, hr0hi⟩
  rcases abs_le.mp hsr1 with ⟨hsr1lo, hsr1hi⟩
  rcases abs_le.mp hs2r2 with ⟨hs2r2lo, hs2r2hi⟩
  rcases abs_le.mp hs3r3 with ⟨hs3r3lo, hs3r3hi⟩
  rcases abs_le.mp he0 with ⟨he0lo, he0hi⟩
  rcases abs_le.mp hse1 with ⟨hse1lo, hse1hi⟩
  rcases abs_le.mp hs2e2 with ⟨hs2e2lo, hs2e2hi⟩
  rcases abs_le.mp hs3e3 with ⟨hs3e3lo, hs3e3hi⟩
  repeat' apply And.intro
  · rw [abs_le]
    constructor <;> unfold secondBaseTail <;> norm_num at * <;> linarith
  · rw [abs_le]
    constructor <;> unfold secondZ <;> norm_num at * <;> nlinarith
  · rw [abs_le]
    constructor <;> unfold secondR <;> norm_num at * <;> nlinarith
  · rw [abs_le]
    constructor <;> unfold secondE <;> norm_num at * <;> nlinarith

set_option maxHeartbeats 0 in
private lemma second_high_core_bound {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) (hq : InEndpointBox q) :
    |secondHighCore s q| ≤ 3301 := by
  rcases second_base_and_path_bounds q hs0 hs hq with
    ⟨_hbase, hZ, hR, hE⟩
  have hs1 : s ≤ 1 := by linarith
  have hspow (n : ℕ) (hn : 1 ≤ n) : s ^ n ≤ s := by
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hn0 : n = 0
        · subst n
          simp
        · rw [pow_succ]
          calc
            s ^ n * s ≤ s * 1 :=
              mul_le_mul (ih (Nat.one_le_iff_ne_zero.mpr hn0)) hs1 hs0 hs0
            _ = s := by ring
  have habspow (n : ℕ) (hn : 1 ≤ n) : |s ^ n| ≤ s := by
    rw [abs_of_nonneg (by positivity)]
    exact hspow n hn
  have hmul (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
      (hA : 0 ≤ A) : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hA
  have hpow (a A : ℝ) (n : ℕ) (ha : |a| ≤ A) :
      |a ^ n| ≤ A ^ n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg a) ha n
  let Z := secondZ s q
  let R := secondR s q
  let E := secondE s q
  have hZR : |Z| ≤ 5 ∧ |R| ≤ 3 ∧ |E| ≤ 5 := by simpa [Z, R, E]
    using ⟨hZ, hR, hE⟩
  rcases hZR with ⟨hZ, hR, hE⟩
  have hE2 := hpow E 5 2 hE
  have hR2 := hpow R 3 2 hR
  have hR3 := hpow R 3 3 hR
  have hR4 := hpow R 3 4 hR
  have hZ2 := hpow Z 5 2 hZ
  have hc4 : |(4 : ℝ)| ≤ 4 := by norm_num
  have hc8 : |(8 : ℝ)| ≤ 8 := by norm_num
  have hc2 : |(2 : ℝ)| ≤ 2 := by norm_num
  have hm4ER := hmul (4 * E) R (4 * 5) 3
    (hmul 4 E 4 5 hc4 hE (by norm_num)) hR (by norm_num)
  have hm8R4Z := hmul (8 * R ^ 4) Z (8 * 3 ^ 4) 5
    (hmul 8 (R ^ 4) 8 (3 ^ 4) hc8 hR4 (by norm_num)) hZ (by norm_num)
  have hm8ER3Z := hmul ((8 * E * R ^ 3)) Z (8 * 5 * 3 ^ 3) 5
    (hmul (8 * E) (R ^ 3) (8 * 5) (3 ^ 3)
      (hmul 8 E 8 5 hc8 hE (by norm_num)) hR3 (by norm_num))
    hZ (by norm_num)
  have hm8ERZ := hmul ((8 * E * R)) Z (8 * 5 * 3) 5
    (hmul (8 * E) R (8 * 5) 3
      (hmul 8 E 8 5 hc8 hE (by norm_num)) hR (by norm_num))
    hZ (by norm_num)
  have hm4R4Z2 := hmul (4 * R ^ 4) (Z ^ 2) (4 * 3 ^ 4) (5 ^ 2)
    (hmul 4 (R ^ 4) 4 (3 ^ 4) hc4 hR4 (by norm_num)) hZ2 (by norm_num)
  have hm2E2R2Z := hmul ((2 * E ^ 2 * R ^ 2)) Z
      (2 * 5 ^ 2 * 3 ^ 2) 5
    (hmul (2 * E ^ 2) (R ^ 2) (2 * 5 ^ 2) (3 ^ 2)
      (hmul 2 (E ^ 2) 2 (5 ^ 2) hc2 hE2 (by norm_num)) hR2 (by norm_num))
    hZ (by norm_num)
  have hm2E2Z := hmul (2 * E ^ 2) Z (2 * 5 ^ 2) 5
    (hmul 2 (E ^ 2) 2 (5 ^ 2) hc2 hE2 (by norm_num)) hZ (by norm_num)
  have hm4ER3Z2 := hmul ((4 * E * R ^ 3)) (Z ^ 2)
      (4 * 5 * 3 ^ 3) (5 ^ 2)
    (hmul (4 * E) (R ^ 3) (4 * 5) (3 ^ 3)
      (hmul 4 E 4 5 hc4 hE (by norm_num)) hR3 (by norm_num))
    hZ2 (by norm_num)
  have hm4ERZ2 := hmul ((4 * E * R)) (Z ^ 2) (4 * 5 * 3) (5 ^ 2)
    (hmul (4 * E) R (4 * 5) 3
      (hmul 4 E 4 5 hc4 hE (by norm_num)) hR (by norm_num))
    hZ2 (by norm_num)
  have hmE2R2Z2 := hmul ((E ^ 2 * R ^ 2)) (Z ^ 2)
      (5 ^ 2 * 3 ^ 2) (5 ^ 2)
    (hmul (E ^ 2) (R ^ 2) (5 ^ 2) (3 ^ 2) hE2 hR2 (by norm_num))
    hZ2 (by norm_num)
  have hmE2Z2 := hmul (E ^ 2) (Z ^ 2) (5 ^ 2) (5 ^ 2)
    hE2 hZ2 (by norm_num)
  let T0 := -4 * E * R + 8 * R ^ 4 * Z
  let T1 := -E ^ 2 + 8 * E * R ^ 3 * Z - 8 * E * R * Z +
    4 * R ^ 4 * Z ^ 2
  let T2 := 2 * E ^ 2 * R ^ 2 * Z - 2 * E ^ 2 * Z +
    4 * E * R ^ 3 * Z ^ 2 - 4 * E * R * Z ^ 2
  let T3 := E ^ 2 * R ^ 2 * Z ^ 2 - E ^ 2 * Z ^ 2
  have hT0 : |T0| ≤ 3300 := by
    rcases abs_le.mp hm4ER with ⟨h1l, h1u⟩
    rcases abs_le.mp hm8R4Z with ⟨h2l, h2u⟩
    rw [abs_le]
    dsimp [T0]
    constructor <;> norm_num at * <;> nlinarith
  have hT1 : |T1| ≤ 14125 := by
    rcases abs_le.mp hE2 with ⟨h1l, h1u⟩
    rcases abs_le.mp hm8ER3Z with ⟨h2l, h2u⟩
    rcases abs_le.mp hm8ERZ with ⟨h3l, h3u⟩
    rcases abs_le.mp hm4R4Z2 with ⟨h4l, h4u⟩
    rw [abs_le]
    dsimp [T1]
    constructor <;> norm_num at * <;> nlinarith
  have hT2 : |T2| ≤ 17500 := by
    rcases abs_le.mp hm2E2R2Z with ⟨h1l, h1u⟩
    rcases abs_le.mp hm2E2Z with ⟨h2l, h2u⟩
    rcases abs_le.mp hm4ER3Z2 with ⟨h3l, h3u⟩
    rcases abs_le.mp hm4ERZ2 with ⟨h4l, h4u⟩
    rw [abs_le]
    dsimp [T2]
    constructor <;> norm_num at * <;> nlinarith
  have hT3 : |T3| ≤ 6250 := by
    rcases abs_le.mp hmE2R2Z2 with ⟨h1l, h1u⟩
    rcases abs_le.mp hmE2Z2 with ⟨h2l, h2u⟩
    rw [abs_le]
    dsimp [T3]
    constructor <;> norm_num at * <;> nlinarith
  have hsabs : |s| ≤ s := by rw [abs_of_nonneg hs0]
  have hsT1 := hmul s T1 s 14125 hsabs hT1 hs0
  have hs2T2 := hmul (s ^ 2) T2 s 17500
    (habspow 2 (by norm_num)) hT2 hs0
  have hs3T3 := hmul (s ^ 3) T3 s 6250
    (habspow 3 (by norm_num)) hT3 hs0
  rcases abs_le.mp hT0 with ⟨hT0lo, hT0hi⟩
  rcases abs_le.mp hsT1 with ⟨hsT1lo, hsT1hi⟩
  rcases abs_le.mp hs2T2 with ⟨hsT2lo, hsT2hi⟩
  rcases abs_le.mp hs3T3 with ⟨hsT3lo, hsT3hi⟩
  rw [abs_le]
  change -3301 ≤ T0 + s * T1 + s ^ 2 * T2 + s ^ 3 * T3 ∧
    T0 + s * T1 + s ^ 2 * T2 + s ^ 3 * T3 ≤ 3301
  constructor <;> norm_num at * <;> nlinarith

private lemma poleFreeSecondRescaledRow_close {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) (hq : InEndpointBox q) :
    |poleFreeSecondRescaledRow s q - poleFreeSecondRescaledRow 0 q| < 5 := by
  have hbase := (second_base_and_path_bounds q hs0 hs hq).1
  have hhigh := second_high_core_bound q hs0 hs hq
  have hsabs : |s| ≤ s := by rw [abs_of_nonneg hs0]
  have hs2abs : |s ^ 2| ≤ s ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg s)]
  have hs2R : s ^ 2 ≤ (1 / 126334 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have hmul (a b A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
      (hA : 0 ≤ A) : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg b) hA
  have hbaseTerm := hmul s (secondBaseTail s q) s 166200
    hsabs hbase hs0
  have hhighTerm := hmul (s ^ 2) (secondHighCore s q) (s ^ 2) 3301
    hs2abs hhigh (sq_nonneg s)
  rcases abs_le.mp hbaseTerm with ⟨hbaseLo, hbaseHi⟩
  rcases abs_le.mp hhighTerm with ⟨hhighLo, hhighHi⟩
  rw [poleFreeSecondRescaledRow_expansion]
  rw [abs_lt]
  constructor <;> norm_num at hs hs2R ⊢ <;> linarith

private lemma poleFreeSecondRescaledRow_endpoint_margins (q : Fin 3 → ℝ) :
    (q 1 = endpointBoxLower 1 →
      poleFreeSecondRescaledRow 0 q < -34) ∧
    (q 1 = endpointBoxUpper 1 →
      61 < poleFreeSecondRescaledRow 0 q) := by
  have hpi3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
  have hpi3hi : π ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.pi_lt_d20 Real.pi_pos.le (by norm_num)
  constructor
  · intro hface
    rw [poleFreeSecondRescaledRow_zero]
    simp only [endpointBoxLower, Matrix.cons_val_one] at hface
    rw [hface]
    have hpilo := Real.pi_gt_d20
    norm_num at hpi3hi hpilo ⊢
    nlinarith
  · intro hface
    rw [poleFreeSecondRescaledRow_zero]
    simp only [endpointBoxUpper, Matrix.cons_val_one] at hface
    rw [hface]
    have hpihi := Real.pi_lt_d20
    norm_num at hpi3lo hpihi ⊢
    nlinarith

/-- The complete second pair of endpoint-box faces has strict signs throughout
the explicit closed scale interval `0 ≤ s ≤ 1 / 126334`. -/
theorem explicit_second_face_cell {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) :
    ∀ q, InEndpointBox q →
      (q 1 = endpointBoxLower 1 →
        rescaledOrientedNearOneMap s q 1 < 0) ∧
      (q 1 = endpointBoxUpper 1 →
        0 < rescaledOrientedNearOneMap s q 1) := by
  intro q hq
  have hclose := poleFreeSecondRescaledRow_close q hs0 hs hq
  have hmargins := poleFreeSecondRescaledRow_endpoint_margins q
  rw [abs_lt] at hclose
  rw [rescaledOrientedNearOneMap_second_eq_poleFree]
  constructor
  · intro hface
    nlinarith [hmargins.1 hface]
  · intro hface
    nlinarith [hmargins.2 hface]

end ExplicitSecondRowFaces

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
