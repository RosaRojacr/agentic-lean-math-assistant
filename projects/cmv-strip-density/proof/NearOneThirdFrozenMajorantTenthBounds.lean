/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOnePolynomialMajorant
import NearOneThirdFrozenMajorantTailDefs
import NearOneThirdFrozenEstimate

/-! # Relaxed-radius scalar bounds for the frozen cleared-error majorant -/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell
section FrozenPolynomial


theorem majorant_eval_nonneg {p : ℝ[X]} (P : PolynomialMajorant p)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ P.majorant.eval x := by
  rw [P.majorant.eval_eq_sum_range]
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (P.coeff_nonneg n) (pow_nonneg hx n)
/-- A relaxed radius at which the scalar majorant DAG remains small. -/
def frozenMajorantRadius : ℝ := 1 / 10

theorem mul_divX_eval_le_eval (p : ℝ[X])
    (hp : ∀ n, 0 ≤ p.coeff n) (x : ℝ) :
    x * p.divX.eval x ≤ p.eval x := by
  have h := congrArg (Polynomial.eval x) (Polynomial.X_mul_divX_add p)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C] at h
  calc
    x * p.divX.eval x ≤ x * p.divX.eval x + p.coeff 0 :=
      le_add_of_nonneg_right (hp 0)
    _ = p.eval x := h

theorem sq_mul_divX_two_eval_le_eval (p : ℝ[X])
    (hp : ∀ n, 0 ≤ p.coeff n) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * p.divX.divX.eval x ≤ p.eval x := by
  have h1 := mul_divX_eval_le_eval p.divX
    (fun n => by simpa only [Polynomial.coeff_divX] using hp (n + 1)) x
  have h0 := mul_divX_eval_le_eval p hp x
  calc
    x ^ 2 * p.divX.divX.eval x = x * (x * p.divX.divX.eval x) := by ring
    _ ≤ x * p.divX.eval x := mul_le_mul_of_nonneg_left h1 hx
    _ ≤ p.eval x := h0

theorem fourth_tail_scaled_le_eval (p : ℝ[X])
    (hp : ∀ n, 0 ≤ p.coeff n) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 4 * p.divX.divX.divX.divX.eval x ≤ p.eval x := by
  have h3 := mul_divX_eval_le_eval p.divX.divX.divX
    (fun n => by simpa only [Polynomial.coeff_divX] using hp (n + 3)) x
  have h2 := mul_divX_eval_le_eval p.divX.divX
    (fun n => by simpa only [Polynomial.coeff_divX] using hp (n + 2)) x
  have h1 := mul_divX_eval_le_eval p.divX
    (fun n => by simpa only [Polynomial.coeff_divX] using hp (n + 1)) x
  have h0 := mul_divX_eval_le_eval p hp x
  calc
    x ^ 4 * p.divX.divX.divX.divX.eval x =
        x ^ 3 * (x * p.divX.divX.divX.divX.eval x) := by ring
    _ ≤ x ^ 3 * p.divX.divX.divX.eval x :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = x ^ 2 * (x * p.divX.divX.divX.eval x) := by ring
    _ ≤ x ^ 2 * p.divX.divX.eval x :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = x * (x * p.divX.divX.eval x) := by ring
    _ ≤ x * p.divX.eval x := mul_le_mul_of_nonneg_left h1 hx
    _ ≤ p.eval x := h0

private theorem zPathMajorant_tenth_le (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (zPathMajorant q hq).majorant.eval frozenMajorantRadius ≤ 31 / 5 := by
  norm_num [frozenMajorantRadius, zPathMajorant, boundedC]

private theorem aPathMajorant_tenth_le (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (aPathMajorant q hq).majorant.eval frozenMajorantRadius ≤ 191 / 50 := by
  norm_num [frozenMajorantRadius, aPathMajorant, boundedC]

private theorem bPathMajorant_tenth_le (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (bPathMajorant q hq).majorant.eval frozenMajorantRadius ≤ 123 := by
  norm_num [frozenMajorantRadius, bPathMajorant, boundedC]

private theorem frozenAlgAMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenAlgAMajorant (zPathMajorant q hq)).majorant.eval
      frozenMajorantRadius ≤ 2 := by
  rw [frozenAlgAMajorant_majorant]
  simp only [oneMajorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_X]
  have hz := zPathMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hz ⊢
  linarith

private theorem frozenAlgRMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenAlgRMajorant (aPathMajorant q hq)).majorant.eval
      frozenMajorantRadius ≤ 12 / 5 := by
  rw [frozenAlgRMajorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_mul,
    Polynomial.eval_X]
  have ha := aPathMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at ha ⊢
  linarith


private theorem frozenAlgEMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenAlgEMajorant (zPathMajorant q hq) (aPathMajorant q hq)
      (bPathMajorant q hq)).majorant.eval frozenMajorantRadius ≤ 48 := by
  rw [frozenAlgEMajorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  have hz := zPathMajorant_tenth_le q hq
  have ha := aPathMajorant_tenth_le q hq
  have hb := bPathMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hz ha hb ⊢
  linarith

private theorem frozenAlgDoubleEMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenAlgDoubleEMajorant (zPathMajorant q hq) (aPathMajorant q hq)
      (bPathMajorant q hq)).majorant.eval frozenMajorantRadius ≤ 96 := by
  rw [frozenAlgDoubleEMajorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  have hz := zPathMajorant_tenth_le q hq
  have ha := aPathMajorant_tenth_le q hq
  have hb := bPathMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hz ha hb ⊢
  linarith

private theorem frozenAlgDoubleBMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenAlgDoubleBMajorant (zPathMajorant q hq) (aPathMajorant q hq)
      (bPathMajorant q hq)).majorant.eval frozenMajorantRadius ≤ 15 := by
  rw [frozenAlgDoubleBMajorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X]
  have hr := frozenAlgRMajorant_tenth_le q hq
  have he := frozenAlgDoubleEMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hr he ⊢
  linarith

private theorem frozenPathYMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathYMajorant q hq).majorant.eval frozenMajorantRadius ≤ 1 / 5 := by
  rw [frozenPathYMajorant_majorant, frozenPathAMajorant_majorant]
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have ha := frozenAlgAMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at ha ⊢
  linarith

private theorem frozenPathWMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathWMajorant q hq).majorant.eval frozenMajorantRadius ≤ 6 / 25 := by
  rw [frozenPathWMajorant_majorant, frozenPathRMajorant_majorant]
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  have hr := frozenAlgRMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hr ⊢
  linarith

private theorem frozenPathVMajorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathVMajorant q hq).majorant.eval frozenMajorantRadius ≤ 3 / 4 := by
  rw [frozenPathVMajorant_majorant, frozenPathRMajorant_majorant,
    frozenPathEMajorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  have hr := frozenAlgRMajorant_tenth_le q hq
  have he := frozenAlgEMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hr he ⊢
  linarith

private theorem frozenPathD4Majorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathD4Majorant q hq).majorant.eval frozenMajorantRadius ≤ 11 / 10 := by
  rw [frozenPathD4Majorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_X]
  have hy := frozenPathYMajorant_tenth_le q hq
  norm_num [frozenMajorantRadius] at hy ⊢
  linarith

private theorem frozenPathD3Majorant_tenth_le (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathD3Majorant q hq).majorant.eval frozenMajorantRadius ≤ 5 / 4 := by
  rw [frozenPathD3Majorant_majorant]
  simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul]
  have hw := frozenPathWMajorant_tenth_le q hq
  have hv := frozenPathVMajorant_tenth_le q hq
  have hw0 : 0 ≤ (frozenPathWMajorant q hq).majorant.eval
      frozenMajorantRadius :=
    majorant_eval_nonneg (frozenPathWMajorant q hq)
      (by norm_num [frozenMajorantRadius])
  have hv0 : 0 ≤ (frozenPathVMajorant q hq).majorant.eval
      frozenMajorantRadius :=
    majorant_eval_nonneg (frozenPathVMajorant q hq)
      (by norm_num [frozenMajorantRadius])
  have hprod :
      (frozenPathWMajorant q hq).majorant.eval frozenMajorantRadius *
          (frozenPathVMajorant q hq).majorant.eval frozenMajorantRadius ≤
        (6 / 25 : ℝ) * (3 / 4 : ℝ) :=
    mul_le_mul hw hv hv0 (by norm_num)
  norm_num at hprod ⊢
  linarith

private theorem frozenPathDensityDenominatorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (frozenPathDensityDenominatorMajorant q hq).majorant.eval
      frozenMajorantRadius ≤ 11 / 10 := by
  rw [frozenPathDensityDenominatorMajorant_majorant]
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hy := frozenPathYMajorant_tenth_le q hq
  have hy0 : 0 ≤ (frozenPathYMajorant q hq).majorant.eval
      frozenMajorantRadius :=
    majorant_eval_nonneg (frozenPathYMajorant q hq)
      (by norm_num [frozenMajorantRadius])
  have hy2nonneg := mul_nonneg hy0 (sub_nonneg.mpr hy)
  norm_num [frozenMajorantRadius] at hy2nonneg ⊢
  nlinarith

theorem frozenPathCommonDenominatorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (frozenPathCommonDenominatorMajorant q hq).majorant.eval
      frozenMajorantRadius ≤ 43923 / 5120 := by
  rw [frozenPathCommonDenominatorMajorant_majorant]
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow]
  have hdensity := frozenPathDensityDenominatorMajorant_tenth_le q hq
  have hd3 := frozenPathD3Majorant_tenth_le q hq
  have hd4 := frozenPathD4Majorant_tenth_le q hq
  have hdensity0 :
      0 ≤ (frozenPathDensityDenominatorMajorant q hq).majorant.eval
        frozenMajorantRadius :=
    majorant_eval_nonneg (frozenPathDensityDenominatorMajorant q hq)
      (by norm_num [frozenMajorantRadius])
  have hd30 : 0 ≤ (frozenPathD3Majorant q hq).majorant.eval
      frozenMajorantRadius :=
    majorant_eval_nonneg (frozenPathD3Majorant q hq)
      (by norm_num [frozenMajorantRadius])
  have hd40 : 0 ≤ (frozenPathD4Majorant q hq).majorant.eval
      frozenMajorantRadius :=
    majorant_eval_nonneg (frozenPathD4Majorant q hq)
      (by norm_num [frozenMajorantRadius])
  have hdensityScaled :
      3 * (frozenPathDensityDenominatorMajorant q hq).majorant.eval
          frozenMajorantRadius ≤ 3 * (11 / 10 : ℝ) :=
    mul_le_mul_of_nonneg_left hdensity (by norm_num)
  have hd3pow :
      (frozenPathD3Majorant q hq).majorant.eval frozenMajorantRadius ^ 3 ≤
        (5 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ hd30 hd3 3
  have hd4pow :
      (frozenPathD4Majorant q hq).majorant.eval frozenMajorantRadius ^ 3 ≤
        (11 / 10 : ℝ) ^ 3 := pow_le_pow_left₀ hd40 hd4 3
  have hfirst := mul_le_mul hdensityScaled hd3pow
    (pow_nonneg hd30 3) (by norm_num)
  have hall := mul_le_mul hfirst hd4pow
    (pow_nonneg hd40 3) (by norm_num)
  exact hall.trans (by norm_num)

/-- A scalar bound for a coefficientwise majorant at the relaxed radius. -/
private def TenthBound {p : ℝ[X]} (P : PolynomialMajorant p) (M : ℝ) : Prop :=
  P.majorant.eval frozenMajorantRadius ≤ M

private theorem tenthBound_nonneg {p : ℝ[X]} (P : PolynomialMajorant p) :
    0 ≤ P.majorant.eval frozenMajorantRadius :=
  majorant_eval_nonneg P (by norm_num [frozenMajorantRadius])

private theorem tenthBound_add {p q : ℝ[X]} {P : PolynomialMajorant p}
    {Q : PolynomialMajorant q} {a b : ℝ}
    (hP : TenthBound P a) (hQ : TenthBound Q b) :
    TenthBound (P.add Q) (a + b) := by
  simp only [TenthBound, PolynomialMajorant.add_majorant,
    Polynomial.eval_add] at hP hQ ⊢
  linarith

private theorem tenthBound_sub {p q : ℝ[X]} {P : PolynomialMajorant p}
    {Q : PolynomialMajorant q} {a b : ℝ}
    (hP : TenthBound P a) (hQ : TenthBound Q b) :
    TenthBound (P.sub Q) (a + b) := by
  simp only [TenthBound, PolynomialMajorant.sub_majorant,
    Polynomial.eval_add] at hP hQ ⊢
  linarith

private theorem tenthBound_neg {p : ℝ[X]} {P : PolynomialMajorant p}
    {a : ℝ} (hP : TenthBound P a) : TenthBound P.neg a := by
  simpa only [TenthBound, PolynomialMajorant.neg_majorant] using hP

private theorem tenthBound_mul {p q : ℝ[X]} {P : PolynomialMajorant p}
    {Q : PolynomialMajorant q} {a b : ℝ}
    (hP : TenthBound P a) (hQ : TenthBound Q b) (ha : 0 ≤ a) :
    TenthBound (P.mul Q) (a * b) := by
  simp only [TenthBound, PolynomialMajorant.mul_majorant,
    Polynomial.eval_mul] at hP hQ ⊢
  exact mul_le_mul hP hQ (tenthBound_nonneg Q) ha

private theorem tenthBound_pow {p : ℝ[X]} {P : PolynomialMajorant p}
    {a : ℝ} (hP : TenthBound P a) (n : ℕ) :
    TenthBound (P.pow n) (a ^ n) := by
  simp only [TenthBound, PolynomialMajorant.pow_majorant,
    Polynomial.eval_pow] at hP ⊢
  exact pow_le_pow_left₀ (tenthBound_nonneg P) hP n

private theorem tenthBound_widen {p : ℝ[X]} {P : PolynomialMajorant p}
    {a b : ℝ} (hP : TenthBound P a) (hab : a ≤ b) :
    TenthBound P b :=
  hP.trans hab

private theorem tenthBound_reindex {p q : ℝ[X]} {P : PolynomialMajorant p}
    {M : ℝ} (e : p = q) (hP : TenthBound P M) :
    TenthBound (P.reindex e) M := by
  simpa [TenthBound] using hP

private theorem tenthBound_nat (n : ℕ) : TenthBound (natMajorant n) n := by
  simp [TenthBound, frozenMajorantRadius]

private theorem tenthBound_rational {r M : ℝ} (h : |r| ≤ M) :
    TenthBound (rationalMajorant r) M := by
  simpa [TenthBound, rationalMajorant] using h

private theorem eval_natPolynomial (x : ℝ) (n : ℕ) :
    (n : ℝ[X]).eval x = n := by
  simp

private theorem tenthBound_Xpow (n : ℕ) :
    TenthBound (PolynomialMajorant.X.pow n) (frozenMajorantRadius ^ n) := by
  simp [TenthBound]

private theorem tenthBound_one : TenthBound oneMajorant 1 := by
  simp [TenthBound]

private theorem tenthBound_oneSubX2 :
    TenthBound oneSubX2Majorant (101 / 100) := by
  simp only [TenthBound, oneSubX2Majorant_majorant]
  norm_num [frozenMajorantRadius]

private theorem tenthBound_oneAddX2 :
    TenthBound oneAddX2Majorant (101 / 100) := by
  simp only [TenthBound, oneAddX2Majorant_majorant]
  norm_num [frozenMajorantRadius]

private theorem frozenAlgFoldNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgFoldNumeratorMajorant (zPathMajorant q hq) π) (29 / 2) := by
  let Z := zPathMajorant q hq
  let A := frozenAlgAMajorant Z
  have hZ : TenthBound Z (31 / 5) := by
    simpa [TenthBound, Z] using zPathMajorant_tenth_le q hq
  have hA : TenthBound A 2 := by
    simpa [TenthBound, A, Z] using frozenAlgAMajorant_tenth_le q hq
  have hpi : TenthBound (rationalMajorant π) 4 :=
    tenthBound_rational (by
      rw [abs_of_pos Real.pi_pos]
      exact Real.pi_lt_four.le)
  have hinner := tenthBound_sub tenthBound_one
    (tenthBound_mul (tenthBound_Xpow 2) hA (by positivity))
  have hleft := tenthBound_mul
    (tenthBound_mul hZ tenthBound_oneSubX2 (by norm_num)) hinner
    (by positivity)
  have hright := tenthBound_mul
    (tenthBound_mul hpi hA (by norm_num)) tenthBound_oneAddX2
    (by norm_num)
  have h := tenthBound_sub hleft hright
  unfold frozenAlgFoldNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

set_option maxHeartbeats 1000000 in
-- The six-piece cosine DAG needs additional elaboration heartbeats without
-- expanding its degree-23 majorant polynomial.
private theorem frozenAlgCosineNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgCosineNumeratorMajorant
      (zPathMajorant q hq) (aPathMajorant q hq) (bPathMajorant q hq))
      (9553 / 5) := by
  let z := (zPathMajorant q hq).majorant.eval frozenMajorantRadius
  let r := (frozenAlgRMajorant (aPathMajorant q hq)).majorant.eval
    frozenMajorantRadius
  let e := (frozenAlgDoubleEMajorant (zPathMajorant q hq)
    (aPathMajorant q hq) (bPathMajorant q hq)).majorant.eval
    frozenMajorantRadius
  have hz : z ≤ 31 / 5 := by
    simpa [z] using zPathMajorant_tenth_le q hq
  have hr : r ≤ 12 / 5 := by
    simpa [r] using frozenAlgRMajorant_tenth_le q hq
  have he : e ≤ 96 := by
    simpa [e] using frozenAlgDoubleEMajorant_tenth_le q hq
  have hz0 : 0 ≤ z := by
    exact tenthBound_nonneg (zPathMajorant q hq)
  have hr0 : 0 ≤ r := by
    exact tenthBound_nonneg (frozenAlgRMajorant (aPathMajorant q hq))
  have he0 : 0 ≤ e := by
    exact tenthBound_nonneg (frozenAlgDoubleEMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) (bPathMajorant q hq))
  have h0 :
      4 * e * r + 8 * z ≤ 4 * 96 * (12 / 5) + 8 * (31 / 5) := by
    gcongr
  have h1 :
      frozenMajorantRadius * (e ^ 2 + 4 * z ^ 2) ≤
        (1 / 10 : ℝ) * (96 ^ 2 + 4 * (31 / 5) ^ 2) := by
    gcongr
    all_goals norm_num [frozenMajorantRadius]
  have h4 :
      frozenMajorantRadius ^ 4 *
          (4 * e * r + 8 * r ^ 4 * z) ≤
        (1 / 10 : ℝ) ^ 4 *
          (4 * 96 * (12 / 5) + 8 * (12 / 5) ^ 4 * (31 / 5)) := by
    gcongr
    all_goals norm_num [frozenMajorantRadius]
  have h5 :
      frozenMajorantRadius ^ 5 *
          (e ^ 2 + 8 * e * r ^ 3 * z + 8 * e * r * z +
            4 * r ^ 4 * z ^ 2) ≤
        (1 / 10 : ℝ) ^ 5 *
          (96 ^ 2 + 8 * 96 * (12 / 5) ^ 3 * (31 / 5) +
            8 * 96 * (12 / 5) * (31 / 5) +
            4 * (12 / 5) ^ 4 * (31 / 5) ^ 2) := by
    gcongr
    all_goals norm_num [frozenMajorantRadius]
  have h6 :
      frozenMajorantRadius ^ 6 *
          (2 * e ^ 2 * r ^ 2 * z + 2 * e ^ 2 * z +
            4 * e * r ^ 3 * z ^ 2 + 4 * e * r * z ^ 2) ≤
        (1 / 10 : ℝ) ^ 6 *
          (2 * 96 ^ 2 * (12 / 5) ^ 2 * (31 / 5) +
            2 * 96 ^ 2 * (31 / 5) +
            4 * 96 * (12 / 5) ^ 3 * (31 / 5) ^ 2 +
            4 * 96 * (12 / 5) * (31 / 5) ^ 2) := by
    gcongr
    all_goals norm_num [frozenMajorantRadius]
  have h7 :
      frozenMajorantRadius ^ 7 *
          (e ^ 2 * r ^ 2 * z ^ 2 + e ^ 2 * z ^ 2) ≤
        (1 / 10 : ℝ) ^ 7 *
          (96 ^ 2 * (12 / 5) ^ 2 * (31 / 5) ^ 2 +
            96 ^ 2 * (31 / 5) ^ 2) := by
    gcongr
    all_goals norm_num [frozenMajorantRadius]
  dsimp only [TenthBound, frozenAlgCosineNumeratorMajorant,
    PolynomialMajorant.reindex]
  simp only [PolynomialMajorant.add_majorant,
    PolynomialMajorant.sub_majorant, PolynomialMajorant.neg_majorant,
    PolynomialMajorant.mul_majorant, PolynomialMajorant.pow_majorant,
    PolynomialMajorant.X_majorant, natMajorant_majorant,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, eval_natPolynomial]
  change 4 * e * r + 8 * z +
      frozenMajorantRadius * (e ^ 2 + 4 * z ^ 2) +
      frozenMajorantRadius ^ 4 * (4 * e * r + 8 * r ^ 4 * z) +
      frozenMajorantRadius ^ 5 *
        (e ^ 2 + 8 * e * r ^ 3 * z + 8 * e * r * z +
          4 * r ^ 4 * z ^ 2) +
      frozenMajorantRadius ^ 6 *
        (2 * e ^ 2 * r ^ 2 * z + 2 * e ^ 2 * z +
          4 * e * r ^ 3 * z ^ 2 + 4 * e * r * z ^ 2) +
      frozenMajorantRadius ^ 7 *
        (e ^ 2 * r ^ 2 * z ^ 2 + e ^ 2 * z ^ 2) ≤ 9553 / 5
  norm_num [frozenMajorantRadius] at h0 h1 h4 h5 h6 h7 ⊢
  linarith

private theorem frozenAlgKMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgKMajorant (aPathMajorant q hq)) (161 / 10) := by
  let R := frozenAlgRMajorant (aPathMajorant q hq)
  have hR : TenthBound R (12 / 5) := by
    simpa [TenthBound, R] using frozenAlgRMajorant_tenth_le q hq
  have hR2 := tenthBound_pow hR 2
  have hR4 := tenthBound_pow hR 4
  have h0 := tenthBound_sub
    (tenthBound_mul (tenthBound_nat 2) hR2 (by norm_num))
    (tenthBound_nat 4)
  have h2 := tenthBound_mul (tenthBound_Xpow 2)
    (tenthBound_sub hR4
      (tenthBound_mul (tenthBound_nat 4) hR2 (by norm_num)))
    (by positivity)
  have h4 := tenthBound_mul
    (tenthBound_mul (tenthBound_nat 2) (tenthBound_Xpow 4) (by norm_num))
    (tenthBound_sub hR2 hR4) (by positivity)
  have h6 := tenthBound_mul (tenthBound_Xpow 6) hR4 (by positivity)
  have h := tenthBound_add (tenthBound_add (tenthBound_add h0 h2) h4) h6
  unfold frozenAlgKMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem tenthBound_X :
    TenthBound PolynomialMajorant.X frozenMajorantRadius := by
  simp [TenthBound]

private theorem frozenAlgUMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgUMajorant (zPathMajorant q hq)) (11 / 10) := by
  let A := frozenAlgAMajorant (zPathMajorant q hq)
  have hA : TenthBound A 2 := by
    simpa [TenthBound, A] using frozenAlgAMajorant_tenth_le q hq
  have hleft := tenthBound_pow tenthBound_oneSubX2 2
  have hright := tenthBound_add tenthBound_one
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hA 2)
      (by positivity))
  have h := tenthBound_mul hleft hright (by positivity)
  unfold frozenAlgUMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenAlgWMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgWMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) (bPathMajorant q hq)) 7 := by
  let R := frozenAlgRMajorant (aPathMajorant q hq)
  let DB := frozenAlgDoubleBMajorant (zPathMajorant q hq)
    (aPathMajorant q hq) (bPathMajorant q hq)
  have hR : TenthBound R (12 / 5) := by
    simpa [TenthBound, R] using frozenAlgRMajorant_tenth_le q hq
  have hDB : TenthBound DB 15 := by
    simpa [TenthBound, DB] using frozenAlgDoubleBMajorant_tenth_le q hq
  have hleft := tenthBound_pow
    (tenthBound_add tenthBound_one
      (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hR 2)
        (by positivity))) 2
  have hright := tenthBound_add (tenthBound_nat 4)
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hDB 2)
      (by positivity))
  have h := tenthBound_mul hleft hright (by positivity)
  unfold frozenAlgWMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenAlgAreaXMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgAreaXMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) (bPathMajorant q hq)) 8 := by
  let R := frozenAlgRMajorant (aPathMajorant q hq)
  let DB := frozenAlgDoubleBMajorant (zPathMajorant q hq)
    (aPathMajorant q hq) (bPathMajorant q hq)
  have hR : TenthBound R (12 / 5) := by
    simpa [TenthBound, R] using frozenAlgRMajorant_tenth_le q hq
  have hDB : TenthBound DB 15 := by
    simpa [TenthBound, DB] using frozenAlgDoubleBMajorant_tenth_le q hq
  have hleft := tenthBound_add (tenthBound_nat 3)
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hR 2)
      (by positivity))
  have hright := tenthBound_sub (tenthBound_nat 2)
    (tenthBound_mul
      (tenthBound_mul (tenthBound_Xpow 2) hR (by positivity)) hDB
      (by positivity))
  have h := tenthBound_mul hleft hright (by positivity)
  unfold frozenAlgAreaXMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenAlgAreaZMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgAreaZMajorant (zPathMajorant q hq)) (11 / 10) := by
  let A := frozenAlgAMajorant (zPathMajorant q hq)
  have hA : TenthBound A 2 := by
    simpa [TenthBound, A] using frozenAlgAMajorant_tenth_le q hq
  have hright := tenthBound_sub tenthBound_one
    (tenthBound_mul (tenthBound_Xpow 2) hA (by positivity))
  have h := tenthBound_mul tenthBound_oneSubX2 hright (by norm_num)
  unfold frozenAlgAreaZMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenAlgAreaLMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgAreaLMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) (bPathMajorant q hq)) (2093 / 20) := by
  let A := frozenAlgAMajorant (zPathMajorant q hq)
  let DB := frozenAlgDoubleBMajorant (zPathMajorant q hq)
    (aPathMajorant q hq) (bPathMajorant q hq)
  have hA : TenthBound A 2 := by
    simpa [TenthBound, A] using frozenAlgAMajorant_tenth_le q hq
  have hDB : TenthBound DB 15 := by
    simpa [TenthBound, DB] using frozenAlgDoubleBMajorant_tenth_le q hq
  have hK := frozenAlgKMajorant_tenth_le q hq
  have hleft := tenthBound_add tenthBound_one
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hA 2)
      (by positivity))
  have hmiddle := tenthBound_add (tenthBound_nat 4)
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hDB 2)
      (by positivity))
  have h := tenthBound_mul
    (tenthBound_mul hleft hmiddle (by positivity)) hK (by positivity)
  unfold frozenAlgAreaLMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenAlgAreaNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgAreaNumeratorMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) (bPathMajorant q hq) π) (160443 / 50) := by
  let Z := zPathMajorant q hq
  let E := frozenAlgDoubleEMajorant Z (aPathMajorant q hq)
    (bPathMajorant q hq)
  let U := frozenAlgUMajorant Z
  let W := frozenAlgWMajorant Z (aPathMajorant q hq) (bPathMajorant q hq)
  let AX := frozenAlgAreaXMajorant Z (aPathMajorant q hq)
    (bPathMajorant q hq)
  let AZ := frozenAlgAreaZMajorant Z
  let AL := frozenAlgAreaLMajorant Z (aPathMajorant q hq)
    (bPathMajorant q hq)
  have hZ : TenthBound Z (31 / 5) := by
    simpa [TenthBound, Z] using zPathMajorant_tenth_le q hq
  have hE : TenthBound E 96 := by
    simpa [TenthBound, E, Z] using frozenAlgDoubleEMajorant_tenth_le q hq
  have hU : TenthBound U (11 / 10) := by
    simpa [U, Z] using frozenAlgUMajorant_tenth_le q hq
  have hW : TenthBound W 7 := by
    simpa [W, Z] using frozenAlgWMajorant_tenth_le q hq
  have hAX : TenthBound AX 8 := by
    simpa [AX, Z] using frozenAlgAreaXMajorant_tenth_le q hq
  have hAZ : TenthBound AZ (11 / 10) := by
    simpa [AZ, Z] using frozenAlgAreaZMajorant_tenth_le q hq
  have hAL : TenthBound AL (2093 / 20) := by
    simpa [AL, Z] using frozenAlgAreaLMajorant_tenth_le q hq
  have hpi : TenthBound (rationalMajorant π) 4 :=
    tenthBound_rational (by
      rw [abs_of_pos Real.pi_pos]
      exact Real.pi_lt_four.le)
  have h0 := tenthBound_mul hpi hAL (by norm_num)
  have h1 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_sub hE
        (tenthBound_mul (tenthBound_nat 4) hZ (by norm_num)))
      hU (by positivity)) hW (by positivity)
  have h2 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_nat 2) hE (by norm_num)) hU
      (by norm_num)) hAX (by positivity)
  have hDB : TenthBound
      (frozenAlgDoubleBMajorant Z (aPathMajorant q hq)
        (bPathMajorant q hq)) 15 := by
    dsimp only [TenthBound, Z]
    exact frozenAlgDoubleBMajorant_tenth_le q hq
  have h3 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_nat 4) hZ (by norm_num))
        (tenthBound_add (tenthBound_nat 4)
          (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hDB 2)
            (by positivity)))
        (by positivity)) hAZ (by positivity)
  have h := tenthBound_sub (tenthBound_add (tenthBound_add h0 h1) h2) h3
  unfold frozenAlgAreaNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenAlgQPrimeMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgQPrimeMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) π) (83 / 4) := by
  have hZ : TenthBound (zPathMajorant q hq) (31 / 5) := by
    simpa [TenthBound] using zPathMajorant_tenth_le q hq
  have hA : TenthBound (aPathMajorant q hq) (191 / 50) := by
    simpa [TenthBound] using aPathMajorant_tenth_le q hq
  have hpi : TenthBound (rationalMajorant π) 4 :=
    tenthBound_rational (by
      rw [abs_of_pos Real.pi_pos]
      exact Real.pi_lt_four.le)
  have hthird : TenthBound (rationalMajorant (1 / 3 : ℝ)) (1 / 3) :=
    tenthBound_rational (by norm_num)
  have h := tenthBound_sub
    (tenthBound_mul (tenthBound_nat 4) hA (by norm_num))
    (tenthBound_mul hthird
      (tenthBound_add
        (tenthBound_mul (tenthBound_nat 2) hZ (by norm_num)) hpi)
      (by norm_num))
  unfold frozenAlgQPrimeMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num)

private theorem frozenAlgThirdNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenAlgThirdNumeratorMajorant (zPathMajorant q hq)
      (aPathMajorant q hq) (bPathMajorant q hq) π) (6750317 / 600) := by
  let Z := zPathMajorant q hq
  let area := frozenAlgAreaNumeratorMajorant Z (aPathMajorant q hq)
    (bPathMajorant q hq) π
  let cosine := frozenAlgCosineNumeratorMajorant Z (aPathMajorant q hq)
    (bPathMajorant q hq)
  let fold := frozenAlgFoldNumeratorMajorant Z π
  let qprime := frozenAlgQPrimeMajorant Z (aPathMajorant q hq) π
  have hZ : TenthBound Z (31 / 5) := by
    simpa [TenthBound, Z] using zPathMajorant_tenth_le q hq
  have harea : TenthBound area (160443 / 50) := by
    simpa [area, Z] using frozenAlgAreaNumeratorMajorant_tenth_le q hq
  have hcosine : TenthBound cosine (9553 / 5) := by
    simpa [cosine, Z] using frozenAlgCosineNumeratorMajorant_tenth_le q hq
  have hfold : TenthBound fold (29 / 2) := by
    simpa [fold, Z] using frozenAlgFoldNumeratorMajorant_tenth_le q hq
  have hqprime : TenthBound qprime (83 / 4) := by
    simpa [qprime, Z] using frozenAlgQPrimeMajorant_tenth_le q hq
  have heighthirds :
      TenthBound (rationalMajorant (8 / 3 : ℝ)) (8 / 3) :=
    tenthBound_rational (by norm_num)
  have hinner := tenthBound_sub
    (tenthBound_mul hqprime hcosine (by norm_num))
    (tenthBound_mul
      (tenthBound_mul heighthirds hZ (by norm_num)) hfold
      (by positivity))
  have h := tenthBound_add
    (tenthBound_add (tenthBound_sub harea
      (tenthBound_mul (tenthBound_nat 2) hcosine (by norm_num)))
      (tenthBound_mul (tenthBound_nat 16) hfold (by norm_num)))
    (tenthBound_mul tenthBound_X hinner
      (by norm_num [frozenMajorantRadius]))
  unfold frozenAlgThirdNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenH3PathNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenH3PathNumeratorMajorant q hq) (6750317 / 600) := by
  have h := frozenAlgThirdNumeratorMajorant_tenth_le q hq
  unfold frozenH3PathNumeratorMajorant
  apply tenthBound_reindex
  exact h

private theorem frozenH3PathPolynomialMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenH3PathPolynomialMajorant q hq) 1125053 := by
  have hnum := frozenH3PathNumeratorMajorant_tenth_le q hq
  have hscaled := sq_mul_divX_two_eval_le_eval
    (frozenH3PathNumeratorMajorant q hq).majorant
    (frozenH3PathNumeratorMajorant q hq).coeff_nonneg
    (show 0 ≤ frozenMajorantRadius by norm_num [frozenMajorantRadius])
  have hdiv :
      TenthBound ((frozenH3PathNumeratorMajorant q hq).divX.divX)
        1125053 := by
    dsimp only [TenthBound, PolynomialMajorant.divX]
    have h := hscaled.trans hnum
    norm_num [TenthBound, frozenMajorantRadius] at h ⊢
    linarith
  unfold frozenH3PathPolynomialMajorant
  apply tenthBound_reindex
  exact hdiv

private theorem frozenPathDensityNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathDensityNumeratorMajorant q hq) 33 := by
  have hZ : TenthBound (zPathMajorant q hq) (31 / 5) := by
    simpa [TenthBound] using zPathMajorant_tenth_le q hq
  have h2Z := tenthBound_mul (tenthBound_nat 2) hZ (by norm_num)
  have hXZ := tenthBound_mul tenthBound_X hZ
    (by norm_num [frozenMajorantRadius])
  have h := tenthBound_mul h2Z
    (tenthBound_add (tenthBound_nat 2) hXZ)
    (by norm_num [frozenMajorantRadius])
  unfold frozenPathDensityNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenPathRhoNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathRhoNumeratorMajorant q hq) (1313 / 1250) := by
  have hY : TenthBound (frozenPathYMajorant q hq) (1 / 5) := by
    simpa [TenthBound] using frozenPathYMajorant_tenth_le q hq
  have h := tenthBound_mul tenthBound_oneSubX2
    (tenthBound_add tenthBound_one (tenthBound_pow hY 2)) (by norm_num)
  unfold frozenPathRhoNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num)

private theorem frozenPathFourIncrementNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathFourIncrementNumeratorMajorant q hq) 95 := by
  let Z := zPathMajorant q hq
  have hZ : TenthBound Z (31 / 5) := by
    simpa [TenthBound, Z] using zPathMajorant_tenth_le q hq
  have hA : TenthBound (frozenPathAMajorant q hq) 2 := by
    simpa [TenthBound] using frozenAlgAMajorant_tenth_le q hq
  have hD4 : TenthBound (frozenPathD4Majorant q hq) (11 / 10) := by
    simpa [TenthBound] using frozenPathD4Majorant_tenth_le q hq
  have hleft := tenthBound_neg
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hZ 2)
      (by norm_num [frozenMajorantRadius]))
  have hright := tenthBound_mul
    (tenthBound_mul (tenthBound_nat 3) hA (by norm_num))
    (tenthBound_pow hD4 2) (by norm_num)
  have h := tenthBound_mul
    (tenthBound_mul (tenthBound_nat 2) hZ (by norm_num))
    (tenthBound_sub hleft hright) (by norm_num [frozenMajorantRadius])
  unfold frozenPathFourIncrementNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenPathThreeIncrementNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathThreeIncrementNumeratorMajorant q hq) 10000 := by
  let E := frozenPathEMajorant q hq
  let R := frozenPathRMajorant q hq
  have hE : TenthBound E 48 := by
    simpa [TenthBound, E] using frozenAlgEMajorant_tenth_le q hq
  have hR : TenthBound R (12 / 5) := by
    simpa [TenthBound, R] using frozenAlgRMajorant_tenth_le q hq
  have hD3 : TenthBound (frozenPathD3Majorant q hq) (5 / 4) := by
    simpa [TenthBound] using frozenPathD3Majorant_tenth_le q hq
  have hleft := tenthBound_neg
    (tenthBound_mul (tenthBound_Xpow 2) (tenthBound_pow hE 2)
      (by norm_num [frozenMajorantRadius]))
  have hRplus := tenthBound_add hR
    (tenthBound_mul tenthBound_X hE
      (by norm_num [frozenMajorantRadius]))
  have hright := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_nat 3) hR (by norm_num)) hRplus
      (by norm_num [frozenMajorantRadius]))
    (tenthBound_pow hD3 2) (by norm_num [frozenMajorantRadius])
  have h := tenthBound_mul
    (tenthBound_mul (tenthBound_nat 2) hE (by norm_num))
    (tenthBound_sub hleft hright) (by norm_num [frozenMajorantRadius])
  unfold frozenPathThreeIncrementNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenPathFourBarNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathFourBarNumeratorMajorant q hq)
      (26379901 / 50000) := by
  let density := frozenPathDensityNumeratorMajorant q hq
  let D4 := frozenPathD4Majorant q hq
  have hdensity : TenthBound density 33 := by
    simpa [density] using frozenPathDensityNumeratorMajorant_tenth_le q hq
  have hD4 : TenthBound D4 (11 / 10) := by
    simpa [TenthBound, D4] using frozenPathD4Majorant_tenth_le q hq
  have hrho := frozenPathRhoNumeratorMajorant_tenth_le q hq
  have hinc := frozenPathFourIncrementNumeratorMajorant_tenth_le q hq
  have hZ : TenthBound (zPathMajorant q hq) (31 / 5) := by
    simpa [TenthBound] using zPathMajorant_tenth_le q hq
  have ht0 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_nat 2) hdensity (by norm_num))
      (tenthBound_sub (tenthBound_nat 3) (tenthBound_Xpow 2))
      (by norm_num [frozenMajorantRadius]))
    (tenthBound_pow hD4 3) (by norm_num [frozenMajorantRadius])
  have ht1 := tenthBound_mul hrho hinc
    (by norm_num [frozenMajorantRadius])
  have ht2 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul
        (tenthBound_mul (tenthBound_nat 6) tenthBound_X (by norm_num))
        hZ (by norm_num [frozenMajorantRadius]))
      hdensity (by norm_num [frozenMajorantRadius]))
    (tenthBound_pow hD4 3) (by norm_num [frozenMajorantRadius])
  have h := tenthBound_add (tenthBound_add ht0 ht1) ht2
  unfold frozenPathFourBarNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenPathThreeBarNumeratorMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathThreeBarNumeratorMajorant q hq)
      (2661239 / 200) := by
  let density := frozenPathDensityNumeratorMajorant q hq
  let R := frozenPathRMajorant q hq
  let D3 := frozenPathD3Majorant q hq
  have hdensity : TenthBound density 33 := by
    simpa [density] using frozenPathDensityNumeratorMajorant_tenth_le q hq
  have hR : TenthBound R (12 / 5) := by
    simpa [TenthBound, R] using frozenAlgRMajorant_tenth_le q hq
  have hD3 : TenthBound D3 (5 / 4) := by
    simpa [TenthBound, D3] using frozenPathD3Majorant_tenth_le q hq
  have hW : TenthBound (frozenPathWMajorant q hq) (6 / 25) := by
    simpa [TenthBound] using frozenPathWMajorant_tenth_le q hq
  have hE : TenthBound (frozenPathEMajorant q hq) 48 := by
    simpa [TenthBound] using frozenAlgEMajorant_tenth_le q hq
  have ht0 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul
        (tenthBound_mul (tenthBound_nat 2) hdensity (by norm_num)) hR
        (by norm_num [frozenMajorantRadius]))
      (tenthBound_sub (tenthBound_nat 3) (tenthBound_pow hW 2))
      (by norm_num [frozenMajorantRadius]))
    (tenthBound_pow hD3 3) (by norm_num [frozenMajorantRadius])
  have ht1 := tenthBound_mul
    (frozenPathRhoNumeratorMajorant_tenth_le q hq)
    (frozenPathThreeIncrementNumeratorMajorant_tenth_le q hq)
    (by norm_num [frozenMajorantRadius])
  have ht2 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul
        (tenthBound_mul (tenthBound_nat 6) tenthBound_X (by norm_num))
        hE (by norm_num [frozenMajorantRadius]))
      hdensity (by norm_num [frozenMajorantRadius]))
    (tenthBound_pow hD3 3) (by norm_num [frozenMajorantRadius])
  have h := tenthBound_add (tenthBound_add ht0 ht1) ht2
  unfold frozenPathThreeBarNumeratorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenPathThreeCoefficientMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathThreeCoefficientMajorant q hq) 8 := by
  have hW : TenthBound (frozenPathWMajorant q hq) (6 / 25) := by
    simpa [TenthBound] using frozenPathWMajorant_tenth_le q hq
  have hY : TenthBound (frozenPathYMajorant q hq) (1 / 5) := by
    simpa [TenthBound] using frozenPathYMajorant_tenth_le q hq
  have hV : TenthBound (frozenPathVMajorant q hq) (3 / 4) := by
    simpa [TenthBound] using frozenPathVMajorant_tenth_le q hq
  have h := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul
        (tenthBound_mul (tenthBound_nat 4)
          (tenthBound_pow tenthBound_oneSubX2 2) (by norm_num))
        (tenthBound_pow
          (tenthBound_add tenthBound_one (tenthBound_pow hW 2)) 2)
        (by norm_num [frozenMajorantRadius]))
      (tenthBound_add tenthBound_one (tenthBound_pow hY 2))
      (by norm_num [frozenMajorantRadius]))
    (tenthBound_add tenthBound_one (tenthBound_pow hV 2))
    (by norm_num [frozenMajorantRadius])
  unfold frozenPathThreeCoefficientMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num)

private theorem frozenPathFourCoefficientMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathFourCoefficientMajorant q hq) 14 := by
  have hY : TenthBound (frozenPathYMajorant q hq) (1 / 5) := by
    simpa [TenthBound] using frozenPathYMajorant_tenth_le q hq
  have hV : TenthBound (frozenPathVMajorant q hq) (3 / 4) := by
    simpa [TenthBound] using frozenPathVMajorant_tenth_le q hq
  have h := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_neg (tenthBound_nat 8))
        (tenthBound_pow tenthBound_oneAddX2 2) (by norm_num))
      (tenthBound_add tenthBound_one (tenthBound_pow hY 2))
      (by norm_num [frozenMajorantRadius]))
    (tenthBound_add tenthBound_one (tenthBound_pow hV 2))
    (by norm_num [frozenMajorantRadius])
  unfold frozenPathFourCoefficientMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num)

private theorem frozenPathPiCoefficientMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathPiCoefficientMajorant q hq) (64883 / 25) := by
  have hZ : TenthBound (zPathMajorant q hq) (31 / 5) := by
    simpa [TenthBound] using zPathMajorant_tenth_le q hq
  have hK := frozenAlgKMajorant_tenth_le q hq
  have hY : TenthBound (frozenPathYMajorant q hq) (1 / 5) := by
    simpa [TenthBound] using frozenPathYMajorant_tenth_le q hq
  have hV : TenthBound (frozenPathVMajorant q hq) (3 / 4) := by
    simpa [TenthBound] using frozenPathVMajorant_tenth_le q hq
  have h := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul
        (tenthBound_mul (tenthBound_nat 16) hZ (by norm_num)) hK
        (by norm_num))
      (tenthBound_add tenthBound_one (tenthBound_pow hY 2))
      (by norm_num [frozenMajorantRadius]))
    (tenthBound_add tenthBound_one (tenthBound_pow hV 2))
    (by norm_num [frozenMajorantRadius])
  unfold frozenPathPiCoefficientMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num)

private theorem frozenPathFoldCoefficientMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenPathFoldCoefficientMajorant q hq) 72 := by
  have hZ : TenthBound (zPathMajorant q hq) (31 / 5) := by
    simpa [TenthBound] using zPathMajorant_tenth_le q hq
  have hA : TenthBound (frozenPathAMajorant q hq) 2 := by
    simpa [TenthBound] using frozenAlgAMajorant_tenth_le q hq
  have h23 : TenthBound (rationalMajorant (2 / 3 : ℝ)) (2 / 3) :=
    tenthBound_rational (by norm_num)
  have hinner := tenthBound_sub (tenthBound_nat 4)
    (tenthBound_mul (tenthBound_mul h23 hZ (by norm_num)) tenthBound_X
      (by norm_num))
  have h := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_neg hinner) (tenthBound_nat 8)
        (by norm_num [frozenMajorantRadius]))
      hA (by norm_num [frozenMajorantRadius]))
    tenthBound_oneAddX2 (by norm_num [frozenMajorantRadius])
  unfold frozenPathFoldCoefficientMajorant
  apply tenthBound_reindex
  exact tenthBound_widen h (by norm_num [frozenMajorantRadius])

private theorem frozenEndpointQuadraticMajorant_tenth_le
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    TenthBound (frozenEndpointQuadraticMajorant q hq) 16 := by
  simp [TenthBound, frozenEndpointQuadraticMajorant, boundedC]

/-- The complete cleared-error coefficient majorant has value at most
`7870625783673 / 800000` at the relaxed radius `1/10`. -/
theorem errorMajorant_tenth_le (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (errorMajorant q hq).majorant.eval frozenMajorantRadius ≤
      7870625783673 / 800000 := by
  let commonD := frozenPathCommonDenominatorMajorant q hq
  let D3 := frozenPathD3Majorant q hq
  let D4 := frozenPathD4Majorant q hq
  let threeC := frozenPathThreeCoefficientMajorant q hq
  let fourC := frozenPathFourCoefficientMajorant q hq
  let foldC := frozenPathFoldCoefficientMajorant q hq
  have hD : TenthBound commonD (43923 / 5120) := by
    simpa [TenthBound, commonD] using
      frozenPathCommonDenominatorMajorant_tenth_le q hq
  have hD3 : TenthBound D3 (5 / 4) := by
    simpa [TenthBound, D3] using frozenPathD3Majorant_tenth_le q hq
  have hD4 : TenthBound D4 (11 / 10) := by
    simpa [TenthBound, D4] using frozenPathD4Majorant_tenth_le q hq
  have hthreeC : TenthBound threeC 8 := by
    simpa [threeC] using frozenPathThreeCoefficientMajorant_tenth_le q hq
  have hfourC : TenthBound fourC 14 := by
    simpa [fourC] using frozenPathFourCoefficientMajorant_tenth_le q hq
  have hfoldC : TenthBound foldC 72 := by
    simpa [foldC] using frozenPathFoldCoefficientMajorant_tenth_le q hq
  have hZ : TenthBound (zPathMajorant q hq) (31 / 5) := by
    simpa [TenthBound] using zPathMajorant_tenth_le q hq
  have h0 := tenthBound_mul hD
    (frozenH3PathPolynomialMajorant_tenth_le q hq) (by norm_num)
  have h1 := tenthBound_mul
    (tenthBound_mul (tenthBound_pow hD4 3) hthreeC (by positivity))
    (frozenPathThreeBarNumeratorMajorant_tenth_le q hq) (by positivity)
  have h2 := tenthBound_mul
    (tenthBound_mul (tenthBound_pow hD3 3) hfourC (by positivity))
    (frozenPathFourBarNumeratorMajorant_tenth_le q hq) (by positivity)
  have h3 := tenthBound_mul hD
    (frozenPathPiCoefficientMajorant_tenth_le q hq) (by norm_num)
  have h4 := tenthBound_mul
    (tenthBound_mul hD hfoldC (by norm_num))
    (tenthBound_mul (tenthBound_nat 2) hZ (by norm_num))
    (by norm_num)
  have h5 := tenthBound_mul
    (tenthBound_mul
      (tenthBound_mul (tenthBound_pow hD3 3) hfoldC (by positivity))
      (tenthBound_Xpow 2) (by positivity))
    (frozenPathFourBarNumeratorMajorant_tenth_le q hq) (by positivity)
  have hcommon := tenthBound_add
    (tenthBound_add (tenthBound_add (tenthBound_add (tenthBound_add
      h0 h1) h2) h3) h4) h5
  have hcommon' :
      TenthBound (frozenPathCommonNumeratorMajorant q hq)
        (3935312342799 / 400000) := by
    unfold frozenPathCommonNumeratorMajorant
    apply tenthBound_reindex
    exact tenthBound_widen hcommon (by norm_num [frozenMajorantRadius])
  have hendpoint := tenthBound_mul
    (tenthBound_mul hD (tenthBound_Xpow 2) (by norm_num))
    (frozenEndpointQuadraticMajorant_tenth_le q hq) (by positivity)
  have herror := tenthBound_sub hcommon' hendpoint
  unfold errorMajorant
  apply tenthBound_reindex
  exact tenthBound_widen herror (by norm_num [frozenMajorantRadius])

/-- A radius-`1/10` majorant bounds the fourth-order tail on the common
physical radius `1/126334`; the exact cubic coefficient is kept separate. -/
private theorem cubicQuotient_abs_le_of_majorant_tenth
    {p : ℝ[X]} (P : PolynomialMajorant p) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hP : P.majorant.eval frozenMajorantRadius ≤
      7870625783673 / 800000)
    (hcubic : |p.divX.divX.divX.coeff 0| ≤ 736875) :
    |p.divX.divX.divX.eval s| ≤ 1515627 := by
  have hsr : s ≤ frozenMajorantRadius := by
    norm_num [frozenMajorantRadius] at hs ⊢
    linarith
  have hscaled :
      frozenMajorantRadius ^ 4 *
          P.majorant.divX.divX.divX.divX.eval frozenMajorantRadius ≤
        P.majorant.eval frozenMajorantRadius :=
    fourth_tail_scaled_le_eval P.majorant P.coeff_nonneg
      (by norm_num [frozenMajorantRadius])
  have hscaled' := hscaled.trans hP
  have htailR :
      P.majorant.divX.divX.divX.divX.eval frozenMajorantRadius ≤
        7870625783673 / 80 := by
    norm_num [frozenMajorantRadius] at hscaled'
    calc
      _ = 10000 * ((1 / 10000 : ℝ) *
          P.majorant.divX.divX.divX.divX.eval frozenMajorantRadius) := by
        ring
      _ ≤ 10000 * (7870625783673 / 800000 : ℝ) :=
        mul_le_mul_of_nonneg_left hscaled' (by norm_num)
      _ = 7870625783673 / 80 := by norm_num
  have htail : |p.divX.divX.divX.divX.eval s| ≤
      7870625783673 / 80 := by
    have habs : |s| ≤ frozenMajorantRadius := by
      rw [abs_of_nonneg hs0]
      exact hsr
    have hmajor :=
      (P.divX.divX.divX.divX).abs_eval_le_eval_of_abs_le habs
    simp only [PolynomialMajorant.divX_majorant] at hmajor
    exact hmajor.trans htailR
  have hsmalltail :
      s * |p.divX.divX.divX.divX.eval s| ≤ 778752 := by
    have hmul := mul_le_mul hs htail (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1 / 126334)
    norm_num at hmul ⊢
    linarith
  have hsplit := congrArg (Polynomial.eval s)
    (Polynomial.X_mul_divX_add p.divX.divX.divX)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C] at hsplit
  calc
    |p.divX.divX.divX.eval s| =
        |s * p.divX.divX.divX.divX.eval s +
          p.divX.divX.divX.coeff 0| :=
      congrArg abs hsplit.symm
    _ ≤ |s * p.divX.divX.divX.divX.eval s| +
          |p.divX.divX.divX.coeff 0| :=
      abs_add_le _ _
    _ = s * |p.divX.divX.divX.divX.eval s| +
          |p.divX.divX.divX.coeff 0| := by
      rw [abs_mul, abs_of_nonneg hs0]
    _ ≤ 778752 + 736875 := add_le_add hsmalltail hcubic
    _ ≤ 1515627 := by norm_num

/-- Explicit cubic-quotient contract on the relaxed next-cell radius. -/
theorem explicitThirdClearedErrorBound : ExplicitThirdClearedErrorBound := by
  intro s hspos hs q hq
  apply cubicQuotient_abs_le_of_majorant_tenth
    (errorMajorant q hq) s hspos.le hs
  · exact errorMajorant_tenth_le q hq
  · rw [frozenPathClearedError_divX_three_coeff_zero]
    exact frozenCommonCubic_abs_le q hq

/-- Fully explicit frozen third-row estimate on the radius-`1/126334` cell. -/
theorem explicitThirdFrozenEstimate : ExplicitThirdFrozenEstimate :=
  explicitThirdFrozenEstimate_of_cleared_error_bound
    explicitThirdClearedErrorBound
end FrozenPolynomial
end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
