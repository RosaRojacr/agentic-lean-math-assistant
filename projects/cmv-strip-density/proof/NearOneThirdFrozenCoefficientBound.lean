/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFrozenCoefficient
import NearOneRescaledFirstCell

/-!
# Uniform bound for the cleared-error cubic coefficient
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

private lemma cubic_component_interval_bounds :
    (1137753 : ℝ) ≤
        (90263 * π ^ 7 - 27975264 * π ^ 5 + 1163718144 * π ^ 3) /
          (7776 * π) ∧
    (90263 * π ^ 7 - 27975264 * π ^ 5 + 1163718144 * π ^ 3) /
          (7776 * π) ≤ 56887671 / 50 ∧
    (20140 : ℝ) ≤
        (-54756 * π ^ 4 - 6082560 * π ^ 2 + 557383680) /
          (7776 * π) ∧
    (-54756 * π ^ 4 - 6082560 * π ^ 2 + 557383680) /
          (7776 * π) ≤ 201407 / 10 ∧
    (-187763 : ℝ) ≤
        (310608 * π ^ 4 - 104758272 * π ^ 2 - 3583180800) /
          (7776 * π) ∧
    (310608 * π ^ 4 - 104758272 * π ^ 2 - 3583180800) /
          (7776 * π) ≤ -938811 / 5 ∧
    (-936971 / 1000 : ℝ) ≤
        (18144 * π ^ 3 - 7464960 * π) / (7776 * π) ∧
    (18144 * π ^ 3 - 7464960 * π) / (7776 * π) ≤ -936 := by
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  have hlo0 : (0 : ℝ) < 3.14159265358979323846 := by norm_num
  have hp2lo : (3.14159265358979323846 : ℝ) ^ 2 < π ^ 2 :=
    pow_lt_pow_left₀ hlo hlo0.le (by norm_num)
  have hp2hi : π ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  have hp3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ hlo hlo0.le (by norm_num)
  have hp3hi : π ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  have hp4lo : (3.14159265358979323846 : ℝ) ^ 4 < π ^ 4 :=
    pow_lt_pow_left₀ hlo hlo0.le (by norm_num)
  have hp4hi : π ^ 4 < (3.14159265358979323847 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  have hp5lo : (3.14159265358979323846 : ℝ) ^ 5 < π ^ 5 :=
    pow_lt_pow_left₀ hlo hlo0.le (by norm_num)
  have hp5hi : π ^ 5 < (3.14159265358979323847 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  have hp7lo : (3.14159265358979323846 : ℝ) ^ 7 < π ^ 7 :=
    pow_lt_pow_left₀ hlo hlo0.le (by norm_num)
  have hp7hi : π ^ 7 < (3.14159265358979323847 : ℝ) ^ 7 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  have hden : 0 < 7776 * π := by positivity
  repeat' apply And.intro
  · rw [le_div_iff₀ hden]
    norm_num at hlo hhi hp3lo hp3hi hp5lo hp5hi hp7lo hp7hi ⊢
    nlinarith
  · rw [div_le_iff₀ hden]
    norm_num at hlo hhi hp3lo hp3hi hp5lo hp5hi hp7lo hp7hi ⊢
    nlinarith
  · rw [le_div_iff₀ hden]
    norm_num at hlo hhi hp2lo hp2hi hp4lo hp4hi ⊢
    nlinarith
  · rw [div_le_iff₀ hden]
    norm_num at hlo hhi hp2lo hp2hi hp4lo hp4hi ⊢
    nlinarith
  · rw [le_div_iff₀ hden]
    norm_num at hlo hhi hp2lo hp2hi hp4lo hp4hi ⊢
    nlinarith
  · rw [div_le_iff₀ hden]
    norm_num at hlo hhi hp2lo hp2hi hp4lo hp4hi ⊢
    nlinarith
  · rw [le_div_iff₀ hden]
    norm_num at hlo hhi hp3lo hp3hi ⊢
    nlinarith
  · rw [div_le_iff₀ hden]
    norm_num at hlo hhi hp3lo hp3hi ⊢
    nlinarith

/-- Uniform endpoint-box bound for the exact cubic coefficient.  Keeping the
signed cancellation between its four affine components reduces the former
triangle-inequality bound by more than an order of magnitude. -/
theorem frozenCommonCubic_abs_le (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    |frozenCommonCubic q| ≤ 736875 := by
  rcases cubic_component_interval_bounds with
    ⟨hbaseLo, hbaseHi, h0Lo, h0Hi, h1Lo, h1Hi, h2Lo, h2Hi⟩
  have hq0 := hq (0 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  have hq2 := hq (2 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at hq2
  let cbase := (90263 * π ^ 7 - 27975264 * π ^ 5 +
    1163718144 * π ^ 3) / (7776 * π)
  let c0 := (-54756 * π ^ 4 - 6082560 * π ^ 2 + 557383680) /
    (7776 * π)
  let c1 := (310608 * π ^ 4 - 104758272 * π ^ 2 - 3583180800) /
    (7776 * π)
  let c2 := (18144 * π ^ 3 - 7464960 * π) / (7776 * π)
  have hcbaseLo : (1137753 : ℝ) ≤ cbase := by simpa [cbase] using hbaseLo
  have hcbaseHi : cbase ≤ (56887671 / 50 : ℝ) := by simpa [cbase] using hbaseHi
  have hc0Lo : (20140 : ℝ) ≤ c0 := by simpa [c0] using h0Lo
  have hc0Hi : c0 ≤ (201407 / 10 : ℝ) := by simpa [c0] using h0Hi
  have hc1Lo : (-187763 : ℝ) ≤ c1 := by simpa [c1] using h1Lo
  have hc1Hi : c1 ≤ (-938811 / 5 : ℝ) := by simpa [c1] using h1Hi
  have hc2Lo : (-936971 / 1000 : ℝ) ≤ c2 := by simpa [c2] using h2Lo
  have hc2Hi : c2 ≤ (-936 : ℝ) := by simpa [c2] using h2Hi
  have hc0pos : 0 ≤ c0 := by linarith
  have hq0nonneg : 0 ≤ q 0 := by linarith
  have ht0Lo : (20140 : ℝ) * 52 ≤ c0 * q 0 :=
    mul_le_mul hc0Lo hq0.1 (by norm_num) hc0pos
  have ht0Hi : c0 * q 0 ≤ (201407 / 10 : ℝ) * 54 :=
    mul_le_mul hc0Hi hq0.2 hq0nonneg (by norm_num)
  have hnegc1Lo : (938811 / 5 : ℝ) ≤ -c1 := by linarith
  have hnegc1Hi : -c1 ≤ (187763 : ℝ) := by linarith
  have hnegc1pos : 0 ≤ -c1 := by linarith
  have hq1nonneg : 0 ≤ q 1 := by linarith
  have ht1ProdLo : (938811 / 5 : ℝ) * 27 ≤ (-c1) * q 1 :=
    mul_le_mul hnegc1Lo hq1.1 (by norm_num) hnegc1pos
  have ht1ProdHi : (-c1) * q 1 ≤ (187763 : ℝ) * 28 :=
    mul_le_mul hnegc1Hi hq1.2 hq1nonneg (by norm_num)
  have ht1Lo : (-187763 : ℝ) * 28 ≤ c1 * q 1 := by nlinarith
  have ht1Hi : c1 * q 1 ≤ (-938811 / 5 : ℝ) * 27 := by nlinarith
  have hnegc2Lo : (936 : ℝ) ≤ -c2 := by linarith
  have hnegc2Hi : -c2 ≤ (936971 / 1000 : ℝ) := by linarith
  have hnegc2pos : 0 ≤ -c2 := by linarith
  have hnegq2Lo : (3821 : ℝ) ≤ -q 2 := by linarith
  have hnegq2Hi : -q 2 ≤ (3822 : ℝ) := by linarith
  have hnegq2pos : 0 ≤ -q 2 := by linarith
  have ht2Lo : (936 : ℝ) * 3821 ≤ (-c2) * (-q 2) :=
    mul_le_mul hnegc2Lo hnegq2Lo (by norm_num) hnegc2pos
  have ht2Hi : (-c2) * (-q 2) ≤ (936971 / 1000 : ℝ) * 3822 :=
    mul_le_mul hnegc2Hi hnegq2Hi hnegq2pos (by norm_num)
  have hrewrite : frozenCommonCubic q =
      -(cbase + c0 * q 0 + c1 * q 1 + c2 * q 2) := by
    simp only [frozenCommonCubic, cbase, c0, c1, c2]
    field_simp [Real.pi_ne_zero]
    ring
  have hsumLo :
      0 < cbase + c0 * q 0 + c1 * q 1 + c2 * q 2 := by
    nlinarith
  have hsumHi :
      cbase + c0 * q 0 + c1 * q 1 + c2 * q 2 ≤ 736875 := by
    nlinarith
  rw [hrewrite, abs_neg, abs_of_pos hsumLo]
  exact hsumHi

/-- The triple-divided cleared error starts with the compact cubic
coefficient. -/
theorem frozenPathClearedError_divX_three_coeff_zero (q : Fin 3 → ℝ) :
    ((frozenPathClearedError q).divX.divX.divX).coeff 0 =
      frozenCommonCubic q := by
  simpa only [coeff_divX] using frozenPathClearedError_coeff_three q

end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
