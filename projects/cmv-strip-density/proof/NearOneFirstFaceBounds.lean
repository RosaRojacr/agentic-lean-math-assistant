/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneFirstCellGap

/-!
# Explicit first-row bounds for the near-one endpoint cell

This module gives a literal closed scale interval on which the first pair of
endpoint-box faces retains its strict signs. Its deliberately coarse rational
bounds are reusable inputs for the complete quantitative six-face certificate.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open Filter
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section ExplicitFirstRowFaces

set_option maxHeartbeats 0 in
-- The nested rational interval normalization exceeds the default deterministic budget.
private lemma typeFourAngleBar2_abs_bound
    {s z : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hz0 : 0 ≤ z) (hz : z ≤ 5) :
    -1000 ≤ typeFourAngleBar2 s z ∧ typeFourAngleBar2 s z ≤ 1000 := by
  have hs1 : s ≤ 1 := by linarith
  have hs2 : s ^ 2 ≤ s := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hs2one : s ^ 2 ≤ 1 := hs2.trans hs1
  have hsz : s * z ≤ (1 / 126334 : ℝ) * 5 :=
    mul_le_mul hs hz hz0 (by norm_num)
  have ha0 : 0 ≤ aCoord s z := by
    simp only [aCoord]
    positivity
  have ha : aCoord s z ≤ 2 := by
    simp only [aCoord]
    norm_num at hsz ⊢
    linarith
  have hy0 : 0 ≤ yCoord s z := by
    simp only [yCoord]
    positivity
  have hy : yCoord s z ≤ 1 / 1000 := by
    simp only [yCoord]
    calc
      s * aCoord s z ≤ (1 / 126334 : ℝ) * 2 :=
        mul_le_mul hs ha ha0 (by norm_num)
      _ ≤ 1 / 1000 := by norm_num
  have hy2 : yCoord s z ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by
    gcongr
  have hcos : 0 < 1 - yCoord s z ^ 2 := by
    nlinarith [hy2]
  have hcosHalf : (1 / 2 : ℝ) ≤ 1 - yCoord s z ^ 2 := by
    nlinarith [hy2]
  have hdenDensity : (1 / 2 : ℝ) ≤
      (1 + s ^ 2) * (1 - yCoord s z ^ 2) := by
    calc
      (1 / 2 : ℝ) ≤ 1 * (1 - yCoord s z ^ 2) := by
        simpa using hcosHalf
      _ ≤ (1 + s ^ 2) * (1 - yCoord s z ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg s]) hcos.le
  have hdq0 : 0 ≤ densityCubeQuotient s z := by
    rw [densityCubeQuotient]
    positivity
  have hdq : densityCubeQuotient s z ≤ 60 := by
    rw [densityCubeQuotient]
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hdenDensity)]
    have htwo : 2 + s * z ≤ 3 := by norm_num at hsz ⊢; linarith
    have hnum : 2 * z * (2 + s * z) ≤ 30 := by
      calc
        2 * z * (2 + s * z) ≤ 2 * 5 * 3 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num)) htwo
            (by positivity) (by norm_num)
        _ = 30 := by norm_num
    nlinarith
  have hrhoEq : density s z = 1 + s ^ 3 * densityCubeQuotient s z := by
    linarith [density_sub_one_eq_cube_mul s z (ne_of_gt hcos)]
  have hs3 : s ^ 3 ≤ s := by
    calc
      s ^ 3 = s ^ 2 * s := by ring
      _ ≤ s * s := mul_le_mul_of_nonneg_right hs2 hs0
      _ ≤ s * 1 := mul_le_mul_of_nonneg_left hs1 hs0
      _ = s := by ring
  have hsdq : s ^ 3 * densityCubeQuotient s z ≤ 1 := by
    calc
      s ^ 3 * densityCubeQuotient s z ≤ s * 60 :=
        mul_le_mul hs3 hdq hdq0 (by positivity)
      _ ≤ 1 := by norm_num at hs ⊢; nlinarith
  have hrho0 : 0 ≤ density s z := by rw [hrhoEq]; positivity
  have hrho : density s z ≤ 2 := by rw [hrhoEq]; linarith
  have hrs := atanQuotientSqRemainder_centered_bounds hs2one
  have hrslo : -(1 / 3 : ℝ) ≤ atanQuotientSqRemainder s := by linarith [hrs.1]
  have hrshi : atanQuotientSqRemainder s ≤ 0 := by
    have : s ^ 2 / 5 ≤ (1 / 5 : ℝ) := by nlinarith
    linarith [hrs.2]
  have hatan0 : 0 ≤ atanQuotient s := by
    rw [atanQuotient_eq_one_add_sq_mul]
    have hm := mul_le_mul_of_nonneg_left hrslo (sq_nonneg s)
    nlinarith
  have hatan : atanQuotient s ≤ 1 := by
    rw [atanQuotient_eq_one_add_sq_mul]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hrshi)
  let d : ℝ := 1 + s * yCoord s z
  let x : ℝ := s ^ 2 * z / d
  have hd : 1 ≤ d := by
    dsimp [d]
    nlinarith [mul_nonneg hs0 hy0]
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hnumx : s ^ 2 * z ≤ 1 := by
    calc
      s ^ 2 * z ≤ s * 5 := mul_le_mul hs2 hz hz0 (by positivity)
      _ ≤ 1 := by norm_num at hs ⊢; nlinarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 1 := by
    dsimp [x]
    rw [div_le_iff₀ hd0]
    simpa using hnumx.trans hd
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hrx := atanQuotientSqRemainder_centered_bounds hx2
  have hrxlo : -(1 / 3 : ℝ) ≤ atanQuotientSqRemainder x := by linarith [hrx.1]
  have hrxhi : atanQuotientSqRemainder x ≤ 0 := by
    have : x ^ 2 / 5 ≤ (1 / 5 : ℝ) := by nlinarith
    linarith [hrx.2]
  let c : ℝ := s ^ 2 * z ^ 2 / d ^ 2
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hz2 : z ^ 2 ≤ 25 := by nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz)]
  have hd2 : 1 ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 1)]
  have hc : c ≤ 25 := by
    dsimp [c]
    rw [div_le_iff₀ (sq_pos_of_pos hd0)]
    have hleft : s ^ 2 * z ^ 2 ≤ 25 := by
      calc
        s ^ 2 * z ^ 2 ≤ 1 * 25 := mul_le_mul hs2one hz2 (sq_nonneg z) (by norm_num)
        _ = 25 := by norm_num
    calc
      s ^ 2 * z ^ 2 ≤ 25 := hleft
      _ ≤ 25 * d ^ 2 := by nlinarith
  let u : ℝ := c * atanQuotientSqRemainder x - aCoord s z
  have hcu0 : c * atanQuotientSqRemainder x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc0 hrxhi
  have huhi : u ≤ 0 := by dsimp [u]; nlinarith
  have hculo : -(25 / 3 : ℝ) ≤ c * atanQuotientSqRemainder x := by
    calc
      -(25 / 3 : ℝ) = 25 * (-(1 / 3 : ℝ)) := by ring
      _ ≤ c * (-(1 / 3 : ℝ)) := mul_le_mul_of_nonpos_right hc (by norm_num)
      _ ≤ c * atanQuotientSqRemainder x := mul_le_mul_of_nonneg_left hrxlo hc0
  have hulo : -11 ≤ u := by dsimp [u]; nlinarith
  let m : ℝ := 2 * z / d
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hm : m ≤ 10 := by
    dsimp [m]
    rw [div_le_iff₀ hd0]
    nlinarith
  have hmulhi : m * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hm0 huhi
  have hmullo : -110 ≤ m * u := by
    calc
      (-110 : ℝ) = 10 * (-11) := by norm_num
      _ ≤ m * (-11) := mul_le_mul_of_nonpos_right hm (by norm_num)
      _ ≤ m * u := mul_le_mul_of_nonneg_left hulo hm0
  have hincEq : typeFourAngleIncrementBar2 s z = m * u := by
    simp only [typeFourAngleIncrementBar2]
    change 2 * z / d * (s ^ 2 * z ^ 2 / d ^ 2 *
      atanQuotientSqRemainder x - aCoord s z) = m * u
    rfl
  have hinc0 : typeFourAngleIncrementBar2 s z ≤ 0 := by rw [hincEq]; exact hmulhi
  have hinc : -110 ≤ typeFourAngleIncrementBar2 s z := by rw [hincEq]; exact hmullo
  rw [typeFourAngleBar2]
  have hfirst0 : 0 ≤ 2 * densityCubeQuotient s z * atanQuotient s := by positivity
  have hfirst : 2 * densityCubeQuotient s z * atanQuotient s ≤ 120 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdq) (sub_nonneg.mpr hatan)]
  have hmiddle0 : density s z * typeFourAngleIncrementBar2 s z ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hrho0 hinc0
  have hmiddle : -220 ≤ density s z * typeFourAngleIncrementBar2 s z := by
    calc
      (-220 : ℝ) = 2 * (-110) := by norm_num
      _ ≤ density s z * (-110) := mul_le_mul_of_nonpos_right hrho (by norm_num)
      _ ≤ density s z * typeFourAngleIncrementBar2 s z :=
        mul_le_mul_of_nonneg_left hinc hrho0
  have hlast0 : 0 ≤ 2 * s * z * densityCubeQuotient s z := by positivity
  have hlast : 2 * s * z * densityCubeQuotient s z ≤ 600 := by
    have hsz5 : s * z ≤ 5 := hsz.trans (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsz5) (sub_nonneg.mpr hdq)]
  constructor <;> nlinarith

private def firstRowTail (s q : ℝ) : ℝ :=
  3 * π ^ 4 * s ^ 5 + 5 * π ^ 4 * s ^ 3 +
  6 * π ^ 3 * s ^ 4 + 11 * π ^ 3 * s ^ 2 +
  6 * π ^ 2 * q * s ^ 6 + 10 * π ^ 2 * q * s ^ 4 +
  6 * π ^ 2 * s ^ 3 + 12 * π ^ 2 * s +
  6 * π * q * s ^ 5 + 11 * π * q * s ^ 3 + π * q * s +
  3 * π * s ^ 2 + 3 * q ^ 2 * s ^ 7 + 5 * q ^ 2 * s ^ 5 +
  3 * q * s ^ 4 + 6 * q * s ^ 2

private lemma firstRowTail_bounds {s q : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq0 : 0 ≤ q) (hq : q ≤ 54) :
    0 ≤ firstRowTail s q ∧ firstRowTail s q ≤ 50000 * s := by
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
  have hp0 : 0 ≤ π := Real.pi_pos.le
  have hp : π ≤ 4 := Real.pi_lt_four.le
  constructor
  · unfold firstRowTail
    positivity
  · unfold firstRowTail
    calc
      3 * π ^ 4 * s ^ 5 + 5 * π ^ 4 * s ^ 3 +
          6 * π ^ 3 * s ^ 4 + 11 * π ^ 3 * s ^ 2 +
          6 * π ^ 2 * q * s ^ 6 + 10 * π ^ 2 * q * s ^ 4 +
          6 * π ^ 2 * s ^ 3 + 12 * π ^ 2 * s +
          6 * π * q * s ^ 5 + 11 * π * q * s ^ 3 + π * q * s +
          3 * π * s ^ 2 + 3 * q ^ 2 * s ^ 7 + 5 * q ^ 2 * s ^ 5 +
          3 * q * s ^ 4 + 6 * q * s ^ 2
          ≤ 3 * 4 ^ 4 * s + 5 * 4 ^ 4 * s +
          6 * 4 ^ 3 * s + 11 * 4 ^ 3 * s +
          6 * 4 ^ 2 * 54 * s + 10 * 4 ^ 2 * 54 * s +
          6 * 4 ^ 2 * s + 12 * 4 ^ 2 * s +
          6 * 4 * 54 * s + 11 * 4 * 54 * s + 4 * 54 * s +
          3 * 4 * s + 3 * 54 ^ 2 * s + 5 * 54 ^ 2 * s +
          3 * 54 * s + 6 * 54 * s := by
            gcongr <;>
              first | exact hp | exact hq | (apply hspow; norm_num)
      _ ≤ 50000 * s := by ring_nf; nlinarith

private lemma firstRescaledAlgebraicFactor_eq
    (s q B : ℝ)
    (hangle : typeFourAngleBar s (rescaledFirstPhysicalCoordinate s q) =
      2 * rescaledFirstPhysicalCoordinate s q + s ^ 2 * B) :
    firstRescaledAlgebraicFactor s q
        (typeFourAngleBar s (rescaledFirstPhysicalCoordinate s q)) =
      2 * (q - π ^ 3 - 7 * π) - 2 * firstRowTail s q -
        4 * s ^ 2 * (1 + s ^ 2) *
          (1 + s * rescaledFirstPhysicalCoordinate s q) * B := by
  rw [hangle]
  unfold firstRescaledAlgebraicFactor rescaledFirstPhysicalCoordinate firstRowTail
  ring

private lemma first_row_data {s q : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq0 : 0 ≤ q) (hq : q ≤ 54) :
    let z := rescaledFirstPhysicalCoordinate s q
    let B := typeFourAngleBar2 s z
    let C := 4 * s ^ 2 * (1 + s ^ 2) * (1 + s * z) * B
    firstRescaledAlgebraicFactor s q (typeFourAngleBar s z) =
        2 * (q - π ^ 3 - 7 * π) - 2 * firstRowTail s q - C ∧
      -1000 ≤ B ∧ B ≤ 1000 ∧
      0 ≤ firstRowTail s q ∧ firstRowTail s q ≤ 50000 * s ∧
      -16000 * s ^ 2 ≤ C ∧ C ≤ 16000 * s ^ 2 := by
  dsimp only
  let z := rescaledFirstPhysicalCoordinate s q
  let B := typeFourAngleBar2 s z
  have hs1 : s ≤ 1 := by linarith
  have hs2 : s ^ 2 ≤ s := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hp2 : π ^ 2 ≤ 16 := by
    have h : π ^ 2 < (4 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ Real.pi_lt_four Real.pi_pos.le (by norm_num)
    norm_num at h ⊢
    exact h.le
  have hsPi2 : s * π ^ 2 ≤ (1 / 126334 : ℝ) * 16 :=
    mul_le_mul hs hp2 (sq_nonneg π) (by norm_num)
  have hs2q : s ^ 2 * q ≤ (1 / 126334 : ℝ) * 54 :=
    mul_le_mul (hs2.trans hs) hq hq0 (by positivity)
  have hz0 : 0 ≤ z := by
    dsimp [z, rescaledFirstPhysicalCoordinate]
    positivity
  have hz : z ≤ 5 := by
    dsimp [z, rescaledFirstPhysicalCoordinate]
    nlinarith [Real.pi_lt_four]
  have hB := typeFourAngleBar2_abs_bound hs0 hs hz0 hz
  have hsz : s * z ≤ (1 / 126334 : ℝ) * 5 :=
    mul_le_mul hs hz hz0 (by norm_num)
  have ha0 : 0 ≤ aCoord s z := by simp only [aCoord]; positivity
  have ha : aCoord s z ≤ 2 := by
    simp only [aCoord]
    norm_num at hsz ⊢
    linarith
  have hy0 : 0 ≤ yCoord s z := by simp only [yCoord]; positivity
  have hy : yCoord s z ≤ 1 / 1000 := by
    simp only [yCoord]
    calc
      s * aCoord s z ≤ (1 / 126334 : ℝ) * 2 :=
        mul_le_mul hs ha ha0 (by norm_num)
      _ ≤ 1 / 1000 := by norm_num
  have hy2 : yCoord s z ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := by gcongr
  have hyne : 1 - yCoord s z ^ 2 ≠ 0 := by
    have : yCoord s z ^ 2 < 1 := by nlinarith [hy2]
    nlinarith
  have hdne : 1 + s * yCoord s z ≠ 0 := by positivity
  have hangle : typeFourAngleBar s z = 2 * z + s ^ 2 * B := by
    have h := sq_mul_typeFourAngleBar2 s z hyne hdne
    dsimp only [B]
    linarith
  have hfactor := firstRescaledAlgebraicFactor_eq s q B (by
    simpa [z] using hangle)
  have htail := firstRowTail_bounds hs0 hs hq0 hq
  let F : ℝ := (1 + s ^ 2) * (1 + s * z)
  have hF0 : 0 ≤ F := by dsimp [F]; positivity
  have hF : F ≤ 4 := by
    have hleft : 1 + s ^ 2 ≤ 2 := by nlinarith
    have hright : 1 + s * z ≤ 2 := by norm_num at hsz ⊢; linarith
    dsimp [F]
    nlinarith [mul_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hright)]
  let K : ℝ := 4 * s ^ 2 * F
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ 16 * s ^ 2 := by
    dsimp [K]
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hF)]
  have hClo : -16000 * s ^ 2 ≤ K * B := by
    calc
      -16000 * s ^ 2 = (16 * s ^ 2) * (-1000) := by ring
      _ ≤ K * (-1000) := mul_le_mul_of_nonpos_right hK (by norm_num)
      _ ≤ K * B := mul_le_mul_of_nonneg_left hB.1 hK0
  have hChi : K * B ≤ 16000 * s ^ 2 := by
    calc
      K * B ≤ K * 1000 := mul_le_mul_of_nonneg_left hB.2 hK0
      _ ≤ (16 * s ^ 2) * 1000 :=
        mul_le_mul_of_nonneg_right hK (by norm_num)
      _ = 16000 * s ^ 2 := by ring
  refine ⟨?_, hB.1, hB.2, htail.1, htail.2, ?_, ?_⟩
  · simpa [z, B, F, K] using hfactor
  · simpa [z, B, F, K, mul_assoc] using hClo
  · simpa [z, B, F, K, mul_assoc] using hChi

/-- The two explicit first-coordinate faces keep opposite strict signs
throughout the closed scale interval `0 ≤ s ≤ 1 / 126334`. -/
theorem explicit_first_row_face_signs {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) :
    poleFreeFirstRescaledRow s 52 < 0 ∧
      0 < poleFreeFirstRescaledRow s 54 := by
  have hloData := first_row_data hs0 hs (q := (52 : ℝ))
    (by norm_num) (by norm_num)
  have hhiData := first_row_data hs0 hs (q := (54 : ℝ))
    (by norm_num) (by norm_num)
  have hs2small : 16000 * s ^ 2 ≤ 1 / 10 := by
    have hs2 : s ^ 2 ≤ s := by
      have hs1 : s ≤ 1 := by linarith
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
    nlinarith
  have hp3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
  have hp3hi : π ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ Real.pi_lt_d20 Real.pi_pos.le (by norm_num)
  have hbaseLo : 2 * ((52 : ℝ) - π ^ 3 - 7 * π) < -1 := by
    have hpilo := Real.pi_gt_d20
    norm_num at hp3lo hpilo ⊢
    nlinarith
  have hbaseHi : 1 < 2 * ((54 : ℝ) - π ^ 3 - 7 * π) := by
    have hpihi := Real.pi_lt_d20
    norm_num at hp3hi hpihi ⊢
    nlinarith
  constructor
  · unfold poleFreeFirstRescaledRow
    rw [hloData.1]
    apply div_neg_of_neg_of_pos
    · nlinarith [hloData.2.2.2.1, hloData.2.2.2.2.2.1]
    · positivity
  · unfold poleFreeFirstRescaledRow
    rw [hhiData.1]
    apply div_pos
    · have htailSmall : 2 * firstRowTail s 54 ≤ 4 / 5 := by
        have := hhiData.2.2.2.2.1
        nlinarith
      nlinarith [hhiData.2.2.2.1, hhiData.2.2.2.2.2.2]
    · positivity

end ExplicitFirstRowFaces


/-- The complete first pair of endpoint-box faces has strict signs throughout
the explicit closed scale interval `0 ≤ s ≤ 1 / 126334`. -/
theorem explicit_first_face_cell {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) :
    ∀ q, InEndpointBox q →
      (q 0 = endpointBoxLower 0 →
        rescaledOrientedNearOneMap s q 0 < 0) ∧
      (q 0 = endpointBoxUpper 0 →
        0 < rescaledOrientedNearOneMap s q 0) := by
  have hfaces := explicit_first_row_face_signs hs0 hs
  intro q _hq
  constructor
  · intro hface
    rw [rescaledOrientedNearOneMap_first_eq_poleFree, hface]
    simpa [endpointBoxLower] using hfaces.1
  · intro hface
    rw [rescaledOrientedNearOneMap_first_eq_poleFree, hface]
    simpa [endpointBoxUpper] using hfaces.2

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
