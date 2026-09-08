/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneSecondFaceBounds

/-!
# Explicit geometric bounds for the third near-one endpoint face

This file records the quantitative path and arctangent-remainder estimates used
by an explicit third-row endpoint-face proof near `s = 0`.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open Filter
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section ExplicitThirdRowFaces

/-- The three physical coordinates on the quadratically rescaled endpoint path. -/
def thirdPhysicalZ (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j) 0

def thirdPhysicalA (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j) 1

def thirdPhysicalB (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j) 2

theorem thirdPhysicalZ_eq (s : ℝ) (q : Fin 3 → ℝ) :
    thirdPhysicalZ s q = π + s * π ^ 2 + s ^ 2 * q 0 := by
  simp [thirdPhysicalZ, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
    exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem thirdPhysicalA_eq (s : ℝ) (q : Fin 3 → ℝ) :
    thirdPhysicalA s q = 5 * π / 12 +
      s * ((43 * π ^ 2 + 1056) / 144) +
      s ^ 2 * (5 * q 0 / 12 + q 1) := by
  simp [thirdPhysicalA, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
    exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem thirdPhysicalB_eq (s : ℝ) (q : Fin 3 → ℝ) :
    thirdPhysicalB s q = -44 + 19 * π ^ 2 / 24 +
      s * (π * (295 * π ^ 2 - 14256) / 216) +
      s ^ 2 * ((109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2) := by
  simp [thirdPhysicalB, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
    exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

set_option maxHeartbeats 0 in
/-- Uniform rational bounds for the physical and half-angle coordinates on the
relaxed scale interval.  The half-angle bounds retain their linear dependence
on `s`, so narrower-cell callers recover their sharper constants directly. -/
theorem explicit_third_path_geometry {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) (hq : InEndpointBox q) :
    3 ≤ thirdPhysicalZ s q ∧ thirdPhysicalZ s q ≤ 4 ∧
    1 ≤ thirdPhysicalA s q ∧ thirdPhysicalA s q ≤ 2 ∧
    |thirdPhysicalB s q| ≤ 45 ∧
    2 ≤ rCoord s (thirdPhysicalA s q) ∧
      rCoord s (thirdPhysicalA s q) ≤ 3 ∧
    |eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q)| ≤ 8 ∧
    0 ≤ yCoord s (thirdPhysicalZ s q) ∧
      yCoord s (thirdPhysicalZ s q) ≤ 2 * s ∧
    0 ≤ wCoord s (thirdPhysicalA s q) ∧
      wCoord s (thirdPhysicalA s q) ≤ 3 * s ∧
    0 ≤ vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q) ∧
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) ≤ 4 * s ∧
    1 ≤ 1 + s * yCoord s (thirdPhysicalZ s q) ∧
    1 ≤ 1 + wCoord s (thirdPhysicalA s q) *
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) := by
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
  have hpi3142 : π ≤ 3142 / 1000 := by
    have := Real.pi_lt_d20
    norm_num at this ⊢
    linarith
  have hs1 : s ≤ 1 := by linarith
  have hs2 : s ^ 2 ≤ 1 / 15960279556 := by nlinarith
  have hzlo : 3 ≤ thirdPhysicalZ s q := by
    rw [thirdPhysicalZ_eq]
    nlinarith [mul_nonneg hs0 hpi2lo,
      mul_nonneg (sq_nonneg s) (by linarith : 0 ≤ q 0)]
  have hzhi : thirdPhysicalZ s q ≤ 4 := by
    rw [thirdPhysicalZ_eq]
    have hsp2 : s * π ^ 2 ≤ (1 / 126334 : ℝ) * 16 :=
      mul_le_mul hs hpi2hi hpi2lo (by norm_num)
    have hs2q : s ^ 2 * q 0 ≤ (1 / 15960279556 : ℝ) * 54 :=
      mul_le_mul hs2 hq0.2 (by linarith) (by norm_num)
    norm_num at hsp2 hs2q ⊢
    linarith
  have halo : 1 ≤ thirdPhysicalA s q := by
    rw [thirdPhysicalA_eq]
    have hcoef : 0 ≤ 5 * q 0 / 12 + q 1 := by linarith
    have hbase : 1 ≤ 5 * π / 12 := by nlinarith
    nlinarith [mul_nonneg hs0 (by positivity :
      0 ≤ (43 * π ^ 2 + 1056) / 144),
      mul_nonneg (sq_nonneg s) hcoef]
  have hahi : thirdPhysicalA s q ≤ 2 := by
    rw [thirdPhysicalA_eq]
    have hlin : (43 * π ^ 2 + 1056) / 144 ≤ 13 := by
      nlinarith
    have hquad : 5 * q 0 / 12 + q 1 ≤ 51 := by
      linarith
    have hsLin : s * ((43 * π ^ 2 + 1056) / 144) ≤
        (1 / 126334 : ℝ) * 13 :=
      mul_le_mul hs hlin (by positivity) (by norm_num)
    have hsQuad : s ^ 2 * (5 * q 0 / 12 + q 1) ≤
        (1 / 15960279556 : ℝ) * 51 :=
      mul_le_mul hs2 hquad (by linarith) (by norm_num)
    norm_num at hsLin hsQuad ⊢
    nlinarith
  have hbbaseLo : -44 ≤ -44 + 19 * π ^ 2 / 24 := by nlinarith
  have hbbaseHi : -44 + 19 * π ^ 2 / 24 ≤ -31 := by
    norm_num
    nlinarith
  have hblinLo : -270 ≤ π * (295 * π ^ 2 - 14256) / 216 := by
    have hinnerLo : -14256 ≤ 295 * π ^ 2 - 14256 := by nlinarith
    have hinnerHi : 295 * π ^ 2 - 14256 ≤ 0 := by nlinarith
    have hprodLo : -57024 ≤ π * (295 * π ^ 2 - 14256) := by
      calc
        (-57024 : ℝ) = 4 * (-14256) := by norm_num
        _ ≤ π * (-14256) := mul_le_mul_of_nonpos_right hpi4 (by norm_num)
        _ ≤ π * (295 * π ^ 2 - 14256) :=
          mul_le_mul_of_nonneg_left hinnerLo hpi0
    linarith
  have hblinHi : π * (295 * π ^ 2 - 14256) / 216 ≤ 0 := by
    have : 295 * π ^ 2 - 14256 ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hpi0 this) (by norm_num)
  have hcoef0lo : -5376 ≤ 109 * π ^ 2 - 5376 := by nlinarith
  have hcoef0hi : 109 * π ^ 2 - 5376 ≤ 0 := by nlinarith
  have hcoef1lo : 0 ≤ 2880 - 7 * π ^ 2 := by nlinarith
  have hcoef1hi : 2880 - 7 * π ^ 2 ≤ 2880 := by nlinarith
  have hden72 : 0 < 72 * π := by positivity
  have hden6 : 0 < 6 * π := by positivity
  have ht0lo : -1300 ≤ (109 * π ^ 2 - 5376) / (72 * π) * q 0 := by
    have hfrac : -24 ≤ (109 * π ^ 2 - 5376) / (72 * π) := by
      rw [le_div_iff₀ hden72]
      nlinarith
    have hq0nonneg : 0 ≤ q 0 := by linarith
    calc
      (-1300 : ℝ) ≤ -24 * q 0 := by nlinarith
      _ ≤ (109 * π ^ 2 - 5376) / (72 * π) * q 0 :=
        mul_le_mul_of_nonneg_right hfrac hq0nonneg
  have ht0hi : (109 * π ^ 2 - 5376) / (72 * π) * q 0 ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg hcoef0hi hden72.le) (by linarith)
  have ht1lo : 0 ≤ (2880 - 7 * π ^ 2) / (6 * π) * q 1 :=
    mul_nonneg (div_nonneg hcoef1lo hden6.le) (by linarith)
  have ht1hi : (2880 - 7 * π ^ 2) / (6 * π) * q 1 ≤ 4480 := by
    have hfrac : (2880 - 7 * π ^ 2) / (6 * π) ≤ 160 := by
      rw [div_le_iff₀ hden6]
      nlinarith
    exact (mul_le_mul hfrac hq1.2 (by linarith) (by linarith)).trans_eq (by norm_num)
  have hbquadLo : -5200 ≤
      (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 := by linarith
  have hbquadHi :
      (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 ≤ 700 := by linarith
  have hsblinLo : -(270 / 126334 : ℝ) ≤
      s * (π * (295 * π ^ 2 - 14256) / 216) := by
    have := mul_le_mul_of_nonneg_left hblinLo hs0
    nlinarith
  have hsblinHi : s * (π * (295 * π ^ 2 - 14256) / 216) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hs0 hblinHi
  have hsbquadLo : -(5200 / 15960279556 : ℝ) ≤ s ^ 2 *
      ((109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2) := by
    have := mul_le_mul_of_nonneg_left hbquadLo (sq_nonneg s)
    have hs2nonneg : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have hsbquadHi : s ^ 2 *
      ((109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2) ≤
      700 / 15960279556 := by
    have hcoeff_nonneg_or_nonpos :
        0 ≤ (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
          (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 ∨
        (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
          (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 ≤ 0 := le_total 0 _
    rcases hcoeff_nonneg_or_nonpos with hc | hc
    · calc
        s ^ 2 * ((109 * π ^ 2 - 5376) / (72 * π) * q 0 +
            (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2) ≤
            (1 / 15960279556 : ℝ) * 700 :=
          mul_le_mul hs2 hbquadHi hc (by norm_num)
        _ = 700 / 15960279556 := by ring
    · exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) hc).trans (by norm_num)
  have hbabs : |thirdPhysicalB s q| ≤ 45 := by
    rw [thirdPhysicalB_eq, abs_le]
    constructor <;> norm_num at * <;> linarith
  have hrlo : 2 ≤ rCoord s (thirdPhysicalA s q) := by
    simp only [rCoord]
    nlinarith [mul_nonneg hs0 (by linarith : 0 ≤ thirdPhysicalA s q)]
  have hrhi : rCoord s (thirdPhysicalA s q) ≤ 3 := by
    simp only [rCoord]
    have hsa : s * thirdPhysicalA s q ≤ (1 / 126334 : ℝ) * 2 :=
      mul_le_mul hs hahi (by linarith) (by norm_num)
    norm_num at hsa ⊢
    linarith
  have heabs : |eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q)| ≤ 8 := by
    rcases abs_le.mp hbabs with ⟨hblo, hbhi⟩
    rw [eCoord, abs_le]
    have hsblo : -(45 / 126334 : ℝ) ≤ s * thirdPhysicalB s q := by
      have := mul_le_mul_of_nonneg_left hblo hs0
      nlinarith
    have hsbhi : s * thirdPhysicalB s q ≤ 45 / 126334 := by
      calc
        s * thirdPhysicalB s q ≤ s * 45 :=
          mul_le_mul_of_nonneg_left hbhi hs0
        _ ≤ (1 / 126334 : ℝ) * 45 := mul_le_mul_of_nonneg_right hs (by norm_num)
        _ = 45 / 126334 := by ring
    constructor <;> norm_num at * <;> nlinarith
  have hy0 : 0 ≤ yCoord s (thirdPhysicalZ s q) := by
    simp only [yCoord, aCoord]
    positivity
  have hyhi : yCoord s (thirdPhysicalZ s q) ≤ 2 * s := by
    simp only [yCoord, aCoord]
    have hAhi : 1 + s * thirdPhysicalZ s q ≤ 2 := by
      have hsz : s * thirdPhysicalZ s q ≤ (1 / 126334 : ℝ) * 4 :=
        mul_le_mul hs hzhi (by linarith) (by norm_num)
      norm_num at hsz ⊢
      linarith
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hAhi hs0
  have hw0 : 0 ≤ wCoord s (thirdPhysicalA s q) := by
    simp only [wCoord]
    positivity
  have hwhi : wCoord s (thirdPhysicalA s q) ≤ 3 * s := by
    simp only [wCoord]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hrhi hs0
  have hervlo : 1 ≤ rCoord s (thirdPhysicalA s q) + s *
      eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) := by
    rcases abs_le.mp heabs with ⟨helo, _⟩
    have hse := mul_le_mul_of_nonneg_left helo hs0
    have hs8 : s * 8 ≤ 8 / 126334 := by
      calc
        s * 8 ≤ (1 / 126334 : ℝ) * 8 :=
          mul_le_mul_of_nonneg_right hs (by norm_num)
        _ = 8 / 126334 := by ring
    norm_num at hse hs8 ⊢
    nlinarith
  have hervhi : rCoord s (thirdPhysicalA s q) + s *
      eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) ≤ 4 := by
    rcases abs_le.mp heabs with ⟨_, hehi⟩
    have hse := mul_le_mul_of_nonneg_left hehi hs0
    have hs8 : s * 8 ≤ 8 / 126334 := by
      calc
        s * 8 ≤ (1 / 126334 : ℝ) * 8 :=
          mul_le_mul_of_nonneg_right hs (by norm_num)
        _ = 8 / 126334 := by ring
    norm_num at hse hs8 ⊢
    nlinarith
  have hv0 : 0 ≤ vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q) := by
    simp only [vCoord]
    positivity
  have hvhi : vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q) ≤ 4 * s := by
    simp only [vCoord]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hervhi hs0
  repeat' apply And.intro
  · exact hzlo
  · exact hzhi
  · exact halo
  · exact hahi
  · exact hbabs
  · exact hrlo
  · exact hrhi
  · exact heabs
  · exact hy0
  · exact hyhi
  · exact hw0
  · exact hwhi
  · exact hv0
  · exact hvhi
  · nlinarith [mul_nonneg hs0 hy0]
  · nlinarith [mul_nonneg hw0 hv0]

/-- The small argument in the type-(iv) angle-addition quotient. -/
def thirdFourAtanArgument (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  s ^ 2 * thirdPhysicalZ s q /
    (1 + s * yCoord s (thirdPhysicalZ s q))

/-- The small argument in the type-(iii) angle-addition quotient. -/
def thirdThreeAtanArgument (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  s ^ 2 * eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q) /
    (1 + wCoord s (thirdPhysicalA s q) *
      vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q))

set_option maxHeartbeats 0 in
/-- All four arctangent remainders occurring in the regularized third row share
the cap `1/8000000000`.  The centered remainder's `x²/5` factor keeps this
cap valid on the widened scale interval after the exact path cancellations. -/
theorem explicit_third_atan_remainder_bounds {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334) (hq : InEndpointBox q) :
    (0 ≤ atanQuotientSqRemainder s + 1 / 3 ∧
      atanQuotientSqRemainder s + 1 / 3 ≤ 1 / 8000000000) ∧
    (0 ≤ atanQuotientSqRemainder
        (wCoord s (thirdPhysicalA s q)) + 1 / 3 ∧
      atanQuotientSqRemainder
        (wCoord s (thirdPhysicalA s q)) + 1 / 3 ≤
          1 / 8000000000) ∧
    (0 ≤ atanQuotientSqRemainder (thirdFourAtanArgument s q) + 1 / 3 ∧
      atanQuotientSqRemainder (thirdFourAtanArgument s q) + 1 / 3 ≤
        1 / 8000000000) ∧
    (0 ≤ atanQuotientSqRemainder (thirdThreeAtanArgument s q) + 1 / 3 ∧
      atanQuotientSqRemainder (thirdThreeAtanArgument s q) + 1 / 3 ≤
        1 / 8000000000) := by
  rcases explicit_third_path_geometry q hs0 hs hq with
    ⟨hz0, hz, _ha0, _ha, _hb, _hr0, _hr, he, hy0, _hy, hw0, hwByS,
      _hv0, _hv, hden4, hden3⟩
  have hs2 : s ^ 2 ≤ 1 / 15960279556 := by nlinarith
  have hsabs : |s| ≤ 3 / 126334 := by
    rw [abs_of_nonneg hs0]
    linarith
  have hwabs : |wCoord s (thirdPhysicalA s q)| ≤ 3 / 126334 := by
    rw [abs_of_nonneg hw0]
    nlinarith
  have hx4abs : |thirdFourAtanArgument s q| ≤ 3 / 126334 := by
    have hdpos : 0 < 1 + s * yCoord s (thirdPhysicalZ s q) := by linarith
    have hnum0 : 0 ≤ s ^ 2 * thirdPhysicalZ s q :=
      mul_nonneg (sq_nonneg s) (by linarith)
    rw [thirdFourAtanArgument, abs_of_nonneg (div_nonneg hnum0 hdpos.le)]
    rw [div_le_iff₀ hdpos]
    have hnum : s ^ 2 * thirdPhysicalZ s q ≤
        (1 / 15960279556 : ℝ) * 4 :=
      mul_le_mul hs2 hz (by linarith) (by norm_num)
    have hrhs : (1 / 15960279556 : ℝ) * 4 ≤
        3 / 126334 * (1 + s * yCoord s (thirdPhysicalZ s q)) := by
      nlinarith
    exact hnum.trans hrhs
  have hx3abs : |thirdThreeAtanArgument s q| ≤ 3 / 126334 := by
    have hdpos : 0 < 1 + wCoord s (thirdPhysicalA s q) *
        vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) := by linarith
    rw [thirdThreeAtanArgument, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
    rw [abs_mul, abs_of_nonneg (sq_nonneg s)]
    have hnum : s ^ 2 *
        |eCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q)| ≤
        (1 / 15960279556 : ℝ) * 8 :=
      mul_le_mul hs2 he (abs_nonneg _) (by norm_num)
    have hrhs : (1 / 15960279556 : ℝ) * 8 ≤
        3 / 126334 *
          (1 + wCoord s (thirdPhysicalA s q) *
            vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
              (thirdPhysicalB s q)) := by
      nlinarith
    exact hnum.trans hrhs
  have remainder_bound (x : ℝ) (hx : |x| ≤ 3 / 126334) :
      0 ≤ atanQuotientSqRemainder x + 1 / 3 ∧
        atanQuotientSqRemainder x + 1 / 3 ≤ 1 / 8000000000 := by
    have hx2small : x ^ 2 ≤ (3 / 126334 : ℝ) ^ 2 := by
      have hp := pow_le_pow_left₀ (abs_nonneg x) hx 2
      simpa [sq_abs] using hp
    have hx2one : x ^ 2 ≤ 1 := by nlinarith
    have hr := atanQuotientSqRemainder_centered_bounds hx2one
    constructor
    · exact hr.1
    · nlinarith [hr.2]
  exact ⟨remainder_bound s hsabs,
    remainder_bound (wCoord s (thirdPhysicalA s q)) hwabs,
    remainder_bound (thirdFourAtanArgument s q) hx4abs,
    remainder_bound (thirdThreeAtanArgument s q) hx3abs⟩

/-- The type-(iv) divided increment with all arctangent square remainders
frozen at their common endpoint value `-1/3`. -/
def thirdFourIncrementFrozen (s z : ℝ) : ℝ :=
  let d := 1 + s * yCoord s z
  2 * z / d *
    (s ^ 2 * z ^ 2 / d ^ 2 * (-(1 / 3 : ℝ)) - aCoord s z)

/-- The analogous frozen type-(iii) divided increment. -/
def thirdThreeIncrementFrozen (s z a b : ℝ) : ℝ :=
  let e := eCoord s z a b
  let r := rCoord s a
  let d := 1 + wCoord s a * vCoord s z a b
  2 * e / d *
    (s ^ 2 * e ^ 2 / d ^ 2 * (-(1 / 3 : ℝ)) - r * (r + s * e))

def thirdFourBarFrozen (s z : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * (1 - s ^ 2 / 3) +
    density s z * thirdFourIncrementFrozen s z +
    2 * s * z * densityCubeQuotient s z

def thirdThreeBarFrozen (s z a b : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * rCoord s a *
      (1 - wCoord s a ^ 2 / 3) +
    density s z * thirdThreeIncrementFrozen s z a b +
    2 * s * eCoord s z a b * densityCubeQuotient s z

/-- The fully rational row obtained by freezing the four arctangent square
remainders at `-1/3`.  Its difference from the analytic row is displayed
exactly in `regularizedThirdRow_sub_frozen`. -/
def thirdRegularizedFrozen (s z a b : ℝ) : ℝ :=
  H3hatPolynomial s z a b π +
    areaDenominator s z a b *
      (2 * halfCos s ^ 2 * thirdThreeBarFrozen s z a b -
        (1 + halfCos (wCoord s a)) ^ 2 * thirdFourBarFrozen s z +
        4 * z * areaPiWeight s a) +
    (4 - 2 * z * s / 3) *
      (-foldDenominator s z * typeFourSineProductBar s z *
        (2 * z + s ^ 2 * thirdFourBarFrozen s z))

private def thirdFourRemainderError (s z : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * s ^ 2 *
      (atanQuotientSqRemainder s + 1 / 3) +
    density s z *
      (2 * z / (1 + s * yCoord s z) *
        (s ^ 2 * z ^ 2 / (1 + s * yCoord s z) ^ 2 *
          (atanQuotientSqRemainder
            (s ^ 2 * z / (1 + s * yCoord s z)) + 1 / 3)))

private def thirdThreeRemainderError (s z a b : ℝ) : ℝ :=
  2 * densityCubeQuotient s z * rCoord s a * wCoord s a ^ 2 *
      (atanQuotientSqRemainder (wCoord s a) + 1 / 3) +
    density s z *
      (2 * eCoord s z a b /
          (1 + wCoord s a * vCoord s z a b) *
        (s ^ 2 * eCoord s z a b ^ 2 /
            (1 + wCoord s a * vCoord s z a b) ^ 2 *
          (atanQuotientSqRemainder
            (s ^ 2 * eCoord s z a b /
              (1 + wCoord s a * vCoord s z a b)) + 1 / 3)))

set_option maxHeartbeats 0 in
private theorem typeFourAngleBar2_sub_frozen (s z : ℝ) :
    typeFourAngleBar2 s z - thirdFourBarFrozen s z =
      thirdFourRemainderError s z := by
  unfold typeFourAngleBar2 thirdFourBarFrozen thirdFourRemainderError
    typeFourAngleIncrementBar2 thirdFourIncrementFrozen
  simp only [atanQuotient_eq_one_add_sq_mul]
  ring_nf

set_option maxHeartbeats 0 in
private theorem typeThreeAngleBar2_sub_frozen (s z a b : ℝ) :
    typeThreeAngleBar2 s z a b - thirdThreeBarFrozen s z a b =
      thirdThreeRemainderError s z a b := by
  unfold typeThreeAngleBar2 thirdThreeBarFrozen thirdThreeRemainderError
    typeThreeAngleIncrementBar2 thirdThreeIncrementFrozen
  simp only [atanQuotient_eq_one_add_sq_mul]
  ring_nf

set_option maxHeartbeats 0 in
/-- Exact four-remainder expansion.  Thus the only nonlinear error terms left
after freezing are the four nonnegative quantities bounded in
`explicit_third_atan_remainder_bounds`. -/
theorem regularizedThirdRow_sub_frozen {s z a b : ℝ}
    (hy : 1 - yCoord s z ^ 2 ≠ 0)
    (hd : 1 + s * yCoord s z ≠ 0) :
    regularizedThirdRow s z a b π - thirdRegularizedFrozen s z a b =
      areaDenominator s z a b *
        (2 * halfCos s ^ 2 * thirdThreeRemainderError s z a b -
          (1 + halfCos (wCoord s a)) ^ 2 *
            thirdFourRemainderError s z) +
      (4 - 2 * z * s / 3) *
        (-foldDenominator s z * typeFourSineProductBar s z * s ^ 2 *
          thirdFourRemainderError s z) := by
  have hfour := sq_mul_typeFourAngleBar2 s z hy hd
  rw [regularizedThirdRow, thirdRegularizedFrozen, areaAngleCorrectionBar,
    foldAngleCorrectionBar]
  rw [show typeFourAngleBar s z =
      2 * z + s ^ 2 * typeFourAngleBar2 s z by linarith]
  rw [← typeFourAngleBar2_sub_frozen s z,
    ← typeThreeAngleBar2_sub_frozen s z a b]
  ring

private lemma halfCos_abs_le_one (x : ℝ) : |halfCos x| ≤ 1 := by
  rw [halfCos, abs_div]
  have hd : 0 < 1 + x ^ 2 := by positivity
  rw [abs_of_pos hd, div_le_iff₀ hd]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x]

set_option maxHeartbeats 0 in
-- The nested exact rational products exceed the default deterministic budget.
/-- On the explicit scale interval, replacing all four arctangent square
remainders by their common endpoint value `-1/3` costs at most one tenth of
one percent of the `s²` third-row face margin. -/
theorem explicit_regularizedThirdRow_sub_frozen_abs_bound {s : ℝ}
    (q : Fin 3 → ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq : InEndpointBox q) :
    |regularizedThirdRow s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) π -
      thirdRegularizedFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q)| ≤ s ^ 2 / 1000 := by
  let z := thirdPhysicalZ s q
  let a := thirdPhysicalA s q
  let b := thirdPhysicalB s q
  let r := rCoord s a
  let e := eCoord s z a b
  let y := yCoord s z
  let w := wCoord s a
  let v := vCoord s z a b
  let d₄ := 1 + s * y
  let d₃ := 1 + w * v
  let x₄ := s ^ 2 * z / d₄
  let x₃ := s ^ 2 * e / d₃
  let Q := densityCubeQuotient s z
  let ρ := density s z
  have hgeomRelaxed := explicit_third_path_geometry q hs0 hs hq
  rcases hgeomRelaxed with
    ⟨hz0, hz, ha0, ha, hb, hr0, hr, he, hy0, hyByS, hw0, hwByS,
      hv0, hvByS, hd₄, hd₃⟩
  have hy : y ≤ 2 / 126334 := by
    change yCoord s (thirdPhysicalZ s q) ≤ 2 / 126334
    nlinarith
  have hw : w ≤ 3 / 126334 := by
    change wCoord s (thirdPhysicalA s q) ≤ 3 / 126334
    nlinarith
  have hv : v ≤ 4 / 126334 := by
    change vCoord s (thirdPhysicalZ s q) (thirdPhysicalA s q)
      (thirdPhysicalB s q) ≤ 4 / 126334
    nlinarith
  have hremainders :
      (0 ≤ atanQuotientSqRemainder s + 1 / 3 ∧
        atanQuotientSqRemainder s + 1 / 3 ≤ 1 / 8000000000) ∧
      (0 ≤ atanQuotientSqRemainder w + 1 / 3 ∧
        atanQuotientSqRemainder w + 1 / 3 ≤ 1 / 8000000000) ∧
      (0 ≤ atanQuotientSqRemainder x₄ + 1 / 3 ∧
        atanQuotientSqRemainder x₄ + 1 / 3 ≤ 1 / 8000000000) ∧
      (0 ≤ atanQuotientSqRemainder x₃ + 1 / 3 ∧
        atanQuotientSqRemainder x₃ + 1 / 3 ≤ 1 / 8000000000) := by
    simpa [w, x₄, x₃, d₄, d₃, y, v, e, z, a, b,
      thirdFourAtanArgument, thirdThreeAtanArgument] using
      explicit_third_atan_remainder_bounds q hs0 hs hq
  rcases hremainders with ⟨hδs, hδw, hδ₄, hδ₃⟩
  let δs := atanQuotientSqRemainder s + 1 / 3
  let δw := atanQuotientSqRemainder w + 1 / 3
  let δ₄ := atanQuotientSqRemainder x₄ + 1 / 3
  let δ₃ := atanQuotientSqRemainder x₃ + 1 / 3
  change 0 ≤ δs ∧ δs ≤ 1 / 8000000000 at hδs
  change 0 ≤ δw ∧ δw ≤ 1 / 8000000000 at hδw
  change 0 ≤ δ₄ ∧ δ₄ ≤ 1 / 8000000000 at hδ₄
  change 0 ≤ δ₃ ∧ δ₃ ≤ 1 / 8000000000 at hδ₃
  have hmul {u t U T : ℝ} (hu : |u| ≤ U) (ht : |t| ≤ T)
      (hU : 0 ≤ U) : |u * t| ≤ U * T := by
    rw [abs_mul]
    exact mul_le_mul hu ht (abs_nonneg t) hU
  have hdiv {u d U : ℝ} (hu : |u| ≤ U) (hd : 1 ≤ d)
      (hU : 0 ≤ U) : |u / d| ≤ U := by
    have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    exact hu.trans (by nlinarith)
  have hpow {u U : ℝ} (hu : |u| ≤ U) (hU : 0 ≤ U) :
      |u ^ 2| ≤ U ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg u) hu 2
  have hs1 : s ≤ 1 := hs.trans (by norm_num)
  have hs2one : s ^ 2 ≤ 1 := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hs2R : s ^ 2 ≤ (1 / 126334 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have hy2 : y ^ 2 ≤ 1 / 2 := by nlinarith [sq_nonneg y]
  have hdenQ : (1 / 2 : ℝ) ≤ (1 + s ^ 2) * (1 - y ^ 2) := by
    calc
      (1 / 2 : ℝ) ≤ 1 * (1 - y ^ 2) := by nlinarith
      _ ≤ (1 + s ^ 2) * (1 - y ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg s]) (by nlinarith)
  have hdenQ0 : 0 < (1 + s ^ 2) * (1 - y ^ 2) :=
    lt_of_lt_of_le (by norm_num) hdenQ
  have hsz : s * z ≤ 1 := by
    calc
      s * z ≤ (1 / 126334 : ℝ) * 4 :=
        mul_le_mul hs hz (by linarith) (by norm_num)
      _ ≤ 1 := by norm_num
  have hQ0 : 0 ≤ Q := by
    change 0 ≤ 2 * z * (2 + s * z) / ((1 + s ^ 2) * (1 - y ^ 2))
    positivity
  have hQ : Q ≤ 48 := by
    change 2 * z * (2 + s * z) / ((1 + s ^ 2) * (1 - y ^ 2)) ≤ 48
    rw [div_le_iff₀ hdenQ0]
    have hnum : 2 * z * (2 + s * z) ≤ 24 := by
      calc
        2 * z * (2 + s * z) ≤ 2 * 4 * 3 := by
          gcongr
          all_goals nlinarith
        _ = 24 := by norm_num
    nlinarith
  have hQabs : |Q| ≤ 48 := by rw [abs_of_nonneg hQ0]; exact hQ
  have hyne : 1 - y ^ 2 ≠ 0 := ne_of_gt (by nlinarith)
  have hρeq : ρ = 1 + s ^ 3 * Q := by
    dsimp only [ρ, Q]
    have h := density_sub_one_eq_cube_mul s z (by simpa [y] using hyne)
    linarith
  have hρ0 : 0 ≤ ρ := by rw [hρeq]; positivity
  have hρ : ρ ≤ 2 := by
    rw [hρeq]
    have hs3 : s ^ 3 ≤ s := by
      calc
        s ^ 3 = s ^ 2 * s := by ring
        _ ≤ 1 * s := mul_le_mul_of_nonneg_right hs2one hs0
        _ = s := by ring
    have : s ^ 3 * Q ≤ s * 48 :=
      mul_le_mul hs3 hQ hQ0 (by positivity)
    norm_num at hs ⊢
    nlinarith
  have hρabs : |ρ| ≤ 2 := by rw [abs_of_nonneg hρ0]; exact hρ
  have hzabs : |z| ≤ 4 := by rw [abs_of_nonneg (by linarith)]; exact hz
  have hrabs : |r| ≤ 3 := by rw [abs_of_nonneg (by linarith)]; exact hr
  have hsabs : |s| ≤ s := by rw [abs_of_nonneg hs0]
  have hs2abs : |s ^ 2| ≤ s ^ 2 := by rw [abs_of_nonneg (sq_nonneg s)]
  have hδsabs : |δs| ≤ 1 / 8000000000 := by
    rw [abs_of_nonneg hδs.1]
    exact hδs.2
  have hδwabs : |δw| ≤ 1 / 8000000000 := by
    rw [abs_of_nonneg hδw.1]
    exact hδw.2
  have hδ₄abs : |δ₄| ≤ 1 / 8000000000 := by
    rw [abs_of_nonneg hδ₄.1]
    exact hδ₄.2
  have hδ₃abs : |δ₃| ≤ 1 / 8000000000 := by
    rw [abs_of_nonneg hδ₃.1]
    exact hδ₃.2
  have hd₄sq : 1 ≤ d₄ ^ 2 := by nlinarith [sq_nonneg (d₄ - 1)]
  have hd₃sq : 1 ≤ d₃ ^ 2 := by nlinarith [sq_nonneg (d₃ - 1)]
  have hzsq := hpow hzabs (by norm_num)
  have hesq := hpow he (by norm_num)
  have hs2z2 : |s ^ 2 * z ^ 2| ≤ 16 * s ^ 2 := by
    have h := hmul hs2abs hzsq (sq_nonneg s)
    nlinarith
  have hs2e2 : |s ^ 2 * e ^ 2| ≤ 64 * s ^ 2 := by
    have h := hmul hs2abs hesq (sq_nonneg s)
    nlinarith
  have htwoz : |2 * z / d₄| ≤ 8 := by
    apply hdiv (hd := hd₄) (hU := by norm_num)
    rw [abs_mul]
    norm_num
    linarith
  have htwoe : |2 * e / d₃| ≤ 16 := by
    apply hdiv (hd := hd₃) (hU := by norm_num)
    rw [abs_mul]
    norm_num
    linarith
  have hsmallz : |s ^ 2 * z ^ 2 / d₄ ^ 2| ≤ 16 * s ^ 2 :=
    hdiv hs2z2 hd₄sq (by positivity)
  have hsmalle : |s ^ 2 * e ^ 2 / d₃ ^ 2| ≤ 64 * s ^ 2 :=
    hdiv hs2e2 hd₃sq (by positivity)
  have hwByS : |w| ≤ 3 * s := by
    have hwr : w = s * r := by simp [w, r, wCoord]
    rw [hwr, abs_mul, abs_of_nonneg hs0, abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hr hs0]
  have hw2ByS : |w ^ 2| ≤ 9 * s ^ 2 := by
    have := hpow hwByS (by positivity)
    nlinarith
  have hfour :
      |thirdFourRemainderError s z| ≤ s ^ 2 / 1000000 := by
    have h2Q := hmul (show |(2 : ℝ)| ≤ 2 by norm_num) hQabs (by norm_num)
    have h2Qs := hmul h2Q hs2abs (by norm_num)
    have ht₁ := hmul h2Qs hδsabs (by positivity)
    have hzδ := hmul hsmallz hδ₄abs (by positivity)
    have hquot := hmul htwoz hzδ (by norm_num)
    have ht₂ := hmul hρabs hquot (by norm_num)
    unfold thirdFourRemainderError
    change |2 * Q * s ^ 2 * δs + ρ * (2 * z / d₄ *
      (s ^ 2 * z ^ 2 / d₄ ^ 2 * δ₄))| ≤ s ^ 2 / 1000000
    calc
      _ ≤ |2 * Q * s ^ 2 * δs| +
          |ρ * (2 * z / d₄ * (s ^ 2 * z ^ 2 / d₄ ^ 2 * δ₄))| :=
        abs_add_le _ _
      _ ≤ (2 * 48 * s ^ 2) * (1 / 8000000000) +
          2 * (8 * ((16 * s ^ 2) * (1 / 8000000000))) := by
            gcongr
      _ ≤ s ^ 2 / 1000000 := by nlinarith [sq_nonneg s]
  have hthree :
      |thirdThreeRemainderError s z a b| ≤ s ^ 2 / 1000000 := by
    have h2Q := hmul (show |(2 : ℝ)| ≤ 2 by norm_num) hQabs (by norm_num)
    have h2Qr := hmul h2Q hrabs (by norm_num)
    have h2Qrw := hmul h2Qr hw2ByS (by norm_num)
    have ht₁ := hmul h2Qrw hδwabs (by positivity)
    have heδ := hmul hsmalle hδ₃abs (by positivity)
    have hquot := hmul htwoe heδ (by norm_num)
    have ht₂ := hmul hρabs hquot (by norm_num)
    unfold thirdThreeRemainderError
    change |2 * Q * r * w ^ 2 * δw +
      ρ * (2 * e / d₃ * (s ^ 2 * e ^ 2 / d₃ ^ 2 * δ₃))| ≤
        s ^ 2 / 1000000
    calc
      _ ≤ |2 * Q * r * w ^ 2 * δw| +
          |ρ * (2 * e / d₃ * (s ^ 2 * e ^ 2 / d₃ ^ 2 * δ₃))| :=
        abs_add_le _ _
      _ ≤ ((2 * 48 * 3) * (9 * s ^ 2)) * (1 / 8000000000) +
          2 * (16 * ((64 * s ^ 2) * (1 / 8000000000))) := by
            gcongr
      _ ≤ s ^ 2 / 1000000 := by nlinarith [sq_nonneg s]
  have hsFactor : |4 - 2 * z * s / 3| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hs0 (by linarith : 0 ≤ z)]
  have hsPlus : |1 + s ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hwPlus : |1 + w ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg w]
  have hyPlus : |1 + y ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg y]
  have hvPlus : |1 + v ^ 2| ≤ 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg v]
  have hsPlusSq := hpow hsPlus (by norm_num)
  have hwPlusSq := hpow hwPlus (by norm_num)
  have hareaDen :
      |areaDenominator s z a b| ≤ 128 := by
    unfold areaDenominator
    have h₁ := hmul (show |(2 : ℝ)| ≤ 2 by norm_num) hsPlusSq (by norm_num)
    have h₂ := hmul h₁ hwPlusSq (by norm_num)
    have h₃ := hmul h₂ hyPlus (by norm_num)
    have h₄ := hmul h₃ hvPlus (by norm_num)
    norm_num at h₄ ⊢
    simpa [mul_assoc] using h₄
  have hfoldDen : |foldDenominator s z| ≤ 16 := by
    unfold foldDenominator
    have h₁ := hmul (show |(2 : ℝ)| ≤ 2 by norm_num) hsPlusSq (by norm_num)
    have h₂ := hmul h₁ hyPlus (by norm_num)
    norm_num at h₂ ⊢
    simpa [mul_assoc] using h₂
  have hA0 : 0 ≤ aCoord s z := by simp only [aCoord]; positivity
  have hA : aCoord s z ≤ 2 := by simp only [aCoord]; nlinarith
  have hfourSine : |typeFourSineProductBar s z| ≤ 8 := by
    unfold typeFourSineProductBar
    have hden : 1 ≤ (1 + s ^ 2) * (1 + y ^ 2) := by
      nlinarith [sq_nonneg s, sq_nonneg y,
        mul_nonneg (sq_nonneg s) (sq_nonneg y)]
    apply hdiv (hd := hden) (hU := by norm_num)
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hhcS := halfCos_abs_le_one s
  have hhcW := halfCos_abs_le_one w
  have htwoCos : |2 * halfCos s ^ 2| ≤ 2 := by
    have hsq := hpow hhcS (by norm_num)
    simpa using hmul (show |(2 : ℝ)| ≤ 2 by norm_num) hsq (by norm_num)
  have honeCos : |(1 + halfCos w) ^ 2| ≤ 4 := by
    have hbase : |1 + halfCos w| ≤ 2 := by
      calc
        |1 + halfCos w| ≤ |(1 : ℝ)| + |halfCos w| := abs_add_le _ _
        _ ≤ 2 := by norm_num at hhcW ⊢; linarith
    have h := hpow hbase (by norm_num)
    norm_num at h ⊢
    exact h
  have hareaInside :
      |2 * halfCos s ^ 2 * thirdThreeRemainderError s z a b -
        (1 + halfCos w) ^ 2 * thirdFourRemainderError s z| ≤
          6 * (s ^ 2 / 1000000) := by
    have h₃ := hmul htwoCos hthree (by norm_num)
    have h₄ := hmul honeCos hfour (by norm_num)
    calc
      _ ≤ |2 * halfCos s ^ 2 * thirdThreeRemainderError s z a b| +
          |(1 + halfCos w) ^ 2 * thirdFourRemainderError s z| :=
        abs_sub _ _
      _ ≤ 2 * (s ^ 2 / 1000000) + 4 * (s ^ 2 / 1000000) := by
        gcongr
      _ = 6 * (s ^ 2 / 1000000) := by ring
  have harea :
      |areaDenominator s z a b *
        (2 * halfCos s ^ 2 * thirdThreeRemainderError s z a b -
          (1 + halfCos w) ^ 2 * thirdFourRemainderError s z)| ≤
          128 * (6 * (s ^ 2 / 1000000)) :=
    hmul hareaDen hareaInside (by norm_num)
  have hfold :
      |(4 - 2 * z * s / 3) *
        (-foldDenominator s z * typeFourSineProductBar s z * s ^ 2 *
          thirdFourRemainderError s z)| ≤
          5 * 16 * 8 * s ^ 2 * (s ^ 2 / 1000000) := by
    have hnegFold : |-foldDenominator s z| ≤ 16 := by simpa using hfoldDen
    have h₁ := hmul hsFactor hnegFold (by norm_num)
    have h₂ := hmul h₁ hfourSine (by norm_num)
    have h₃ := hmul h₂ hs2abs (by norm_num)
    have h₄ := hmul h₃ hfour (by positivity)
    norm_num at h₄ ⊢
    simpa [mul_assoc] using h₄
  change |regularizedThirdRow s z a b π -
    thirdRegularizedFrozen s z a b| ≤ s ^ 2 / 1000
  rw [regularizedThirdRow_sub_frozen (by simpa [y] using hyne)
    (by exact ne_of_gt (lt_of_lt_of_le (by norm_num) hd₄))]
  calc
    _ ≤
        |areaDenominator s z a b *
          (2 * halfCos s ^ 2 * thirdThreeRemainderError s z a b -
            (1 + halfCos w) ^ 2 * thirdFourRemainderError s z)| +
        |(4 - 2 * z * s / 3) *
          (-foldDenominator s z * typeFourSineProductBar s z * s ^ 2 *
            thirdFourRemainderError s z)| := abs_add_le _ _
    _ ≤ 128 * (6 * (s ^ 2 / 1000000)) +
        5 * 16 * 8 * s ^ 2 * (s ^ 2 / 1000000) := add_le_add harea hfold
    _ ≤ s ^ 2 / 1000 := by
      nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs2R)]


/-- A quantitative numerator estimate for the honest regularized row is
exactly the remaining obligation in the explicit third-face argument.  This
form avoids both the totalized quotient and any division by the small scale. -/
theorem explicit_third_face_cell_of_regularized_error {s : ℝ}
    (hs0 : 0 ≤ s)
    (herror : ∀ q, InEndpointBox q →
      |regularizedThirdRow s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) π -
        s ^ 2 * poleFreeThirdRescaledRow 0 q| < 4 * s ^ 2) :
    ∀ q, InEndpointBox q →
      (q 2 = endpointBoxLower 2 →
        rescaledOrientedNearOneMap s q 2 < 0) ∧
      (q 2 = endpointBoxUpper 2 →
        0 < rescaledOrientedNearOneMap s q 2) := by
  apply third_face_signs_of_endpoint_perturbation
  intro q hq
  rw [rescaledOrientedNearOneMap_third_eq_neg_poleFree,
    rescaledOrientedNearOneMap_third_eq_neg_poleFree]
  rw [show -poleFreeThirdRescaledRow s q -
      -poleFreeThirdRescaledRow 0 q =
        -(poleFreeThirdRescaledRow s q -
          poleFreeThirdRescaledRow 0 q) by ring, abs_neg]
  by_cases hs : s = 0
  · subst s
    simp
  · have hs2pos : 0 < s ^ 2 := sq_pos_of_ne_zero hs
    rw [poleFreeThirdRescaledRow, if_neg hs]
    change |regularizedThirdRow s (thirdPhysicalZ s q)
        (thirdPhysicalA s q) (thirdPhysicalB s q) π / s ^ 2 -
      poleFreeThirdRescaledRow 0 q| < 4
    rw [show regularizedThirdRow s (thirdPhysicalZ s q)
          (thirdPhysicalA s q) (thirdPhysicalB s q) π / s ^ 2 -
          poleFreeThirdRescaledRow 0 q =
        (regularizedThirdRow s (thirdPhysicalZ s q)
            (thirdPhysicalA s q) (thirdPhysicalB s q) π -
          s ^ 2 * poleFreeThirdRescaledRow 0 q) / s ^ 2 by
        field_simp]
    rw [abs_div, abs_of_pos hs2pos, div_lt_iff₀ hs2pos]
    exact herror q hq

/-- Version of `explicit_third_face_cell_of_regularized_error` with the
endpoint coefficient completely expanded.  In particular, this statement
isolates a single rational-algebraic inequality and contains no hidden
continuity or limiting obligation. -/
theorem explicit_third_face_cell_of_explicit_numerator_error {s : ℝ}
    (hs0 : 0 ≤ s)
    (herror : ∀ q, InEndpointBox q →
      |regularizedThirdRow s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) π -
        s ^ 2 *
          (π * (1193 * π ^ 4 + 2748816 * π ^ 2 -
            31104 * q 2 - 146105856) / 7776)| < 4 * s ^ 2) :
    ∀ q, InEndpointBox q →
      (q 2 = endpointBoxLower 2 →
        rescaledOrientedNearOneMap s q 2 < 0) ∧
      (q 2 = endpointBoxUpper 2 →
        0 < rescaledOrientedNearOneMap s q 2) := by
  apply explicit_third_face_cell_of_regularized_error hs0
  intro q hq
  simpa using herror q hq
/-- At positive scale it remains to bound only the fully rational frozen row.
Any strict `3999/1000` frozen-row estimate combines with the proved arctangent
error budget to give both third-coordinate face signs. -/
theorem explicit_third_face_cell_of_frozen_error {s : ℝ}
    (hspos : 0 < s) (hs : s ≤ 1 / 126334)
    (hfrozen : ∀ q, InEndpointBox q →
      |thirdRegularizedFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) -
        s ^ 2 *
          (π * (1193 * π ^ 4 + 2748816 * π ^ 2 -
            31104 * q 2 - 146105856) / 7776)| <
        (3999 / 1000 : ℝ) * s ^ 2) :
    ∀ q, InEndpointBox q →
      (q 2 = endpointBoxLower 2 →
        rescaledOrientedNearOneMap s q 2 < 0) ∧
      (q 2 = endpointBoxUpper 2 →
        0 < rescaledOrientedNearOneMap s q 2) := by
  apply explicit_third_face_cell_of_explicit_numerator_error hspos.le
  intro q hq
  have hatan :=
    explicit_regularizedThirdRow_sub_frozen_abs_bound q hspos.le hs hq
  have hfrozenq := hfrozen q hq
  calc
    |regularizedThirdRow s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) π -
        s ^ 2 *
          (π * (1193 * π ^ 4 + 2748816 * π ^ 2 -
            31104 * q 2 - 146105856) / 7776)| ≤
        |regularizedThirdRow s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q) π -
          thirdRegularizedFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q)| +
        |thirdRegularizedFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
            (thirdPhysicalB s q) -
          s ^ 2 *
            (π * (1193 * π ^ 4 + 2748816 * π ^ 2 -
              31104 * q 2 - 146105856) / 7776)| := abs_sub_le _ _ _
    _ < s ^ 2 / 1000 + (3999 / 1000 : ℝ) * s ^ 2 :=
      add_lt_add_of_le_of_lt hatan hfrozenq
    _ = 4 * s ^ 2 := by ring

/-- The one remaining quantitative premise for the complete relaxed endpoint
cell.  It is purely rational: all arctangent remainders have already been
removed from `thirdRegularizedFrozen`. -/
def ExplicitThirdFrozenEstimate : Prop :=
  ∀ s, 0 < s → s ≤ 1 / 126334 →
    ∀ q, InEndpointBox q →
      |thirdRegularizedFrozen s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q) -
        s ^ 2 *
          (π * (1193 * π ^ 4 + 2748816 * π ^ 2 -
            31104 * q 2 - 146105856) / 7776)| <
        (3999 / 1000 : ℝ) * s ^ 2

/-- Once the rational frozen-row estimate is supplied, the first, second, and
third pairs of endpoint faces compose into a literal six-face radius.  The
zero-scale face is handled directly by the exact diagonal cusp map. -/
theorem explicit_all_face_cell_of_frozen_estimate
    (hfrozen : ExplicitThirdFrozenEstimate) :
    ∀ s, 0 ≤ s → s ≤ 1 / 126334 → HasEndpointBoxFaceSigns s := by
  intro s hs0 hs
  by_cases hsZero : s = 0
  · subst s
    exact endpointBox_strict_opposite_faces
  have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZero)
  have hfirstSecondRadius : s ≤ 1 / 126334 := by
    norm_num at hs ⊢
    linarith
  have hfirst := explicit_first_face_cell hs0 hfirstSecondRadius
  have hsecond := explicit_second_face_cell hs0 hfirstSecondRadius
  have hthird := explicit_third_face_cell_of_frozen_error hspos hs
    (hfrozen s hspos hs)
  intro q hq i
  fin_cases i
  · exact hfirst q hq
  · exact hsecond q hq
  · exact hthird q hq

end ExplicitThirdRowFaces

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
