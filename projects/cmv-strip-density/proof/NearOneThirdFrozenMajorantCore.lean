/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOnePolynomialMajorant
import NearOneThirdFrozenCoefficientBound

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

section FrozenPolynomial

def boundedC (c M : ℝ) (hM : 0 ≤ M) (h : |c| ≤ M) :
    PolynomialMajorant (C c) where
  majorant := C M
  coeff_nonneg := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [hM]
    · simp [coeff_C, hn]
  coeff_abs_le := by
    intro n
    by_cases hn : n = 0
    · subst n
      simpa using h
    · simp [coeff_C, hn]

lemma endpoint_coordinate_bounds (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    52 ≤ q 0 ∧ q 0 ≤ 54 ∧ 27 ≤ q 1 ∧ q 1 ≤ 28 ∧
      -3822 ≤ q 2 ∧ q 2 ≤ -3821 := by
  have hq0 := hq (0 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  have hq2 := hq (2 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at hq2
  exact ⟨hq0.1, hq0.2, hq1.1, hq1.2, hq2.1, hq2.2⟩

/-- Exact nonnegative coefficient majorant `[4, 16, 54]` for the `z` path. -/
def zPathMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (rescaledZPathPolynomial q) := by
  have hbounds := endpoint_coordinate_bounds q hq
  have hq0hi := hbounds.2.1
  have hpi : |π| ≤ (4 : ℝ) := by
    rw [abs_of_pos Real.pi_pos]
    exact Real.pi_lt_four.le
  have hpi2 : |π ^ 2| ≤ (16 : ℝ) := by
    rw [abs_of_nonneg (sq_nonneg π)]
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hq0 : |q 0| ≤ (54 : ℝ) := by
    rw [abs_of_nonneg (by linarith)]
    exact hq0hi
  exact
    (((boundedC π 4 (by norm_num) hpi).add
      ((boundedC (π ^ 2) 16 (by norm_num) hpi2).mul PolynomialMajorant.X)).add
      ((boundedC (q 0) 54 (by norm_num) hq0).mul
        (PolynomialMajorant.X.pow 2))).reindex (by
          simp [rescaledZPathPolynomial])

/-- Exact nonnegative coefficient majorant `[2, 13, 51]` for the `a` path. -/
def aPathMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (rescaledAPathPolynomial q) := by
  have hbounds := endpoint_coordinate_bounds q hq
  have hq0lo := hbounds.1
  have hq0hi := hbounds.2.1
  have hq1lo := hbounds.2.2.1
  have hq1hi := hbounds.2.2.2.1
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
  have ha0 : |5 * π / 12| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have ha1nonneg : 0 ≤ (43 * π ^ 2 + 1056) / 144 := by positivity
  have ha1 : |(43 * π ^ 2 + 1056) / 144| ≤ (13 : ℝ) := by
    rw [abs_of_nonneg ha1nonneg]
    nlinarith [sq_nonneg (π - 4)]
  have ha2nonneg : 0 ≤ 5 * q 0 / 12 + q 1 := by linarith
  have ha2 : |5 * q 0 / 12 + q 1| ≤ (51 : ℝ) := by
    rw [abs_of_nonneg ha2nonneg]
    linarith
  exact
    (((boundedC (5 * π / 12) 2 (by norm_num) ha0).add
      ((boundedC ((43 * π ^ 2 + 1056) / 144) 13
        (by norm_num) ha1).mul PolynomialMajorant.X)).add
      ((boundedC (5 * q 0 / 12 + q 1) 51
        (by norm_num) ha2).mul (PolynomialMajorant.X.pow 2))).reindex (by
          simp [rescaledAPathPolynomial])

/-- Exact nonnegative coefficient majorant `[44, 270, 5200]` for the `b` path. -/
def bPathMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (rescaledBPathPolynomial q) := by
  have hbounds := endpoint_coordinate_bounds q hq
  have hq0lo := hbounds.1
  have hq0hi := hbounds.2.1
  have hq1lo := hbounds.2.2.1
  have hq1hi := hbounds.2.2.2.1
  have hq2lo := hbounds.2.2.2.2.1
  have hq2hi := hbounds.2.2.2.2.2
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hpi3 : 3 ≤ π := Real.pi_gt_three.le
  have hpi4 : π ≤ 4 := Real.pi_lt_four.le
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
    have hi : 295 * π ^ 2 - 14256 ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hpi0 hi) (by norm_num)
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
    exact (mul_le_mul hfrac hq1hi (by linarith) (by linarith)).trans_eq
      (by norm_num)
  have hbquadLo : -5200 ≤
      (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 := by linarith
  have hbquadHi :
      (109 * π ^ 2 - 5376) / (72 * π) * q 0 +
        (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2 ≤ 700 := by linarith
  have hb0 : |-44 + 19 * π ^ 2 / 24| ≤ (44 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hb1 : |π * (295 * π ^ 2 - 14256) / 216| ≤ (270 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hb2 : |(109 * π ^ 2 - 5376) / (72 * π) * q 0 +
      (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2| ≤ (5200 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  exact
    (((boundedC (-44 + 19 * π ^ 2 / 24) 44 (by norm_num) hb0).add
      ((boundedC (π * (295 * π ^ 2 - 14256) / 216) 270
        (by norm_num) hb1).mul PolynomialMajorant.X)).add
      ((boundedC ((109 * π ^ 2 - 5376) / (72 * π) * q 0 +
          (2880 - 7 * π ^ 2) / (6 * π) * q 1 + q 2) 5200
        (by norm_num) hb2).mul (PolynomialMajorant.X.pow 2))).reindex (by
          simp [rescaledBPathPolynomial])

def oneMajorant : PolynomialMajorant (1 : ℝ[X]) :=
  (PolynomialMajorant.C 1).reindex (by norm_num)

def natMajorant (n : ℕ) : PolynomialMajorant (n : ℝ[X]) :=
  (PolynomialMajorant.C (n : ℝ)).reindex (by simp)

@[simp] theorem oneMajorant_majorant :
    oneMajorant.majorant = (1 : ℝ[X]) := by
  change Polynomial.C |(1 : ℝ)| = _
  norm_num

@[simp] theorem natMajorant_majorant (n : ℕ) :
    (natMajorant n).majorant = (n : ℝ[X]) := by
  change Polynomial.C |(n : ℝ)| = _
  rw [abs_of_nonneg (Nat.cast_nonneg n)]
  simp

def rationalMajorant (r : ℝ) : PolynomialMajorant (C r) :=
  PolynomialMajorant.C r

def oneSubX2Majorant : PolynomialMajorant ((1 : ℝ[X]) - X ^ 2) :=
  oneMajorant.sub (PolynomialMajorant.X.pow 2)

def oneAddX2Majorant : PolynomialMajorant ((1 : ℝ[X]) + X ^ 2) :=
  oneMajorant.add (PolynomialMajorant.X.pow 2)

@[simp] theorem oneSubX2Majorant_majorant :
    oneSubX2Majorant.majorant = (1 : ℝ[X]) + X ^ 2 := by
  change (oneMajorant.sub (PolynomialMajorant.X.pow 2)).majorant = _
  simp

@[simp] theorem oneAddX2Majorant_majorant :
    oneAddX2Majorant.majorant = (1 : ℝ[X]) + X ^ 2 := by
  change (oneMajorant.add (PolynomialMajorant.X.pow 2)).majorant = _
  simp

def frozenAlgAMajorant {Z : ℝ[X]} (hZ : PolynomialMajorant Z) :
    PolynomialMajorant (frozenAlgA Z) :=
  (oneMajorant.add (PolynomialMajorant.X.mul hZ)).reindex (by
    simp [frozenAlgA])

@[simp] theorem frozenAlgAMajorant_majorant {Z : ℝ[X]}
    (hZ : PolynomialMajorant Z) :
    (frozenAlgAMajorant hZ).majorant =
      oneMajorant.majorant + Polynomial.X * hZ.majorant := by
  change (oneMajorant.add (PolynomialMajorant.X.mul hZ)).majorant = _
  rfl

def frozenAlgRMajorant {A : ℝ[X]} (hA : PolynomialMajorant A) :
    PolynomialMajorant (frozenAlgR A) :=
  ((natMajorant 2).add (PolynomialMajorant.X.mul hA)).reindex (by
    simp [frozenAlgR])

@[simp] theorem frozenAlgRMajorant_majorant {A : ℝ[X]}
    (hA : PolynomialMajorant A) :
    (frozenAlgRMajorant hA).majorant =
      (2 : ℝ[X]) + Polynomial.X * hA.majorant := by
  change ((natMajorant 2).add (PolynomialMajorant.X.mul hA)).majorant = _
  simp

def frozenAlgEMajorant {Z A B : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgE Z A B) :=
  (((natMajorant 6).mul hA).sub ((natMajorant 2).mul hZ) |>.add
    (PolynomialMajorant.X.mul hB)).reindex (by
      simp [frozenAlgE])

@[simp] theorem frozenAlgEMajorant_majorant {Z A B : ℝ[X]}
    (hZ : PolynomialMajorant Z) (hA : PolynomialMajorant A)
    (hB : PolynomialMajorant B) :
    (frozenAlgEMajorant hZ hA hB).majorant =
      (6 : ℝ[X]) * hA.majorant + (2 : ℝ[X]) * hZ.majorant +
        Polynomial.X * hB.majorant := by
  change ((((natMajorant 6).mul hA).sub ((natMajorant 2).mul hZ)).add
    (PolynomialMajorant.X.mul hB)).majorant = _
  simp

def frozenAlgDoubleEMajorant {Z A B : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgDoubleE Z A B) :=
  (((natMajorant 12).mul hA).sub ((natMajorant 4).mul hZ) |>.add
    (((natMajorant 2).mul PolynomialMajorant.X).mul hB)).reindex (by
      simp [frozenAlgDoubleE, mul_assoc])

@[simp] theorem frozenAlgDoubleEMajorant_majorant {Z A B : ℝ[X]}
    (hZ : PolynomialMajorant Z) (hA : PolynomialMajorant A)
    (hB : PolynomialMajorant B) :
    (frozenAlgDoubleEMajorant hZ hA hB).majorant =
      (12 : ℝ[X]) * hA.majorant + (4 : ℝ[X]) * hZ.majorant +
        ((2 : ℝ[X]) * Polynomial.X) * hB.majorant := by
  change ((((natMajorant 12).mul hA).sub ((natMajorant 4).mul hZ)).add
    (((natMajorant 2).mul PolynomialMajorant.X).mul hB)).majorant = _
  simp

def frozenAlgDoubleBMajorant {Z A B : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgDoubleB Z A B) :=
  (((natMajorant 2).mul (frozenAlgRMajorant hA)).add
    (PolynomialMajorant.X.mul
      (frozenAlgDoubleEMajorant hZ hA hB))).reindex (by
        simp [frozenAlgDoubleB])

@[simp] theorem frozenAlgDoubleBMajorant_majorant {Z A B : ℝ[X]}
    (hZ : PolynomialMajorant Z) (hA : PolynomialMajorant A)
    (hB : PolynomialMajorant B) :
    (frozenAlgDoubleBMajorant hZ hA hB).majorant =
      (2 : ℝ[X]) * (frozenAlgRMajorant hA).majorant +
        Polynomial.X * (frozenAlgDoubleEMajorant hZ hA hB).majorant := by
  change (((natMajorant 2).mul (frozenAlgRMajorant hA)).add
    (PolynomialMajorant.X.mul
      (frozenAlgDoubleEMajorant hZ hA hB))).majorant = _
  simp

def frozenAlgFoldNumeratorMajorant {Z : ℝ[X]} (hZ : PolynomialMajorant Z)
    (p : ℝ) : PolynomialMajorant (frozenAlgFoldNumerator Z p) :=
  let hAlgA := frozenAlgAMajorant hZ
  (((hZ.mul oneSubX2Majorant).mul
    (oneMajorant.sub ((PolynomialMajorant.X.pow 2).mul hAlgA))).sub
    (((rationalMajorant p).mul hAlgA).mul oneAddX2Majorant)).reindex (by
      simp [frozenAlgFoldNumerator])

def frozenAlgCosineNumeratorMajorant {Z A B : ℝ[X]}
    (hZ : PolynomialMajorant Z) (hA : PolynomialMajorant A)
    (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgCosineNumerator Z A B) :=
  let R := frozenAlgRMajorant hA
  let E := frozenAlgDoubleEMajorant hZ hA hB
  let t0 := ((natMajorant 4).mul E).mul R |>.sub ((natMajorant 8).mul hZ)
  let t1 := PolynomialMajorant.X.mul
    ((E.pow 2).sub ((natMajorant 4).mul (hZ.pow 2)))
  let t4 := (PolynomialMajorant.X.pow 4).mul
    ((((natMajorant 4).mul E).mul R).neg.add
      ((((natMajorant 8).mul (R.pow 4)).mul hZ)))
  let t5 := (PolynomialMajorant.X.pow 5).mul
    ((((E.pow 2).neg.add
      ((((natMajorant 8).mul E).mul (R.pow 3)).mul hZ)).sub
        ((((natMajorant 8).mul E).mul R).mul hZ)).add
      (((natMajorant 4).mul (R.pow 4)).mul (hZ.pow 2)))
  let t6 := (PolynomialMajorant.X.pow 6).mul
    (((((natMajorant 2).mul (E.pow 2)).mul (R.pow 2)).mul hZ).sub
      (((natMajorant 2).mul (E.pow 2)).mul hZ) |>.add
      ((((natMajorant 4).mul E).mul (R.pow 3)).mul (hZ.pow 2)) |>.sub
      ((((natMajorant 4).mul E).mul R).mul (hZ.pow 2)))
  let t7 := (PolynomialMajorant.X.pow 7).mul
    ((((E.pow 2).mul (R.pow 2)).mul (hZ.pow 2)).sub
      ((E.pow 2).mul (hZ.pow 2)))
  (((((t0.add t1).add t4).add t5).add t6).add t7).reindex (by
    simp [frozenAlgCosineNumerator])

def frozenAlgKMajorant {A : ℝ[X]} (hA : PolynomialMajorant A) :
    PolynomialMajorant (frozenAlgK A) :=
  (((((natMajorant 2).mul ((frozenAlgRMajorant hA).pow 2)).sub
        (natMajorant 4)).add
      ((PolynomialMajorant.X.pow 2).mul
        (((frozenAlgRMajorant hA).pow 4).sub
          ((natMajorant 4).mul ((frozenAlgRMajorant hA).pow 2))))).add
    (((natMajorant 2).mul (PolynomialMajorant.X.pow 4)).mul
      (((frozenAlgRMajorant hA).pow 2).sub
        ((frozenAlgRMajorant hA).pow 4)))).add
    ((PolynomialMajorant.X.pow 6).mul
      ((frozenAlgRMajorant hA).pow 4)) |>.reindex (by
        simp [frozenAlgK])

def frozenAlgUMajorant {Z : ℝ[X]} (hZ : PolynomialMajorant Z) :
    PolynomialMajorant (frozenAlgU Z) :=
  ((oneSubX2Majorant.pow 2).mul
    (oneMajorant.add ((PolynomialMajorant.X.pow 2).mul
      ((frozenAlgAMajorant hZ).pow 2)))).reindex (by
        simp [frozenAlgU])

def frozenAlgWMajorant {Z A B : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgW Z A B) :=
  ((oneMajorant.add ((PolynomialMajorant.X.pow 2).mul
    ((frozenAlgRMajorant hA).pow 2))).pow 2 |>.mul
    ((natMajorant 4).add ((PolynomialMajorant.X.pow 2).mul
      ((frozenAlgDoubleBMajorant hZ hA hB).pow 2)))).reindex (by
        simp [frozenAlgW])

def frozenAlgAreaXMajorant {Z A B : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgAreaX Z A B) :=
  let R := frozenAlgRMajorant hA
  let DB := frozenAlgDoubleBMajorant hZ hA hB
  (((natMajorant 3).add ((PolynomialMajorant.X.pow 2).mul (R.pow 2))).mul
    ((natMajorant 2).sub
      (((PolynomialMajorant.X.pow 2).mul R).mul DB))).reindex (by
        simp [frozenAlgAreaX])

def frozenAlgAreaZMajorant {Z : ℝ[X]} (hZ : PolynomialMajorant Z) :
    PolynomialMajorant (frozenAlgAreaZ Z) :=
  (oneSubX2Majorant.mul
    (oneMajorant.sub ((PolynomialMajorant.X.pow 2).mul
      (frozenAlgAMajorant hZ)))).reindex (by
        simp [frozenAlgAreaZ])

def frozenAlgAreaLMajorant {Z A B : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (hB : PolynomialMajorant B) :
    PolynomialMajorant (frozenAlgAreaL Z A B) :=
  (((oneMajorant.add ((PolynomialMajorant.X.pow 2).mul
    ((frozenAlgAMajorant hZ).pow 2))).mul
    ((natMajorant 4).add ((PolynomialMajorant.X.pow 2).mul
      ((frozenAlgDoubleBMajorant hZ hA hB).pow 2)))) |>.mul
    (frozenAlgKMajorant hA)).reindex (by
      simp [frozenAlgAreaL])

def frozenAlgAreaNumeratorMajorant {Z A B : ℝ[X]}
    (hZ : PolynomialMajorant Z) (hA : PolynomialMajorant A)
    (hB : PolynomialMajorant B) (p : ℝ) :
    PolynomialMajorant (frozenAlgAreaNumerator Z A B p) :=
  let E := frozenAlgDoubleEMajorant hZ hA hB
  let U := frozenAlgUMajorant hZ
  let W := frozenAlgWMajorant hZ hA hB
  let AX := frozenAlgAreaXMajorant hZ hA hB
  let AZ := frozenAlgAreaZMajorant hZ
  let AL := frozenAlgAreaLMajorant hZ hA hB
  (((((rationalMajorant p).mul AL).add
    ((((E.sub ((natMajorant 4).mul hZ)).mul U).mul W))).add
    ((((natMajorant 2).mul E).mul U).mul AX)).sub
    (((natMajorant 4).mul hZ).mul
      ((natMajorant 4).add ((PolynomialMajorant.X.pow 2).mul
        ((frozenAlgDoubleBMajorant hZ hA hB).pow 2))) |>.mul AZ)).reindex (by
          simp [frozenAlgAreaNumerator])

def frozenAlgQPrimeMajorant {Z A : ℝ[X]} (hZ : PolynomialMajorant Z)
    (hA : PolynomialMajorant A) (p : ℝ) :
    PolynomialMajorant (frozenAlgQPrime Z A p) :=
  (((natMajorant 4).mul hA).sub
    ((rationalMajorant (1 / 3 : ℝ)).mul
      (((natMajorant 2).mul hZ).add (rationalMajorant p)))).reindex (by
        simp [frozenAlgQPrime])

def frozenAlgThirdNumeratorMajorant {Z A B : ℝ[X]}
    (hZ : PolynomialMajorant Z) (hA : PolynomialMajorant A)
    (hB : PolynomialMajorant B) (p : ℝ) :
    PolynomialMajorant (frozenAlgThirdNumerator Z A B p) :=
  let area := frozenAlgAreaNumeratorMajorant hZ hA hB p
  let cosine := frozenAlgCosineNumeratorMajorant hZ hA hB
  let fold := frozenAlgFoldNumeratorMajorant hZ p
  let qprime := frozenAlgQPrimeMajorant hZ hA p
  (((area.sub ((natMajorant 2).mul cosine)).add
    ((natMajorant 16).mul fold)).add
    (PolynomialMajorant.X.mul
      ((qprime.mul cosine).sub
        ((((rationalMajorant (8 / 3 : ℝ)).mul hZ).mul fold))))).reindex (by
          simp [frozenAlgThirdNumerator])

def frozenH3PathNumeratorMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenH3PathNumerator q) :=
  (frozenAlgThirdNumeratorMajorant (zPathMajorant q hq)
    (aPathMajorant q hq) (bPathMajorant q hq) π).reindex (by
      simp [frozenH3PathNumerator])

def frozenH3PathPolynomialMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenH3PathPolynomial q) :=
  ((frozenH3PathNumeratorMajorant q hq).divX.divX).reindex (by
    simp [frozenH3PathPolynomial])

def frozenPathAMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathA q) :=
  (frozenAlgAMajorant (zPathMajorant q hq)).reindex (by
    simp [frozenPathA])

@[simp] theorem frozenPathAMajorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathAMajorant q hq).majorant =
      (frozenAlgAMajorant (zPathMajorant q hq)).majorant := by
  rfl

def frozenPathRMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathR q) :=
  (frozenAlgRMajorant (aPathMajorant q hq)).reindex (by
    simp [frozenPathR])

@[simp] theorem frozenPathRMajorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathRMajorant q hq).majorant =
      (frozenAlgRMajorant (aPathMajorant q hq)).majorant := by
  rfl

def frozenPathEMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathE q) :=
  (frozenAlgEMajorant (zPathMajorant q hq)
    (aPathMajorant q hq) (bPathMajorant q hq)).reindex (by
      simp [frozenPathE])

@[simp] theorem frozenPathEMajorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathEMajorant q hq).majorant =
      (frozenAlgEMajorant (zPathMajorant q hq)
        (aPathMajorant q hq) (bPathMajorant q hq)).majorant := by
  rfl

def frozenPathYMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathY q) :=
  (PolynomialMajorant.X.mul (frozenPathAMajorant q hq)).reindex (by
    simp [frozenPathY])

@[simp] theorem frozenPathYMajorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathYMajorant q hq).majorant =
      X * (frozenPathAMajorant q hq).majorant := by
  rfl

def frozenPathWMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathW q) :=
  (PolynomialMajorant.X.mul (frozenPathRMajorant q hq)).reindex (by
    simp [frozenPathW])

@[simp] theorem frozenPathWMajorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathWMajorant q hq).majorant =
      X * (frozenPathRMajorant q hq).majorant := by
  rfl

def frozenPathVMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathV q) :=
  (PolynomialMajorant.X.mul
    ((frozenPathRMajorant q hq).add
      (PolynomialMajorant.X.mul (frozenPathEMajorant q hq)))).reindex (by
        simp [frozenPathV])

@[simp] theorem frozenPathVMajorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathVMajorant q hq).majorant =
      X * ((frozenPathRMajorant q hq).majorant +
        X * (frozenPathEMajorant q hq).majorant) := by
  rfl

def frozenPathD4Majorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathD4 q) :=
  (oneMajorant.add
    (PolynomialMajorant.X.mul (frozenPathYMajorant q hq))).reindex (by
      simp [frozenPathD4])

@[simp] theorem frozenPathD4Majorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathD4Majorant q hq).majorant =
      1 + X * (frozenPathYMajorant q hq).majorant := by
  change (oneMajorant.add
    (PolynomialMajorant.X.mul (frozenPathYMajorant q hq))).majorant = _
  simp

def frozenPathD3Majorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathD3 q) :=
  (oneMajorant.add
    ((frozenPathWMajorant q hq).mul
      (frozenPathVMajorant q hq))).reindex (by
        simp [frozenPathD3])

@[simp] theorem frozenPathD3Majorant_majorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    (frozenPathD3Majorant q hq).majorant =
      1 + (frozenPathWMajorant q hq).majorant *
        (frozenPathVMajorant q hq).majorant := by
  change (oneMajorant.add
    ((frozenPathWMajorant q hq).mul
      (frozenPathVMajorant q hq))).majorant = _
  simp

def frozenPathDensityDenominatorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathDensityDenominator q) :=
  (oneAddX2Majorant.mul
    (oneMajorant.sub ((frozenPathYMajorant q hq).pow 2))).reindex (by
      simp [frozenPathDensityDenominator])

@[simp] theorem frozenPathDensityDenominatorMajorant_majorant
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (frozenPathDensityDenominatorMajorant q hq).majorant =
      (1 + X ^ 2) * (1 + (frozenPathYMajorant q hq).majorant ^ 2) := by
  change (oneAddX2Majorant.mul
    (oneMajorant.sub ((frozenPathYMajorant q hq).pow 2))).majorant = _
  simp

def frozenPathDensityNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathDensityNumerator q) :=
  (((natMajorant 2).mul (zPathMajorant q hq)).mul
    ((natMajorant 2).add
      (PolynomialMajorant.X.mul (zPathMajorant q hq)))).reindex (by
        simp [frozenPathDensityNumerator])

def frozenPathRhoNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathRhoNumerator q) :=
  (oneSubX2Majorant.mul
    (oneMajorant.add ((frozenPathYMajorant q hq).pow 2))).reindex (by
      simp [frozenPathRhoNumerator])

def frozenPathFourIncrementNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathFourIncrementNumerator q) :=
  let Z := zPathMajorant q hq
  (((natMajorant 2).mul Z).mul
    ((((PolynomialMajorant.X.pow 2).mul (Z.pow 2)).neg).sub
      ((((natMajorant 3).mul (frozenPathAMajorant q hq)).mul
        ((frozenPathD4Majorant q hq).pow 2))))).reindex (by
          simp [frozenPathFourIncrementNumerator])

def frozenPathThreeIncrementNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathThreeIncrementNumerator q) :=
  let E := frozenPathEMajorant q hq
  let R := frozenPathRMajorant q hq
  (((natMajorant 2).mul E).mul
    ((((PolynomialMajorant.X.pow 2).mul (E.pow 2)).neg).sub
      (((((natMajorant 3).mul R).mul
        (R.add (PolynomialMajorant.X.mul E))).mul
        ((frozenPathD3Majorant q hq).pow 2))))).reindex (by
          simp [frozenPathThreeIncrementNumerator])

def frozenPathFourBarNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathFourBarNumerator q) :=
  let density := frozenPathDensityNumeratorMajorant q hq
  let D4 := frozenPathD4Majorant q hq
  ((((((natMajorant 2).mul density).mul
    ((natMajorant 3).sub (PolynomialMajorant.X.pow 2))).mul
    (D4.pow 3)).add
    ((frozenPathRhoNumeratorMajorant q hq).mul
      (frozenPathFourIncrementNumeratorMajorant q hq))).add
    (((((natMajorant 6).mul PolynomialMajorant.X).mul
      (zPathMajorant q hq)).mul density).mul (D4.pow 3))).reindex (by
        simp [frozenPathFourBarNumerator])

def frozenPathThreeBarNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathThreeBarNumerator q) :=
  let density := frozenPathDensityNumeratorMajorant q hq
  let R := frozenPathRMajorant q hq
  let D3 := frozenPathD3Majorant q hq
  (((((((natMajorant 2).mul density).mul R).mul
    ((natMajorant 3).sub ((frozenPathWMajorant q hq).pow 2))).mul
    (D3.pow 3)).add
    ((frozenPathRhoNumeratorMajorant q hq).mul
      (frozenPathThreeIncrementNumeratorMajorant q hq))).add
    (((((natMajorant 6).mul PolynomialMajorant.X).mul
      (frozenPathEMajorant q hq)).mul density).mul (D3.pow 3))).reindex (by
        simp [frozenPathThreeBarNumerator])

def frozenPathCommonDenominatorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathCommonDenominator q) :=
  ((((natMajorant 3).mul (frozenPathDensityDenominatorMajorant q hq)).mul
    ((frozenPathD3Majorant q hq).pow 3)).mul
    ((frozenPathD4Majorant q hq).pow 3)).reindex (by
      simp [frozenPathCommonDenominator])

@[simp] theorem frozenPathCommonDenominatorMajorant_majorant
    (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    (frozenPathCommonDenominatorMajorant q hq).majorant =
      3 * (frozenPathDensityDenominatorMajorant q hq).majorant *
        (frozenPathD3Majorant q hq).majorant ^ 3 *
        (frozenPathD4Majorant q hq).majorant ^ 3 := by
  change ((((natMajorant 3).mul
    (frozenPathDensityDenominatorMajorant q hq)).mul
      ((frozenPathD3Majorant q hq).pow 3)).mul
      ((frozenPathD4Majorant q hq).pow 3)).majorant = _
  simp

def frozenPathThreeCoefficientMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathThreeCoefficient q) :=
  (((((natMajorant 4).mul (oneSubX2Majorant.pow 2)).mul
    ((oneMajorant.add ((frozenPathWMajorant q hq).pow 2)).pow 2)).mul
    (oneMajorant.add ((frozenPathYMajorant q hq).pow 2))).mul
    (oneMajorant.add ((frozenPathVMajorant q hq).pow 2))).reindex (by
      simp [frozenPathThreeCoefficient])

def frozenPathFourCoefficientMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathFourCoefficient q) :=
  (((((natMajorant 8).neg).mul (oneAddX2Majorant.pow 2)).mul
    (oneMajorant.add ((frozenPathYMajorant q hq).pow 2))).mul
    (oneMajorant.add ((frozenPathVMajorant q hq).pow 2))).reindex (by
      simp [frozenPathFourCoefficient])

def frozenPathPiCoefficientMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathPiCoefficient q) :=
  (((((natMajorant 16).mul (zPathMajorant q hq)).mul
    (frozenAlgKMajorant (aPathMajorant q hq))).mul
    (oneMajorant.add ((frozenPathYMajorant q hq).pow 2))).mul
    (oneMajorant.add ((frozenPathVMajorant q hq).pow 2))).reindex (by
      simp [frozenPathPiCoefficient])

def frozenPathFoldCoefficientMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathFoldCoefficient q) :=
  (((((natMajorant 4).sub
    (((rationalMajorant (2 / 3 : ℝ)).mul (zPathMajorant q hq)).mul
      PolynomialMajorant.X)).neg.mul (natMajorant 8)).mul
    (frozenPathAMajorant q hq)).mul oneAddX2Majorant).reindex (by
      simp [frozenPathFoldCoefficient])

def frozenPathCommonNumeratorMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : PolynomialMajorant (frozenPathCommonNumerator q) :=
  let commonD := frozenPathCommonDenominatorMajorant q hq
  let D3 := frozenPathD3Majorant q hq
  let D4 := frozenPathD4Majorant q hq
  let threeC := frozenPathThreeCoefficientMajorant q hq
  let fourC := frozenPathFourCoefficientMajorant q hq
  let foldC := frozenPathFoldCoefficientMajorant q hq
  (((((((commonD.mul (frozenH3PathPolynomialMajorant q hq)).add
    (((D4.pow 3).mul threeC).mul
      (frozenPathThreeBarNumeratorMajorant q hq))).add
    (((D3.pow 3).mul fourC).mul
      (frozenPathFourBarNumeratorMajorant q hq))).add
    (commonD.mul (frozenPathPiCoefficientMajorant q hq))).add
    ((commonD.mul foldC).mul
      ((natMajorant 2).mul (zPathMajorant q hq)))).add
    (((D3.pow 3).mul foldC).mul
      (PolynomialMajorant.X.pow 2) |>.mul
      (frozenPathFourBarNumeratorMajorant q hq))).reindex (by
        simp [frozenPathCommonNumerator]))

lemma frozenEndpointQuadratic_abs_le (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    |frozenEndpointQuadratic q| ≤ 16 := by
  have hq2 := (endpoint_coordinate_bounds q hq).2.2.2.2
  have hseed := seed_two_bounds
  have hid : frozenEndpointQuadratic q =
      4 * π * (exactRescaledOrientedNearOneSeed 2 - q 2) := by
    rw [frozenEndpointQuadratic]
    rw [show exactRescaledOrientedNearOneSeed 2 =
      (1193 * π ^ 4 + 2748816 * π ^ 2 - 146105856) / 31104 by
        simp [exactRescaledOrientedNearOneSeed]]
    ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_pos Real.pi_pos]
  have hdiff : |exactRescaledOrientedNearOneSeed 2 - q 2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc
    4 * π * |exactRescaledOrientedNearOneSeed 2 - q 2| ≤ 4 * 4 * 1 := by
      gcongr
      exact Real.pi_lt_four.le
    _ = 16 := by norm_num

def frozenEndpointQuadraticMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (C (frozenEndpointQuadratic q)) :=
  boundedC (frozenEndpointQuadratic q) 16 (by norm_num)
    (frozenEndpointQuadratic_abs_le q hq)

/-- Coefficientwise certificate for the entire cleared frozen-path error. -/
def errorMajorant (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    PolynomialMajorant (frozenPathClearedError q) :=
  ((frozenPathCommonNumeratorMajorant q hq).sub
    (((frozenPathCommonDenominatorMajorant q hq).mul
      (PolynomialMajorant.X.pow 2)).mul
      (frozenEndpointQuadraticMajorant q hq))).reindex (by
        simp [frozenPathClearedError])

/-- Coefficientwise certificate for the cubic quotient of the cleared error. -/
def frozenPathClearedErrorQuotientMajorant (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    PolynomialMajorant ((frozenPathClearedError q).divX.divX.divX) :=
  (errorMajorant q hq).divX.divX.divX


end FrozenPolynomial

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
