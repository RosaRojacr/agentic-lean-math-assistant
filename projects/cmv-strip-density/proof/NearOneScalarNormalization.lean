/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import LeanSuffixAnalytic
import NearOneAnalyticSystem

/-!
# Source-native scalar normalization near density one

This module records exact cancellation-preserving normalizations for the scalar
CMV type-(iii)/type-(iv) equations after `lam = 1 + t^3` and
`x = 1 - t^2 c`.  It contains no interval or numerical assumptions.
-/

namespace NearOneScalarNormalization

open Real Set

noncomputable section

/-- The prescribed density parameter. -/
def lam (t : ℝ) : ℝ := 1 + t ^ 3

/-- A source curvature written in a cusp-scaled coefficient. -/
def xCoord (t c : ℝ) : ℝ := 1 - t ^ 2 * c

/-- The two pole-free radical radicands. -/
def uInner (t c : ℝ) : ℝ := 2 * c - t ^ 2 * c ^ 2

def vInner (t c : ℝ) : ℝ := 2 * c + 2 * t - t ^ 2 * c ^ 2 + t ^ 4

/-- The two positive pole-free radicals. -/
def U (t c : ℝ) : ℝ := sqrt (uInner t c)

def V (t c : ℝ) : ℝ := sqrt (vInner t c)

/-- Normalized reciprocal-radical difference. -/
def K (t c : ℝ) : ℝ :=
  xCoord t c ^ 2 * (2 + t ^ 3) /
    (U t c * V t c * (V t c + lam t * U t c))

/-- Normalized radial displacement. -/
def D (t c : ℝ) : ℝ :=
  xCoord t c ^ 2 * (2 + t ^ 3) /
    (lam t * (V t c + lam t * U t c))

/-- Rationalized principal arctangent increment. -/
def rho (t c : ℝ) : ℝ :=
  xCoord t c * (2 + t ^ 3) /
    ((U t c + V t c) *
      (xCoord t c ^ 2 + t ^ 2 * U t c * V t c))

/-- Pole-free normalized source angle increment. -/
def H (t c : ℝ) : ℝ :=
  t ^ 2 * (V t c / xCoord t c) *
      NearOneAnalyticSystem.atanQuotient (t * V t c / xCoord t c) +
    rho t c * NearOneAnalyticSystem.atanQuotient (t ^ 2 * rho t c)

/-- The actual source angle block at `xCoord t c`. -/
def sourceAngle (t c : ℝ) : ℝ :=
  lam t * arccos (xCoord t c / lam t) + arcsin (xCoord t c)

/-- Type-(iv) and type-(iii) source heights.  The type-(iii) shape is
`xCoord t (2*b)`. -/
def hFour (t a : ℝ) : ℝ := xCoord t a

def hThree (t b : ℝ) : ℝ := xCoord t b

/-- Cancellation-preserving fold residual. -/
def F (t a : ℝ) : ℝ :=
  hFour t a * K t a - π / 2 - t ^ 2 * H t a

/-- Cancellation-preserving equal-area residual. -/
def E (t a b : ℝ) : ℝ :=
  π * (b - a) * (hFour t a + hThree t b) +
    hFour t a ^ 2 *
      (H t (2 * b) + (2 * hThree t b + 1) * D t (2 * b)) -
    2 * hThree t b ^ 2 * (H t a + hFour t a * D t a)

/-- Cancellation-preserving reduced-fold-gap residual. -/
def J (t a b : ℝ) : ℝ :=
  (a - b) * K t a + hThree t b * D t a - hFour t a * D t (2 * b)

/-- Exact first radical factorization. -/
theorem one_sub_xCoord_sq (t c : ℝ) :
    1 - xCoord t c ^ 2 = t ^ 2 * uInner t c := by
  unfold xCoord uInner
  ring

/-- Exact second radical factorization. -/
theorem lam_sq_sub_xCoord_sq (t c : ℝ) :
    lam t ^ 2 - xCoord t c ^ 2 = t ^ 2 * vInner t c := by
  unfold lam xCoord vInner
  ring

/-- Rationalization identity shared by all three residuals. -/
theorem vInner_sub_lam_sq_mul_uInner (t c : ℝ) :
    vInner t c - lam t ^ 2 * uInner t c =
      t * (2 + t ^ 3) * xCoord t c ^ 2 := by
  unfold lam xCoord uInner vInner
  ring

/-- Difference of the two unscaled radical squares. -/
theorem vInner_sub_uInner (t c : ℝ) :
    vInner t c - uInner t c = t * (2 + t ^ 3) := by
  unfold uInner vInner
  ring

private theorem lam_pos {t : ℝ} (ht : 0 < t) : 0 < lam t := by
  unfold lam
  nlinarith [pow_pos ht 3]

private theorem uInner_pos {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) : 0 < uInner t c := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hplus : 0 < 1 + xCoord t c :=
    add_pos_of_pos_of_nonneg (show 0 < (1 : ℝ) by norm_num) hx.1.le
  have hrad : 0 < 1 - xCoord t c ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) hplus]
  rw [one_sub_xCoord_sq] at hrad
  by_contra hu
  have hu' : uInner t c ≤ 0 := le_of_not_gt hu
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ht2.le hu')) hrad

private theorem vInner_pos {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) : 0 < vInner t c := by
  have hl : 1 < lam t := by
    unfold lam
    nlinarith [pow_pos ht 3]
  have hrad : 0 < lam t ^ 2 - xCoord t c ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr (hx.2.trans hl))
      (by linarith [hx.1, hl] : 0 < lam t + xCoord t c)]
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  rw [lam_sq_sub_xCoord_sq] at hrad
  by_contra hv
  have hv' : vInner t c ≤ 0 := le_of_not_gt hv
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ht2.le hv')) hrad

/-- All source denominators in `K`, `D`, `rho`, and `H` are strictly positive
on the regular cusp-scaled domain. -/
theorem source_guards {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    1 < lam t ∧ 0 < U t c ∧ 0 < V t c ∧
      0 < V t c + lam t * U t c ∧
      0 < U t c + V t c ∧
      0 < xCoord t c ^ 2 + t ^ 2 * U t c * V t c := by
  have hl : 1 < lam t := by
    unfold lam
    nlinarith [pow_pos ht 3]
  have hu : 0 < U t c := Real.sqrt_pos.2 (uInner_pos ht hx)
  have hv : 0 < V t c := Real.sqrt_pos.2 (vInner_pos ht hx)
  refine ⟨hl, hu, hv, ?_, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg hv (mul_nonneg (lam_pos ht).le hu.le)
  · exact add_pos hu hv
  · exact add_pos (sq_pos_of_pos hx.1)
      (mul_pos (mul_pos (sq_pos_of_pos ht) hu) hv)

/-- The first source radical is exactly `t*U`. -/
theorem sqrt_one_sub_xCoord_sq {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    sqrt (1 - xCoord t c ^ 2) = t * U t c := by
  have hplus : 0 < 1 + xCoord t c :=
    add_pos_of_pos_of_nonneg (show 0 < (1 : ℝ) by norm_num) hx.1.le
  have hrad : 0 ≤ 1 - xCoord t c ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) hplus]
  apply (Real.sqrt_eq_iff_eq_sq hrad
    (mul_nonneg ht.le (Real.sqrt_nonneg _))).2
  have huSq : U t c ^ 2 = uInner t c :=
    Real.sq_sqrt (uInner_pos ht hx).le
  calc
    1 - xCoord t c ^ 2 = t ^ 2 * uInner t c := one_sub_xCoord_sq t c
    _ = t ^ 2 * U t c ^ 2 := by rw [huSq]
    _ = (t * U t c) ^ 2 := by ring

/-- The second source radical is exactly `t*V`. -/
theorem sqrt_lam_sq_sub_xCoord_sq {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    sqrt (lam t ^ 2 - xCoord t c ^ 2) = t * V t c := by
  have hl := lam_pos ht
  have hlone : 1 < lam t := by
    unfold lam
    nlinarith [pow_pos ht 3]
  have hrad : 0 ≤ lam t ^ 2 - xCoord t c ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr (hx.2.trans hlone))
      (by linarith [hx.1, hl] : 0 < lam t + xCoord t c)]
  apply (Real.sqrt_eq_iff_eq_sq hrad
    (mul_nonneg ht.le (Real.sqrt_nonneg _))).2
  have hvSq : V t c ^ 2 = vInner t c :=
    Real.sq_sqrt (vInner_pos ht hx).le
  calc
    lam t ^ 2 - xCoord t c ^ 2 =
        t ^ 2 * vInner t c := lam_sq_sub_xCoord_sq t c
    _ = t ^ 2 * V t c ^ 2 := by rw [hvSq]
    _ = (t * V t c) ^ 2 := by ring

/-- The radical in `arccos (x/lam)` is the corresponding scaled `V`. -/
private theorem sqrt_one_sub_xCoord_div_lam_sq {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    sqrt (1 - (xCoord t c / lam t) ^ 2) = t * V t c / lam t := by
  have hl := lam_pos ht
  have hratio : 0 < xCoord t c / lam t := div_pos hx.1 hl
  have hratio1 : xCoord t c / lam t < 1 :=
    (div_lt_one hl).2 (hx.2.trans (by
      unfold lam
      nlinarith [pow_pos ht 3]))
  apply (Real.sqrt_eq_iff_eq_sq (by nlinarith)
    (div_nonneg (mul_nonneg ht.le (Real.sqrt_nonneg _)) hl.le)).2
  have hv : V t c ^ 2 = vInner t c := by
    exact Real.sq_sqrt (vInner_pos ht hx).le
  have hfactor := lam_sq_sub_xCoord_sq t c
  change 1 - (xCoord t c / lam t) ^ 2 =
    (t * V t c / lam t) ^ 2
  field_simp [ne_of_gt hl]
  nlinarith

/-- Rationalization of the reciprocal-radical source difference. -/
theorem reciprocalGap_eq_K {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    1 / sqrt (1 - xCoord t c ^ 2) -
        lam t / sqrt (lam t ^ 2 - xCoord t c ^ 2) = K t c := by
  have g := source_guards ht hx
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hu0 : U t c ≠ 0 := ne_of_gt g.2.1
  have hv0 : V t c ≠ 0 := ne_of_gt g.2.2.1
  have hsum0 : V t c + lam t * U t c ≠ 0 := ne_of_gt g.2.2.2.1
  have hsum0' : V t c + U t c * lam t ≠ 0 := by
    nlinarith [g.2.2.2.1]
  have huSq : U t c ^ 2 = uInner t c :=
    Real.sq_sqrt (uInner_pos ht hx).le
  have hvSq : V t c ^ 2 = vInner t c :=
    Real.sq_sqrt (vInner_pos ht hx).le
  have hrat : (V t c - lam t * U t c) *
      (V t c + lam t * U t c) =
      t * (2 + t ^ 3) * xCoord t c ^ 2 := by
    calc
      (V t c - lam t * U t c) * (V t c + lam t * U t c) =
          V t c ^ 2 - lam t ^ 2 * U t c ^ 2 := by ring
      _ = t * (2 + t ^ 3) * xCoord t c ^ 2 := by
        rw [huSq, hvSq, vInner_sub_lam_sq_mul_uInner]
  rw [sqrt_one_sub_xCoord_sq ht hx, sqrt_lam_sq_sub_xCoord_sq ht hx]
  unfold K
  field_simp [ht0, hu0, hv0, hsum0, hsum0']
  nlinarith

/-- Rationalization of the radial displacement. -/
theorem delta_eq_sq_mul_D {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    sqrt (lam t ^ 2 - xCoord t c ^ 2) / lam t -
        sqrt (1 - xCoord t c ^ 2) = t ^ 2 * D t c := by
  have g := source_guards ht hx
  have hl0 : lam t ≠ 0 := ne_of_gt (lam_pos ht)
  have hsum0 : V t c + lam t * U t c ≠ 0 := ne_of_gt g.2.2.2.1
  have huSq : U t c ^ 2 = uInner t c :=
    Real.sq_sqrt (uInner_pos ht hx).le
  have hvSq : V t c ^ 2 = vInner t c :=
    Real.sq_sqrt (vInner_pos ht hx).le
  have hrat : (V t c - lam t * U t c) *
      (V t c + lam t * U t c) =
      t * (2 + t ^ 3) * xCoord t c ^ 2 := by
    calc
      (V t c - lam t * U t c) * (V t c + lam t * U t c) =
          V t c ^ 2 - lam t ^ 2 * U t c ^ 2 := by ring
      _ = t * (2 + t ^ 3) * xCoord t c ^ 2 := by
        rw [huSq, hvSq, vInner_sub_lam_sq_mul_uInner]
  rw [sqrt_one_sub_xCoord_sq ht hx, sqrt_lam_sq_sub_xCoord_sq ht hx]
  unfold D
  field_simp [hl0, hsum0]
  nlinarith

/-- Principal arctangent subtraction for nonnegative tangent coordinates. -/
private theorem arctan_sub_eq {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    arctan A - arctan B = arctan ((A - B) / (1 + A * B)) := by
  have hden : 0 < 1 + A * B := by positivity
  let r := (A - B) / (1 + A * B)
  have hrden : r * (1 + A * B) = A - B := by
    dsimp [r]
    field_simp [ne_of_gt hden]
  have hremain : 0 < 1 - B * r := by
    have hid : 1 - B * r = (1 + B ^ 2) / (1 + A * B) := by
      apply (eq_div_iff (ne_of_gt hden)).2
      nlinarith [hrden]
    rw [hid]
    positivity
  have hquot : (B + r) / (1 - B * r) = A := by
    apply (div_eq_iff (ne_of_gt hremain)).2
    nlinarith [hrden]
  have hadd := Real.arctan_add (x := B) (y := r) (sub_pos.mp hremain)
  rw [hquot] at hadd
  change arctan A - arctan B = arctan r
  linarith

/-- Exact rationalization of the source angle increment's arctangent
subtraction argument. -/
private theorem angleIncrementArgument_eq {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    ((t * V t c / xCoord t c) - (t * U t c / xCoord t c)) /
        (1 + (t * V t c / xCoord t c) * (t * U t c / xCoord t c)) =
      t ^ 2 * rho t c := by
  have g := source_guards ht hx
  have hx0 : xCoord t c ≠ 0 := ne_of_gt hx.1
  have hsum0 : U t c + V t c ≠ 0 := ne_of_gt g.2.2.2.2.1
  have hquad0 : xCoord t c ^ 2 + t ^ 2 * U t c * V t c ≠ 0 :=
    ne_of_gt g.2.2.2.2.2
  have hquad0' : xCoord t c ^ 2 + t ^ 2 * V t c * U t c ≠ 0 := by
    nlinarith [g.2.2.2.2.2]
  have huSq : U t c ^ 2 = uInner t c :=
    Real.sq_sqrt (uInner_pos ht hx).le
  have hvSq : V t c ^ 2 = vInner t c :=
    Real.sq_sqrt (vInner_pos ht hx).le
  have hdiff : (V t c - U t c) * (U t c + V t c) =
      t * (2 + t ^ 3) := by
    calc
      (V t c - U t c) * (U t c + V t c) =
          V t c ^ 2 - U t c ^ 2 := by ring
      _ = t * (2 + t ^ 3) := by
        rw [huSq, hvSq, vInner_sub_uInner]
  unfold rho
  field_simp [hx0, hsum0, hquad0, hquad0']
  nlinarith

/-- Exact pole-free normalization of the complete principal source angle. -/
theorem sourceAngle_eq_halfPi_add_sq_mul_H {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    sourceAngle t c = π / 2 + t ^ 2 * H t c := by
  have hl := lam_pos ht
  have g := source_guards ht hx
  let A := t * V t c / xCoord t c
  let B := t * U t c / xCoord t c
  have hA : 0 ≤ A := by
    exact div_nonneg (mul_nonneg ht.le g.2.2.1.le) hx.1.le
  have hB : 0 ≤ B := by
    exact div_nonneg (mul_nonneg ht.le g.2.1.le) hx.1.le
  have hratio : (t * V t c / lam t) / (xCoord t c / lam t) = A := by
    dsimp [A]
    field_simp [ne_of_gt hl, ne_of_gt hx.1]
  have hsub : arctan A - arctan B = arctan (t ^ 2 * rho t c) := by
    rw [arctan_sub_eq hA hB, angleIncrementArgument_eq ht hx]
  unfold sourceAngle
  rw [Real.arcsin_eq_pi_div_two_sub_arccos,
    Real.arccos_eq_arctan (div_pos hx.1 hl),
    sqrt_one_sub_xCoord_div_lam_sq ht hx, hratio,
    Real.arccos_eq_arctan hx.1,
    sqrt_one_sub_xCoord_sq ht hx]
  change lam t * arctan A + (π / 2 - arctan B) = π / 2 + t ^ 2 * H t c
  calc
    lam t * arctan A + (π / 2 - arctan B) =
        π / 2 + (arctan A - arctan B) + t ^ 3 * arctan A := by
      unfold lam
      ring
    _ = π / 2 + arctan (t ^ 2 * rho t c) + t ^ 3 * arctan A := by
      rw [hsub]
    _ = π / 2 + t ^ 2 * H t c := by
      rw [← NearOneAnalyticSystem.mul_atanQuotient A,
        ← NearOneAnalyticSystem.mul_atanQuotient (t ^ 2 * rho t c)]
      unfold H
      dsimp [A]
      ring

/-- The normalized radial displacement is the actual type-(iv) displacement. -/
theorem typeFourDelta_eq_sq_mul_D {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    LeanSuffixAnalytic.typeFourDelta (lam t) (xCoord t c) = t ^ 2 * D t c := by
  exact delta_eq_sq_mul_D ht hx

/-- The normalized source angle is the actual type-(iv) angle. -/
theorem typeFourAngle_eq_halfPi_add_sq_mul_H {t c : ℝ} (ht : 0 < t)
    (hx : xCoord t c ∈ Ioo (0 : ℝ) 1) :
    LeanSuffixAnalytic.typeFourAngle (lam t) (xCoord t c) =
      π / 2 + t ^ 2 * H t c := by
  exact sourceAngle_eq_halfPi_add_sq_mul_H ht hx

/-- Exact source identity for the normalized type-(iv) fold residual. -/
theorem typeFourFold_eq_four_mul_F {t a : ℝ} (ht : 0 < t)
    (ha : hFour t a ∈ Ioo (0 : ℝ) 1) :
    LeanSuffixAnalytic.typeFourFold (lam t) (hFour t a) = 4 * F t a := by
  have hrec := reciprocalGap_eq_K ht ha
  have hang := typeFourAngle_eq_halfPi_add_sq_mul_H ht ha
  unfold LeanSuffixAnalytic.typeFourFold F hFour at *
  rw [hrec, hang]
  ring

/-- Exact source identity for the normalized equal-area residual. -/
theorem scaled_areaDifference_eq_sq_mul_E {t a b : ℝ} (ht : 0 < t)
    (ha : hFour t a ∈ Ioo (0 : ℝ) 1)
    (hb : xCoord t (2 * b) ∈ Ioo (0 : ℝ) 1) :
    hThree t b ^ 2 * hFour t a ^ 2 *
        (LeanSuffixAnalytic.typeThreeArea (lam t) (hThree t b) -
          LeanSuffixAnalytic.typeFourArea (lam t) (hFour t a)) =
      t ^ 2 * E t a b := by
  have hshape : LeanSuffixAnalytic.typeThreeShape (hThree t b) =
      xCoord t (2 * b) := by
    unfold LeanSuffixAnalytic.typeThreeShape hThree xCoord
    ring
  have hangleFour :
      LeanSuffixAnalytic.typeFourAngle (lam t) (hFour t a) =
        π / 2 + t ^ 2 * H t a := by
    simpa only [hFour] using typeFourAngle_eq_halfPi_add_sq_mul_H ht ha
  have hdeltaFour :
      LeanSuffixAnalytic.typeFourDelta (lam t) (hFour t a) =
        t ^ 2 * D t a := by
    simpa only [hFour] using typeFourDelta_eq_sq_mul_D ht ha
  have hangleThree :
      LeanSuffixAnalytic.typeThreeAngle (lam t) (hThree t b) =
        π / 2 + t ^ 2 * H t (2 * b) := by
    unfold LeanSuffixAnalytic.typeThreeAngle
    rw [hshape]
    exact sourceAngle_eq_halfPi_add_sq_mul_H ht hb
  have hdeltaThree :
      LeanSuffixAnalytic.typeThreeDelta (lam t) (hThree t b) =
        t ^ 2 * D t (2 * b) := by
    unfold LeanSuffixAnalytic.typeThreeDelta
    rw [hshape]
    exact delta_eq_sq_mul_D ht hb
  have hhThree : hThree t b ≠ 0 := by
    apply ne_of_gt
    unfold hThree xCoord at *
    nlinarith [hb.1]
  have hhFour : hFour t a ≠ 0 := ne_of_gt ha.1
  unfold LeanSuffixAnalytic.typeThreeArea LeanSuffixAnalytic.typeFourArea
  rw [hangleThree, hdeltaThree, hangleFour, hdeltaFour]
  rw [hshape]
  unfold E
  field_simp [hhThree, hhFour]
  unfold hFour hThree xCoord at *
  ring

/-- Exact source identity for the normalized reduced fold gap. -/
theorem hFour_mul_reducedFoldGap_eq_sq_mul_J {t a b : ℝ} (ht : 0 < t)
    (ha : hFour t a ∈ Ioo (0 : ℝ) 1)
    (hb : xCoord t (2 * b) ∈ Ioo (0 : ℝ) 1) :
    hFour t a * LeanSuffixAnalytic.reducedFoldGap
        (lam t) (hThree t b) (hFour t a) = t ^ 2 * J t a b := by
  have hshape : LeanSuffixAnalytic.typeThreeShape (hThree t b) =
      xCoord t (2 * b) := by
    unfold LeanSuffixAnalytic.typeThreeShape hThree xCoord
    ring
  have hrec :
      1 / sqrt (1 - hFour t a ^ 2) -
          lam t / sqrt (lam t ^ 2 - hFour t a ^ 2) = K t a := by
    simpa only [hFour] using reciprocalGap_eq_K ht ha
  have hdeltaFour :
      LeanSuffixAnalytic.typeFourDelta (lam t) (hFour t a) =
        t ^ 2 * D t a := by
    simpa only [hFour] using typeFourDelta_eq_sq_mul_D ht ha
  have hdeltaThree :
      LeanSuffixAnalytic.typeThreeDelta (lam t) (hThree t b) =
        t ^ 2 * D t (2 * b) := by
    unfold LeanSuffixAnalytic.typeThreeDelta
    rw [hshape]
    exact delta_eq_sq_mul_D ht hb
  have hhFour : hFour t a ≠ 0 := ne_of_gt ha.1
  unfold LeanSuffixAnalytic.reducedFoldGap
  rw [hrec, hdeltaFour, hdeltaThree]
  unfold J hFour hThree xCoord at *
  field_simp [hhFour]
  ring

end

end NearOneScalarNormalization
