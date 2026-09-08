/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneRescaledFirstCell
import LeanSuffixAnalytic

/-!
# Source-equation bridge for the first near-one cell

This module proves that every point in the validated positive endpoint box has
strictly ordered principal tangent-half-angle coordinates and incidence density
in `1 < lambda < 51/50`. These bounds supply the principal-chart guards used to
transport the simultaneous zero from `NearOneRescaledFirstCell` to the three
original source residuals.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell
private theorem cos_halfAngle (x : ℝ) :
    Real.cos (halfAngle x) = halfCos x := by
  rw [halfAngle, halfCos, Real.cos_two_mul, Real.cos_arctan]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [div_pow, one_pow, Real.sq_sqrt hpos.le]
  field_simp [ne_of_gt hpos]
  ring

private theorem sin_halfAngle (x : ℝ) :
    Real.sin (halfAngle x) = halfSin x := by
  rw [halfAngle, halfSin, Real.sin_two_mul, Real.sin_arctan,
    Real.cos_arctan]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  field_simp [ne_of_gt (Real.sqrt_pos.2 hpos), Real.sq_sqrt hpos.le]
  rw [Real.sq_sqrt hpos.le]

private theorem halfAngle_pos {x : ℝ} (hx : 0 < x) :
    0 < halfAngle x := by
  unfold halfAngle
  exact mul_pos (by norm_num) (Real.arctan_pos.2 hx)

private theorem halfAngle_lt_pi (x : ℝ) :
    halfAngle x < π := by
  unfold halfAngle
  nlinarith [Real.arctan_lt_pi_div_two x]

private theorem halfCos_pos {x : ℝ} (hx : x < 1) (hx0 : 0 ≤ x) :
    0 < halfCos x := by
  unfold halfCos
  exact div_pos (by nlinarith) (by positivity)

private theorem halfCos_lt_one {x : ℝ} (hx : 0 < x) :
    halfCos x < 1 := by
  unfold halfCos
  rw [div_lt_iff₀ (by positivity : 0 < 1 + x ^ 2)]
  nlinarith [sq_pos_of_pos hx]


/-- Source residuals on the positive principal tangent-half-angle chart define
the scalar stationary equal-area pair used by the suffix reduction. -/
noncomputable def sourceResiduals_stationaryEqualAreaPair
    {s z a b : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hy0 : 0 < yCoord s z) (hy1 : yCoord s z < 1)
    (hw0 : 0 < wCoord s a) (hw1 : wCoord s a < 1)
    (hv0 : 0 < vCoord s z a b)
    (hlam : 1 < density s z)
    (hfold : sourceFoldResidual s z π = 0)
    (hcosine : sourceCosineResidual s z a b = 0)
    (harea : sourceAreaResidual s z a b π = 0) :
    LeanSuffixAnalytic.StationaryEqualAreaPair (density s z) := by
  have hlamPos : 0 < density s z := lt_trans (by norm_num) hlam
  have hsAngle0 : 0 < halfAngle s := halfAngle_pos hs0
  have hsAnglePi : halfAngle s < π := halfAngle_lt_pi s
  have hyAngle0 : 0 < halfAngle (yCoord s z) := halfAngle_pos hy0
  have hyAnglePi : halfAngle (yCoord s z) < π :=
    halfAngle_lt_pi (yCoord s z)
  have hwAngle0 : 0 < halfAngle (wCoord s a) := halfAngle_pos hw0
  have hwAnglePi : halfAngle (wCoord s a) < π :=
    halfAngle_lt_pi (wCoord s a)
  have hvAngle0 : 0 < halfAngle (vCoord s z a b) := halfAngle_pos hv0
  have hvAnglePi : halfAngle (vCoord s z a b) < π :=
    halfAngle_lt_pi (vCoord s z a b)
  have hcosSPos : 0 < halfCos s := halfCos_pos hs1 hs0.le
  have hcosSLt : halfCos s < 1 := halfCos_lt_one hs0
  have hcosYPos : 0 < halfCos (yCoord s z) :=
    halfCos_pos hy1 hy0.le
  have hcosWPos : 0 < halfCos (wCoord s a) :=
    halfCos_pos hw1 hw0.le
  have hcosWLt : halfCos (wCoord s a) < 1 := halfCos_lt_one hw0
  have hcosXY :
      halfCos s = density s z * halfCos (yCoord s z) := by
    rw [density]
    field_simp [ne_of_gt hcosYPos]
  have hcosWV :
      halfCos (wCoord s a) =
        density s z * halfCos (vCoord s z a b) := by
    unfold sourceCosineResidual at hcosine
    rw [hcosXY] at hcosine
    nlinarith
  have hshape :
      LeanSuffixAnalytic.typeThreeShape
          ((1 + halfCos (wCoord s a)) / 2) =
        halfCos (wCoord s a) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  have hcosXYDiv :
      halfCos s / density s z = halfCos (yCoord s z) := by
    rw [hcosXY]
    field_simp [ne_of_gt hlamPos]
  have hcosWVDiv :
      halfCos (wCoord s a) / density s z =
        halfCos (vCoord s z a b) := by
    rw [hcosWV]
    field_simp [ne_of_gt hlamPos]
  have hB4 :
      LeanSuffixAnalytic.typeFourAngle (density s z) (halfCos s) =
        sourceTypeFourAngleBlock s z π := by
    rw [LeanSuffixAnalytic.typeFourAngle_eq_checker, hcosXYDiv,
      ← cos_halfAngle (yCoord s z),
      Real.arccos_cos hyAngle0.le hyAnglePi.le,
      ← cos_halfAngle s, Real.arccos_cos hsAngle0.le hsAnglePi.le]
    rfl
  have hB3 :
      LeanSuffixAnalytic.typeThreeAngle (density s z)
          ((1 + halfCos (wCoord s a)) / 2) + π / 2 =
        sourceTypeThreeAngleBlock s z a b π := by
    rw [LeanSuffixAnalytic.typeThreeAngle_add_halfPi, hshape, hcosWVDiv,
      ← cos_halfAngle (vCoord s z a b),
      Real.arccos_cos hvAngle0.le hvAnglePi.le,
      ← cos_halfAngle (wCoord s a),
      Real.arccos_cos hwAngle0.le hwAnglePi.le]
    rfl
  have hsinSPos : 0 < halfSin s := by
    rw [← sin_halfAngle s]
    exact Real.sin_pos_of_pos_of_lt_pi hsAngle0 hsAnglePi
  have hsinYPos : 0 < halfSin (yCoord s z) := by
    rw [← sin_halfAngle (yCoord s z)]
    exact Real.sin_pos_of_pos_of_lt_pi hyAngle0 hyAnglePi
  have hsinWPos : 0 < halfSin (wCoord s a) := by
    rw [← sin_halfAngle (wCoord s a)]
    exact Real.sin_pos_of_pos_of_lt_pi hwAngle0 hwAnglePi
  have hsinVPos : 0 < halfSin (vCoord s z a b) := by
    rw [← sin_halfAngle (vCoord s z a b)]
    exact Real.sin_pos_of_pos_of_lt_pi hvAngle0 hvAnglePi
  have hsqrtS :
      sqrt (1 - halfCos s ^ 2) = halfSin s := by
    rw [← cos_halfAngle s, ← sin_halfAngle s]
    have htrig := Real.sin_sq_add_cos_sq (halfAngle s)
    rw [show 1 - cos (halfAngle s) ^ 2 =
        sin (halfAngle s) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hsAngle0 hsAnglePi)]
  have hsqrtW :
      sqrt (1 - halfCos (wCoord s a) ^ 2) =
        halfSin (wCoord s a) := by
    rw [← cos_halfAngle (wCoord s a), ← sin_halfAngle (wCoord s a)]
    have htrig := Real.sin_sq_add_cos_sq (halfAngle (wCoord s a))
    rw [show 1 - cos (halfAngle (wCoord s a)) ^ 2 =
        sin (halfAngle (wCoord s a)) ^ 2 by linarith,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hwAngle0 hwAnglePi)]
  have hsqrtLamS :
      sqrt (density s z ^ 2 - halfCos s ^ 2) =
        density s z * halfSin (yCoord s z) := by
    have htrig := Real.sin_sq_add_cos_sq (halfAngle (yCoord s z))
    rw [show density s z ^ 2 - halfCos s ^ 2 =
        (density s z * halfSin (yCoord s z)) ^ 2 by
      rw [hcosXY, ← cos_halfAngle (yCoord s z),
        ← sin_halfAngle (yCoord s z)]
      linear_combination -(density s z) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos hlamPos hsinYPos)]
  have hsqrtLamW :
      sqrt (density s z ^ 2 - halfCos (wCoord s a) ^ 2) =
        density s z * halfSin (vCoord s z a b) := by
    have htrig := Real.sin_sq_add_cos_sq (halfAngle (vCoord s z a b))
    rw [show density s z ^ 2 - halfCos (wCoord s a) ^ 2 =
        (density s z * halfSin (vCoord s z a b)) ^ 2 by
      rw [hcosWV, ← cos_halfAngle (vCoord s z a b),
        ← sin_halfAngle (vCoord s z a b)]
      linear_combination -(density s z) ^ 2 * htrig,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos hlamPos hsinVPos)]
  have hD4 :
      LeanSuffixAnalytic.typeFourDelta (density s z) (halfCos s) =
        halfSin (yCoord s z) - halfSin s := by
    rw [LeanSuffixAnalytic.typeFourDelta, hsqrtLamS, hsqrtS]
    field_simp [ne_of_gt hlamPos]
  have hD3 :
      LeanSuffixAnalytic.typeThreeDelta (density s z)
          ((1 + halfCos (wCoord s a)) / 2) =
        halfSin (vCoord s z a b) - halfSin (wCoord s a) := by
    rw [LeanSuffixAnalytic.typeThreeDelta, hshape, hsqrtLamW, hsqrtW]
    field_simp [ne_of_gt hlamPos]
  have hh3Pos : 0 < (1 + halfCos (wCoord s a)) / 2 := by linarith
  have hareaSemantic :
      LeanSuffixAnalytic.typeThreeArea (density s z)
          ((1 + halfCos (wCoord s a)) / 2) =
        LeanSuffixAnalytic.typeFourArea (density s z) (halfCos s) := by
    rw [LeanSuffixAnalytic.typeThreeArea, LeanSuffixAnalytic.typeFourArea,
      hshape, hB3, hD3, hB4, hD4]
    apply (div_eq_div_iff (pow_ne_zero 2 (ne_of_gt hh3Pos))
      (pow_ne_zero 2 (ne_of_gt hcosSPos))).2
    unfold sourceAreaResidual at harea
    linear_combination (1 / 2 : ℝ) * harea
  have hstationary :
      LeanSuffixAnalytic.typeFourFold (density s z) (halfCos s) = 0 := by
    have hdenNe :
        halfSin s * halfSin (yCoord s z) ≠ 0 :=
      mul_ne_zero (ne_of_gt hsinSPos) (ne_of_gt hsinYPos)
    have hnumerator :
        halfCos s * (halfSin (yCoord s z) - halfSin s) =
          halfSin s * halfSin (yCoord s z) *
            sourceTypeFourAngleBlock s z π := by
      unfold sourceFoldResidual at hfold
      linarith
    have hcore :
        halfCos s * (1 / halfSin s - 1 / halfSin (yCoord s z)) =
          sourceTypeFourAngleBlock s z π := by
      calc
        halfCos s * (1 / halfSin s - 1 / halfSin (yCoord s z)) =
            (halfCos s *
              (halfSin (yCoord s z) - halfSin s)) /
                (halfSin s * halfSin (yCoord s z)) := by
                  field_simp [ne_of_gt hsinSPos, ne_of_gt hsinYPos]
        _ = sourceTypeFourAngleBlock s z π := (div_eq_iff hdenNe).2 (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hnumerator)
    have hcancel :
        density s z / (density s z * halfSin (yCoord s z)) =
          1 / halfSin (yCoord s z) := by
      field_simp [ne_of_gt hlamPos, ne_of_gt hsinYPos]
    rw [LeanSuffixAnalytic.typeFourFold, hsqrtS, hsqrtLamS, hB4,
      hcancel, hcore]
    ring
  exact
    { h₃ := (1 + halfCos (wCoord s a)) / 2
      h₄ := halfCos s
      h₃_gt_half := by linarith
      h₃_lt_one := by linarith
      h₄_pos := hcosSPos
      h₄_lt_one := hcosSLt
      equalArea := hareaSemantic
      stationary := hstationary }

/-- The physical `(z,a,b)` point represented by a quadratically rescaled
endpoint-box coordinate. -/
def endpointPhysicalPoint (s : ℝ) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  tangentCenteredPoint s (fun j => s ^ 2 * q j)

set_option maxHeartbeats 0 in
-- The exact box arithmetic exceeds the default deterministic elaboration budget.
/-- Every positive endpoint-box slice below `1/100` gives strictly ordered
principal half-angle coordinates for both profiles and a density in the
remaining open near-one range. -/
theorem endpointBox_coordinate_bounds {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    let x := endpointPhysicalPoint s q
    (0 < s ∧ s < yCoord s (x 0) ∧ yCoord s (x 0) < 1) ∧
      (0 < wCoord s (x 1) ∧
        wCoord s (x 1) < vCoord s (x 0) (x 1) (x 2) ∧
        vCoord s (x 0) (x 1) (x 2) < 1) ∧
      (1 < density s (x 0) ∧ density s (x 0) < (51 / 50 : ℝ)) := by
  let z := endpointPhysicalPoint s q 0
  let a := endpointPhysicalPoint s q 1
  let b := endpointPhysicalPoint s q 2
  have hq0 := hq (0 : Fin 3)
  have hq1 := hq (1 : Fin 3)
  have hq2 := hq (2 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at hq2
  have hq1pos' : 0 < q 1 := by linarith [hq1.1]
  have hq0pos : 0 ≤ q 0 := by linarith [hq0.1]
  have hq1pos : 0 ≤ q 1 := by linarith [hq1.1]
  have hs2 : s ^ 2 < (1 / 100 : ℝ) ^ 2 := by nlinarith
  have hp2 : π ^ 2 < (4 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ Real.pi_lt_four Real.pi_pos.le (by norm_num)
  have hp2' : π ^ 2 < (16 : ℝ) := by
    norm_num at hp2 ⊢
    exact hp2
  have hzEq : z = π + s * π ^ 2 + s ^ 2 * q 0 := by
    simp [z, endpointPhysicalPoint, tangentCenteredPoint, exactCuspPoint,
      exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  have hzpos : 0 < z := by
    rw [hzEq]
    positivity
  have hsPi2 : s * π ^ 2 < (1 / 100 : ℝ) * 16 :=
    mul_lt_mul hs hp2'.le (sq_pos_of_pos Real.pi_pos) (by norm_num)
  have hq0pos' : 0 < q 0 := by linarith [hq0.1]
  have hs2q0 : s ^ 2 * q 0 < (1 / 100 : ℝ) ^ 2 * 54 :=
    mul_lt_mul hs2 hq0.2 hq0pos' (by norm_num)
  have hzHi : z < (10 / 3 : ℝ) := by
    rw [hzEq]
    have hpihi := Real.pi_lt_d20
    norm_num at hsPi2 hs2q0 hpihi ⊢
    nlinarith
  have haEq : a = 5 * π / 12 +
      s * ((43 * π ^ 2 + 1056) / 144) +
      s ^ 2 * (5 * q 0 / 12 + q 1) := by
    simp [a, endpointPhysicalPoint, tangentCenteredPoint, exactCuspPoint,
      exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
    ring
  have haLo : (5 / 4 : ℝ) < a := by
    rw [haEq]
    have hrest0 : 0 ≤ s * ((43 * π ^ 2 + 1056) / 144) := by positivity
    have hlast0 : 0 ≤ s ^ 2 * (5 * q 0 / 12 + q 1) := by positivity
    nlinarith [Real.pi_gt_three]
  have ha0 : 0 < a := lt_trans (by norm_num) haLo
  have hcoefA : (43 * π ^ 2 + 1056) / 144 < (13 : ℝ) := by
    nlinarith [hp2']
  have hcoefA0 : 0 < (43 * π ^ 2 + 1056) / 144 := by positivity
  have hsCoefA : s * ((43 * π ^ 2 + 1056) / 144) < (13 / 100 : ℝ) := by
    have h := mul_lt_mul hs hcoefA.le hcoefA0 (by norm_num)
    norm_num at h ⊢
    exact h
  have hqA : 5 * q 0 / 12 + q 1 ≤ (51 : ℝ) := by
    nlinarith [hq0.2, hq1.2]
  have hqA0 : 0 < 5 * q 0 / 12 + q 1 := by nlinarith [hq0.1, hq1.1]
  have hs2qA : s ^ 2 * (5 * q 0 / 12 + q 1) < (51 / 10000 : ℝ) := by
    have h := mul_lt_mul hs2 hqA hqA0 (by norm_num)
    norm_num at h ⊢
    exact h
  have haHi : a < 2 := by
    rw [haEq]
    nlinarith [Real.pi_lt_four]
  let T : ℝ := π * (295 * π ^ 2 - 14256) / 216
  let C0 : ℝ := (109 * π ^ 2 - 5376) / (72 * π)
  let C1 : ℝ := (2880 - 7 * π ^ 2) / (6 * π)
  have hTlo : (-200 : ℝ) < T := by
    have hp3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
      pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
    have hpihi := Real.pi_lt_d20
    dsimp only [T]
    rw [show π * (295 * π ^ 2 - 14256) / 216 =
      (295 * π ^ 3 - 14256 * π) / 216 by ring]
    norm_num at hp3lo hpihi ⊢
    nlinarith
  have hTneg : T < 0 := by
    dsimp only [T]
    have hinner : 295 * π ^ 2 - 14256 < 0 := by
      norm_num at hp2 ⊢
      nlinarith
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos hinner)
      (by norm_num)
  have hC0lo : (-25 : ℝ) < C0 := by
    dsimp only [C0]
    rw [lt_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    have hp2lo : (3 : ℝ) ^ 2 < π ^ 2 :=
      pow_lt_pow_left₀ (by nlinarith [Real.pi_gt_three])
        (by norm_num) (by norm_num)
    nlinarith [Real.pi_gt_three]
  have hC0neg : C0 < 0 := by
    dsimp only [C0]
    exact div_neg_of_neg_of_pos (by nlinarith [hp2])
      (mul_pos (by norm_num) Real.pi_pos)
  have hC1pos : 0 < C1 := by
    dsimp only [C1]
    exact div_pos (by nlinarith [hp2])
      (mul_pos (by norm_num) Real.pi_pos)
  have hC1Hi : C1 < 160 := by
    dsimp only [C1]
    rw [div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_gt_three, sq_nonneg π]
  have hC0q0 : (-1350 : ℝ) < C0 * q 0 := calc
    (-1350 : ℝ) = (-25) * 54 := by norm_num
    _ < C0 * 54 := mul_lt_mul_of_pos_right hC0lo (by norm_num)
    _ ≤ C0 * q 0 := mul_le_mul_of_nonpos_left hq0.2 hC0neg.le
  have hQ : (-5200 : ℝ) < C0 * q 0 + C1 * q 1 + q 2 := by
    have hC1q1 : 0 ≤ C1 * q 1 := mul_nonneg hC1pos.le hq1pos
    linarith [hq2.1]
  have hQHi : C0 * q 0 + C1 * q 1 + q 2 < (1000 : ℝ) := by
    have hC0q0nonpos : C0 * q 0 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC0neg.le hq0pos
    have hC1q1 : C1 * q 1 < 160 * 28 :=
      mul_lt_mul hC1Hi hq1.2 hq1pos' (by norm_num)
    nlinarith [hq2.2]
  have hsT : (-2 : ℝ) < s * T := by
    have h₁ : (-200 : ℝ) * s < T * s :=
      mul_lt_mul_of_pos_right hTlo hs0
    have h₂ : (-2 : ℝ) < (-200) * s := by
      norm_num at hs ⊢
      nlinarith
    nlinarith
  have hs2Q : (-1 : ℝ) <
      s ^ 2 * (C0 * q 0 + C1 * q 1 + q 2) := by
    have h₁ := mul_lt_mul_of_pos_left hQ (sq_pos_of_pos hs0)
    have h₂ : (-1 : ℝ) < (-5200) * s ^ 2 := by
      norm_num at hs2 ⊢
      nlinarith
    nlinarith
  have hs2QHi : s ^ 2 * (C0 * q 0 + C1 * q 1 + q 2) < 1 := by
    by_cases hQsign : 0 ≤ C0 * q 0 + C1 * q 1 + q 2
    · have h := mul_le_mul hs2.le hQHi.le hQsign (by norm_num)
      norm_num at h ⊢
      nlinarith
    · have : s ^ 2 * (C0 * q 0 + C1 * q 1 + q 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg s) (le_of_not_ge hQsign)
      linarith
  have hbEq : b = -44 + 19 * π ^ 2 / 24 + s * T +
      s ^ 2 * (C0 * q 0 + C1 * q 1 + q 2) := by
    simp [b, endpointPhysicalPoint, tangentCenteredPoint, exactCuspPoint,
      exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, T, C0, C1]
    ring
  have hbLo : (-50 : ℝ) < b := by
    rw [hbEq]
    have : 0 < 19 * π ^ 2 / 24 := by positivity
    linarith
  have hbNeg : b < 0 := by
    rw [hbEq]
    nlinarith [hp2']
  have hsbLo : (-1 / 2 : ℝ) < s * b := by
    have h₁ : (-50 : ℝ) * s < b * s :=
      mul_lt_mul_of_pos_right hbLo hs0
    have h₂ : (-1 / 2 : ℝ) < (-50) * s := by
      norm_num at hs ⊢
      nlinarith
    nlinarith
  have hsbNeg : s * b < 0 := mul_neg_of_pos_of_neg hs0 hbNeg
  have hePos : 0 < eCoord s z a b := by
    simp only [eCoord]
    nlinarith
  have heHi : eCoord s z a b < 12 := by
    simp only [eCoord]
    nlinarith
  have hsz : s * z < (1 / 30 : ℝ) := by
    have h := mul_lt_mul hs hzHi.le hzpos (by norm_num)
    norm_num at h ⊢
    exact h
  have hApos : 0 < aCoord s z := by
    simp only [aCoord]
    positivity
  have hAHi : aCoord s z < (31 / 30 : ℝ) := by
    simp only [aCoord]
    linarith
  have hyPos : 0 < yCoord s z := by
    simp only [yCoord]
    positivity
  have hsy : s < yCoord s z := by
    simp only [yCoord, aCoord]
    nlinarith [mul_pos (sq_pos_of_pos hs0) hzpos]
  have hySmall : yCoord s z < (1 / 50 : ℝ) := by
    have h := mul_lt_mul hs hAHi.le hApos (by norm_num)
    simp only [yCoord]
    norm_num at h ⊢
    nlinarith
  have hySqSmall : yCoord s z ^ 2 < (1 / 2500 : ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr hySmall)
      (add_pos (by norm_num : (0 : ℝ) < 1 / 50) hyPos)]
  have hySq : yCoord s z ^ 2 < 1 := lt_trans hySqSmall (by norm_num)
  have hwPos : 0 < wCoord s a := by
    simp only [wCoord]
    exact mul_pos hs0 (by simp only [rCoord]; positivity)
  have hwv : wCoord s a < vCoord s z a b := by
    simp only [wCoord, vCoord]
    nlinarith [mul_pos (sq_pos_of_pos hs0) hePos]
  have hsa : s * a < (1 / 50 : ℝ) := by
    have h := mul_lt_mul hs haHi.le ha0 (by norm_num)
    norm_num at h ⊢
    exact h
  have hse : s * eCoord s z a b < (3 / 25 : ℝ) := by
    have h := mul_lt_mul hs heHi.le hePos (by norm_num)
    norm_num at h ⊢
    exact h
  have hrvPos : 0 < rCoord s a + s * eCoord s z a b := by
    simp only [rCoord]
    positivity
  have hrvHi : rCoord s a + s * eCoord s z a b < 3 := by
    simp only [rCoord]
    linarith
  have hvHi : vCoord s z a b < 1 := by
    have h := mul_lt_mul hs hrvHi.le hrvPos (by norm_num)
    simp only [vCoord]
    norm_num at h ⊢
    linarith
  have hdensityFormula : density s z =
      ((1 - s ^ 2) * (1 + yCoord s z ^ 2)) /
        ((1 + s ^ 2) * (1 - yCoord s z ^ 2)) := by
    unfold density halfCos
    field_simp
  have hdensityDen : 0 < (1 + s ^ 2) * (1 - yCoord s z ^ 2) :=
    mul_pos (by positivity) (sub_pos.mpr hySq)
  have hsSqLtOne : s ^ 2 < 1 := lt_trans hs2 (by norm_num)
  have hsqOrder : s ^ 2 < yCoord s z ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hsy) (add_pos hyPos hs0)]
  have hdensityLo : 1 < density s z := by
    rw [hdensityFormula]
    apply (lt_div_iff₀ hdensityDen).2
    nlinarith
  have hnum :
      (1 - s ^ 2) * (1 + yCoord s z ^ 2) < (2501 / 2500 : ℝ) := by
    have hfac : 1 - s ^ 2 ≤ 1 := by nlinarith [sq_nonneg s]
    have hmul := mul_le_mul_of_nonneg_right hfac
      (by positivity : 0 ≤ 1 + yCoord s z ^ 2)
    nlinarith
  have hdenLo : (2499 / 2500 : ℝ) <
      (1 + s ^ 2) * (1 - yCoord s z ^ 2) := by
    have hfac : 1 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    have hmul := mul_le_mul_of_nonneg_right hfac (sub_pos.mpr hySq).le
    nlinarith
  have hscale : (2501 / 2500 : ℝ) <
      (51 / 50 : ℝ) * (2499 / 2500 : ℝ) := by norm_num
  have hdensityHi : density s z < (51 / 50 : ℝ) := by
    rw [hdensityFormula]
    apply (div_lt_iff₀ hdensityDen).2
    have hdenScaled := mul_lt_mul_of_pos_left hdenLo
      (by norm_num : (0 : ℝ) < 51 / 50)
    linarith
  change (0 < s ∧ s < yCoord s z ∧ yCoord s z < 1) ∧
    (0 < wCoord s a ∧ wCoord s a < vCoord s z a b ∧
      vCoord s z a b < 1) ∧
    (1 < density s z ∧ density s z < (51 / 50 : ℝ))
  exact ⟨⟨hs0, hsy, hySmall.trans (by norm_num)⟩,
    ⟨hwPos, hwv, hvHi⟩, hdensityLo, hdensityHi⟩

set_option maxHeartbeats 0 in
-- The exact box arithmetic exceeds the default deterministic elaboration budget.
/-- The cancellation-free cubic density quotient is strictly above `251 / 20`
and below `14` throughout the positive endpoint box. -/
theorem endpointBox_densityCubeQuotient_bounds {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    251 / 20 < densityCubeQuotient s (endpointPhysicalPoint s q 0) ∧
      densityCubeQuotient s (endpointPhysicalPoint s q 0) < 14 := by
  let z := endpointPhysicalPoint s q 0
  have hq0 := hq (0 : Fin 3)
  change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
  have hq0pos : 0 < q 0 := by linarith [hq0.1]
  have hs2 : s ^ 2 < (1 / 100 : ℝ) ^ 2 := by nlinarith
  have hp2 : π ^ 2 < (4 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ Real.pi_lt_four Real.pi_pos.le (by norm_num)
  have hp2' : π ^ 2 < (16 : ℝ) := by
    norm_num at hp2 ⊢
    exact hp2
  have hzEq : z = π + s * π ^ 2 + s ^ 2 * q 0 := by
    simp [z, endpointPhysicalPoint, tangentCenteredPoint, exactCuspPoint,
      exactCuspTangent, exactCuspShear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three]
  have hzpos : 0 < z := by
    rw [hzEq]
    positivity
  have hzLo : (157 / 50 : ℝ) < z := by
    rw [hzEq]
    have hpilo := Real.pi_gt_d20
    have hlinear : 0 ≤ s * π ^ 2 := by positivity
    have hquad : 0 ≤ s ^ 2 * q 0 := by positivity
    norm_num at hpilo ⊢
    linarith
  have hsPi2 : s * π ^ 2 < (1 / 100 : ℝ) * 16 :=
    mul_lt_mul hs hp2'.le (sq_pos_of_pos Real.pi_pos) (by norm_num)
  have hs2q0 : s ^ 2 * q 0 < (1 / 100 : ℝ) ^ 2 * 54 :=
    mul_lt_mul hs2 hq0.2 hq0pos (by norm_num)
  have hzHi : z < (10 / 3 : ℝ) := by
    rw [hzEq]
    have hpihi := Real.pi_lt_d20
    norm_num at hsPi2 hs2q0 hpihi ⊢
    nlinarith
  have hszpos : 0 < s * z := mul_pos hs0 hzpos
  have hsz : s * z < (1 / 30 : ℝ) := by
    have h := mul_lt_mul hs hzHi.le hzpos (by norm_num)
    norm_num at h ⊢
    exact h
  have hApos : 0 < aCoord s z := by
    simp only [aCoord]
    positivity
  have hAHi : aCoord s z < (31 / 30 : ℝ) := by
    simp only [aCoord]
    linarith
  have hyPos : 0 < yCoord s z := by
    simp only [yCoord]
    positivity
  have hySmall : yCoord s z < (1 / 50 : ℝ) := by
    have h := mul_lt_mul hs hAHi.le hApos (by norm_num)
    simp only [yCoord]
    norm_num at h ⊢
    nlinarith
  have hySqSmall : yCoord s z ^ 2 < (1 / 2500 : ℝ) := by
    nlinarith [mul_pos (sub_pos.mpr hySmall)
      (add_pos (by norm_num : (0 : ℝ) < 1 / 50) hyPos)]
  have hySq : yCoord s z ^ 2 < 1 := lt_trans hySqSmall (by norm_num)
  have hdenPos : 0 < (1 + s ^ 2) * (1 - yCoord s z ^ 2) :=
    mul_pos (by positivity) (sub_pos.mpr hySq)
  have hdenHi :
      (1 + s ^ 2) * (1 - yCoord s z ^ 2) <
        (10001 / 10000 : ℝ) := by
    have hySqPos : 0 < yCoord s z ^ 2 := sq_pos_of_pos hyPos
    have hmul := mul_lt_mul_of_pos_left
      (show 1 - yCoord s z ^ 2 < 1 by nlinarith)
      (show 0 < 1 + s ^ 2 by positivity)
    norm_num at hs2 ⊢
    nlinarith
  have hdenLo : (2499 / 2500 : ℝ) <
      (1 + s ^ 2) * (1 - yCoord s z ^ 2) := by
    have hfac : 1 ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    have hmul := mul_le_mul_of_nonneg_right hfac (sub_pos.mpr hySq).le
    nlinarith
  have hnumLo : (314 / 25 : ℝ) <
      2 * z * (2 + s * z) := by
    have hgrowth := mul_lt_mul_of_pos_left
      (show 2 < 2 + s * z by linarith)
      (show 0 < 2 * z by positivity)
    nlinarith
  have hnumHi : 2 * z * (2 + s * z) < (122 / 9 : ℝ) := by
    have hzScaled : 2 * z < (20 / 3 : ℝ) := by nlinarith
    have hfactor : 2 + s * z < (61 / 30 : ℝ) := by linarith
    have hmul := mul_lt_mul hzScaled hfactor.le
      (show 0 < 2 + s * z by positivity) (by norm_num : (0 : ℝ) ≤ 20 / 3)
    nlinarith
  change
    251 / 20 < 2 * z * (2 + s * z) /
        ((1 + s ^ 2) * (1 - yCoord s z ^ 2)) ∧
      2 * z * (2 + s * z) /
        ((1 + s ^ 2) * (1 - yCoord s z ^ 2)) < 14
  constructor
  · apply (lt_div_iff₀ hdenPos).2
    nlinarith
  · apply (div_lt_iff₀ hdenPos).2
    nlinarith

set_option maxHeartbeats 0 in
-- The exact box arithmetic exceeds the default deterministic elaboration budget.
/-- Every positive endpoint-box slice below `1/100` lies in the principal
half-angle chart required to recover the source fold, incidence, and area
equations from the corrected normalized rows. -/
theorem endpointBox_principalChart {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) :
    yCoord s (endpointPhysicalPoint s q 0) ^ 2 < 1 ∧
      1 + s * yCoord s (endpointPhysicalPoint s q 0) ≠ 0 ∧
      s * ((yCoord s (endpointPhysicalPoint s q 0) - s) /
        (1 + s * yCoord s (endpointPhysicalPoint s q 0))) < 1 ∧
      1 + wCoord s (endpointPhysicalPoint s q 1) *
        vCoord s (endpointPhysicalPoint s q 0)
          (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2) ≠ 0 ∧
      wCoord s (endpointPhysicalPoint s q 1) *
        ((vCoord s (endpointPhysicalPoint s q 0)
            (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2) -
            wCoord s (endpointPhysicalPoint s q 1)) /
          (1 + wCoord s (endpointPhysicalPoint s q 1) *
            vCoord s (endpointPhysicalPoint s q 0)
              (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2))) < 1 := by
  let z := endpointPhysicalPoint s q 0
  let a := endpointPhysicalPoint s q 1
  let b := endpointPhysicalPoint s q 2
  have hbounds := endpointBox_coordinate_bounds hs0 hs q hq
  change
    (0 < s ∧ s < yCoord s z ∧ yCoord s z < 1) ∧
      (0 < wCoord s a ∧ wCoord s a < vCoord s z a b ∧
        vCoord s z a b < 1) ∧
      (1 < density s z ∧ density s z < (51 / 50 : ℝ)) at hbounds
  rcases hbounds with
    ⟨⟨_, hsy, hylt⟩, ⟨hw, hwv, _⟩, _⟩
  have hy : 0 < yCoord s z := lt_trans hs0 hsy
  have hv : 0 < vCoord s z a b := lt_trans hw hwv
  have hySq : yCoord s z ^ 2 < 1 := by nlinarith
  have hdenFourPos : 0 < 1 + s * yCoord s z := by positivity
  have hdenThreePos : 0 < 1 + wCoord s a * vCoord s z a b := by positivity
  have haddFour : s * ((yCoord s z - s) /
      (1 + s * yCoord s z)) < 1 := by
    rw [← mul_div_assoc, div_lt_iff₀ hdenFourPos]
    nlinarith [sq_nonneg s]
  have haddThree : wCoord s a * ((vCoord s z a b - wCoord s a) /
      (1 + wCoord s a * vCoord s z a b)) < 1 := by
    rw [← mul_div_assoc, div_lt_iff₀ hdenThreePos]
    nlinarith [sq_nonneg (wCoord s a)]
  change yCoord s z ^ 2 < 1 ∧
    1 + s * yCoord s z ≠ 0 ∧
    s * ((yCoord s z - s) / (1 + s * yCoord s z)) < 1 ∧
    1 + wCoord s a * vCoord s z a b ≠ 0 ∧
    wCoord s a * ((vCoord s z a b - wCoord s a) /
      (1 + wCoord s a * vCoord s z a b)) < 1
  exact ⟨hySq, ne_of_gt hdenFourPos, haddFour,
    ne_of_gt hdenThreePos, haddThree⟩

/-- The validated positive endpoint cell contains a geometrically ordered
principal-chart point at density `1 < lambda < 51/50` and a simultaneous zero
of the three original source fold, incidence, and equal-area residuals. -/
theorem positive_rational_source_nearOneRoot :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      let x := endpointPhysicalPoint s q
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        s < yCoord s (x 0) ∧ yCoord s (x 0) < 1 ∧
        0 < wCoord s (x 1) ∧
        wCoord s (x 1) < vCoord s (x 0) (x 1) (x 2) ∧
        vCoord s (x 0) (x 1) (x 2) < 1 ∧
        1 < density s (x 0) ∧ density s (x 0) < (51 / 50 : ℝ) ∧
        sourceFoldResidual s (x 0) π = 0 ∧
        sourceCosineResidual s (x 0) (x 1) (x 2) = 0 ∧
        sourceAreaResidual s (x 0) (x 1) (x 2) π = 0 := by
  rcases positive_rational_corrected_nearOneRoot with
    ⟨n, q, hs0, hs, hq, hroot⟩
  let s : ℝ := 1 / (n + 1 : ℝ)
  let x := endpointPhysicalPoint s q
  change nearOneRootMap s π x = 0 at hroot
  have hfold : foldRow s (x 0) π = 0 := by
    have h := congrFun hroot (0 : Fin 3)
    simpa [nearOneRootMap] using h
  have hcosine : (NearOneNormalizedFlow.H2 (x 0) (x 1) (x 2)).eval s = 0 := by
    have h := congrFun hroot (1 : Fin 3)
    simpa [nearOneRootMap] using h
  have harea : regularizedThirdRow s (x 0) (x 1) (x 2) π = 0 := by
    have h := congrFun hroot (2 : Fin 3)
    simpa [nearOneRootMap] using h
  rcases endpointBox_principalChart hs0 hs q hq with
    ⟨hy, hdenFour, haddFour, hdenThree, haddThree⟩
  rcases endpointBox_coordinate_bounds hs0 hs q hq with
    ⟨⟨_, hsy, hylt⟩, ⟨hw, hwv, hvlt⟩, hlamlo, hlamhi⟩
  have hfoldSource : sourceFoldResidual s (x 0) π = 0 := by
    apply (sourceFoldResidual_eq_zero_iff_complete s (x 0) π
      (ne_of_gt hs0) (ne_of_gt (sub_pos.mpr hy)) hdenFour haddFour).mpr
    exact (foldRow_eq_zero_iff s (x 0) π).mp hfold
  have hcosineSource : sourceCosineResidual s (x 0) (x 1) (x 2) = 0 :=
    (sourceCosineResidual_eq_zero_iff_H2 s (x 0) (x 1) (x 2)
      (ne_of_gt hs0) hy).mpr hcosine
  have hareaSource : sourceAreaResidual s (x 0) (x 1) (x 2) π = 0 :=
    (sourceAreaResidual_eq_zero_iff_regularizedThirdRow
      s (x 0) (x 1) (x 2) π (ne_of_gt hs0) hy hdenFour haddFour
        hdenThree haddThree hfoldSource hcosineSource).mpr harea
  exact ⟨n, q, hs0, hs, hq, hsy, hylt, hw, hwv, hvlt,
    hlamlo, hlamhi, hfoldSource, hcosineSource, hareaSource⟩

/-- The validated positive endpoint cell produces an actual stationary,
equal-area scalar pair in the unresolved near-one density range. -/
theorem positive_rational_stationaryEqualAreaPair :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      let x := endpointPhysicalPoint s q
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        ∃ pair : LeanSuffixAnalytic.StationaryEqualAreaPair (density s (x 0)),
          pair.h₃ = (1 + halfCos (wCoord s (x 1))) / 2 ∧
          pair.h₄ = halfCos s ∧
          1 < density s (x 0) ∧ density s (x 0) < (51 / 50 : ℝ) := by
  rcases positive_rational_source_nearOneRoot with
    ⟨n, q, hs0, hs, hq, hsy, hy1, hw0, hwv, hv1,
      hlam, hlam51, hfold, hcosine, harea⟩
  refine ⟨n, q, hs0, hs, hq, ?_⟩
  let s : ℝ := 1 / (n + 1 : ℝ)
  let x := endpointPhysicalPoint s q
  have hs1 : s < 1 := lt_trans hs (by norm_num)
  have hy0 : 0 < yCoord s (x 0) := lt_trans hs0 hsy
  have hw1 : wCoord s (x 1) < 1 := lt_trans hwv hv1
  have hv0 : 0 < vCoord s (x 0) (x 1) (x 2) := lt_trans hw0 hwv
  let pair :=
    sourceResiduals_stationaryEqualAreaPair
      hs0 hs1 hy0 hy1 hw0 hw1 hv0 hlam hfold hcosine harea
  exact ⟨pair, rfl, rfl, hlam, hlam51⟩

end NearOneRescaledFirstCell

end

end NearOneRegularizedThirdRow
