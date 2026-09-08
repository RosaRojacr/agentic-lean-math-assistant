/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneThirdFaceBounds

/-!
# Explicit reduced-gap bounds on the first near-one endpoint box

The polynomial is split in the scale before substituting the physical path.
Only the first three coefficients require the cusp cancellations; the remaining
coefficients have direct rational absolute-value bounds.
-/

namespace NearOneRegularizedThirdRow
open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
noncomputable section
namespace NearOneRescaledFirstCell

private lemma gapAbsAdd {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x + y| ≤ X + Y := (abs_add_le x y).trans (add_le_add hx hy)

private lemma gapAbsMul {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) :
    |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

private lemma gapAbsPow {x X : ℝ} (hx : |x| ≤ X) (n : ℕ) :
    |x ^ n| ≤ X ^ n := by
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg x) hx n

private def gapHigh3 (z a b : ℝ) : ℝ :=
  ((6 * (z ^ 2)) + (16 * b) + (384 * (a ^ 2)) + ((-132) * a * z))

private def gapHigh4 (z a b : ℝ) : ℝ :=
  (((-6) * z) + (24 * a) + (26 * (z ^ 3)) + (168 * (a ^ 3)) + ((-196) * a * (z ^ 2)) + ((-16) * b
    * z) + (112 * a * b) + (263 * z * (a ^ 2)))

private def gapHigh5 (z a b : ℝ) : ℝ :=
  (((-118) * (z ^ 2)) + (4 * b) + (8 * (b ^ 2)) + (24 * (z ^ 4)) + ((-140) * a * (z ^ 3)) + ((-56)
    * z * (a ^ 3)) + ((-36) * b * (z ^ 2)) + (52 * b * (a ^ 2)) + (211 * (a ^ 2) * (z ^ 2)) + (284
    * a * z) + (108 * a * b * z))

private def gapHigh6 (z a b : ℝ) : ℝ :=
  (((-96) * a) + (10 * (z ^ 3)) + (36 * z) + ((-400) * a * (z ^ 2)) + ((-49) * z * (a ^ 4)) +
    ((-20) * b * (z ^ 3)) + ((-5) * (a ^ 2) * (z ^ 3)) + (4 * a * (b ^ 2)) + (10 * z * (b ^ 2)) +
    (28 * (a ^ 3) * (z ^ 2)) + (44 * b * z) + (885 * z * (a ^ 2)) + ((-8) * b * z * (a ^ 2)) + (56
    * a * b * (z ^ 2)))

private def gapHigh7 (z a b : ℝ) : ℝ :=
  (((-384) * (a ^ 2)) + ((-16) * b) + (66 * (z ^ 4)) + (76 * (z ^ 2)) + ((-360) * a * (z ^ 3)) +
    ((-44) * b * (z ^ 2)) + (4 * a * z) + (4 * (b ^ 2) * (z ^ 2)) + (222 * (a ^ 2) * (z ^ 2)) +
    (560 * z * (a ^ 3)) + ((-14) * b * z * (a ^ 3)) + (4 * b * (a ^ 2) * (z ^ 2)) + (240 * a * b *
    z))

private def gapHigh8 (z a b : ℝ) : ℝ :=
  (((-168) * (a ^ 3)) + ((-44) * (z ^ 3)) + ((-16) * z) + (8 * (z ^ 5)) + ((-835) * z * (a ^ 2)) +
    ((-210) * (a ^ 2) * (z ^ 3)) + ((-112) * a * b) + ((-60) * b * (z ^ 3)) + ((-8) * b * z) + (12
    * a * (z ^ 4)) + (16 * z * (b ^ 2)) + (49 * z * (a ^ 4)) + (252 * (a ^ 3) * (z ^ 2)) + (612 *
    a * (z ^ 2)) + ((-1) * z * (a ^ 2) * (b ^ 2)) + (132 * a * b * (z ^ 2)) + (164 * b * z * (a ^
    2)))

private def gapHigh9 (z a b : ℝ) : ℝ :=
  (((-100) * (z ^ 4)) + ((-16) * (z ^ 2)) + ((-8) * (b ^ 2)) + ((-280) * z * (a ^ 3)) + ((-128) *
    a * z) + ((-52) * b * (a ^ 2)) + ((-49) * (a ^ 4) * (z ^ 2)) + ((-28) * (a ^ 3) * (z ^ 3)) +
    ((-9) * (a ^ 2) * (z ^ 2)) + ((-8) * b * (z ^ 4)) + (13 * (a ^ 2) * (z ^ 4)) + (14 * (b ^ 2) *
    (z ^ 2)) + (80 * b * (z ^ 2)) + (468 * a * (z ^ 3)) + ((-276) * a * b * z) + ((-20) * a * b *
    (z ^ 3)) + (12 * a * z * (b ^ 2)) + (14 * b * z * (a ^ 3)) + (92 * b * (a ^ 2) * (z ^ 2)))

private def gapHigh10 (z a b : ℝ) : ℝ :=
  (((-8) * (z ^ 5)) + (32 * (z ^ 3)) + ((-312) * z * (a ^ 2)) + ((-240) * a * (z ^ 2)) + ((-100) *
    a * (z ^ 4)) + ((-49) * (a ^ 4) * (z ^ 3)) + ((-22) * z * (b ^ 2)) + ((-16) * b * z) + ((-4) *
    a * (b ^ 2)) + ((-4) * (a ^ 2) * (z ^ 5)) + (2 * (b ^ 2) * (z ^ 3)) + (28 * (a ^ 3) * (z ^ 4))
    + (49 * z * (a ^ 4)) + (80 * b * (z ^ 3)) + (364 * (a ^ 3) * (z ^ 2)) + (403 * (a ^ 2) * (z ^
    3)) + (z * (a ^ 2) * (b ^ 2)) + ((-100) * a * b * (z ^ 2)) + ((-96) * b * z * (a ^ 2)) +
    ((-14) * b * (a ^ 3) * (z ^ 2)) + ((-4) * b * (a ^ 2) * (z ^ 3)) + (8 * a * (b ^ 2) * (z ^
    2)))

private def gapHigh11 (z a b : ℝ) : ℝ :=
  ((8 * (z ^ 6)) + (32 * (z ^ 4)) + ((-816) * (a ^ 2) * (z ^ 2)) + ((-224) * z * (a ^ 3)) +
    ((-147) * (a ^ 2) * (z ^ 4)) + ((-40) * a * (z ^ 5)) + ((-32) * b * (z ^ 2)) + ((-14) * (b ^
    2) * (z ^ 2)) + (32 * a * (z ^ 3)) + (196 * (a ^ 4) * (z ^ 2)) + (616 * (a ^ 3) * (z ^ 3)) +
    ((-1) * (a ^ 2) * (b ^ 2) * (z ^ 2)) + ((-72) * a * b * z) + ((-14) * b * (a ^ 3) * (z ^ 3)) +
    ((-8) * a * z * (b ^ 2)) + (4 * b * (a ^ 2) * (z ^ 4)) + (14 * b * z * (a ^ 3)) + (76 * a * b
    * (z ^ 3)) + (80 * b * (a ^ 2) * (z ^ 2)))

private def gapHigh12 (z a b : ℝ) : ℝ :=
  (((-16) * (z ^ 5)) + ((-644) * (a ^ 3) * (z ^ 2)) + ((-580) * (a ^ 2) * (z ^ 3)) + ((-104) * (a
    ^ 2) * (z ^ 5)) + ((-49) * z * (a ^ 4)) + ((-8) * b * (z ^ 5)) + ((-4) * z * (b ^ 2)) + (2 *
    (b ^ 2) * (z ^ 3)) + (16 * a * (z ^ 6)) + (112 * (a ^ 3) * (z ^ 4)) + (196 * (a ^ 4) * (z ^
    3)) + (256 * a * (z ^ 4)) + (z * (a ^ 2) * (b ^ 2)) + ((-1) * (a ^ 2) * (b ^ 2) * (z ^ 3)) +
    ((-200) * a * b * (z ^ 2)) + ((-60) * b * z * (a ^ 2)) + ((-4) * a * b * (z ^ 4)) + (4 * a *
    (b ^ 2) * (z ^ 2)) + (56 * b * (a ^ 3) * (z ^ 2)) + (172 * b * (a ^ 2) * (z ^ 3)))

private def gapHigh13 (z a b : ℝ) : ℝ :=
  (((-16) * (z ^ 6)) + ((-588) * (a ^ 3) * (z ^ 3)) + ((-147) * (a ^ 4) * (z ^ 2)) + ((-28) * (a ^
    3) * (z ^ 5)) + ((-12) * (b ^ 2) * (z ^ 2)) + (2 * (b ^ 2) * (z ^ 4)) + (4 * (a ^ 2) * (z ^
    6)) + (32 * b * (z ^ 4)) + (36 * (a ^ 2) * (z ^ 4)) + (49 * (a ^ 4) * (z ^ 4)) + (96 * a * (z
    ^ 5)) + ((-176) * b * (a ^ 2) * (z ^ 2)) + ((-168) * a * b * (z ^ 3)) + ((-16) * a * b * (z ^
    5)) + ((-14) * b * z * (a ^ 3)) + ((-4) * a * z * (b ^ 2)) + (4 * (a ^ 2) * (b ^ 2) * (z ^ 2))
    + (12 * a * (b ^ 2) * (z ^ 3)) + (44 * b * (a ^ 2) * (z ^ 4)) + (56 * b * (a ^ 3) * (z ^ 3)))

private def gapHigh14 (z a b : ℝ) : ℝ :=
  (((-147) * (a ^ 4) * (z ^ 3)) + ((-140) * (a ^ 3) * (z ^ 4)) + ((-16) * a * (z ^ 6)) + ((-12) *
    (b ^ 2) * (z ^ 3)) + (16 * b * (z ^ 5)) + (108 * (a ^ 2) * (z ^ 5)) + ((-1) * z * (a ^ 2) * (b
    ^ 2)) + ((-168) * b * (a ^ 2) * (z ^ 3)) + ((-42) * b * (a ^ 3) * (z ^ 2)) + ((-24) * a * b *
    (z ^ 4)) + ((-12) * a * (b ^ 2) * (z ^ 2)) + ((-4) * b * (a ^ 2) * (z ^ 5)) + (4 * a * (b ^ 2)
    * (z ^ 4)) + (4 * (a ^ 2) * (b ^ 2) * (z ^ 3)) + (14 * b * (a ^ 3) * (z ^ 4)))

private def gapHigh15 (z a b : ℝ) : ℝ :=
  (((-49) * (a ^ 4) * (z ^ 4)) + ((-4) * (a ^ 2) * (z ^ 6)) + ((-4) * (b ^ 2) * (z ^ 4)) + (28 *
    (a ^ 3) * (z ^ 5)) + ((a ^ 2) * (b ^ 2) * (z ^ 4)) + ((-48) * b * (a ^ 2) * (z ^ 4)) + ((-42)
    * b * (a ^ 3) * (z ^ 3)) + ((-12) * a * (b ^ 2) * (z ^ 3)) + ((-3) * (a ^ 2) * (b ^ 2) * (z ^
    2)) + (16 * a * b * (z ^ 5)))

private def gapHigh16 (z a b : ℝ) : ℝ :=
  (((-14) * b * (a ^ 3) * (z ^ 4)) + ((-4) * a * (b ^ 2) * (z ^ 4)) + ((-3) * (a ^ 2) * (b ^ 2) *
    (z ^ 3)) + (4 * b * (a ^ 2) * (z ^ 5)))

private def gapHigh17 (z a b : ℝ) : ℝ :=
  ((-1) * (a ^ 2) * (b ^ 2) * (z ^ 4))

private def gapLow3 (q : Fin 3 → ℝ) : ℝ :=
  ((1 / 288 : ℝ) * (π)⁻¹ * (((-552960) * (q 1)) + ((-1559) * (π ^ 5)) + (67168 * (π ^ 3)) + (86016
    * (q 0)) + (202752 * π) + ((-6720) * (q 1) * (π ^ 2)) + ((-1552) * (q 0) * (π ^ 2)) + ((-1152)
    * π * (q 2))))

private def gapLow4 (q : Fin 3 → ℝ) : ℝ :=
  (((-1824) * (q 1)) + ((-120289 / 20736 : ℝ) * (π ^ 5)) + ((-484 / 9 : ℝ) * π) + ((856 / 3 : ℝ) *
    (q 0)) + ((27379 / 108 : ℝ) * (π ^ 3)) + ((-4) * π * (q 2)) + ((-277 / 48 : ℝ) * (q 0) * (π ^
    2)) + ((-145 / 6 : ℝ) * (q 1) * (π ^ 2)))

private def gapLow5 (q : Fin 3 → ℝ) : ℝ :=
  (((-1849 / 20736 : ℝ) * (π ^ 6)) + ((-484 / 9 : ℝ) * (π ^ 2)) + ((-473 / 108 : ℝ) * (π ^ 4)) +
    ((1 / 3 : ℝ) * ((q 0) ^ 2)) + ((-28) * (q 0) * (q 1)) + ((-4) * (q 2) * (π ^ 2)) + ((-5804 / 3
    : ℝ) * π * (q 1)) + ((-5341 / 432 : ℝ) * (q 0) * (π ^ 3)) + ((233 / 72 : ℝ) * (q 1) * (π ^ 3))
    + ((4954 / 9 : ℝ) * π * (q 0)))

private def gapLow6 (q : Fin 3 → ℝ) : ℝ :=
  ((1 / 20736 : ℝ) * (π)⁻¹ * ((6193152 * ((q 0) ^ 2)) + ((-39813120) * (q 0) * (q 1)) +
    ((-1115136) * π * (q 0)) + ((-304128) * (q 1) * (π ^ 3)) + ((-217536) * (q 0) * (π ^ 3)) +
    ((-136368) * (π ^ 2) * ((q 0) ^ 2)) + ((-20736) * (π ^ 2) * ((q 1) ^ 2)) + ((-12384) * (q 1) *
    (π ^ 5)) + ((-7009) * (q 0) * (π ^ 5)) + ((-82944) * π * (q 2) * (q 0)) + (62208 * (q 0) * (q
    1) * (π ^ 2))))

private def gapLow7 (q : Fin 3 → ℝ) : ℝ :=
  (((-55 / 9 : ℝ) * ((q 0) ^ 2)) + ((-1) * (π ^ 2) * ((q 1) ^ 2)) + ((-365 / 864 : ℝ) * (π ^ 2) *
    ((q 0) ^ 2)) + ((-44 / 3 : ℝ) * (q 0) * (q 1)) + ((-103 / 72 : ℝ) * (q 0) * (q 1) * (π ^ 2)))

private def gapLow8 (q : Fin 3 → ℝ) : ℝ :=
  (((-25 / 144 : ℝ) * ((q 0) ^ 3)) + ((-1) * (q 0) * ((q 1) ^ 2)) + ((-5 / 6 : ℝ) * (q 1) * ((q 0)
    ^ 2)))

private lemma gapHigh3_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh3 z a b| ≤ 3408 := by
  unfold gapHigh3
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |(6 : ℝ)| ≤ 6) (gapAbsPow
    hz 2)) (gapAbsMul (by norm_num : |(16 : ℝ)| ≤ 16) hb)) (gapAbsMul (by norm_num : |(384 : ℝ)| ≤
    384) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-132) : ℝ)| ≤ 132) ha) hz))
  norm_num at h ⊢
  exact h

private lemma gapHigh4_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh4 z a b| ≤ 26520 := by
  unfold gapHigh4
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsMul (by norm_num : |((-6) : ℝ)| ≤ 6) hz) (gapAbsMul (by norm_num : |(24 : ℝ)| ≤ 24)
    ha)) (gapAbsMul (by norm_num : |(26 : ℝ)| ≤ 26) (gapAbsPow hz 3))) (gapAbsMul (by norm_num :
    |(168 : ℝ)| ≤ 168) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-196) : ℝ)| ≤
    196) ha) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16) hb) hz))
    (gapAbsMul (gapAbsMul (by norm_num : |(112 : ℝ)| ≤ 112) ha) hb)) (gapAbsMul (gapAbsMul (by
    norm_num : |(263 : ℝ)| ≤ 263) hz) (gapAbsPow ha 2)))
  norm_num at h ⊢
  exact h

private lemma gapHigh5_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh5 z a b| ≤ 134060 := by
  unfold gapHigh5
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-118) : ℝ)| ≤ 118) (gapAbsPow hz
    2)) (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) hb)) (gapAbsMul (by norm_num : |(8 : ℝ)| ≤ 8)
    (gapAbsPow hb 2))) (gapAbsMul (by norm_num : |(24 : ℝ)| ≤ 24) (gapAbsPow hz 4))) (gapAbsMul
    (gapAbsMul (by norm_num : |((-140) : ℝ)| ≤ 140) ha) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul
    (by norm_num : |((-56) : ℝ)| ≤ 56) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (by norm_num :
    |((-36) : ℝ)| ≤ 36) hb) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |(52 : ℝ)| ≤
    52) hb) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (by norm_num : |(211 : ℝ)| ≤ 211) (gapAbsPow
    ha 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |(284 : ℝ)| ≤ 284) ha) hz))
    (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(108 : ℝ)| ≤ 108) ha) hb) hz))
  norm_num at h ⊢
  exact h

private lemma gapHigh6_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh6 z a b| ≤ 285056 := by
  unfold gapHigh6
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num :
    |((-96) : ℝ)| ≤ 96) ha) (gapAbsMul (by norm_num : |(10 : ℝ)| ≤ 10) (gapAbsPow hz 3)))
    (gapAbsMul (by norm_num : |(36 : ℝ)| ≤ 36) hz)) (gapAbsMul (gapAbsMul (by norm_num : |((-400)
    : ℝ)| ≤ 400) ha) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-49) : ℝ)| ≤ 49)
    hz) (gapAbsPow ha 4))) (gapAbsMul (gapAbsMul (by norm_num : |((-20) : ℝ)| ≤ 20) hb) (gapAbsPow
    hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-5) : ℝ)| ≤ 5) (gapAbsPow ha 2)) (gapAbsPow hz
    3))) (gapAbsMul (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) ha) (gapAbsPow hb 2))) (gapAbsMul
    (gapAbsMul (by norm_num : |(10 : ℝ)| ≤ 10) hz) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (by
    norm_num : |(28 : ℝ)| ≤ 28) (gapAbsPow ha 3)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by
    norm_num : |(44 : ℝ)| ≤ 44) hb) hz)) (gapAbsMul (gapAbsMul (by norm_num : |(885 : ℝ)| ≤ 885)
    hz) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-8) : ℝ)| ≤ 8) hb)
    hz) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(56 : ℝ)| ≤ 56) ha)
    hb) (gapAbsPow hz 2)))
  norm_num at h ⊢
  exact h

private lemma gapHigh7_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh7 z a b| ≤ 377968 := by
  unfold gapHigh7
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-384) :
    ℝ)| ≤ 384) (gapAbsPow ha 2)) (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16) hb)) (gapAbsMul (by
    norm_num : |(66 : ℝ)| ≤ 66) (gapAbsPow hz 4))) (gapAbsMul (by norm_num : |(76 : ℝ)| ≤ 76)
    (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-360) : ℝ)| ≤ 360) ha) (gapAbsPow
    hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-44) : ℝ)| ≤ 44) hb) (gapAbsPow hz 2)))
    (gapAbsMul (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) ha) hz)) (gapAbsMul (gapAbsMul (by
    norm_num : |(4 : ℝ)| ≤ 4) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by
    norm_num : |(222 : ℝ)| ≤ 222) (gapAbsPow ha 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by
    norm_num : |(560 : ℝ)| ≤ 560) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-14) : ℝ)| ≤ 14) hb) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |(4 : ℝ)| ≤ 4) hb) (gapAbsPow ha 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(240 : ℝ)| ≤ 240) ha) hb) hz))
  norm_num at h ⊢
  exact h

private lemma gapHigh8_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh8 z a b| ≤ 795136 := by
  unfold gapHigh8
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsMul (by norm_num : |((-168) : ℝ)| ≤ 168) (gapAbsPow ha 3)) (gapAbsMul (by
    norm_num : |((-44) : ℝ)| ≤ 44) (gapAbsPow hz 3))) (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤
    16) hz)) (gapAbsMul (by norm_num : |(8 : ℝ)| ≤ 8) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (by
    norm_num : |((-835) : ℝ)| ≤ 835) hz) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (by norm_num :
    |((-210) : ℝ)| ≤ 210) (gapAbsPow ha 2)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by norm_num
    : |((-112) : ℝ)| ≤ 112) ha) hb)) (gapAbsMul (gapAbsMul (by norm_num : |((-60) : ℝ)| ≤ 60) hb)
    (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-8) : ℝ)| ≤ 8) hb) hz)) (gapAbsMul
    (gapAbsMul (by norm_num : |(12 : ℝ)| ≤ 12) ha) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by
    norm_num : |(16 : ℝ)| ≤ 16) hz) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (by norm_num : |(49 :
    ℝ)| ≤ 49) hz) (gapAbsPow ha 4))) (gapAbsMul (gapAbsMul (by norm_num : |(252 : ℝ)| ≤ 252)
    (gapAbsPow ha 3)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |(612 : ℝ)| ≤ 612)
    ha) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-1) : ℝ)| ≤ 1) hz)
    (gapAbsPow ha 2)) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(132 :
    ℝ)| ≤ 132) ha) hb) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(164 :
    ℝ)| ≤ 164) hb) hz) (gapAbsPow ha 2)))
  norm_num at h ⊢
  exact h

private lemma gapHigh9_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh9 z a b| ≤ 1459512 := by
  unfold gapHigh9
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-100) : ℝ)| ≤ 100) (gapAbsPow hz
    4)) (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16) (gapAbsPow hz 2))) (gapAbsMul (by norm_num :
    |((-8) : ℝ)| ≤ 8) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-280) : ℝ)| ≤
    280) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-128) : ℝ)| ≤ 128) ha)
    hz)) (gapAbsMul (gapAbsMul (by norm_num : |((-52) : ℝ)| ≤ 52) hb) (gapAbsPow ha 2)))
    (gapAbsMul (gapAbsMul (by norm_num : |((-49) : ℝ)| ≤ 49) (gapAbsPow ha 4)) (gapAbsPow hz 2)))
    (gapAbsMul (gapAbsMul (by norm_num : |((-28) : ℝ)| ≤ 28) (gapAbsPow ha 3)) (gapAbsPow hz 3)))
    (gapAbsMul (gapAbsMul (by norm_num : |((-9) : ℝ)| ≤ 9) (gapAbsPow ha 2)) (gapAbsPow hz 2)))
    (gapAbsMul (gapAbsMul (by norm_num : |((-8) : ℝ)| ≤ 8) hb) (gapAbsPow hz 4))) (gapAbsMul
    (gapAbsMul (by norm_num : |(13 : ℝ)| ≤ 13) (gapAbsPow ha 2)) (gapAbsPow hz 4))) (gapAbsMul
    (gapAbsMul (by norm_num : |(14 : ℝ)| ≤ 14) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul
    (gapAbsMul (by norm_num : |(80 : ℝ)| ≤ 80) hb) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by
    norm_num : |(468 : ℝ)| ≤ 468) ha) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-276) : ℝ)| ≤ 276) ha) hb) hz)) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num :
    |((-20) : ℝ)| ≤ 20) ha) hb) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num :
    |(12 : ℝ)| ≤ 12) ha) hz) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num :
    |(14 : ℝ)| ≤ 14) hb) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num :
    |(92 : ℝ)| ≤ 92) hb) (gapAbsPow ha 2)) (gapAbsPow hz 2)))
  norm_num at h ⊢
  exact h

private lemma gapHigh10_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh10 z a b| ≤ 1928432 := by
  unfold gapHigh10
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num :
    |((-8) : ℝ)| ≤ 8) (gapAbsPow hz 5)) (gapAbsMul (by norm_num : |(32 : ℝ)| ≤ 32) (gapAbsPow hz
    3))) (gapAbsMul (gapAbsMul (by norm_num : |((-312) : ℝ)| ≤ 312) hz) (gapAbsPow ha 2)))
    (gapAbsMul (gapAbsMul (by norm_num : |((-240) : ℝ)| ≤ 240) ha) (gapAbsPow hz 2))) (gapAbsMul
    (gapAbsMul (by norm_num : |((-100) : ℝ)| ≤ 100) ha) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul
    (by norm_num : |((-49) : ℝ)| ≤ 49) (gapAbsPow ha 4)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul
    (by norm_num : |((-22) : ℝ)| ≤ 22) hz) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (by norm_num :
    |((-16) : ℝ)| ≤ 16) hb) hz)) (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) ha)
    (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) (gapAbsPow ha 2))
    (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (by norm_num : |(2 : ℝ)| ≤ 2) (gapAbsPow hb 2))
    (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |(28 : ℝ)| ≤ 28) (gapAbsPow ha 3))
    (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by norm_num : |(49 : ℝ)| ≤ 49) hz) (gapAbsPow ha
    4))) (gapAbsMul (gapAbsMul (by norm_num : |(80 : ℝ)| ≤ 80) hb) (gapAbsPow hz 3))) (gapAbsMul
    (gapAbsMul (by norm_num : |(364 : ℝ)| ≤ 364) (gapAbsPow ha 3)) (gapAbsPow hz 2))) (gapAbsMul
    (gapAbsMul (by norm_num : |(403 : ℝ)| ≤ 403) (gapAbsPow ha 2)) (gapAbsPow hz 3))) (gapAbsMul
    (gapAbsMul hz (gapAbsPow ha 2)) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-100) : ℝ)| ≤ 100) ha) hb) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |((-96) : ℝ)| ≤ 96) hb) hz) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |((-14) : ℝ)| ≤ 14) hb) (gapAbsPow ha 3)) (gapAbsPow hz 2))) (gapAbsMul
    (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) hb) (gapAbsPow ha 2)) (gapAbsPow hz
    3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(8 : ℝ)| ≤ 8) ha) (gapAbsPow hb 2))
    (gapAbsPow hz 2)))
  norm_num at h ⊢
  exact h

private lemma gapHigh11_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh11 z a b| ≤ 2659424 := by
  unfold gapHigh11
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |(8 : ℝ)| ≤ 8) (gapAbsPow hz 6))
    (gapAbsMul (by norm_num : |(32 : ℝ)| ≤ 32) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by
    norm_num : |((-816) : ℝ)| ≤ 816) (gapAbsPow ha 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul
    (by norm_num : |((-224) : ℝ)| ≤ 224) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul (by norm_num
    : |((-147) : ℝ)| ≤ 147) (gapAbsPow ha 2)) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by
    norm_num : |((-40) : ℝ)| ≤ 40) ha) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (by norm_num :
    |((-32) : ℝ)| ≤ 32) hb) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-14) : ℝ)|
    ≤ 14) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |(32 : ℝ)| ≤
    32) ha) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |(196 : ℝ)| ≤ 196) (gapAbsPow
    ha 4)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |(616 : ℝ)| ≤ 616) (gapAbsPow
    ha 3)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-1) : ℝ)| ≤ 1)
    (gapAbsPow ha 2)) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-72) : ℝ)| ≤ 72) ha) hb) hz)) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num :
    |((-14) : ℝ)| ≤ 14) hb) (gapAbsPow ha 3)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |((-8) : ℝ)| ≤ 8) ha) hz) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |(4 : ℝ)| ≤ 4) hb) (gapAbsPow ha 2)) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(14 : ℝ)| ≤ 14) hb) hz) (gapAbsPow ha 3))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(76 : ℝ)| ≤ 76) ha) hb) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(80 : ℝ)| ≤ 80) hb) (gapAbsPow ha 2)) (gapAbsPow hz 2)))
  norm_num at h ⊢
  exact h

private lemma gapHigh12_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh12 z a b| ≤ 5566240 := by
  unfold gapHigh12
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16)
    (gapAbsPow hz 5)) (gapAbsMul (gapAbsMul (by norm_num : |((-644) : ℝ)| ≤ 644) (gapAbsPow ha 3))
    (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-580) : ℝ)| ≤ 580) (gapAbsPow ha
    2)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-104) : ℝ)| ≤ 104) (gapAbsPow
    ha 2)) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (by norm_num : |((-49) : ℝ)| ≤ 49) hz)
    (gapAbsPow ha 4))) (gapAbsMul (gapAbsMul (by norm_num : |((-8) : ℝ)| ≤ 8) hb) (gapAbsPow hz
    5))) (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) hz) (gapAbsPow hb 2))) (gapAbsMul
    (gapAbsMul (by norm_num : |(2 : ℝ)| ≤ 2) (gapAbsPow hb 2)) (gapAbsPow hz 3))) (gapAbsMul
    (gapAbsMul (by norm_num : |(16 : ℝ)| ≤ 16) ha) (gapAbsPow hz 6))) (gapAbsMul (gapAbsMul (by
    norm_num : |(112 : ℝ)| ≤ 112) (gapAbsPow ha 3)) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by
    norm_num : |(196 : ℝ)| ≤ 196) (gapAbsPow ha 4)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by
    norm_num : |(256 : ℝ)| ≤ 256) ha) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul hz (gapAbsPow ha
    2)) (gapAbsPow hb 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-1) : ℝ)| ≤ 1)
    (gapAbsPow ha 2)) (gapAbsPow hb 2)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-200) : ℝ)| ≤ 200) ha) hb) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |((-60) : ℝ)| ≤ 60) hb) hz) (gapAbsPow ha 2))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |((-4) : ℝ)| ≤ 4) ha) hb) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |(4 : ℝ)| ≤ 4) ha) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(56 : ℝ)| ≤ 56) hb) (gapAbsPow ha 3)) (gapAbsPow hz 2))) (gapAbsMul
    (gapAbsMul (gapAbsMul (by norm_num : |(172 : ℝ)| ≤ 172) hb) (gapAbsPow ha 2)) (gapAbsPow hz
    3)))
  norm_num at h ⊢
  exact h

private lemma gapHigh13_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh13 z a b| ≤ 12908192 := by
  unfold gapHigh13
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16)
    (gapAbsPow hz 6)) (gapAbsMul (gapAbsMul (by norm_num : |((-588) : ℝ)| ≤ 588) (gapAbsPow ha 3))
    (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-147) : ℝ)| ≤ 147) (gapAbsPow ha
    4)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-28) : ℝ)| ≤ 28) (gapAbsPow ha
    3)) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (by norm_num : |((-12) : ℝ)| ≤ 12) (gapAbsPow hb
    2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (by norm_num : |(2 : ℝ)| ≤ 2) (gapAbsPow hb 2))
    (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) (gapAbsPow ha 2))
    (gapAbsPow hz 6))) (gapAbsMul (gapAbsMul (by norm_num : |(32 : ℝ)| ≤ 32) hb) (gapAbsPow hz
    4))) (gapAbsMul (gapAbsMul (by norm_num : |(36 : ℝ)| ≤ 36) (gapAbsPow ha 2)) (gapAbsPow hz
    4))) (gapAbsMul (gapAbsMul (by norm_num : |(49 : ℝ)| ≤ 49) (gapAbsPow ha 4)) (gapAbsPow hz
    4))) (gapAbsMul (gapAbsMul (by norm_num : |(96 : ℝ)| ≤ 96) ha) (gapAbsPow hz 5))) (gapAbsMul
    (gapAbsMul (gapAbsMul (by norm_num : |((-176) : ℝ)| ≤ 176) hb) (gapAbsPow ha 2)) (gapAbsPow hz
    2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-168) : ℝ)| ≤ 168) ha) hb) (gapAbsPow
    hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16) ha) hb) (gapAbsPow
    hz 5))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-14) : ℝ)| ≤ 14) hb) hz) (gapAbsPow
    ha 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) ha) hz) (gapAbsPow
    hb 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) (gapAbsPow ha 2))
    (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(12 :
    ℝ)| ≤ 12) ha) (gapAbsPow hb 2)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |(44 : ℝ)| ≤ 44) hb) (gapAbsPow ha 2)) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(56 : ℝ)| ≤ 56) hb) (gapAbsPow ha 3)) (gapAbsPow hz 3)))
  norm_num at h ⊢
  exact h

private lemma gapHigh14_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh14 z a b| ≤ 15091728 := by
  unfold gapHigh14
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul
    (gapAbsMul (by norm_num : |((-147) : ℝ)| ≤ 147) (gapAbsPow ha 4)) (gapAbsPow hz 3)) (gapAbsMul
    (gapAbsMul (by norm_num : |((-140) : ℝ)| ≤ 140) (gapAbsPow ha 3)) (gapAbsPow hz 4)))
    (gapAbsMul (gapAbsMul (by norm_num : |((-16) : ℝ)| ≤ 16) ha) (gapAbsPow hz 6))) (gapAbsMul
    (gapAbsMul (by norm_num : |((-12) : ℝ)| ≤ 12) (gapAbsPow hb 2)) (gapAbsPow hz 3))) (gapAbsMul
    (gapAbsMul (by norm_num : |(16 : ℝ)| ≤ 16) hb) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (by
    norm_num : |(108 : ℝ)| ≤ 108) (gapAbsPow ha 2)) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |((-1) : ℝ)| ≤ 1) hz) (gapAbsPow ha 2)) (gapAbsPow hb 2)))
    (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-168) : ℝ)| ≤ 168) hb) (gapAbsPow ha 2))
    (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-42) : ℝ)| ≤ 42) hb)
    (gapAbsPow ha 3)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-24) :
    ℝ)| ≤ 24) ha) hb) (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-12) :
    ℝ)| ≤ 12) ha) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-4) : ℝ)| ≤ 4) hb) (gapAbsPow ha 2)) (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul
    (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) ha) (gapAbsPow hb 2)) (gapAbsPow hz 4))) (gapAbsMul
    (gapAbsMul (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) (gapAbsPow ha 2)) (gapAbsPow hb 2))
    (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(14 : ℝ)| ≤ 14) hb)
    (gapAbsPow ha 3)) (gapAbsPow hz 4)))
  norm_num at h ⊢
  exact h

private lemma gapHigh15_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh15 z a b| ≤ 12796096 := by
  unfold gapHigh15
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsMul (gapAbsMul (by norm_num : |((-49) : ℝ)| ≤ 49) (gapAbsPow ha
    4)) (gapAbsPow hz 4)) (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) (gapAbsPow ha 2))
    (gapAbsPow hz 6))) (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) (gapAbsPow hb 2))
    (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (by norm_num : |(28 : ℝ)| ≤ 28) (gapAbsPow ha 3))
    (gapAbsPow hz 5))) (gapAbsMul (gapAbsMul (gapAbsPow ha 2) (gapAbsPow hb 2)) (gapAbsPow hz 4)))
    (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-48) : ℝ)| ≤ 48) hb) (gapAbsPow ha 2))
    (gapAbsPow hz 4))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-42) : ℝ)| ≤ 42) hb)
    (gapAbsPow ha 3)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-12) :
    ℝ)| ≤ 12) ha) (gapAbsPow hb 2)) (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by
    norm_num : |((-3) : ℝ)| ≤ 3) (gapAbsPow ha 2)) (gapAbsPow hb 2)) (gapAbsPow hz 2))) (gapAbsMul
    (gapAbsMul (gapAbsMul (by norm_num : |(16 : ℝ)| ≤ 16) ha) hb) (gapAbsPow hz 5)))
  norm_num at h ⊢
  exact h

private lemma gapHigh16_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh16 z a b| ≤ 7729920 := by
  unfold gapHigh16
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num :
    |((-14) : ℝ)| ≤ 14) hb) (gapAbsPow ha 3)) (gapAbsPow hz 4)) (gapAbsMul (gapAbsMul (gapAbsMul
    (by norm_num : |((-4) : ℝ)| ≤ 4) ha) (gapAbsPow hb 2)) (gapAbsPow hz 4))) (gapAbsMul
    (gapAbsMul (gapAbsMul (by norm_num : |((-3) : ℝ)| ≤ 3) (gapAbsPow ha 2)) (gapAbsPow hb 2))
    (gapAbsPow hz 3))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(4 : ℝ)| ≤ 4) hb)
    (gapAbsPow ha 2)) (gapAbsPow hz 5)))
  norm_num at h ⊢
  exact h

private lemma gapHigh17_bound {z a b : ℝ}
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHigh17 z a b| ≤ 2073600 := by
  unfold gapHigh17
  have h := (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-1) : ℝ)| ≤ 1) (gapAbsPow ha 2))
    (gapAbsPow hb 2)) (gapAbsPow hz 4))
  norm_num at h ⊢
  exact h

private lemma gapLow_bounds (q : Fin 3 → ℝ) (hq : InEndpointBox q) :
    |gapLow3 q| ≤ (508304 / 9 : ℝ) ∧
    |gapLow4 q| ≤ (13431790 / 81 : ℝ) ∧
    |gapLow5 q| ≤ (54623860 / 81 : ℝ) ∧
    |gapLow6 q| ≤ (68202692 / 27 : ℝ) ∧
    |gapLow7 q| ≤ 106858 ∧
    |gapLow8 q| ≤ (275427 / 2 : ℝ) := by
  have hp : |π| ≤ 4 := by rw [abs_of_pos Real.pi_pos]; exact Real.pi_lt_four.le
  have hpInv : |π⁻¹| ≤ 1 / 3 := by
    rw [abs_of_pos (inv_pos.mpr Real.pi_pos), inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) Real.pi_gt_three.le
  have hq0 : |q 0| ≤ 54 := by
    have h := hq (0 : Fin 3)
    change 52 ≤ q 0 ∧ q 0 ≤ 54 at h
    rw [abs_le]
    constructor <;> linarith
  have hq1 : |q 1| ≤ 28 := by
    have h := hq (1 : Fin 3)
    change 27 ≤ q 1 ∧ q 1 ≤ 28 at h
    rw [abs_le]
    constructor <;> linarith
  have hq2 : |q 2| ≤ 3822 := by
    have h := hq (2 : Fin 3)
    change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at h
    rw [abs_le]
    constructor <;> linarith
  repeat' apply And.intro
  · unfold gapLow3
    have h := (gapAbsMul (gapAbsMul (by norm_num : |((1 / 288 : ℝ) : ℝ)| ≤ (1 / 288 : ℝ)) hpInv)
      (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by
      norm_num : |((-552960) : ℝ)| ≤ 552960) hq1) (gapAbsMul (by norm_num : |((-1559) : ℝ)| ≤
      1559) (gapAbsPow hp 5))) (gapAbsMul (by norm_num : |(67168 : ℝ)| ≤ 67168) (gapAbsPow hp 3)))
      (gapAbsMul (by norm_num : |(86016 : ℝ)| ≤ 86016) hq0)) (gapAbsMul (by norm_num : |(202752 :
      ℝ)| ≤ 202752) hp)) (gapAbsMul (gapAbsMul (by norm_num : |((-6720) : ℝ)| ≤ 6720) hq1)
      (gapAbsPow hp 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-1552) : ℝ)| ≤ 1552) hq0)
      (gapAbsPow hp 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-1152) : ℝ)| ≤ 1152) hp) hq2)))
    norm_num at h ⊢
    exact h
  · unfold gapLow4
    have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
      (gapAbsMul (by norm_num : |((-1824) : ℝ)| ≤ 1824) hq1) (gapAbsMul (by norm_num : |((-120289
      / 20736 : ℝ) : ℝ)| ≤ (120289 / 20736 : ℝ)) (gapAbsPow hp 5))) (gapAbsMul (by norm_num :
      |((-484 / 9 : ℝ) : ℝ)| ≤ (484 / 9 : ℝ)) hp)) (gapAbsMul (by norm_num : |((856 / 3 : ℝ) : ℝ)|
      ≤ (856 / 3 : ℝ)) hq0)) (gapAbsMul (by norm_num : |((27379 / 108 : ℝ) : ℝ)| ≤ (27379 / 108 :
      ℝ)) (gapAbsPow hp 3))) (gapAbsMul (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) hp) hq2))
      (gapAbsMul (gapAbsMul (by norm_num : |((-277 / 48 : ℝ) : ℝ)| ≤ (277 / 48 : ℝ)) hq0)
      (gapAbsPow hp 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-145 / 6 : ℝ) : ℝ)| ≤ (145 / 6 :
      ℝ)) hq1) (gapAbsPow hp 2)))
    norm_num at h ⊢
    exact h
  · unfold gapLow5
    have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
      (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-1849 / 20736 : ℝ) : ℝ)| ≤ (1849 / 20736
      : ℝ)) (gapAbsPow hp 6)) (gapAbsMul (by norm_num : |((-484 / 9 : ℝ) : ℝ)| ≤ (484 / 9 : ℝ))
      (gapAbsPow hp 2))) (gapAbsMul (by norm_num : |((-473 / 108 : ℝ) : ℝ)| ≤ (473 / 108 : ℝ))
      (gapAbsPow hp 4))) (gapAbsMul (by norm_num : |((1 / 3 : ℝ) : ℝ)| ≤ (1 / 3 : ℝ)) (gapAbsPow
      hq0 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-28) : ℝ)| ≤ 28) hq0) hq1)) (gapAbsMul
      (gapAbsMul (by norm_num : |((-4) : ℝ)| ≤ 4) hq2) (gapAbsPow hp 2))) (gapAbsMul (gapAbsMul
      (by norm_num : |((-5804 / 3 : ℝ) : ℝ)| ≤ (5804 / 3 : ℝ)) hp) hq1)) (gapAbsMul (gapAbsMul (by
      norm_num : |((-5341 / 432 : ℝ) : ℝ)| ≤ (5341 / 432 : ℝ)) hq0) (gapAbsPow hp 3))) (gapAbsMul
      (gapAbsMul (by norm_num : |((233 / 72 : ℝ) : ℝ)| ≤ (233 / 72 : ℝ)) hq1) (gapAbsPow hp 3)))
      (gapAbsMul (gapAbsMul (by norm_num : |((4954 / 9 : ℝ) : ℝ)| ≤ (4954 / 9 : ℝ)) hp) hq0))
    norm_num at h ⊢
    exact h
  · unfold gapLow6
    have h := (gapAbsMul (gapAbsMul (by norm_num : |((1 / 20736 : ℝ) : ℝ)| ≤ (1 / 20736 : ℝ))
      hpInv) (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
      (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |(6193152 : ℝ)| ≤ 6193152)
      (gapAbsPow hq0 2)) (gapAbsMul (gapAbsMul (by norm_num : |((-39813120) : ℝ)| ≤ 39813120) hq0)
      hq1)) (gapAbsMul (gapAbsMul (by norm_num : |((-1115136) : ℝ)| ≤ 1115136) hp) hq0))
      (gapAbsMul (gapAbsMul (by norm_num : |((-304128) : ℝ)| ≤ 304128) hq1) (gapAbsPow hp 3)))
      (gapAbsMul (gapAbsMul (by norm_num : |((-217536) : ℝ)| ≤ 217536) hq0) (gapAbsPow hp 3)))
      (gapAbsMul (gapAbsMul (by norm_num : |((-136368) : ℝ)| ≤ 136368) (gapAbsPow hp 2))
      (gapAbsPow hq0 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-20736) : ℝ)| ≤ 20736)
      (gapAbsPow hp 2)) (gapAbsPow hq1 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-12384) : ℝ)|
      ≤ 12384) hq1) (gapAbsPow hp 5))) (gapAbsMul (gapAbsMul (by norm_num : |((-7009) : ℝ)| ≤
      7009) hq0) (gapAbsPow hp 5))) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |((-82944) :
      ℝ)| ≤ 82944) hp) hq2) hq0)) (gapAbsMul (gapAbsMul (gapAbsMul (by norm_num : |(62208 : ℝ)| ≤
      62208) hq0) hq1) (gapAbsPow hp 2))))
    norm_num at h ⊢
    exact h
  · unfold gapLow7
    have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-55 / 9 :
      ℝ) : ℝ)| ≤ (55 / 9 : ℝ)) (gapAbsPow hq0 2)) (gapAbsMul (gapAbsMul (by norm_num : |((-1) :
      ℝ)| ≤ 1) (gapAbsPow hp 2)) (gapAbsPow hq1 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-365
      / 864 : ℝ) : ℝ)| ≤ (365 / 864 : ℝ)) (gapAbsPow hp 2)) (gapAbsPow hq0 2))) (gapAbsMul
      (gapAbsMul (by norm_num : |((-44 / 3 : ℝ) : ℝ)| ≤ (44 / 3 : ℝ)) hq0) hq1)) (gapAbsMul
      (gapAbsMul (gapAbsMul (by norm_num : |((-103 / 72 : ℝ) : ℝ)| ≤ (103 / 72 : ℝ)) hq0) hq1)
      (gapAbsPow hp 2)))
    norm_num at h ⊢
    exact h
  · unfold gapLow8
    have h := (gapAbsAdd (gapAbsAdd (gapAbsMul (by norm_num : |((-25 / 144 : ℝ) : ℝ)| ≤ (25 / 144
      : ℝ)) (gapAbsPow hq0 3)) (gapAbsMul (gapAbsMul (by norm_num : |((-1) : ℝ)| ≤ 1) hq0)
      (gapAbsPow hq1 2))) (gapAbsMul (gapAbsMul (by norm_num : |((-5 / 6 : ℝ) : ℝ)| ≤ (5 / 6 : ℝ))
      hq1) (gapAbsPow hq0 2)))
    norm_num at h ⊢
    exact h

private def gapHighTail (s z a b : ℝ) : ℝ :=
  gapHigh3 z a b +
    s * gapHigh4 z a b +
    s ^ 2 * gapHigh5 z a b +
    s ^ 3 * gapHigh6 z a b +
    s ^ 4 * gapHigh7 z a b +
    s ^ 5 * gapHigh8 z a b +
    s ^ 6 * gapHigh9 z a b +
    s ^ 7 * gapHigh10 z a b +
    s ^ 8 * gapHigh11 z a b +
    s ^ 9 * gapHigh12 z a b +
    s ^ 10 * gapHigh13 z a b +
    s ^ 11 * gapHigh14 z a b +
    s ^ 12 * gapHigh15 z a b +
    s ^ 13 * gapHigh16 z a b +
    s ^ 14 * gapHigh17 z a b

private def gapLowTail (s : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  gapLow3 q +
    s * gapLow4 q +
    s ^ 2 * gapLow5 q +
    s ^ 3 * gapLow6 q +
    s ^ 4 * gapLow7 q +
    s ^ 5 * gapLow8 q

private def gapAlgebraicLow (s z a b : ℝ) : ℝ :=
  10 * z - 24 * a + s * (12 * z ^ 2 - 28 * a * z - 4 * b) +
    s ^ 2 * (-a ^ 2 * z + 96 * a - 4 * b * z - 24 * z)

set_option maxHeartbeats 0 in
-- Normalizing the degree-17 scalar identity exceeds the default heartbeat budget.
private lemma gap_numerator_split (s z a b : ℝ) :
    reducedGapNumeratorBar s z a b =
      gapAlgebraicLow s z a b + s ^ 3 * gapHighTail s z a b := by
  unfold reducedGapNumeratorBar gapAlgebraicLow gapHighTail
  simp only [aCoord, rCoord, eCoord, yCoord, wCoord, vCoord]
  unfold gapHigh3 gapHigh4 gapHigh5 gapHigh6 gapHigh7 gapHigh8 gapHigh9 gapHigh10 gapHigh11
    gapHigh12 gapHigh13 gapHigh14 gapHigh15 gapHigh16 gapHigh17
  ring

set_option maxHeartbeats 0 in
-- Clearing the exact cusp coefficients and normalizing the path exceeds the default budget.
private lemma gap_low_path_split (s : ℝ) (q : Fin 3 → ℝ) :
    gapAlgebraicLow s (thirdPhysicalZ s q) (thirdPhysicalA s q)
        (thirdPhysicalB s q) =
      s ^ 2 * poleFreeReducedGap 0 q + s ^ 3 * gapLowTail s q := by
  rw [thirdPhysicalZ_eq, thirdPhysicalA_eq, thirdPhysicalB_eq,
    poleFreeReducedGap_zero]
  unfold gapAlgebraicLow gapLowTail gapLow3 gapLow4 gapLow5 gapLow6 gapLow7 gapLow8
  field_simp
  ring

private lemma gap_scale_pow_bound {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) : |s ^ n| ≤ s := by
  rw [abs_of_nonneg (pow_nonneg hs0 n)]
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n; simp
      · rw [pow_succ]
        exact (mul_le_mul (ih (Nat.one_le_iff_ne_zero.mpr hn0)) hs hs0 hs0).trans_eq
          (mul_one s)

private lemma gap_scale_pow_bound_sq {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) : |s ^ n| ≤ s ^ 2 := by
  rw [abs_of_nonneg (pow_nonneg hs0 n)]
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn1 : n = 1
      · subst n
        simp
      · rw [pow_succ]
        have hn2 : 2 ≤ n := by omega
        calc
          s ^ n * s ≤ s ^ 2 * 1 :=
            mul_le_mul (ih hn2) hs hs0 (sq_nonneg s)
          _ = s ^ 2 := by ring


private lemma gap_high_tail_bound {s z a b : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hz : |z| ≤ 4) (ha : |a| ≤ 2) (hb : |b| ≤ 45) :
    |gapHighTail s z a b| ≤ 3409 := by
  have hs1 : s ≤ 1 := hs.trans (by norm_num)
  have hsabs : |s| ≤ s := by rw [abs_of_nonneg hs0]
  have h3 := gapHigh3_bound hz ha hb
  have h4 := gapHigh4_bound hz ha hb
  have h5 := gapHigh5_bound hz ha hb
  have h6 := gapHigh6_bound hz ha hb
  have h7 := gapHigh7_bound hz ha hb
  have h8 := gapHigh8_bound hz ha hb
  have h9 := gapHigh9_bound hz ha hb
  have h10 := gapHigh10_bound hz ha hb
  have h11 := gapHigh11_bound hz ha hb
  have h12 := gapHigh12_bound hz ha hb
  have h13 := gapHigh13_bound hz ha hb
  have h14 := gapHigh14_bound hz ha hb
  have h15 := gapHigh15_bound hz ha hb
  have h16 := gapHigh16_bound hz ha hb
  have h17 := gapHigh17_bound hz ha hb
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd
    (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd h3 (gapAbsMul
    hsabs h4)) (gapAbsMul (gap_scale_pow_bound_sq hs0 hs1 2 (by norm_num)) h5)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 3 (by norm_num)) h6)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 4 (by norm_num)) h7)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 5 (by norm_num)) h8)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 6 (by norm_num)) h9)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 7 (by norm_num)) h10)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 8 (by norm_num)) h11)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 9 (by norm_num)) h12)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 10 (by norm_num)) h13)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 11 (by norm_num)) h14)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 12 (by norm_num)) h15)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 13 (by norm_num)) h16)) (gapAbsMul
    (gap_scale_pow_bound_sq hs0 hs1 14 (by norm_num)) h17))
  change |gapHighTail s z a b| ≤ _ at h
  norm_num at h hs ⊢
  nlinarith

private lemma gap_low_tail_bound {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq : InEndpointBox q) :
    |gapLowTail s q| ≤ 56507 := by
  have hs1 : s ≤ 1 := hs.trans (by norm_num)
  have hsabs : |s| ≤ s := by rw [abs_of_nonneg hs0]
  rcases gapLow_bounds q hq with ⟨h3, h4, h5, h6, h7, h8⟩
  have h := (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd (gapAbsAdd h3 (gapAbsMul hsabs h4))
    (gapAbsMul (gap_scale_pow_bound hs0 hs1 2 (by norm_num)) h5)) (gapAbsMul (gap_scale_pow_bound
    hs0 hs1 3 (by norm_num)) h6)) (gapAbsMul (gap_scale_pow_bound hs0 hs1 4 (by norm_num)) h7))
    (gapAbsMul (gap_scale_pow_bound hs0 hs1 5 (by norm_num)) h8))
  change |gapLowTail s q| ≤ _ at h
  norm_num at h hs ⊢
  linarith


/-- A literal uniform modulus for the rescaled reduced gap.  The bound includes
the zero-scale face and every point of the closed endpoint box. -/
theorem explicit_poleFreeReducedGap_error_bound {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq : InEndpointBox q) :
    |poleFreeReducedGap s q - poleFreeReducedGap 0 q| ≤ s * 59916 := by
  by_cases hsne : s = 0
  · subst s
    simp
  have hgeom := explicit_third_path_geometry q hs0 hs hq
  have hz : |thirdPhysicalZ s q| ≤ 4 := by
    rw [abs_of_nonneg (by linarith [hgeom.1])]
    exact hgeom.2.1
  have ha : |thirdPhysicalA s q| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hgeom.2.2.1])]
    exact hgeom.2.2.2.1
  have hb : |thirdPhysicalB s q| ≤ 45 := hgeom.2.2.2.2.1
  have hlow := gap_low_tail_bound q hs0 hs hq
  have hhigh := gap_high_tail_bound hs0 hs hz ha hb
  have hfactor := reducedGapNumeratorBar_rescaled_factorization s q
  change reducedGapNumeratorBar s (thirdPhysicalZ s q)
      (thirdPhysicalA s q) (thirdPhysicalB s q) =
    s ^ 2 * poleFreeReducedGap s q at hfactor
  have heq : poleFreeReducedGap s q = poleFreeReducedGap 0 q +
      s * (gapLowTail s q +
        gapHighTail s (thirdPhysicalZ s q) (thirdPhysicalA s q)
          (thirdPhysicalB s q)) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hsne)
    rw [← hfactor, gap_numerator_split, gap_low_path_split]
    ring
  have htail := gapAbsAdd hlow hhigh
  have hscaled := gapAbsMul (show |s| ≤ s by rw [abs_of_nonneg hs0]) htail
  rw [heq]
  simpa only [add_sub_cancel_left,
    show (56507 : ℝ) + 3409 = 59916 by norm_num,
    mul_comm 59916] using hscaled

/-- The exact zero-scale reduced gap lies strictly below `-10`. -/
theorem poleFreeReducedGap_zero_lt_neg_ten (q : Fin 3 → ℝ)
    (hq : InEndpointBox q) : poleFreeReducedGap 0 q < -10 := by
  rw [poleFreeReducedGap_zero]
  have hq1 := hq (1 : Fin 3)
  change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
  have hp3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
  have hpihi := Real.pi_lt_d20
  norm_num at hp3lo hpihi ⊢
  nlinarith

/-- The uniform modulus combines with the exact zero-scale gap to give a
rational negative margin on the full radius-`1/126334` prism. -/
theorem explicit_poleFreeReducedGap_neg {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 126334)
    (hq : InEndpointBox q) :
    poleFreeReducedGap s q < -(19 / 2 : ℝ) := by
  have herror := (abs_le.mp
    (explicit_poleFreeReducedGap_error_bound q hs0 hs hq)).2
  have hzero := poleFreeReducedGap_zero_lt_neg_ten q hq
  norm_num at hs ⊢
  linarith

/-- The explicit negative margin transfers to the actual source reduced gap at
every positive scale in the certified interval, without a root hypothesis. -/
theorem explicit_sourceReducedGap_neg {s : ℝ} (q : Fin 3 → ℝ)
    (hs0 : 0 < s) (hs : s ≤ 1 / 126334)
    (hq : InEndpointBox q) :
    sourceReducedGap s (endpointPhysicalPoint s q 0)
      (endpointPhysicalPoint s q 1) (endpointPhysicalPoint s q 2) < 0 := by
  apply sourceReducedGap_neg_of_poleFree hs0 (hs.trans_lt (by norm_num)) hq
  exact (explicit_poleFreeReducedGap_neg q hs0.le hs hq).trans (by norm_num)

end NearOneRescaledFirstCell
end
end NearOneRegularizedThirdRow
