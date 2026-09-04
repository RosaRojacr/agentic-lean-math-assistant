/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CompactCellCertificate

/-!
# The first compact fold-gap cell

This module records kernel-checked real consequences for box 0 of
`compact_fold_gap/compact_certificate.json`.  The certificate endpoints are
repeated as exact rationals; the JSON file is not trusted by Lean.
-/

open Real Set
noncomputable section

namespace CompactFirstCell

abbrev QInterval := ScalarSuffixCertificate.QInterval

namespace QInterval

/-- A convenient exact-rational wrapper around the Taylor inverse-sine rule. -/
theorem realContains_arcsin_of_taylor
    (a : QInterval) (x : ℚ)
    (hx : (-1 : ℚ) ≤ x ∧ x ≤ 1)
    (hbranch : (a.lo : ℝ) ∈ Icc (-(π / 2)) (π / 2) ∧
      (a.hi : ℝ) ∈ Icc (-(π / 2)) (π / 2))
    (hlo : (ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi ≤ x)
    (hhi : x ≤ (ScalarSuffixCertificate.sinTaylor27Interval a.hi).lo) :
    a.RealContains (arcsin (x : ℝ)) :=
  CompactCellCertificate.QInterval.realContains_arcsin_of_taylor
    a x hx hbranch hlo hhi

end QInterval

/-- Interval-input version of the inverse-sine Taylor wrapper.  This is useful
when the inverse-sine argument is itself obtained by exact interval division. -/
theorem realContains_arcsin_of_taylor_interval
    (a xInterval : QInterval) (x : ℝ)
    (hx : xInterval.RealContains x)
    (hxUnit : (-1 : ℝ) ≤ x ∧ x ≤ 1)
    (hbranch : (a.lo : ℝ) ∈ Icc (-(π / 2)) (π / 2) ∧
      (a.hi : ℝ) ∈ Icc (-(π / 2)) (π / 2))
    (hlo : (ScalarSuffixCertificate.sinTaylor27Interval a.lo).hi ≤ xInterval.lo)
    (hhi : xInterval.hi ≤
      (ScalarSuffixCertificate.sinTaylor27Interval a.hi).lo) :
    a.RealContains (arcsin x) :=
  CompactCellCertificate.QInterval.realContains_arcsin_of_taylor_interval
    a xInterval x hx hxUnit hbranch hlo hhi

/-- Lambda interval of box 0. -/
def lambdaInterval : QInterval :=
  ⟨33 / 32, 236601 / 229376, by norm_num⟩

/-- Type-(iv) root slab of box 0. -/
def h4Interval : QInterval :=
  ⟨34445267662685 / 35184372088832,
    275599301332823 / 281474976710656, by norm_num⟩

/-- Type-(iii) equal-area root slab of box 0. -/
def h3Interval : QInterval :=
  ⟨132572791017099 / 140737488355328,
    133157808072187 / 140737488355328, by norm_num⟩

/-- Exact midpoint used by the centered type-(iv) checker evaluation. -/
def h4Center : ℚ := (h4Interval.lo + h4Interval.hi) / 2

/-- Exact midpoint used by the centered type-(iii) checker evaluation. -/
def h3Center : ℚ := (h3Interval.lo + h3Interval.hi) / 2

private def u3LowerInterval : QInterval :=
  ⟨467538 / 1000000, 467540 / 1000000, by norm_num⟩
private def d3LowerInterval : QInterval :=
  ⟨531101 / 1000000, 531585 / 1000000, by norm_num⟩
private def asinQ3LowerInterval : QInterval :=
  ⟨1084291 / 1000000, 1084294 / 1000000, by norm_num⟩
private def asinRatio3LowerInterval : QInterval :=
  ⟨1029378 / 1000000, 1029781 / 1000000, by norm_num⟩

private def u3UpperInterval : QInterval :=
  ⟨451469 / 1000000, 451471 / 1000000, by norm_num⟩
private def d3UpperInterval : QInterval :=
  ⟨517012 / 1000000, 517509 / 1000000, by norm_num⟩
private def asinQ3UpperInterval : QInterval :=
  ⟨1102383 / 1000000, 1102385 / 1000000, by norm_num⟩
private def asinRatio3UpperInterval : QInterval :=
  ⟨1045227 / 1000000, 1045645 / 1000000, by norm_num⟩

private def u3CellInterval : QInterval :=
  ⟨451469 / 1000000, 467540 / 1000000, by norm_num⟩
private def d3CellInterval : QInterval :=
  ⟨517012 / 1000000, 531585 / 1000000, by norm_num⟩
private def asinQ3CellInterval : QInterval :=
  ⟨1084291 / 1000000, 1102385 / 1000000, by norm_num⟩
private def asinRatio3CellInterval : QInterval :=
  ⟨1029378 / 1000000, 1045645 / 1000000, by norm_num⟩

private def u3CenterInterval : QInterval :=
  ⟨459592 / 1000000, 459595 / 1000000, by norm_num⟩
private def d3CenterInterval : QInterval :=
  ⟨524120 / 1000000, 524611 / 1000000, by norm_num⟩
private def asinQ3CenterInterval : QInterval :=
  ⟨1093258 / 1000000, 1093261 / 1000000, by norm_num⟩
private def asinRatio3CenterInterval : QInterval :=
  ⟨1037250 / 1000000, 1037660 / 1000000, by norm_num⟩

private def u4CellInterval : QInterval :=
  ⟨203256 / 1000000, 203893 / 1000000, by norm_num⟩
private def d4CellInterval : QInterval :=
  ⟨323712 / 1000000, 324903 / 1000000, by norm_num⟩
private def asinH4CellInterval : QInterval :=
  ⟨1365463 / 1000000, 1366115 / 1000000, by norm_num⟩
private def asinRatio4CellInterval : QInterval :=
  ⟨1250359 / 1000000, 1251496 / 1000000, by norm_num⟩

private def u4CenterInterval : QInterval :=
  ⟨203574 / 1000000, 203576 / 1000000, by norm_num⟩
private def d4CenterInterval : QInterval :=
  ⟨323912 / 1000000, 324704 / 1000000, by norm_num⟩
private def asinH4CenterInterval : QInterval :=
  ⟨1365787 / 1000000, 1365790 / 1000000, by norm_num⟩
private def asinRatio4CenterInterval : QInterval :=
  ⟨1250562 / 1000000, 1251293 / 1000000, by norm_num⟩


private def u4LowInterval : QInterval :=
  ⟨20389 / 100000, 20390 / 100000, by norm_num⟩
private def d4LowInterval : QInterval :=
  ⟨32411 / 100000, 32491 / 100000, by norm_num⟩
private def asinH4LowInterval : QInterval :=
  ⟨136546 / 100000, 136547 / 100000, by norm_num⟩
private def asinRatioLowInterval : QInterval :=
  ⟨125035 / 100000, 125110 / 100000, by norm_num⟩

private def u4HighInterval : QInterval :=
  ⟨20325 / 100000, 20326 / 100000, by norm_num⟩
private def d4HighInterval : QInterval :=
  ⟨32371 / 100000, 32451 / 100000, by norm_num⟩
private def asinH4HighInterval : QInterval :=
  ⟨136611 / 100000, 136612 / 100000, by norm_num⟩
private def asinRatioHighInterval : QInterval :=
  ⟨125075 / 100000, 125151 / 100000, by norm_num⟩

private def acosRatioLowInterval : QInterval :=
  (ScalarSuffixCertificate.piInterval.nsmul (1 / 2) (by norm_num)).sub
    asinRatioLowInterval
private def acosRatioHighInterval : QInterval :=
  (ScalarSuffixCertificate.piInterval.nsmul (1 / 2) (by norm_num)).sub
    asinRatioHighInterval

private theorem lambda_one_lt {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) : 1 < lam := by
  norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains] at hlam ⊢
  linarith

private theorem h4_slab_regular {h : ℝ}
    (hh : h4Interval.RealContains h) : h ∈ Ioo (0 : ℝ) 1 := by
  norm_num [h4Interval, LeanSuffixReflective.QInterval.RealContains] at hh ⊢
  exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
    lt_of_le_of_lt hh.2 (by norm_num)⟩

private theorem h3_slab_regular {h : ℝ}
    (hh : h3Interval.RealContains h) : h ∈ Ioo (0 : ℝ) 1 := by
  norm_num [h3Interval, LeanSuffixReflective.QInterval.RealContains] at hh ⊢
  exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
    lt_of_le_of_lt hh.2 (by norm_num)⟩

private theorem h4Center_mem : h4Interval.RealContains (h4Center : ℝ) := by
  norm_num [h4Center, h4Interval, LeanSuffixReflective.QInterval.RealContains]

private theorem h3Center_mem : h3Interval.RealContains (h3Center : ℝ) := by
  norm_num [h3Center, h3Interval, LeanSuffixReflective.QInterval.RealContains]

private theorem realContains_of_mem_uIcc {i : QInterval} {c h x : ℝ}
    (hc : i.RealContains c) (hh : i.RealContains h)
    (hx : x ∈ uIcc c h) : i.RealContains x :=
  CompactCellCertificate.realContains_of_mem_uIcc hc hh hx

/-- The lower face of the exact box-0 type-(iv) slab has negative fold value,
uniformly over the whole exact lambda interval. -/
theorem typeFourFold_lowerFace_neg {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    LeanSuffixAnalytic.typeFourFold lam (h4Interval.lo : ℝ) < 0 := by
  let h : ℚ := h4Interval.lo
  have hu : u4LowInterval.RealContains (sqrt (1 - (h : ℝ) ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt
    · norm_num [u4LowInterval]
    · norm_num [u4LowInterval, h, h4Interval]
    · norm_num [u4LowInterval, h, h4Interval]
  have hd : d4LowInterval.RealContains (sqrt (lam ^ 2 - (h : ℝ) ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt
    · norm_num [d4LowInterval]
    · norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains] at hlam
      norm_num [d4LowInterval, h, h4Interval]
      nlinarith
    · norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains] at hlam
      norm_num [d4LowInterval, h, h4Interval]
      nlinarith
  have hasinH : asinH4LowInterval.RealContains (arcsin (h : ℝ)) := by
    apply QInterval.realContains_arcsin_of_taylor
    · norm_num [h, h4Interval]
    · constructor <;> constructor <;>
        norm_num [asinH4LowInterval] <;>
        have hp := Real.pi_gt_three <;> nlinarith
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinH4LowInterval, h, h4Interval,
        Nat.factorial]
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinH4LowInterval, h, h4Interval,
        Nat.factorial]
  have hlamLoPos : 0 < lambdaInterval.lo := by norm_num [lambdaInterval]
  have hratio : (ScalarSuffixCertificate.QInterval.divPos
      (LeanSuffixReflective.QInterval.point h) lambdaInterval hlamLoPos).RealContains
      ((h : ℝ) / lam) := by
    exact ScalarSuffixCertificate.QInterval.realContains_divPos hlamLoPos
      (LeanSuffixReflective.QInterval.realContains_point h (h : ℝ) |>.2 rfl) hlam
  have hasinRatio : asinRatioLowInterval.RealContains (arcsin ((h : ℝ) / lam)) := by
    apply ScalarSuffixCertificate.realContains_arcsin_of_sin_bounds
    · constructor
      · norm_num [h, h4Interval, lambdaInterval,
          ScalarSuffixCertificate.QInterval.divPos,
          ScalarSuffixCertificate.QInterval.recipPos,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point,
          LeanSuffixReflective.QInterval.RealContains] at hratio ⊢
        linarith [hratio.1]
      · norm_num [h, h4Interval, lambdaInterval,
          ScalarSuffixCertificate.QInterval.divPos,
          ScalarSuffixCertificate.QInterval.recipPos,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point,
          LeanSuffixReflective.QInterval.RealContains] at hratio ⊢
        linarith [hratio.2]
    · constructor <;> constructor <;>
        norm_num [asinRatioLowInterval] <;>
        have hp := Real.pi_gt_three <;> nlinarith
    · refine (ScalarSuffixCertificate.sinTaylor27Interval_sound
          asinRatioLowInterval.lo).2.trans ?_
      norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinRatioLowInterval,
        lambdaInterval, h, h4Interval,
        ScalarSuffixCertificate.QInterval.divPos,
        ScalarSuffixCertificate.QInterval.recipPos,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point,
        LeanSuffixReflective.QInterval.RealContains, Nat.factorial] at hratio ⊢
      linarith [hratio.1]
    · have hupper : ((h : ℝ) / lam) ≤
          (ScalarSuffixCertificate.sinTaylor27Interval asinRatioLowInterval.hi).lo := by
        norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
          ScalarSuffixCertificate.sinTaylor27, asinRatioLowInterval,
          lambdaInterval, h, h4Interval,
          ScalarSuffixCertificate.QInterval.divPos,
          ScalarSuffixCertificate.QInterval.recipPos,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point,
          LeanSuffixReflective.QInterval.RealContains, Nat.factorial] at hratio ⊢
        linarith [hratio.2]
      exact hupper.trans
        (ScalarSuffixCertificate.sinTaylor27Interval_sound
          asinRatioLowInterval.hi).1
  have hacos : acosRatioLowInterval.RealContains (arccos ((h : ℝ) / lam)) := by
    exact ScalarSuffixCertificate.realContains_arccos_of_arcsin
      ScalarSuffixCertificate.piInterval_sound hasinRatio
  have hinvU := ScalarSuffixCertificate.QInterval.realContains_recipPos
    (i := u4LowInterval) (by norm_num [u4LowInterval]) hu
  have hlamDivD := ScalarSuffixCertificate.QInterval.realContains_divPos
    (i := lambdaInterval) (j := d4LowInterval) (by norm_num [d4LowInterval]) hlam hd
  let e : ScalarSuffixCertificate.CertificateExpr :=
    .mul (.rational 4)
      (.add
        (.mul (.rational h)
          (.add (.atom (1 / sqrt (1 - (h : ℝ) ^ 2))
                    (u4LowInterval.recipPos (by norm_num [u4LowInterval])) hinvU)
            (.neg (.atom (lam / sqrt (lam ^ 2 - (h : ℝ) ^ 2))
                    (lambdaInterval.divPos d4LowInterval (by norm_num [d4LowInterval]))
                    hlamDivD))))
        (.neg (.add
          (.mul (.atom lam lambdaInterval hlam)
            (.atom (arccos ((h : ℝ) / lam)) acosRatioLowInterval hacos))
          (.atom (arcsin (h : ℝ)) asinH4LowInterval hasinH))))
  have he : e.value < 0 := by
    apply ScalarSuffixCertificate.CertificateExpr.value_neg_of_hi_neg
    norm_num [e, ScalarSuffixCertificate.CertificateExpr.enclosure,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.divPos, lambdaInterval, u4LowInterval,
      d4LowInterval, asinH4LowInterval, asinRatioLowInterval,
      acosRatioLowInterval, ScalarSuffixCertificate.piInterval, h, h4Interval]
  convert he using 1 <;>
    simp only [e, ScalarSuffixCertificate.CertificateExpr.value,
      LeanSuffixAnalytic.typeFourFold, LeanSuffixAnalytic.typeFourAngle, h] <;>
    ring

/-- The upper face of the exact box-0 type-(iv) slab has positive fold value,
uniformly over the whole exact lambda interval. -/
theorem typeFourFold_upperFace_pos {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    0 < LeanSuffixAnalytic.typeFourFold lam (h4Interval.hi : ℝ) := by
  let h : ℚ := h4Interval.hi
  have hu : u4HighInterval.RealContains (sqrt (1 - (h : ℝ) ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt
    · norm_num [u4HighInterval]
    · norm_num [u4HighInterval, h, h4Interval]
    · norm_num [u4HighInterval, h, h4Interval]
  have hd : d4HighInterval.RealContains (sqrt (lam ^ 2 - (h : ℝ) ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt
    · norm_num [d4HighInterval]
    · norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains] at hlam
      norm_num [d4HighInterval, h, h4Interval]
      nlinarith
    · norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains] at hlam
      norm_num [d4HighInterval, h, h4Interval]
      nlinarith
  have hasinH : asinH4HighInterval.RealContains (arcsin (h : ℝ)) := by
    apply QInterval.realContains_arcsin_of_taylor
    · norm_num [h, h4Interval]
    · constructor <;> constructor <;>
        norm_num [asinH4HighInterval] <;>
        have hp := Real.pi_gt_three <;> nlinarith
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinH4HighInterval, h, h4Interval,
        Nat.factorial]
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinH4HighInterval, h, h4Interval,
        Nat.factorial]
  have hlamLoPos : 0 < lambdaInterval.lo := by norm_num [lambdaInterval]
  have hratio : (ScalarSuffixCertificate.QInterval.divPos
      (LeanSuffixReflective.QInterval.point h) lambdaInterval hlamLoPos).RealContains
      ((h : ℝ) / lam) := by
    exact ScalarSuffixCertificate.QInterval.realContains_divPos hlamLoPos
      (LeanSuffixReflective.QInterval.realContains_point h (h : ℝ) |>.2 rfl) hlam
  have hasinRatio : asinRatioHighInterval.RealContains (arcsin ((h : ℝ) / lam)) := by
    apply ScalarSuffixCertificate.realContains_arcsin_of_sin_bounds
    · constructor
      · norm_num [h, h4Interval, lambdaInterval,
          ScalarSuffixCertificate.QInterval.divPos,
          ScalarSuffixCertificate.QInterval.recipPos,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point,
          LeanSuffixReflective.QInterval.RealContains] at hratio ⊢
        linarith [hratio.1]
      · norm_num [h, h4Interval, lambdaInterval,
          ScalarSuffixCertificate.QInterval.divPos,
          ScalarSuffixCertificate.QInterval.recipPos,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point,
          LeanSuffixReflective.QInterval.RealContains] at hratio ⊢
        linarith [hratio.2]
    · constructor <;> constructor <;>
        norm_num [asinRatioHighInterval] <;>
        have hp := Real.pi_gt_three <;> nlinarith
    · refine (ScalarSuffixCertificate.sinTaylor27Interval_sound
          asinRatioHighInterval.lo).2.trans ?_
      norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinRatioHighInterval,
        lambdaInterval, h, h4Interval,
        ScalarSuffixCertificate.QInterval.divPos,
        ScalarSuffixCertificate.QInterval.recipPos,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.point,
        LeanSuffixReflective.QInterval.RealContains, Nat.factorial] at hratio ⊢
      linarith [hratio.1]
    · have hupper : ((h : ℝ) / lam) ≤
          (ScalarSuffixCertificate.sinTaylor27Interval asinRatioHighInterval.hi).lo := by
        norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
          ScalarSuffixCertificate.sinTaylor27, asinRatioHighInterval,
          lambdaInterval, h, h4Interval,
          ScalarSuffixCertificate.QInterval.divPos,
          ScalarSuffixCertificate.QInterval.recipPos,
          ScalarSuffixCertificate.QInterval.mul,
          LeanSuffixReflective.QInterval.point,
          LeanSuffixReflective.QInterval.RealContains, Nat.factorial] at hratio ⊢
        linarith [hratio.2]
      exact hupper.trans
        (ScalarSuffixCertificate.sinTaylor27Interval_sound
          asinRatioHighInterval.hi).1
  have hacos : acosRatioHighInterval.RealContains (arccos ((h : ℝ) / lam)) := by
    exact ScalarSuffixCertificate.realContains_arccos_of_arcsin
      ScalarSuffixCertificate.piInterval_sound hasinRatio
  have hinvU := ScalarSuffixCertificate.QInterval.realContains_recipPos
    (i := u4HighInterval) (by norm_num [u4HighInterval]) hu
  have hlamDivD := ScalarSuffixCertificate.QInterval.realContains_divPos
    (i := lambdaInterval) (j := d4HighInterval) (by norm_num [d4HighInterval]) hlam hd
  let e : ScalarSuffixCertificate.CertificateExpr :=
    .mul (.rational 4)
      (.add
        (.mul (.rational h)
          (.add (.atom (1 / sqrt (1 - (h : ℝ) ^ 2))
                    (u4HighInterval.recipPos (by norm_num [u4HighInterval])) hinvU)
            (.neg (.atom (lam / sqrt (lam ^ 2 - (h : ℝ) ^ 2))
                    (lambdaInterval.divPos d4HighInterval (by norm_num [d4HighInterval]))
                    hlamDivD))))
        (.neg (.add
          (.mul (.atom lam lambdaInterval hlam)
            (.atom (arccos ((h : ℝ) / lam)) acosRatioHighInterval hacos))
          (.atom (arcsin (h : ℝ)) asinH4HighInterval hasinH))))
  have he : 0 < e.value := by
    apply ScalarSuffixCertificate.QInterval.positive_of_realContains e.sound
    norm_num [e, ScalarSuffixCertificate.CertificateExpr.enclosure,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.divPos, lambdaInterval, u4HighInterval,
      d4HighInterval, asinH4HighInterval, asinRatioHighInterval,
      acosRatioHighInterval, ScalarSuffixCertificate.piInterval, h, h4Interval]
  convert he using 1 <;>
    simp only [e, ScalarSuffixCertificate.CertificateExpr.value,
      LeanSuffixAnalytic.typeFourFold, LeanSuffixAnalytic.typeFourAngle, h] <;>
    ring

/-- Box-0 specialization of the centered type-(iv) area enclosure used by
`centered_type4`.  The endpoint interval is a conclusion of the generic
mean-value soundness theorem; only the center and derivative leaf enclosures
remain to be checked by exact arithmetic. -/
theorem typeFourArea_centered_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h4Interval.RealContains h)
    (base slope displacement : QInterval)
    (hbase : base.RealContains
      (LeanSuffixAnalytic.typeFourArea lam (h4Center : ℝ)))
    (hslope : ∀ x, h4Interval.RealContains x →
      slope.RealContains
        (LeanSuffixAnalytic.typeFourFold lam x / x ^ 3))
    (hdisplacement : displacement.RealContains (h - (h4Center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeFourArea lam h) :=
  CompactCellCertificate.typeFourArea_centered_enclosure
    lambdaInterval h4Interval h4Center hlam hh h4Center_mem
    (lambda_one_lt hlam) (fun hx => h4_slab_regular hx)
    base slope displacement hbase hslope hdisplacement

/-- Box-0 specialization of the centered type-(iv) perimeter enclosure. -/
theorem typeFourPerimeter_centered_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h4Interval.RealContains h)
    (base slope displacement : QInterval)
    (hbase : base.RealContains
      (LeanSuffixAnalytic.typeFourPerimeter lam (h4Center : ℝ)))
    (hslope : ∀ x, h4Interval.RealContains x →
      slope.RealContains
        (LeanSuffixAnalytic.typeFourFold lam x / x ^ 2))
    (hdisplacement : displacement.RealContains (h - (h4Center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeFourPerimeter lam h) :=
  CompactCellCertificate.typeFourPerimeter_centered_enclosure
    lambdaInterval h4Interval h4Center hlam hh h4Center_mem
    (lambda_one_lt hlam) (fun hx => h4_slab_regular hx)
    base slope displacement hbase hslope hdisplacement

/-- Box-0 specialization of the centered type-(iii) area enclosure used by
`centered_type3`. -/
theorem typeThreeArea_centered_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h3Interval.RealContains h)
    (base slope displacement : QInterval)
    (hbase : base.RealContains
      (LeanSuffixAnalytic.typeThreeArea lam (h3Center : ℝ)))
    (hslope : ∀ x, h3Interval.RealContains x →
      slope.RealContains
        (LeanSuffixAnalytic.typeThreeFold lam x / x ^ 3))
    (hdisplacement : displacement.RealContains (h - (h3Center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeThreeArea lam h) :=
  CompactCellCertificate.typeThreeArea_centered_enclosure
    lambdaInterval h3Interval h3Center hlam hh h3Center_mem
    (lambda_one_lt hlam) (fun hx => h3_slab_regular hx)
    base slope displacement hbase hslope hdisplacement

/-- Box-0 specialization of the centered type-(iii) perimeter enclosure. -/
theorem typeThreePerimeter_centered_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h3Interval.RealContains h)
    (base slope displacement : QInterval)
    (hbase : base.RealContains
      (LeanSuffixAnalytic.typeThreePerimeter lam (h3Center : ℝ)))
    (hslope : ∀ x, h3Interval.RealContains x →
      slope.RealContains
        (LeanSuffixAnalytic.typeThreeFold lam x / x ^ 2))
    (hdisplacement : displacement.RealContains (h - (h3Center : ℝ))) :
    (base.add (slope.mul displacement)).RealContains
      (LeanSuffixAnalytic.typeThreePerimeter lam h) :=
  CompactCellCertificate.typeThreePerimeter_centered_enclosure
    lambdaInterval h3Interval h3Center hlam hh h3Center_mem
    (lambda_one_lt hlam) (fun hx => h3_slab_regular hx)
    base slope displacement hbase hslope hdisplacement


/-- Any two type-(iv) fold roots lying in the exact box-0 root slab coincide. -/
theorem typeFourFold_root_unique_in_slab {lam h₁ h₂ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₁ : h4Interval.RealContains h₁)
    (hh₂ : h4Interval.RealContains h₂)
    (hz₁ : LeanSuffixAnalytic.typeFourFold lam h₁ = 0)
    (hz₂ : LeanSuffixAnalytic.typeFourFold lam h₂ = 0) :
    h₁ = h₂ :=
  LeanSuffixAnalytic.typeFourFold_zero_unique (lambda_one_lt hlam)
    (h4_slab_regular hh₁) (h4_slab_regular hh₂) hz₁ hz₂

/-- For every lambda in box 0, the exact recorded type-(iv) slab contains
exactly one stationary fold root.  Existence uses the two independently
Taylor-checked face signs above; uniqueness is the exact analytic
strict-monotonicity theorem. -/
theorem typeFourFold_existsUnique_in_slab {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    ∃! h₄ : ℝ, h4Interval.RealContains h₄ ∧
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 := by
  let a : ℝ := h4Interval.lo
  let b : ℝ := h4Interval.hi
  have hab : a ≤ b := by
    simpa [a, b] using (show (h4Interval.lo : ℝ) ≤ h4Interval.hi by
      exact_mod_cast h4Interval.ordered)
  have hcont : ContinuousOn (LeanSuffixAnalytic.typeFourFold lam) (Icc a b) := by
    intro h hh
    have hhSlab : h4Interval.RealContains h := by
      simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh
    have hhReg := h4_slab_regular hhSlab
    exact (LeanSuffixAnalytic.hasDerivAt_typeFourFold
      (lambda_one_lt hlam) hhReg.1 hhReg.2).continuousAt.continuousWithinAt
  rcases ScalarSuffixCertificate.oppositeFace_zero hab hcont
      (typeFourFold_lowerFace_neg hlam).le
      (typeFourFold_upperFace_pos hlam).le with ⟨h₄, hh₄, hzero⟩
  have hhSlab : h4Interval.RealContains h₄ := by
    simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh₄
  refine ⟨h₄, ⟨hhSlab, hzero⟩, ?_⟩
  intro y hy
  exact typeFourFold_root_unique_in_slab hlam hy.1 hhSlab hy.2 hzero

/-- A fully concrete centered mean-value consequence for box 0: the
independently proved stationary root has an exact correlated area witness
between the checker midpoint and the root.  No numerical enclosure is assumed
in this statement. -/
theorem typeFourFold_root_centered_area_witness {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    ∃ h₄ ξ : ℝ,
      h4Interval.RealContains h₄ ∧
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 ∧
      ξ ∈ uIcc (h4Center : ℝ) h₄ ∧
      LeanSuffixAnalytic.typeFourArea lam h₄ =
        LeanSuffixAnalytic.typeFourArea lam (h4Center : ℝ) +
          LeanSuffixAnalytic.typeFourFold lam ξ / ξ ^ 3 *
            (h₄ - (h4Center : ℝ)) := by
  rcases typeFourFold_existsUnique_in_slab hlam with
    ⟨h₄, ⟨hh₄, hzero⟩, _⟩
  have hcReg := h4_slab_regular h4Center_mem
  have hhReg := h4_slab_regular hh₄
  rcases LeanSuffixAnalytic.typeFourArea_centered_meanValue
      (lambda_one_lt hlam) hcReg hhReg with ⟨ξ, hξ, hmean⟩
  exact ⟨h₄, ξ, hh₄, hzero, hξ, hmean⟩


private theorem typeThreeCell_atoms {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h3Interval.RealContains h) :
    u3CellInterval.RealContains
        (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      d3CellInterval.RealContains
        (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQ3CellInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRatio3CellInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)) := by
  let qI : QInterval :=
    (h3Interval.nsmul 2 (by norm_num)).sub
      (LeanSuffixReflective.QInterval.point 1)
  have hq : qI.RealContains (LeanSuffixAnalytic.typeThreeShape h) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_nsmul (by norm_num) hh)
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
  have hu : u3CellInterval.RealContains
      (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt
    · norm_num [u3CellInterval]
    · norm_num [qI, h3Interval, u3CellInterval,
        LeanSuffixReflective.QInterval.RealContains,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point] at hq ⊢
      nlinarith
    · norm_num [qI, h3Interval, u3CellInterval,
        LeanSuffixReflective.QInterval.RealContains,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point] at hq ⊢
      nlinarith
  have hd : d3CellInterval.RealContains
      (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) := by
    apply ScalarSuffixCertificate.QInterval.realContains_sqrt
    · norm_num [d3CellInterval]
    · norm_num [lambdaInterval, qI, h3Interval, d3CellInterval,
        LeanSuffixReflective.QInterval.RealContains,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point] at hlam hq ⊢
      nlinarith
    · norm_num [lambdaInterval, qI, h3Interval, d3CellInterval,
        LeanSuffixReflective.QInterval.RealContains,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point] at hlam hq ⊢
      nlinarith
  have hasinQ : asinQ3CellInterval.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape h)) := by
    apply realContains_arcsin_of_taylor_interval asinQ3CellInterval qI _ hq
    · constructor
      · exact (show (-1 : ℝ) ≤ (qI.lo : ℝ) by
          norm_num [qI, h3Interval, LeanSuffixReflective.QInterval.nsmul,
            LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
            LeanSuffixReflective.QInterval.neg,
            LeanSuffixReflective.QInterval.point]).trans hq.1
      · exact hq.2.trans (show (qI.hi : ℝ) ≤ 1 by
          norm_num [qI, h3Interval, LeanSuffixReflective.QInterval.nsmul,
            LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
            LeanSuffixReflective.QInterval.neg,
            LeanSuffixReflective.QInterval.point])
    · constructor <;> constructor <;>
        norm_num [asinQ3CellInterval] <;>
        have hp := Real.pi_gt_three <;> nlinarith
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinQ3CellInterval, qI, h3Interval,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point, Nat.factorial]
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinQ3CellInterval, qI, h3Interval,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point, Nat.factorial]
  have hlamLoPos : 0 < lambdaInterval.lo := by norm_num [lambdaInterval]
  have hratio : (ScalarSuffixCertificate.QInterval.divPos qI lambdaInterval
      hlamLoPos).RealContains (LeanSuffixAnalytic.typeThreeShape h / lam) :=
    ScalarSuffixCertificate.QInterval.realContains_divPos hlamLoPos hq hlam
  have hasinRatio : asinRatio3CellInterval.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)) := by
    apply realContains_arcsin_of_taylor_interval asinRatio3CellInterval
      (ScalarSuffixCertificate.QInterval.divPos qI lambdaInterval hlamLoPos) _
      hratio
    · constructor
      · exact (show (-1 : ℝ) ≤
            ((ScalarSuffixCertificate.QInterval.divPos qI lambdaInterval
              hlamLoPos).lo : ℝ) by
          norm_num [lambdaInterval, qI, h3Interval,
            ScalarSuffixCertificate.QInterval.divPos,
            ScalarSuffixCertificate.QInterval.recipPos,
            ScalarSuffixCertificate.QInterval.mul,
            LeanSuffixReflective.QInterval.nsmul,
            LeanSuffixReflective.QInterval.sub,
            LeanSuffixReflective.QInterval.add,
            LeanSuffixReflective.QInterval.neg,
            LeanSuffixReflective.QInterval.point]).trans hratio.1
      · exact hratio.2.trans (show
            ((ScalarSuffixCertificate.QInterval.divPos qI lambdaInterval
              hlamLoPos).hi : ℝ) ≤ 1 by
          norm_num [lambdaInterval, qI, h3Interval,
            ScalarSuffixCertificate.QInterval.divPos,
            ScalarSuffixCertificate.QInterval.recipPos,
            ScalarSuffixCertificate.QInterval.mul,
            LeanSuffixReflective.QInterval.nsmul,
            LeanSuffixReflective.QInterval.sub,
            LeanSuffixReflective.QInterval.add,
            LeanSuffixReflective.QInterval.neg,
            LeanSuffixReflective.QInterval.point])
    · constructor <;> constructor <;>
        norm_num [asinRatio3CellInterval] <;>
        have hp := Real.pi_gt_three <;> nlinarith
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinRatio3CellInterval,
        lambdaInterval, qI, h3Interval,
        ScalarSuffixCertificate.QInterval.divPos,
        ScalarSuffixCertificate.QInterval.recipPos,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point, Nat.factorial]
    · norm_num [ScalarSuffixCertificate.sinTaylor27Interval,
        ScalarSuffixCertificate.sinTaylor27, asinRatio3CellInterval,
        lambdaInterval, qI, h3Interval,
        ScalarSuffixCertificate.QInterval.divPos,
        ScalarSuffixCertificate.QInterval.recipPos,
        ScalarSuffixCertificate.QInterval.mul,
        LeanSuffixReflective.QInterval.nsmul,
        LeanSuffixReflective.QInterval.sub,
        LeanSuffixReflective.QInterval.add,
        LeanSuffixReflective.QInterval.neg,
        LeanSuffixReflective.QInterval.point, Nat.factorial]
  exact ⟨hu, hd, hasinQ, hasinRatio⟩

private theorem typeThree_atoms_of_exact_bounds
    (hI uI dI asinQI asinRatioI : QInterval)
    {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hqNonneg : 0 ≤
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo)
    (hqLeOne :
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ≤ 1)
    (huNonneg : 0 ≤ uI.lo)
    (huLower : uI.lo ^ 2 ≤ 1 -
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ^ 2)
    (huUpper : 1 -
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ uI.hi ^ 2)
    (hdNonneg : 0 ≤ dI.lo)
    (hdLower : dI.lo ^ 2 ≤ lambdaInterval.lo ^ 2 -
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ^ 2)
    (hdUpper : lambdaInterval.hi ^ 2 -
      ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ dI.hi ^ 2)
    (hasinQBranch : 0 ≤ asinQI.lo ∧
      asinQI.hi ≤ CompactCellCertificate.halfPiBox.lo)
    (hasinQLower :
      (ScalarSuffixCertificate.sinTaylor27Interval asinQI.lo).hi ≤
        ((hI.nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1)).lo)
    (hasinQUpper :
      ((hI.nsmul 2 (by norm_num)).sub
          (LeanSuffixReflective.QInterval.point 1)).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinQI.hi).lo)
    (hasinRatioBranch : 0 ≤ asinRatioI.lo ∧
      asinRatioI.hi ≤ CompactCellCertificate.halfPiBox.lo)
    (hasinRatioLower :
      (ScalarSuffixCertificate.sinTaylor27Interval asinRatioI.lo).hi ≤
        (ScalarSuffixCertificate.QInterval.divPos
          ((hI.nsmul 2 (by norm_num)).sub
            (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval])).lo)
    (hasinRatioUpper :
      (ScalarSuffixCertificate.QInterval.divPos
          ((hI.nsmul 2 (by norm_num)).sub
            (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval])).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinRatioI.hi).lo) :
    uI.RealContains
        (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      dI.RealContains
        (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQI.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRatioI.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)) :=
  CompactCellCertificate.typeThree_atoms_of_exact_bounds
    lambdaInterval hI uI dI asinQI asinRatioI hlam hh
    (by norm_num [lambdaInterval]) (lambda_one_lt hlam)
    hqNonneg hqLeOne huNonneg huLower huUpper hdNonneg hdLower hdUpper
    hasinQBranch hasinQLower hasinQUpper hasinRatioBranch
    hasinRatioLower hasinRatioUpper

private theorem typeThreeLower_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u3LowerInterval.RealContains
        (sqrt (1 - LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ) ^ 2)) ∧
      d3LowerInterval.RealContains
        (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ) ^ 2)) ∧
      asinQ3LowerInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ))) ∧
      asinRatio3LowerInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ) / lam)) := by
  apply typeThree_atoms_of_exact_bounds
    (LeanSuffixReflective.QInterval.point h3Interval.lo)
    u3LowerInterval d3LowerInterval asinQ3LowerInterval asinRatio3LowerInterval
    hlam <;>
    norm_num [h3Interval, lambdaInterval, u3LowerInterval, d3LowerInterval,
      asinQ3LowerInterval, asinRatio3LowerInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial]

private theorem typeThreeUpper_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u3UpperInterval.RealContains
        (sqrt (1 - LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ) ^ 2)) ∧
      d3UpperInterval.RealContains
        (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ) ^ 2)) ∧
      asinQ3UpperInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ))) ∧
      asinRatio3UpperInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ) / lam)) := by
  apply typeThree_atoms_of_exact_bounds
    (LeanSuffixReflective.QInterval.point h3Interval.hi)
    u3UpperInterval d3UpperInterval asinQ3UpperInterval asinRatio3UpperInterval
    hlam <;>
    norm_num [h3Interval, lambdaInterval, u3UpperInterval, d3UpperInterval,
      asinQ3UpperInterval, asinRatio3UpperInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial]

private theorem typeThreeCenter_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u3CenterInterval.RealContains
        (sqrt (1 - LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ) ^ 2)) ∧
      d3CenterInterval.RealContains
        (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ) ^ 2)) ∧
      asinQ3CenterInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ))) ∧
      asinRatio3CenterInterval.RealContains
        (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ) / lam)) := by
  apply typeThree_atoms_of_exact_bounds
    (LeanSuffixReflective.QInterval.point h3Center)
    u3CenterInterval d3CenterInterval asinQ3CenterInterval asinRatio3CenterInterval
    hlam <;>
    norm_num [h3Center, h3Interval, lambdaInterval, u3CenterInterval,
      d3CenterInterval, asinQ3CenterInterval, asinRatio3CenterInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial]

private theorem typeFourCell_atoms {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h4Interval.RealContains h) :
    u4CellInterval.RealContains (sqrt (1 - h ^ 2)) ∧
      d4CellInterval.RealContains (sqrt (lam ^ 2 - h ^ 2)) ∧
      asinH4CellInterval.RealContains (arcsin h) ∧
      asinRatio4CellInterval.RealContains (arcsin (h / lam)) := by
  let shifted : QInterval :=
    (h4Interval.add (LeanSuffixReflective.QInterval.point 1)).nsmul
      (1 / 2) (by norm_num)
  have ht : shifted.RealContains ((h + 1) / 2) := by
    have hadd := LeanSuffixReflective.QInterval.realContains_add hh
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
    convert ScalarSuffixCertificate.QInterval.realContains_nsmul
      (q := (1 / 2 : ℚ)) (by norm_num) hadd using 1 <;> ring
  have ha := typeThree_atoms_of_exact_bounds shifted
    u4CellInterval d4CellInterval asinH4CellInterval asinRatio4CellInterval
    hlam ht
    (by norm_num [shifted, h4Interval, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point])
    (by norm_num [shifted, h4Interval, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point])
    (by norm_num [u4CellInterval])
    (by norm_num [shifted, h4Interval, u4CellInterval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [shifted, h4Interval, u4CellInterval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [d4CellInterval])
    (by norm_num [shifted, h4Interval, lambdaInterval, d4CellInterval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [shifted, h4Interval, lambdaInterval, d4CellInterval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [asinH4CellInterval])
    (by norm_num [shifted, h4Interval, asinH4CellInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial])
    (by norm_num [shifted, h4Interval, asinH4CellInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial])
    (by norm_num [asinRatio4CellInterval])
    (by norm_num [shifted, h4Interval, lambdaInterval, asinRatio4CellInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])
    (by norm_num [shifted, h4Interval, lambdaInterval, asinRatio4CellInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])
  have hs : LeanSuffixAnalytic.typeThreeShape ((h + 1) / 2) = h := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  simpa [hs] using ha

private theorem typeFourCenter_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u4CenterInterval.RealContains (sqrt (1 - (h4Center : ℝ) ^ 2)) ∧
      d4CenterInterval.RealContains (sqrt (lam ^ 2 - (h4Center : ℝ) ^ 2)) ∧
      asinH4CenterInterval.RealContains (arcsin (h4Center : ℝ)) ∧
      asinRatio4CenterInterval.RealContains
        (arcsin ((h4Center : ℝ) / lam)) := by
  have hh := h4Center_mem
  let shifted : QInterval :=
    LeanSuffixReflective.QInterval.point ((h4Center + 1) / 2)
  have ht : shifted.RealContains (((h4Center : ℝ) + 1) / 2) := by
    norm_num [shifted, LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.point]
  have ha := typeThree_atoms_of_exact_bounds shifted
    u4CenterInterval d4CenterInterval asinH4CenterInterval
    asinRatio4CenterInterval hlam ht
    (by norm_num [shifted, h4Center, h4Interval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [shifted, h4Center, h4Interval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [u4CenterInterval])
    (by norm_num [shifted, h4Center, h4Interval, u4CenterInterval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [shifted, h4Center, h4Interval, u4CenterInterval,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [d4CenterInterval])
    (by norm_num [shifted, h4Center, h4Interval, lambdaInterval,
      d4CenterInterval, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point])
    (by norm_num [shifted, h4Center, h4Interval, lambdaInterval,
      d4CenterInterval, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point])
    (by norm_num [asinH4CenterInterval])
    (by norm_num [shifted, h4Center, h4Interval, asinH4CenterInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial])
    (by norm_num [shifted, h4Center, h4Interval, asinH4CenterInterval,
      ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
      LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
      Nat.factorial])
    (by norm_num [asinRatio4CenterInterval])
    (by norm_num [shifted, h4Center, h4Interval, lambdaInterval,
      asinRatio4CenterInterval, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])
    (by norm_num [shifted, h4Center, h4Interval, lambdaInterval,
      asinRatio4CenterInterval, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])
  have hs : LeanSuffixAnalytic.typeThreeShape
      (((h4Center : ℝ) + 1) / 2) = (h4Center : ℝ) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    ring
  simpa [hs] using ha

private def typeThreeFoldCellInterval : QInterval :=
  ⟨-5233379 / 1000000, -4039328 / 1000000, by norm_num⟩

/-- Exact atom enclosure for the type-(iii) fold numerator on the whole box-0
height slab. -/
theorem typeThreeFold_cell_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h3Interval.RealContains h) :
    typeThreeFoldCellInterval.RealContains
      (LeanSuffixAnalytic.typeThreeFold lam h) := by
  rcases typeThreeCell_atoms hlam hh with ⟨hu, hd, hasinQ, hasinRatio⟩
  let qI : QInterval :=
    (h3Interval.nsmul 2 (by norm_num)).sub
      (LeanSuffixReflective.QInterval.point 1)
  have hq : qI.RealContains (LeanSuffixAnalytic.typeThreeShape h) := by
    unfold LeanSuffixAnalytic.typeThreeShape
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_nsmul (by norm_num) hh)
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
  let halfPi : QInterval :=
    ScalarSuffixCertificate.piInterval.nsmul (1 / 2) (by norm_num)
  have hhalfPi : halfPi.RealContains (π / 2) := by
    convert ScalarSuffixCertificate.QInterval.realContains_nsmul
      (q := (1 / 2 : ℚ)) (by norm_num)
      ScalarSuffixCertificate.piInterval_sound using 1 <;> ring
  let acosI : QInterval := halfPi.sub asinRatio3CellInterval
  have hacos : acosI.RealContains
      (arccos (LeanSuffixAnalytic.typeThreeShape h / lam)) := by
    exact ScalarSuffixCertificate.realContains_arccos_of_arcsin
      ScalarSuffixCertificate.piInterval_sound hasinRatio
  have hangle : (lambdaInterval.mul acosI).add asinQ3CellInterval |>.RealContains
      (LeanSuffixAnalytic.typeThreeAngle lam h) := by
    unfold LeanSuffixAnalytic.typeThreeAngle
    exact LeanSuffixReflective.QInterval.realContains_add
      (ScalarSuffixCertificate.QInterval.realContains_mul hlam hacos) hasinQ
  have hlamPos : 0 < lambdaInterval.lo := by norm_num [lambdaInterval]
  have huPos : 0 < u3CellInterval.lo := by norm_num [u3CellInterval]
  have hdPos : 0 < d3CellInterval.lo := by norm_num [d3CellInterval]
  have hdelta :
      ((d3CellInterval.divPos lambdaInterval hlamPos).sub u3CellInterval).RealContains
        (LeanSuffixAnalytic.typeThreeDelta lam h) := by
    unfold LeanSuffixAnalytic.typeThreeDelta
    exact LeanSuffixReflective.QInterval.realContains_sub
      (ScalarSuffixCertificate.QInterval.realContains_divPos hlamPos hd hlam) hu
  have hnumOne :
      ((LeanSuffixReflective.QInterval.point 1).add qI).RealContains
        (1 + LeanSuffixAnalytic.typeThreeShape h) :=
    LeanSuffixReflective.QInterval.realContains_add
      (LeanSuffixReflective.QInterval.realContains_point 1 (1 : ℝ) |>.2 (by norm_num))
      hq
  have hdivOne :=
    ScalarSuffixCertificate.QInterval.realContains_divPos huPos hnumOne hu
  have hlamSq := ScalarSuffixCertificate.QInterval.realContains_mul hlam hlam
  have hnumTwo :
      ((lambdaInterval.mul lambdaInterval).add qI).RealContains
        (lam ^ 2 + LeanSuffixAnalytic.typeThreeShape h) := by
    convert LeanSuffixReflective.QInterval.realContains_add hlamSq hq using 1 <;> ring
  have hlamD := ScalarSuffixCertificate.QInterval.realContains_mul hlam hd
  have hlamDPos : 0 < (lambdaInterval.mul d3CellInterval).lo := by
    norm_num [lambdaInterval, d3CellInterval,
      ScalarSuffixCertificate.QInterval.mul]
  have hdivTwo :=
    ScalarSuffixCertificate.QInterval.realContains_divPos hlamDPos hnumTwo hlamD
  let e : ScalarSuffixCertificate.CertificateExpr :=
    .add
      (.mul (.rational 4)
        (.mul (.atom h h3Interval hh)
          (.add
            (.atom
              ((1 + LeanSuffixAnalytic.typeThreeShape h) /
                sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2))
              (ScalarSuffixCertificate.QInterval.divPos
                ((LeanSuffixReflective.QInterval.point 1).add qI)
                u3CellInterval huPos) hdivOne)
            (.neg (.atom
              ((lam ^ 2 + LeanSuffixAnalytic.typeThreeShape h) /
                (lam * sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)))
              (ScalarSuffixCertificate.QInterval.divPos
                ((lambdaInterval.mul lambdaInterval).add qI)
                (lambdaInterval.mul d3CellInterval) hlamDPos) hdivTwo)))))
      (.neg (.mul (.rational 2)
        (.add
          (.add
            (.atom (LeanSuffixAnalytic.typeThreeAngle lam h)
              ((lambdaInterval.mul acosI).add asinQ3CellInterval) hangle)
            (.atom (π / 2) halfPi hhalfPi))
          (.atom (LeanSuffixAnalytic.typeThreeDelta lam h)
            ((d3CellInterval.divPos lambdaInterval hlamPos).sub u3CellInterval)
            hdelta))))
  have hv : e.value = LeanSuffixAnalytic.typeThreeFold lam h := by
    simp only [e, ScalarSuffixCertificate.CertificateExpr.value,
      LeanSuffixAnalytic.typeThreeFold]
    ring
  rw [← hv]
  have he := e.sound
  norm_num [typeThreeFoldCellInterval, e,
    ScalarSuffixCertificate.CertificateExpr.enclosure,
    ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.point,
    LeanSuffixReflective.QInterval.nsmul, qI, halfPi, acosI, h3Interval,
    lambdaInterval, u3CellInterval, d3CellInterval, asinQ3CellInterval,
    asinRatio3CellInterval, ScalarSuffixCertificate.piInterval,
    LeanSuffixReflective.QInterval.RealContains] at he ⊢
  exact ⟨by linarith [he.1], by linarith [he.2]⟩

/-- The type-(iii) branch is genuinely descending on the whole exact box-0
height slab. -/
theorem typeThreeFold_neg_on_slab {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h3Interval.RealContains h) :
    LeanSuffixAnalytic.typeThreeFold lam h < 0 :=
  ScalarSuffixCertificate.QInterval.negative_of_realContains
    (typeThreeFold_cell_enclosure hlam hh)
    (by norm_num [typeThreeFoldCellInterval])

private def halfPiBox : QInterval := CompactCellCertificate.halfPiBox

private def typeThreeQBox (hI : QInterval) : QInterval :=
  CompactCellCertificate.typeThreeQBox hI

private def typeThreeAngleBox (asinQI asinRatioI : QInterval) : QInterval :=
  CompactCellCertificate.typeThreeAngleBox lambdaInterval asinQI asinRatioI

private def typeThreeDeltaBox (uI dI : QInterval) : QInterval :=
  CompactCellCertificate.typeThreeDeltaBox lambdaInterval uI dI
    (by norm_num [lambdaInterval])

private def typeThreeAreaBox (hI uI dI asinQI asinRatioI : QInterval)
    (hhSq : 0 < (hI.mul hI).lo) : QInterval :=
  CompactCellCertificate.typeThreeAreaBox lambdaInterval hI uI dI
    asinQI asinRatioI (by norm_num [lambdaInterval]) hhSq

private def typeThreePerimeterBox (hI uI dI asinQI asinRatioI : QInterval)
    (hh : 0 < hI.lo) : QInterval :=
  CompactCellCertificate.typeThreePerimeterBox lambdaInterval hI uI dI
    asinQI asinRatioI (by norm_num [lambdaInterval]) hh

private theorem typeThree_area_perimeter_atom_enclosure
    (hI uI dI asinQI asinRatioI : QInterval)
    {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hatoms :
      uI.RealContains
          (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
        dI.RealContains
          (sqrt (lam ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
        asinQI.RealContains
          (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
        asinRatioI.RealContains
          (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)))
    (hhPos : 0 < hI.lo)
    (hhSq : 0 < (hI.mul hI).lo) :
    (typeThreeAreaBox hI uI dI asinQI asinRatioI hhSq).RealContains
        (LeanSuffixAnalytic.typeThreeArea lam h) ∧
      (typeThreePerimeterBox hI uI dI asinQI asinRatioI hhPos).RealContains
        (LeanSuffixAnalytic.typeThreePerimeter lam h) :=
  CompactCellCertificate.typeThree_area_perimeter_atom_enclosure
    lambdaInterval hI uI dI asinQI asinRatioI hlam hh hatoms
    (by norm_num [lambdaInterval]) hhPos hhSq

private def typeThreeLowerAreaInterval : QInterval :=
  ⟨3774822 / 1000000, 3777383 / 1000000, by norm_num⟩

private def typeThreeUpperAreaInterval : QInterval :=
  ⟨3751888 / 1000000, 3754474 / 1000000, by norm_num⟩

private def typeThreeCenterPerimeterInterval : QInterval :=
  ⟨6911328 / 1000000, 6913788 / 1000000, by norm_num⟩

private theorem typeThreeArea_lower_enclosure {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    typeThreeLowerAreaInterval.RealContains
      (LeanSuffixAnalytic.typeThreeArea lam (h3Interval.lo : ℝ)) := by
  have henc := typeThree_area_perimeter_atom_enclosure
    (LeanSuffixReflective.QInterval.point h3Interval.lo)
    u3LowerInterval d3LowerInterval asinQ3LowerInterval asinRatio3LowerInterval
    hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Interval.lo
      (h3Interval.lo : ℝ) |>.2 rfl)
    (typeThreeLower_atoms hlam)
    (by norm_num [h3Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
  rcases henc with ⟨harea, _⟩
  norm_num [typeThreeLowerAreaInterval, typeThreeAreaBox, typeThreeAngleBox,
    typeThreeDeltaBox, typeThreeQBox, halfPiBox, h3Interval, lambdaInterval,
    CompactCellCertificate.typeThreeAreaBox,
    CompactCellCertificate.typeThreeAngleBox,
    CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    u3LowerInterval, d3LowerInterval, asinQ3LowerInterval,
    asinRatio3LowerInterval, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at harea ⊢
  exact ⟨by linarith [harea.1], by linarith [harea.2]⟩

private theorem typeThreeArea_upper_enclosure {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    typeThreeUpperAreaInterval.RealContains
      (LeanSuffixAnalytic.typeThreeArea lam (h3Interval.hi : ℝ)) := by
  have henc := typeThree_area_perimeter_atom_enclosure
    (LeanSuffixReflective.QInterval.point h3Interval.hi)
    u3UpperInterval d3UpperInterval asinQ3UpperInterval asinRatio3UpperInterval
    hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Interval.hi
      (h3Interval.hi : ℝ) |>.2 rfl)
    (typeThreeUpper_atoms hlam)
    (by norm_num [h3Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
  rcases henc with ⟨harea, _⟩
  norm_num [typeThreeUpperAreaInterval, typeThreeAreaBox, typeThreeAngleBox,
    typeThreeDeltaBox, typeThreeQBox, halfPiBox, h3Interval, lambdaInterval,
    CompactCellCertificate.typeThreeAreaBox,
    CompactCellCertificate.typeThreeAngleBox,
    CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    u3UpperInterval, d3UpperInterval, asinQ3UpperInterval,
    asinRatio3UpperInterval, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at harea ⊢
  exact ⟨by linarith [harea.1], by linarith [harea.2]⟩

private theorem typeThreePerimeter_center_enclosure {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    typeThreeCenterPerimeterInterval.RealContains
      (LeanSuffixAnalytic.typeThreePerimeter lam (h3Center : ℝ)) := by
  have henc := typeThree_area_perimeter_atom_enclosure
    (LeanSuffixReflective.QInterval.point h3Center)
    u3CenterInterval d3CenterInterval asinQ3CenterInterval asinRatio3CenterInterval
    hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Center
      (h3Center : ℝ) |>.2 rfl)
    (typeThreeCenter_atoms hlam)
    (by norm_num [h3Center, h3Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3Center, h3Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
  rcases henc with ⟨_, hperimeter⟩
  norm_num [typeThreeCenterPerimeterInterval, typeThreePerimeterBox,
    typeThreeAngleBox, typeThreeDeltaBox, typeThreeQBox, halfPiBox,
    CompactCellCertificate.typeThreePerimeterBox,
    CompactCellCertificate.typeThreeAngleBox,
    CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    h3Center, h3Interval, lambdaInterval, u3CenterInterval, d3CenterInterval,
    asinQ3CenterInterval, asinRatio3CenterInterval,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at hperimeter ⊢
  exact ⟨by linarith [hperimeter.1], by linarith [hperimeter.2]⟩

private def typeFourAngleBox (asinHI asinRatioI : QInterval) : QInterval :=
  CompactCellCertificate.typeFourAngleBox lambdaInterval asinHI asinRatioI

private def typeFourDeltaBox (uI dI : QInterval) : QInterval :=
  CompactCellCertificate.typeFourDeltaBox lambdaInterval uI dI
    (by norm_num [lambdaInterval])

private def typeFourAreaBox (hI uI dI asinHI asinRatioI : QInterval)
    (hhSq : 0 < (hI.mul hI).lo) : QInterval :=
  CompactCellCertificate.typeFourAreaBox lambdaInterval hI uI dI
    asinHI asinRatioI (by norm_num [lambdaInterval]) hhSq

private def typeFourPerimeterBox (hI asinHI asinRatioI : QInterval)
    (hh : 0 < hI.lo) : QInterval :=
  CompactCellCertificate.typeFourPerimeterBox lambdaInterval hI
    asinHI asinRatioI hh

private def typeFourFoldBox (hI uI dI asinHI asinRatioI : QInterval)
    (hu : 0 < uI.lo) (hd : 0 < dI.lo) : QInterval :=
  CompactCellCertificate.typeFourFoldBox lambdaInterval hI uI dI
    asinHI asinRatioI (by norm_num [lambdaInterval]) hu hd

private theorem typeFour_atom_enclosures
    (hI uI dI asinHI asinRatioI : QInterval)
    {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : hI.RealContains h)
    (hatoms :
      uI.RealContains (sqrt (1 - h ^ 2)) ∧
        dI.RealContains (sqrt (lam ^ 2 - h ^ 2)) ∧
        asinHI.RealContains (arcsin h) ∧
        asinRatioI.RealContains (arcsin (h / lam)))
    (hhPos : 0 < hI.lo)
    (hhSq : 0 < (hI.mul hI).lo)
    (huPos : 0 < uI.lo)
    (hdPos : 0 < dI.lo) :
    (typeFourAreaBox hI uI dI asinHI asinRatioI hhSq).RealContains
        (LeanSuffixAnalytic.typeFourArea lam h) ∧
      (typeFourPerimeterBox hI asinHI asinRatioI hhPos).RealContains
        (LeanSuffixAnalytic.typeFourPerimeter lam h) ∧
      (typeFourFoldBox hI uI dI asinHI asinRatioI huPos hdPos).RealContains
        (LeanSuffixAnalytic.typeFourFold lam h) :=
  CompactCellCertificate.typeFour_atom_enclosures
    lambdaInterval hI uI dI asinHI asinRatioI hlam hh hatoms
    (by norm_num [lambdaInterval]) hhPos hhSq huPos hdPos

private def typeFourFoldCellInterval : QInterval :=
  ⟨-58700 / 1000000, 58800 / 1000000, by norm_num⟩

private def typeFourCenterAreaInterval : QInterval :=
  ⟨3762750 / 1000000, 3766227 / 1000000, by norm_num⟩

private def typeFourCenterPerimeterInterval : QInterval :=
  ⟨6926135 / 1000000, 6929555 / 1000000, by norm_num⟩

private theorem typeFourFold_cell_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h4Interval.RealContains h) :
    typeFourFoldCellInterval.RealContains
      (LeanSuffixAnalytic.typeFourFold lam h) := by
  have henc := typeFour_atom_enclosures h4Interval u4CellInterval d4CellInterval
    asinH4CellInterval asinRatio4CellInterval hlam hh
    (typeFourCell_atoms hlam hh)
    (by norm_num [h4Interval])
    (by norm_num [h4Interval, ScalarSuffixCertificate.QInterval.mul])
    (by norm_num [u4CellInterval])
    (by norm_num [d4CellInterval])
  rcases henc with ⟨_, _, hfold⟩
  norm_num [typeFourFoldCellInterval, typeFourFoldBox, typeFourAngleBox,
    halfPiBox, h4Interval, lambdaInterval, u4CellInterval, d4CellInterval,
    CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    asinH4CellInterval, asinRatio4CellInterval,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at hfold ⊢
  exact ⟨by linarith [hfold.1], by linarith [hfold.2]⟩

private theorem typeFour_center_enclosures {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    typeFourCenterAreaInterval.RealContains
        (LeanSuffixAnalytic.typeFourArea lam (h4Center : ℝ)) ∧
      typeFourCenterPerimeterInterval.RealContains
        (LeanSuffixAnalytic.typeFourPerimeter lam (h4Center : ℝ)) := by
  have henc := typeFour_atom_enclosures
    (LeanSuffixReflective.QInterval.point h4Center)
    u4CenterInterval d4CenterInterval asinH4CenterInterval asinRatio4CenterInterval
    hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Center
      (h4Center : ℝ) |>.2 rfl)
    (typeFourCenter_atoms hlam)
    (by norm_num [h4Center, h4Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4Center, h4Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
    (by norm_num [u4CenterInterval])
    (by norm_num [d4CenterInterval])
  rcases henc with ⟨harea, hperimeter, _⟩
  constructor
  · norm_num [typeFourCenterAreaInterval, typeFourAreaBox, typeFourAngleBox,
      typeFourDeltaBox, halfPiBox, h4Center, h4Interval, lambdaInterval,
      CompactCellCertificate.typeFourAreaBox,
      CompactCellCertificate.typeFourAngleBox,
      CompactCellCertificate.typeFourDeltaBox,
      CompactCellCertificate.halfPiBox,
      u4CenterInterval, d4CenterInterval, asinH4CenterInterval,
      asinRatio4CenterInterval, ScalarSuffixCertificate.piInterval,
      ScalarSuffixCertificate.QInterval.mul,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.point] at harea ⊢
    exact ⟨by linarith [harea.1], by linarith [harea.2]⟩
  · norm_num [typeFourCenterPerimeterInterval, typeFourPerimeterBox,
      typeFourAngleBox, halfPiBox, h4Center, h4Interval, lambdaInterval,
      CompactCellCertificate.typeFourPerimeterBox,
      CompactCellCertificate.typeFourAngleBox,
      CompactCellCertificate.halfPiBox,
      asinH4CenterInterval, asinRatio4CenterInterval,
      ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
      ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos,
      LeanSuffixReflective.QInterval.RealContains,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
      LeanSuffixReflective.QInterval.point] at hperimeter ⊢
    exact ⟨by linarith [hperimeter.1], by linarith [hperimeter.2]⟩

private def h4SquareInterval : QInterval :=
  h4Interval.mul h4Interval

private def h4CubeInterval : QInterval :=
  h4SquareInterval.mul h4Interval

private def h4DisplacementInterval : QInterval :=
  h4Interval.sub (LeanSuffixReflective.QInterval.point h4Center)

private def typeFourAreaSlopeInterval : QInterval :=
  typeFourFoldCellInterval.divPos h4CubeInterval
    (by norm_num [h4CubeInterval, h4SquareInterval, h4Interval,
      ScalarSuffixCertificate.QInterval.mul])

private def typeFourPerimeterSlopeInterval : QInterval :=
  typeFourFoldCellInterval.divPos h4SquareInterval
    (by norm_num [h4SquareInterval, h4Interval,
      ScalarSuffixCertificate.QInterval.mul])

private def typeFourAreaCenteredInterval : QInterval :=
  typeFourCenterAreaInterval.add
    (typeFourAreaSlopeInterval.mul h4DisplacementInterval)

private def typeFourPerimeterCenteredInterval : QInterval :=
  typeFourCenterPerimeterInterval.add
    (typeFourPerimeterSlopeInterval.mul h4DisplacementInterval)

private theorem typeFour_centered_enclosures {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h4Interval.RealContains h) :
    typeFourAreaCenteredInterval.RealContains
        (LeanSuffixAnalytic.typeFourArea lam h) ∧
      typeFourPerimeterCenteredInterval.RealContains
        (LeanSuffixAnalytic.typeFourPerimeter lam h) := by
  have hcenter := typeFour_center_enclosures hlam
  have hdisp : h4DisplacementInterval.RealContains (h - (h4Center : ℝ)) := by
    exact LeanSuffixReflective.QInterval.realContains_sub hh
      (LeanSuffixReflective.QInterval.realContains_point h4Center
        (h4Center : ℝ) |>.2 rfl)
  have hslopeArea : ∀ x, h4Interval.RealContains x →
      typeFourAreaSlopeInterval.RealContains
        (LeanSuffixAnalytic.typeFourFold lam x / x ^ 3) := by
    intro x hx
    have hsq := ScalarSuffixCertificate.QInterval.realContains_mul hx hx
    have hcube := ScalarSuffixCertificate.QInterval.realContains_mul hsq hx
    have hfold := typeFourFold_cell_enclosure hlam hx
    convert ScalarSuffixCertificate.QInterval.realContains_divPos
      (i := typeFourFoldCellInterval) (j := h4CubeInterval)
      (by norm_num [h4CubeInterval, h4SquareInterval, h4Interval,
        ScalarSuffixCertificate.QInterval.mul]) hfold hcube using 1 <;>
      first | rfl | ring
  have hslopePerimeter : ∀ x, h4Interval.RealContains x →
      typeFourPerimeterSlopeInterval.RealContains
        (LeanSuffixAnalytic.typeFourFold lam x / x ^ 2) := by
    intro x hx
    have hsq := ScalarSuffixCertificate.QInterval.realContains_mul hx hx
    have hfold := typeFourFold_cell_enclosure hlam hx
    convert ScalarSuffixCertificate.QInterval.realContains_divPos
      (i := typeFourFoldCellInterval) (j := h4SquareInterval)
      (by norm_num [h4SquareInterval, h4Interval,
        ScalarSuffixCertificate.QInterval.mul]) hfold hsq using 1 <;>
      first | rfl | ring
  constructor
  · exact typeFourArea_centered_enclosure hlam hh
      typeFourCenterAreaInterval typeFourAreaSlopeInterval
      h4DisplacementInterval hcenter.1 hslopeArea hdisp
  · exact typeFourPerimeter_centered_enclosure hlam hh
      typeFourCenterPerimeterInterval typeFourPerimeterSlopeInterval
      h4DisplacementInterval hcenter.2 hslopePerimeter hdisp

private def h3SquareInterval : QInterval :=
  h3Interval.mul h3Interval

private def h3DisplacementInterval : QInterval :=
  h3Interval.sub (LeanSuffixReflective.QInterval.point h3Center)

private def typeThreePerimeterSlopeInterval : QInterval :=
  typeThreeFoldCellInterval.divPos h3SquareInterval
    (by norm_num [h3SquareInterval, h3Interval,
      ScalarSuffixCertificate.QInterval.mul])

private def typeThreePerimeterCenteredInterval : QInterval :=
  typeThreeCenterPerimeterInterval.add
    (typeThreePerimeterSlopeInterval.mul h3DisplacementInterval)

private theorem typeThreePerimeter_centered_cell_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh : h3Interval.RealContains h) :
    typeThreePerimeterCenteredInterval.RealContains
      (LeanSuffixAnalytic.typeThreePerimeter lam h) := by
  have hdisp : h3DisplacementInterval.RealContains (h - (h3Center : ℝ)) := by
    exact LeanSuffixReflective.QInterval.realContains_sub hh
      (LeanSuffixReflective.QInterval.realContains_point h3Center
        (h3Center : ℝ) |>.2 rfl)
  have hslope : ∀ x, h3Interval.RealContains x →
      typeThreePerimeterSlopeInterval.RealContains
        (LeanSuffixAnalytic.typeThreeFold lam x / x ^ 2) := by
    intro x hx
    have hsq := ScalarSuffixCertificate.QInterval.realContains_mul hx hx
    have hfold := typeThreeFold_cell_enclosure hlam hx
    convert ScalarSuffixCertificate.QInterval.realContains_divPos
      (i := typeThreeFoldCellInterval) (j := h3SquareInterval)
      (by norm_num [h3SquareInterval, h3Interval,
        ScalarSuffixCertificate.QInterval.mul]) hfold hsq using 1 <;>
      first | rfl | ring
  exact typeThreePerimeter_centered_enclosure hlam hh
    typeThreeCenterPerimeterInterval typeThreePerimeterSlopeInterval
    h3DisplacementInterval (typeThreePerimeter_center_enclosure hlam)
    hslope hdisp

/-- The lower type-(iii) face lies strictly above the stationary type-(iv)
area, uniformly on the exact lambda box. -/
theorem typeThreeArea_lowerFace_minus_stationaryTypeFour_pos
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h4Interval.RealContains h₄)
    (_hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0) :
    0 < LeanSuffixAnalytic.typeThreeArea lam (h3Interval.lo : ℝ) -
      LeanSuffixAnalytic.typeFourArea lam h₄ := by
  have hthree := typeThreeArea_lower_enclosure hlam
  have hfour := (typeFour_centered_enclosures hlam hh₄).1
  norm_num [typeThreeLowerAreaInterval, typeFourAreaCenteredInterval,
    typeFourCenterAreaInterval, typeFourAreaSlopeInterval,
    typeFourFoldCellInterval, h4CubeInterval, h4SquareInterval,
    h4DisplacementInterval, h4Interval, h4Center,
    ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.point]
    at hthree hfour ⊢
  linarith

/-- The upper type-(iii) face lies strictly below the stationary type-(iv)
area, uniformly on the exact lambda box. -/
theorem typeThreeArea_upperFace_minus_stationaryTypeFour_neg
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h4Interval.RealContains h₄)
    (_hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0) :
    LeanSuffixAnalytic.typeThreeArea lam (h3Interval.hi : ℝ) -
      LeanSuffixAnalytic.typeFourArea lam h₄ < 0 := by
  have hthree := typeThreeArea_upper_enclosure hlam
  have hfour := (typeFour_centered_enclosures hlam hh₄).1
  norm_num [typeThreeUpperAreaInterval, typeFourAreaCenteredInterval,
    typeFourCenterAreaInterval, typeFourAreaSlopeInterval,
    typeFourFoldCellInterval, h4CubeInterval, h4SquareInterval,
    h4DisplacementInterval, h4Interval, h4Center,
    ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.point]
    at hthree hfour ⊢
  linarith

/-- The centered perimeter boxes retain a strict gap everywhere in the two
recorded root slabs. -/
theorem typeThreePerimeter_minus_typeFour_neg
    {lam h₃ h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₃ : h3Interval.RealContains h₃)
    (hh₄ : h4Interval.RealContains h₄) :
    LeanSuffixAnalytic.typeThreePerimeter lam h₃ -
      LeanSuffixAnalytic.typeFourPerimeter lam h₄ < 0 := by
  have hthree := typeThreePerimeter_centered_cell_enclosure hlam hh₃
  have hfour := (typeFour_centered_enclosures hlam hh₄).2
  norm_num [typeThreePerimeterCenteredInterval,
    typeThreeCenterPerimeterInterval, typeThreePerimeterSlopeInterval,
    typeThreeFoldCellInterval, h3SquareInterval, h3DisplacementInterval,
    h3Interval, h3Center, typeFourPerimeterCenteredInterval,
    typeFourCenterPerimeterInterval, typeFourPerimeterSlopeInterval,
    typeFourFoldCellInterval, h4SquareInterval, h4DisplacementInterval,
    h4Interval, h4Center, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.point]
    at hthree hfour ⊢
  linarith

private theorem checkedConditions :
    CompactCellAssembly.Conditions lambdaInterval h3Interval h4Interval where
  lambda_one_lt := by
    intro lam hlam
    exact lambda_one_lt hlam
  h3_slab_regular := by
    intro h hh
    exact h3_slab_regular hh
  h3_slab_above_half := by
    intro h hh
    have hlo : (h3Interval.lo : ℝ) ≤ h := hh.1
    norm_num [h3Interval] at hlo ⊢
    linarith
  h4_slab_regular := by
    intro h hh
    exact h4_slab_regular hh
  typeFourFold_lowerFace_neg := by
    intro lam hlam
    exact typeFourFold_lowerFace_neg hlam
  typeFourFold_upperFace_pos := by
    intro lam hlam
    exact typeFourFold_upperFace_pos hlam
  typeThreeFold_neg_on_slab := by
    intro lam h hlam hh
    exact typeThreeFold_neg_on_slab hlam hh
  typeThreeArea_lowerFace_gap_pos := by
    intro lam h₄ hlam hh₄ hstationary
    exact typeThreeArea_lowerFace_minus_stationaryTypeFour_pos
      hlam hh₄ hstationary
  typeThreeArea_upperFace_gap_neg := by
    intro lam h₄ hlam hh₄ hstationary
    exact typeThreeArea_upperFace_minus_stationaryTypeFour_neg
      hlam hh₄ hstationary
  typeThreePerimeter_gap_neg := by
    intro lam h₃ h₄ hlam hh₃ hh₄
    exact typeThreePerimeter_minus_typeFour_neg hlam hh₃ hh₄

/-- For a stationary type-(iv) height in box 0, the descending type-(iii)
branch contains exactly one equal-area height. -/
theorem typeThreeEqualArea_existsUnique_in_slab
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h4Interval.RealContains h₄)
    (hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0) :
    ∃! h₃ : ℝ, h3Interval.RealContains h₃ ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ :=
  checkedConditions.typeThreeEqualArea_existsUnique_in_slab
    hlam hh₄ hstationary

/-- The concrete box-0 certificate identifies its slab root globally: it is
the least equal-area type-(iii) root in `0 < h ≤ 1`, with at most one distinct
upper root. -/
theorem typeThreeEqualArea_root_classification
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h4Interval.RealContains h₄)
    (hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0) :
    ∃ h₃ : ℝ, h3Interval.RealContains h₃ ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ ∧
      (∀ y ∈ Ioc (0 : ℝ) 1,
        LeanSuffixAnalytic.typeThreeArea lam y =
          LeanSuffixAnalytic.typeFourArea lam h₄ → h₃ ≤ y) ∧
      (∀ y ∈ Ioc (0 : ℝ) 1, ∀ z ∈ Ioc (0 : ℝ) 1,
        h₃ < y → h₃ < z →
        LeanSuffixAnalytic.typeThreeArea lam y =
          LeanSuffixAnalytic.typeFourArea lam h₄ →
        LeanSuffixAnalytic.typeThreeArea lam z =
          LeanSuffixAnalytic.typeFourArea lam h₄ → y = z) :=
  checkedConditions.typeThreeEqualArea_root_classification
    hlam hh₄ hstationary

/-- Box 0 now constructs the unique descending equal-area type-(iii) root below
every regular or endpoint type-(iv) curvature.  The curvature need not lie in
the stationary cell slab. -/
theorem descendingTypeThreeEqualArea_existsUnique
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h₄ ∈ Ioc (0 : ℝ) 1) :
    ∃! h₃ : ℝ, h₃ ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ ∧
      LeanSuffixAnalytic.typeThreeFold lam h₃ < 0 ∧ h₃ < h₄ :=
  checkedConditions.descendingTypeThreeEqualArea_existsUnique hlam hh₄

/-- End-to-end box-0 root isolation: every exact lambda has one and only one
stationary type-(iv) root, and that root has one and only one descending
equal-area type-(iii) root. -/
theorem stationaryAndEqualArea_existsUnique {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    ∃! h₄ : ℝ,
      h4Interval.RealContains h₄ ∧
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 ∧
      ∃! h₃ : ℝ, h3Interval.RealContains h₃ ∧
        LeanSuffixAnalytic.typeThreeArea lam h₃ =
          LeanSuffixAnalytic.typeFourArea lam h₄ := by
  rcases typeFourFold_existsUnique_in_slab hlam with
    ⟨h₄, ⟨hh₄, hfold⟩, hunique⟩
  refine ⟨h₄, ⟨hh₄, hfold,
    typeThreeEqualArea_existsUnique_in_slab hlam hh₄ hfold⟩, ?_⟩
  intro y hy
  exact hunique y ⟨hy.1, hy.2.1⟩

/-- At the isolated equal-area root, the type-(iii) perimeter is strictly
smaller.  The equal-area premise identifies the intended root; the strict
inequality itself is the centered correlated enclosure above. -/
theorem stationaryEqualArea_typeThreePerimeter_lt
    {lam h₃ h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₃ : h3Interval.RealContains h₃)
    (hh₄ : h4Interval.RealContains h₄)
    (_hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0)
    (_hequalArea : LeanSuffixAnalytic.typeThreeArea lam h₃ =
      LeanSuffixAnalytic.typeFourArea lam h₄) :
    LeanSuffixAnalytic.typeThreePerimeter lam h₃ <
      LeanSuffixAnalytic.typeFourPerimeter lam h₄ := by
  linarith [typeThreePerimeter_minus_typeFour_neg hlam hh₃ hh₄]

/-- Fully concrete scalar improvement witnesses for every lambda in box 0. -/
theorem stationaryEqualArea_improvement_exists {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    ∃ h₄ h₃ : ℝ,
      h4Interval.RealContains h₄ ∧
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 ∧
      h3Interval.RealContains h₃ ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter lam h₃ <
        LeanSuffixAnalytic.typeFourPerimeter lam h₄ :=
  checkedConditions.stationaryEqualArea_improvement_exists hlam

/-- Strongest candidate-facing box-0 conclusion: every regular stationary
modeled four-arc candidate is not a weighted-perimeter minimizer.  Global
fold uniqueness identifies the arbitrary candidate height with the root in
the exact compact slab; slab membership is not an input. -/
theorem stationaryCompactCandidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1)
    (hstationary :
      LeanSuffixAnalytic.typeFourFold lam candidate.h = 0) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  checkedConditions.regularStationaryCandidate_not_isWeightedPerimeterMinimizer
    hlam candidate hcandidate hregular hstationary

/-- Complete box-0 candidate-facing conclusion: one stationary certified pair
promotes to every regular or endpoint modeled type-(iv) curvature. -/
theorem compactCandidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  checkedConditions.candidate_not_isWeightedPerimeterMinimizer
    hlam candidate hcandidate
end CompactFirstCell
