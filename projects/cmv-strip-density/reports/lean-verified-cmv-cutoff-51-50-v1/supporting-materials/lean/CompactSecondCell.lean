/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CompactCellCertificate
import CompactFirstCell

/-!
# The second compact fold-gap cell

Kernel-checked exact-rational replay of zero-based box 1 from
`compact_fold_gap/compact_certificate.json`.  The JSON is not trusted by Lean.
-/

open Real Set
noncomputable section

namespace CompactSecondCell

abbrev QInterval := ScalarSuffixCertificate.QInterval

/-- Lambda interval of zero-based box 1. -/
def lambdaInterval : QInterval :=
  ⟨236601 / 229376, 118329 / 114688, by norm_num⟩

/-- Type-(iv) stationary-root slab of box 1. -/
def h4Interval : QInterval :=
  ⟨275542293618597 / 281474976710656,
    275579321170665 / 281474976710656, by norm_num⟩

/-- Type-(iii) equal-area-root slab of box 1. -/
def h3Interval : QInterval :=
  ⟨265075342400937 / 281474976710656,
    266245093661975 / 281474976710656, by norm_num⟩

/-- Certificate center for the type-(iv) slab. -/
def h4Center : ℚ := 275560807394631 / 281474976710656

/-- Certificate center for the type-(iii) slab. -/
def h3Center : ℚ := 8301881813483 / 8796093022208

private def u3Lower : QInterval := ⟨468480/1000000, 468481/1000000, by norm_num⟩
private def d3Lower : QInterval := ⟨532412/1000000, 532895/1000000, by norm_num⟩
private def asinQ3Lower : QInterval := ⟨1083225/1000000, 1083226/1000000, by norm_num⟩
private def asinR3Lower : QInterval := ⟨1028041/1000000, 1028441/1000000, by norm_num⟩

private def u3Upper : QInterval := ⟨452459/1000000, 452460/1000000, by norm_num⟩
private def d3Upper : QInterval := ⟨518370/1000000, 518866/1000000, by norm_num⟩
private def asinQ3Upper : QInterval := ⟨1101275/1000000, 1101276/1000000, by norm_num⟩
private def asinR3Upper : QInterval := ⟨1043846/1000000, 1044261/1000000, by norm_num⟩

private def u3Cell : QInterval := ⟨452459/1000000, 468481/1000000, by norm_num⟩
private def d3Cell : QInterval := ⟨518370/1000000, 532895/1000000, by norm_num⟩
private def asinQ3Cell : QInterval := ⟨1083225/1000000, 1101276/1000000, by norm_num⟩
private def asinR3Cell : QInterval := ⟨1028041/1000000, 1044261/1000000, by norm_num⟩

private def u3Center : QInterval := ⟨460558/1000000, 460559/1000000, by norm_num⟩
private def d3Center : QInterval := ⟨525455/1000000, 525943/1000000, by norm_num⟩
private def asinQ3Center : QInterval := ⟨1092172/1000000, 1092173/1000000, by norm_num⟩
private def asinR3Center : QInterval := ⟨1035891/1000000, 1036298/1000000, by norm_num⟩

private def u4Lower : QInterval := ⟨204230/1000000, 204231/1000000, by norm_num⟩
private def d4Lower : QInterval := ⟨325114/1000000, 325902/1000000, by norm_num⟩
private def asinH4Lower : QInterval := ⟨1365118/1000000, 1365119/1000000, by norm_num⟩
private def asinR4Lower : QInterval := ⟨1249419/1000000, 1250144/1000000, by norm_num⟩

private def u4Upper : QInterval := ⟨203598/1000000, 203599/1000000, by norm_num⟩
private def d4Upper : QInterval := ⟨324717/1000000, 325507/1000000, by norm_num⟩
private def asinH4Upper : QInterval := ⟨1365764/1000000, 1365765/1000000, by norm_num⟩
private def asinR4Upper : QInterval := ⟨1249822/1000000, 1250549/1000000, by norm_num⟩

private def u4Cell : QInterval := ⟨203598/1000000, 204231/1000000, by norm_num⟩
private def d4Cell : QInterval := ⟨324717/1000000, 325902/1000000, by norm_num⟩
private def asinH4Cell : QInterval := ⟨1365118/1000000, 1365765/1000000, by norm_num⟩
private def asinR4Cell : QInterval := ⟨1249419/1000000, 1250549/1000000, by norm_num⟩

private def u4Center : QInterval := ⟨203914/1000000, 203915/1000000, by norm_num⟩
private def d4Center : QInterval := ⟨324915/1000000, 325705/1000000, by norm_num⟩
private def asinH4Center : QInterval := ⟨1365441/1000000, 1365442/1000000, by norm_num⟩
private def asinR4Center : QInterval := ⟨1249620/1000000, 1250346/1000000, by norm_num⟩

private theorem lambda_one_lt {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) : 1 < lam := by
  norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains] at hlam ⊢
  linarith

private theorem h3_slab_regular {h : ℝ}
    (hh : h3Interval.RealContains h) : h ∈ Ioo (0 : ℝ) 1 := by
  norm_num [h3Interval, LeanSuffixReflective.QInterval.RealContains] at hh ⊢
  exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
    lt_of_le_of_lt hh.2 (by norm_num)⟩

private theorem h4_slab_regular {h : ℝ}
    (hh : h4Interval.RealContains h) : h ∈ Ioo (0 : ℝ) 1 := by
  norm_num [h4Interval, LeanSuffixReflective.QInterval.RealContains] at hh ⊢
  exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
    lt_of_le_of_lt hh.2 (by norm_num)⟩

private theorem h3Center_mem : h3Interval.RealContains (h3Center : ℝ) := by
  norm_num [h3Center, h3Interval, LeanSuffixReflective.QInterval.RealContains]

private theorem h4Center_mem : h4Interval.RealContains (h4Center : ℝ) := by
  norm_num [h4Center, h4Interval, LeanSuffixReflective.QInterval.RealContains]

private theorem typeThreeLower_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u3Lower.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ)^2)) ∧
    d3Lower.RealContains (sqrt (lam^2 - LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ)^2)) ∧
    asinQ3Lower.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ))) ∧
    asinR3Lower.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.lo : ℝ) / lam)) := by
  apply CompactCellCertificate.typeThree_atoms_of_exact_bounds lambdaInterval
    (LeanSuffixReflective.QInterval.point h3Interval.lo)
    u3Lower d3Lower asinQ3Lower asinR3Lower hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Interval.lo
      (h3Interval.lo : ℝ) |>.2 rfl)
    (by norm_num [lambdaInterval]) (lambda_one_lt hlam)
  all_goals norm_num [lambdaInterval, h3Interval, u3Lower, d3Lower,
    asinQ3Lower, asinR3Lower, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    Nat.factorial]

private theorem typeThreeUpper_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u3Upper.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ)^2)) ∧
    d3Upper.RealContains (sqrt (lam^2 - LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ)^2)) ∧
    asinQ3Upper.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ))) ∧
    asinR3Upper.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Interval.hi : ℝ) / lam)) := by
  apply CompactCellCertificate.typeThree_atoms_of_exact_bounds lambdaInterval
    (LeanSuffixReflective.QInterval.point h3Interval.hi)
    u3Upper d3Upper asinQ3Upper asinR3Upper hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Interval.hi
      (h3Interval.hi : ℝ) |>.2 rfl)
    (by norm_num [lambdaInterval]) (lambda_one_lt hlam)
  all_goals norm_num [lambdaInterval, h3Interval, u3Upper, d3Upper,
    asinQ3Upper, asinR3Upper, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    Nat.factorial]

private theorem typeThreeCell_atoms {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : h3Interval.RealContains h) :
    u3Cell.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h^2)) ∧
    d3Cell.RealContains (sqrt (lam^2 - LeanSuffixAnalytic.typeThreeShape h^2)) ∧
    asinQ3Cell.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
    asinR3Cell.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h / lam)) := by
  apply CompactCellCertificate.typeThree_atoms_of_exact_bounds lambdaInterval h3Interval
    u3Cell d3Cell asinQ3Cell asinR3Cell hlam hh
    (by norm_num [lambdaInterval]) (lambda_one_lt hlam)
  all_goals norm_num [lambdaInterval, h3Interval, u3Cell, d3Cell,
    asinQ3Cell, asinR3Cell, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    Nat.factorial]

private theorem typeThreeCenter_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u3Center.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ)^2)) ∧
    d3Center.RealContains (sqrt (lam^2 - LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ)^2)) ∧
    asinQ3Center.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ))) ∧
    asinR3Center.RealContains
      (arcsin (LeanSuffixAnalytic.typeThreeShape (h3Center : ℝ) / lam)) := by
  apply CompactCellCertificate.typeThree_atoms_of_exact_bounds lambdaInterval
    (LeanSuffixReflective.QInterval.point h3Center)
    u3Center d3Center asinQ3Center asinR3Center hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Center
      (h3Center : ℝ) |>.2 rfl)
    (by norm_num [lambdaInterval]) (lambda_one_lt hlam)
  all_goals norm_num [lambdaInterval, h3Center, h3Interval, u3Center, d3Center,
    asinQ3Center, asinR3Center, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    Nat.factorial]

private abbrev shiftedInterval := CompactCellCertificate.typeFourShiftedInterval

private theorem typeFour_atoms_of_exact_bounds
    (hI uI dI asinHI asinRI : QInterval) {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : hI.RealContains h)
    (hexact :
      0 ≤ (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ∧
      (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ≤ 1 ∧
      0 ≤ uI.lo ∧
      uI.lo ^ 2 ≤ 1 -
        (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
          (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      1 - (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤
          uI.hi ^ 2 ∧
      0 ≤ dI.lo ∧
      dI.lo ^ 2 ≤ lambdaInterval.lo ^ 2 -
        (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
          (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      lambdaInterval.hi ^ 2 -
        (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
          (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤
            dI.hi ^ 2 ∧
      (0 ≤ asinHI.lo ∧ asinHI.hi ≤ CompactCellCertificate.halfPiBox.lo) ∧
      (ScalarSuffixCertificate.sinTaylor27Interval asinHI.lo).hi ≤
        (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
          (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ∧
      (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ≤
          (ScalarSuffixCertificate.sinTaylor27Interval asinHI.hi).lo ∧
      (0 ≤ asinRI.lo ∧ asinRI.hi ≤ CompactCellCertificate.halfPiBox.lo) ∧
      (ScalarSuffixCertificate.sinTaylor27Interval asinRI.lo).hi ≤
        (ScalarSuffixCertificate.QInterval.divPos
          (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
            (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval])).lo ∧
      (ScalarSuffixCertificate.QInterval.divPos
          (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
            (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval])).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinRI.hi).lo) :
    uI.RealContains (sqrt (1 - h ^ 2)) ∧
      dI.RealContains (sqrt (lam ^ 2 - h ^ 2)) ∧
      asinHI.RealContains (arcsin h) ∧
      asinRI.RealContains (arcsin (h / lam)) :=
  CompactCellCertificate.typeFour_atoms_of_exact_bounds
    lambdaInterval hI uI dI asinHI asinRI hlam hh
    (by norm_num [lambdaInterval]) (lambda_one_lt hlam) hexact

private theorem typeFourLower_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u4Lower.RealContains (sqrt (1-(h4Interval.lo : ℝ)^2)) ∧
      d4Lower.RealContains (sqrt (lam^2-(h4Interval.lo : ℝ)^2)) ∧
      asinH4Lower.RealContains (arcsin (h4Interval.lo : ℝ)) ∧
      asinR4Lower.RealContains (arcsin ((h4Interval.lo : ℝ)/lam)) :=
  typeFour_atoms_of_exact_bounds
    (LeanSuffixReflective.QInterval.point h4Interval.lo)
    u4Lower d4Lower asinH4Lower asinR4Lower hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Interval.lo
      (h4Interval.lo : ℝ) |>.2 rfl)
    (by norm_num [shiftedInterval, CompactCellCertificate.typeFourShiftedInterval,
      lambdaInterval, h4Interval, u4Lower, d4Lower,
      asinH4Lower, asinR4Lower, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])

private theorem typeFourUpper_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u4Upper.RealContains (sqrt (1-(h4Interval.hi : ℝ)^2)) ∧
      d4Upper.RealContains (sqrt (lam^2-(h4Interval.hi : ℝ)^2)) ∧
      asinH4Upper.RealContains (arcsin (h4Interval.hi : ℝ)) ∧
      asinR4Upper.RealContains (arcsin ((h4Interval.hi : ℝ)/lam)) :=
  typeFour_atoms_of_exact_bounds
    (LeanSuffixReflective.QInterval.point h4Interval.hi)
    u4Upper d4Upper asinH4Upper asinR4Upper hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Interval.hi
      (h4Interval.hi : ℝ) |>.2 rfl)
    (by norm_num [shiftedInterval, CompactCellCertificate.typeFourShiftedInterval,
      lambdaInterval, h4Interval, u4Upper, d4Upper,
      asinH4Upper, asinR4Upper, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])

private theorem typeFourCell_atoms {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : h4Interval.RealContains h) :
    u4Cell.RealContains (sqrt (1-h^2)) ∧
      d4Cell.RealContains (sqrt (lam^2-h^2)) ∧
      asinH4Cell.RealContains (arcsin h) ∧
      asinR4Cell.RealContains (arcsin (h/lam)) :=
  typeFour_atoms_of_exact_bounds h4Interval u4Cell d4Cell asinH4Cell asinR4Cell
    hlam hh
    (by norm_num [shiftedInterval, CompactCellCertificate.typeFourShiftedInterval,
      lambdaInterval, h4Interval, u4Cell, d4Cell,
      asinH4Cell, asinR4Cell, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])

private theorem typeFourCenter_atoms {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    u4Center.RealContains (sqrt (1-(h4Center : ℝ)^2)) ∧
      d4Center.RealContains (sqrt (lam^2-(h4Center : ℝ)^2)) ∧
      asinH4Center.RealContains (arcsin (h4Center : ℝ)) ∧
      asinR4Center.RealContains (arcsin ((h4Center : ℝ)/lam)) :=
  typeFour_atoms_of_exact_bounds
    (LeanSuffixReflective.QInterval.point h4Center)
    u4Center d4Center asinH4Center asinR4Center hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Center
      (h4Center : ℝ) |>.2 rfl)
    (by norm_num [shiftedInterval, CompactCellCertificate.typeFourShiftedInterval,
      lambdaInterval, h4Center, h4Interval,
      u4Center, d4Center,
      asinH4Center, asinR4Center, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
      ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
      LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
      LeanSuffixReflective.QInterval.point, Nat.factorial])

private def typeFourLowerFold : QInterval := ⟨-40361/1000000, -3918/1000000, by norm_num⟩
private def typeFourUpperFold : QInterval := ⟨3953/1000000, 40563/1000000, by norm_num⟩
private def typeThreeFoldCell : QInterval := ⟨-5229914/1000000, -4044182/1000000, by norm_num⟩
private def typeThreeLowerArea : QInterval := ⟨3777973/1000000, 3780523/1000000, by norm_num⟩
private def typeThreeUpperArea : QInterval := ⟨3755019/1000000, 3757595/1000000, by norm_num⟩
private def typeFourCenteredArea : QInterval := ⟨3765895/1000000, 3769360/1000000, by norm_num⟩

private theorem typeFourFold_lowerFace_neg {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    LeanSuffixAnalytic.typeFourFold lam (h4Interval.lo : ℝ) < 0 := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval
    (LeanSuffixReflective.QInterval.point h4Interval.lo)
    u4Lower d4Lower asinH4Lower asinR4Lower hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Interval.lo
      (h4Interval.lo : ℝ) |>.2 rfl) (typeFourLower_atoms hlam)
    (by norm_num [lambdaInterval]) (by norm_num [h4Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [u4Lower]) (by norm_num [d4Lower])
  rcases henc with ⟨_,_,hfold⟩
  norm_num [CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h4Interval, u4Lower, d4Lower, asinH4Lower, asinR4Lower,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hfold ⊢
  linarith [hfold.2]

private theorem typeFourFold_upperFace_pos {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    0 < LeanSuffixAnalytic.typeFourFold lam (h4Interval.hi : ℝ) := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval
    (LeanSuffixReflective.QInterval.point h4Interval.hi)
    u4Upper d4Upper asinH4Upper asinR4Upper hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Interval.hi
      (h4Interval.hi : ℝ) |>.2 rfl) (typeFourUpper_atoms hlam)
    (by norm_num [lambdaInterval]) (by norm_num [h4Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [u4Upper]) (by norm_num [d4Upper])
  rcases henc with ⟨_,_,hfold⟩
  norm_num [CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h4Interval, u4Upper, d4Upper, asinH4Upper, asinR4Upper,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hfold ⊢
  linarith [hfold.1]

private theorem typeThreeFold_neg_on_slab {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : h3Interval.RealContains h) :
    LeanSuffixAnalytic.typeThreeFold lam h < 0 := by
  have hfold := CompactCellCertificate.typeThree_fold_atom_enclosure lambdaInterval
    h3Interval u3Cell d3Cell asinQ3Cell asinR3Cell hlam hh
    (typeThreeCell_atoms hlam hh) (by norm_num [lambdaInterval])
    (by norm_num [u3Cell])
    (by norm_num [lambdaInterval, d3Cell, ScalarSuffixCertificate.QInterval.mul])
  norm_num [CompactCellCertificate.typeThreeFoldBox,
    CompactCellCertificate.typeThreeAngleBox, CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h3Interval, u3Cell, d3Cell, asinQ3Cell, asinR3Cell,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hfold
  linarith [hfold.2]

private theorem typeThreeArea_lower_enclosure {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    typeThreeLowerArea.RealContains
      (LeanSuffixAnalytic.typeThreeArea lam (h3Interval.lo : ℝ)) := by
  have henc := CompactCellCertificate.typeThree_area_perimeter_atom_enclosure
    lambdaInterval (LeanSuffixReflective.QInterval.point h3Interval.lo)
    u3Lower d3Lower asinQ3Lower asinR3Lower hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Interval.lo
      (h3Interval.lo : ℝ) |>.2 rfl) (typeThreeLower_atoms hlam)
    (by norm_num [lambdaInterval])
    (by norm_num [h3Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
  rcases henc with ⟨harea,_⟩
  norm_num [typeThreeLowerArea, CompactCellCertificate.typeThreeAreaBox,
    CompactCellCertificate.typeThreeAngleBox, CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h3Interval, u3Lower, d3Lower, asinQ3Lower, asinR3Lower,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at harea ⊢
  exact ⟨by linarith [harea.1], by linarith [harea.2]⟩

private theorem typeThreeArea_upper_enclosure {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    typeThreeUpperArea.RealContains
      (LeanSuffixAnalytic.typeThreeArea lam (h3Interval.hi : ℝ)) := by
  have henc := CompactCellCertificate.typeThree_area_perimeter_atom_enclosure
    lambdaInterval (LeanSuffixReflective.QInterval.point h3Interval.hi)
    u3Upper d3Upper asinQ3Upper asinR3Upper hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Interval.hi
      (h3Interval.hi : ℝ) |>.2 rfl) (typeThreeUpper_atoms hlam)
    (by norm_num [lambdaInterval])
    (by norm_num [h3Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
  rcases henc with ⟨harea,_⟩
  norm_num [typeThreeUpperArea, CompactCellCertificate.typeThreeAreaBox,
    CompactCellCertificate.typeThreeAngleBox, CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h3Interval, u3Upper, d3Upper, asinQ3Upper, asinR3Upper,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at harea ⊢
  exact ⟨by linarith [harea.1], by linarith [harea.2]⟩

private def h4Square := h4Interval.mul h4Interval
private def h4Cube := h4Square.mul h4Interval
private def h4Displacement := h4Interval.sub (LeanSuffixReflective.QInterval.point h4Center)
private def h4FoldCell := CompactCellCertificate.typeFourFoldBox lambdaInterval h4Interval
  u4Cell d4Cell asinH4Cell asinR4Cell (by norm_num [lambdaInterval])
  (by norm_num [u4Cell]) (by norm_num [d4Cell])
private def h4AreaCenter := CompactCellCertificate.typeFourAreaBox lambdaInterval
  (LeanSuffixReflective.QInterval.point h4Center) u4Center d4Center asinH4Center asinR4Center
  (by norm_num [lambdaInterval])
  (by norm_num [h4Center, h4Interval, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.point])
private def h4PerimeterCenter := CompactCellCertificate.typeFourPerimeterBox lambdaInterval
  (LeanSuffixReflective.QInterval.point h4Center) asinH4Center asinR4Center
  (by norm_num [h4Center, h4Interval, LeanSuffixReflective.QInterval.point])
private def h4AreaSlope := h4FoldCell.divPos h4Cube
  (by norm_num [h4Cube, h4Square, h4Interval, ScalarSuffixCertificate.QInterval.mul])
private def h4PerimeterSlope := h4FoldCell.divPos h4Square
  (by norm_num [h4Square, h4Interval, ScalarSuffixCertificate.QInterval.mul])
private def h4AreaCentered := h4AreaCenter.add (h4AreaSlope.mul h4Displacement)
private def h4PerimeterCentered := h4PerimeterCenter.add (h4PerimeterSlope.mul h4Displacement)

private theorem typeFour_center_enclosures {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    h4AreaCenter.RealContains (LeanSuffixAnalytic.typeFourArea lam (h4Center : ℝ)) ∧
    h4PerimeterCenter.RealContains (LeanSuffixAnalytic.typeFourPerimeter lam (h4Center : ℝ)) := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval
    (LeanSuffixReflective.QInterval.point h4Center)
    u4Center d4Center asinH4Center asinR4Center hlam
    (LeanSuffixReflective.QInterval.realContains_point h4Center (h4Center : ℝ) |>.2 rfl)
    (typeFourCenter_atoms hlam) (by norm_num [lambdaInterval])
    (by norm_num [h4Center, h4Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4Center, h4Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [u4Center]) (by norm_num [d4Center])
  exact ⟨henc.1, henc.2.1⟩

private theorem typeFourFold_cell_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : h4Interval.RealContains h) :
    h4FoldCell.RealContains (LeanSuffixAnalytic.typeFourFold lam h) := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval h4Interval
    u4Cell d4Cell asinH4Cell asinR4Cell hlam hh (typeFourCell_atoms hlam hh)
    (by norm_num [lambdaInterval]) (by norm_num [h4Interval])
    (by norm_num [h4Interval, ScalarSuffixCertificate.QInterval.mul])
    (by norm_num [u4Cell]) (by norm_num [d4Cell])
  exact henc.2.2

private theorem typeFour_centered_enclosures {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : h4Interval.RealContains h) :
    h4AreaCentered.RealContains (LeanSuffixAnalytic.typeFourArea lam h) ∧
    h4PerimeterCentered.RealContains (LeanSuffixAnalytic.typeFourPerimeter lam h) := by
  rcases typeFour_center_enclosures hlam with ⟨harea,hper⟩
  have hslope3 : ∀ x, h4Interval.RealContains x →
      h4AreaSlope.RealContains (LeanSuffixAnalytic.typeFourFold lam x / x^3) := by
    intro x hx
    have hpow : h4Cube.RealContains (x^3) := by
      simpa [h4Cube, h4Square, pow_succ] using
        (ScalarSuffixCertificate.QInterval.realContains_mul
          (ScalarSuffixCertificate.QInterval.realContains_mul hx hx) hx)
    exact ScalarSuffixCertificate.QInterval.realContains_divPos
      (by norm_num [h4Cube, h4Square, h4Interval,
        ScalarSuffixCertificate.QInterval.mul])
      (typeFourFold_cell_enclosure hlam hx) hpow
  have hslope2 : ∀ x, h4Interval.RealContains x →
      h4PerimeterSlope.RealContains (LeanSuffixAnalytic.typeFourFold lam x / x^2) := by
    intro x hx
    have hpow : h4Square.RealContains (x^2) := by
      simpa [h4Square, pow_succ] using
        ScalarSuffixCertificate.QInterval.realContains_mul hx hx
    exact ScalarSuffixCertificate.QInterval.realContains_divPos
      (by norm_num [h4Square, h4Interval, ScalarSuffixCertificate.QInterval.mul])
      (typeFourFold_cell_enclosure hlam hx) hpow
  have hdisp := LeanSuffixReflective.QInterval.realContains_sub hh
    (LeanSuffixReflective.QInterval.realContains_point h4Center (h4Center : ℝ) |>.2 rfl)
  constructor
  · exact CompactCellCertificate.typeFourArea_centered_enclosure lambdaInterval h4Interval
      h4Center hlam hh h4Center_mem (lambda_one_lt hlam)
      (fun hx => h4_slab_regular hx) h4AreaCenter h4AreaSlope h4Displacement
      harea hslope3 hdisp
  · exact CompactCellCertificate.typeFourPerimeter_centered_enclosure lambdaInterval h4Interval
      h4Center hlam hh h4Center_mem (lambda_one_lt hlam)
      (fun hx => h4_slab_regular hx) h4PerimeterCenter h4PerimeterSlope h4Displacement
      hper hslope2 hdisp

private def h3Square := h3Interval.mul h3Interval
private def h3Displacement := h3Interval.sub (LeanSuffixReflective.QInterval.point h3Center)
private def h3PerimeterCenter := CompactCellCertificate.typeThreePerimeterBox lambdaInterval
  (LeanSuffixReflective.QInterval.point h3Center) u3Center d3Center asinQ3Center asinR3Center
  (by norm_num [lambdaInterval])
  (by norm_num [h3Center, h3Interval, LeanSuffixReflective.QInterval.point])
private def h3PerimeterSlope :=
  (CompactCellCertificate.typeThreeFoldBox lambdaInterval h3Interval u3Cell d3Cell
    asinQ3Cell asinR3Cell (by norm_num [lambdaInterval]) (by norm_num [u3Cell])
    (by norm_num [lambdaInterval, d3Cell, ScalarSuffixCertificate.QInterval.mul])).divPos
      h3Square (by norm_num [h3Square, h3Interval, ScalarSuffixCertificate.QInterval.mul])
private def h3PerimeterCentered := h3PerimeterCenter.add
  (h3PerimeterSlope.mul h3Displacement)

private theorem typeThreePerimeter_center_enclosure {lam : ℝ}
    (hlam : lambdaInterval.RealContains lam) :
    h3PerimeterCenter.RealContains
      (LeanSuffixAnalytic.typeThreePerimeter lam (h3Center : ℝ)) := by
  have henc := CompactCellCertificate.typeThree_area_perimeter_atom_enclosure
    lambdaInterval (LeanSuffixReflective.QInterval.point h3Center)
    u3Center d3Center asinQ3Center asinR3Center hlam
    (LeanSuffixReflective.QInterval.realContains_point h3Center (h3Center : ℝ) |>.2 rfl)
    (typeThreeCenter_atoms hlam) (by norm_num [lambdaInterval])
    (by norm_num [h3Center, h3Interval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3Center, h3Interval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])
  exact henc.2

private theorem typeThreePerimeter_centered_enclosure {lam h : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh : h3Interval.RealContains h) :
    h3PerimeterCentered.RealContains (LeanSuffixAnalytic.typeThreePerimeter lam h) := by
  have hslope : ∀ x, h3Interval.RealContains x →
      h3PerimeterSlope.RealContains (LeanSuffixAnalytic.typeThreeFold lam x / x^2) := by
    intro x hx
    have hpow : h3Square.RealContains (x^2) := by
      simpa [h3Square, pow_succ] using
        ScalarSuffixCertificate.QInterval.realContains_mul hx hx
    exact ScalarSuffixCertificate.QInterval.realContains_divPos
      (by norm_num [h3Square, h3Interval, ScalarSuffixCertificate.QInterval.mul])
      (CompactCellCertificate.typeThree_fold_atom_enclosure lambdaInterval h3Interval
        u3Cell d3Cell asinQ3Cell asinR3Cell hlam hx (typeThreeCell_atoms hlam hx)
        (by norm_num [lambdaInterval]) (by norm_num [u3Cell])
        (by norm_num [lambdaInterval, d3Cell, ScalarSuffixCertificate.QInterval.mul]))
      hpow
  have hdisp := LeanSuffixReflective.QInterval.realContains_sub hh
    (LeanSuffixReflective.QInterval.realContains_point h3Center (h3Center : ℝ) |>.2 rfl)
  exact CompactCellCertificate.typeThreePerimeter_centered_enclosure
    lambdaInterval h3Interval h3Center hlam hh h3Center_mem (lambda_one_lt hlam)
    (fun hx => h3_slab_regular hx) h3PerimeterCenter h3PerimeterSlope h3Displacement
    (typeThreePerimeter_center_enclosure hlam) hslope hdisp

private theorem typeThreeArea_lowerFace_gap_pos {lam h4 : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh4 : h4Interval.RealContains h4)
    (_hstationary : LeanSuffixAnalytic.typeFourFold lam h4 = 0) :
    0 < LeanSuffixAnalytic.typeThreeArea lam (h3Interval.lo : ℝ) -
      LeanSuffixAnalytic.typeFourArea lam h4 := by
  have h3 := typeThreeArea_lower_enclosure hlam
  have h4 := (typeFour_centered_enclosures hlam hh4).1
  norm_num [typeThreeLowerArea, h4AreaCentered, h4AreaCenter, h4AreaSlope,
    h4FoldCell, h4Displacement, h4Cube, h4Square,
    CompactCellCertificate.typeFourAreaBox, CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, lambdaInterval, h4Interval, h4Center,
    u4Center, d4Center, asinH4Center, asinR4Center, u4Cell, d4Cell,
    asinH4Cell, asinR4Cell, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at h3 h4 ⊢
  linarith [h3.1, h4.2]

private theorem typeThreeArea_upperFace_gap_neg {lam h4 : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh4 : h4Interval.RealContains h4)
    (_hstationary : LeanSuffixAnalytic.typeFourFold lam h4 = 0) :
    LeanSuffixAnalytic.typeThreeArea lam (h3Interval.hi : ℝ) -
      LeanSuffixAnalytic.typeFourArea lam h4 < 0 := by
  have h3 := typeThreeArea_upper_enclosure hlam
  have h4 := (typeFour_centered_enclosures hlam hh4).1
  norm_num [typeThreeUpperArea, h4AreaCentered, h4AreaCenter, h4AreaSlope,
    h4FoldCell, h4Displacement, h4Cube, h4Square,
    CompactCellCertificate.typeFourAreaBox, CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, lambdaInterval, h4Interval, h4Center,
    u4Center, d4Center, asinH4Center, asinR4Center, u4Cell, d4Cell,
    asinH4Cell, asinR4Cell, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at h3 h4 ⊢
  linarith [h3.2, h4.1]

private theorem typeThreePerimeter_gap_neg {lam h3 h4 : ℝ}
    (hlam : lambdaInterval.RealContains lam) (hh3 : h3Interval.RealContains h3)
    (hh4 : h4Interval.RealContains h4) :
    LeanSuffixAnalytic.typeThreePerimeter lam h3 -
      LeanSuffixAnalytic.typeFourPerimeter lam h4 < 0 := by
  have hp3 := typeThreePerimeter_centered_enclosure hlam hh3
  have hp4 := (typeFour_centered_enclosures hlam hh4).2
  norm_num [h3PerimeterCentered, h3PerimeterCenter, h3PerimeterSlope,
    h3Displacement, h3Square, h4PerimeterCentered, h4PerimeterCenter,
    h4PerimeterSlope, h4FoldCell, h4Displacement, h4Square,
    CompactCellCertificate.typeThreePerimeterBox,
    CompactCellCertificate.typeThreeFoldBox, CompactCellCertificate.typeThreeAngleBox,
    CompactCellCertificate.typeThreeDeltaBox, CompactCellCertificate.typeThreeQBox,
    CompactCellCertificate.typeFourPerimeterBox, CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h3Interval, h3Center, h4Interval, h4Center,
    u3Center, d3Center, asinQ3Center, asinR3Center, u3Cell, d3Cell,
    asinQ3Cell, asinR3Cell, u4Center, d4Center, asinH4Center, asinR4Center,
    u4Cell, d4Cell, asinH4Cell, asinR4Cell, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at hp3 hp4 ⊢
  linarith [hp3.2, hp4.1]

/-- The complete exact-rational `Conditions` payload for zero-based box 1. -/
theorem checkedConditions :
    CompactCellAssembly.Conditions lambdaInterval h3Interval h4Interval where
  lambda_one_lt := fun hlam => lambda_one_lt hlam
  h3_slab_regular := fun hh => h3_slab_regular hh
  h3_slab_above_half := by
    intro h hh
    have hlo : (h3Interval.lo : ℝ) ≤ h := hh.1
    norm_num [h3Interval] at hlo ⊢
    linarith
  h4_slab_regular := fun hh => h4_slab_regular hh
  typeFourFold_lowerFace_neg := fun hlam => typeFourFold_lowerFace_neg hlam
  typeFourFold_upperFace_pos := fun hlam => typeFourFold_upperFace_pos hlam
  typeThreeFold_neg_on_slab := fun hlam hh => typeThreeFold_neg_on_slab hlam hh
  typeThreeArea_lowerFace_gap_pos := fun hlam hh hz =>
    typeThreeArea_lowerFace_gap_pos hlam hh hz
  typeThreeArea_upperFace_gap_neg := fun hlam hh hz =>
    typeThreeArea_upperFace_gap_neg hlam hh hz
  typeThreePerimeter_gap_neg := fun hlam hh3 hh4 =>
    typeThreePerimeter_gap_neg hlam hh3 hh4

/-- Every regular stationary candidate in zero-based compact box 1 is excluded. -/
theorem stationaryCompactCandidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ} (hlam : lambdaInterval.RealContains lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1)
    (hstationary : LeanSuffixAnalytic.typeFourFold lam candidate.h = 0) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  checkedConditions.regularStationaryCandidate_not_isWeightedPerimeterMinimizer
    hlam candidate hcandidate hregular hstationary

/-- Every modeled type-(iv) candidate in zero-based compact box 1 is excluded,
including the endpoint `h = 1`. -/
theorem compactCandidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ} (hlam : lambdaInterval.RealContains lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer :=
  checkedConditions.candidate_not_isWeightedPerimeterMinimizer
    hlam candidate hcandidate

/-- Candidate-facing exclusion on the closed union of zero-based boxes 0 and 1
across their exact seam. -/
theorem firstTwoBoxes_candidate_not_isWeightedPerimeterMinimizer
    {lam : ℝ}
    (hlower : (33 / 32 : ℝ) ≤ lam) (hupper : lam ≤ (118329 / 114688 : ℝ))
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  by_cases hseam : lam ≤ (236601/229376 : ℝ)
  · have hbox : CompactFirstCell.lambdaInterval.RealContains lam := by
      norm_num [CompactFirstCell.lambdaInterval,
        LeanSuffixReflective.QInterval.RealContains] at hlower hseam ⊢
      exact ⟨hlower, hseam⟩
    exact CompactFirstCell.compactCandidate_not_isWeightedPerimeterMinimizer
      hbox candidate hcandidate
  · have hbox : lambdaInterval.RealContains lam := by
      norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains]
        at hseam hupper ⊢
      exact ⟨hseam.le, hupper⟩
    exact compactCandidate_not_isWeightedPerimeterMinimizer
      hbox candidate hcandidate

end CompactSecondCell
