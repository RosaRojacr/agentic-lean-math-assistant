/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CompactCellCertificate
import CMVSuffixModel

/-!
# The exact lambda = 5/4 endpoint closure cell

A kernel-checked rational/Taylor certificate replacing the type-(iii) endpoint
`h = 1` by its second regular equal-area root and matching that endpoint area
to a regular type-(iv) root.  The candidate consumer uses no stationarity.
-/

open Real Set
noncomputable section

namespace EndpointClosureCell

abbrev QInterval := ScalarSuffixCertificate.QInterval

private def lambdaInterval : QInterval :=
  LeanSuffixReflective.QInterval.point (5 / 4)

/-- Slab containing the second regular type-(iii) root with endpoint area. -/
def h3RegularInterval : QInterval :=
  ⟨3319 / 4096, 3320 / 4096, by norm_num⟩

/-- Slab containing the type-(iv) root matching the type-(iii) endpoint area. -/
def h4MatchingInterval : QInterval :=
  ⟨3663 / 4096, 3665 / 4096, by norm_num⟩

/-- Slab containing the second, near-one type-(iv) root with endpoint area. -/
def h4SecondInterval : QInterval :=
  ⟨1046830 / 1048576, 1046831 / 1048576, by norm_num⟩

private def endpointAsinR : QInterval := ⟨927295/1000000, 927296/1000000, by norm_num⟩

private def h3ULower : QInterval := ⟨784122/1000000, 784124/1000000, by norm_num⟩
private def h3DLower : QInterval := ⟨1085056/1000000, 1085058/1000000, by norm_num⟩
private def h3AsinQLower : QInterval := ⟨669514/1000000, 669516/1000000, by norm_num⟩
private def h3AsinRLower : QInterval := ⟨519543/1000000, 519545/1000000, by norm_num⟩
private def h3UUpper : QInterval := ⟨783735/1000000, 783738/1000000, by norm_num⟩
private def h3DUpper : QInterval := ⟨1084777/1000000, 1084779/1000000, by norm_num⟩
private def h3AsinQUpper : QInterval := ⟨670137/1000000, 670138/1000000, by norm_num⟩
private def h3AsinRUpper : QInterval := ⟨519993/1000000, 519995/1000000, by norm_num⟩
private def h3UCell : QInterval := ⟨783735/1000000, 784124/1000000, by norm_num⟩
private def h3DCell : QInterval := ⟨1084777/1000000, 1085058/1000000, by norm_num⟩
private def h3AsinQCell : QInterval := ⟨669514/1000000, 670138/1000000, by norm_num⟩
private def h3AsinRCell : QInterval := ⟨519543/1000000, 519995/1000000, by norm_num⟩

private def h4ULower : QInterval := ⟨447493/1000000, 447495/1000000, by norm_num⟩
private def h4DLower : QInterval := ⟨873355/1000000, 873357/1000000, by norm_num⟩
private def h4AsinHLower : QInterval := ⟨1106835/1000000, 1106837/1000000, by norm_num⟩
private def h4AsinRLower : QInterval := ⟨797238/1000000, 797240/1000000, by norm_num⟩
private def h4UUpper : QInterval := ⟨446515/1000000, 446518/1000000, by norm_num⟩
private def h4DUpper : QInterval := ⟨872855/1000000, 872857/1000000, by norm_num⟩
private def h4AsinHUpper : QInterval := ⟨1107927/1000000, 1107929/1000000, by norm_num⟩
private def h4AsinRUpper : QInterval := ⟨797797/1000000, 797800/1000000, by norm_num⟩
private def h4UCell : QInterval := ⟨446515/1000000, 447495/1000000, by norm_num⟩
private def h4DCell : QInterval := ⟨872855/1000000, 873357/1000000, by norm_num⟩
private def h4AsinHCell : QInterval := ⟨1106835/1000000, 1107929/1000000, by norm_num⟩
private def h4AsinRCell : QInterval := ⟨797238/1000000, 797800/1000000, by norm_num⟩

private def h4SecondULower : QInterval :=
  ⟨5768412/100000000, 5768413/100000000, by norm_num⟩
private def h4SecondDLower : QInterval :=
  ⟨75221503/100000000, 75221504/100000000, by norm_num⟩
private def h4SecondAsinHLower : QInterval :=
  ⟨151308016/100000000, 151308017/100000000, by norm_num⟩
private def h4SecondAsinRLower : QInterval :=
  ⟨92507833/100000000, 92507834/100000000, by norm_num⟩
private def h4SecondUUpper : QInterval :=
  ⟨5766761/100000000, 5766762/100000000, by norm_num⟩
private def h4SecondDUpper : QInterval :=
  ⟨75221376/100000000, 75221377/100000000, by norm_num⟩
private def h4SecondAsinHUpper : QInterval :=
  ⟨151309670/100000000, 151309671/100000000, by norm_num⟩
private def h4SecondAsinRUpper : QInterval :=
  ⟨92507960/100000000, 92507961/100000000, by norm_num⟩
private def h4SecondUCell : QInterval :=
  ⟨5766761/100000000, 5768413/100000000, by norm_num⟩
private def h4SecondDCell : QInterval :=
  ⟨75221376/100000000, 75221504/100000000, by norm_num⟩
private def h4SecondAsinHCell : QInterval :=
  ⟨151308016/100000000, 151309671/100000000, by norm_num⟩
private def h4SecondAsinRCell : QInterval :=
  ⟨92507833/100000000, 92507961/100000000, by norm_num⟩

private def endpointAreaBox : QInterval := ⟨5745967/1000000, 5745970/1000000, by norm_num⟩
private def endpointPerimeterBox : QInterval := ⟨9091934/1000000, 9091940/1000000, by norm_num⟩
private def h3AreaLowerBox : QInterval := ⟨5748327/1000000, 5748350/1000000, by norm_num⟩
private def h3AreaUpperBox : QInterval := ⟨5745668/1000000, 5745695/1000000, by norm_num⟩
private def h3PerimeterCellBox : QInterval := ⟨8975445/1000000, 8982595/1000000, by norm_num⟩
private def h4AreaLowerBox : QInterval := ⟨5747837/1000000, 5747859/1000000, by norm_num⟩
private def h4AreaUpperBox : QInterval := ⟨5744141/1000000, 5744169/1000000, by norm_num⟩
private def h4PerimeterCellBox : QInterval := ⟨9267493/1000000, 9280582/1000000, by norm_num⟩
private def h4SecondAreaLowerBox : QInterval :=
  ⟨5745937/1000000, 5745940/1000000, by norm_num⟩
private def h4SecondAreaUpperBox : QInterval :=
  ⟨5745988/1000000, 5745991/1000000, by norm_num⟩
private def h4SecondPerimeterCellBox : QInterval :=
  ⟨9296373/1000000, 9296458/1000000, by norm_num⟩
private def h4SecondFoldCellBox : QInterval :=
  ⟨53310741/1000000, 53330720/1000000, by norm_num⟩

private theorem lambda_mem : lambdaInterval.RealContains (5 / 4 : ℝ) := by
  norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.point]

private theorem typeThree_atoms
    (hI uI dI asinQI asinRI : QInterval) {h : ℝ}
    (hh : hI.RealContains h)
    (hexact :
      0 ≤ ((hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ∧
      ((hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ≤ 1 ∧
      0 ≤ uI.lo ∧
      uI.lo ^ 2 ≤ 1 - ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      1 - ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ uI.hi ^ 2 ∧
      0 ≤ dI.lo ∧
      dI.lo ^ 2 ≤ lambdaInterval.lo ^ 2 - ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      lambdaInterval.hi ^ 2 - ((hI.nsmul 2 (by norm_num)).sub
        (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ dI.hi ^ 2 ∧
      (0 ≤ asinQI.lo ∧ asinQI.hi ≤ CompactCellCertificate.halfPiBox.lo) ∧
      (ScalarSuffixCertificate.sinTaylor27Interval asinQI.lo).hi ≤
        ((hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ∧
      ((hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinQI.hi).lo ∧
      (0 ≤ asinRI.lo ∧ asinRI.hi ≤ CompactCellCertificate.halfPiBox.lo) ∧
      (ScalarSuffixCertificate.sinTaylor27Interval asinRI.lo).hi ≤
        (ScalarSuffixCertificate.QInterval.divPos
          ((hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval,
            LeanSuffixReflective.QInterval.point])).lo ∧
      (ScalarSuffixCertificate.QInterval.divPos
          ((hI.nsmul 2 (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval,
            LeanSuffixReflective.QInterval.point])).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinRI.hi).lo) :
    uI.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      dI.RealContains (sqrt ((5 / 4 : ℝ) ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h / (5 / 4 : ℝ))) := by
  rcases hexact with ⟨hq0, hq1, hu0, hul, huh, hd0, hdl, hdh,
    haB, hal, hah, hrB, hrl, hrh⟩
  exact CompactCellCertificate.typeThree_atoms_of_exact_bounds
    lambdaInterval hI uI dI asinQI asinRI lambda_mem hh
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num) hq0 hq1 hu0 hul huh hd0 hdl hdh haB hal hah hrB hrl hrh

private theorem typeFour_atoms
    (hI uI dI asinHI asinRI : QInterval) {h : ℝ}
    (hh : hI.RealContains h) (hexact :
      0 ≤ (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ∧
      (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ≤ 1 ∧
      0 ≤ uI.lo ∧
      uI.lo ^ 2 ≤ 1 - (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      1 - (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
        (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ uI.hi ^ 2 ∧
      0 ≤ dI.lo ∧
      dI.lo ^ 2 ≤ lambdaInterval.lo ^ 2 -
        (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
          (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).hi ^ 2 ∧
      lambdaInterval.hi ^ 2 -
        (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
          (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1)).lo ^ 2 ≤ dI.hi ^ 2 ∧
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
          lambdaInterval (by norm_num [lambdaInterval,
            LeanSuffixReflective.QInterval.point])).lo ∧
      (ScalarSuffixCertificate.QInterval.divPos
          (((CompactCellCertificate.typeFourShiftedInterval hI).nsmul 2
            (by norm_num)).sub (LeanSuffixReflective.QInterval.point 1))
          lambdaInterval (by norm_num [lambdaInterval,
            LeanSuffixReflective.QInterval.point])).hi ≤
        (ScalarSuffixCertificate.sinTaylor27Interval asinRI.hi).lo) :
    uI.RealContains (sqrt (1 - h ^ 2)) ∧
      dI.RealContains (sqrt ((5 / 4 : ℝ) ^ 2 - h ^ 2)) ∧
      asinHI.RealContains (arcsin h) ∧
      asinRI.RealContains (arcsin (h / (5 / 4 : ℝ))) := by
  exact CompactCellCertificate.typeFour_atoms_of_exact_bounds
    lambdaInterval hI uI dI asinHI asinRI lambda_mem hh
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num) hexact

set_option linter.defProp false

private def h3_lower_atoms := typeThree_atoms
  (LeanSuffixReflective.QInterval.point h3RegularInterval.lo)
  h3ULower h3DLower h3AsinQLower h3AsinRLower
  (LeanSuffixReflective.QInterval.realContains_point h3RegularInterval.lo
    (h3RegularInterval.lo : ℝ) |>.2 rfl)
  (by norm_num [h3RegularInterval, h3ULower, h3DLower, h3AsinQLower, h3AsinRLower,
    lambdaInterval, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, CompactCellCertificate.halfPiBox,
    ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h3_upper_atoms := typeThree_atoms
  (LeanSuffixReflective.QInterval.point h3RegularInterval.hi)
  h3UUpper h3DUpper h3AsinQUpper h3AsinRUpper
  (LeanSuffixReflective.QInterval.realContains_point h3RegularInterval.hi
    (h3RegularInterval.hi : ℝ) |>.2 rfl)
  (by norm_num [h3RegularInterval, h3UUpper, h3DUpper, h3AsinQUpper, h3AsinRUpper,
    lambdaInterval, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, CompactCellCertificate.halfPiBox,
    ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h3_cell_atoms {h : ℝ} (hh : h3RegularInterval.RealContains h) :=
  typeThree_atoms h3RegularInterval h3UCell h3DCell h3AsinQCell h3AsinRCell hh
  (by norm_num [h3RegularInterval, h3UCell, h3DCell, h3AsinQCell, h3AsinRCell,
    lambdaInterval, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, CompactCellCertificate.halfPiBox,
    ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h4_lower_atoms := typeFour_atoms
  (LeanSuffixReflective.QInterval.point h4MatchingInterval.lo)
  h4ULower h4DLower h4AsinHLower h4AsinRLower
  (LeanSuffixReflective.QInterval.realContains_point h4MatchingInterval.lo
    (h4MatchingInterval.lo : ℝ) |>.2 rfl)
  (by norm_num [CompactCellCertificate.typeFourShiftedInterval, h4MatchingInterval,
    h4ULower, h4DLower, h4AsinHLower, h4AsinRLower, lambdaInterval,
    ScalarSuffixCertificate.sinTaylor27Interval, ScalarSuffixCertificate.sinTaylor27,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    CompactCellCertificate.halfPiBox, ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h4_upper_atoms := typeFour_atoms
  (LeanSuffixReflective.QInterval.point h4MatchingInterval.hi)
  h4UUpper h4DUpper h4AsinHUpper h4AsinRUpper
  (LeanSuffixReflective.QInterval.realContains_point h4MatchingInterval.hi
    (h4MatchingInterval.hi : ℝ) |>.2 rfl)
  (by norm_num [CompactCellCertificate.typeFourShiftedInterval, h4MatchingInterval,
    h4UUpper, h4DUpper, h4AsinHUpper, h4AsinRUpper, lambdaInterval,
    ScalarSuffixCertificate.sinTaylor27Interval, ScalarSuffixCertificate.sinTaylor27,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    CompactCellCertificate.halfPiBox, ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h4_cell_atoms {h : ℝ} (hh : h4MatchingInterval.RealContains h) :=
  typeFour_atoms h4MatchingInterval h4UCell h4DCell h4AsinHCell h4AsinRCell hh
  (by norm_num [CompactCellCertificate.typeFourShiftedInterval, h4MatchingInterval,
    h4UCell, h4DCell, h4AsinHCell, h4AsinRCell, lambdaInterval,
    ScalarSuffixCertificate.sinTaylor27Interval, ScalarSuffixCertificate.sinTaylor27,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point,
    CompactCellCertificate.halfPiBox, ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h4_second_lower_atoms := typeFour_atoms
  (LeanSuffixReflective.QInterval.point h4SecondInterval.lo)
  h4SecondULower h4SecondDLower h4SecondAsinHLower h4SecondAsinRLower
  (LeanSuffixReflective.QInterval.realContains_point h4SecondInterval.lo
    (h4SecondInterval.lo : ℝ) |>.2 rfl)
  (by norm_num [CompactCellCertificate.typeFourShiftedInterval, h4SecondInterval,
    h4SecondULower, h4SecondDLower, h4SecondAsinHLower, h4SecondAsinRLower,
    lambdaInterval, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, CompactCellCertificate.halfPiBox,
    ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h4_second_upper_atoms := typeFour_atoms
  (LeanSuffixReflective.QInterval.point h4SecondInterval.hi)
  h4SecondUUpper h4SecondDUpper h4SecondAsinHUpper h4SecondAsinRUpper
  (LeanSuffixReflective.QInterval.realContains_point h4SecondInterval.hi
    (h4SecondInterval.hi : ℝ) |>.2 rfl)
  (by norm_num [CompactCellCertificate.typeFourShiftedInterval, h4SecondInterval,
    h4SecondUUpper, h4SecondDUpper, h4SecondAsinHUpper, h4SecondAsinRUpper,
    lambdaInterval, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, CompactCellCertificate.halfPiBox,
    ScalarSuffixCertificate.piInterval, Nat.factorial])

private def h4_second_cell_atoms {h : ℝ}
    (hh : h4SecondInterval.RealContains h) :=
  typeFour_atoms h4SecondInterval h4SecondUCell h4SecondDCell
    h4SecondAsinHCell h4SecondAsinRCell hh
  (by norm_num [CompactCellCertificate.typeFourShiftedInterval, h4SecondInterval,
    h4SecondUCell, h4SecondDCell, h4SecondAsinHCell, h4SecondAsinRCell,
    lambdaInterval, ScalarSuffixCertificate.sinTaylor27Interval,
    ScalarSuffixCertificate.sinTaylor27, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, ScalarSuffixCertificate.QInterval.mul,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.point, CompactCellCertificate.halfPiBox,
    ScalarSuffixCertificate.piInterval, Nat.factorial])
private def typeThree_enclosure
    (hI uI dI asinQI asinRI : QInterval) {h : ℝ}
    (hh : hI.RealContains h) (hatoms :
      uI.RealContains (sqrt (1 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      dI.RealContains (sqrt ((5 / 4 : ℝ) ^ 2 - LeanSuffixAnalytic.typeThreeShape h ^ 2)) ∧
      asinQI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h)) ∧
      asinRI.RealContains (arcsin (LeanSuffixAnalytic.typeThreeShape h / (5 / 4 : ℝ)))) :=
  CompactCellCertificate.typeThree_area_perimeter_atom_enclosure
    lambdaInterval hI uI dI asinQI asinRI lambda_mem hh hatoms
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
set_option maxHeartbeats 1000000 in
-- Exact normalization of the degree-27 rational Taylor inequalities is large.
private theorem endpoint_asin_enclosure :
    endpointAsinR.RealContains (arcsin (((4 / 5 : ℚ) : ℝ))) := by
  refine CompactCellCertificate.QInterval.realContains_arcsin_of_taylor
    endpointAsinR (4 / 5 : ℚ) (by norm_num) ?_ ?_ ?_
  · constructor <;> constructor
    · have hp := Real.pi_pos
      norm_num [endpointAsinR]
      linarith
    · have hp := Real.pi_gt_three
      norm_num [endpointAsinR]
      linarith
    · have hp := Real.pi_pos
      norm_num [endpointAsinR]
      linarith
    · have hp := Real.pi_gt_three
      norm_num [endpointAsinR]
      linarith
  · norm_num [endpointAsinR, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, Nat.factorial]
  · norm_num [endpointAsinR, ScalarSuffixCertificate.sinTaylor27Interval,
      ScalarSuffixCertificate.sinTaylor27, Nat.factorial]
private theorem endpoint_area_formula :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 =
      13 * π / 8 - 5 * arcsin (4 / 5 : ℝ) / 4 + 9 / 5 := by
  unfold LeanSuffixAnalytic.typeThreeArea LeanSuffixAnalytic.typeThreeAngle
    LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape
  norm_num [Real.arcsin_one, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring
private theorem typeFour_endpoint_area_formula :
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) 1 =
      9 * π / 4 - 5 * arcsin (4 / 5 : ℝ) / 2 + 6 / 5 := by
  unfold LeanSuffixAnalytic.typeFourArea LeanSuffixAnalytic.typeFourAngle
    LeanSuffixAnalytic.typeFourDelta
  norm_num [Real.arcsin_one, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring

private theorem endpoint_perimeter_formula :
    LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 =
      13 * π / 4 - 5 * arcsin (4 / 5 : ℝ) / 2 + 6 / 5 := by
  unfold LeanSuffixAnalytic.typeThreePerimeter LeanSuffixAnalytic.typeThreeAngle
    LeanSuffixAnalytic.typeThreeDelta LeanSuffixAnalytic.typeThreeShape
  norm_num [Real.arcsin_one, Real.arccos_eq_pi_div_two_sub_arcsin]
  ring
private theorem endpoint_enclosure :
    endpointAreaBox.RealContains (LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) ∧
    endpointPerimeterBox.RealContains (LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1) := by
  have ha := endpoint_asin_enclosure
  have hp := ScalarSuffixCertificate.piInterval_sound
  rw [endpoint_area_formula, endpoint_perimeter_formula]
  norm_num [endpointAreaBox, endpointPerimeterBox, endpointAsinR,
    ScalarSuffixCertificate.piInterval,
    LeanSuffixReflective.QInterval.RealContains] at ha hp ⊢
  constructor <;> constructor <;> linarith

private theorem h3_lower_area_enclosure : h3AreaLowerBox.RealContains
    (LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (h3RegularInterval.lo : ℝ)) := by
  have h := (typeThree_enclosure
    (LeanSuffixReflective.QInterval.point h3RegularInterval.lo)
    h3ULower h3DLower h3AsinQLower h3AsinRLower
    (LeanSuffixReflective.QInterval.realContains_point h3RegularInterval.lo
      (h3RegularInterval.lo : ℝ) |>.2 rfl) h3_lower_atoms
    (by norm_num [h3RegularInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3RegularInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])).1
  norm_num [h3AreaLowerBox, CompactCellCertificate.typeThreeAreaBox,
    CompactCellCertificate.typeThreeAngleBox, CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    h3RegularInterval, h3ULower, h3DLower, h3AsinQLower, h3AsinRLower,
    lambdaInterval, ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem h3_upper_area_enclosure : h3AreaUpperBox.RealContains
    (LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (h3RegularInterval.hi : ℝ)) := by
  have h := (typeThree_enclosure
    (LeanSuffixReflective.QInterval.point h3RegularInterval.hi)
    h3UUpper h3DUpper h3AsinQUpper h3AsinRUpper
    (LeanSuffixReflective.QInterval.realContains_point h3RegularInterval.hi
      (h3RegularInterval.hi : ℝ) |>.2 rfl) h3_upper_atoms
    (by norm_num [h3RegularInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h3RegularInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point])).1
  norm_num [h3AreaUpperBox, CompactCellCertificate.typeThreeAreaBox,
    CompactCellCertificate.typeThreeAngleBox, CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    h3RegularInterval, h3UUpper, h3DUpper, h3AsinQUpper, h3AsinRUpper,
    lambdaInterval, ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private def typeFour_enclosure
    (hI uI dI asinHI asinRI : QInterval) {h : ℝ}
    (hh : hI.RealContains h) (hatoms :
      uI.RealContains (sqrt (1 - h ^ 2)) ∧
      dI.RealContains (sqrt ((5 / 4 : ℝ) ^ 2 - h ^ 2)) ∧
      asinHI.RealContains (arcsin h) ∧
      asinRI.RealContains (arcsin (h / (5 / 4 : ℝ)))) :=
  CompactCellCertificate.typeFour_atom_enclosures
    lambdaInterval hI uI dI asinHI asinRI lambda_mem hh hatoms
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])

private theorem h4_lower_area_enclosure : h4AreaLowerBox.RealContains
    (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4MatchingInterval.lo : ℝ)) := by
  have h := (typeFour_enclosure
    (LeanSuffixReflective.QInterval.point h4MatchingInterval.lo)
    h4ULower h4DLower h4AsinHLower h4AsinRLower
    (LeanSuffixReflective.QInterval.realContains_point h4MatchingInterval.lo
      (h4MatchingInterval.lo : ℝ) |>.2 rfl) h4_lower_atoms
    (by norm_num [h4MatchingInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4MatchingInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [h4ULower])
    (by norm_num [h4DLower])).1
  norm_num [h4AreaLowerBox, CompactCellCertificate.typeFourAreaBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, h4MatchingInterval, h4ULower, h4DLower,
    h4AsinHLower, h4AsinRLower, lambdaInterval, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem h4_upper_area_enclosure : h4AreaUpperBox.RealContains
    (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4MatchingInterval.hi : ℝ)) := by
  have h := (typeFour_enclosure
    (LeanSuffixReflective.QInterval.point h4MatchingInterval.hi)
    h4UUpper h4DUpper h4AsinHUpper h4AsinRUpper
    (LeanSuffixReflective.QInterval.realContains_point h4MatchingInterval.hi
      (h4MatchingInterval.hi : ℝ) |>.2 rfl) h4_upper_atoms
    (by norm_num [h4MatchingInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4MatchingInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [h4UUpper])
    (by norm_num [h4DUpper])).1
  norm_num [h4AreaUpperBox, CompactCellCertificate.typeFourAreaBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, h4MatchingInterval, h4UUpper, h4DUpper,
    h4AsinHUpper, h4AsinRUpper, lambdaInterval, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem h4_second_lower_area_enclosure :
    h4SecondAreaLowerBox.RealContains
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4SecondInterval.lo : ℝ)) := by
  have h := (typeFour_enclosure
    (LeanSuffixReflective.QInterval.point h4SecondInterval.lo)
    h4SecondULower h4SecondDLower h4SecondAsinHLower h4SecondAsinRLower
    (LeanSuffixReflective.QInterval.realContains_point h4SecondInterval.lo
      (h4SecondInterval.lo : ℝ) |>.2 rfl) h4_second_lower_atoms
    (by norm_num [h4SecondInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4SecondInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [h4SecondULower])
    (by norm_num [h4SecondDLower])).1
  norm_num [h4SecondAreaLowerBox, CompactCellCertificate.typeFourAreaBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, h4SecondInterval, h4SecondULower,
    h4SecondDLower, h4SecondAsinHLower, h4SecondAsinRLower, lambdaInterval,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem h4_second_upper_area_enclosure :
    h4SecondAreaUpperBox.RealContains
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4SecondInterval.hi : ℝ)) := by
  have h := (typeFour_enclosure
    (LeanSuffixReflective.QInterval.point h4SecondInterval.hi)
    h4SecondUUpper h4SecondDUpper h4SecondAsinHUpper h4SecondAsinRUpper
    (LeanSuffixReflective.QInterval.realContains_point h4SecondInterval.hi
      (h4SecondInterval.hi : ℝ) |>.2 rfl) h4_second_upper_atoms
    (by norm_num [h4SecondInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4SecondInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [h4SecondUUpper])
    (by norm_num [h4SecondDUpper])).1
  norm_num [h4SecondAreaUpperBox, CompactCellCertificate.typeFourAreaBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, h4SecondInterval, h4SecondUUpper,
    h4SecondDUpper, h4SecondAsinHUpper, h4SecondAsinRUpper, lambdaInterval,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

private theorem h4_second_cell_enclosure {h : ℝ}
    (hh : h4SecondInterval.RealContains h) :
    h4SecondPerimeterCellBox.RealContains
        (LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h) ∧
      h4SecondFoldCellBox.RealContains
        (LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) h) := by
  have he := typeFour_enclosure h4SecondInterval h4SecondUCell h4SecondDCell
    h4SecondAsinHCell h4SecondAsinRCell hh (h4_second_cell_atoms hh)
    (by norm_num [h4SecondInterval])
    (by norm_num [h4SecondInterval, ScalarSuffixCertificate.QInterval.mul])
    (by norm_num [h4SecondUCell]) (by norm_num [h4SecondDCell])
  rcases he.2 with ⟨hp, hf⟩
  norm_num [h4SecondPerimeterCellBox, h4SecondFoldCellBox,
    CompactCellCertificate.typeFourPerimeterBox,
    CompactCellCertificate.typeFourFoldBox, CompactCellCertificate.typeFourAngleBox,
    CompactCellCertificate.halfPiBox, h4SecondInterval, h4SecondUCell,
    h4SecondDCell, h4SecondAsinHCell, h4SecondAsinRCell, lambdaInterval,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hp hf ⊢
  exact ⟨⟨by linarith [hp.1], by linarith [hp.2]⟩,
    ⟨by linarith [hf.1], by linarith [hf.2]⟩⟩

set_option linter.defProp true

/-- Direct degree-27 Taylor certificate for the endpoint area. -/
theorem endpoint_area_bounds :
    (5745967 / 1000000 : ℝ) ≤ LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ≤ 5745970 / 1000000 := by
  simpa [endpointAreaBox, LeanSuffixReflective.QInterval.RealContains] using
    endpoint_enclosure.1
/-- The `h₄ = 1` type-(iv) endpoint has strictly more area than the
type-(iii) endpoint.  In particular, it is not a third endpoint-area root. -/
theorem endpoint_area_lt_typeFour_endpoint :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 <
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) 1 := by
  have ha := endpoint_asin_enclosure
  have hp := ScalarSuffixCertificate.piInterval_sound
  rw [endpoint_area_formula, typeFour_endpoint_area_formula]
  norm_num [endpointAsinR, ScalarSuffixCertificate.piInterval,
    LeanSuffixReflective.QInterval.RealContains] at ha hp ⊢
  linarith


/-- Direct degree-27 Taylor certificate for the endpoint perimeter. -/
theorem endpoint_perimeter_bounds :
    (9091934 / 1000000 : ℝ) ≤ LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 ≤ 9091940 / 1000000 := by
  simpa [endpointPerimeterBox, LeanSuffixReflective.QInterval.RealContains] using
    endpoint_enclosure.2

private theorem h3_lower_area_gt_endpoint :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 <
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (h3RegularInterval.lo : ℝ) := by
  have he := endpoint_enclosure.1
  have hl := h3_lower_area_enclosure
  norm_num [endpointAreaBox, h3AreaLowerBox,
    LeanSuffixReflective.QInterval.RealContains] at he hl ⊢
  linarith [he.2, hl.1]

private theorem h3_upper_area_lt_endpoint :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (h3RegularInterval.hi : ℝ) <
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := by
  have he := endpoint_enclosure.1
  have hu := h3_upper_area_enclosure
  norm_num [endpointAreaBox, h3AreaUpperBox,
    LeanSuffixReflective.QInterval.RealContains] at he hu ⊢
  linarith [he.1, hu.2]

private theorem h4_lower_area_gt_endpoint :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 <
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4MatchingInterval.lo : ℝ) := by
  have he := endpoint_enclosure.1
  have hl := h4_lower_area_enclosure
  norm_num [endpointAreaBox, h4AreaLowerBox,
    LeanSuffixReflective.QInterval.RealContains] at he hl ⊢
  linarith [he.2, hl.1]

private theorem h4_upper_area_lt_endpoint :
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4MatchingInterval.hi : ℝ) <
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := by
  have he := endpoint_enclosure.1
  have hu := h4_upper_area_enclosure
  norm_num [endpointAreaBox, h4AreaUpperBox,
    LeanSuffixReflective.QInterval.RealContains] at he hu ⊢
  linarith [he.1, hu.2]

private theorem h4_second_lower_area_lt_endpoint :
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4SecondInterval.lo : ℝ) <
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := by
  have he := endpoint_enclosure.1
  have hl := h4_second_lower_area_enclosure
  norm_num [endpointAreaBox, h4SecondAreaLowerBox,
    LeanSuffixReflective.QInterval.RealContains] at he hl ⊢
  linarith [hl.2, he.1]

private theorem endpoint_lt_h4_second_upper_area :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 <
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) (h4SecondInterval.hi : ℝ) := by
  have he := endpoint_enclosure.1
  have hu := h4_second_upper_area_enclosure
  norm_num [endpointAreaBox, h4SecondAreaUpperBox,
    LeanSuffixReflective.QInterval.RealContains] at he hu ⊢
  linarith [he.2, hu.1]

/-- Throughout the regular root slab, the type-(iii) perimeter is below the
endpoint type-(iii) perimeter. -/
theorem regular_perimeter_lt_endpoint {h : ℝ}
    (hh : h3RegularInterval.RealContains h) :
    LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) h <
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 := by
  have hp := (typeThree_enclosure h3RegularInterval h3UCell h3DCell
    h3AsinQCell h3AsinRCell hh (h3_cell_atoms hh)
    (by norm_num [h3RegularInterval])
    (by norm_num [h3RegularInterval, ScalarSuffixCertificate.QInterval.mul])).2
  have he := endpoint_enclosure.2
  norm_num [h3PerimeterCellBox, endpointPerimeterBox,
    CompactCellCertificate.typeThreePerimeterBox,
    CompactCellCertificate.typeThreeAngleBox, CompactCellCertificate.typeThreeDeltaBox,
    CompactCellCertificate.typeThreeQBox, CompactCellCertificate.halfPiBox,
    h3RegularInterval, h3UCell, h3DCell, h3AsinQCell, h3AsinRCell,
    lambdaInterval, ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hp
  norm_num [endpointPerimeterBox, LeanSuffixReflective.QInterval.RealContains] at he ⊢
  linarith [hp.2, he.1]

/-- Throughout the matching type-(iv) slab, the endpoint type-(iii) perimeter
is strictly smaller than the type-(iv) perimeter. -/
theorem endpoint_perimeter_lt_typeFour {h : ℝ}
    (hh : h4MatchingInterval.RealContains h) :
    LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
      LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h := by
  have hp := (typeFour_enclosure h4MatchingInterval h4UCell h4DCell
    h4AsinHCell h4AsinRCell hh (h4_cell_atoms hh)
    (by norm_num [h4MatchingInterval])
    (by norm_num [h4MatchingInterval, ScalarSuffixCertificate.QInterval.mul])
    (by norm_num [h4UCell]) (by norm_num [h4DCell])).2.1
  have he := endpoint_enclosure.2
  norm_num [h4PerimeterCellBox, CompactCellCertificate.typeFourPerimeterBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    h4MatchingInterval, h4AsinHCell, h4AsinRCell, lambdaInterval,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hp
  norm_num [endpointPerimeterBox, LeanSuffixReflective.QInterval.RealContains] at he ⊢
  linarith [he.2, hp.1]

/-- The lower matching root slab lies strictly on the descending,
nonstationary type-(iv) branch. -/
theorem typeFourFold_neg_matching {h : ℝ}
    (hh : h4MatchingInterval.RealContains h) :
    LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) h < 0 := by
  have hf := (typeFour_enclosure h4MatchingInterval h4UCell h4DCell
    h4AsinHCell h4AsinRCell hh (h4_cell_atoms hh)
    (by norm_num [h4MatchingInterval])
    (by norm_num [h4MatchingInterval, ScalarSuffixCertificate.QInterval.mul])
    (by norm_num [h4UCell]) (by norm_num [h4DCell])).2.2
  norm_num [CompactCellCertificate.typeFourFoldBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    h4MatchingInterval, h4UCell, h4DCell, h4AsinHCell, h4AsinRCell,
    lambdaInterval, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at hf ⊢
  linarith [hf.2]

/-- Throughout the second, near-one type-(iv) root slab, the endpoint
type-(iii) perimeter is strictly smaller than the type-(iv) perimeter. -/
theorem endpoint_perimeter_lt_typeFour_second {h : ℝ}
    (hh : h4SecondInterval.RealContains h) :
    LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
      LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h := by
  have hp := (h4_second_cell_enclosure hh).1
  have he := endpoint_enclosure.2
  norm_num [h4SecondPerimeterCellBox, endpointPerimeterBox,
    LeanSuffixReflective.QInterval.RealContains] at hp he ⊢
  linarith [he.2, hp.1]

/-- The second root slab lies strictly on a nonstationary type-(iv) branch. -/
theorem typeFourFold_pos_second {h : ℝ}
    (hh : h4SecondInterval.RealContains h) :
    0 < LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) h := by
  have hf := (h4_second_cell_enclosure hh).2
  norm_num [h4SecondFoldCellBox,
    LeanSuffixReflective.QInterval.RealContains] at hf ⊢
  linarith [hf.1]

/-- The second regular type-(iii) equal-area root exists in the certified slab
and strictly improves on the endpoint perimeter. -/
theorem exists_regular_h3 :
    ∃ h : ℝ, h3RegularInterval.RealContains h ∧
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) h =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) h <
        LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 := by
  let f : ℝ → ℝ := fun h => LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 -
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) h
  have hc : ContinuousOn f
      (Icc (h3RegularInterval.lo : ℝ) (h3RegularInterval.hi : ℝ)) := by
    intro h hh
    have hr : 0 < h ∧ h < 1 := by
      norm_num [h3RegularInterval] at hh ⊢
      exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
        lt_of_le_of_lt hh.2 (by norm_num)⟩
    exact
      (continuousAt_const.sub
        (LeanSuffixAnalytic.hasDerivAt_typeThreeArea
          (by norm_num) hr.1 hr.2).continuousAt).continuousWithinAt
  rcases ScalarSuffixCertificate.oppositeFace_zero
      (show (h3RegularInterval.lo : ℝ) ≤ h3RegularInterval.hi by
        norm_num [h3RegularInterval]) hc
      (le_of_lt (sub_neg.mpr h3_lower_area_gt_endpoint))
      (le_of_lt (sub_pos.mpr h3_upper_area_lt_endpoint)) with ⟨h, hh, hz⟩
  refine ⟨h, ?_, ?_, regular_perimeter_lt_endpoint ?_⟩
  · simpa [LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh
  · dsimp [f] at hz
    linarith
  · simpa [LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh

/-- A type-(iv) height matching the type-(iii) endpoint area exists in the
certified slab. -/
theorem exists_matching_h4 :
    ∃ h : ℝ, h4MatchingInterval.RealContains h ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
        LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h := by
  let f : ℝ → ℝ := fun h => LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 -
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h
  have hc : ContinuousOn f
      (Icc (h4MatchingInterval.lo : ℝ) (h4MatchingInterval.hi : ℝ)) := by
    intro h hh
    have hr : 0 < h ∧ h < 1 := by
      norm_num [h4MatchingInterval] at hh ⊢
      exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
        lt_of_le_of_lt hh.2 (by norm_num)⟩
    exact
      (continuousAt_const.sub
        (LeanSuffixAnalytic.hasDerivAt_typeFourArea
          (by norm_num) hr.1 hr.2).continuousAt).continuousWithinAt
  rcases ScalarSuffixCertificate.oppositeFace_zero
      (show (h4MatchingInterval.lo : ℝ) ≤ h4MatchingInterval.hi by
        norm_num [h4MatchingInterval]) hc
      (le_of_lt (sub_neg.mpr h4_lower_area_gt_endpoint))
      (le_of_lt (sub_pos.mpr h4_upper_area_lt_endpoint)) with ⟨h, hh, hz⟩
  refine ⟨h, ?_, ?_, endpoint_perimeter_lt_typeFour ?_⟩
  · simpa [LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh
  · dsimp [f] at hz
    linarith
  · simpa [LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh

/-- The second, near-one type-(iv) height matching the endpoint area exists in
the certified slab.  Its perimeter is larger than the endpoint type-(iii)
perimeter and its fold numerator is strictly positive. -/
theorem exists_second_h4 :
    ∃ h : ℝ, h4SecondInterval.RealContains h ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
        LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h ∧
      0 < LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) h := by
  let f : ℝ → ℝ := fun h => LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h -
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1
  have hc : ContinuousOn f
      (Icc (h4SecondInterval.lo : ℝ) (h4SecondInterval.hi : ℝ)) := by
    intro h hh
    have hr : 0 < h ∧ h < 1 := by
      norm_num [h4SecondInterval] at hh ⊢
      exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
        lt_of_le_of_lt hh.2 (by norm_num)⟩
    exact
      ((LeanSuffixAnalytic.hasDerivAt_typeFourArea
          (by norm_num) hr.1 hr.2).continuousAt.sub
        continuousAt_const).continuousWithinAt
  rcases ScalarSuffixCertificate.oppositeFace_zero
      (show (h4SecondInterval.lo : ℝ) ≤ h4SecondInterval.hi by
        norm_num [h4SecondInterval]) hc
      (le_of_lt (sub_neg.mpr h4_second_lower_area_lt_endpoint))
      (le_of_lt (sub_pos.mpr endpoint_lt_h4_second_upper_area)) with ⟨h, hh, hz⟩
  have hh' : h4SecondInterval.RealContains h := by
    simpa [LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh
  refine ⟨h, hh', ?_, endpoint_perimeter_lt_typeFour_second hh',
    typeFourFold_pos_second hh'⟩
  dsimp [f] at hz
  linarith

/-- The scalar closure certificate with one root of each modeled type and the
strict perimeter chain through the endpoint. -/
theorem endpoint_closure_exists :
    ∃ h3 h4 : ℝ, h3RegularInterval.RealContains h3 ∧
      h4MatchingInterval.RealContains h4 ∧
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) h3 =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h4 =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) h3 <
        LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
        LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h4 := by
  rcases exists_regular_h3 with ⟨h3, hh3, ha3, hp3⟩
  rcases exists_matching_h4 with ⟨h4, hh4, ha4, hp4⟩
  exact ⟨h3, h4, hh3, hh4, ha3, ha4, hp3, hp4⟩

/-- The endpoint area has a certified regular type-(iii) replacement and two
distinct certified regular type-(iv) roots, one on each side of the type-(iv)
fold. -/
theorem endpoint_three_roots_exist :
    ∃ h3 h4Lower h4Upper : ℝ,
      h3RegularInterval.RealContains h3 ∧
      h4MatchingInterval.RealContains h4Lower ∧
      h4SecondInterval.RealContains h4Upper ∧
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) h3 =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h4Lower =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h4Upper =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) h3 <
        LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
        LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h4Lower ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) 1 <
        LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h4Upper ∧
      LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) h4Lower < 0 ∧
      0 < LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) h4Upper := by
  rcases endpoint_closure_exists with ⟨h3, h4Lower, hh3, hh4Lower,
    ha3, ha4Lower, hp3, hp4Lower⟩
  rcases exists_second_h4 with ⟨h4Upper, hh4Upper, ha4Upper, hp4Upper,
    hfoldUpper⟩
  exact ⟨h3, h4Lower, h4Upper, hh3, hh4Lower, hh4Upper, ha3,
    ha4Lower, ha4Upper, hp3, hp4Lower, hp4Upper,
    typeFourFold_neg_matching hh4Lower, hfoldUpper⟩


/-- The type-(iii) endpoint-area equation has exactly one regular root. -/
theorem typeThree_endpoint_area_roots_existsUnique :
    ∃! h : ℝ, h ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) h =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 := by
  rcases exists_regular_h3 with ⟨root, hroot, hareaRoot, _⟩
  have hrootReg : root ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num [h3RegularInterval]) hroot.1,
      lt_of_le_of_lt hroot.2 (by norm_num [h3RegularInterval])⟩
  refine ⟨root, ⟨hrootReg, hareaRoot⟩, ?_⟩
  intro h hharea
  rcases hharea with ⟨hh, harea⟩
  rcases lt_trichotomy h root with hlt | heq | hgt
  · exact (LeanSuffixAnalytic.typeThreeArea_not_three_roots
      (lam := (5 / 4 : ℝ)) (by norm_num)
      ⟨hh.1, hh.2.le⟩ ⟨hrootReg.1, hrootReg.2.le⟩
      (by constructor <;> norm_num) hlt hrootReg.2
      ⟨harea.trans hareaRoot.symm, hareaRoot⟩).elim
  · exact heq
  · exact (LeanSuffixAnalytic.typeThreeArea_not_three_roots
      (lam := (5 / 4 : ℝ)) (by norm_num)
      ⟨hrootReg.1, hrootReg.2.le⟩ ⟨hh.1, hh.2.le⟩
      (by constructor <;> norm_num) hgt hh.2
      ⟨hareaRoot.trans harea.symm, harea⟩).elim

/-- The certified slab exhausts the regular type-(iii) heights having the
type-(iii) endpoint area. -/
theorem typeThree_endpoint_area_root_classification {h : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1)
    (harea : LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) h =
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    h3RegularInterval.RealContains h := by
  rcases typeThree_endpoint_area_roots_existsUnique with
    ⟨root, _, hunique⟩
  rcases exists_regular_h3 with ⟨slabRoot, hslab, hareaSlab, _⟩
  have hslabReg : slabRoot ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num [h3RegularInterval]) hslab.1,
      lt_of_le_of_lt hslab.2 (by norm_num [h3RegularInterval])⟩
  have hhEq : h = root := hunique h ⟨hh, harea⟩
  have hslabEq : slabRoot = root :=
    hunique slabRoot ⟨hslabReg, hareaSlab⟩
  simpa [hhEq.trans hslabEq.symm] using hslab

/-- Rolle's theorem turns two distinct regular heights with equal type-(iv)
area into a zero of the type-(iv) fold between them. -/
private theorem typeFourFold_zero_between_of_area_eq {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b)
    (harea : LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) a =
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) b) :
    ∃ c ∈ Ioo a b,
      LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) c = 0 := by
  have hcont : ContinuousOn
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)) (Icc a b) := by
    intro x hx
    have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
    exact (LeanSuffixAnalytic.hasDerivAt_typeFourArea
      (by norm_num) hxreg.1 hxreg.2).continuousAt.continuousWithinAt
  rcases exists_deriv_eq_zero hab hcont harea with ⟨c, hc, hzero⟩
  have hcreg : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.1.trans hc.1, hc.2.trans hb.2⟩
  rw [(LeanSuffixAnalytic.hasDerivAt_typeFourArea
    (by norm_num) hcreg.1 hcreg.2).deriv] at hzero
  refine ⟨c, hc, ?_⟩
  exact (div_eq_zero_iff.mp hzero).resolve_right
    (pow_ne_zero 3 (ne_of_gt hcreg.1))

/-- A regular type-(iv) area fiber contains at most two heights. -/
private theorem typeFourArea_not_three_roots {a b c : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) (hbc : b < c)
    (hareaAB : LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) a =
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) b)
    (hareaBC : LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) b =
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) c) : False := by
  rcases typeFourFold_zero_between_of_area_eq ha hb hab hareaAB with
    ⟨x, hx, hfoldX⟩
  rcases typeFourFold_zero_between_of_area_eq hb hc hbc hareaBC with
    ⟨y, hy, hfoldY⟩
  have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hyreg : y ∈ Ioo (0 : ℝ) 1 :=
    ⟨hb.1.trans hy.1, hy.2.trans hc.2⟩
  have hxy : x < y := hx.2.trans hy.1
  have hmono := LeanSuffixAnalytic.typeFourFold_strictMonoOn
    (lam := (5 / 4 : ℝ)) (by norm_num) hxreg hyreg hxy
  rw [hfoldX, hfoldY] at hmono
  exact (lt_irrefl 0 hmono).elim

/-- The endpoint-area equation has exactly two regular type-(iv) roots, one
in each certified slab. -/
theorem typeFour_endpoint_area_roots_exactly_two :
    ∃ lower upper : ℝ,
      h4MatchingInterval.RealContains lower ∧
      h4SecondInterval.RealContains upper ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) lower =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) upper =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 ∧
      lower < upper ∧
      ∀ h : ℝ, h ∈ Ioo (0 : ℝ) 1 →
        LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h =
          LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 →
        h = lower ∨ h = upper := by
  rcases exists_matching_h4 with ⟨lower, hlower, hareaLower, _⟩
  rcases exists_second_h4 with ⟨upper, hupper, hareaUpper, _, _⟩
  have hlowerReg : lower ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨lt_of_lt_of_le (by norm_num [h4MatchingInterval]) hlower.1,
      lt_of_le_of_lt hlower.2 (by norm_num [h4MatchingInterval])⟩
  have hupperReg : upper ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨lt_of_lt_of_le (by norm_num [h4SecondInterval]) hupper.1,
      lt_of_le_of_lt hupper.2 (by norm_num [h4SecondInterval])⟩
  have hlowerUpper : lower < upper :=
    lt_of_le_of_lt hlower.2 (lt_of_lt_of_le
      (by norm_num [h4MatchingInterval, h4SecondInterval]) hupper.1)
  refine ⟨lower, upper, hlower, hupper, hareaLower, hareaUpper,
    hlowerUpper, ?_⟩
  intro h hh harea
  rcases lt_trichotomy h lower with hlt | heq | hgt
  · exact (typeFourArea_not_three_roots hh hlowerReg hupperReg
      hlt hlowerUpper (harea.trans hareaLower.symm)
      (hareaLower.trans hareaUpper.symm)).elim
  · exact Or.inl heq
  · rcases lt_trichotomy h upper with hlt | heq | hgt'
    · exact (typeFourArea_not_three_roots hlowerReg hh hupperReg
        hgt hlt (hareaLower.trans harea.symm)
        (harea.trans hareaUpper.symm)).elim
    · exact Or.inr heq
    · exact (typeFourArea_not_three_roots hlowerReg hupperReg hh
        hlowerUpper hgt' (hareaLower.trans hareaUpper.symm)
        (hareaUpper.trans harea.symm)).elim

/-- The two certified slabs exhaust the regular type-(iv) heights having the
type-(iii) endpoint area. -/
theorem typeFour_endpoint_area_root_classification {h : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1)
    (harea : LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h =
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    h4MatchingInterval.RealContains h ∨
      h4SecondInterval.RealContains h := by
  rcases typeFour_endpoint_area_roots_exactly_two with
    ⟨lower, upper, hlower, hupper, _, _, _, hroots⟩
  rcases hroots h hh harea with heq | heq
  · left
    simpa [heq] using hlower
  · right
    simpa [heq] using hupper

/-- Every genuine type-(iv) candidate in the matching slab whose weighted area
is the type-(iii) endpoint area is defeated by the certified regular type-(iii)
root.  The CMV hypotheses are used only to identify the candidate's scalar
model; no stationarity is assumed. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    (candidate : _root_.FourArcCandidate (5 / 4 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hh : h4MatchingInterval.RealContains candidate.h)
    (harea : candidate.WeightedArea =
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases exists_regular_h3 with ⟨h3, hh3, ha3, hp3⟩
  have hh3_pos : 0 < h3 :=
    lt_of_lt_of_le (by norm_num [h3RegularInterval]) hh3.1
  have hh3_one : h3 < 1 :=
    lt_of_le_of_lt hh3.2 (by norm_num [h3RegularInterval])
  let a : _root_.TypeThreeAssembly (5 / 4 : ℝ) :=
    { h := h3
      density_jump := by norm_num
      h_pos := hh3_pos
      h_lt_one := hh3_one }
  rcases a.hasModeledCompetitor with ⟨realization⟩
  apply candidate.not_isWeightedPerimeterMinimizer_of_typeThree a realization
  · rw [CMVSuffixModel.TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea a]
    exact ha3.trans harea.symm
  · rw [CMVSuffixModel.TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter a,
      CMVSuffixModel.FourArcCandidate.weightedPerimeter_eq_typeFourPerimeter
        candidate hcandidate]
    exact hp3.trans (endpoint_perimeter_lt_typeFour hh)

/-- A genuine type-(iv) candidate in the second, near-one endpoint-area root
slab is defeated by the same regular type-(iii) replacement. -/
theorem second_candidate_not_isWeightedPerimeterMinimizer
    (candidate : _root_.FourArcCandidate (5 / 4 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hh : h4SecondInterval.RealContains candidate.h)
    (harea : candidate.WeightedArea =
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases exists_regular_h3 with ⟨h3, hh3, ha3, hp3⟩
  have hh3_pos : 0 < h3 :=
    lt_of_lt_of_le (by norm_num [h3RegularInterval]) hh3.1
  have hh3_one : h3 < 1 :=
    lt_of_le_of_lt hh3.2 (by norm_num [h3RegularInterval])
  let a : _root_.TypeThreeAssembly (5 / 4 : ℝ) :=
    { h := h3
      density_jump := by norm_num
      h_pos := hh3_pos
      h_lt_one := hh3_one }
  rcases a.hasModeledCompetitor with ⟨realization⟩
  apply candidate.not_isWeightedPerimeterMinimizer_of_typeThree a realization
  · rw [CMVSuffixModel.TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea a]
    exact ha3.trans harea.symm
  · rw [CMVSuffixModel.TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter a,
      CMVSuffixModel.FourArcCandidate.weightedPerimeter_eq_typeFourPerimeter
        candidate hcandidate]
    exact hp3.trans (endpoint_perimeter_lt_typeFour_second hh)

/-- Every regular genuine type-(iv) candidate at `λ = 5/4` with the
type-(iii) endpoint area is defeated.  Root-slab membership and stationarity
are derived rather than assumed. -/
theorem regular_candidate_not_isWeightedPerimeterMinimizer
    (candidate : _root_.FourArcCandidate (5 / 4 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1)
    (harea : candidate.WeightedArea =
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  have hscalar :
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) candidate.h =
        LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 :=
    (CMVSuffixModel.FourArcCandidate.regular_weightedArea_eq_typeFourArea
      candidate hcandidate hregular).symm.trans harea
  rcases typeFour_endpoint_area_root_classification
      ⟨candidate.h_pos, hregular⟩ hscalar with hh | hh
  · exact candidate_not_isWeightedPerimeterMinimizer
      candidate hcandidate hh harea
  · exact second_candidate_not_isWeightedPerimeterMinimizer
      candidate hcandidate hh harea

/-- Every genuine type-(iv) candidate at `λ = 5/4` whose weighted area is the
type-(iii) endpoint area is defeated.  The regular branch is exhausted by the
two certified roots; the `h₄ = 1` branch is impossible by the strict endpoint
area inequality. -/
theorem endpoint_area_candidate_not_isWeightedPerimeterMinimizer
    (candidate : _root_.FourArcCandidate (5 / 4 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (harea : candidate.WeightedArea =
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases lt_or_eq_of_le candidate.h_le_one with hregular | hendpoint
  · exact regular_candidate_not_isWeightedPerimeterMinimizer
      candidate hcandidate hregular harea
  · intro _
    have hscalar :
        LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) candidate.h =
          LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) 1 :=
      (CMVSuffixModel.FourArcCandidate.endpoint_weightedArea_eq_typeFourArea
        candidate hcandidate hendpoint).symm.trans harea
    rw [hendpoint] at hscalar
    exact endpoint_area_lt_typeFour_endpoint.ne hscalar.symm

end EndpointClosureCell
