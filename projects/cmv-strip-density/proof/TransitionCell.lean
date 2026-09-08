/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CompactCellCertificate
import CMVSuffixModel

/-!
# The exact semicircular transition cell

A kernel-checked rational/Taylor certificate for the type-(iii)/type-(iv)
transition at `lambda = 5/4` and type-(iii) height `1/2`.
-/

open Real Set
noncomputable section

namespace TransitionCell

abbrev QInterval := ScalarSuffixCertificate.QInterval

private def lambdaInterval : QInterval :=
  LeanSuffixReflective.QInterval.point (5 / 4)

/-- The exact dyadic type-(iv) transition slab. -/
def h4TransitionInterval : QInterval :=
  ⟨34912 / 65536, 34913 / 65536, by norm_num⟩

private def uLower : QInterval := ⟨846294/1000000, 846295/1000000, by norm_num⟩
private def dLower : QInterval := ⟨1130802/1000000, 1130803/1000000, by norm_num⟩
private def asinHLower : QInterval := ⟨561805/1000000, 561806/1000000, by norm_num⟩
private def asinRLower : QInterval := ⟨440256/1000000, 440257/1000000, by norm_num⟩

private def uUpper : QInterval := ⟨846285/1000000, 846286/1000000, by norm_num⟩
private def dUpper : QInterval := ⟨1130795/1000000, 1130796/1000000, by norm_num⟩
private def asinHUpper : QInterval := ⟨561823/1000000, 561824/1000000, by norm_num⟩
private def asinRUpper : QInterval := ⟨440270/1000000, 440271/1000000, by norm_num⟩

private def uCell : QInterval := ⟨846285/1000000, 846295/1000000, by norm_num⟩
private def dCell : QInterval := ⟨1130795/1000000, 1130803/1000000, by norm_num⟩
private def asinHCell : QInterval := ⟨561805/1000000, 561824/1000000, by norm_num⟩
private def asinRCell : QInterval := ⟨440256/1000000, 440271/1000000, by norm_num⟩

private def areaLowerBox : QInterval :=
  ⟨14137886/1000000, 14137914/1000000, by norm_num⟩
private def areaUpperBox : QInterval :=
  ⟨14137099/1000000, 14137127/1000000, by norm_num⟩

/-- At the semicircular type-(iii) height, the weighted area is exactly
`9*pi/2`. -/
theorem typeThreeArea_semicircular :
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (1 / 2) = 9 * π / 2 := by
  let a : _root_.TypeThreeAssembly (5 / 4 : ℝ) :=
    { h := 1 / 2
      density_jump := by norm_num
      h_pos := by norm_num
      h_lt_one := by norm_num }
  calc
    LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (1 / 2) =
        a.scalarWeightedArea := by
          symm
          exact CMVSuffixModel.TypeThreeAssembly.scalarWeightedArea_eq_typeThreeArea a
    _ = 2 * π * ((5 / 4 : ℝ) + 1) := a.scalarWeightedArea_semicircular rfl
    _ = 9 * π / 2 := by ring

/-- At the semicircular type-(iii) height, the weighted perimeter is exactly
`9*pi/2`. -/
theorem typeThreePerimeter_semicircular :
    LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) (1 / 2) = 9 * π / 2 := by
  let a : _root_.TypeThreeAssembly (5 / 4 : ℝ) :=
    { h := 1 / 2
      density_jump := by norm_num
      h_pos := by norm_num
      h_lt_one := by norm_num }
  calc
    LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) (1 / 2) =
        a.scalarWeightedPerimeter := by
          symm
          exact CMVSuffixModel.TypeThreeAssembly.scalarWeightedPerimeter_eq_typeThreePerimeter a
    _ = 2 * π * ((5 / 4 : ℝ) + 1) := a.scalarWeightedPerimeter_semicircular rfl
    _ = 9 * π / 2 := by ring

private theorem lambda_mem : lambdaInterval.RealContains (5 / 4 : ℝ) := by
  norm_num [lambdaInterval, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.point]

private theorem exact_atoms
    (hI uI dI asinHI asinRI : QInterval) {h : ℝ}
    (hh : hI.RealContains h)
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
    uI.RealContains (sqrt (1 - h^2)) ∧
      dI.RealContains (sqrt ((5 / 4 : ℝ)^2 - h^2)) ∧
      asinHI.RealContains (arcsin h) ∧
      asinRI.RealContains (arcsin (h / (5 / 4 : ℝ))) := by
  exact CompactCellCertificate.typeFour_atoms_of_exact_bounds
    lambdaInterval hI uI dI asinHI asinRI lambda_mem hh
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num) hexact

private theorem lower_atoms :
    uLower.RealContains (sqrt (1 - (h4TransitionInterval.lo : ℝ)^2)) ∧
      dLower.RealContains (sqrt ((5 / 4 : ℝ)^2 - (h4TransitionInterval.lo : ℝ)^2)) ∧
      asinHLower.RealContains (arcsin (h4TransitionInterval.lo : ℝ)) ∧
      asinRLower.RealContains
        (arcsin ((h4TransitionInterval.lo : ℝ) / (5 / 4 : ℝ))) := by
  apply exact_atoms (LeanSuffixReflective.QInterval.point h4TransitionInterval.lo)
    uLower dLower asinHLower asinRLower
    (LeanSuffixReflective.QInterval.realContains_point h4TransitionInterval.lo
      (h4TransitionInterval.lo : ℝ) |>.2 rfl)
  norm_num [CompactCellCertificate.typeFourShiftedInterval, lambdaInterval,
    h4TransitionInterval, uLower, dLower, asinHLower, asinRLower,
    ScalarSuffixCertificate.sinTaylor27Interval, ScalarSuffixCertificate.sinTaylor27,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point, Nat.factorial]

private theorem upper_atoms :
    uUpper.RealContains (sqrt (1 - (h4TransitionInterval.hi : ℝ)^2)) ∧
      dUpper.RealContains (sqrt ((5 / 4 : ℝ)^2 - (h4TransitionInterval.hi : ℝ)^2)) ∧
      asinHUpper.RealContains (arcsin (h4TransitionInterval.hi : ℝ)) ∧
      asinRUpper.RealContains
        (arcsin ((h4TransitionInterval.hi : ℝ) / (5 / 4 : ℝ))) := by
  apply exact_atoms (LeanSuffixReflective.QInterval.point h4TransitionInterval.hi)
    uUpper dUpper asinHUpper asinRUpper
    (LeanSuffixReflective.QInterval.realContains_point h4TransitionInterval.hi
      (h4TransitionInterval.hi : ℝ) |>.2 rfl)
  norm_num [CompactCellCertificate.typeFourShiftedInterval, lambdaInterval,
    h4TransitionInterval, uUpper, dUpper, asinHUpper, asinRUpper,
    ScalarSuffixCertificate.sinTaylor27Interval, ScalarSuffixCertificate.sinTaylor27,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point, Nat.factorial]

private theorem cell_atoms {h : ℝ} (hh : h4TransitionInterval.RealContains h) :
    uCell.RealContains (sqrt (1 - h^2)) ∧
      dCell.RealContains (sqrt ((5 / 4 : ℝ)^2 - h^2)) ∧
      asinHCell.RealContains (arcsin h) ∧
      asinRCell.RealContains (arcsin (h / (5 / 4 : ℝ))) := by
  apply exact_atoms h4TransitionInterval uCell dCell asinHCell asinRCell hh
  norm_num [CompactCellCertificate.typeFourShiftedInterval, lambdaInterval,
    h4TransitionInterval, uCell, dCell, asinHCell, asinRCell,
    ScalarSuffixCertificate.sinTaylor27Interval, ScalarSuffixCertificate.sinTaylor27,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    ScalarSuffixCertificate.QInterval.mul, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.point, Nat.factorial]

private theorem area_lower_enclosure :
    areaLowerBox.RealContains
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)
        (h4TransitionInterval.lo : ℝ)) := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval
    (LeanSuffixReflective.QInterval.point h4TransitionInterval.lo)
    uLower dLower asinHLower asinRLower lambda_mem
    (LeanSuffixReflective.QInterval.realContains_point h4TransitionInterval.lo
      (h4TransitionInterval.lo : ℝ) |>.2 rfl) lower_atoms
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4TransitionInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4TransitionInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [uLower]) (by norm_num [dLower])
  have harea := henc.1
  norm_num [areaLowerBox, CompactCellCertificate.typeFourAreaBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, lambdaInterval, h4TransitionInterval,
    uLower, dLower, asinHLower, asinRLower, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at harea ⊢
  exact ⟨by linarith [harea.1], by linarith [harea.2]⟩

private theorem area_upper_enclosure :
    areaUpperBox.RealContains
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)
        (h4TransitionInterval.hi : ℝ)) := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval
    (LeanSuffixReflective.QInterval.point h4TransitionInterval.hi)
    uUpper dUpper asinHUpper asinRUpper lambda_mem
    (LeanSuffixReflective.QInterval.realContains_point h4TransitionInterval.hi
      (h4TransitionInterval.hi : ℝ) |>.2 rfl) upper_atoms
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4TransitionInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4TransitionInterval, ScalarSuffixCertificate.QInterval.mul,
      LeanSuffixReflective.QInterval.point]) (by norm_num [uUpper]) (by norm_num [dUpper])
  have harea := henc.1
  norm_num [areaUpperBox, CompactCellCertificate.typeFourAreaBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.typeFourDeltaBox,
    CompactCellCertificate.halfPiBox, lambdaInterval, h4TransitionInterval,
    uUpper, dUpper, asinHUpper, asinRUpper, ScalarSuffixCertificate.piInterval,
    ScalarSuffixCertificate.QInterval.mul, ScalarSuffixCertificate.QInterval.divPos,
    ScalarSuffixCertificate.QInterval.recipPos, LeanSuffixReflective.QInterval.RealContains,
    LeanSuffixReflective.QInterval.add, LeanSuffixReflective.QInterval.neg,
    LeanSuffixReflective.QInterval.sub, LeanSuffixReflective.QInterval.nsmul,
    LeanSuffixReflective.QInterval.point] at harea ⊢
  exact ⟨by linarith [harea.1], by linarith [harea.2]⟩

/-- At the lower dyadic face, type-(iv) area is strictly above the transition
area. -/
theorem typeFourArea_lower_gt_target :
    9 * π / 2 < LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)
      (h4TransitionInterval.lo : ℝ) := by
  have harea := area_lower_enclosure
  have hpi := ScalarSuffixCertificate.piInterval_sound
  norm_num [areaLowerBox, ScalarSuffixCertificate.piInterval,
    LeanSuffixReflective.QInterval.RealContains] at harea hpi ⊢
  linarith [harea.1, hpi.2]

/-- At the upper dyadic face, type-(iv) area is strictly below the transition
area. -/
theorem typeFourArea_upper_lt_target :
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)
      (h4TransitionInterval.hi : ℝ) < 9 * π / 2 := by
  have harea := area_upper_enclosure
  have hpi := ScalarSuffixCertificate.piInterval_sound
  norm_num [areaUpperBox, ScalarSuffixCertificate.piInterval,
    LeanSuffixReflective.QInterval.RealContains] at harea hpi ⊢
  linarith [harea.2, hpi.1]

/-- Uniformly over the dyadic transition slab, type-(iv) perimeter is strictly
larger than `9*pi/2`. -/
theorem target_lt_typeFourPerimeter {h : ℝ}
    (hh : h4TransitionInterval.RealContains h) :
    9 * π / 2 < LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h := by
  have henc := CompactCellCertificate.typeFour_atom_enclosures lambdaInterval
    h4TransitionInterval uCell dCell asinHCell asinRCell lambda_mem hh (cell_atoms hh)
    (by norm_num [lambdaInterval, LeanSuffixReflective.QInterval.point])
    (by norm_num [h4TransitionInterval])
    (by norm_num [h4TransitionInterval, ScalarSuffixCertificate.QInterval.mul])
    (by norm_num [uCell]) (by norm_num [dCell])
  have hp := henc.2.1
  have hpi := ScalarSuffixCertificate.piInterval_sound
  norm_num [CompactCellCertificate.typeFourPerimeterBox,
    CompactCellCertificate.typeFourAngleBox, CompactCellCertificate.halfPiBox,
    lambdaInterval, h4TransitionInterval, asinHCell, asinRCell,
    ScalarSuffixCertificate.piInterval, ScalarSuffixCertificate.QInterval.mul,
    ScalarSuffixCertificate.QInterval.divPos, ScalarSuffixCertificate.QInterval.recipPos,
    LeanSuffixReflective.QInterval.RealContains, LeanSuffixReflective.QInterval.add,
    LeanSuffixReflective.QInterval.neg, LeanSuffixReflective.QInterval.sub,
    LeanSuffixReflective.QInterval.nsmul, LeanSuffixReflective.QInterval.point] at hp hpi ⊢
  linarith [hp.1, hpi.2]

/-- A type-(iv) height of exactly the semicircular type-(iii) area exists in
the certified dyadic slab. -/
theorem exists_transition_h4 :
    ∃ h : ℝ, h4TransitionInterval.RealContains h ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h = 9 * π / 2 := by
  let f : ℝ → ℝ := fun h => 9 * π / 2 -
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h
  have hcontinuous : ContinuousOn f
      (Icc (h4TransitionInterval.lo : ℝ) (h4TransitionInterval.hi : ℝ)) := by
    intro h hh
    have hr : 0 < h ∧ h < 1 := by
      norm_num [h4TransitionInterval] at hh ⊢
      exact ⟨lt_of_lt_of_le (by norm_num) hh.1,
        lt_of_le_of_lt hh.2 (by norm_num)⟩
    exact
      (continuousAt_const.sub
        (LeanSuffixAnalytic.hasDerivAt_typeFourArea
          (by norm_num) hr.1 hr.2).continuousAt).continuousWithinAt
  rcases ScalarSuffixCertificate.oppositeFace_zero
      (show (h4TransitionInterval.lo : ℝ) ≤ h4TransitionInterval.hi by
        norm_num [h4TransitionInterval]) hcontinuous
      (le_of_lt (sub_neg.mpr typeFourArea_lower_gt_target))
      (le_of_lt (sub_pos.mpr typeFourArea_upper_lt_target)) with ⟨h, hh, hz⟩
  refine ⟨h, ?_, ?_⟩
  · simpa [LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh
  · dsimp [f] at hz
    linarith

/-- The regular type-(iv) endpoint lies strictly below the semicircular
transition area. -/
theorem typeFourArea_endpoint_lt_target :
    LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) 1 < 9 * π / 2 := by
  unfold LeanSuffixAnalytic.typeFourArea LeanSuffixAnalytic.typeFourAngle
    LeanSuffixAnalytic.typeFourDelta
  norm_num [Real.arcsin_one, Real.arccos_eq_pi_div_two_sub_arcsin]
  have hasin : 0 ≤ arcsin (4 / 5 : ℝ) := Real.arcsin_nonneg.mpr (by norm_num)
  nlinarith [Real.pi_gt_three]

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

/-- Every regular transition-area root has a later point where the type-(iv)
fold is negative. -/
private theorem exists_typeFourFold_neg_after {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1)
    (harea : LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) q = 9 * π / 2) :
    ∃ y ∈ Ioo q 1,
      LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) y < 0 := by
  have hcont : ContinuousOn
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)) (Icc q 1) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hq.1.trans_le hx.1)
    unfold LeanSuffixAnalytic.typeFourArea LeanSuffixAnalytic.typeFourAngle
      LeanSuffixAnalytic.typeFourDelta
    fun_prop (disch := simp_all)
  have hdiff : DifferentiableOn ℝ
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)) (Ioo q 1) := by
    intro x hx
    exact (LeanSuffixAnalytic.hasDerivAt_typeFourArea (by norm_num)
      (hq.1.trans hx.1) hx.2).differentiableAt.differentiableWithinAt
  rcases exists_deriv_eq_slope
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ)) hq.2 hcont hdiff with
    ⟨y, hy, hslope⟩
  have hyreg : y ∈ Ioo (0 : ℝ) 1 := ⟨hq.1.trans hy.1, hy.2⟩
  rw [(LeanSuffixAnalytic.hasDerivAt_typeFourArea
    (by norm_num) hyreg.1 hyreg.2).deriv] at hslope
  have hslopeNeg :
      (LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) 1 -
        LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) q) / (1 - q) < 0 :=
    div_neg_of_neg_of_pos
      (by rw [harea]; exact sub_neg.mpr typeFourArea_endpoint_lt_target)
      (sub_pos.mpr hq.2)
  have hfold : LeanSuffixAnalytic.typeFourFold (5 / 4 : ℝ) y < 0 := by
    rw [← hslope] at hslopeNeg
    by_contra hnot
    exact (not_lt_of_ge
      (div_nonneg (le_of_not_gt hnot) (pow_nonneg hyreg.1.le 3))) hslopeNeg
  exact ⟨y, hy, hfold⟩

/-- The semicircular transition-area equation has exactly one regular
type-(iv) root. -/
theorem typeFour_transition_area_roots_existsUnique :
    ∃! h : ℝ, h ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h = 9 * π / 2 := by
  rcases exists_transition_h4 with ⟨root, hroot, hareaRoot⟩
  have hrootReg : root ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num [h4TransitionInterval]) hroot.1,
      lt_of_le_of_lt hroot.2 (by norm_num [h4TransitionInterval])⟩
  refine ⟨root, ⟨hrootReg, hareaRoot⟩, ?_⟩
  intro h hharea
  rcases hharea with ⟨hh, harea⟩
  rcases lt_trichotomy h root with hlt | heq | hgt
  · rcases typeFourFold_zero_between_of_area_eq hh hrootReg hlt
      (harea.trans hareaRoot.symm) with ⟨x, hx, hfoldX⟩
    rcases exists_typeFourFold_neg_after hrootReg hareaRoot with ⟨y, hy, hfoldY⟩
    have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hh.1.trans hx.1, hx.2.trans hrootReg.2⟩
    have hyreg : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨hrootReg.1.trans hy.1, hy.2⟩
    have hmono := LeanSuffixAnalytic.typeFourFold_strictMonoOn
      (lam := (5 / 4 : ℝ)) (by norm_num) hxreg hyreg (hx.2.trans hy.1)
    rw [hfoldX] at hmono
    linarith
  · exact heq
  · rcases typeFourFold_zero_between_of_area_eq hrootReg hh hgt
      (hareaRoot.trans harea.symm) with ⟨x, hx, hfoldX⟩
    rcases exists_typeFourFold_neg_after hh harea with ⟨y, hy, hfoldY⟩
    have hxreg : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hrootReg.1.trans hx.1, hx.2.trans hh.2⟩
    have hyreg : y ∈ Ioo (0 : ℝ) 1 :=
      ⟨hh.1.trans hy.1, hy.2⟩
    have hmono := LeanSuffixAnalytic.typeFourFold_strictMonoOn
      (lam := (5 / 4 : ℝ)) (by norm_num) hxreg hyreg (hx.2.trans hy.1)
    rw [hfoldX] at hmono
    linarith

/-- The certified transition slab exhausts the regular type-(iv) heights with
the semicircular transition area. -/
theorem typeFour_transition_area_root_classification {h : ℝ}
    (hh : h ∈ Ioo (0 : ℝ) 1)
    (harea : LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h = 9 * π / 2) :
    h4TransitionInterval.RealContains h := by
  rcases typeFour_transition_area_roots_existsUnique with
    ⟨root, _, hunique⟩
  rcases exists_transition_h4 with ⟨slabRoot, hslab, hareaSlab⟩
  have hslabReg : slabRoot ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num [h4TransitionInterval]) hslab.1,
      lt_of_le_of_lt hslab.2 (by norm_num [h4TransitionInterval])⟩
  have hhEq : h = root := hunique h ⟨hh, harea⟩
  have hslabEq : slabRoot = root :=
    hunique slabRoot ⟨hslabReg, hareaSlab⟩
  simpa [hhEq.trans hslabEq.symm] using hslab

/-- Scalar transition witness: equal area and strict type-(iii) perimeter
improvement are certified together. -/
theorem semicircular_transition_exists :
    ∃ h : ℝ, h4TransitionInterval.RealContains h ∧
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (1 / 2) =
        LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) h ∧
      LeanSuffixAnalytic.typeThreePerimeter (5 / 4 : ℝ) (1 / 2) <
        LeanSuffixAnalytic.typeFourPerimeter (5 / 4 : ℝ) h := by
  rcases exists_transition_h4 with ⟨h, hh, harea⟩
  refine ⟨h, hh, ?_, ?_⟩
  · rw [typeThreeArea_semicircular, harea]
  · rw [typeThreePerimeter_semicircular]
    exact target_lt_typeFourPerimeter hh

/-- Every genuine type-(iv) candidate with the semicircular weighted area is
defeated by the canonical type-(iii) semicircular competitor.  The complete
regular root classification derives slab membership, while the endpoint area
inequality excludes `candidate.h = 1`.  No stationarity assumption is used. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    (candidate : _root_.FourArcCandidate (5 / 4 : ℝ))
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (harea : candidate.WeightedArea = 9 * π / 2) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  have hscalar :
      LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) candidate.h = 9 * π / 2 :=
    (CMVSuffixModel.FourArcCandidate.weightedArea_eq_typeFourArea
      candidate hcandidate).symm.trans harea
  have hregular : candidate.h < 1 := by
    apply lt_of_le_of_ne candidate.h_le_one
    intro heq
    rw [heq] at hscalar
    exact typeFourArea_endpoint_lt_target.ne hscalar
  have hh := typeFour_transition_area_root_classification
    ⟨candidate.h_pos, hregular⟩ hscalar
  apply CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree
    candidate hcandidate (h₃ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  · calc
      LeanSuffixAnalytic.typeThreeArea (5 / 4 : ℝ) (1 / 2) = 9 * π / 2 :=
        typeThreeArea_semicircular
      _ = candidate.WeightedArea := harea.symm
      _ = LeanSuffixAnalytic.typeFourArea (5 / 4 : ℝ) candidate.h :=
        CMVSuffixModel.FourArcCandidate.weightedArea_eq_typeFourArea
          candidate hcandidate
  · rw [typeThreePerimeter_semicircular]
    exact target_lt_typeFourPerimeter hh

end TransitionCell
