/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import ScalarSuffixCertificate
import SameCurvatureArea

/-!
# Generic compact-cell assembly

This module separates the analytic root/IVT argument shared by compact cells
from their exact-rational interval calculations.  A `Conditions` value records
only the real consequences that a proof-producing cell checker must establish.
-/

open Real Set
noncomputable section

namespace CompactCellAssembly

abbrev QInterval := ScalarSuffixCertificate.QInterval

/-- Sound real consequences required from one compact-cell interval
certificate.  Numerical cell modules prove these fields from exact rational
interval arithmetic; the shared assembly below contains no numerical oracle. -/
structure Conditions (lambdaInterval h3Interval h4Interval : QInterval) : Prop where
  lambda_one_lt : ∀ {lam : ℝ},
    lambdaInterval.RealContains lam → 1 < lam
  h3_slab_regular : ∀ {h : ℝ},
    h3Interval.RealContains h → h ∈ Ioo (0 : ℝ) 1
  h3_slab_above_half : ∀ {h : ℝ},
    h3Interval.RealContains h → 1 / 2 < h
  h4_slab_regular : ∀ {h : ℝ},
    h4Interval.RealContains h → h ∈ Ioo (0 : ℝ) 1
  typeFourFold_lowerFace_neg : ∀ {lam : ℝ},
    lambdaInterval.RealContains lam →
      LeanSuffixAnalytic.typeFourFold lam (h4Interval.lo : ℝ) < 0
  typeFourFold_upperFace_pos : ∀ {lam : ℝ},
    lambdaInterval.RealContains lam →
      0 < LeanSuffixAnalytic.typeFourFold lam (h4Interval.hi : ℝ)
  typeThreeFold_neg_on_slab : ∀ {lam h : ℝ},
    lambdaInterval.RealContains lam → h3Interval.RealContains h →
      LeanSuffixAnalytic.typeThreeFold lam h < 0
  typeThreeArea_lowerFace_gap_pos : ∀ {lam h₄ : ℝ},
    lambdaInterval.RealContains lam → h4Interval.RealContains h₄ →
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 →
      0 < LeanSuffixAnalytic.typeThreeArea lam (h3Interval.lo : ℝ) -
        LeanSuffixAnalytic.typeFourArea lam h₄
  typeThreeArea_upperFace_gap_neg : ∀ {lam h₄ : ℝ},
    lambdaInterval.RealContains lam → h4Interval.RealContains h₄ →
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 →
      LeanSuffixAnalytic.typeThreeArea lam (h3Interval.hi : ℝ) -
        LeanSuffixAnalytic.typeFourArea lam h₄ < 0
  typeThreePerimeter_gap_neg : ∀ {lam h₃ h₄ : ℝ},
    lambdaInterval.RealContains lam → h3Interval.RealContains h₃ →
      h4Interval.RealContains h₄ →
      LeanSuffixAnalytic.typeThreePerimeter lam h₃ -
        LeanSuffixAnalytic.typeFourPerimeter lam h₄ < 0

namespace Conditions

variable {lambdaInterval h3Interval h4Interval : QInterval}

private theorem lower_mem (i : QInterval) :
    i.RealContains (i.lo : ℝ) := by
  constructor
  · exact le_rfl
  · exact_mod_cast i.ordered

private theorem upper_mem (i : QInterval) :
    i.RealContains (i.hi : ℝ) := by
  constructor
  · exact_mod_cast i.ordered
  · exact le_rfl

/-- The type-(iv) slab contains exactly one stationary root. -/
theorem typeFourFold_existsUnique_in_slab
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam : ℝ} (hlam : lambdaInterval.RealContains lam) :
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
    have hhReg := conditions.h4_slab_regular hhSlab
    exact (LeanSuffixAnalytic.hasDerivAt_typeFourFold
      (conditions.lambda_one_lt hlam) hhReg.1 hhReg.2).continuousAt.continuousWithinAt
  rcases ScalarSuffixCertificate.oppositeFace_zero hab hcont
      (conditions.typeFourFold_lowerFace_neg hlam).le
      (conditions.typeFourFold_upperFace_pos hlam).le with ⟨h₄, hh₄, hzero⟩
  have hhSlab : h4Interval.RealContains h₄ := by
    simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc] using hh₄
  refine ⟨h₄, ⟨hhSlab, hzero⟩, ?_⟩
  intro y hy
  exact LeanSuffixAnalytic.typeFourFold_zero_unique
    (conditions.lambda_one_lt hlam)
    (conditions.h4_slab_regular hy.1)
    (conditions.h4_slab_regular hhSlab) hy.2 hzero

/-- A stationary type-(iv) root in the cell has exactly one equal-area
height on the descending type-(iii) slab. -/
theorem typeThreeEqualArea_existsUnique_in_slab
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h4Interval.RealContains h₄)
    (hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0) :
    ∃! h₃ : ℝ, h3Interval.RealContains h₃ ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ := by
  let a : ℝ := h3Interval.lo
  let b : ℝ := h3Interval.hi
  let f : ℝ → ℝ := fun y =>
    LeanSuffixAnalytic.typeFourArea lam h₄ -
      LeanSuffixAnalytic.typeThreeArea lam y
  have hab : a ≤ b := by
    simpa [a, b] using (show (h3Interval.lo : ℝ) ≤ h3Interval.hi by
      exact_mod_cast h3Interval.ordered)
  have hcont : ContinuousOn f (Icc a b) := by
    intro y hy
    have hySlab : h3Interval.RealContains y := by
      simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc]
        using hy
    have hyReg := conditions.h3_slab_regular hySlab
    exact (continuousAt_const.sub
      (LeanSuffixAnalytic.hasDerivAt_typeThreeArea
        (conditions.lambda_one_lt hlam) hyReg.1 hyReg.2).continuousAt).continuousWithinAt
  have hfa : f a ≤ 0 := by
    dsimp [f, a]
    linarith [conditions.typeThreeArea_lowerFace_gap_pos
      hlam hh₄ hstationary]
  have hfb : 0 ≤ f b := by
    dsimp [f, b]
    linarith [conditions.typeThreeArea_upperFace_gap_neg
      hlam hh₄ hstationary]
  rcases ScalarSuffixCertificate.oppositeFace_zero hab hcont hfa hfb with
    ⟨h₃, hh₃, hzero⟩
  have hhSlab : h3Interval.RealContains h₃ := by
    simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc]
      using hh₃
  have hequal :
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ := by
    dsimp [f] at hzero
    linarith
  have hderiv : ∀ y ∈ Ioo a b,
      deriv (LeanSuffixAnalytic.typeThreeArea lam) y < 0 := by
    intro y hy
    have hySlab : h3Interval.RealContains y := by
      simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Ioo]
        using ⟨hy.1.le, hy.2.le⟩
    have hyReg := conditions.h3_slab_regular hySlab
    rw [(LeanSuffixAnalytic.hasDerivAt_typeThreeArea
      (conditions.lambda_one_lt hlam) hyReg.1 hyReg.2).deriv]
    exact div_neg_of_neg_of_pos
      (conditions.typeThreeFold_neg_on_slab hlam hySlab)
      (pow_pos hyReg.1 3)
  have hanti := LeanSuffixAnalytic.typeThreeArea_strictAntiOn_Icc
    (conditions.lambda_one_lt hlam)
    (conditions.h3_slab_regular (lower_mem h3Interval)).1
    (conditions.h3_slab_regular (upper_mem h3Interval)).2 hderiv
  refine ⟨h₃, ⟨hhSlab, hequal⟩, ?_⟩
  intro y hy
  apply hanti.injOn
  · simpa [a, b, LeanSuffixReflective.QInterval.RealContains, Set.mem_Icc]
      using hy.1
  · exact hh₃
  · exact hy.2.trans hequal.symm

/-- The slab-isolated negative-fold root is the global descending root of its
equal-area level.  Every root in `0 < h ≤ 1` lies at or above it, and there is
at most one distinct upper root. -/
theorem typeThreeEqualArea_root_classification
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
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
          LeanSuffixAnalytic.typeFourArea lam h₄ → y = z) := by
  rcases conditions.typeThreeEqualArea_existsUnique_in_slab
      hlam hh₄ hstationary with ⟨h₃, ⟨hh₃, harea⟩, _⟩
  have hh₃Reg := conditions.h3_slab_regular hh₃
  refine ⟨h₃, hh₃, harea, ?_, ?_⟩
  · intro y hy hareaY
    exact LeanSuffixAnalytic.typeThreeArea_root_le_of_fold_neg
      (conditions.lambda_one_lt hlam) hh₃Reg hy
      (conditions.typeThreeFold_neg_on_slab hlam hh₃)
      (harea.trans hareaY.symm)
  · intro y hy z hz hh₃Y hh₃Z hareaY hareaZ
    exact LeanSuffixAnalytic.typeThreeArea_upper_root_unique
      (conditions.lambda_one_lt hlam)
      ⟨hh₃Reg.1, hh₃Reg.2.le⟩ hy hz hh₃Y hh₃Z
      (harea.trans hareaY.symm) (harea.trans hareaZ.symm)

/-- One stationary compact-cell certificate constructs the unique descending
type-(iii) equal-area root below every `0 < h₄ ≤ 1`, not only below the
stationary type-(iv) curvature inside the cell. -/
theorem descendingTypeThreeEqualArea_existsUnique
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h₄ ∈ Ioc (0 : ℝ) 1) :
    ∃! h₃ : ℝ, h₃ ∈ Ioo (0 : ℝ) 1 ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ ∧
      LeanSuffixAnalytic.typeThreeFold lam h₃ < 0 ∧ h₃ < h₄ := by
  rcases conditions.typeFourFold_existsUnique_in_slab hlam with
    ⟨h₄fold, ⟨hh₄fold, hfoldFour⟩, _⟩
  rcases conditions.typeThreeEqualArea_existsUnique_in_slab
      hlam hh₄fold hfoldFour with
    ⟨h₃fold, ⟨hh₃fold, hequalFold⟩, _⟩
  rcases
      LeanSuffixAnalytic.typeThreeArea_descending_root_existsUnique_of_stationary_pair
        (conditions.lambda_one_lt hlam)
        (conditions.h3_slab_regular hh₃fold)
        (conditions.h4_slab_regular hh₄fold) hh₄
        (conditions.typeThreeFold_neg_on_slab hlam hh₃fold)
        hfoldFour hequalFold with
    ⟨h₃, ⟨hh₃, harea, hfold⟩, hunique⟩
  refine ⟨h₃, ⟨hh₃, harea, hfold, ?_⟩, ?_⟩
  · exact LeanSuffixAnalytic.typeThreeArea_descending_root_lt
      (conditions.lambda_one_lt hlam) hh₃ hh₄.1 hh₄.2 hfold harea
  · intro y hy
    exact hunique y ⟨hy.1, hy.2.1, hy.2.2.1⟩

/-- Every lambda in a checked compact cell has isolated stationary and
matching equal-area roots with a strict type-(iii) perimeter improvement. -/
theorem stationaryEqualArea_improvement_exists
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam : ℝ} (hlam : lambdaInterval.RealContains lam) :
    ∃ h₄ h₃ : ℝ,
      h4Interval.RealContains h₄ ∧
      LeanSuffixAnalytic.typeFourFold lam h₄ = 0 ∧
      h3Interval.RealContains h₃ ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter lam h₃ <
        LeanSuffixAnalytic.typeFourPerimeter lam h₄ := by
  rcases conditions.typeFourFold_existsUnique_in_slab hlam with
    ⟨h₄, ⟨hh₄, hfold⟩, _⟩
  rcases conditions.typeThreeEqualArea_existsUnique_in_slab
      hlam hh₄ hfold with ⟨h₃, ⟨hh₃, hequal⟩, _⟩
  refine ⟨h₄, h₃, hh₄, hfold, hh₃, hequal, ?_⟩
  linarith [conditions.typeThreePerimeter_gap_neg hlam hh₃ hh₄]

/-- Global type-(iv) fold uniqueness identifies any regular stationary root
with the root isolated by this cell; slab membership need not be assumed for
the arbitrary root. -/
theorem regularStationary_improvement
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam h₄ : ℝ}
    (hlam : lambdaInterval.RealContains lam)
    (hh₄ : h₄ ∈ Ioo (0 : ℝ) 1)
    (hstationary : LeanSuffixAnalytic.typeFourFold lam h₄ = 0) :
    ∃ h₃ : ℝ,
      h3Interval.RealContains h₃ ∧
      LeanSuffixAnalytic.typeThreeArea lam h₃ =
        LeanSuffixAnalytic.typeFourArea lam h₄ ∧
      LeanSuffixAnalytic.typeThreePerimeter lam h₃ <
        LeanSuffixAnalytic.typeFourPerimeter lam h₄ := by
  rcases conditions.typeFourFold_existsUnique_in_slab hlam with
    ⟨root, ⟨hrootSlab, hrootFold⟩, _⟩
  have hrootEq : root = h₄ :=
    LeanSuffixAnalytic.typeFourFold_zero_unique
      (conditions.lambda_one_lt hlam)
      (conditions.h4_slab_regular hrootSlab) hh₄ hrootFold hstationary
  rcases conditions.typeThreeEqualArea_existsUnique_in_slab
      hlam hrootSlab hrootFold with ⟨h₃, ⟨hh₃, hequal⟩, _⟩
  refine ⟨h₃, hh₃, ?_, ?_⟩
  · simpa [hrootEq] using hequal
  · have hgap := conditions.typeThreePerimeter_gap_neg hlam hh₃ hrootSlab
    rw [hrootEq] at hgap
    linarith

/-- Candidate-facing consequence for every regular stationary modeled
four-arc candidate.  Global fold uniqueness supplies its cell membership. -/
theorem regularStationaryCandidate_not_isWeightedPerimeterMinimizer
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam : ℝ} (hlam : lambdaInterval.RealContains lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses)
    (hregular : candidate.h < 1)
    (hstationary :
      LeanSuffixAnalytic.typeFourFold lam candidate.h = 0) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases conditions.regularStationary_improvement hlam
      ⟨candidate.h_pos, hregular⟩ hstationary with
    ⟨h₃, hh₃, hequal, hperimeter⟩
  have hreg := conditions.h3_slab_regular hh₃
  exact CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_analytic_typeThree
    candidate hcandidate hreg.1 hreg.2 hequal hperimeter

/-- Candidate-facing consequence for every modeled four-arc candidate, including
the endpoint `h = 1`.  A stationary pair certified inside the cell drives the
all-curvature comparison. -/
theorem candidate_not_isWeightedPerimeterMinimizer
    (conditions : Conditions lambdaInterval h3Interval h4Interval)
    {lam : ℝ} (hlam : lambdaInterval.RealContains lam)
    (candidate : _root_.FourArcCandidate lam)
    (hcandidate : candidate.SatisfiesCMVTypeIVHypotheses) :
    ¬ candidate.IsWeightedPerimeterMinimizer := by
  rcases conditions.stationaryEqualArea_improvement_exists hlam with
    ⟨h₄, h₃, hh₄, hstationary, hh₃, hequal, hperimeter⟩
  have hh₃reg := conditions.h3_slab_regular hh₃
  have hh₄reg := conditions.h4_slab_regular hh₄
  let pair : LeanSuffixAnalytic.StationaryEqualAreaPair lam :=
    { h₃ := h₃
      h₄ := h₄
      h₃_gt_half := conditions.h3_slab_above_half hh₃
      h₃_lt_one := hh₃reg.2
      h₄_pos := hh₄reg.1
      h₄_lt_one := hh₄reg.2
      equalArea := hequal
      stationary := hstationary }
  apply
    CMVSuffixModel.FourArcCandidate.not_isWeightedPerimeterMinimizer_of_stationaryEqualAreaPair
      candidate hcandidate pair
  · exact conditions.typeThreeFold_neg_on_slab hlam hh₃
  · exact hperimeter

end Conditions
end CompactCellAssembly
