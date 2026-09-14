import CMVFiniteBandEqualityRigidity

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation.FiniteBandRearrangement.TwoBandWidthJump

/-- Two one-component bands with constant fibers `[0,2]` and `[0,4]`.
Their one-sided width functions are continuous, but the width jumps at the
internal cut. -/
def region : Region where
  bandCount := 2
  bandCount_pos := by norm_num
  cuts := fun i => i.val
  cuts_strict := by
    intro i j hij
    change (i.val : ℝ) < j.val
    exact_mod_cast hij
  componentCount := fun _ => 1
  componentCount_pos := by intro i; norm_num
  left := fun _ _ _ => 0
  right := fun i _ _ => 2 * (i.val + 1)
  left_continuous := by intro i j; fun_prop
  right_continuous := by intro i j; fun_prop
  left_contDiffOn := by intro i j; fun_prop
  right_contDiffOn := by intro i j; fun_prop
  left_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  right_speed_integrable := by
    intro i j
    simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, Real.sqrt_one]
    exact integrableOn_const measure_Ioo_lt_top.ne
  width_nonneg := by intro i j y hy; positivity
  width_pos := by intro i j y hy; positivity
  components_ordered := by intro i j k hjk y hy; omega
  components_strict := by intro i j k hjk y hy; omega

@[simp] theorem componentCount (i : Fin region.bandCount) :
    region.componentCount i = 1 := rfl

def lowerBand : Fin region.bandCount := ⟨0, by simp [region]⟩

def upperBand : Fin region.bandCount := ⟨1, by simp [region]⟩

@[simp] theorem totalWidth_zero (y : ℝ) :
    region.totalWidth lowerBand y = 2 := by
  rw [Region.totalWidth_eq_single_of_componentCount_eq_one
    region lowerBand (componentCount lowerBand)]
  change 2 * ((lowerBand.val : ℝ) + 1) - 0 = 2
  norm_num [lowerBand]

@[simp] theorem totalWidth_one (y : ℝ) :
    region.totalWidth upperBand y = 4 := by
  rw [Region.totalWidth_eq_single_of_componentCount_eq_one
    region upperBand (componentCount upperBand)]
  change 2 * ((upperBand.val : ℝ) + 1) - 0 = 4
  norm_num [upperBand]

@[simp] theorem bandCenter_zero (y : ℝ) :
    region.bandCenter lowerBand y = 1 := by
  change (0 + 2 * ((lowerBand.val : ℝ) + 1)) / 2 = 1
  norm_num [lowerBand]

@[simp] theorem bandCenter_one (y : ℝ) :
    region.bandCenter upperBand y = 2 := by
  change (0 + 2 * ((upperBand.val : ℝ) + 1)) / 2 = 2
  norm_num [upperBand]

theorem oneSidedTotalWidths_continuous :
    Continuous (region.totalWidth lowerBand) ∧
      Continuous (region.totalWidth upperBand) :=
  ⟨region.continuous_totalWidth lowerBand,
    region.continuous_totalWidth upperBand⟩

def seam : Fin (region.bandCount - 1) := ⟨0, by simp [region]⟩

@[simp] theorem seamLowerBand : region.seamLowerBand seam = lowerBand :=
  Fin.ext rfl

@[simp] theorem seamUpperBand : region.seamUpperBand seam = upperBand :=
  Fin.ext rfl

@[simp] theorem seamHeight : region.seamHeight seam = 1 := by
  change ((region.seamUpperBand seam).val : ℝ) = 1
  norm_num [Region.seamUpperBand, seam, region]

@[simp] theorem lowerFiber (y : ℝ) :
    region.fiber lowerBand y = Icc (0 : ℝ) 2 := by
  rw [region.fiber_eq_Icc_bandCenter_totalWidth_of_componentCount_eq_one
    lowerBand (componentCount lowerBand) y]
  simp only [bandCenter_zero, totalWidth_zero]
  norm_num

@[simp] theorem upperFiber (y : ℝ) :
    region.fiber upperBand y = Icc (0 : ℝ) 4 := by
  rw [region.fiber_eq_Icc_bandCenter_totalWidth_of_componentCount_eq_one
    upperBand (componentCount upperBand) y]
  simp only [bandCenter_one, totalWidth_one]
  norm_num

theorem originalSeamVolume (i : Fin (region.bandCount - 1)) :
    volume
      (region.fiber (region.seamLowerBand i) (region.seamHeight i) ∆
        region.fiber (region.seamUpperBand i) (region.seamHeight i)) = 2 := by
  have hi : i = seam := by
    apply Fin.ext
    change i.val = 0
    have hiLt : i.val < 1 := by
      simpa [region] using i.isLt
    omega
  subst i
  rw [seamLowerBand, seamUpperBand, lowerFiber, upperFiber]
  have hsub : Icc (0 : ℝ) 2 ⊆ Icc (0 : ℝ) 4 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  rw [symmDiff_of_le hsub,
    measure_sdiff hsub measurableSet_Icc.nullMeasurableSet]
  · rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_sub]
    · norm_num
    · norm_num
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem centeredSeamVolume (i : Fin (region.bandCount - 1)) :
    volume
      (region.centeredFiber (region.seamLowerBand i) (region.seamHeight i) ∆
        region.centeredFiber (region.seamUpperBand i) (region.seamHeight i)) = 2 := by
  have hi : i = seam := by
    apply Fin.ext
    change i.val = 0
    have hiLt : i.val < 1 := by
      simpa [region] using i.isLt
    omega
  subst i
  rw [region.volume_centeredSeamSymmDiff_eq_abs_totalWidth,
    seamLowerBand, seamUpperBand, seamHeight, totalWidth_zero, totalWidth_one]
  norm_num

theorem seam_widths_ne :
    region.totalWidth (region.seamLowerBand seam) (region.seamHeight seam) ≠
      region.totalWidth (region.seamUpperBand seam) (region.seamHeight seam) := by
  norm_num

theorem seam_bandCenters_ne :
    region.bandCenter (region.seamLowerBand seam) (region.seamHeight seam) ≠
      region.bandCenter (region.seamUpperBand seam) (region.seamHeight seam) := by
  norm_num

theorem deriv_bandCenter_eq_zero (i : Fin region.bandCount) (y : ℝ) :
    deriv (region.bandCenter i) y = 0 := by
  change deriv
    (fun _ : ℝ => (0 + 2 * ((i.val : ℝ) + 1)) / 2) y = 0
  simp only [deriv_const]

theorem graphCost_eq :
    weightedTraceCost 2 region.centeredGraphTrace =
      weightedTraceCost 2 region.graphTrace := by
  rw [region.weightedTraceCost_centeredGraphTrace,
    region.weightedTraceCost_graphTrace,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  exact
    region.centeredBandGraphCost_eq_of_componentCount_eq_one_of_deriv_bandCenter_eq
      2 i (componentCount i) (fun y _hy => deriv_bandCenter_eq_zero i y)

theorem horizontalCost_eq :
    weightedTraceCost 2 region.centeredHorizontalFrontierTrace =
      weightedTraceCost 2 region.horizontalFrontierTrace := by
  rw [region.weightedTraceCost_centeredHorizontalFrontierTrace,
    region.weightedTraceCost_horizontalFrontierTrace,
    region.volume_centeredLowerOuterFiber_eq,
    region.volume_centeredUpperOuterFiber_eq]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _hi
  rw [centeredSeamVolume i, originalSeamVolume i]

/-- Equal literal complete-frontier costs despite unequal band centers.  This
does not satisfy the matching-width hypothesis: the continuous one-sided width
representatives jump from `2` to `4` at the internal cut. -/
theorem frontierCost_eq :
    weightedTraceCost 2 (frontier region.centeredCarrier) =
      weightedTraceCost 2 (frontier region.carrier) := by
  rw [region.weightedTraceCost_frontier_centeredCarrier,
    region.weightedTraceCost_frontier_carrier,
    region.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal,
    region.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal,
    graphCost_eq, horizontalCost_eq]

theorem equal_cost_but_width_jump_and_unequal_centers :
    weightedTraceCost 2 (frontier region.centeredCarrier) =
        weightedTraceCost 2 (frontier region.carrier) ∧
      region.totalWidth (region.seamLowerBand seam) (region.seamHeight seam) ≠
        region.totalWidth (region.seamUpperBand seam) (region.seamHeight seam) ∧
      region.bandCenter (region.seamLowerBand seam) (region.seamHeight seam) ≠
        region.bandCenter (region.seamUpperBand seam) (region.seamHeight seam) :=
  ⟨frontierCost_eq, seam_widths_ne, seam_bandCenters_ne⟩

end CMVRelaxation.FiniteBandRearrangement.TwoBandWidthJump
