import CMVFiniteBandCostAssembly

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation.FiniteBandRearrangement

lemma norm_one_add_mul_I (x : ℝ) :
    ‖(1 : ℂ) + (x : ℂ) * Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring


lemma norm_one_sub_mul_I (x : ℝ) :
    ‖(1 : ℂ) + -(x : ℂ) * Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring
lemma norm_real_add_mul_I (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma endpoint_speed_sum_lower_bound
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    Real.sqrt ((2 * (Fintype.card ι : ℝ)) ^ 2 +
        (∑ i, (b i - a i)) ^ 2) ≤
      ∑ i, (Real.sqrt (1 + (a i) ^ 2) + Real.sqrt (1 + (b i) ^ 2)) := by
  classical
  let z : ι × Bool → ℂ := fun q =>
    (1 : ℂ) + ((if q.2 then b q.1 else -a q.1) : ℂ) * Complex.I
  have hnorm := norm_sum_le (Finset.univ : Finset (ι × Bool)) z
  have hsum : (∑ q : ι × Bool, z q) =
      ((2 * (Fintype.card ι : ℝ) : ℝ) : ℂ) +
        ((∑ i, (b i - a i) : ℝ) : ℂ) * Complex.I := by
    rw [Fintype.sum_prod_type]
    simp only [z, Fintype.sum_bool]
    push_cast
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    apply Complex.ext <;> simp
    · ring
    · ring
  calc
    Real.sqrt ((2 * (Fintype.card ι : ℝ)) ^ 2 +
        (∑ i, (b i - a i)) ^ 2) =
        ‖((2 * (Fintype.card ι : ℝ) : ℝ) : ℂ) +
          ((∑ i, (b i - a i) : ℝ) : ℂ) * Complex.I‖ :=
      (norm_real_add_mul_I _ _).symm
    _ = ‖∑ q : ι × Bool, z q‖ := congrArg norm hsum.symm
    _ ≤ ∑ q : ι × Bool, ‖z q‖ := hnorm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Fintype.sum_bool]
      simp only [z, Bool.false_eq_true, ↓reduceIte,
        norm_one_add_mul_I, norm_one_sub_mul_I]
      ac_rfl

lemma two_mul_speed_half_eq (w : ℝ) :
    2 * Real.sqrt (1 + (w / 2) ^ 2) = Real.sqrt (4 + w ^ 2) := by
  have hinner : 0 ≤ 1 + (w / 2) ^ 2 := by positivity
  have hsquareLeft :
      (2 * Real.sqrt (1 + (w / 2) ^ 2)) ^ 2 = 4 + w ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hinner]
    ring
  have hsquareRight :
      Real.sqrt (4 + w ^ 2) ^ 2 = 4 + w ^ 2 :=
    Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (1 + (w / 2) ^ 2),
    Real.sqrt_nonneg (4 + w ^ 2)]

lemma centered_speed_le_endpoint_speed_sum
    {ι : Type*} [Fintype ι] [Nonempty ι] (a b : ι → ℝ) :
    2 * Real.sqrt (1 + ((∑ i, (b i - a i)) / 2) ^ 2) ≤
      ∑ i, (Real.sqrt (1 + (a i) ^ 2) + Real.sqrt (1 + (b i) ^ 2)) := by
  rw [two_mul_speed_half_eq]
  calc
    Real.sqrt (4 + (∑ i, (b i - a i)) ^ 2) ≤
        Real.sqrt ((2 * (Fintype.card ι : ℝ)) ^ 2 +
          (∑ i, (b i - a i)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
      have hcardReal : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
      nlinarith
    _ ≤ _ := endpoint_speed_sum_lower_bound a b

lemma centered_speed_lt_endpoint_speed_sum_of_one_lt_card
    {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (hcard : 1 < Fintype.card ι) :
    2 * Real.sqrt (1 + ((∑ i, (b i - a i)) / 2) ^ 2) <
      ∑ i, (Real.sqrt (1 + (a i) ^ 2) + Real.sqrt (1 + (b i) ^ 2)) := by
  rw [two_mul_speed_half_eq]
  calc
    Real.sqrt (4 + (∑ i, (b i - a i)) ^ 2) <
        Real.sqrt ((2 * (Fintype.card ι : ℝ)) ^ 2 +
          (∑ i, (b i - a i)) ^ 2) := by
      apply Real.sqrt_lt_sqrt (by positivity)
      have htwo : (2 : ℝ) ≤ Fintype.card ι := by
        exact_mod_cast (Nat.succ_le_iff.mpr hcard)
      nlinarith [sq_nonneg (2 * (Fintype.card ι : ℝ))]
    _ ≤ _ := endpoint_speed_sum_lower_bound a b



/-- A two-component specimen with endpoint slopes `0` and `1`.  Its total
width has nonzero derivative, so the centered interval moves nontrivially in
width, while the two-component graph cost is still strictly larger. -/
theorem twoComponentNonconstantCenter_graphSpeed_strict :
    2 * Real.sqrt
        (1 + ((∑ _j : Fin 2, ((1 : ℝ) - 0)) / 2) ^ 2) <
      ∑ _j : Fin 2,
        (Real.sqrt (1 + (0 : ℝ) ^ 2) +
          Real.sqrt (1 + (1 : ℝ) ^ 2)) := by
  simpa only [Fintype.card_fin] using
    centered_speed_lt_endpoint_speed_sum_of_one_lt_card
      (fun _j : Fin 2 => (0 : ℝ)) (fun _j : Fin 2 => (1 : ℝ))
      (by norm_num)

/-- A translated centered one-component interval has the same graph speed as
its recentered interval.  The constant translation `c` disappears from both
endpoint derivatives. -/
theorem translatedCenteredSingleComponent_graphSpeed_eq (c d y : ℝ) :
    2 * Real.sqrt (1 + d ^ 2) =
      Real.sqrt (1 + deriv (fun z => c - d * z) y ^ 2) +
        Real.sqrt (1 + deriv (fun z => c + d * z) y ^ 2) := by
  have hl : HasDerivAt (fun z : ℝ => c - d * z) (-d) y := by
    simpa using ((hasDerivAt_id y).const_mul d).const_sub c
  have hr : HasDerivAt (fun z : ℝ => c + d * z) d y := by
    simpa only [id_eq, mul_one, add_comm] using
      ((hasDerivAt_id y).const_mul d).add_const c
  rw [hl.deriv, hr.deriv, neg_sq, two_mul]
def Region.originalBandGraphSpeed (R : Region) (i : Fin R.bandCount)
    (y : ℝ) : ℝ :=
  ∑ j : Fin (R.componentCount i),
    (Real.sqrt (1 + deriv (R.left i j) y ^ 2) +
      Real.sqrt (1 + deriv (R.right i j) y ^ 2))

def Region.centeredBandGraphSpeed (R : Region) (i : Fin R.bandCount)
    (y : ℝ) : ℝ :=
  Real.sqrt (1 + deriv (fun z => -R.totalWidth i z / 2) y ^ 2) +
    Real.sqrt (1 + deriv (fun z => R.totalWidth i z / 2) y ^ 2)

theorem Region.deriv_totalWidth (R : Region) (i : Fin R.bandCount)
    {y : ℝ} (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    deriv (R.totalWidth i) y =
      ∑ j : Fin (R.componentCount i),
        (deriv (R.right i j) y - deriv (R.left i j) y) := by
  have hrightDiff (j : Fin (R.componentCount i)) :
      DifferentiableAt ℝ (R.right i j) y :=
    ((R.right_contDiffOn i j).differentiableOn (by norm_num) y hy)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hleftDiff (j : Fin (R.componentCount i)) :
      DifferentiableAt ℝ (R.left i j) y :=
    ((R.left_contDiffOn i j).differentiableOn (by norm_num) y hy)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hhas :
      HasDerivAt (R.totalWidth i)
        (∑ j : Fin (R.componentCount i),
          (deriv (R.right i j) y - deriv (R.left i j) y)) y := by
    rw [show R.totalWidth i =
        ∑ j : Fin (R.componentCount i),
          fun z => R.right i j z - R.left i j z by
      funext z
      simp only [Region.totalWidth, Finset.sum_apply]]
    exact HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (hrightDiff j).hasDerivAt.sub (hleftDiff j).hasDerivAt)
  exact hhas.deriv

theorem Region.centeredBandGraphSpeed_le_originalBandGraphSpeed
    (R : Region) (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    R.centeredBandGraphSpeed i y ≤ R.originalBandGraphSpeed i y := by
  let _ : Nonempty (Fin (R.componentCount i)) :=
    ⟨⟨0, R.componentCount_pos i⟩⟩
  have hwidthDiff : DifferentiableAt ℝ (R.totalWidth i) y :=
    ((R.totalWidth_contDiffOn i).differentiableOn (by norm_num) y hy)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hright :
      deriv (fun z => R.totalWidth i z / 2) y =
        deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.div_const 2 |>.deriv
  have hleft :
      deriv (fun z => -R.totalWidth i z / 2) y =
        -deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.neg.div_const 2 |>.deriv
  rw [Region.centeredBandGraphSpeed, Region.originalBandGraphSpeed,
    hright, hleft, neg_div, neg_sq, R.deriv_totalWidth i hy]
  simpa only [two_mul] using
    centered_speed_le_endpoint_speed_sum
      (fun j : Fin (R.componentCount i) => deriv (R.left i j) y)
      (fun j : Fin (R.componentCount i) => deriv (R.right i j) y)

theorem Region.centeredBandGraphSpeed_lt_originalBandGraphSpeed
    (R : Region) (i : Fin R.bandCount)
    (hmulti : 1 < R.componentCount i) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    R.centeredBandGraphSpeed i y < R.originalBandGraphSpeed i y := by
  have hwidthDiff : DifferentiableAt ℝ (R.totalWidth i) y :=
    ((R.totalWidth_contDiffOn i).differentiableOn (by norm_num) y hy)
      |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
  have hright :
      deriv (fun z => R.totalWidth i z / 2) y =
        deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.div_const 2 |>.deriv
  have hleft :
      deriv (fun z => -R.totalWidth i z / 2) y =
        -deriv (R.totalWidth i) y / 2 :=
    hwidthDiff.hasDerivAt.neg.div_const 2 |>.deriv
  rw [Region.centeredBandGraphSpeed, Region.originalBandGraphSpeed,
    hright, hleft, neg_div, neg_sq, R.deriv_totalWidth i hy]
  simpa only [two_mul, Fintype.card_fin] using
    centered_speed_lt_endpoint_speed_sum_of_one_lt_card
      (fun j : Fin (R.componentCount i) => deriv (R.left i j) y)
      (fun j : Fin (R.componentCount i) => deriv (R.right i j) y)
      (by simpa only [Fintype.card_fin] using hmulti)

def Region.originalBandGraphCost (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) : ENNReal :=
  ∑ q : Fin (R.componentCount i) × Bool,
    R.indexedGraphSpeedCost lam ⟨i, q⟩

def Region.centeredBandGraphCost (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) : ENNReal :=
  ∑ side : Bool, R.indexedCenteredGraphSpeedCost lam (i, side)

lemma Region.ofReal_originalBandGraphSpeed (R : Region)
    (i : Fin R.bandCount) (y : ℝ) :
    ENNReal.ofReal (R.originalBandGraphSpeed i y) =
      ∑ j : Fin (R.componentCount i),
        (ENNReal.ofReal (Real.sqrt (1 + deriv (R.left i j) y ^ 2)) +
          ENNReal.ofReal (Real.sqrt (1 + deriv (R.right i j) y ^ 2))) := by
  rw [Region.originalBandGraphSpeed, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro j _hj
    rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  · intro j _hj
    positivity

lemma Region.ofReal_centeredBandGraphSpeed (R : Region)
    (i : Fin R.bandCount) (y : ℝ) :
    ENNReal.ofReal (R.centeredBandGraphSpeed i y) =
      ENNReal.ofReal
          (Real.sqrt (1 + deriv (fun z => -R.totalWidth i z / 2) y ^ 2)) +
        ENNReal.ofReal
          (Real.sqrt (1 + deriv (fun z => R.totalWidth i z / 2) y ^ 2)) := by
  rw [Region.centeredBandGraphSpeed,
    ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]


lemma sum_setLIntegral_add_eq {ι α : Type*} [Fintype ι]
    [MeasureSpace α] (s : Set α) (f g : ι → α → ENNReal)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    (∑ i, ((∫⁻ x in s, f i x) + ∫⁻ x in s, g i x)) =
      ∫⁻ x in s, ∑ i, (f i x + g i x) := by
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [← lintegral_add_left (hf i) (g i)]
  · intro i _hi
    exact (hf i).add (hg i)
theorem Region.originalBandGraphCost_eq_integrals (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) :
    R.originalBandGraphCost lam i =
      (∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩
          {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal (R.originalBandGraphSpeed i y)) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
            {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal (R.originalBandGraphSpeed i y) := by
  let S₀ := Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩
    {y : ℝ | |y| ≤ 1}
  let S₁ := Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
    {y : ℝ | |y| ≤ 1}
  let L : Fin (R.componentCount i) → ℝ → ENNReal := fun j y =>
    ENNReal.ofReal (Real.sqrt (1 + deriv (R.left i j) y ^ 2))
  let U : Fin (R.componentCount i) → ℝ → ENNReal := fun j y =>
    ENNReal.ofReal (Real.sqrt (1 + deriv (R.right i j) y ^ 2))
  have hL (j : Fin (R.componentCount i)) : Measurable (L j) := by
    dsimp only [L]
    fun_prop
  have hU (j : Fin (R.componentCount i)) : Measurable (U j) := by
    dsimp only [U]
    fun_prop
  have hleft (j : Fin (R.componentCount i)) :
      R.indexedGraphSpeedCost lam ⟨i, (j, false)⟩ =
        (∫⁻ y in S₀, L j y) + ENNReal.ofReal lam * ∫⁻ y in S₁, L j y := by
    rfl
  have hright (j : Fin (R.componentCount i)) :
      R.indexedGraphSpeedCost lam ⟨i, (j, true)⟩ =
        (∫⁻ y in S₀, U j y) + ENNReal.ofReal lam * ∫⁻ y in S₁, U j y := by
    rfl
  rw [Region.originalBandGraphCost, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool, hright, hleft]
  calc
    (∑ j, (((∫⁻ y in S₀, U j y) +
          ENNReal.ofReal lam * ∫⁻ y in S₁, U j y) +
        ((∫⁻ y in S₀, L j y) +
          ENNReal.ofReal lam * ∫⁻ y in S₁, L j y))) =
        (∑ j, ((∫⁻ y in S₀, L j y) + ∫⁻ y in S₀, U j y)) +
          ENNReal.ofReal lam *
            ∑ j, ((∫⁻ y in S₁, L j y) + ∫⁻ y in S₁, U j y) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [mul_add]
      ac_rfl
    _ = (∫⁻ y in S₀, ∑ j, (L j y + U j y)) +
          ENNReal.ofReal lam * ∫⁻ y in S₁, ∑ j, (L j y + U j y) := by
      rw [sum_setLIntegral_add_eq S₀ L U hL hU,
        sum_setLIntegral_add_eq S₁ L U hL hU]
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply setLIntegral_congr_fun
          (measurableSet_Ioo.inter
            (measurableSet_le measurable_abs measurable_const))
        intro y _hy
        dsimp only [L, U]
        exact (R.ofReal_originalBandGraphSpeed i y).symm
      · apply congrArg (ENNReal.ofReal lam * ·)
        apply setLIntegral_congr_fun
          (measurableSet_Ioo.diff
            (measurableSet_le measurable_abs measurable_const))
        intro y _hy
        dsimp only [L, U]
        exact (R.ofReal_originalBandGraphSpeed i y).symm

theorem Region.centeredBandGraphCost_eq_integrals (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) :
    R.centeredBandGraphCost lam i =
      (∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩
          {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal (R.centeredBandGraphSpeed i y)) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
            {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal (R.centeredBandGraphSpeed i y) := by
  let S₀ := Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩
    {y : ℝ | |y| ≤ 1}
  let S₁ := Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
    {y : ℝ | |y| ≤ 1}
  let L : ℝ → ENNReal := fun y => ENNReal.ofReal
    (Real.sqrt (1 + deriv (fun z => -R.totalWidth i z / 2) y ^ 2))
  let U : ℝ → ENNReal := fun y => ENNReal.ofReal
    (Real.sqrt (1 + deriv (fun z => R.totalWidth i z / 2) y ^ 2))
  have hL : Measurable L := by dsimp only [L]; fun_prop
  have hU : Measurable U := by dsimp only [U]; fun_prop
  have hleft :
      R.indexedCenteredGraphSpeedCost lam (i, false) =
        (∫⁻ y in S₀, L y) + ENNReal.ofReal lam * ∫⁻ y in S₁, L y := by
    rfl
  have hright :
      R.indexedCenteredGraphSpeedCost lam (i, true) =
        (∫⁻ y in S₀, U y) + ENNReal.ofReal lam * ∫⁻ y in S₁, U y := by
    rfl
  rw [Region.centeredBandGraphCost, Fintype.sum_bool, hright, hleft]
  calc
    ((∫⁻ y in S₀, U y) + ENNReal.ofReal lam * ∫⁻ y in S₁, U y) +
          ((∫⁻ y in S₀, L y) + ENNReal.ofReal lam * ∫⁻ y in S₁, L y) =
        ((∫⁻ y in S₀, L y) + ∫⁻ y in S₀, U y) +
          ENNReal.ofReal lam *
            ((∫⁻ y in S₁, L y) + ∫⁻ y in S₁, U y) := by
      simp only [mul_add]
      ac_rfl
    _ = (∫⁻ y in S₀, L y + U y) +
          ENNReal.ofReal lam * ∫⁻ y in S₁, L y + U y := by
      rw [← lintegral_add_left hL U, ← lintegral_add_left hL U]
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply setLIntegral_congr_fun
          (measurableSet_Ioo.inter
            (measurableSet_le measurable_abs measurable_const))
        intro y _hy
        dsimp only [L, U]
        exact (R.ofReal_centeredBandGraphSpeed i y).symm
      · apply congrArg (ENNReal.ofReal lam * ·)
        apply setLIntegral_congr_fun
          (measurableSet_Ioo.diff
            (measurableSet_le measurable_abs measurable_const))
        intro y _hy
        dsimp only [L, U]
        exact (R.ofReal_centeredBandGraphSpeed i y).symm

theorem Region.centeredBandGraphCost_le_originalBandGraphCost
    (R : Region) (lam : ℝ) (i : Fin R.bandCount) :
    R.centeredBandGraphCost lam i ≤ R.originalBandGraphCost lam i := by
  rw [R.centeredBandGraphCost_eq_integrals,
    R.originalBandGraphCost_eq_integrals]
  apply add_le_add
  · apply setLIntegral_mono'
      (measurableSet_Ioo.inter
        (measurableSet_le measurable_abs measurable_const))
    intro y hy
    exact ENNReal.ofReal_le_ofReal
      (R.centeredBandGraphSpeed_le_originalBandGraphSpeed i hy.1)
  · apply mul_le_mul_right
    apply setLIntegral_mono'
      (measurableSet_Ioo.diff
        (measurableSet_le measurable_abs measurable_const))
    intro y hy
    exact ENNReal.ofReal_le_ofReal
      (R.centeredBandGraphSpeed_le_originalBandGraphSpeed i hy.1)


theorem Region.centeredBandGraphCost_lt_originalBandGraphCost
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam) (i : Fin R.bandCount)
    (hmulti : 1 < R.componentCount i) :
    R.centeredBandGraphCost lam i < R.originalBandGraphCost lam i := by
  let S := Ioo (R.cuts i.castSucc) (R.cuts i.succ)
  let Z : Set ℝ := {y | |y| ≤ 1}
  let S₀ := S ∩ Z
  let S₁ := S \ Z
  let C : ℝ → ENNReal := fun y =>
    ENNReal.ofReal (R.centeredBandGraphSpeed i y)
  let O : ℝ → ENNReal := fun y =>
    ENNReal.ofReal (R.originalBandGraphSpeed i y)
  have hCmeas : Measurable C := by
    dsimp only [C]
    apply ENNReal.measurable_ofReal.comp
    unfold Region.centeredBandGraphSpeed
    fun_prop
  have hOmeas : Measurable O := by
    dsimp only [O]
    apply ENNReal.measurable_ofReal.comp
    unfold Region.originalBandGraphSpeed
    fun_prop
  have hCintegrable : IntegrableOn (R.centeredBandGraphSpeed i) S := by
    dsimp only [S]
    unfold Region.centeredBandGraphSpeed
    exact
      (integrableOn_speed_neg_div_two (R.totalWidth_contDiffOn i)
        (R.totalWidth_speed_integrable i)).add
      (integrableOn_speed_div_two (R.totalWidth_contDiffOn i)
        (R.totalWidth_speed_integrable i))
  have hCfinite : (∫⁻ y in S, C y) ≠ ⊤ := by
    exact (hCintegrable.setLIntegral_lt_top).ne
  have hSmeas : MeasurableSet S := measurableSet_Ioo
  have hZmeas : MeasurableSet Z :=
    measurableSet_le measurable_abs measurable_const
  have hS₀meas : MeasurableSet S₀ := hSmeas.inter hZmeas
  have hS₁meas : MeasurableSet S₁ := hSmeas.diff hZmeas
  have hdisjoint : Disjoint S₀ S₁ := by
    rw [Set.disjoint_left]
    intro y hy₀ hy₁
    exact hy₁.2 hy₀.2
  have hunion : S₀ ∪ S₁ = S := by
    ext y
    simp only [S₀, S₁, mem_union, mem_inter_iff, Set.mem_sdiff, Z, S]
    tauto
  have hpartition (f : ℝ → ENNReal) :
      (∫⁻ y in S, f y) = (∫⁻ y in S₀, f y) + ∫⁻ y in S₁, f y := by
    rw [← lintegral_union hS₁meas hdisjoint, hunion]
  have hstrictWhole : (∫⁻ y in S, C y) < ∫⁻ y in S, O y := by
    apply setLIntegral_strict_mono hSmeas
        (ne_of_gt ((Measure.measure_Ioo_pos volume).2
          (R.cuts_strict Fin.castSucc_lt_succ)))
      hOmeas hCfinite
    filter_upwards with y
    intro hy
    have hstrict :=
      R.centeredBandGraphSpeed_lt_originalBandGraphSpeed i hmulti hy
    dsimp only [C, O]
    apply (ENNReal.ofReal_lt_ofReal_iff
      (lt_of_le_of_lt (by
        unfold Region.centeredBandGraphSpeed
        positivity) hstrict)).2
    exact hstrict
  have hstrictSplit :
      (∫⁻ y in S₀, C y) + (∫⁻ y in S₁, C y) <
        (∫⁻ y in S₀, O y) + ∫⁻ y in S₁, O y := by
    rw [← hpartition C, ← hpartition O]
    exact hstrictWhole
  have hC₁O₁ : (∫⁻ y in S₁, C y) ≤ ∫⁻ y in S₁, O y := by
    apply setLIntegral_mono' hS₁meas
    intro y hy
    exact ENNReal.ofReal_le_ofReal
      (R.centeredBandGraphSpeed_le_originalBandGraphSpeed i hy.1)
  have ha : (1 : ENNReal) ≤ ENNReal.ofReal lam := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hlam
  have hadecomp :
      ENNReal.ofReal lam = 1 + (ENNReal.ofReal lam - 1) :=
    (add_tsub_cancel_of_le ha).symm
  rw [R.centeredBandGraphCost_eq_integrals,
    R.originalBandGraphCost_eq_integrals]
  change (∫⁻ y in S₀, C y) + ENNReal.ofReal lam * (∫⁻ y in S₁, C y) <
    (∫⁻ y in S₀, O y) + ENNReal.ofReal lam * ∫⁻ y in S₁, O y
  rw [hadecomp, add_mul, one_mul, add_mul, one_mul]
  calc
    (∫⁻ y in S₀, C y) +
          ((∫⁻ y in S₁, C y) +
            (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, C y) =
        ((∫⁻ y in S₀, C y) + ∫⁻ y in S₁, C y) +
          (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, C y := by ac_rfl
    _ < ((∫⁻ y in S₀, O y) + ∫⁻ y in S₁, O y) +
          (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, O y := by
      apply ENNReal.add_lt_add_of_lt_of_le
      · apply ENNReal.mul_ne_top
        · exact ENNReal.sub_ne_top ENNReal.ofReal_ne_top
        · exact (hCintegrable.mono_set Set.sdiff_subset).setLIntegral_lt_top.ne
      · exact hstrictSplit
      · exact mul_le_mul_right hC₁O₁ _
    _ = (∫⁻ y in S₀, O y) +
          ((∫⁻ y in S₁, O y) +
            (ENNReal.ofReal lam - 1) * ∫⁻ y in S₁, O y) := by ac_rfl
theorem Region.weightedTraceCost_centeredGraphTrace_le_graphTrace
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.centeredGraphTrace ≤
      weightedTraceCost lam R.graphTrace := by
  rw [R.weightedTraceCost_centeredGraphTrace,
    R.weightedTraceCost_graphTrace,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro i _hi
  exact R.centeredBandGraphCost_le_originalBandGraphCost lam i

theorem Region.weightedTraceCost_centeredGraphTrace_lt_graphTrace
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam) (i : Fin R.bandCount)
    (hmulti : 1 < R.componentCount i) :
    weightedTraceCost lam R.centeredGraphTrace <
      weightedTraceCost lam R.graphTrace := by
  rw [R.weightedTraceCost_centeredGraphTrace,
    R.weightedTraceCost_graphTrace,
    Fintype.sum_prod_type, Fintype.sum_sigma]
  have hrestLe :
      (∑ k ∈ Finset.univ.erase i, R.centeredBandGraphCost lam k) ≤
        ∑ k ∈ Finset.univ.erase i, R.originalBandGraphCost lam k := by
    apply Finset.sum_le_sum
    intro k _hk
    exact R.centeredBandGraphCost_le_originalBandGraphCost lam k
  have hrestFinite :
      (∑ k ∈ Finset.univ.erase i, R.centeredBandGraphCost lam k) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro k _hk
    unfold Region.centeredBandGraphCost
    exact ENNReal.sum_ne_top.mpr fun side _ =>
      R.indexedCenteredGraphSpeedCost_ne_top lam (k, side)
  calc
    (∑ k, R.centeredBandGraphCost lam k) =
        (∑ k ∈ Finset.univ.erase i, R.centeredBandGraphCost lam k) +
          R.centeredBandGraphCost lam i :=
      (Finset.sum_erase_add Finset.univ
        (fun k => R.centeredBandGraphCost lam k) (Finset.mem_univ i)).symm
    _ < (∑ k ∈ Finset.univ.erase i, R.originalBandGraphCost lam k) +
          R.originalBandGraphCost lam i :=
      ENNReal.add_lt_add_of_le_of_lt hrestFinite hrestLe
        (R.centeredBandGraphCost_lt_originalBandGraphCost hlam i hmulti)
    _ = ∑ k, R.originalBandGraphCost lam k :=
      Finset.sum_erase_add Finset.univ
        (fun k => R.originalBandGraphCost lam k) (Finset.mem_univ i)

theorem Region.totalWidth_nonneg_of_mem_Icc (R : Region)
    (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)) :
    0 ≤ R.totalWidth i y := by
  rw [Region.totalWidth]
  apply Finset.sum_nonneg
  intro j _hj
  exact sub_nonneg.mpr (R.width_nonneg i j y hy)

theorem Region.volume_centeredFiber_eq (R : Region)
    (i : Fin R.bandCount) (y : ℝ) :
    volume (R.centeredFiber i y) = ENNReal.ofReal (R.totalWidth i y) := by
  rw [Region.centeredFiber, Real.volume_Icc]
  congr 1
  ring

lemma volume_centeredInterval_symmDiff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    volume (Icc (-u / 2) (u / 2) ∆ Icc (-v / 2) (v / 2)) =
      ENNReal.ofReal |u - v| := by
  rcases le_total u v with huv | hvu
  · have hsub : Icc (-u / 2) (u / 2) ⊆ Icc (-v / 2) (v / 2) := by
      intro x hx
      constructor <;> linarith [hx.1, hx.2]
    rw [symmDiff_of_le hsub,
      measure_sdiff hsub measurableSet_Icc.nullMeasurableSet]
    · rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_sub]
      · congr 1
        rw [abs_of_nonpos (sub_nonpos.mpr huv)]
        ring
      · nlinarith
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
  · have hsub : Icc (-v / 2) (v / 2) ⊆ Icc (-u / 2) (u / 2) := by
      intro x hx
      constructor <;> linarith [hx.1, hx.2]
    rw [symmDiff_of_ge hsub,
      measure_sdiff hsub measurableSet_Icc.nullMeasurableSet]
    · rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_sub]
      · congr 1
        rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
        ring
      · nlinarith
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top


theorem Region.volume_centeredFiber_symmDiff_eq_abs_totalWidth
    (R : Region) (i k : Fin R.bandCount) (y : ℝ)
    (hyi : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ))
    (hyk : y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ)) :
    volume (R.centeredFiber i y ∆ R.centeredFiber k y) =
      ENNReal.ofReal |R.totalWidth i y - R.totalWidth k y| := by
  rw [Region.centeredFiber, Region.centeredFiber]
  exact volume_centeredInterval_symmDiff
    (R.totalWidth_nonneg_of_mem_Icc i hyi)
    (R.totalWidth_nonneg_of_mem_Icc k hyk)
theorem Region.volume_centeredFiber_symmDiff_le_fiber_symmDiff
    (R : Region) (i k : Fin R.bandCount) (y : ℝ)
    (hyi : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ))
    (hyk : y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ)) :
    volume (R.centeredFiber i y ∆ R.centeredFiber k y) ≤
      volume (R.fiber i y ∆ R.fiber k y) := by
  have hui := R.totalWidth_nonneg_of_mem_Icc i hyi
  have huk := R.totalWidth_nonneg_of_mem_Icc k hyk
  rw [Region.centeredFiber, Region.centeredFiber,
    volume_centeredInterval_symmDiff hui huk]
  rcases le_total (R.totalWidth i y) (R.totalWidth k y) with hik | hki
  · rw [abs_of_nonpos (sub_nonpos.mpr hik)]
    rw [show -(R.totalWidth i y - R.totalWidth k y) =
      R.totalWidth k y - R.totalWidth i y by ring]
    calc
      ENNReal.ofReal (R.totalWidth k y - R.totalWidth i y) =
          ENNReal.ofReal (R.totalWidth k y) -
            ENNReal.ofReal (R.totalWidth i y) := ENNReal.ofReal_sub _ hui
      _ = volume (R.fiber k y) - volume (R.fiber i y) := by
        rw [R.volume_fiber_of_mem_Icc k hyk,
          R.volume_fiber_of_mem_Icc i hyi]
      _ ≤ volume (R.fiber k y ∆ R.fiber i y) := le_measure_symmDiff
      _ = volume (R.fiber i y ∆ R.fiber k y) := by
        rw [symmDiff_comm]
  · rw [abs_of_nonneg (sub_nonneg.mpr hki)]
    calc
      ENNReal.ofReal (R.totalWidth i y - R.totalWidth k y) =
          ENNReal.ofReal (R.totalWidth i y) -
            ENNReal.ofReal (R.totalWidth k y) := ENNReal.ofReal_sub _ huk
      _ = volume (R.fiber i y) - volume (R.fiber k y) := by
        rw [R.volume_fiber_of_mem_Icc i hyi,
          R.volume_fiber_of_mem_Icc k hyk]
      _ ≤ volume (R.fiber i y ∆ R.fiber k y) := le_measure_symmDiff

theorem Region.volume_centeredLowerOuterFiber_eq (R : Region) :
    volume (R.centeredFiber R.firstBand (R.cuts R.firstBand.castSucc)) =
      volume (R.fiber R.firstBand (R.cuts R.firstBand.castSucc)) := by
  rw [R.volume_centeredFiber_eq,
    R.volume_fiber_of_mem_Icc R.firstBand
      ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩]

theorem Region.volume_centeredUpperOuterFiber_eq (R : Region) :
    volume (R.centeredFiber R.lastBand (R.cuts R.lastBand.succ)) =
      volume (R.fiber R.lastBand (R.cuts R.lastBand.succ)) := by
  rw [R.volume_centeredFiber_eq,
    R.volume_fiber_of_mem_Icc R.lastBand
      ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩]


theorem Region.volume_centeredSeamSymmDiff_eq_abs_totalWidth (R : Region)
    (i : Fin (R.bandCount - 1)) :
    volume
        (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) =
      ENNReal.ofReal
        |R.totalWidth (R.seamLowerBand i) (R.seamHeight i) -
          R.totalWidth (R.seamUpperBand i) (R.seamHeight i)| := by
  apply R.volume_centeredFiber_symmDiff_eq_abs_totalWidth
  · rw [R.cuts_seamLower_succ i]
    exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
  · exact ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩
theorem Region.volume_centeredSeamSymmDiff_le (R : Region)
    (i : Fin (R.bandCount - 1)) :
    volume
        (R.centeredFiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.centeredFiber (R.seamUpperBand i) (R.seamHeight i)) ≤
      volume
        (R.fiber (R.seamLowerBand i) (R.seamHeight i) ∆
          R.fiber (R.seamUpperBand i) (R.seamHeight i)) := by
  apply R.volume_centeredFiber_symmDiff_le_fiber_symmDiff
  · rw [R.cuts_seamLower_succ i]
    exact ⟨(R.cuts_strict Fin.castSucc_lt_succ).le, le_rfl⟩
  · exact ⟨le_rfl, (R.cuts_strict Fin.castSucc_lt_succ).le⟩

theorem Region.weightedTraceCost_centeredHorizontalFrontierTrace_le
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.centeredHorizontalFrontierTrace ≤
      weightedTraceCost lam R.horizontalFrontierTrace := by
  rw [R.weightedTraceCost_centeredHorizontalFrontierTrace,
    R.weightedTraceCost_horizontalFrontierTrace,
    R.volume_centeredLowerOuterFiber_eq,
    R.volume_centeredUpperOuterFiber_eq]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _hi
  apply mul_le_mul_right
  exact R.volume_centeredSeamSymmDiff_le i

theorem Region.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeFrontierTrace =
      weightedTraceCost lam R.graphTrace +
        weightedTraceCost lam R.horizontalFrontierTrace := by
  rw [R.weightedTraceCost_completeFrontierTrace,
    R.weightedTraceCost_graphTrace,
    R.weightedTraceCost_horizontalFrontierTrace]

theorem Region.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeCenteredFrontierTrace =
      weightedTraceCost lam R.centeredGraphTrace +
        weightedTraceCost lam R.centeredHorizontalFrontierTrace := by
  rw [R.weightedTraceCost_completeCenteredFrontierTrace,
    R.weightedTraceCost_centeredGraphTrace,
    R.weightedTraceCost_centeredHorizontalFrontierTrace]

theorem Region.weightedTraceCost_completeCenteredFrontierTrace_le
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam R.completeCenteredFrontierTrace ≤
      weightedTraceCost lam R.completeFrontierTrace := by
  rw [R.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal,
    R.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal]
  exact add_le_add
    (R.weightedTraceCost_centeredGraphTrace_le_graphTrace lam)
    (R.weightedTraceCost_centeredHorizontalFrontierTrace_le lam)

theorem Region.weightedTraceCost_completeCenteredFrontierTrace_lt
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam) (i : Fin R.bandCount)
    (hmulti : 1 < R.componentCount i) :
    weightedTraceCost lam R.completeCenteredFrontierTrace <
      weightedTraceCost lam R.completeFrontierTrace := by
  have hhorizontalFinite :
      weightedTraceCost lam R.centeredHorizontalFrontierTrace ≠ ⊤ := by
    have hcomplete :=
      R.weightedTraceCost_completeCenteredFrontierTrace_ne_top lam
    rw [R.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal]
      at hcomplete
    exact (ENNReal.add_ne_top.mp hcomplete).2
  rw [R.weightedTraceCost_completeCenteredFrontierTrace_eq_graph_add_horizontal,
    R.weightedTraceCost_completeFrontierTrace_eq_graph_add_horizontal]
  exact ENNReal.add_lt_add_of_lt_of_le hhorizontalFinite
    (R.weightedTraceCost_centeredGraphTrace_lt_graphTrace hlam i hmulti)
    (R.weightedTraceCost_centeredHorizontalFrontierTrace_le lam)

/-- Horizontal centering does not increase the literal complete-frontier
weighted cost.  This compares the actual topological frontiers, not relaxed
perimeters or almost-everywhere representatives. -/
theorem Region.weightedTraceCost_frontier_centeredCarrier_le
    (R : Region) (lam : ℝ) :
    weightedTraceCost lam (frontier R.centeredCarrier) ≤
      weightedTraceCost lam (frontier R.carrier) := by
  rw [R.weightedTraceCost_frontier_centeredCarrier,
    R.weightedTraceCost_frontier_carrier]
  exact R.weightedTraceCost_completeCenteredFrontierTrace_le lam

theorem Region.weightedTraceCost_frontier_centeredCarrier_lt
    (R : Region) {lam : ℝ} (hlam : 1 ≤ lam) (i : Fin R.bandCount)
    (hmulti : 1 < R.componentCount i) :
    weightedTraceCost lam (frontier R.centeredCarrier) <
      weightedTraceCost lam (frontier R.carrier) := by
  rw [R.weightedTraceCost_frontier_centeredCarrier,
    R.weightedTraceCost_frontier_carrier]
  exact R.weightedTraceCost_completeCenteredFrontierTrace_lt hlam i hmulti
end CMVRelaxation.FiniteBandRearrangement
