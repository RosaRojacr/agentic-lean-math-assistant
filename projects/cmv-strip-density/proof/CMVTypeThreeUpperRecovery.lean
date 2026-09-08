/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTypeThreeLowerRecovery

/-!
# Upper-contact recovery for type-(iii) assemblies

This module constructs the parameter-safe upper junction collar used to smooth
the two contacts between the strip-side circles and the exterior cap.  The
collar scale is derived from the actual assembly; no caller supplies it.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff

noncomputable section

namespace CMVRelaxation.TypeThreeRecovery

/-- Radicand of either strip-side circle when it is written as a horizontal
half-width near the upper interface. -/
def upperSideRadicand {lam : ℝ} (a : TypeThreeAssembly lam) (y : ℝ) : ℝ :=
  a.radius ^ 2 - (y - (a.radius - 1)) ^ 2

/-- Squared half-width of the actual type-(iii) core near `y = 1`. -/
def upperSideSquare {lam : ℝ} (a : TypeThreeAssembly lam) (y : ℝ) : ℝ :=
  (a.sideHalfWidth + √(upperSideRadicand a y)) ^ 2

/-- Squared half-width of the actual exterior cap. -/
def upperCapSquare {lam : ℝ} (a : TypeThreeAssembly lam) (y : ℝ) : ℝ :=
  a.radius ^ 2 - (y - a.upperCenter.2) ^ 2

/-- Positive half-width of the common upper attachment chord. -/
def upperAttachmentWidth {lam : ℝ} (a : TypeThreeAssembly lam) : ℝ :=
  a.radius * Real.sin a.outerAngle

lemma upperAttachmentWidth_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 < upperAttachmentWidth a := by
  exact mul_pos a.radius_pos a.outerSin_pos

lemma radius_mul_cos_innerAngle
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    a.radius * Real.cos a.innerAngle = 2 - a.radius := by
  rw [a.cos_innerAngle, TypeThreeAssembly.shapeParameter]
  nlinarith [a.radius_mul_h]

lemma upperSideRadicand_one
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    upperSideRadicand a 1 =
      (a.radius * Real.sin a.innerAngle) ^ 2 := by
  have htrig := congrArg (fun z : ℝ => a.radius ^ 2 * z)
    (Real.sin_sq_add_cos_sq a.innerAngle)
  have hcos := radius_mul_cos_innerAngle a
  unfold upperSideRadicand
  nlinarith

lemma upperSideRadicand_one_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 < upperSideRadicand a 1 := by
  rw [upperSideRadicand_one]
  exact sq_pos_of_pos (mul_pos a.radius_pos a.innerSin_pos)

lemma upperSideSquare_one
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    upperSideSquare a 1 = upperAttachmentWidth a ^ 2 := by
  rw [upperSideSquare, upperSideRadicand_one,
    Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos a.radius_pos a.innerSin_pos)]
  unfold upperAttachmentWidth TypeThreeAssembly.sideHalfWidth
  ring

lemma upperCapSquare_one
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    upperCapSquare a 1 = upperAttachmentWidth a ^ 2 := by
  have htrig := congrArg (fun z : ℝ => a.radius ^ 2 * z)
    (Real.sin_sq_add_cos_sq a.outerAngle)
  unfold upperCapSquare upperAttachmentWidth TypeThreeAssembly.upperCenter
  nlinarith

lemma upperAttachmentSquare_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 < upperAttachmentWidth a ^ 2 :=
  sq_pos_of_pos (upperAttachmentWidth_pos a)

lemma contDiff_upperSideRadicand
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ContDiff ℝ ∞ (upperSideRadicand a) := by
  unfold upperSideRadicand
  fun_prop

lemma continuous_upperSideSquare
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    Continuous (upperSideSquare a) := by
  unfold upperSideSquare
  exact (continuous_const.add
    (Real.continuous_sqrt.comp
      (contDiff_upperSideRadicand a).continuous)).pow 2

lemma contDiff_upperCapSquare
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ContDiff ℝ ∞ (upperCapSquare a) := by
  unfold upperCapSquare TypeThreeAssembly.upperCenter
  fun_prop

/-- A positive collar on which the side radical is regular and both squared
widths stay uniformly separated from zero. -/
private theorem exists_upperSafeScaleData
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 8 ∧
      ∀ y : ℝ, |y - 1| ≤ 2 * s →
        0 < upperSideRadicand a y ∧
        upperAttachmentWidth a ^ 2 / 2 < upperSideSquare a y ∧
        upperAttachmentWidth a ^ 2 / 2 < upperCapSquare a y := by
  let A : ℝ := upperAttachmentWidth a ^ 2
  have hA : 0 < A := upperAttachmentSquare_pos a
  have hradNhd : {y : ℝ | 0 < upperSideRadicand a y} ∈ 𝓝 (1 : ℝ) := by
    apply (isOpen_lt continuous_const
      (contDiff_upperSideRadicand a).continuous).mem_nhds
    exact upperSideRadicand_one_pos a
  have hsideNhd : {y : ℝ | A / 2 < upperSideSquare a y} ∈ 𝓝 (1 : ℝ) := by
    apply (isOpen_lt continuous_const
      (continuous_upperSideSquare a)).mem_nhds
    change A / 2 < upperSideSquare a 1
    rw [upperSideSquare_one]
    dsimp [A]
    linarith
  have hcapNhd : {y : ℝ | A / 2 < upperCapSquare a y} ∈ 𝓝 (1 : ℝ) := by
    apply (isOpen_lt continuous_const
      (contDiff_upperCapSquare a).continuous).mem_nhds
    change A / 2 < upperCapSquare a 1
    rw [upperCapSquare_one]
    dsimp [A]
    linarith
  have hall :
      ({y : ℝ | 0 < upperSideRadicand a y} ∩
        ({y : ℝ | A / 2 < upperSideSquare a y} ∩
          {y : ℝ | A / 2 < upperCapSquare a y})) ∈ 𝓝 (1 : ℝ) :=
    inter_mem hradNhd (inter_mem hsideNhd hcapNhd)
  rcases Metric.mem_nhds_iff.mp hall with ⟨r, hr, hball⟩
  let s : ℝ := min (1 / 8) (r / 4)
  have hs : 0 < s := by
    dsimp [s]
    rw [lt_min_iff]
    exact ⟨by norm_num, div_pos hr (by norm_num)⟩
  refine ⟨s, hs, min_le_left _ _, ?_⟩
  intro y hy
  have hsle : s ≤ r / 4 := min_le_right _ _
  have hydist : dist y 1 < r := by
    rw [Real.dist_eq]
    calc
      |y - 1| ≤ 2 * s := hy
      _ ≤ r / 2 := by linarith
      _ < r := by linarith
  have hyall := hball hydist
  exact ⟨hyall.1, hyall.2.1, hyall.2.2⟩

/-- Internally selected upper-contact collar scale. -/
def upperSafeScale {lam : ℝ} (a : TypeThreeAssembly lam) : ℝ :=
  Classical.choose (exists_upperSafeScaleData a)

lemma upperSafeScale_spec
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 < upperSafeScale a ∧ upperSafeScale a ≤ 1 / 8 ∧
      ∀ y : ℝ, |y - 1| ≤ 2 * upperSafeScale a →
        0 < upperSideRadicand a y ∧
        upperAttachmentWidth a ^ 2 / 2 < upperSideSquare a y ∧
        upperAttachmentWidth a ^ 2 / 2 < upperCapSquare a y :=
  Classical.choose_spec (exists_upperSafeScaleData a)

lemma upperSafeScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 < upperSafeScale a :=
  (upperSafeScale_spec a).1

lemma upperSafeScale_le_eighth
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    upperSafeScale a ≤ 1 / 8 :=
  (upperSafeScale_spec a).2.1

lemma upper_collar_width_bounds
    {lam : ℝ} (a : TypeThreeAssembly lam) {y : ℝ}
    (hy : |y - 1| ≤ 2 * upperSafeScale a) :
    0 < upperSideRadicand a y ∧
      upperAttachmentWidth a ^ 2 / 2 < upperSideSquare a y ∧
      upperAttachmentWidth a ^ 2 / 2 < upperCapSquare a y :=
  (upperSafeScale_spec a).2.2 y hy

lemma contDiffOn_upperSideSquare
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ContDiffOn ℝ ∞ (upperSideSquare a)
      (Ioo (1 - 2 * upperSafeScale a)
        (1 + 2 * upperSafeScale a)) := by
  have hrad : ∀ y ∈ Ioo (1 - 2 * upperSafeScale a)
      (1 + 2 * upperSafeScale a), upperSideRadicand a y ≠ 0 := by
    intro y hy
    have habs : |y - 1| ≤ 2 * upperSafeScale a := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    exact (upper_collar_width_bounds a habs).1.ne'
  unfold upperSideSquare
  exact (contDiffOn_const.add
    ((contDiff_upperSideRadicand a).contDiffOn.sqrt hrad)).pow 2

/-- Smooth transition from the side squared width at `y ≤ 1 - epsilon` to the
cap squared width at `y ≥ 1`. -/
def upperJunctionWeight (epsilon y : ℝ) : ℝ :=
  Real.smoothTransition ((y - (1 - epsilon)) / epsilon)

lemma contDiff_upperJunctionWeight (epsilon : ℝ) :
    ContDiff ℝ ∞ (upperJunctionWeight epsilon) := by
  unfold upperJunctionWeight
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const epsilon)

lemma upperJunctionWeight_mem_Icc (epsilon y : ℝ) :
    upperJunctionWeight epsilon y ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma upperJunctionWeight_eq_zero
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hy : y ≤ 1 - epsilon) :
    upperJunctionWeight epsilon y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hepsilon.le

lemma upperJunctionWeight_eq_one
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hy : 1 ≤ y) :
    upperJunctionWeight epsilon y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hepsilon]
  linarith

/-- The actual squared-width interpolation across the upper contact. -/
def upperBlendQ {lam : ℝ} (a : TypeThreeAssembly lam)
    (epsilon y : ℝ) : ℝ :=
  upperSideSquare a y + upperJunctionWeight epsilon y *
    (upperCapSquare a y - upperSideSquare a y)

lemma upperBlendQ_eq_side
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hy : y ≤ 1 - epsilon) :
    upperBlendQ a epsilon y = upperSideSquare a y := by
  rw [upperBlendQ, upperJunctionWeight_eq_zero hepsilon hy]
  ring

lemma upperBlendQ_eq_cap
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hy : 1 ≤ y) :
    upperBlendQ a epsilon y = upperCapSquare a y := by
  rw [upperBlendQ, upperJunctionWeight_eq_one hepsilon hy]
  ring

lemma contDiffOn_upperBlendQ
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    ContDiffOn ℝ ∞ (upperBlendQ a epsilon)
      (Ioo (1 - 2 * upperSafeScale a)
        (1 + 2 * upperSafeScale a)) := by
  unfold upperBlendQ
  exact (contDiffOn_upperSideSquare a).add
    ((contDiff_upperJunctionWeight epsilon).contDiffOn.mul
      ((contDiff_upperCapSquare a).contDiffOn.sub
        (contDiffOn_upperSideSquare a)))

/-- Height parameter for either upper replacement trace. -/
def upperJunctionHeight (epsilon t : ℝ) : ℝ :=
  1 - epsilon + epsilon * t

/-- Squared width along the normalized upper replacement trace. -/
def upperNormalizedQ {lam : ℝ} (a : TypeThreeAssembly lam)
    (epsilon t : ℝ) : ℝ :=
  upperBlendQ a epsilon (upperJunctionHeight epsilon t)

lemma upperJunctionHeight_mem_collar
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ upperSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |upperJunctionHeight epsilon t - 1| ≤ 2 * upperSafeScale a := by
  have hheight :
      -epsilon ≤ upperJunctionHeight epsilon t - 1 ∧
        upperJunctionHeight epsilon t - 1 ≤ 0 := by
    unfold upperJunctionHeight
    constructor <;> nlinarith [ht.1, ht.2]
  rw [abs_le]
  constructor <;> linarith

lemma upperNormalizedQ_lower
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ upperSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    upperAttachmentWidth a ^ 2 / 2 < upperNormalizedQ a epsilon t := by
  let y := upperJunctionHeight epsilon t
  let w := upperJunctionWeight epsilon y
  have hwidth := upper_collar_width_bounds a
    (upperJunctionHeight_mem_collar a hepsilon hepsilon_le ht)
  have hw := upperJunctionWeight_mem_Icc epsilon y
  rw [show upperNormalizedQ a epsilon t =
      (1 - w) * upperSideSquare a y + w * upperCapSquare a y by
    unfold upperNormalizedQ upperBlendQ y w
    ring]
  calc
    upperAttachmentWidth a ^ 2 / 2 =
        (1 - w) * (upperAttachmentWidth a ^ 2 / 2) +
          w * (upperAttachmentWidth a ^ 2 / 2) := by ring
    _ < (1 - w) * upperSideSquare a y + w * upperCapSquare a y := by
      rcases eq_or_lt_of_le hw.2 with hw1 | hw1
      · change w = 1 at hw1
        rw [hw1]
        simpa using hwidth.2.2
      · change w < 1 at hw1
        have hleft : 0 < 1 - w := sub_pos.mpr hw1
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hwidth.2.1 hleft)
          (mul_le_mul_of_nonneg_left hwidth.2.2.le hw.1)

lemma upperNormalizedQ_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ upperSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < upperNormalizedQ a epsilon t :=
  lt_trans (div_pos (upperAttachmentSquare_pos a) (by norm_num))
    (upperNormalizedQ_lower a hepsilon hepsilon_le ht)

/-- One of the two reflected upper replacement traces. -/
def signedUpperContactTrace
    {lam : ℝ} (a : TypeThreeAssembly lam)
    (horizontalSign epsilon t : ℝ) : PlanePoint :=
  (horizontalSign * √(upperNormalizedQ a epsilon t),
    upperJunctionHeight epsilon t)

/-- Local open squared-width domain supplying the regular upper splice. -/
def upperBlendDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) : Set PlanePoint :=
  {p | p.1 ^ 2 < upperBlendQ a epsilon p.2}

lemma isOpen_upperBlendDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    IsOpen (upperBlendDomain a epsilon) := by
  apply isOpen_lt (continuous_fst.pow 2)
  unfold upperBlendQ upperSideSquare upperSideRadicand upperCapSquare
    TypeThreeAssembly.upperCenter upperJunctionWeight
  fun_prop

/-- Every point on either normalized upper trace has a literal local regular
one-sided defining function.  Positivity of the common attachment width makes
the horizontal derivative nonzero throughout the collar. -/
theorem signedUpperContactTrace_regular_at
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon t : ℝ}
    (hsign : |horizontalSign| = 1)
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ upperSafeScale a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ (V : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen V ∧ signedUpperContactTrace a horizontalSign epsilon t ∈ V ∧
      ContDiffOn ℝ ∞ g V ∧
      g (signedUpperContactTrace a horizontalSign epsilon t) = 0 ∧
      HasFDerivAt g D
        (signedUpperContactTrace a horizontalSign epsilon t) ∧
      D ≠ 0 ∧
      upperBlendDomain a epsilon ∩ V = V ∩ {q | g q < 0} := by
  let p := signedUpperContactTrace a horizontalSign epsilon t
  let I : Set ℝ := Ioo (1 - 2 * upperSafeScale a)
    (1 + 2 * upperSafeScale a)
  let V : Set PlanePoint := Prod.snd ⁻¹' I
  let g : PlanePoint → ℝ :=
    fun q => q.1 ^ 2 - upperBlendQ a epsilon q.2
  have hheight := upperJunctionHeight_mem_collar a hepsilon hepsilon_le ht
  have hheightStrict : |upperJunctionHeight epsilon t - 1| <
      2 * upperSafeScale a := by
    have hs := upperSafeScale_pos a
    have hraw : |upperJunctionHeight epsilon t - 1| ≤ epsilon := by
      unfold upperJunctionHeight
      rw [abs_le]
      constructor <;> nlinarith [ht.1, ht.2]
    exact lt_of_le_of_lt hraw (by linarith)
  have hpV : p ∈ V := by
    change upperJunctionHeight epsilon t ∈
      Ioo (1 - 2 * upperSafeScale a) (1 + 2 * upperSafeScale a)
    rw [abs_lt] at hheightStrict
    exact ⟨by linarith [hheightStrict.1], by linarith [hheightStrict.2]⟩
  have hqAt : ContDiffAt ℝ ∞ (upperBlendQ a epsilon) p.2 := by
    exact (contDiffOn_upperBlendQ a epsilon).contDiffAt
      (isOpen_Ioo.mem_nhds hpV)
  let d : ℝ := deriv (upperBlendQ a epsilon) p.2
  let D : PlanePoint →L[ℝ] ℝ :=
    (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ -
      (ContinuousLinearMap.toSpanSingleton ℝ d).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hqDeriv : HasDerivAt (upperBlendQ a epsilon) d p.2 :=
    (hqAt.differentiableAt (by simp)).hasDerivAt
  have hderiv : HasFDerivAt g D p := by
    change HasFDerivAt
      ((fun q : PlanePoint => q.1 ^ 2) -
        upperBlendQ a epsilon ∘ Prod.snd) D p
    simpa [D, d] using
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).sub
        (hqDeriv.hasFDerivAt.comp p
          (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  have hqpos := upperNormalizedQ_pos a hepsilon hepsilon_le ht
  have hsqrtpos : 0 < √(upperNormalizedQ a epsilon t) :=
    Real.sqrt_pos.2 hqpos
  have hp1 : p.1 ≠ 0 := by
    have hsignne : horizontalSign ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hsign
      norm_num at hsign
    dsimp [p, signedUpperContactTrace]
    exact mul_ne_zero hsignne hsqrtpos.ne'
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg
      (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hzero
    have : 2 * p.1 = 0 := by simpa [D] using happ
    exact hp1 (by linarith)
  refine ⟨V, g, D, ?_, hpV, ?_, ?_, hderiv, hD, ?_⟩
  · exact isOpen_Ioo.preimage continuous_snd
  · change ContDiffOn ℝ ∞
      (fun q : PlanePoint => q.1 ^ 2 - upperBlendQ a epsilon q.2) V
    exact (contDiffOn_fst.pow 2).sub
      ((contDiffOn_upperBlendQ a epsilon).comp contDiffOn_snd
        (fun _ hq => hq))
  · dsimp [g, p, signedUpperContactTrace]
    have hsq := Real.sq_sqrt hqpos.le
    rw [mul_pow, show horizontalSign ^ 2 = 1 by
      calc
        horizontalSign ^ 2 = |horizontalSign| ^ 2 := by rw [sq_abs]
        _ = 1 := by rw [hsign]; norm_num,
      one_mul, hsq]
    simp [upperNormalizedQ]
  · ext q
    change ((q.1 ^ 2 < upperBlendQ a epsilon q.2) ∧ q ∈ V) ↔
      (q ∈ V ∧ q.1 ^ 2 - upperBlendQ a epsilon q.2 < 0)
    constructor
    · rintro ⟨hq, hqV⟩
      exact ⟨hqV, sub_neg.mpr hq⟩
    · rintro ⟨hqV, hq⟩
      exact ⟨sub_neg.mp hq, hqV⟩

lemma signedUpperContactTrace_start
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ} (hepsilon : 0 < epsilon) :
    signedUpperContactTrace a horizontalSign epsilon 0 =
      (horizontalSign * √(upperSideSquare a (1 - epsilon)),
        1 - epsilon) := by
  unfold signedUpperContactTrace upperNormalizedQ upperJunctionHeight
  rw [upperBlendQ_eq_side a hepsilon (by linarith)]
  congr 1 <;> ring

lemma signedUpperContactTrace_end
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ} (hepsilon : 0 < epsilon) :
    signedUpperContactTrace a horizontalSign epsilon 1 =
      (horizontalSign * upperAttachmentWidth a, 1) := by
  unfold signedUpperContactTrace upperNormalizedQ upperJunctionHeight
  rw [show 1 - epsilon + epsilon * 1 = 1 by ring,
    upperBlendQ_eq_cap a hepsilon le_rfl, upperCapSquare_one,
    Real.sqrt_sq_eq_abs, abs_of_pos (upperAttachmentWidth_pos a)]

/-! ## Buffered upper replacement and global convergence -/

/-- Closed band removed from the target interior before inserting the smooth
upper splice.  It is strictly buffered inside `upperOuterBand`. -/
def upperInnerBand (epsilon : ℝ) : Set PlanePoint :=
  Prod.snd ⁻¹' Icc (1 - 4 * epsilon / 3) (1 + epsilon / 3)

/-- Open band carrying the smooth squared-width splice. -/
def upperOuterBand (epsilon : ℝ) : Set PlanePoint :=
  Prod.snd ⁻¹' Ioo (1 - 3 * epsilon / 2) (1 + epsilon / 2)

lemma isClosed_upperInnerBand (epsilon : ℝ) :
    IsClosed (upperInnerBand epsilon) :=
  isClosed_Icc.preimage continuous_snd

lemma isOpen_upperOuterBand (epsilon : ℝ) :
    IsOpen (upperOuterBand epsilon) :=
  isOpen_Ioo.preimage continuous_snd

lemma upperInnerBand_subset_outerBand
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    upperInnerBand epsilon ⊆ upperOuterBand epsilon := by
  intro p hp
  change p.2 ∈ Icc (1 - 4 * epsilon / 3) (1 + epsilon / 3) at hp
  change p.2 ∈ Ioo (1 - 3 * epsilon / 2) (1 + epsilon / 2)
  constructor <;> linarith [hp.1, hp.2]

/-- Replace the complete upper-contact band while retaining the target
interior outside a smaller closed band.  The two buffers are what permit a
later local gluing proof at both window edges. -/
def upperSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) : Set PlanePoint :=
  (interior a.carrier \ upperInnerBand epsilon) ∪
    (upperBlendDomain a epsilon ∩ upperOuterBand epsilon)

lemma isOpen_upperSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    IsOpen (upperSurgeryDomain a epsilon) := by
  exact (isOpen_interior.sdiff (isClosed_upperInnerBand epsilon)).union
    ((isOpen_upperBlendDomain a epsilon).inter
      (isOpen_upperOuterBand epsilon))

/-- Every point changed by the upper replacement lies in its explicit
shrinking outer band. -/
lemma upperSurgeryDomain_symmDiff_interior_subset_outerBand
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    upperSurgeryDomain a epsilon ∆ interior a.carrier ⊆
      upperOuterBand epsilon := by
  intro p hp
  have hinner := upperInnerBand_subset_outerBand hepsilon
  simp only [Set.mem_symmDiff, upperSurgeryDomain, Set.mem_union,
    Set.mem_sdiff, Set.mem_inter_iff] at hp
  rcases hp with hp | hp
  · rcases hp.1 with htarget | hblend
    · exact False.elim (hp.2 htarget.1)
    · exact hblend.2
  · by_contra hnot
    apply hp.2
    left
    exact ⟨hp.1, fun hpInner => hnot (hinner hpInner)⟩

/-- A finite assembly-dependent horizontal radius containing both the target
and every retained upper splice section. -/
def upperHorizontalRadius
    {lam : ℝ} (a : TypeThreeAssembly lam) : ℝ :=
  a.sideHalfWidth + a.radius + 1

lemma upperHorizontalRadius_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 < upperHorizontalRadius a := by
  unfold upperHorizontalRadius
  linarith [a.sideHalfWidth_nonneg, a.radius_pos]

lemma carrier_abs_fst_lt_upperHorizontalRadius
    {lam : ℝ} (a : TypeThreeAssembly lam) {p : PlanePoint}
    (hp : p ∈ a.carrier) :
    |p.1| < upperHorizontalRadius a := by
  have hR := a.radius_pos
  have hw := a.sideHalfWidth_nonneg
  simp only [TypeThreeAssembly.carrier, TypeThreeAssembly.coreCarrier,
    TypeThreeAssembly.rectangleCarrier, TypeThreeAssembly.leftSegmentCarrier,
    TypeThreeAssembly.rightSegmentCarrier, OneSidedCircularCap.carrier,
    Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq] at hp
  rcases hp with ((hrect | hleft) | hright) | hcap
  · have habs : |p.1| ≤ a.sideHalfWidth := abs_le.mpr ⟨hrect.1.1, hrect.1.2⟩
    unfold upperHorizontalRadius
    linarith
  · have hdisk := hleft.1
    have hshift :
        |p.1 + a.sideHalfWidth| ≤ a.radius := by
      rw [abs_le]
      constructor <;>
        simp only [TypeThreeAssembly.leftCenter] at hdisk <;> nlinarith
    have hpbound : |p.1| ≤ a.sideHalfWidth + a.radius := by
      calc
        |p.1| = |(p.1 + a.sideHalfWidth) - a.sideHalfWidth| := by ring_nf
        _ ≤ |p.1 + a.sideHalfWidth| + |a.sideHalfWidth| := abs_sub _ _
        _ ≤ a.radius + a.sideHalfWidth := by
          rw [abs_of_nonneg hw]
          gcongr
        _ = a.sideHalfWidth + a.radius := by ring
    unfold upperHorizontalRadius
    linarith
  · have hdisk := hright.1
    have hshift :
        |p.1 - a.sideHalfWidth| ≤ a.radius := by
      rw [abs_le]
      constructor <;>
        simp only [TypeThreeAssembly.rightCenter] at hdisk <;> nlinarith
    have hpbound : |p.1| ≤ a.sideHalfWidth + a.radius := by
      calc
        |p.1| = |(p.1 - a.sideHalfWidth) + a.sideHalfWidth| := by ring_nf
        _ ≤ |p.1 - a.sideHalfWidth| + |a.sideHalfWidth| := abs_add_le _ _
        _ ≤ a.radius + a.sideHalfWidth := by
          rw [abs_of_nonneg hw]
          gcongr
        _ = a.sideHalfWidth + a.radius := by ring
    unfold upperHorizontalRadius
    linarith
  · have hdisk := hcap.1
    have hxSq : p.1 ^ 2 ≤ a.radius ^ 2 := by
      rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
        a.outerCap_radius] at hdisk
      simp only [TypeThreeAssembly.upperCenter, sub_zero] at hdisk
      nlinarith [sq_nonneg (p.2 - (1 - a.radius * Real.cos a.outerAngle))]
    have habs : |p.1| ≤ a.radius := by
      exact (sq_le_sq₀ (abs_nonneg p.1) hR.le).1
        (by simpa only [sq_abs] using hxSq)
    unfold upperHorizontalRadius
    linarith

lemma upperBlendQ_le_horizontalRadius_sq
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon y : ℝ} (_hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a)
    (hy : |y - 1| ≤ 2 * epsilon) :
    upperBlendQ a epsilon y ≤ upperHorizontalRadius a ^ 2 := by
  have hcollar : |y - 1| ≤ 2 * upperSafeScale a := by
    exact hy.trans (mul_le_mul_of_nonneg_left hepsilon_le (by norm_num))
  have hrad := (upper_collar_width_bounds a hcollar).1
  have hsqrtSq :
      (√(upperSideRadicand a y)) ^ 2 = upperSideRadicand a y :=
    Real.sq_sqrt hrad.le
  have hsqrt0 : 0 ≤ √(upperSideRadicand a y) := Real.sqrt_nonneg _
  have hsqrtLe : √(upperSideRadicand a y) ≤ a.radius := by
    apply (sq_le_sq₀ hsqrt0 a.radius_pos.le).1
    rw [hsqrtSq]
    unfold upperSideRadicand
    nlinarith [sq_nonneg (y - (a.radius - 1))]
  have hsideWidth0 :
      0 ≤ a.sideHalfWidth + √(upperSideRadicand a y) :=
    add_nonneg a.sideHalfWidth_nonneg hsqrt0
  have hsideWidth :
      a.sideHalfWidth + √(upperSideRadicand a y) <
        upperHorizontalRadius a := by
    unfold upperHorizontalRadius
    linarith
  have hside :
      upperSideSquare a y ≤ upperHorizontalRadius a ^ 2 := by
    unfold upperSideSquare
    exact (sq_le_sq₀ hsideWidth0
      (upperHorizontalRadius_pos a).le).2 hsideWidth.le
  have hcap :
      upperCapSquare a y ≤ upperHorizontalRadius a ^ 2 := by
    have hRle : a.radius < upperHorizontalRadius a := by
      unfold upperHorizontalRadius
      linarith [a.sideHalfWidth_nonneg]
    unfold upperCapSquare
    calc
      a.radius ^ 2 - (y - a.upperCenter.2) ^ 2 ≤ a.radius ^ 2 := by
        nlinarith [sq_nonneg (y - a.upperCenter.2)]
      _ ≤ upperHorizontalRadius a ^ 2 :=
        (sq_le_sq₀ a.radius_pos.le
          (upperHorizontalRadius_pos a).le).2 hRle.le
  let w := upperJunctionWeight epsilon y
  have hw := upperJunctionWeight_mem_Icc epsilon y
  rw [show upperBlendQ a epsilon y =
      (1 - w) * upperSideSquare a y + w * upperCapSquare a y by
    unfold upperBlendQ w
    ring]
  calc
    (1 - w) * upperSideSquare a y + w * upperCapSquare a y ≤
        (1 - w) * upperHorizontalRadius a ^ 2 +
          w * upperHorizontalRadius a ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hside (sub_nonneg.mpr hw.2))
        (mul_le_mul_of_nonneg_left hcap hw.1)
    _ = upperHorizontalRadius a ^ 2 := by ring

lemma upperSurgeryDomain_symmDiff_interior_subset_rectangle
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    upperSurgeryDomain a epsilon ∆ interior a.carrier ⊆
      Icc (-upperHorizontalRadius a) (upperHorizontalRadius a) ×ˢ
        Ioo (1 - 3 * epsilon / 2) (1 + epsilon / 2) := by
  intro p hp
  have hy :=
    upperSurgeryDomain_symmDiff_interior_subset_outerBand a hepsilon hp
  have hx : |p.1| ≤ upperHorizontalRadius a := by
    rcases hp with hp | hp
    · rcases hp.1 with htarget | hblend
      · exact (carrier_abs_fst_lt_upperHorizontalRadius a
          (interior_subset htarget.1)).le
      · have hyabs : |p.2 - 1| ≤ 2 * epsilon := by
          have hyBand := hblend.2
          change p.2 ∈ Ioo (1 - 3 * epsilon / 2)
            (1 + epsilon / 2) at hyBand
          rw [abs_le]
          constructor <;> linarith [hyBand.1, hyBand.2]
        have hq := upperBlendQ_le_horizontalRadius_sq a hepsilon
          hepsilon_le hyabs
        have hpq : p.1 ^ 2 < upperBlendQ a epsilon p.2 := hblend.1
        exact (abs_le).2 ⟨by
          nlinarith [upperHorizontalRadius_pos a],
          by nlinarith [upperHorizontalRadius_pos a]⟩
    · exact (carrier_abs_fst_lt_upperHorizontalRadius a
        (interior_subset hp.1)).le
  exact ⟨(abs_le.mp hx), hy⟩

theorem characteristicDistance_upperSurgeryDomain_interior_le
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    characteristicDistance (upperSurgeryDomain a epsilon)
        (interior a.carrier) ≤
      ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) := by
  unfold characteristicDistance
  calc
    volume (upperSurgeryDomain a epsilon ∆ interior a.carrier) ≤
        volume
          (Icc (-upperHorizontalRadius a) (upperHorizontalRadius a) ×ˢ
            Ioo (1 - 3 * epsilon / 2) (1 + epsilon / 2)) :=
      measure_mono
        (upperSurgeryDomain_symmDiff_interior_subset_rectangle
          a hepsilon hepsilon_le)
    _ = ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) := by
      rw [Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_Icc, Real.volume_Ioo, ← ENNReal.ofReal_mul]
      · congr 1
        ring
      · linarith [upperHorizontalRadius_pos a]

theorem characteristicDistance_upperSurgeryDomain_carrier_le
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    characteristicDistance (upperSurgeryDomain a epsilon) a.carrier ≤
      ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) := by
  rw [← characteristicDistance_congr_ae
    (upperSurgeryDomain a epsilon) (interior_carrier_ae_eq_carrier a)]
  exact characteristicDistance_upperSurgeryDomain_interior_le
    a hepsilon hepsilon_le

/-- Positive upper-contact scales tending to zero. -/
def upperRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) : ℝ :=
  upperSafeScale a / ((n : ℝ) + 1)

lemma upperRecoveryScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) :
    0 < upperRecoveryScale a n :=
  div_pos (upperSafeScale_pos a) (by positivity)

lemma upperRecoveryScale_le
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) :
    upperRecoveryScale a n ≤ upperSafeScale a := by
  unfold upperRecoveryScale
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  nlinarith [upperSafeScale_pos a]

lemma tendsto_upperRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    Tendsto (upperRecoveryScale a) atTop (𝓝 0) := by
  unfold upperRecoveryScale
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- The buffered upper replacements converge globally to the literal closed
type-(iii) carrier.  Smooth-domain gluing with the lower patches is a separate
obligation; this theorem does not mislabel the partial replacement as a
`SmoothSequence`. -/
theorem tendsto_characteristicDistance_upperSurgeryDomain_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    Tendsto
      (fun n => characteristicDistance
        (upperSurgeryDomain a (upperRecoveryScale a n)) a.carrier)
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun n : ℕ =>
        ENNReal.ofReal
          (4 * upperHorizontalRadius a * upperRecoveryScale a n))
      atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n : ℕ =>
          4 * upperHorizontalRadius a * upperRecoveryScale a n)
        atTop (𝓝 (4 * upperHorizontalRadius a * 0)) :=
      tendsto_const_nhds.mul (tendsto_upperRecoveryScale a)
    simpa using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun n =>
      characteristicDistance_upperSurgeryDomain_carrier_le a
        (upperRecoveryScale_pos a n) (upperRecoveryScale_le a n))

/-! ## Actual target agreement on both gluing buffers -/

lemma mem_carrier_iff_sq_le_upperSideSquare
    {lam : ℝ} (a : TypeThreeAssembly lam) (p : PlanePoint)
    (hy : p.2 ∈ Icc (-1 : ℝ) 1) :
    p ∈ a.carrier ↔ p.1 ^ 2 ≤ upperSideSquare a p.2 := by
  have hR := a.radius_pos
  have hw := a.sideHalfWidth_nonneg
  have hoffset :
      |p.2 - (a.radius - 1)| ≤ a.radius := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2, a.one_lt_radius]
  have hoffsetSq :
      (p.2 - (a.radius - 1)) ^ 2 ≤ a.radius ^ 2 := by
    apply sq_le_sq.mpr
    simpa [abs_of_pos hR] using hoffset
  have hrad : 0 ≤ upperSideRadicand a p.2 := by
    unfold upperSideRadicand
    linarith
  let root := √(upperSideRadicand a p.2)
  let W := a.sideHalfWidth + root
  have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
  have hrootSq : root ^ 2 = upperSideRadicand a p.2 :=
    Real.sq_sqrt hrad
  have hW0 : 0 ≤ W := add_nonneg hw hroot0
  have hside : upperSideSquare a p.2 = W ^ 2 := by
    rfl
  simp only [TypeThreeAssembly.carrier, TypeThreeAssembly.coreCarrier,
    TypeThreeAssembly.rectangleCarrier, TypeThreeAssembly.leftSegmentCarrier,
    TypeThreeAssembly.rightSegmentCarrier, OneSidedCircularCap.carrier,
    Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (((hrect | hleft) | hright) | hcap)
    · have habs : |p.1| ≤ a.sideHalfWidth :=
        abs_le.mpr ⟨hrect.1.1, hrect.1.2⟩
      rw [hside]
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg p.1) hW0).2
          (habs.trans (by dsimp [W]; linarith)))
    · have hxside : p.1 ≤ -a.sideHalfWidth := by
        simpa only [TypeThreeAssembly.leftCenter] using hleft.2.1
      have hshift0 : p.1 + a.sideHalfWidth ≤ 0 := by linarith
      have hshiftSq :
          (p.1 + a.sideHalfWidth) ^ 2 ≤ root ^ 2 := by
        rw [hrootSq]
        unfold upperSideRadicand
        have hdisk := hleft.1
        simp only [TypeThreeAssembly.leftCenter, sub_neg_eq_add] at hdisk
        nlinarith
      have hshiftAbs : |p.1 + a.sideHalfWidth| ≤ root :=
        (sq_le_sq₀ (abs_nonneg _) hroot0).1
          (by simpa only [sq_abs] using hshiftSq)
      have hx0 : p.1 ≤ 0 := by linarith
      have habs : |p.1| ≤ W := by
        rw [abs_of_nonpos hx0]
        rw [abs_of_nonpos hshift0] at hshiftAbs
        dsimp [W]
        linarith
      rw [hside]
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg p.1) hW0).2 habs)
    · have hxside : a.sideHalfWidth ≤ p.1 := by
        simpa only [TypeThreeAssembly.rightCenter] using hright.2.1
      have hshift0 : 0 ≤ p.1 - a.sideHalfWidth := by linarith
      have hshiftSq :
          (p.1 - a.sideHalfWidth) ^ 2 ≤ root ^ 2 := by
        rw [hrootSq]
        unfold upperSideRadicand
        have hdisk := hright.1
        simp only [TypeThreeAssembly.rightCenter] at hdisk
        nlinarith
      have hshiftAbs : |p.1 - a.sideHalfWidth| ≤ root :=
        (sq_le_sq₀ (abs_nonneg _) hroot0).1
          (by simpa only [sq_abs] using hshiftSq)
      have hx0 : 0 ≤ p.1 := by linarith
      have habs : |p.1| ≤ W := by
        rw [abs_of_nonneg hx0]
        rw [abs_of_nonneg hshift0] at hshiftAbs
        dsimp [W]
        linarith
      rw [hside]
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg p.1) hW0).2 habs)
    · have hyeq : p.2 = 1 := by
        have hycap : (1 : ℝ) ≤ p.2 := by
          simpa only [TypeThreeAssembly.outerCap] using hcap.2
        exact le_antisymm hy.2 hycap
      have hxcap : p.1 ^ 2 ≤ upperCapSquare a 1 := by
        have hdisk := hcap.1
        rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
          a.outerCap_radius] at hdisk
        rw [hyeq] at hdisk
        simp only [TypeThreeAssembly.upperCenter, sub_zero] at hdisk
        unfold upperCapSquare
        simp only [TypeThreeAssembly.upperCenter]
        nlinarith
      rw [hyeq, upperSideSquare_one, ← upperCapSquare_one]
      exact hxcap
  · intro hxSq
    have habs : |p.1| ≤ W := by
      rw [hside] at hxSq
      exact (sq_le_sq₀ (abs_nonneg p.1) hW0).1
        (by simpa only [sq_abs] using hxSq)
    by_cases hxleft : p.1 ≤ -a.sideHalfWidth
    · apply Or.inl
      apply Or.inl
      apply Or.inr
      refine ⟨?_, ?_, hy.1, hy.2⟩
      · have hx0 : p.1 ≤ 0 := by linarith
        have hshift0 : p.1 + a.sideHalfWidth ≤ 0 := by linarith
        have hshiftAbs : |p.1 + a.sideHalfWidth| ≤ root := by
          rw [abs_of_nonpos hshift0]
          rw [abs_of_nonpos hx0] at habs
          dsimp [W] at habs
          linarith
        have hshiftSq :
            (p.1 + a.sideHalfWidth) ^ 2 ≤ root ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) hroot0).2 hshiftAbs
        rw [hrootSq] at hshiftSq
        unfold upperSideRadicand at hshiftSq
        simp only [TypeThreeAssembly.leftCenter, sub_neg_eq_add]
        nlinarith
      · simpa only [TypeThreeAssembly.leftCenter] using hxleft
    · by_cases hxright : a.sideHalfWidth ≤ p.1
      · apply Or.inl
        apply Or.inr
        refine ⟨?_, ?_, hy.1, hy.2⟩
        · have hx0 : 0 ≤ p.1 := by linarith
          have hshift0 : 0 ≤ p.1 - a.sideHalfWidth := by linarith
          have hshiftAbs : |p.1 - a.sideHalfWidth| ≤ root := by
            rw [abs_of_nonneg hshift0]
            rw [abs_of_nonneg hx0] at habs
            dsimp [W] at habs
            linarith
          have hshiftSq :
              (p.1 - a.sideHalfWidth) ^ 2 ≤ root ^ 2 := by
            simpa only [sq_abs] using
              (sq_le_sq₀ (abs_nonneg _) hroot0).2 hshiftAbs
          rw [hrootSq] at hshiftSq
          unfold upperSideRadicand at hshiftSq
          simp only [TypeThreeAssembly.rightCenter]
          nlinarith
        · simpa only [TypeThreeAssembly.rightCenter] using hxright
      · apply Or.inl
        apply Or.inl
        apply Or.inl
        exact ⟨⟨le_of_not_ge hxleft, le_of_not_ge hxright⟩, hy⟩

lemma mem_interior_carrier_iff_sq_lt_upperSideSquare
    {lam : ℝ} (a : TypeThreeAssembly lam) (p : PlanePoint)
    (hy : p.2 ∈ Ioo (-1 : ℝ) 1) :
    p ∈ interior a.carrier ↔ p.1 ^ 2 < upperSideSquare a p.2 := by
  have hyClosed : p.2 ∈ Icc (-1 : ℝ) 1 := ⟨hy.1.le, hy.2.le⟩
  constructor
  · intro hp
    have hle := (mem_carrier_iff_sq_le_upperSideSquare a p hyClosed).1
      (interior_subset hp)
    apply lt_of_le_of_ne hle
    intro heq
    have hnhds : interior a.carrier ∈ 𝓝 p :=
      isOpen_interior.mem_nhds hp
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hball⟩
    by_cases hx : 0 ≤ p.1
    · let z : PlanePoint := (p.1 + r / 2, p.2)
      have hzball : z ∈ Metric.ball p r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [z]
        rw [abs_of_pos (by linarith : 0 < p.1 + r / 2 - p.1)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hzCarrier : z ∈ a.carrier := interior_subset (hball hzball)
      have hzle := (mem_carrier_iff_sq_le_upperSideSquare a z hyClosed).1
        hzCarrier
      change (p.1 + r / 2) ^ 2 ≤ upperSideSquare a p.2 at hzle
      nlinarith
    · have hxneg : p.1 < 0 := lt_of_not_ge hx
      let z : PlanePoint := (p.1 - r / 2, p.2)
      have hzball : z ∈ Metric.ball p r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [z]
        rw [abs_of_neg (by linarith : p.1 - r / 2 - p.1 < 0)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hzCarrier : z ∈ a.carrier := interior_subset (hball hzball)
      have hzle := (mem_carrier_iff_sq_le_upperSideSquare a z hyClosed).1
        hzCarrier
      change (p.1 - r / 2) ^ 2 ≤ upperSideSquare a p.2 at hzle
      nlinarith
  · intro hp
    let U : Set PlanePoint :=
      {q | q.1 ^ 2 < upperSideSquare a q.2} ∩
        (Prod.snd ⁻¹' Ioo (-1 : ℝ) 1)
    have hopen : IsOpen U :=
      (isOpen_lt (continuous_fst.pow 2)
        ((continuous_upperSideSquare a).comp continuous_snd)).inter
        (isOpen_Ioo.preimage continuous_snd)
    have hsub : U ⊆ a.carrier := by
      intro q hq
      exact (mem_carrier_iff_sq_le_upperSideSquare a q
        ⟨hq.2.1.le, hq.2.2.le⟩).2 hq.1.le
    exact interior_maximal hsub hopen ⟨hp, hy⟩

lemma mem_carrier_iff_sq_le_upperCapSquare_of_one_lt
    {lam : ℝ} (a : TypeThreeAssembly lam) (p : PlanePoint)
    (hy : 1 < p.2) :
    p ∈ a.carrier ↔ p.1 ^ 2 ≤ upperCapSquare a p.2 := by
  simp only [TypeThreeAssembly.carrier, TypeThreeAssembly.coreCarrier,
    TypeThreeAssembly.rectangleCarrier, TypeThreeAssembly.leftSegmentCarrier,
    TypeThreeAssembly.rightSegmentCarrier, OneSidedCircularCap.carrier,
    Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (((hrect | hleft) | hright) | hcap)
    · exfalso
      linarith [hrect.2.2]
    · exfalso
      linarith [hleft.2.2.2]
    · exfalso
      linarith [hright.2.2.2]
    · have hdisk := hcap.1
      rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
        a.outerCap_radius] at hdisk
      simp only [TypeThreeAssembly.upperCenter, sub_zero] at hdisk
      unfold upperCapSquare
      simp only [TypeThreeAssembly.upperCenter]
      nlinarith
  · intro hp
    apply Or.inr
    constructor
    · rw [OneSidedCircularCap.radiusSquaredAt, a.outerCap_center,
        a.outerCap_radius]
      unfold upperCapSquare at hp
      simp only [TypeThreeAssembly.upperCenter, sub_zero] at hp ⊢
      nlinarith
    · simpa only [TypeThreeAssembly.outerCap] using hy.le

lemma mem_interior_carrier_iff_sq_lt_upperCapSquare
    {lam : ℝ} (a : TypeThreeAssembly lam) (p : PlanePoint)
    (hy : 1 < p.2) (hqpos : 0 < upperCapSquare a p.2) :
    p ∈ interior a.carrier ↔ p.1 ^ 2 < upperCapSquare a p.2 := by
  constructor
  · intro hp
    have hle := (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt a p hy).1
      (interior_subset hp)
    apply lt_of_le_of_ne hle
    intro heq
    have hxne : p.1 ≠ 0 := by
      intro hx
      rw [hx] at heq
      norm_num at heq
      linarith
    have hnhds : interior a.carrier ∈ 𝓝 p :=
      isOpen_interior.mem_nhds hp
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hball⟩
    by_cases hx : 0 < p.1
    · let z : PlanePoint := (p.1 + r / 2, p.2)
      have hzball : z ∈ Metric.ball p r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [z]
        rw [abs_of_pos (by linarith : 0 < p.1 + r / 2 - p.1)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hzCarrier : z ∈ a.carrier := interior_subset (hball hzball)
      have hzle :=
        (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt a z hy).1 hzCarrier
      change (p.1 + r / 2) ^ 2 ≤ upperCapSquare a p.2 at hzle
      nlinarith
    · have hxneg : p.1 < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
      let z : PlanePoint := (p.1 - r / 2, p.2)
      have hzball : z ∈ Metric.ball p r := by
        rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        dsimp [z]
        rw [abs_of_neg (by linarith : p.1 - r / 2 - p.1 < 0)]
        simp only [sub_self, abs_zero]
        ring_nf
        rw [max_eq_left (by positivity)]
        linarith
      have hzCarrier : z ∈ a.carrier := interior_subset (hball hzball)
      have hzle :=
        (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt a z hy).1 hzCarrier
      change (p.1 - r / 2) ^ 2 ≤ upperCapSquare a p.2 at hzle
      nlinarith
  · intro hp
    let U : Set PlanePoint :=
      {q | q.1 ^ 2 < upperCapSquare a q.2} ∩
        (Prod.snd ⁻¹' Ioi (1 : ℝ))
    have hopen : IsOpen U :=
      (isOpen_lt (continuous_fst.pow 2)
        ((contDiff_upperCapSquare a).continuous.comp continuous_snd)).inter
        (isOpen_Ioi.preimage continuous_snd)
    have hsub : U ⊆ a.carrier := by
      intro q hq
      exact (mem_carrier_iff_sq_le_upperCapSquare_of_one_lt a q hq.2).2
        hq.1.le
    exact interior_maximal hsub hopen ⟨hp, hy⟩

/-- On the lower gluing buffer the actual target interior and the smooth
replacement agree exactly. -/
theorem upperBlendDomain_eq_interior_on_lowerBuffer
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    upperBlendDomain a epsilon ∩
        (Prod.snd ⁻¹' Ioo (1 - 3 * epsilon / 2) (1 - epsilon)) =
      interior a.carrier ∩
        (Prod.snd ⁻¹' Ioo (1 - 3 * epsilon / 2) (1 - epsilon)) := by
  ext p
  simp only [upperBlendDomain, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_preimage, Set.mem_Ioo]
  constructor
  · rintro ⟨hp, hy⟩
    refine ⟨?_, hy⟩
    have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · have hs := hepsilon_le.trans (upperSafeScale_le_eighth a)
        linarith
      · linarith
    rw [upperBlendQ_eq_side a hepsilon hy.2.le] at hp
    exact (mem_interior_carrier_iff_sq_lt_upperSideSquare a p hyStrip).2 hp
  · rintro ⟨hp, hy⟩
    refine ⟨?_, hy⟩
    have hyStrip : p.2 ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · have hs := hepsilon_le.trans (upperSafeScale_le_eighth a)
        linarith
      · linarith
    rw [upperBlendQ_eq_side a hepsilon hy.2.le]
    exact (mem_interior_carrier_iff_sq_lt_upperSideSquare a p hyStrip).1 hp

/-- On the upper gluing buffer the replacement is exactly the actual cap
interior. -/
theorem upperBlendDomain_eq_interior_on_upperBuffer
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    upperBlendDomain a epsilon ∩
        (Prod.snd ⁻¹' Ioo 1 (1 + epsilon / 2)) =
      interior a.carrier ∩
        (Prod.snd ⁻¹' Ioo 1 (1 + epsilon / 2)) := by
  ext p
  simp only [upperBlendDomain, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.mem_preimage, Set.mem_Ioo]
  have hyabs (hylo : 1 < p.2) (hyhi : p.2 < 1 + epsilon / 2) :
      |p.2 - 1| ≤ 2 * upperSafeScale a := by
    rw [abs_le]
    constructor
    · linarith
    · have he := hepsilon_le
      linarith
  constructor
  · rintro ⟨hp, hy⟩
    refine ⟨?_, hy⟩
    rw [upperBlendQ_eq_cap a hepsilon hy.1.le] at hp
    have hcapPos := (upper_collar_width_bounds a (hyabs hy.1 hy.2)).2.2
    exact (mem_interior_carrier_iff_sq_lt_upperCapSquare
      a p hy.1 (lt_trans (by
        exact div_pos (upperAttachmentSquare_pos a) (by norm_num)) hcapPos)).2 hp
  · rintro ⟨hp, hy⟩
    refine ⟨?_, hy⟩
    rw [upperBlendQ_eq_cap a hepsilon hy.1.le]
    have hcapPos := (upper_collar_width_bounds a (hyabs hy.1 hy.2)).2.2
    exact (mem_interior_carrier_iff_sq_lt_upperCapSquare
      a p hy.1 (lt_trans (by
        exact div_pos (upperAttachmentSquare_pos a) (by norm_num)) hcapPos)).1 hp
/-! ## Combined lower-and-upper surgery -/

/-- The nondegenerate candidate recovery set: the buffered upper replacement
together with both lower-contact patches. -/
def combinedSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) : Set PlanePoint :=
  upperSurgeryDomain a epsilon ∪
    (signedLowerPatch a 1 epsilon ∪ signedLowerPatch a (-1) epsilon)

lemma isOpen_combinedSurgeryDomain
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    IsOpen (combinedSurgeryDomain a epsilon) :=
  (isOpen_upperSurgeryDomain a epsilon).union
    ((isOpen_signedLowerPatch a 1 epsilon).union
      (isOpen_signedLowerPatch a (-1) epsilon))

/-- A single internally positive scale controls the upper splice and both
lower contacts on every nonsemicircular branch. -/
def combinedSafeScale
    {lam : ℝ} (a : TypeThreeAssembly lam) : ℝ :=
  min (lowerSafeScale a) (upperSafeScale a)

lemma combinedSafeScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    0 < combinedSafeScale a := by
  rw [combinedSafeScale, lt_min_iff]
  exact ⟨lowerSafeScale_pos a hh, upperSafeScale_pos a⟩

lemma combinedSafeScale_le_lower
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    combinedSafeScale a ≤ lowerSafeScale a :=
  min_le_left _ _

lemma combinedSafeScale_le_upper
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    combinedSafeScale a ≤ upperSafeScale a :=
  min_le_right _ _

lemma combinedSurgeryDomain_symmDiff_interior_subset
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    combinedSurgeryDomain a epsilon ∆ interior a.carrier ⊆
      upperOuterBand epsilon ∪
        (signedLowerPatchWindow a 1 epsilon ∪
          signedLowerPatchWindow a (-1) epsilon) := by
  intro p hp
  have hupper :=
    upperSurgeryDomain_symmDiff_interior_subset_outerBand a hepsilon
  simp only [combinedSurgeryDomain, Set.mem_symmDiff, Set.mem_union] at hp
  rcases hp with hp | hp
  · rcases hp.1 with hupperDomain | hright | hleft
    · exact Or.inl (hupper (Or.inl ⟨hupperDomain, hp.2⟩))
    · exact Or.inr (Or.inl hright.2)
    · exact Or.inr (Or.inr hleft.2)
  · exact Or.inl (hupper (Or.inr ⟨hp.1, fun hupperDomain =>
      hp.2 (Or.inl hupperDomain)⟩))


/-- The complete change is the upper replacement change plus the two explicit
lower windows.  This sharper inclusion keeps the upper term horizontally
bounded through its already proved estimate. -/
lemma combinedSurgeryDomain_symmDiff_interior_subset_upperDiff_union_lower
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) :
    combinedSurgeryDomain a epsilon ∆ interior a.carrier ⊆
      (upperSurgeryDomain a epsilon ∆ interior a.carrier) ∪
        (signedLowerPatchWindow a 1 epsilon ∪
          signedLowerPatchWindow a (-1) epsilon) := by
  intro p hp
  simp only [combinedSurgeryDomain, signedLowerPatch, Set.mem_symmDiff,
    Set.mem_union, Set.mem_inter_iff] at hp ⊢
  rcases hp with hp | hp
  · rcases hp.1 with hu | hr | hl
    · exact Or.inl (Or.inl ⟨hu, hp.2⟩)
    · exact Or.inr (Or.inl hr.2)
    · exact Or.inr (Or.inr hl.2)
  · exact Or.inl (Or.inr ⟨hp.1, fun hu => hp.2 (Or.inl hu)⟩)

theorem characteristicDistance_combinedSurgeryDomain_carrier_le
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (_hepsilon_lower : epsilon ≤ lowerSafeScale a)
    (hepsilon_upper : epsilon ≤ upperSafeScale a) :
    characteristicDistance (combinedSurgeryDomain a epsilon) a.carrier ≤
      ENNReal.ofReal ((4 * upperHorizontalRadius a + 4) * epsilon) := by
  rw [← characteristicDistance_congr_ae
    (combinedSurgeryDomain a epsilon) (interior_carrier_ae_eq_carrier a)]
  unfold characteristicDistance
  have hupper := characteristicDistance_upperSurgeryDomain_interior_le
    a hepsilon hepsilon_upper
  change volume (upperSurgeryDomain a epsilon ∆ interior a.carrier) ≤
    ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) at hupper
  calc
    volume (combinedSurgeryDomain a epsilon ∆ interior a.carrier) ≤
        volume ((upperSurgeryDomain a epsilon ∆ interior a.carrier) ∪
          (signedLowerPatchWindow a 1 epsilon ∪
            signedLowerPatchWindow a (-1) epsilon)) :=
      measure_mono
        (combinedSurgeryDomain_symmDiff_interior_subset_upperDiff_union_lower
          a epsilon)
    _ ≤ volume (upperSurgeryDomain a epsilon ∆ interior a.carrier) +
        volume (signedLowerPatchWindow a 1 epsilon ∪
          signedLowerPatchWindow a (-1) epsilon) :=
      measure_union_le _ _
    _ ≤ volume (upperSurgeryDomain a epsilon ∆ interior a.carrier) +
        (volume (signedLowerPatchWindow a 1 epsilon) +
          volume (signedLowerPatchWindow a (-1) epsilon)) := by
      gcongr
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) +
        (ENNReal.ofReal (2 * epsilon) + ENNReal.ofReal (2 * epsilon)) := by
      exact add_le_add hupper
        (add_le_add
          (volume_signedLowerPatchWindow a 1 hepsilon.le (Or.inl rfl)).le
          (volume_signedLowerPatchWindow a (-1) hepsilon.le
            (Or.inr rfl)).le)
    _ = ENNReal.ofReal ((4 * upperHorizontalRadius a + 4) * epsilon) := by
      have htwo : 0 ≤ 2 * epsilon := mul_nonneg (by norm_num) hepsilon.le
      have hupperReal : 0 ≤ 4 * upperHorizontalRadius a * epsilon :=
        mul_nonneg
          (mul_nonneg (by norm_num) (upperHorizontalRadius_pos a).le)
          hepsilon.le
      calc
        ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) +
            (ENNReal.ofReal (2 * epsilon) + ENNReal.ofReal (2 * epsilon)) =
          ENNReal.ofReal (4 * upperHorizontalRadius a * epsilon) +
            ENNReal.ofReal (2 * epsilon + 2 * epsilon) := by
              rw [ENNReal.ofReal_add htwo htwo]
        _ = ENNReal.ofReal
            (4 * upperHorizontalRadius a * epsilon +
              (2 * epsilon + 2 * epsilon)) :=
          (ENNReal.ofReal_add hupperReal (add_nonneg htwo htwo)).symm
        _ = ENNReal.ofReal
            ((4 * upperHorizontalRadius a + 4) * epsilon) := by
          congr 1
          ring

/-- Common shrinking scale for the complete nondegenerate surgery. -/
def combinedRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) : ℝ :=
  combinedSafeScale a / ((n : ℝ) + 1)

lemma combinedRecoveryScale_pos
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) (n : ℕ) :
    0 < combinedRecoveryScale a n :=
  div_pos (combinedSafeScale_pos a hh) (by positivity)

lemma combinedRecoveryScale_le
    {lam : ℝ} (a : TypeThreeAssembly lam) (n : ℕ) :
    combinedRecoveryScale a n ≤ combinedSafeScale a := by
  unfold combinedRecoveryScale
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hs : 0 ≤ combinedSafeScale a := by
    have hlower : 0 ≤ lowerSafeScale a := by
      unfold lowerSafeScale
      exact le_min
        (div_nonneg a.sideHalfWidth_nonneg (by norm_num))
        (le_min (div_nonneg a.radius_pos.le (by norm_num)) (by norm_num))
    exact le_min hlower (upperSafeScale_pos a).le
  nlinarith

lemma tendsto_combinedRecoveryScale
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    Tendsto (combinedRecoveryScale a) atTop (𝓝 0) := by
  unfold combinedRecoveryScale
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)

/-- The branch-complete geometric surgery converges to the literal carrier on
both open branches.  Establishing `IsSmoothDomain` globally at the unchanged
arc pieces remains the next gluing obligation. -/
theorem tendsto_characteristicDistance_combinedSurgeryDomain_carrier
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    Tendsto
      (fun n => characteristicDistance
        (combinedSurgeryDomain a (combinedRecoveryScale a n)) a.carrier)
      atTop (𝓝 0) := by
  have hbound : Tendsto
      (fun n : ℕ => ENNReal.ofReal
        ((4 * upperHorizontalRadius a + 4) * combinedRecoveryScale a n))
      atTop (𝓝 0) := by
    have hreal : Tendsto
        (fun n : ℕ =>
          (4 * upperHorizontalRadius a + 4) * combinedRecoveryScale a n)
        atTop (𝓝 ((4 * upperHorizontalRadius a + 4) * 0)) :=
      tendsto_const_nhds.mul (tendsto_combinedRecoveryScale a)
    simpa using ENNReal.tendsto_ofReal hreal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun n =>
      characteristicDistance_combinedSurgeryDomain_carrier_le a
        (combinedRecoveryScale_pos a hh n)
        ((combinedRecoveryScale_le a n).trans (combinedSafeScale_le_lower a))
        ((combinedRecoveryScale_le a n).trans (combinedSafeScale_le_upper a)))



end CMVRelaxation.TypeThreeRecovery
