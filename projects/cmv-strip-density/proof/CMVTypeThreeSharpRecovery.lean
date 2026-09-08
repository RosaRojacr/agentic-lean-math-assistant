/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVTypeThreeSmoothRecovery

/-!
# Sharp recovery for actual type-(iii) assemblies

This module bounds the moving upper and lower surgery traces by `O(epsilon)`.
It then charges the unchanged literal frontier at its original weighted cost.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff BigOperators

noncomputable section

namespace CMVRelaxation.TypeThreeRecovery

lemma upperNormalizedQ_eq_smoothTransition
    {lam : ℝ} (a : TypeThreeAssembly lam) {epsilon t : ℝ}
    (hepsilon : 0 < epsilon) :
    upperNormalizedQ a epsilon t =
      upperSideSquare a (upperJunctionHeight epsilon t) +
        Real.smoothTransition t *
          (upperCapSquare a (upperJunctionHeight epsilon t) -
            upperSideSquare a (upperJunctionHeight epsilon t)) := by
  unfold upperNormalizedQ upperBlendQ upperJunctionWeight
  rw [show
      (upperJunctionHeight epsilon t - (1 - epsilon)) / epsilon = t by
    unfold upperJunctionHeight
    field_simp [hepsilon.ne']
    ring]

/-- The normalized upper squared width has a Lipschitz constant proportional
 to the physical collar scale.  Equality of the side and cap widths at `y = 1`
 removes the apparent fixed-size cutoff term. -/
theorem exists_scaled_upperNormalizedQ_lipschitz
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
      epsilon ≤ upperSafeScale a →
      LipschitzOnWith (K * epsilon.toNNReal)
        (upperNormalizedQ a epsilon) (Icc (0 : ℝ) 1) := by
  let I : Set ℝ := Icc (1 - upperSafeScale a) 1
  have hsmoothSideInf : ContDiffOn ℝ ∞ (upperSideSquare a) I := by
    apply (contDiffOn_upperSideSquare a).mono
    intro y hy
    dsimp [I] at hy ⊢
    constructor <;> linarith [hy.1, hy.2, upperSafeScale_pos a]
  have hsmoothSide : ContDiffOn ℝ 1 (upperSideSquare a) I :=
    hsmoothSideInf.of_le (by simp)
  rcases hsmoothSide.exists_lipschitzOnWith (by norm_num)
      (convex_Icc _ _) isCompact_Icc with ⟨Ks, hKs⟩
  have hsmoothCap : ContDiffOn ℝ 1 (upperCapSquare a) I :=
    ((contDiff_upperCapSquare a).of_le (by simp)).contDiffOn
  rcases hsmoothCap.exists_lipschitzOnWith (by norm_num)
      (convex_Icc _ _) isCompact_Icc with ⟨Kc, hKc⟩
  have hsmoothWeightInf : ContDiffOn ℝ ∞ Real.smoothTransition
      (Icc (0 : ℝ) 1) :=
    Real.smoothTransition.contDiff.contDiffOn
  have hsmoothWeight : ContDiffOn ℝ 1 Real.smoothTransition (Icc (0 : ℝ) 1) :=
    hsmoothWeightInf.of_le (by simp)
  rcases hsmoothWeight.exists_lipschitzOnWith (by norm_num)
      (convex_Icc _ _) isCompact_Icc with ⟨Kw, hKw⟩
  let C : ℝ :=
    (Ks : ℝ) + ((Kc : ℝ) + (Ks : ℝ)) +
      (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨⟨C, hC⟩, ?_⟩
  intro epsilon hepsilon hepsilon_le
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  let yt := upperJunctionHeight epsilon t
  let yu := upperJunctionHeight epsilon u
  have hyt : yt ∈ I := by
    dsimp [I, yt, upperJunctionHeight]
    constructor
    · nlinarith [ht.1, hepsilon_le]
    · nlinarith [ht.2, hepsilon]
  have hyu : yu ∈ I := by
    dsimp [I, yu, upperJunctionHeight]
    constructor
    · nlinarith [hu.1, hepsilon_le]
    · nlinarith [hu.2, hepsilon]
  have hydist : |yt - yu| = epsilon * |t - u| := by
    dsimp [yt, yu, upperJunctionHeight]
    rw [show
        (1 - epsilon + epsilon * t) -
            (1 - epsilon + epsilon * u) = epsilon * (t - u) by ring,
      abs_mul, abs_of_pos hepsilon]
  have hside :
      |upperSideSquare a yt - upperSideSquare a yu| ≤
        (Ks : ℝ) * (epsilon * |t - u|) := by
    have h := hKs.dist_le_mul yt hyt yu hyu
    simpa only [Real.dist_eq, hydist] using h
  have hcap :
      |upperCapSquare a yt - upperCapSquare a yu| ≤
        (Kc : ℝ) * (epsilon * |t - u|) := by
    have h := hKc.dist_le_mul yt hyt yu hyu
    simpa only [Real.dist_eq, hydist] using h
  have hgapDiff :
      |(upperCapSquare a yt - upperSideSquare a yt) -
        (upperCapSquare a yu - upperSideSquare a yu)| ≤
          ((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|) := by
    calc
      |(upperCapSquare a yt - upperSideSquare a yt) -
          (upperCapSquare a yu - upperSideSquare a yu)| =
          |(upperCapSquare a yt - upperCapSquare a yu) -
            (upperSideSquare a yt - upperSideSquare a yu)| := by
              congr 1
              ring
      _ ≤ |upperCapSquare a yt - upperCapSquare a yu| +
          |upperSideSquare a yt - upperSideSquare a yu| := abs_sub _ _
      _ ≤ (Kc : ℝ) * (epsilon * |t - u|) +
          (Ks : ℝ) * (epsilon * |t - u|) := add_le_add hcap hside
      _ = ((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|) := by ring
  have hyuOne : |yu - 1| ≤ epsilon := by
    dsimp [yu, upperJunctionHeight]
    rw [abs_le]
    constructor <;> nlinarith [hu.1, hu.2]
  have hOneI : (1 : ℝ) ∈ I := by
    dsimp [I]
    constructor <;> linarith [upperSafeScale_pos a]
  have hcOne := hKc.dist_le_mul yu hyu 1 hOneI
  have hsOne := hKs.dist_le_mul yu hyu 1 hOneI
  have hgapU :
      |upperCapSquare a yu - upperSideSquare a yu| ≤
        ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by
    calc
      |upperCapSquare a yu - upperSideSquare a yu| =
          |(upperCapSquare a yu - upperCapSquare a 1) -
            (upperSideSquare a yu - upperSideSquare a 1)| := by
              rw [upperCapSquare_one a, upperSideSquare_one a]
              congr 1
              ring
      _ ≤ |upperCapSquare a yu - upperCapSquare a 1| +
          |upperSideSquare a yu - upperSideSquare a 1| := abs_sub _ _
      _ ≤ (Kc : ℝ) * |yu - 1| + (Ks : ℝ) * |yu - 1| := by
        simpa only [Real.dist_eq] using add_le_add hcOne hsOne
      _ ≤ (Kc : ℝ) * epsilon + (Ks : ℝ) * epsilon := by gcongr
      _ = ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by ring
  let wt := Real.smoothTransition t
  let wu := Real.smoothTransition u
  have hwt : |wt| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hweight : |wt - wu| ≤ (Kw : ℝ) * |t - u| := by
    have h := hKw.dist_le_mul t ht u hu
    simpa only [Real.dist_eq, wt, wu] using h
  have hproduct :
      |wt * (upperCapSquare a yt - upperSideSquare a yt) -
        wu * (upperCapSquare a yu - upperSideSquare a yu)| ≤
        (((Kc : ℝ) + (Ks : ℝ)) +
          (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
            (epsilon * |t - u|) := by
    calc
      |wt * (upperCapSquare a yt - upperSideSquare a yt) -
          wu * (upperCapSquare a yu - upperSideSquare a yu)| =
          |wt * ((upperCapSquare a yt - upperSideSquare a yt) -
              (upperCapSquare a yu - upperSideSquare a yu)) +
            (wt - wu) *
              (upperCapSquare a yu - upperSideSquare a yu)| := by
                congr 1
                ring
      _ ≤ |wt * ((upperCapSquare a yt - upperSideSquare a yt) -
              (upperCapSquare a yu - upperSideSquare a yu))| +
            |(wt - wu) *
              (upperCapSquare a yu - upperSideSquare a yu)| := abs_add_le _ _
      _ = |wt| *
            |(upperCapSquare a yt - upperSideSquare a yt) -
              (upperCapSquare a yu - upperSideSquare a yu)| +
          |wt - wu| *
            |upperCapSquare a yu - upperSideSquare a yu| := by
              rw [abs_mul, abs_mul]
      _ ≤ 1 * (((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|)) +
          ((Kw : ℝ) * |t - u|) *
            (((Kc : ℝ) + (Ks : ℝ)) * epsilon) := by gcongr
      _ = (((Kc : ℝ) + (Ks : ℝ)) +
          (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
            (epsilon * |t - u|) := by ring
  have hq :
      |upperNormalizedQ a epsilon t - upperNormalizedQ a epsilon u| ≤
        C * (epsilon * |t - u|) := by
    rw [upperNormalizedQ_eq_smoothTransition a hepsilon,
      upperNormalizedQ_eq_smoothTransition a hepsilon]
    change
      |upperSideSquare a yt + wt *
          (upperCapSquare a yt - upperSideSquare a yt) -
        (upperSideSquare a yu + wu *
          (upperCapSquare a yu - upperSideSquare a yu))| ≤ _
    calc
      _ = |(upperSideSquare a yt - upperSideSquare a yu) +
            (wt * (upperCapSquare a yt - upperSideSquare a yt) -
              wu * (upperCapSquare a yu - upperSideSquare a yu))| := by
                congr 1
                ring
      _ ≤ |upperSideSquare a yt - upperSideSquare a yu| +
          |wt * (upperCapSquare a yt - upperSideSquare a yt) -
            wu * (upperCapSquare a yu - upperSideSquare a yu)| := abs_add_le _ _
      _ ≤ (Ks : ℝ) * (epsilon * |t - u|) +
          (((Kc : ℝ) + (Ks : ℝ)) +
            (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
              (epsilon * |t - u|) := add_le_add hside hproduct
      _ = C * (epsilon * |t - u|) := by
        dsimp [C]
        ring
  calc
    dist (upperNormalizedQ a epsilon t) (upperNormalizedQ a epsilon u) =
        |upperNormalizedQ a epsilon t - upperNormalizedQ a epsilon u| :=
      Real.dist_eq _ _
    _ ≤ C * (epsilon * |t - u|) := hq
    _ = ((⟨C, hC⟩ : ℝ≥0) * epsilon.toNNReal : ℝ) * dist t u := by
      change C * (epsilon * |t - u|) =
        C * (epsilon.toNNReal : ℝ) * dist t u
      rw [Real.coe_toNNReal epsilon hepsilon.le, Real.dist_eq]
      ring

private lemma dist_sqrt_le_abs_sub_div
    {w x y : ℝ} (hw : 0 < w) (hx : w ^ 2 ≤ x) (hy : w ^ 2 ≤ y) :
    dist (√x) (√y) ≤ |x - y| / w := by
  have hx0 : 0 ≤ x := le_trans (sq_nonneg w) hx
  have hy0 : 0 ≤ y := le_trans (sq_nonneg w) hy
  have hsx : w ≤ √x := Real.le_sqrt_of_sq_le hx
  have hsy : w ≤ √y := Real.le_sqrt_of_sq_le hy
  have hsum : w ≤ |√x + √y| := by
    rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith
  have hidentity : |√x - √y| * |√x + √y| = |x - y| := by
    rw [← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt hy0]
  rw [Real.dist_eq]
  apply (le_div_iff₀ hw).2
  calc
    |√x - √y| * w ≤ |√x - √y| * |√x + √y| :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |x - y| := hidentity

/-- Each of the two actual upper branches has Euclidean Lipschitz constant
 proportional to the collar scale. -/
theorem exists_scaled_signedUpperContactTrace_lipschitz
    {lam : ℝ} (a : TypeThreeAssembly lam) {horizontalSign : ℝ}
    (hsign : |horizontalSign| = 1) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
      epsilon ≤ upperSafeScale a →
      LipschitzOnWith (K * epsilon.toNNReal)
        (fun t : ℝ => planeEuclideanHomeomorph
          (signedUpperContactTrace a horizontalSign epsilon t))
        (Icc (0 : ℝ) 1) := by
  rcases exists_scaled_upperNormalizedQ_lipschitz a with ⟨Kq, hKq⟩
  let w : ℝ≥0 := ⟨upperAttachmentWidth a / 2,
    (div_nonneg (upperAttachmentWidth_pos a).le (by norm_num))⟩
  have hw : 0 < (w : ℝ) := div_pos (upperAttachmentWidth_pos a) (by norm_num)
  refine ⟨Kq / w + 1, ?_⟩
  intro epsilon hepsilon hepsilon_le
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  let qt := upperNormalizedQ a epsilon t
  let qu := upperNormalizedQ a epsilon u
  have hqt : (w : ℝ) ^ 2 ≤ qt := by
    change (upperAttachmentWidth a / 2) ^ 2 ≤
      upperNormalizedQ a epsilon t
    have h := upperNormalizedQ_lower a hepsilon hepsilon_le ht
    nlinarith [sq_nonneg (upperAttachmentWidth a)]
  have hqu : (w : ℝ) ^ 2 ≤ qu := by
    change (upperAttachmentWidth a / 2) ^ 2 ≤
      upperNormalizedQ a epsilon u
    have h := upperNormalizedQ_lower a hepsilon hepsilon_le hu
    nlinarith [sq_nonneg (upperAttachmentWidth a)]
  have hqdist :
      dist qt qu ≤ ((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u :=
    (hKq hepsilon hepsilon_le).dist_le_mul t ht u hu
  have hsqrt :
      dist (√qt) (√qu) ≤
        (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
    calc
      dist (√qt) (√qu) ≤ |qt - qu| / (w : ℝ) :=
        dist_sqrt_le_abs_sub_div hw hqt hqu
      _ ≤ (((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u) /
          (w : ℝ) := by
        exact (div_le_div_iff_of_pos_right hw).2
          (by simpa only [Real.dist_eq] using hqdist)
      _ = (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
        change ((Kq : ℝ) * (epsilon.toNNReal : ℝ) * dist t u) / (w : ℝ) =
          (((Kq : ℝ) / (w : ℝ)) * (epsilon.toNNReal : ℝ)) * dist t u
        field_simp [ne_of_gt hw]
  have hx :
      dist (horizontalSign * √qt) (horizontalSign * √qu) ≤
        (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
    rw [Real.dist_eq, show horizontalSign * √qt - horizontalSign * √qu =
      horizontalSign * (√qt - √qu) by ring, abs_mul, hsign, one_mul]
    simpa only [Real.dist_eq] using hsqrt
  have hy :
      dist (upperJunctionHeight epsilon t) (upperJunctionHeight epsilon u) =
        epsilon * dist t u := by
    rw [Real.dist_eq, Real.dist_eq, show
      upperJunctionHeight epsilon t - upperJunctionHeight epsilon u =
        epsilon * (t - u) by unfold upperJunctionHeight; ring,
      abs_mul, abs_of_pos hepsilon]
  calc
    dist (planeEuclideanHomeomorph
          (signedUpperContactTrace a horizontalSign epsilon t))
        (planeEuclideanHomeomorph
          (signedUpperContactTrace a horizontalSign epsilon u)) ≤
        dist (horizontalSign * √qt) (horizontalSign * √qu) +
          dist (upperJunctionHeight epsilon t)
            (upperJunctionHeight epsilon u) := by
      apply FrozenSquaredRecovery.dist_planeEuclideanHomeomorph_le
    _ ≤ (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u +
        epsilon * dist t u := add_le_add hx hy.le
    _ = ((((Kq / w) + 1) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
      simp only [NNReal.coe_mul, NNReal.coe_add,
        Real.coe_toNNReal epsilon hepsilon.le, NNReal.coe_one]
      ring

/-- The two reflected moving upper traces. -/
def upperReplacementTrace
    {lam : ℝ} (a : TypeThreeAssembly lam) (epsilon : ℝ) : Set EuclideanPlane :=
  (fun t : ℝ => planeEuclideanHomeomorph
      (signedUpperContactTrace a 1 epsilon t)) '' Icc (0 : ℝ) 1 ∪
    (fun t : ℝ => planeEuclideanHomeomorph
      (signedUpperContactTrace a (-1) epsilon t)) '' Icc (0 : ℝ) 1

/-- The complete upper replacement trace has Euclidean `H¹` bounded by one
 finite assembly-dependent coefficient times `epsilon`. -/
theorem exists_scaled_upperReplacementTrace_hausdorffMeasure
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ upperSafeScale a →
        (μH[1] : Measure EuclideanPlane) (upperReplacementTrace a epsilon) ≤
          C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_signedUpperContactTrace_lipschitz a
      (horizontalSign := (1 : ℝ)) (by norm_num) with ⟨Kr, hKr⟩
  rcases exists_scaled_signedUpperContactTrace_lipschitz a
      (horizontalSign := (-1 : ℝ)) (by norm_num) with ⟨Kl, hKl⟩
  let C : ℝ≥0∞ := (Kr : ℝ≥0∞) + (Kl : ℝ≥0∞)
  refine ⟨C, (ENNReal.add_lt_top).2
    ⟨ENNReal.coe_lt_top, ENNReal.coe_lt_top⟩, ?_⟩
  intro epsilon hepsilon hepsilon_le
  have hr := (hKr hepsilon hepsilon_le).hausdorffMeasure_image_le
    (d := (1 : ℝ)) (by norm_num)
  have hl := (hKl hepsilon hepsilon_le).hausdorffMeasure_image_le
    (d := (1 : ℝ)) (by norm_num)
  calc
    (μH[1] : Measure EuclideanPlane) (upperReplacementTrace a epsilon) ≤
        (μH[1] : Measure EuclideanPlane)
          ((fun t : ℝ => planeEuclideanHomeomorph
            (signedUpperContactTrace a 1 epsilon t)) '' Icc (0 : ℝ) 1) +
        (μH[1] : Measure EuclideanPlane)
          ((fun t : ℝ => planeEuclideanHomeomorph
            (signedUpperContactTrace a (-1) epsilon t)) '' Icc (0 : ℝ) 1) :=
      measure_union_le _ _
    _ ≤ ((Kr * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) +
        ((Kl * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      apply add_le_add
      · simpa [ENNReal.rpow_one, hausdorffMeasure_real,
          Real.volume_Icc] using hr
      · simpa [ENNReal.rpow_one, hausdorffMeasure_real,
          Real.volume_Icc] using hl
    _ = C * (epsilon.toNNReal : ℝ≥0∞) := by
      dsimp [C]
      ring

/-- The upper surgery frontier is either an unchanged literal source-frontier
point or one of the two normalized upper replacement traces. -/
theorem realized_frontier_upperSurgeryDomain_subset
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ upperSafeScale a) :
    planeEuclideanHomeomorph '' frontier (upperSurgeryDomain a epsilon) ⊆
      planeEuclideanHomeomorph '' frontier a.carrier ∪
        upperReplacementTrace a epsilon := by
  rintro _ ⟨p, hpfrontier, rfl⟩
  by_cases hyBelow : p.2 < 1 - epsilon
  · left
    refine ⟨p, ?_, rfl⟩
    have hpPair : p ∈ frontier (upperSurgeryDomain a epsilon) ∩
        belowUpperTransition epsilon := ⟨hpfrontier, hyBelow⟩
    rw [← frontier_inter_open_inter (isOpen_belowUpperTransition epsilon),
      upperSurgeryDomain_eq_interior_belowTransition a hepsilon hepsilon_le,
      frontier_inter_open_inter (isOpen_belowUpperTransition epsilon)] at hpPair
    exact frontier_interior_subset hpPair.1
  · by_cases hyAbove : 1 < p.2
    · left
      refine ⟨p, ?_, rfl⟩
      have hpPair : p ∈ frontier (upperSurgeryDomain a epsilon) ∩
          aboveUpperTransition := ⟨hpfrontier, hyAbove⟩
      rw [← frontier_inter_open_inter isOpen_aboveUpperTransition,
        upperSurgeryDomain_eq_interior_aboveTransition a hepsilon hepsilon_le,
        frontier_inter_open_inter isOpen_aboveUpperTransition] at hpPair
      exact frontier_interior_subset hpPair.1
    · right
      have hyCore : p.2 ∈ Icc (1 - epsilon) 1 :=
        ⟨le_of_not_gt hyBelow, le_of_not_gt hyAbove⟩
      have hpV : p ∈ upperModelNeighborhood epsilon :=
        ⟨by nlinarith [hyCore.1, hepsilon],
          by nlinarith [hyCore.2, hepsilon]⟩
      have hpPair : p ∈ frontier (upperSurgeryDomain a epsilon) ∩
          upperModelNeighborhood epsilon := ⟨hpfrontier, hpV⟩
      rw [← frontier_inter_open_inter (isOpen_upperModelNeighborhood epsilon),
        upperSurgeryDomain_eq_upperBlend_on_modelNeighborhood a hepsilon,
        frontier_inter_open_inter (isOpen_upperModelNeighborhood epsilon)]
        at hpPair
      have hqContinuous : Continuous (upperBlendQ a epsilon) := by
        unfold upperBlendQ upperSideSquare upperSideRadicand upperCapSquare
          TypeThreeAssembly.upperCenter upperJunctionWeight
        fun_prop
      have heq : p.1 ^ 2 = upperBlendQ a epsilon p.2 := by
        apply frontier_lt_subset_eq (continuous_fst.pow 2)
          (hqContinuous.comp continuous_snd)
        simpa [upperBlendDomain] using hpPair.1
      have hqnonneg : 0 ≤ upperBlendQ a epsilon p.2 := by
        rw [← heq]
        positivity
      have hsqrtSq :
          (√(upperBlendQ a epsilon p.2)) ^ 2 =
            upperBlendQ a epsilon p.2 :=
        Real.sq_sqrt hqnonneg
      have hroot :
          p.1 = √(upperBlendQ a epsilon p.2) ∨
            p.1 = -√(upperBlendQ a epsilon p.2) := by
        rw [← hsqrtSq] at heq
        exact (sq_eq_sq_iff_eq_or_eq_neg).mp heq
      let t := (p.2 - (1 - epsilon)) / epsilon
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor
        · exact div_nonneg (sub_nonneg.mpr hyCore.1) hepsilon.le
        · rw [div_le_one hepsilon]
          linarith [hyCore.2]
      have hheight : upperJunctionHeight epsilon t = p.2 := by
        unfold upperJunctionHeight
        dsimp [t]
        field_simp [hepsilon.ne']
        ring
      rcases hroot with hright | hleft
      · apply Or.inl
        refine ⟨t, ht, ?_⟩
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · change 1 * √(upperNormalizedQ a epsilon t) = p.1
          rw [one_mul, upperNormalizedQ, hheight]
          exact hright.symm
        · exact hheight
      · apply Or.inr
        refine ⟨t, ht, ?_⟩
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · change (-1 : ℝ) * √(upperNormalizedQ a epsilon t) = p.1
          rw [upperNormalizedQ, hheight]
          linarith
        · exact hheight

private lemma signedLowerContactTrace_eq_of_graph
    {lam : ℝ} (a : TypeThreeAssembly lam)
    {horizontalSign epsilon : ℝ} (hsign : |horizontalSign| = 1)
    (hepsilon : 0 < epsilon) {p : PlanePoint}
    (heq : lowerContactGraph a epsilon
      (signedLowerOutwardCoordinate a horizontalSign p) = p.2) :
    signedLowerContactTrace a horizontalSign epsilon
        (signedLowerOutwardCoordinate a horizontalSign p / epsilon) = p := by
  let u := signedLowerOutwardCoordinate a horizontalSign p
  have hsignSq : horizontalSign ^ 2 = 1 := by
    calc
      horizontalSign ^ 2 = |horizontalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hsign]; norm_num
  have hepsU : epsilon * (u / epsilon) = u := by
    field_simp [hepsilon.ne']
  have hgraph := lowerContactGraph_scaled a hepsilon (u / epsilon)
  rw [hepsU] at hgraph
  change lowerContactGraph a epsilon u = p.2 at heq
  rw [heq] at hgraph
  apply Prod.ext
  · change horizontalSign *
      (a.sideHalfWidth + epsilon * (u / epsilon)) = p.1
    rw [hepsU]
    dsimp [u]
    unfold signedLowerOutwardCoordinate
    rw [show horizontalSign *
        (a.sideHalfWidth +
          (horizontalSign * p.1 - a.sideHalfWidth)) =
        horizontalSign ^ 2 * p.1 by ring, hsignSq, one_mul]
  · change -1 + lowerContactWeight (u / epsilon) *
      lowerCircleRise a (epsilon * (u / epsilon)) = p.2
    rw [hepsU]
    exact hgraph.symm

/-- Literal frontier domination for the complete nondegenerate surgery.
Window edges create no extra boundary: inside each closed lower change support
the frontier is the replacement graph, and outside both supports it is the
already classified upper-surgery frontier. -/
theorem realized_frontier_combinedSurgeryDomain_subset
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ combinedSafeScale a / 2) :
    planeEuclideanHomeomorph '' frontier (combinedSurgeryDomain a epsilon) ⊆
      planeEuclideanHomeomorph '' frontier a.carrier ∪
        (lowerReplacementTrace a epsilon ∪ upperReplacementTrace a epsilon) := by
  have hepsilon_lower : epsilon ≤ lowerSafeScale a / 2 := by
    have hle := combinedSafeScale_le_lower a
    nlinarith
  have hepsilon_upper : epsilon ≤ upperSafeScale a := by
    have hle := combinedSafeScale_le_upper a
    have hs0 := (combinedSafeScale_pos a hh).le
    nlinarith
  rintro _ ⟨p, hpfrontier, rfl⟩
  by_cases hpRight : p ∈ signedLowerChangeSupport a 1 epsilon
  · right
    left
    apply Or.inl
    let t := signedLowerOutwardCoordinate a 1 p / epsilon
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor
      · exact div_nonneg hpRight.1.1 hepsilon.le
      · rw [div_le_one hepsilon]
        nlinarith [hpRight.1.2, hepsilon]
    refine ⟨t, ht, ?_⟩
    have hpV : p ∈ signedLowerModelNeighborhood a 1 epsilon :=
      signedLowerChangeSupport_subset_modelNeighborhood
        a hepsilon hepsilon_lower hpRight
    have hpPair : p ∈ frontier (combinedSurgeryDomain a epsilon) ∩
        signedLowerModelNeighborhood a 1 epsilon := ⟨hpfrontier, hpV⟩
    rw [← frontier_inter_open_inter
      (isOpen_signedLowerModelNeighborhood a 1 epsilon),
      combinedSurgeryDomain_eq_rightLowerLocal_on_modelNeighborhood
        a hh hepsilon hepsilon_lower hepsilon_upper,
      frontier_inter_open_inter
        (isOpen_signedLowerModelNeighborhood a 1 epsilon)] at hpPair
    have hgraphContinuous : Continuous (fun z : PlanePoint =>
        lowerContactGraph a epsilon
          (signedLowerOutwardCoordinate a 1 z)) := by
      unfold lowerContactGraph lowerContactWeight lowerCircleRise
        signedLowerOutwardCoordinate
      fun_prop
    have heq : lowerContactGraph a epsilon
        (signedLowerOutwardCoordinate a 1 p) = p.2 := by
      apply frontier_lt_subset_eq hgraphContinuous continuous_snd
      simpa [signedLowerLocalDomain] using hpPair.1
    change planeEuclideanHomeomorph
      (signedLowerContactTrace a 1 epsilon t) = planeEuclideanHomeomorph p
    apply congrArg planeEuclideanHomeomorph
    exact signedLowerContactTrace_eq_of_graph a (by norm_num) hepsilon heq
  · by_cases hpLeft : p ∈ signedLowerChangeSupport a (-1) epsilon
    · right
      left
      apply Or.inr
      let t := signedLowerOutwardCoordinate a (-1) p / epsilon
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor
        · exact div_nonneg hpLeft.1.1 hepsilon.le
        · rw [div_le_one hepsilon]
          nlinarith [hpLeft.1.2, hepsilon]
      refine ⟨t, ht, ?_⟩
      have hpV : p ∈ signedLowerModelNeighborhood a (-1) epsilon :=
        signedLowerChangeSupport_subset_modelNeighborhood
          a hepsilon hepsilon_lower hpLeft
      have hpPair : p ∈ frontier (combinedSurgeryDomain a epsilon) ∩
          signedLowerModelNeighborhood a (-1) epsilon := ⟨hpfrontier, hpV⟩
      rw [← frontier_inter_open_inter
        (isOpen_signedLowerModelNeighborhood a (-1) epsilon),
        combinedSurgeryDomain_eq_leftLowerLocal_on_modelNeighborhood
          a hh hepsilon hepsilon_lower hepsilon_upper,
        frontier_inter_open_inter
          (isOpen_signedLowerModelNeighborhood a (-1) epsilon)] at hpPair
      have hgraphContinuous : Continuous (fun z : PlanePoint =>
          lowerContactGraph a epsilon
            (signedLowerOutwardCoordinate a (-1) z)) := by
        unfold lowerContactGraph lowerContactWeight lowerCircleRise
          signedLowerOutwardCoordinate
        fun_prop
      have heq : lowerContactGraph a epsilon
          (signedLowerOutwardCoordinate a (-1) p) = p.2 := by
        apply frontier_lt_subset_eq hgraphContinuous continuous_snd
        simpa [signedLowerLocalDomain] using hpPair.1
      change planeEuclideanHomeomorph
        (signedLowerContactTrace a (-1) epsilon t) = planeEuclideanHomeomorph p
      apply congrArg planeEuclideanHomeomorph
      exact signedLowerContactTrace_eq_of_graph a (by norm_num) hepsilon heq
    · have hpOutside : p ∈ (lowerChangeSupports a epsilon)ᶜ := by
        exact fun hpSupport => hpSupport.elim hpRight hpLeft
      have hlocal :=
        combinedSurgeryDomain_eq_upperSurgeryDomain_off_lowerSupports
          a hh hepsilon hepsilon_lower hepsilon_upper
      have hpPair : p ∈ frontier (combinedSurgeryDomain a epsilon) ∩
          (lowerChangeSupports a epsilon)ᶜ := ⟨hpfrontier, hpOutside⟩
      have hopen : IsOpen ((lowerChangeSupports a epsilon)ᶜ) :=
        (isClosed_lowerChangeSupports a epsilon).isOpen_compl
      rw [← frontier_inter_open_inter hopen, hlocal,
        frontier_inter_open_inter hopen] at hpPair
      rcases realized_frontier_upperSurgeryDomain_subset
          a hepsilon hepsilon_upper ⟨p, hpPair.1, rfl⟩ with hsource | hupper
      · exact Or.inl hsource
      · exact Or.inr (Or.inr hupper)

/-- The lower and upper moving traces together have vanishing Euclidean
`H¹`, with one finite assembly-dependent coefficient. -/
theorem exists_scaled_replacementTrace_hausdorffMeasure
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
        epsilon ≤ lowerSafeScale a → epsilon ≤ upperSafeScale a →
        (μH[1] : Measure EuclideanPlane)
            (lowerReplacementTrace a epsilon ∪ upperReplacementTrace a epsilon) ≤
          C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_lowerReplacementTrace_hausdorffMeasure a with
    ⟨Cl, hCl, hlower⟩
  rcases exists_scaled_upperReplacementTrace_hausdorffMeasure a with
    ⟨Cu, hCu, hupper⟩
  refine ⟨Cl + Cu, (ENNReal.add_lt_top).2 ⟨hCl, hCu⟩, ?_⟩
  intro epsilon hepsilon hepsilon_lower hepsilon_upper
  calc
    (μH[1] : Measure EuclideanPlane)
        (lowerReplacementTrace a epsilon ∪ upperReplacementTrace a epsilon) ≤
      (μH[1] : Measure EuclideanPlane) (lowerReplacementTrace a epsilon) +
        (μH[1] : Measure EuclideanPlane) (upperReplacementTrace a epsilon) :=
      measure_union_le _ _
    _ ≤ Cl * (epsilon.toNNReal : ℝ≥0∞) +
        Cu * (epsilon.toNNReal : ℝ≥0∞) :=
      add_le_add (hlower hepsilon hepsilon_lower)
        (hupper hepsilon hepsilon_upper)
    _ = (Cl + Cu) * (epsilon.toNNReal : ℝ≥0∞) := by ring

/-- The extended nonnegative cost of the literal type-(iii) frontier is the
`ENNReal.ofReal` of its existing real weighted-perimeter integral. -/
theorem extended_frontierCost_eq_smoothCost_assembly
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) =
      smoothCost lam a.carrier := by
  have hlam : 0 ≤ lam := le_trans (by norm_num) a.density_jump.le
  have hnonneg :
      0 ≤ᵐ[FrontierMeasure a.carrier] StripDensity lam :=
    Eventually.of_forall (fun p => by
      unfold StripDensity
      split_ifs
      · norm_num
      · exact hlam)
  unfold _root_.WeightedPerimeter smoothCost
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    a.integrable_frontierMeasure hnonneg

/-- Sharp weighted cost for the complete nondegenerate surgery.  The source
frontier keeps its literal strip density.  The lower replacement is charged at
its proved density one; only the upper replacement uses the exterior bound
`lam`. -/
theorem exists_sharp_smoothCost_combinedSurgeryDomain_bound
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
        epsilon ≤ combinedSafeScale a / 2 →
        smoothCost lam (combinedSurgeryDomain a epsilon) ≤
          ENNReal.ofReal
              (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) +
            C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_lowerReplacementTrace_hausdorffMeasure a with
    ⟨Cl, hCl, hlowerMeasure⟩
  rcases exists_scaled_upperReplacementTrace_hausdorffMeasure a with
    ⟨Cu, hCu, hupperMeasure⟩
  let Λ : ℝ≥0∞ := ENNReal.ofReal lam
  refine ⟨Cl + Λ * Cu, (ENNReal.add_lt_top).2
    ⟨hCl, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCu⟩, ?_⟩
  intro epsilon hepsilon hepsilon_le
  have hepsilon_lower : epsilon ≤ lowerSafeScale a := by
    have hle := combinedSafeScale_le_lower a
    have hs0 := (combinedSafeScale_pos a hh).le
    nlinarith
  have hepsilon_upper : epsilon ≤ upperSafeScale a := by
    have hle := combinedSafeScale_le_upper a
    have hs0 := (combinedSafeScale_pos a hh).le
    nlinarith
  let μ : Measure EuclideanPlane := μH[1]
  let f : EuclideanPlane → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (euclideanStripDensity lam z)
  have hfrontier :
      frontier (planeEuclideanHomeomorph ''
        combinedSurgeryDomain a epsilon) ⊆
      frontier (planeEuclideanHomeomorph '' a.carrier) ∪
        (lowerReplacementTrace a epsilon ∪ upperReplacementTrace a epsilon) := by
    simpa only [planeEuclideanHomeomorph.image_frontier] using
      realized_frontier_combinedSurgeryDomain_subset
        a hh hepsilon hepsilon_le
  have hlowerCost :
      (∫⁻ z in lowerReplacementTrace a epsilon, f z ∂μ) ≤
        μ (lowerReplacementTrace a epsilon) := by
    calc
      (∫⁻ z in lowerReplacementTrace a epsilon, f z ∂μ) ≤
          ∫⁻ _z in lowerReplacementTrace a epsilon, (1 : ℝ≥0∞) ∂μ := by
        apply MeasureTheory.setLIntegral_mono measurable_const
        intro z hz
        rcases hz with hz | hz
        · rcases hz with ⟨t, ht, rfl⟩
          dsimp [f, euclideanStripDensity]
          rw [signedLowerContactTrace_one,
            stripDensity_rightLowerContactTrace a hepsilon
              hepsilon_lower ht]
          norm_num
        · rcases hz with ⟨t, ht, rfl⟩
          dsimp [f, euclideanStripDensity]
          rw [signedLowerContactTrace_neg_one,
            stripDensity_leftLowerContactTrace a hepsilon
              hepsilon_lower ht]
          norm_num
      _ = μ (lowerReplacementTrace a epsilon) := by simp
  have hupperCost :
      (∫⁻ z in upperReplacementTrace a epsilon, f z ∂μ) ≤
        Λ * μ (upperReplacementTrace a epsilon) := by
    calc
      (∫⁻ z in upperReplacementTrace a epsilon, f z ∂μ) ≤
          ∫⁻ _z in upperReplacementTrace a epsilon, Λ ∂μ := by
        apply MeasureTheory.setLIntegral_mono measurable_const
        intro z _hz
        dsimp [f, Λ, euclideanStripDensity]
        unfold StripDensity
        split_ifs
        · exact ENNReal.ofReal_le_ofReal a.density_jump.le
        · exact le_rfl
      _ = Λ * μ (upperReplacementTrace a epsilon) := by simp
  have hlowerMeasure :
      μ (lowerReplacementTrace a epsilon) ≤
        Cl * (epsilon.toNNReal : ℝ≥0∞) := by
    simpa only [μ] using hlowerMeasure hepsilon hepsilon_lower
  have hupperMeasure :
      μ (upperReplacementTrace a epsilon) ≤
        Cu * (epsilon.toNNReal : ℝ≥0∞) := by
    simpa only [μ] using hupperMeasure hepsilon hepsilon_upper
  rw [FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral]
  change (∫⁻ z in frontier
      (planeEuclideanHomeomorph '' combinedSurgeryDomain a epsilon), f z ∂μ) ≤ _
  calc
    (∫⁻ z in frontier
        (planeEuclideanHomeomorph '' combinedSurgeryDomain a epsilon), f z ∂μ) ≤
      ∫⁻ z in frontier (planeEuclideanHomeomorph '' a.carrier) ∪
          (lowerReplacementTrace a epsilon ∪ upperReplacementTrace a epsilon),
        f z ∂μ :=
      MeasureTheory.lintegral_mono_set hfrontier
    _ ≤ (∫⁻ z in frontier (planeEuclideanHomeomorph '' a.carrier), f z ∂μ) +
        ∫⁻ z in lowerReplacementTrace a epsilon ∪ upperReplacementTrace a epsilon,
          f z ∂μ :=
      MeasureTheory.lintegral_union_le _ _ _
    _ ≤ (∫⁻ z in frontier (planeEuclideanHomeomorph '' a.carrier), f z ∂μ) +
        ((∫⁻ z in lowerReplacementTrace a epsilon, f z ∂μ) +
          ∫⁻ z in upperReplacementTrace a epsilon, f z ∂μ) := by
      apply add_le_add le_rfl
      exact MeasureTheory.lintegral_union_le _ _ _
    _ ≤ smoothCost lam a.carrier +
        (μ (lowerReplacementTrace a epsilon) +
          Λ * μ (upperReplacementTrace a epsilon)) := by
      rw [FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral]
      exact add_le_add le_rfl (add_le_add hlowerCost hupperCost)
    _ = ENNReal.ofReal
          (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) +
        (μ (lowerReplacementTrace a epsilon) +
          Λ * μ (upperReplacementTrace a epsilon)) := by
      rw [extended_frontierCost_eq_smoothCost_assembly a]
    _ ≤ ENNReal.ofReal
          (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) +
        (Cl * (epsilon.toNNReal : ℝ≥0∞) +
          Λ * (Cu * (epsilon.toNNReal : ℝ≥0∞))) := by
      gcongr
    _ = ENNReal.ofReal
          (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) +
        (Cl + Λ * Cu) * (epsilon.toNNReal : ℝ≥0∞) := by ring

/-- The actual nondegenerate recovery sequence has liminf cost no larger than
the literal complete-frontier weighted perimeter. -/
theorem nondegenerateRecoverySequence_cost_le_frontierCost
    {lam : ℝ} (a : TypeThreeAssembly lam) (hh : a.h ≠ 1 / 2) :
    (nondegenerateRecoverySequence a hh).cost lam ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) := by
  rcases exists_sharp_smoothCost_combinedSurgeryDomain_bound a hh with
    ⟨C, hC, hbound⟩
  let P : ℝ≥0∞ := ENNReal.ofReal
    (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier))
  have hpoint : ∀ n : ℕ,
      smoothCost lam ((nondegenerateRecoverySequence a hh).carrier n) ≤
        P + C * ((smoothCombinedRecoveryScale a n).toNNReal : ℝ≥0∞) := by
    intro n
    simpa only [nondegenerateRecoverySequence, P] using
      hbound (smoothCombinedRecoveryScale_pos a hh n)
        (smoothCombinedRecoveryScale_le a n)
  have hscalePoint (n : ℕ) :
      ((smoothCombinedRecoveryScale a n).toNNReal : ℝ≥0∞) =
        ENNReal.ofReal (smoothCombinedRecoveryScale a n) := by
    rw [ENNReal.ofReal_eq_coe_nnreal
      (smoothCombinedRecoveryScale_pos a hh n).le]
    congr 1
    ext
    exact congrArg (fun x : ℝ≥0 => (x : ℝ))
      (Real.toNNReal_of_nonneg
        (smoothCombinedRecoveryScale_pos a hh n).le)
  have hscale :
      Tendsto
        (fun n : ℕ =>
          ((smoothCombinedRecoveryScale a n).toNNReal : ℝ≥0∞))
        atTop (𝓝 0) := by
    simpa only [hscalePoint, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_smoothCombinedRecoveryScale a)
  have herror :
      Tendsto (fun n : ℕ =>
        C * ((smoothCombinedRecoveryScale a n).toNNReal : ℝ≥0∞))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hscale (Or.inr hC.ne)
  unfold SmoothSequence.cost
  change liminf (fun n =>
    smoothCost lam ((nondegenerateRecoverySequence a hh).carrier n)) atTop ≤ _
  calc
    liminf (fun n =>
        smoothCost lam ((nondegenerateRecoverySequence a hh).carrier n))
        atTop ≤
      liminf (fun n => P +
        C * ((smoothCombinedRecoveryScale a n).toNNReal : ℝ≥0∞)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hpoint)
    _ = liminf (fun _n : ℕ => P) atTop :=
      ENNReal.liminf_add_of_right_tendsto_zero herror (fun _n : ℕ => P)
    _ = P := by simp
    _ = ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure a.carrier)) := rfl



/-- Euclidean center of the placed radius-two semicircular branch. -/
private def semicircularDiskCenter : EuclideanPlane :=
  planeEuclideanHomeomorph (0, 1)

private theorem dist_semicircularDiskCenter_sq (p : PlanePoint) :
    dist (planeEuclideanHomeomorph p) semicircularDiskCenter ^ 2 =
      p.1 ^ 2 + (p.2 - 1) ^ 2 := by
  rw [WithLp.prod_dist_eq_add (by norm_num)]
  norm_num [semicircularDiskCenter, Real.dist_eq, sq_abs]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

/-- The smooth representative of the degenerate branch is literally the
Euclidean radius-two open ball at the assembly's placement. -/
theorem semicircularOpenDisk_euclidean_image :
    planeEuclideanHomeomorph '' semicircularOpenDisk =
      Metric.ball semicircularDiskCenter 2 := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp, rfl⟩
    rw [Metric.mem_ball, ← sq_lt_sq₀
      (dist_nonneg : 0 ≤ dist (planeEuclideanHomeomorph p)
        semicircularDiskCenter) (by norm_num : (0 : ℝ) ≤ 2),
      dist_semicircularDiskCenter_sq]
    norm_num
    simpa using (mem_semicircularOpenDisk p).1 hp
  · intro z hz
    obtain ⟨p, rfl⟩ := planeEuclideanHomeomorph.surjective z
    refine ⟨p, ?_, rfl⟩
    rw [Metric.mem_ball] at hz
    rw [mem_semicircularOpenDisk]
    rw [← dist_semicircularDiskCenter_sq]
    have hd0 : 0 ≤ dist (planeEuclideanHomeomorph p)
        semicircularDiskCenter := dist_nonneg
    nlinarith

/-- The literal closed representative of the degenerate branch is the
corresponding Euclidean closed ball. -/
theorem semicircularClosedDisk_euclidean_image :
    planeEuclideanHomeomorph '' semicircularClosedDisk =
      Metric.closedBall semicircularDiskCenter 2 := by
  apply Set.Subset.antisymm
  · rintro z ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, ← sq_le_sq₀
      (dist_nonneg : 0 ≤ dist (planeEuclideanHomeomorph p)
        semicircularDiskCenter) (by norm_num : (0 : ℝ) ≤ 2),
      dist_semicircularDiskCenter_sq]
    norm_num
    simpa using (mem_semicircularClosedDisk p).1 hp
  · intro z hz
    obtain ⟨p, rfl⟩ := planeEuclideanHomeomorph.surjective z
    refine ⟨p, ?_, rfl⟩
    rw [Metric.mem_closedBall] at hz
    rw [mem_semicircularClosedDisk]
    rw [← dist_semicircularDiskCenter_sq]
    have hd0 : 0 ≤ dist (planeEuclideanHomeomorph p)
        semicircularDiskCenter := dist_nonneg
    nlinarith

/-- Open and closed representatives of the semicircular branch have exactly
the same complete frontier, not merely the same area class. -/
theorem frontier_semicircularOpenDisk_euclidean_eq_closed :
    frontier (planeEuclideanHomeomorph '' semicircularOpenDisk) =
      frontier (planeEuclideanHomeomorph '' semicircularClosedDisk) := by
  rw [semicircularOpenDisk_euclidean_image,
    semicircularClosedDisk_euclidean_image,
    frontier_ball semicircularDiskCenter (by norm_num : (2 : ℝ) ≠ 0),
    frontier_closedBall semicircularDiskCenter
      (by norm_num : (2 : ℝ) ≠ 0)]

/-- The constant smooth disk has exactly the literal closed-disk cost. -/
theorem smoothCost_semicircularOpenDisk_eq_closed
    (lam : ℝ) :
    smoothCost lam semicircularOpenDisk =
      smoothCost lam semicircularClosedDisk := by
  rw [FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral,
    FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral,
    frontier_semicircularOpenDisk_euclidean_eq_closed]
/-- Cost of the constant placed-disk sequence. -/
@[simp] theorem semicircularDiskConstantSequence_cost (lam : ℝ) :
    semicircularDiskConstantSequence.cost lam =
      smoothCost lam semicircularOpenDisk := by
  unfold SmoothSequence.cost
  simp [semicircularDiskConstantSequence]

/-- One branch-complete theorem consumes both the sharp nondegenerate surgery
and the exact degenerate disk bridge. -/
theorem typeThreeRecoverySequence_cost_le_frontierCost
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    (typeThreeRecoverySequence a).cost lam ≤
      ENNReal.ofReal a.WeightedPerimeter := by
  by_cases hh : a.h = 1 / 2
  · simp only [typeThreeRecoverySequence, dif_pos hh]
    rw [semicircularDiskConstantSequence_cost,
      smoothCost_semicircularOpenDisk_eq_closed,
      ← carrier_eq_semicircularClosedDisk a hh,
      ← extended_frontierCost_eq_smoothCost_assembly a]
    rfl
  · simp only [typeThreeRecoverySequence, dif_neg hh]
    simpa only [TypeThreeAssembly.WeightedPerimeter] using
      nondegenerateRecoverySequence_cost_le_frontierCost a hh

/-- The existing real complete-frontier integral is nonnegative on every
type-(iii) assembly. -/
theorem assemblyWeightedPerimeter_nonneg
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    0 ≤ a.WeightedPerimeter := by
  unfold TypeThreeAssembly.WeightedPerimeter _root_.WeightedPerimeter
  apply integral_nonneg
  intro p
  unfold StripDensity
  split_ifs
  · norm_num
  · exact le_trans (by norm_num) a.density_jump.le

/-- Every type-(iii) carrier has relaxed cost bounded by its literal weighted
complete frontier. -/
theorem relaxedPerimeter_le_frontierCost_typeThree
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    relaxedPerimeter lam a.carrier ≤
      ENNReal.ofReal a.WeightedPerimeter := by
  apply le_trans ?_ (typeThreeRecoverySequence_cost_le_frontierCost a)
  unfold relaxedPerimeter
  apply sInf_le
  exact ⟨typeThreeRecoverySequence a,
    a.measurableSet_carrier.nullMeasurableSet,
    typeThreeRecoverySequence_converges_carrier a, rfl⟩

/-- The type-(iii) relaxed perimeter is genuinely finite in `ℝ≥0∞`. -/
theorem relaxedPerimeter_lt_top_typeThree
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    relaxedPerimeter lam a.carrier < ⊤ :=
  (relaxedPerimeter_le_frontierCost_typeThree a).trans_lt
    ENNReal.ofReal_lt_top

/-- Every literal type-(iii) carrier belongs to the concrete relaxed source
domain, including the independently required finite weighted area. -/
theorem isAdmissible_typeThree
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    (relaxedSourceSemantics lam).IsAdmissible a.carrier := by
  rw [relaxedSourceSemantics_isAdmissible]
  exact ⟨⟨a.measurableSet_carrier.nullMeasurableSet,
    relaxedPerimeter_lt_top_typeThree a⟩, a.integrableOn_carrier⟩

/-- Finite real source semantics inherit the sharp type-(iii) frontier upper
bound.  This is the exact `model_covered` inequality required by downstream
minimizer reduction. -/
theorem typeThree_perimeter_le_frontier
    {lam : ℝ} (a : TypeThreeAssembly lam) :
    (relaxedSourceSemantics lam).perimeter a.carrier ≤
      a.WeightedPerimeter := by
  change (relaxedPerimeter lam a.carrier).toReal ≤ a.WeightedPerimeter
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (relaxedPerimeter_le_frontierCost_typeThree a)
  simpa [ENNReal.toReal_ofReal (assemblyWeightedPerimeter_nonneg a)] using hreal


end CMVRelaxation.TypeThreeRecovery
