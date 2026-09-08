/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFourArcSquaredWidth
import CMVSharpRecovery

/-!
# Sharp recovery for arbitrary strict four-arc assemblies

This module proves the squared-width sharp-recovery upper bound without a
common-radius or contact-law hypothesis.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff BigOperators

noncomputable section

namespace CMVRelaxation.FourArcSharpRecovery

open FourArcSquaredRecovery

variable {lam : ℝ} (source : FourArcSquaredRecovery.StrictFourArcAssembly)

/-- The source-dependent compact box of normalized junction coordinates. -/
def normalizedJunctionBox : Set PlanePoint :=
  Icc (0 : ℝ) (FourArcSquaredRecovery.safeScale source) ×ˢ Icc (0 : ℝ) 1

/-- The source squared width along a normalized junction collar. -/
def normalizedJunctionQ (verticalSign : ℝ) (z : PlanePoint) : ℝ :=
  let y := verticalSign * FrozenSquaredRecovery.normalizedJunctionHeight z
  FourArcSquaredRecovery.sideSquare source y +
    Real.smoothTransition (FrozenSquaredRecovery.normalizedJunctionArgument z) *
      (FourArcSquaredRecovery.capSquare source y -
        FourArcSquaredRecovery.sideSquare source y)

/-- One of the four Euclidean junction branches. -/
def realizedNormalizedJunctionParam (horizontalSign verticalSign : ℝ)
    (z : PlanePoint) : EuclideanPlane :=
  planeEuclideanHomeomorph
    (horizontalSign * √(normalizedJunctionQ source verticalSign z),
      verticalSign * FrozenSquaredRecovery.normalizedJunctionHeight z)

lemma normalizedJunctionHeight_mem
    {z : PlanePoint} (hz : z ∈ normalizedJunctionBox source) :
    FrozenSquaredRecovery.normalizedJunctionHeight z ∈ Icc (15 / 16 : ℝ) 1 := by
  apply FrozenSquaredRecovery.normalizedJunctionHeight_mem
  exact ⟨⟨hz.1.1, hz.1.2.trans
    (FourArcSquaredRecovery.safeScale_le_sixteenth source)⟩, hz.2⟩

lemma normalizedJunctionQ_eq_q
    {verticalSign epsilon t : ℝ}
    (hvertical : verticalSign ^ 2 = 1) (hepsilon : 0 < epsilon) :
    normalizedJunctionQ source verticalSign (epsilon, t) =
      FourArcSquaredRecovery.q source epsilon
        (verticalSign * FrozenSquaredRecovery.normalizedJunctionHeight
          (epsilon, t)) := by
  unfold normalizedJunctionQ FourArcSquaredRecovery.q
    FrozenSquaredRecovery.junctionWeight
  dsimp only
  rw [FrozenSquaredRecovery.normalizedJunctionArgument_eq hepsilon]
  congr 2
  rw [mul_pow, hvertical, one_mul]
  unfold FrozenSquaredRecovery.normalizedJunctionHeight
  dsimp only

lemma normalizedJunctionQ_ge_attachment
    {verticalSign epsilon t : ℝ} (hvertical : |verticalSign| = 1)
    (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ FourArcSquaredRecovery.safeScale source)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    source.attachmentHalfWidth ^ 2 ≤
      normalizedJunctionQ source verticalSign (epsilon, t) := by
  have hz : (epsilon, t) ∈ normalizedJunctionBox source :=
    ⟨⟨hepsilon.le, hepsilon_le⟩, ht⟩
  have hh := normalizedJunctionHeight_mem source hz
  have hhpos : 0 < FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t) :=
    lt_of_lt_of_le (by norm_num) hh.1
  let y := verticalSign *
    FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t)
  have habsy : |y| ∈ Icc (1 - epsilon : ℝ) 1 := by
    dsimp [y]
    rw [abs_mul, hvertical, one_mul, abs_of_pos hhpos]
    constructor
    · unfold FrozenSquaredRecovery.normalizedJunctionHeight
      dsimp only
      nlinarith [ht.1]
    · exact hh.2
  rw [normalizedJunctionQ_eq_q source
    (by calc verticalSign ^ 2 = |verticalSign| ^ 2 := by rw [sq_abs]
        _ = 1 := by rw [hvertical]; norm_num) hepsilon]
  exact (FourArcSquaredRecovery.q_ge_positive_attachment source
    hepsilon hepsilon_le habsy).2

/-- The source normalized squared width has an `O(epsilon)` Lipschitz
constant in the normalized trace parameter. -/
theorem exists_scaled_normalizedJunctionQ_lipschitz
    {verticalSign : ℝ} (hvertical : |verticalSign| = 1) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
      epsilon ≤ FourArcSquaredRecovery.safeScale source →
      LipschitzOnWith (K * epsilon.toNNReal)
        (fun t : ℝ => normalizedJunctionQ source verticalSign (epsilon, t))
        (Icc (0 : ℝ) 1) := by
  have hsmoothSide : ContDiffOn ℝ 1
      (FourArcSquaredRecovery.sideSquare source) (Icc (-1 : ℝ) 1) :=
    ((FourArcSquaredRecovery.contDiff_sideSquare source).of_le (by simp)).contDiffOn
  rcases hsmoothSide.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (-1 : ℝ) 1) isCompact_Icc with
    ⟨Ks, hKs⟩
  have hsmoothCap : ContDiffOn ℝ 1
      (FourArcSquaredRecovery.capSquare source) (Icc (-1 : ℝ) 1) :=
    ((FourArcSquaredRecovery.contDiff_capSquare source).of_le (by simp)).contDiffOn
  rcases hsmoothCap.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (-1 : ℝ) 1) isCompact_Icc with
    ⟨Kc, hKc⟩
  have hweightSmooth : ContDiffOn ℝ 1
      (fun z : PlanePoint =>
        Real.smoothTransition
          (FrozenSquaredRecovery.normalizedJunctionArgument z))
      (normalizedJunctionBox source) :=
    Real.smoothTransition.contDiff.comp_contDiffOn
      (FrozenSquaredRecovery.contDiffOn_normalizedJunctionArgument.mono
        (fun _ hz =>
          ⟨⟨hz.1.1, hz.1.2.trans
            (FourArcSquaredRecovery.safeScale_le_sixteenth source)⟩, hz.2⟩))
  rcases hweightSmooth.exists_lipschitzOnWith (by norm_num)
      (by
        simpa [normalizedJunctionBox] using
          (Convex.prod (𝕜 := ℝ)
            (convex_Icc (0 : ℝ)
              (FourArcSquaredRecovery.safeScale source))
            (convex_Icc (0 : ℝ) 1) :
            Convex ℝ (Icc (0 : ℝ)
              (FourArcSquaredRecovery.safeScale source) ×ˢ
                Icc (0 : ℝ) 1)))
      (by
        simpa [normalizedJunctionBox] using
          (isCompact_Icc.prod isCompact_Icc :
            IsCompact
              (Icc (0 : ℝ)
                (FourArcSquaredRecovery.safeScale source) ×ˢ
                  Icc (0 : ℝ) 1))) with
    ⟨Kw, hKw⟩
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
  have hzt : (epsilon, t) ∈ normalizedJunctionBox source :=
    ⟨⟨hepsilon.le, hepsilon_le⟩, ht⟩
  have hzu : (epsilon, u) ∈ normalizedJunctionBox source :=
    ⟨⟨hepsilon.le, hepsilon_le⟩, hu⟩
  let yt := verticalSign *
    FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t)
  let yu := verticalSign *
    FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, u)
  have hht := normalizedJunctionHeight_mem source hzt
  have hhu := normalizedJunctionHeight_mem source hzu
  have hht0 : 0 < FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t) :=
    lt_of_lt_of_le (by norm_num) hht.1
  have hhu0 : 0 < FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, u) :=
    lt_of_lt_of_le (by norm_num) hhu.1
  have habst : |yt| ∈ Icc (15 / 16 : ℝ) 1 := by
    dsimp [yt]
    rw [abs_mul, hvertical, one_mul, abs_of_pos hht0]
    exact hht
  have habsu : |yu| ∈ Icc (15 / 16 : ℝ) 1 := by
    dsimp [yu]
    rw [abs_mul, hvertical, one_mul, abs_of_pos hhu0]
    exact hhu
  have hyt : yt ∈ Icc (-1 : ℝ) 1 := abs_le.mp habst.2
  have hyu : yu ∈ Icc (-1 : ℝ) 1 := abs_le.mp habsu.2
  have hydist : |yt - yu| = epsilon * |t - u| := by
    dsimp [yt, yu, FrozenSquaredRecovery.normalizedJunctionHeight]
    rw [show
        verticalSign * (1 - epsilon + epsilon * t) -
            verticalSign * (1 - epsilon + epsilon * u) =
          verticalSign * epsilon * (t - u) by ring,
      abs_mul, abs_mul, hvertical, abs_of_pos hepsilon, one_mul]
  have hside :
      |FourArcSquaredRecovery.sideSquare source yt -
          FourArcSquaredRecovery.sideSquare source yu| ≤
        (Ks : ℝ) * (epsilon * |t - u|) := by
    have h := hKs.dist_le_mul yt hyt yu hyu
    simpa only [Real.dist_eq, hydist] using h
  have hcap :
      |FourArcSquaredRecovery.capSquare source yt -
          FourArcSquaredRecovery.capSquare source yu| ≤
        (Kc : ℝ) * (epsilon * |t - u|) := by
    have h := hKc.dist_le_mul yt hyt yu hyu
    simpa only [Real.dist_eq, hydist] using h
  have hgapDiff :
      |(FourArcSquaredRecovery.capSquare source yt -
          FourArcSquaredRecovery.sideSquare source yt) -
        (FourArcSquaredRecovery.capSquare source yu -
          FourArcSquaredRecovery.sideSquare source yu)| ≤
        ((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|) := by
    calc
      |(FourArcSquaredRecovery.capSquare source yt -
          FourArcSquaredRecovery.sideSquare source yt) -
        (FourArcSquaredRecovery.capSquare source yu -
          FourArcSquaredRecovery.sideSquare source yu)| =
          |(FourArcSquaredRecovery.capSquare source yt -
              FourArcSquaredRecovery.capSquare source yu) -
            (FourArcSquaredRecovery.sideSquare source yt -
              FourArcSquaredRecovery.sideSquare source yu)| := by
                congr 1
                ring
      _ ≤ |FourArcSquaredRecovery.capSquare source yt -
              FourArcSquaredRecovery.capSquare source yu| +
            |FourArcSquaredRecovery.sideSquare source yt -
              FourArcSquaredRecovery.sideSquare source yu| := abs_sub _ _
      _ ≤ (Kc : ℝ) * (epsilon * |t - u|) +
          (Ks : ℝ) * (epsilon * |t - u|) := add_le_add hcap hside
      _ = ((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|) := by ring
  have hvertical_sq : verticalSign ^ 2 = 1 := by
    calc
      verticalSign ^ 2 = |verticalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hvertical]; norm_num
  have hsign : verticalSign = 1 ∨ verticalSign = -1 :=
    sq_eq_one_iff.mp hvertical_sq
  have hgapU :
      |FourArcSquaredRecovery.capSquare source yu -
          FourArcSquaredRecovery.sideSquare source yu| ≤
        ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by
    rcases hsign with hsign | hsign
    · have hyCenter : |yu - 1| ≤ epsilon := by
        rw [abs_le]
        dsimp [yu, FrozenSquaredRecovery.normalizedJunctionHeight]
        rw [hsign]
        constructor <;> nlinarith [hu.1, hu.2]
      have hc := hKc.dist_le_mul yu hyu 1
        (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
      have hs := hKs.dist_le_mul yu hyu 1
        (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
      calc
        |FourArcSquaredRecovery.capSquare source yu -
            FourArcSquaredRecovery.sideSquare source yu| =
            |(FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.capSquare source 1) -
              (FourArcSquaredRecovery.sideSquare source yu -
                FourArcSquaredRecovery.sideSquare source 1)| := by
                  rw [FourArcSquaredRecovery.capSquare_one source,
                    FourArcSquaredRecovery.sideSquare_one source]
                  congr 1
                  ring
        _ ≤ |FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.capSquare source 1| +
              |FourArcSquaredRecovery.sideSquare source yu -
                FourArcSquaredRecovery.sideSquare source 1| := abs_sub _ _
        _ ≤ (Kc : ℝ) * |yu - 1| + (Ks : ℝ) * |yu - 1| := by
          simpa only [Real.dist_eq] using add_le_add hc hs
        _ ≤ (Kc : ℝ) * epsilon + (Ks : ℝ) * epsilon := by gcongr
        _ = ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by ring
    · have hyCenter : |yu - (-1)| ≤ epsilon := by
        rw [abs_le]
        dsimp [yu, FrozenSquaredRecovery.normalizedJunctionHeight]
        rw [hsign]
        constructor <;> nlinarith [hu.1, hu.2]
      have hc := hKc.dist_le_mul yu hyu (-1)
        (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)
      have hs := hKs.dist_le_mul yu hyu (-1)
        (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)
      calc
        |FourArcSquaredRecovery.capSquare source yu -
            FourArcSquaredRecovery.sideSquare source yu| =
            |(FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.capSquare source (-1)) -
              (FourArcSquaredRecovery.sideSquare source yu -
                FourArcSquaredRecovery.sideSquare source (-1))| := by
                  rw [FourArcSquaredRecovery.capSquare_neg_one source,
                    FourArcSquaredRecovery.sideSquare_neg_one source]
                  congr 1
                  ring
        _ ≤ |FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.capSquare source (-1)| +
              |FourArcSquaredRecovery.sideSquare source yu -
                FourArcSquaredRecovery.sideSquare source (-1)| := abs_sub _ _
        _ ≤ (Kc : ℝ) * |yu - (-1)| +
            (Ks : ℝ) * |yu - (-1)| := by
          simpa only [Real.dist_eq] using add_le_add hc hs
        _ ≤ (Kc : ℝ) * epsilon + (Ks : ℝ) * epsilon := by gcongr
        _ = ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by ring
  let wt := Real.smoothTransition
    (FrozenSquaredRecovery.normalizedJunctionArgument (epsilon, t))
  let wu := Real.smoothTransition
    (FrozenSquaredRecovery.normalizedJunctionArgument (epsilon, u))
  have hwt : |wt| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hweight : |wt - wu| ≤ (Kw : ℝ) * |t - u| := by
    have h := hKw.dist_le_mul (epsilon, t) hzt (epsilon, u) hzu
    simpa only [Real.dist_eq, Prod.dist_eq, sub_self, abs_zero,
      max_eq_right (abs_nonneg (t - u)), wt, wu] using h
  have hproduct :
      |wt * (FourArcSquaredRecovery.capSquare source yt -
          FourArcSquaredRecovery.sideSquare source yt) -
        wu * (FourArcSquaredRecovery.capSquare source yu -
          FourArcSquaredRecovery.sideSquare source yu)| ≤
        (((Kc : ℝ) + (Ks : ℝ)) +
          (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
            (epsilon * |t - u|) := by
    calc
      |wt * (FourArcSquaredRecovery.capSquare source yt -
          FourArcSquaredRecovery.sideSquare source yt) -
        wu * (FourArcSquaredRecovery.capSquare source yu -
          FourArcSquaredRecovery.sideSquare source yu)| =
          |wt * ((FourArcSquaredRecovery.capSquare source yt -
              FourArcSquaredRecovery.sideSquare source yt) -
            (FourArcSquaredRecovery.capSquare source yu -
              FourArcSquaredRecovery.sideSquare source yu)) +
          (wt - wu) * (FourArcSquaredRecovery.capSquare source yu -
            FourArcSquaredRecovery.sideSquare source yu)| := by
              congr 1
              ring
      _ ≤ |wt * ((FourArcSquaredRecovery.capSquare source yt -
              FourArcSquaredRecovery.sideSquare source yt) -
            (FourArcSquaredRecovery.capSquare source yu -
              FourArcSquaredRecovery.sideSquare source yu))| +
          |(wt - wu) * (FourArcSquaredRecovery.capSquare source yu -
            FourArcSquaredRecovery.sideSquare source yu)| := abs_add_le _ _
      _ = |wt| *
            |(FourArcSquaredRecovery.capSquare source yt -
                FourArcSquaredRecovery.sideSquare source yt) -
              (FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.sideSquare source yu)| +
          |wt - wu| * |FourArcSquaredRecovery.capSquare source yu -
            FourArcSquaredRecovery.sideSquare source yu| := by
              rw [abs_mul, abs_mul]
      _ ≤ 1 * (((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|)) +
          ((Kw : ℝ) * |t - u|) *
            (((Kc : ℝ) + (Ks : ℝ)) * epsilon) := by gcongr
      _ = (((Kc : ℝ) + (Ks : ℝ)) +
          (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
            (epsilon * |t - u|) := by ring
  have hq :
      |normalizedJunctionQ source verticalSign (epsilon, t) -
        normalizedJunctionQ source verticalSign (epsilon, u)| ≤
        C * (epsilon * |t - u|) := by
    change
      |FourArcSquaredRecovery.sideSquare source yt +
          wt * (FourArcSquaredRecovery.capSquare source yt -
            FourArcSquaredRecovery.sideSquare source yt) -
        (FourArcSquaredRecovery.sideSquare source yu +
          wu * (FourArcSquaredRecovery.capSquare source yu -
            FourArcSquaredRecovery.sideSquare source yu))| ≤ _
    calc
      _ = |(FourArcSquaredRecovery.sideSquare source yt -
              FourArcSquaredRecovery.sideSquare source yu) +
            (wt * (FourArcSquaredRecovery.capSquare source yt -
                FourArcSquaredRecovery.sideSquare source yt) -
              wu * (FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.sideSquare source yu))| := by
                  congr 1
                  ring
      _ ≤ |FourArcSquaredRecovery.sideSquare source yt -
              FourArcSquaredRecovery.sideSquare source yu| +
            |wt * (FourArcSquaredRecovery.capSquare source yt -
                FourArcSquaredRecovery.sideSquare source yt) -
              wu * (FourArcSquaredRecovery.capSquare source yu -
                FourArcSquaredRecovery.sideSquare source yu)| := abs_add_le _ _
      _ ≤ (Ks : ℝ) * (epsilon * |t - u|) +
          (((Kc : ℝ) + (Ks : ℝ)) +
            (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
              (epsilon * |t - u|) := add_le_add hside hproduct
      _ = C * (epsilon * |t - u|) := by
        dsimp [C]
        ring
  calc
    dist (normalizedJunctionQ source verticalSign (epsilon, t))
        (normalizedJunctionQ source verticalSign (epsilon, u)) =
        |normalizedJunctionQ source verticalSign (epsilon, t) -
          normalizedJunctionQ source verticalSign (epsilon, u)| := Real.dist_eq _ _
    _ ≤ C * (epsilon * |t - u|) := hq
    _ = ((⟨C, hC⟩ : ℝ≥0) * epsilon.toNNReal : ℝ) * dist t u := by
      change C * (epsilon * |t - u|) =
        C * (epsilon.toNNReal : ℝ) * dist t u
      rw [Real.coe_toNNReal epsilon hepsilon.le, Real.dist_eq]
      ring


/-- Square root is Lipschitz on squared widths bounded below by `w²`. -/
lemma dist_sqrt_le_abs_sub_div
    {w a b : ℝ} (hw : 0 < w) (ha : w ^ 2 ≤ a) (hb : w ^ 2 ≤ b) :
    dist (√a) (√b) ≤ |a - b| / w := by
  have ha0 : 0 ≤ a := le_trans (sq_nonneg w) ha
  have hb0 : 0 ≤ b := le_trans (sq_nonneg w) hb
  have hsa : w ≤ √a := Real.le_sqrt_of_sq_le ha
  have hsb : w ≤ √b := Real.le_sqrt_of_sq_le hb
  have hsum : w ≤ |√a + √b| := by
    rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith
  have hidentity : |√a - √b| * |√a + √b| = |a - b| := by
    rw [← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt hb0]
  rw [Real.dist_eq]
  apply (le_div_iff₀ hw).2
  calc
    |√a - √b| * w ≤ |√a - √b| * |√a + √b| :=
      mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = |a - b| := hidentity

/-- Each of the four actual source junction branches has Lipschitz constant
proportional to the collar width. -/
theorem exists_scaled_junction_lipschitz
    {horizontalSign verticalSign : ℝ}
    (hhorizontal : |horizontalSign| = 1)
    (hvertical : |verticalSign| = 1) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
      epsilon ≤ FourArcSquaredRecovery.safeScale source →
      LipschitzOnWith (K * epsilon.toNNReal)
        (fun t : ℝ =>
          realizedNormalizedJunctionParam source horizontalSign verticalSign
            (epsilon, t))
        (Icc (0 : ℝ) 1) := by
  rcases exists_scaled_normalizedJunctionQ_lipschitz source hvertical with
    ⟨Kq, hKq⟩
  let w : ℝ≥0 := ⟨source.attachmentHalfWidth,
    (FourArcSquaredRecovery.attachmentHalfWidth_pos source).le⟩
  refine ⟨Kq / w + 1, ?_⟩
  intro epsilon hepsilon hepsilon_le
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  let qt := normalizedJunctionQ source verticalSign (epsilon, t)
  let qu := normalizedJunctionQ source verticalSign (epsilon, u)
  have hqt : source.attachmentHalfWidth ^ 2 ≤ qt := by
    exact normalizedJunctionQ_ge_attachment source hvertical
      hepsilon hepsilon_le ht
  have hqu : source.attachmentHalfWidth ^ 2 ≤ qu := by
    exact normalizedJunctionQ_ge_attachment source hvertical
      hepsilon hepsilon_le hu
  have hqdist :
      dist qt qu ≤ ((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u :=
    (hKq hepsilon hepsilon_le).dist_le_mul t ht u hu
  have hsqrt :
      dist (√qt) (√qu) ≤
        (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
    calc
      dist (√qt) (√qu) ≤
          |qt - qu| / source.attachmentHalfWidth :=
        dist_sqrt_le_abs_sub_div
          (FourArcSquaredRecovery.attachmentHalfWidth_pos source) hqt hqu
      _ ≤ (((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u) /
          source.attachmentHalfWidth := by
        exact (div_le_div_iff_of_pos_right
          (FourArcSquaredRecovery.attachmentHalfWidth_pos source)).2
            (by simpa only [Real.dist_eq] using hqdist)
      _ = (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
        change ((Kq : ℝ) * (epsilon.toNNReal : ℝ) * dist t u) /
            source.attachmentHalfWidth =
          (((Kq : ℝ) / source.attachmentHalfWidth) *
            (epsilon.toNNReal : ℝ)) * dist t u
        field_simp [(FourArcSquaredRecovery.attachmentHalfWidth_pos source).ne']
  have hx :
      dist (horizontalSign * √qt) (horizontalSign * √qu) ≤
        (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
    rw [Real.dist_eq, show
      horizontalSign * √qt - horizontalSign * √qu =
        horizontalSign * (√qt - √qu) by ring, abs_mul, hhorizontal,
      one_mul]
    simpa only [Real.dist_eq] using hsqrt
  have hy :
      dist
          (verticalSign *
            FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t))
          (verticalSign *
            FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, u)) =
        epsilon * dist t u := by
    rw [Real.dist_eq, Real.dist_eq, show
      verticalSign *
          FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t) -
        verticalSign *
          FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, u) =
        verticalSign * epsilon * (t - u) by
          unfold FrozenSquaredRecovery.normalizedJunctionHeight
          dsimp only
          ring,
      abs_mul, abs_mul, hvertical, abs_of_pos hepsilon, one_mul]
  calc
    dist
        (realizedNormalizedJunctionParam source horizontalSign verticalSign
          (epsilon, t))
        (realizedNormalizedJunctionParam source horizontalSign verticalSign
          (epsilon, u)) ≤
        dist (horizontalSign * √qt) (horizontalSign * √qu) +
          dist
            (verticalSign *
              FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t))
            (verticalSign *
              FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, u)) := by
                apply FrozenSquaredRecovery.dist_planeEuclideanHomeomorph_le
    _ ≤ (((Kq / w) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u +
          epsilon * dist t u := add_le_add hx hy.le
    _ = ((((Kq / w) + 1) * epsilon.toNNReal : ℝ≥0) : ℝ) *
          dist t u := by
      simp only [NNReal.coe_mul, NNReal.coe_add,
        Real.coe_toNNReal epsilon hepsilon.le, NNReal.coe_one]
      ring

/-- Index the four sign choices for the moving junction traces. -/
def junctionParam (source : StrictFourArcAssembly) (epsilon : ℝ)
    (i : Fin 4) (t : ℝ) : EuclideanPlane :=
  match i.1 with
  | 0 => realizedNormalizedJunctionParam source (-1) (-1) (epsilon, t)
  | 1 => realizedNormalizedJunctionParam source 1 (-1) (epsilon, t)
  | 2 => realizedNormalizedJunctionParam source (-1) 1 (epsilon, t)
  | _ => realizedNormalizedJunctionParam source 1 1 (epsilon, t)

/-- The union of all four moving source junction traces. -/
def actualJunctionTrace (source : StrictFourArcAssembly) (epsilon : ℝ) :
    Set EuclideanPlane :=
  ⋃ i : Fin 4, junctionParam source epsilon i '' Icc (0 : ℝ) 1

theorem exists_scaled_actual_junction_lipschitz :
    ∃ K : Fin 4 → ℝ≥0,
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
        epsilon ≤ FourArcSquaredRecovery.safeScale source → ∀ i : Fin 4,
        LipschitzOnWith (K i * epsilon.toNNReal)
          (junctionParam source epsilon i) (Icc (0 : ℝ) 1) := by
  rcases exists_scaled_junction_lipschitz source
      (horizontalSign := (-1 : ℝ)) (verticalSign := (-1 : ℝ))
      (by norm_num) (by norm_num) with ⟨K0, hK0⟩
  rcases exists_scaled_junction_lipschitz source
      (horizontalSign := (1 : ℝ)) (verticalSign := (-1 : ℝ))
      (by norm_num) (by norm_num) with ⟨K1, hK1⟩
  rcases exists_scaled_junction_lipschitz source
      (horizontalSign := (-1 : ℝ)) (verticalSign := (1 : ℝ))
      (by norm_num) (by norm_num) with ⟨K2, hK2⟩
  rcases exists_scaled_junction_lipschitz source
      (horizontalSign := (1 : ℝ)) (verticalSign := (1 : ℝ))
      (by norm_num) (by norm_num) with ⟨K3, hK3⟩
  let K : Fin 4 → ℝ≥0 := fun i =>
    match i.1 with
    | 0 => K0
    | 1 => K1
    | 2 => K2
    | _ => K3
  refine ⟨K, ?_⟩
  intro epsilon hepsilon hepsilon_le i
  fin_cases i
  · exact hK0 hepsilon hepsilon_le
  · exact hK1 hepsilon hepsilon_le
  · exact hK2 hepsilon hepsilon_le
  · exact hK3 hepsilon hepsilon_le

/-- The junction union has source-dependent Euclidean `H¹` bounded by
`C * epsilon`, with finite `C`. -/
theorem exists_scaled_actual_junction_union_hausdorffMeasure :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
        epsilon ≤ FourArcSquaredRecovery.safeScale source →
        (μH[1] : Measure EuclideanPlane) (actualJunctionTrace source epsilon) ≤
          C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_actual_junction_lipschitz source with ⟨K, hK⟩
  let C : ℝ≥0∞ := ∑ i : Fin 4, (K i : ℝ≥0∞)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [ENNReal.sum_lt_top]
    intro i hi
    exact ENNReal.coe_lt_top
  · intro epsilon hepsilon hepsilon_le
    calc
      (μH[1] : Measure EuclideanPlane) (actualJunctionTrace source epsilon) ≤
          ∑' i : Fin 4, (μH[1] : Measure EuclideanPlane)
            (junctionParam source epsilon i '' Icc (0 : ℝ) 1) := by
        exact measure_iUnion_le _
      _ ≤ ∑' i : Fin 4,
          ((K i * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by
        apply ENNReal.tsum_le_tsum
        intro i
        have hi := (hK hepsilon hepsilon_le i).hausdorffMeasure_image_le
          (d := (1 : ℝ)) (by norm_num)
        simpa [ENNReal.rpow_one, hausdorffMeasure_real,
          Real.volume_Icc] using hi
      _ = ∑ i : Fin 4,
          ((K i * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by simp
      _ = C * (epsilon.toNNReal : ℝ≥0∞) := by
        dsimp [C]
        simp only [Finset.sum_mul]


/-- Every point satisfying the actual source squared-width equation belongs
to its literal topological frontier, including the two zero-width poles. -/
lemma sq_eq_targetQ_mem_frontier {p : PlanePoint}
    (hp : p.1 ^ 2 = FourArcSquaredRecovery.targetQ source p.2) :
    p ∈ frontier source.assembly.carrier := by
  have hpCarrier : p ∈ source.assembly.carrier :=
    (FourArcSquaredRecovery.mem_source_iff_sq_le_targetQ source p).2 hp.le
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hinterior
  have hnhds : interior source.assembly.carrier ∈ nhds p :=
    isOpen_interior.mem_nhds hinterior
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hball⟩
  have hhalf : 0 < r / 2 := div_pos hr (by norm_num)
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
    have hzCarrier : z ∈ source.assembly.carrier :=
      interior_subset (hball hzball)
    have hzle :=
      (FourArcSquaredRecovery.mem_source_iff_sq_le_targetQ source z).1
        hzCarrier
    change (p.1 + r / 2) ^ 2 ≤
      FourArcSquaredRecovery.targetQ source p.2 at hzle
    nlinarith
  · have hx' : p.1 < 0 := lt_of_not_ge hx
    let z : PlanePoint := (p.1 - r / 2, p.2)
    have hzball : z ∈ Metric.ball p r := by
      rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      dsimp [z]
      rw [abs_of_neg (by linarith : p.1 - r / 2 - p.1 < 0)]
      simp only [sub_self, abs_zero]
      ring_nf
      rw [max_eq_left (by positivity)]
      linarith
    have hzCarrier : z ∈ source.assembly.carrier :=
      interior_subset (hball hzball)
    have hzle :=
      (FourArcSquaredRecovery.mem_source_iff_sq_le_targetQ source z).1
        hzCarrier
    change (p.1 - r / 2) ^ 2 ≤
      FourArcSquaredRecovery.targetQ source p.2 at hzle
    nlinarith

/-- Literal Euclidean frontier domination.  The closed source frontier covers
everything outside the open collars; the four actual traces cover the collars,
including both junction endpoints.  The source term contains both poles. -/
theorem realized_frontier_subset_source_union_actualJunctionTrace
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ FourArcSquaredRecovery.safeScale source) :
    planeEuclideanHomeomorph ''
        frontier (FourArcSquaredRecovery.domain source epsilon) ⊆
      planeEuclideanHomeomorph '' frontier source.assembly.carrier ∪
        actualJunctionTrace source epsilon := by
  rintro _ ⟨p, hpfrontier, rfl⟩
  have hpEq : p.1 ^ 2 =
      FourArcSquaredRecovery.q source epsilon p.2 :=
    frontier_lt_subset_eq (continuous_fst.pow 2)
      ((FourArcSquaredRecovery.contDiff_q source epsilon).continuous.comp
        continuous_snd) hpfrontier
  by_cases hjunction : 1 - epsilon < |p.2| ∧ |p.2| < 1
  · right
    rw [actualJunctionTrace]
    have hqnonneg : 0 ≤ FourArcSquaredRecovery.q source epsilon p.2 := by
      rw [← hpEq]
      positivity
    have hsqrt :
        (√(FourArcSquaredRecovery.q source epsilon p.2)) ^ 2 =
          FourArcSquaredRecovery.q source epsilon p.2 :=
      Real.sq_sqrt hqnonneg
    have hroot :
        p.1 = √(FourArcSquaredRecovery.q source epsilon p.2) ∨
          p.1 = -√(FourArcSquaredRecovery.q source epsilon p.2) := by
      rw [← hsqrt] at hpEq
      exact (sq_eq_sq_iff_eq_or_eq_neg).mp hpEq
    let t := (|p.2| - (1 - epsilon)) / epsilon
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      dsimp [t]
      constructor
      · exact div_nonneg (by linarith [hjunction.1]) hepsilon.le
      · rw [div_le_one hepsilon]
        linarith [hjunction.2]
    have hheight :
        FrozenSquaredRecovery.normalizedJunctionHeight (epsilon, t) =
          |p.2| := by
      unfold FrozenSquaredRecovery.normalizedJunctionHeight
      dsimp only
      dsimp [t]
      field_simp [hepsilon.ne']
      ring
    rcases le_total 0 p.2 with hy0 | hy0
    · have habsy : |p.2| = p.2 := abs_of_nonneg hy0
      have hqbridge := normalizedJunctionQ_eq_q source
        (verticalSign := (1 : ℝ)) (t := t) (by norm_num) hepsilon
      rw [hheight, habsy, one_mul] at hqbridge
      rcases hroot with hright | hleft
      · apply Set.mem_iUnion.2
        refine ⟨(3 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change realizedNormalizedJunctionParam source 1 1 (epsilon, t) =
          planeEuclideanHomeomorph p
        unfold realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hright]
        · simp [hheight, habsy]
      · apply Set.mem_iUnion.2
        refine ⟨(2 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change realizedNormalizedJunctionParam source (-1) 1 (epsilon, t) =
          planeEuclideanHomeomorph p
        unfold realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hleft]
        · simp [hheight, habsy]
    · have habsy : |p.2| = -p.2 := abs_of_nonpos hy0
      have hqbridge := normalizedJunctionQ_eq_q source
        (verticalSign := (-1 : ℝ)) (t := t) (by norm_num) hepsilon
      rw [hheight, habsy] at hqbridge
      norm_num at hqbridge
      rcases hroot with hright | hleft
      · apply Set.mem_iUnion.2
        refine ⟨(1 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change realizedNormalizedJunctionParam source 1 (-1) (epsilon, t) =
          planeEuclideanHomeomorph p
        unfold realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hright]
        · simp [hheight, habsy]
      · apply Set.mem_iUnion.2
        refine ⟨(0 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change realizedNormalizedJunctionParam source (-1) (-1) (epsilon, t) =
          planeEuclideanHomeomorph p
        unfold realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hleft]
        · simp [hheight, habsy]
  · left
    refine ⟨p, ?_, rfl⟩
    apply sq_eq_targetQ_mem_frontier source
    rw [← FourArcSquaredRecovery.recovery_q_eq_targetQ_outside_junction
      source hepsilon hepsilon_le hjunction]
    exact hpEq

/-- On the assembly carrier, the extended smooth cost is exactly the
`ENNReal.ofReal` of its real weighted frontier integral at the same density. -/
theorem extended_frontierCost_eq_smoothCost_source (hlam : 1 < lam) :
    ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure source.assembly.carrier)) =
      smoothCost lam source.assembly.carrier := by
  have hintegrable :
      Integrable (StripDensity lam) (FrontierMeasure source.assembly.carrier) :=
    FourArcAssembly.integrable_frontierMeasure lam source.assembly
  have hlam0 : 0 ≤ lam := le_trans (by norm_num) hlam.le
  have hnonneg :
      0 ≤ᵐ[FrontierMeasure source.assembly.carrier] StripDensity lam :=
    Eventually.of_forall (fun p => by
      unfold StripDensity
      split_ifs
      · norm_num
      · exact hlam0)
  unfold _root_.WeightedPerimeter smoothCost
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hintegrable hnonneg

/-- Sharp assembly-level cost estimate: the full actual frontier is charged
with the literal density, and only the four moving junction traces contribute
the finite `C * epsilon` excess. -/
theorem exists_sharp_smoothCost_domain_bound (hlam : 1 < lam) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon →
        epsilon ≤ FourArcSquaredRecovery.safeScale source →
        smoothCost lam (FourArcSquaredRecovery.domain source epsilon) ≤
          ENNReal.ofReal
              (_root_.WeightedPerimeter lam
                (FrontierMeasure source.assembly.carrier)) +
            C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_actual_junction_union_hausdorffMeasure source with
    ⟨Cj, hCj, hJmeasure⟩
  let Λ : ℝ≥0∞ := ENNReal.ofReal lam
  refine ⟨Λ * Cj, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCj, ?_⟩
  intro epsilon hepsilon hepsilon_le
  let μ : Measure EuclideanPlane := μH[1]
  let f : EuclideanPlane → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (euclideanStripDensity lam z)
  have hfrontier :
      frontier
          (planeEuclideanHomeomorph ''
            FourArcSquaredRecovery.domain source epsilon) ⊆
        frontier (planeEuclideanHomeomorph '' source.assembly.carrier) ∪
          actualJunctionTrace source epsilon := by
    simpa only [planeEuclideanHomeomorph.image_frontier] using
      realized_frontier_subset_source_union_actualJunctionTrace
        source hepsilon hepsilon_le
  have hJmeasure' :
      μ (actualJunctionTrace source epsilon) ≤
        Cj * (epsilon.toNNReal : ℝ≥0∞) := by
    simpa only [μ] using hJmeasure hepsilon hepsilon_le
  have hJcost :
      (∫⁻ z in actualJunctionTrace source epsilon, f z ∂μ) ≤
        Λ * μ (actualJunctionTrace source epsilon) := by
    calc
      (∫⁻ z in actualJunctionTrace source epsilon, f z ∂μ) ≤
          ∫⁻ _z in actualJunctionTrace source epsilon, Λ ∂μ := by
        apply MeasureTheory.setLIntegral_mono measurable_const
        intro z _hz
        dsimp [f, Λ]
        unfold euclideanStripDensity StripDensity
        split_ifs
        · exact ENNReal.ofReal_le_ofReal hlam.le
        · exact le_rfl
      _ = Λ * μ (actualJunctionTrace source epsilon) := by simp
  rw [FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral]
  change (∫⁻ z in frontier
      (planeEuclideanHomeomorph ''
        FourArcSquaredRecovery.domain source epsilon), f z ∂μ) ≤ _
  calc
    (∫⁻ z in frontier
        (planeEuclideanHomeomorph ''
          FourArcSquaredRecovery.domain source epsilon), f z ∂μ) ≤
        ∫⁻ z in
          frontier (planeEuclideanHomeomorph '' source.assembly.carrier) ∪
            actualJunctionTrace source epsilon, f z ∂μ :=
      MeasureTheory.lintegral_mono_set hfrontier
    _ ≤
        (∫⁻ z in frontier
            (planeEuclideanHomeomorph '' source.assembly.carrier), f z ∂μ) +
          ∫⁻ z in actualJunctionTrace source epsilon, f z ∂μ :=
      MeasureTheory.lintegral_union_le _ _ _
    _ ≤ smoothCost lam source.assembly.carrier +
          Λ * μ (actualJunctionTrace source epsilon) := by
      rw [FrozenCanonicalCap.smoothCost_eq_euclidean_lintegral]
      exact add_le_add le_rfl hJcost
    _ =
        ENNReal.ofReal
            (_root_.WeightedPerimeter lam
              (FrontierMeasure source.assembly.carrier)) +
          Λ * μ (actualJunctionTrace source epsilon) := by
      rw [extended_frontierCost_eq_smoothCost_source source hlam]
    _ ≤
        ENNReal.ofReal
            (_root_.WeightedPerimeter lam
              (FrontierMeasure source.assembly.carrier)) +
          (Λ * Cj) * (epsilon.toNNReal : ℝ≥0∞) := by
      apply add_le_add le_rfl
      calc
        Λ * μ (actualJunctionTrace source epsilon) ≤
            Λ * (Cj * (epsilon.toNNReal : ℝ≥0∞)) := by gcongr
        _ = (Λ * Cj) * (epsilon.toNNReal : ℝ≥0∞) := by ring

/-- The existing source squared-width recovery sequence has no more liminf
cost than the exact canonical weighted frontier. -/
theorem recoverySequence_cost_le_frontierCost (hlam : 1 < lam) :
    (FourArcSquaredRecovery.recoverySequence source).cost lam ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure source.assembly.carrier)) := by
  rcases exists_sharp_smoothCost_domain_bound source hlam with ⟨C, hC, hbound⟩
  let P : ℝ≥0∞ :=
    ENNReal.ofReal
      (_root_.WeightedPerimeter lam (FrontierMeasure source.assembly.carrier))
  have hpoint : ∀ n : ℕ,
      smoothCost lam
          ((FourArcSquaredRecovery.recoverySequence source).carrier n) ≤
        P + C * ((FourArcSquaredRecovery.recoveryScale source n).toNNReal :
          ℝ≥0∞) := by
    intro n
    simpa only [FourArcSquaredRecovery.recoverySequence, P] using
      hbound (FourArcSquaredRecovery.recoveryScale_pos source n)
        (FourArcSquaredRecovery.recoveryScale_le source n)
  have hscalePoint (n : ℕ) :
      ((FourArcSquaredRecovery.recoveryScale source n).toNNReal : ℝ≥0∞) =
        ENNReal.ofReal (FourArcSquaredRecovery.recoveryScale source n) := by
    rw [ENNReal.ofReal_eq_coe_nnreal
      (FourArcSquaredRecovery.recoveryScale_pos source n).le]
    congr 1
    ext
    exact congrArg (fun x : ℝ≥0 => (x : ℝ))
      (Real.toNNReal_of_nonneg
        (FourArcSquaredRecovery.recoveryScale_pos source n).le)
  have hscale :
      Tendsto
        (fun n : ℕ =>
          ((FourArcSquaredRecovery.recoveryScale source n).toNNReal : ℝ≥0∞))
        atTop (𝓝 0) := by
    simpa only [hscalePoint, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal
        (FourArcSquaredRecovery.tendsto_recoveryScale source)
  have herror :
      Tendsto
        (fun n : ℕ =>
          C * ((FourArcSquaredRecovery.recoveryScale source n).toNNReal :
            ℝ≥0∞))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hscale (Or.inr hC.ne)
  unfold SmoothSequence.cost
  change
    liminf (fun n =>
      smoothCost lam
        ((FourArcSquaredRecovery.recoverySequence source).carrier n))
      atTop ≤ _
  calc
    liminf (fun n =>
        smoothCost lam
          ((FourArcSquaredRecovery.recoverySequence source).carrier n))
        atTop ≤
      liminf
        (fun n => P +
          C * ((FourArcSquaredRecovery.recoveryScale source n).toNNReal :
            ℝ≥0∞)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hpoint)
    _ = liminf (fun _n : ℕ => P) atTop :=
      ENNReal.liminf_add_of_right_tendsto_zero herror (fun _n : ℕ => P)
    _ = P := by simp
    _ = ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure source.assembly.carrier)) := rfl

/-- The existing source recovery sequence witnesses the sharp relaxed
perimeter upper bound. -/
theorem relaxedPerimeter_le_frontierCost_source (hlam : 1 < lam) :
    relaxedPerimeter lam source.assembly.carrier ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter lam (FrontierMeasure source.assembly.carrier)) := by
  have hmeasurable : MeasurableSet source.assembly.carrier :=
    source.assembly.isClosed_carrier.measurableSet
  apply le_trans ?_ (recoverySequence_cost_le_frontierCost source hlam)
  unfold relaxedPerimeter
  apply sInf_le
  exact ⟨FourArcSquaredRecovery.recoverySequence source,
    hmeasurable.nullMeasurableSet,
    FourArcSquaredRecovery.recoverySequence_converges source, rfl⟩

/-- Assembly-level sharp recovery upper bound.  Unlike the canonical equality,
this theorem uses neither Snell incidence nor a common-radius identity. -/
theorem relaxedPerimeter_le_frontierCost (hlam : 1 < lam) :
    relaxedPerimeter lam source.assembly.carrier ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure source.assembly.carrier)) :=
  relaxedPerimeter_le_frontierCost_source source hlam


/-- The assembly-level recovery sequence, exposed without requiring callers to
manually package the strict-curvature hypothesis. -/
def assemblyRecoverySequence (assembly : FourArcAssembly)
    (hcurvature : assembly.core.curvature < 1) : SmoothSequence :=
  FourArcSquaredRecovery.recoverySequence
    ⟨assembly, hcurvature⟩

theorem assemblyRecoverySequence_converges
    (assembly : FourArcAssembly)
    (hcurvature : assembly.core.curvature < 1) :
    (assemblyRecoverySequence assembly hcurvature).ConvergesTo
      assembly.carrier :=
  FourArcSquaredRecovery.recoverySequence_converges
    ⟨assembly, hcurvature⟩

theorem assemblyRecoverySequence_cost_le
    (assembly : FourArcAssembly)
    (hcurvature : assembly.core.curvature < 1)
    (hlam : 1 < lam) :
    (assemblyRecoverySequence assembly hcurvature).cost lam ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure assembly.carrier)) :=
  recoverySequence_cost_le_frontierCost
    ⟨assembly, hcurvature⟩ hlam

theorem assembly_weightedArea_integrable
    (assembly : FourArcAssembly) :
    IntegrableOn (StripDensity lam) assembly.carrier :=
  FourArcAssembly.integrableOn_carrier lam assembly

theorem assembly_relaxedPerimeter_le_frontierCost
    (assembly : FourArcAssembly)
    (hcurvature : assembly.core.curvature < 1)
    (hlam : 1 < lam) :
    relaxedPerimeter lam assembly.carrier ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter lam
          (FrontierMeasure assembly.carrier)) :=
  relaxedPerimeter_le_frontierCost
    ⟨assembly, hcurvature⟩ hlam

theorem assembly_sourceAdmissible
    (assembly : FourArcAssembly)
    (hcurvature : assembly.core.curvature < 1)
    (hlam : 1 < lam) :
    (relaxedSourceSemantics lam).IsAdmissible assembly.carrier := by
  refine ⟨⟨assembly.isClosed_carrier.measurableSet.nullMeasurableSet, ?_⟩,
    assembly_weightedArea_integrable assembly⟩
  exact lt_of_le_of_lt
    (assembly_relaxedPerimeter_le_frontierCost assembly hcurvature hlam)
    ENNReal.ofReal_lt_top

end CMVRelaxation.FourArcSharpRecovery
