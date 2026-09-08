/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVSquaredWidthRecovery
import CMVCanonicalLowerBound

/-!
# Sharp squared-width recovery estimates

The shrinking junction traces must have length proportional to their width.
This module keeps that factor through the squared-width blend before charging
those traces in the relaxed-perimeter upper bound.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff BigOperators

noncomputable section

namespace CMVRelaxation.FrozenSquaredRecovery

/-- Square root is one-Lipschitz between arguments at least one. -/
lemma dist_sqrt_le_abs_sub_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    dist (√a) (√b) ≤ |a - b| := by
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hsa : 1 ≤ √a := Real.le_sqrt_of_sq_le (by simpa using ha)
  have hsb : 1 ≤ √b := Real.le_sqrt_of_sq_le (by simpa using hb)
  have hsum : 1 ≤ |√a + √b| := by
    rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith
  rw [Real.dist_eq]
  calc
    |√a - √b| ≤ |√a - √b| * |√a + √b| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hsum (abs_nonneg (√a - √b))
    _ = |a - b| := by
      rw [← abs_mul]
      congr 1
      nlinarith [Real.sq_sqrt ha0, Real.sq_sqrt hb0]

/-- Both actual squared widths, hence their junction blend, stay above their
common attachment value throughout either normalized junction band. -/
lemma normalizedJunctionQ_ge_fifteen_four
    {verticalSign : ℝ} (hvertical : |verticalSign| = 1)
    {z : PlanePoint} (hz : z ∈ normalizedJunctionBox) :
    15 / 4 ≤ normalizedJunctionQ verticalSign z := by
  have hh := normalizedJunctionHeight_mem hz
  have hhpos : 0 < normalizedJunctionHeight z :=
    lt_of_lt_of_le (by norm_num) hh.1
  let y := verticalSign * normalizedJunctionHeight z
  have habsy : |y| ∈ Icc (15 / 16 : ℝ) 1 := by
    dsimp [y]
    rw [abs_mul, hvertical, one_mul, abs_of_pos hhpos]
    exact hh
  have hysq : y ^ 2 ≤ 9 / 4 := by
    have hyabs_sq : |y| ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg y) (by norm_num)).2 habsy.2
    simpa [sq_abs] using hyabs_sq.trans (by norm_num)
  have hside : 15 / 4 ≤ sideSquare y := by
    rw [sideSquare_eq_actual hysq]
    have hrad : 0 ≤ 4 - y ^ 2 := by nlinarith [sq_nonneg y]
    have hroot : √3 ≤ √(4 - y ^ 2) := by
      apply Real.sqrt_le_sqrt
      have hyabs_sq : |y| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg y) (by norm_num)).2 habsy.2
      have hy2 : y ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using hyabs_sq
      linarith
    have h15 : (√15 : ℝ) ^ 2 = 15 := by norm_num
    have hbase0 : 0 ≤ (√15 : ℝ) / 2 := by positivity
    have hsum0 : 0 ≤ sideOffset + √(4 - y ^ 2) :=
      add_nonneg sideOffset_pos.le (Real.sqrt_nonneg _)
    have hbase_le : (√15 : ℝ) / 2 ≤ sideOffset + √(4 - y ^ 2) := by
      unfold sideOffset
      linarith
    have hsquares := (sq_le_sq₀ hbase0 hsum0).2 hbase_le
    nlinarith
  have hcap : 15 / 4 ≤ capSquare y := by
    rw [capSquare_eq_of_half_le_abs (by linarith [habsy.1])]
    nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr habsy.2)]
  let w := Real.smoothTransition (normalizedJunctionArgument z)
  have hw : w ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  rw [show normalizedJunctionQ verticalSign z =
      (1 - w) * sideSquare y + w * capSquare y by
    unfold normalizedJunctionQ y w
    ring]
  calc
    15 / 4 = (1 - w) * (15 / 4) + w * (15 / 4) := by ring
    _ ≤ (1 - w) * sideSquare y + w * capSquare y :=
      add_le_add
        (mul_le_mul_of_nonneg_left hside (sub_nonneg.mpr hw.2))
        (mul_le_mul_of_nonneg_left hcap hw.1)


/-- The normalized squared-width blend varies in its trace parameter by at
most a fixed constant times the junction width.  The proof uses exact
attachment at `y = ±1`; in particular the selector's `O(1)` variation is
multiplied by an `O(epsilon)` width gap. -/
theorem exists_scaled_normalizedJunctionQ_lipschitz
    {verticalSign : ℝ} (hvertical : |verticalSign| = 1) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 →
      LipschitzOnWith (K * epsilon.toNNReal)
        (fun t : ℝ => normalizedJunctionQ verticalSign (epsilon, t))
        (Icc (0 : ℝ) 1) := by
  have hsmoothSide : ContDiffOn ℝ 1 sideSquare (Icc (-1 : ℝ) 1) :=
    (contDiff_sideSquare.of_le (by simp)).contDiffOn
  rcases hsmoothSide.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (-1 : ℝ) 1) isCompact_Icc with
    ⟨Ks, hKs⟩
  have hsmoothCap : ContDiffOn ℝ 1 capSquare (Icc (-1 : ℝ) 1) :=
    (contDiff_capSquare.of_le (by simp)).contDiffOn
  rcases hsmoothCap.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (-1 : ℝ) 1) isCompact_Icc with
    ⟨Kc, hKc⟩
  have hweightSmooth : ContDiffOn ℝ 1
      (fun z : PlanePoint =>
        Real.smoothTransition (normalizedJunctionArgument z))
      normalizedJunctionBox :=
    Real.smoothTransition.contDiff.comp_contDiffOn
      contDiffOn_normalizedJunctionArgument
  rcases hweightSmooth.exists_lipschitzOnWith (by norm_num)
      (by
        simpa [normalizedJunctionBox] using
          (Convex.prod (𝕜 := ℝ)
            (convex_Icc (0 : ℝ) (1 / 16))
            (convex_Icc (0 : ℝ) 1) :
            Convex ℝ (Icc (0 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1)))
      (by
        simpa [normalizedJunctionBox] using
          (isCompact_Icc.prod isCompact_Icc :
            IsCompact
              (Icc (0 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1))) with
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
  have hzt : (epsilon, t) ∈ normalizedJunctionBox := by
    exact ⟨⟨hepsilon.le, hepsilon_le⟩, ht⟩
  have hzu : (epsilon, u) ∈ normalizedJunctionBox := by
    exact ⟨⟨hepsilon.le, hepsilon_le⟩, hu⟩
  let yt := verticalSign * normalizedJunctionHeight (epsilon, t)
  let yu := verticalSign * normalizedJunctionHeight (epsilon, u)
  have hht := normalizedJunctionHeight_mem hzt
  have hhu := normalizedJunctionHeight_mem hzu
  have hht0 : 0 < normalizedJunctionHeight (epsilon, t) :=
    lt_of_lt_of_le (by norm_num) hht.1
  have hhu0 : 0 < normalizedJunctionHeight (epsilon, u) :=
    lt_of_lt_of_le (by norm_num) hhu.1
  have habst : |yt| ∈ Icc (15 / 16 : ℝ) 1 := by
    dsimp [yt]
    rw [abs_mul, hvertical, one_mul, abs_of_pos hht0]
    exact hht
  have habsu : |yu| ∈ Icc (15 / 16 : ℝ) 1 := by
    dsimp [yu]
    rw [abs_mul, hvertical, one_mul, abs_of_pos hhu0]
    exact hhu
  have hyt : yt ∈ Icc (-1 : ℝ) 1 := (abs_le.mp habst.2)
  have hyu : yu ∈ Icc (-1 : ℝ) 1 := (abs_le.mp habsu.2)
  have hydist : |yt - yu| = epsilon * |t - u| := by
    dsimp [yt, yu, normalizedJunctionHeight]
    rw [show
        verticalSign * (1 - epsilon + epsilon * t) -
            verticalSign * (1 - epsilon + epsilon * u) =
          verticalSign * epsilon * (t - u) by ring,
      abs_mul, abs_mul, hvertical, abs_of_pos hepsilon, one_mul]
  have hside :
      |sideSquare yt - sideSquare yu| ≤
        (Ks : ℝ) * (epsilon * |t - u|) := by
    have h := hKs.dist_le_mul yt hyt yu hyu
    simpa only [Real.dist_eq, hydist] using h
  have hcap :
      |capSquare yt - capSquare yu| ≤
        (Kc : ℝ) * (epsilon * |t - u|) := by
    have h := hKc.dist_le_mul yt hyt yu hyu
    simpa only [Real.dist_eq, hydist] using h
  have hgapDiff :
      |(capSquare yt - sideSquare yt) -
          (capSquare yu - sideSquare yu)| ≤
        ((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|) := by
    calc
      |(capSquare yt - sideSquare yt) -
          (capSquare yu - sideSquare yu)| =
          |(capSquare yt - capSquare yu) -
            (sideSquare yt - sideSquare yu)| := by
              congr 1
              ring
      _ ≤ |capSquare yt - capSquare yu| +
          |sideSquare yt - sideSquare yu| := abs_sub _ _
      _ ≤ (Kc : ℝ) * (epsilon * |t - u|) +
          (Ks : ℝ) * (epsilon * |t - u|) :=
        add_le_add hcap hside
      _ = ((Kc : ℝ) + (Ks : ℝ)) * (epsilon * |t - u|) := by ring
  have hvertical_sq : verticalSign ^ 2 = 1 := by
    calc
      verticalSign ^ 2 = |verticalSign| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [hvertical]; norm_num
  have hsign : verticalSign = 1 ∨ verticalSign = -1 :=
    sq_eq_one_iff.mp hvertical_sq
  have hgapU :
      |capSquare yu - sideSquare yu| ≤
        ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by
    rcases hsign with hsign | hsign
    · have hyCenter : |yu - 1| ≤ epsilon := by
        rw [abs_le]
        dsimp [yu, normalizedJunctionHeight]
        rw [hsign]
        constructor <;> nlinarith [hu.1, hu.2]
      have hc := hKc.dist_le_mul yu hyu 1
        (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
      have hs := hKs.dist_le_mul yu hyu 1
        (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
      calc
        |capSquare yu - sideSquare yu| =
            |(capSquare yu - capSquare 1) -
              (sideSquare yu - sideSquare 1)| := by
                rw [capSquare_one, sideSquare_one]
                congr 1
                ring
        _ ≤ |capSquare yu - capSquare 1| +
            |sideSquare yu - sideSquare 1| := abs_sub _ _
        _ ≤ (Kc : ℝ) * |yu - 1| + (Ks : ℝ) * |yu - 1| := by
          simpa only [Real.dist_eq] using add_le_add hc hs
        _ ≤ (Kc : ℝ) * epsilon + (Ks : ℝ) * epsilon := by
          gcongr
        _ = ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by ring
    · have hyCenter : |yu - (-1)| ≤ epsilon := by
        rw [abs_le]
        dsimp [yu, normalizedJunctionHeight]
        rw [hsign]
        constructor <;> nlinarith [hu.1, hu.2]
      have hc := hKc.dist_le_mul yu hyu (-1)
        (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)
      have hs := hKs.dist_le_mul yu hyu (-1)
        (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)
      calc
        |capSquare yu - sideSquare yu| =
            |(capSquare yu - capSquare (-1)) -
              (sideSquare yu - sideSquare (-1))| := by
                rw [capSquare_neg_one, sideSquare_neg_one]
                congr 1
                ring
        _ ≤ |capSquare yu - capSquare (-1)| +
            |sideSquare yu - sideSquare (-1)| := abs_sub _ _
        _ ≤ (Kc : ℝ) * |yu - (-1)| +
            (Ks : ℝ) * |yu - (-1)| := by
          simpa only [Real.dist_eq] using add_le_add hc hs
        _ ≤ (Kc : ℝ) * epsilon + (Ks : ℝ) * epsilon := by
          gcongr
        _ = ((Kc : ℝ) + (Ks : ℝ)) * epsilon := by ring
  let wt := Real.smoothTransition
    (normalizedJunctionArgument (epsilon, t))
  let wu := Real.smoothTransition
    (normalizedJunctionArgument (epsilon, u))
  have hwt : |wt| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hweight :
      |wt - wu| ≤ (Kw : ℝ) * |t - u| := by
    have h := hKw.dist_le_mul (epsilon, t) hzt (epsilon, u) hzu
    simpa only [Real.dist_eq, Prod.dist_eq, sub_self, abs_zero,
      max_eq_right (abs_nonneg (t - u)), wt, wu] using h
  have hproduct :
      |wt * (capSquare yt - sideSquare yt) -
          wu * (capSquare yu - sideSquare yu)| ≤
        (((Kc : ℝ) + (Ks : ℝ)) +
          (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
            (epsilon * |t - u|) := by
    calc
      |wt * (capSquare yt - sideSquare yt) -
          wu * (capSquare yu - sideSquare yu)| =
          |wt * ((capSquare yt - sideSquare yt) -
              (capSquare yu - sideSquare yu)) +
            (wt - wu) * (capSquare yu - sideSquare yu)| := by
              congr 1
              ring
      _ ≤ |wt * ((capSquare yt - sideSquare yt) -
              (capSquare yu - sideSquare yu))| +
            |(wt - wu) * (capSquare yu - sideSquare yu)| := abs_add_le _ _
      _ = |wt| *
            |(capSquare yt - sideSquare yt) -
              (capSquare yu - sideSquare yu)| +
          |wt - wu| * |capSquare yu - sideSquare yu| := by
            rw [abs_mul, abs_mul]
      _ ≤ 1 * (((Kc : ℝ) + (Ks : ℝ)) *
              (epsilon * |t - u|)) +
          ((Kw : ℝ) * |t - u|) *
            (((Kc : ℝ) + (Ks : ℝ)) * epsilon) := by
              gcongr
      _ = (((Kc : ℝ) + (Ks : ℝ)) +
          (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
            (epsilon * |t - u|) := by ring
  have hq :
      |normalizedJunctionQ verticalSign (epsilon, t) -
          normalizedJunctionQ verticalSign (epsilon, u)| ≤
        C * (epsilon * |t - u|) := by
    change
      |sideSquare yt + wt * (capSquare yt - sideSquare yt) -
          (sideSquare yu + wu * (capSquare yu - sideSquare yu))| ≤ _
    calc
      |sideSquare yt + wt * (capSquare yt - sideSquare yt) -
          (sideSquare yu + wu * (capSquare yu - sideSquare yu))| =
          |(sideSquare yt - sideSquare yu) +
            (wt * (capSquare yt - sideSquare yt) -
              wu * (capSquare yu - sideSquare yu))| := by
                congr 1
                ring
      _ ≤ |sideSquare yt - sideSquare yu| +
          |wt * (capSquare yt - sideSquare yt) -
            wu * (capSquare yu - sideSquare yu)| := abs_add_le _ _
      _ ≤ (Ks : ℝ) * (epsilon * |t - u|) +
          (((Kc : ℝ) + (Ks : ℝ)) +
            (Kw : ℝ) * ((Kc : ℝ) + (Ks : ℝ))) *
              (epsilon * |t - u|) :=
        add_le_add hside hproduct
      _ = C * (epsilon * |t - u|) := by
        dsimp [C]
        ring
  calc
    dist (normalizedJunctionQ verticalSign (epsilon, t))
        (normalizedJunctionQ verticalSign (epsilon, u)) =
        |normalizedJunctionQ verticalSign (epsilon, t) -
          normalizedJunctionQ verticalSign (epsilon, u)| := Real.dist_eq _ _
    _ ≤ C * (epsilon * |t - u|) := hq
    _ = ((⟨C, hC⟩ : ℝ≥0) * epsilon.toNNReal : ℝ) * dist t u := by
      change C * (epsilon * |t - u|) =
        C * (epsilon.toNNReal : ℝ) * dist t u
      rw [Real.coe_toNNReal epsilon hepsilon.le, Real.dist_eq]
      ring

/-- The Euclidean product distance is bounded by the sum of its coordinate
distances. -/
lemma dist_planeEuclideanHomeomorph_le
    (x₁ y₁ x₂ y₂ : ℝ) :
    dist (planeEuclideanHomeomorph (x₁, y₁))
        (planeEuclideanHomeomorph (x₂, y₂)) ≤
      dist x₁ x₂ + dist y₁ y₂ := by
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change √(dist x₁ x₂ ^ 2 + dist y₁ y₂ ^ 2) ≤
    dist x₁ x₂ + dist y₁ y₂
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [mul_nonneg (dist_nonneg : 0 ≤ dist x₁ x₂)
      (dist_nonneg : 0 ≤ dist y₁ y₂)]

/-- Each actual normalized junction branch has Lipschitz constant proportional
to the shrinking junction width. -/
theorem exists_scaled_junction_lipschitz
    {horizontalSign verticalSign : ℝ}
    (hhorizontal : |horizontalSign| = 1)
    (hvertical : |verticalSign| = 1) :
    ∃ K : ℝ≥0, ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 →
      LipschitzOnWith (K * epsilon.toNNReal)
        (fun t : ℝ =>
          realizedNormalizedJunctionParam horizontalSign verticalSign
            (epsilon, t))
        (Icc (0 : ℝ) 1) := by
  rcases exists_scaled_normalizedJunctionQ_lipschitz hvertical with
    ⟨Kq, hKq⟩
  refine ⟨Kq + 1, ?_⟩
  intro epsilon hepsilon hepsilon_le
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  have hzt : (epsilon, t) ∈ normalizedJunctionBox :=
    ⟨⟨hepsilon.le, hepsilon_le⟩, ht⟩
  have hzu : (epsilon, u) ∈ normalizedJunctionBox :=
    ⟨⟨hepsilon.le, hepsilon_le⟩, hu⟩
  let qt := normalizedJunctionQ verticalSign (epsilon, t)
  let qu := normalizedJunctionQ verticalSign (epsilon, u)
  have hqt : 1 ≤ qt := by
    dsimp [qt]
    linarith [normalizedJunctionQ_ge_fifteen_four hvertical hzt]
  have hqu : 1 ≤ qu := by
    dsimp [qu]
    linarith [normalizedJunctionQ_ge_fifteen_four hvertical hzu]
  have hqdist :
      dist qt qu ≤
        ((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u :=
    (hKq hepsilon hepsilon_le).dist_le_mul t ht u hu
  have hsqrt :
      dist (√qt) (√qu) ≤
        ((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
    exact (dist_sqrt_le_abs_sub_of_one_le hqt hqu).trans
      (by simpa only [Real.dist_eq] using hqdist)
  have hx :
      dist (horizontalSign * √qt) (horizontalSign * √qu) ≤
        ((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
    rw [Real.dist_eq, show
      horizontalSign * √qt - horizontalSign * √qu =
        horizontalSign * (√qt - √qu) by ring, abs_mul, hhorizontal,
      one_mul]
    simpa only [Real.dist_eq] using hsqrt
  have hy :
      dist
          (verticalSign * normalizedJunctionHeight (epsilon, t))
          (verticalSign * normalizedJunctionHeight (epsilon, u)) =
        epsilon * dist t u := by
    rw [Real.dist_eq, Real.dist_eq, show
      verticalSign * normalizedJunctionHeight (epsilon, t) -
          verticalSign * normalizedJunctionHeight (epsilon, u) =
        verticalSign * epsilon * (t - u) by
          unfold normalizedJunctionHeight
          dsimp only
          ring,
      abs_mul, abs_mul, hvertical, abs_of_pos hepsilon, one_mul]
  calc
    dist
        (realizedNormalizedJunctionParam horizontalSign verticalSign
          (epsilon, t))
        (realizedNormalizedJunctionParam horizontalSign verticalSign
          (epsilon, u)) ≤
        dist (horizontalSign * √qt) (horizontalSign * √qu) +
          dist
            (verticalSign * normalizedJunctionHeight (epsilon, t))
            (verticalSign * normalizedJunctionHeight (epsilon, u)) := by
              apply dist_planeEuclideanHomeomorph_le
    _ ≤ ((Kq * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u +
          epsilon * dist t u :=
      add_le_add hx hy.le
    _ = (((Kq + 1) * epsilon.toNNReal : ℝ≥0) : ℝ) * dist t u := by
      simp only [NNReal.coe_mul, NNReal.coe_add,
        Real.coe_toNNReal epsilon hepsilon.le, NNReal.coe_one]
      ring

/-- The four junction lanes inside the retained eight-curve frontier cover. -/
def junctionCoverIndex (i : Fin 4) : Fin 8 :=
  ⟨i.1 + 2, by omega⟩

/-- All four actual junction traces used by `recoveryCoverCurve` retain the
same proportional-to-`epsilon` scale. -/
theorem exists_scaled_actual_junction_lipschitz :
    ∃ K : Fin 4 → ℝ≥0,
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 → ∀ i : Fin 4,
        LipschitzOnWith (K i * epsilon.toNNReal)
          (recoveryCoverCurve epsilon (junctionCoverIndex i))
          (Icc (0 : ℝ) 1) := by
  rcases exists_scaled_junction_lipschitz
      (horizontalSign := (-1 : ℝ)) (verticalSign := (-1 : ℝ))
      (by norm_num) (by norm_num) with
    ⟨K0, hK0⟩
  rcases exists_scaled_junction_lipschitz
      (horizontalSign := (1 : ℝ)) (verticalSign := (-1 : ℝ))
      (by norm_num) (by norm_num) with
    ⟨K1, hK1⟩
  rcases exists_scaled_junction_lipschitz
      (horizontalSign := (-1 : ℝ)) (verticalSign := (1 : ℝ))
      (by norm_num) (by norm_num) with
    ⟨K2, hK2⟩
  rcases exists_scaled_junction_lipschitz
      (horizontalSign := (1 : ℝ)) (verticalSign := (1 : ℝ))
      (by norm_num) (by norm_num) with
    ⟨K3, hK3⟩
  let K : Fin 4 → ℝ≥0 := fun i =>
    match i.1 with
    | 0 => K0
    | 1 => K1
    | 2 => K2
    | _ => K3
  refine ⟨K, ?_⟩
  intro epsilon hepsilon hepsilon_le i
  fin_cases i
  · change LipschitzOnWith (K0 * epsilon.toNNReal)
      (fun t : ℝ =>
        realizedNormalizedJunctionParam (-1) (-1) (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK0 hepsilon hepsilon_le
  · change LipschitzOnWith (K1 * epsilon.toNNReal)
      (fun t : ℝ =>
        realizedNormalizedJunctionParam 1 (-1) (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK1 hepsilon hepsilon_le
  · change LipschitzOnWith (K2 * epsilon.toNNReal)
      (fun t : ℝ =>
        realizedNormalizedJunctionParam (-1) 1 (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK2 hepsilon hepsilon_le
  · change LipschitzOnWith (K3 * epsilon.toNNReal)
      (fun t : ℝ =>
        realizedNormalizedJunctionParam 1 1 (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK3 hepsilon hepsilon_le

/-- The one-dimensional Hausdorff measure of each actual junction trace is
bounded by the same constant times `epsilon`. -/
theorem exists_scaled_actual_junction_hausdorffMeasure :
    ∃ K : Fin 4 → ℝ≥0,
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 → ∀ i : Fin 4,
        (μH[1] : Measure EuclideanPlane)
            (recoveryCoverCurve epsilon (junctionCoverIndex i) ''
              Icc (0 : ℝ) 1) ≤
          ((K i * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by
  rcases exists_scaled_actual_junction_lipschitz with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro epsilon hepsilon hepsilon_le i
  have hi :=
    (hK hepsilon hepsilon_le i).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num)
  simpa [ENNReal.rpow_one, hausdorffMeasure_real,
    Real.volume_Icc] using hi

/-- The union of all four actual junction traces has total Euclidean `H¹`
bounded by one finite coefficient times `epsilon`. -/
theorem exists_scaled_actual_junction_union_hausdorffMeasure :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 →
        (μH[1] : Measure EuclideanPlane)
            (⋃ i : Fin 4,
              recoveryCoverCurve epsilon (junctionCoverIndex i) ''
                Icc (0 : ℝ) 1) ≤
          C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases exists_scaled_actual_junction_hausdorffMeasure with ⟨K, hK⟩
  let C : ℝ≥0∞ := ∑ i : Fin 4, (K i : ℝ≥0∞)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [ENNReal.sum_lt_top]
    intro i hi
    exact ENNReal.coe_lt_top
  · intro epsilon hepsilon hepsilon_le
    calc
      (μH[1] : Measure EuclideanPlane)
          (⋃ i : Fin 4,
            recoveryCoverCurve epsilon (junctionCoverIndex i) ''
              Icc (0 : ℝ) 1) ≤
          ∑' i : Fin 4,
            (μH[1] : Measure EuclideanPlane)
              (recoveryCoverCurve epsilon (junctionCoverIndex i) ''
                Icc (0 : ℝ) 1) :=
        measure_iUnion_le _
      _ ≤ ∑' i : Fin 4,
          ((K i * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum (fun i => hK hepsilon hepsilon_le i)
      _ = ∑ i : Fin 4,
          ((K i * epsilon.toNNReal : ℝ≥0) : ℝ≥0∞) := by simp
      _ = C * (epsilon.toNNReal : ℝ≥0∞) := by
        dsimp [C]
        simp only [Finset.sum_mul]

end CMVRelaxation.FrozenSquaredRecovery

namespace CMVRelaxation.FrozenCanonicalCap

/-- Every point on the squared-width level of the frozen canonical carrier is
on its literal topological frontier.  The horizontal perturbation also covers
the two poles, where the half-width is zero. -/
lemma sq_eq_targetQ_mem_frontier {p : PlanePoint}
    (hp : p.1 ^ 2 = targetQ p.2) :
    p ∈ frontier profile.carrier := by
  have hpCarrier : p ∈ profile.carrier :=
    (mem_profile_iff_sq_le_targetQ p).2 hp.le
  rw [mem_frontier_iff_notMem_interior hpCarrier]
  intro hinterior
  have hnhds : interior profile.carrier ∈ nhds p :=
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
    have hzCarrier : z ∈ profile.carrier :=
      interior_subset (hball hzball)
    have hzle := (mem_profile_iff_sq_le_targetQ z).1 hzCarrier
    change (p.1 + r / 2) ^ 2 ≤ targetQ p.2 at hzle
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
    have hzCarrier : z ∈ profile.carrier :=
      interior_subset (hball hzball)
    have hzle := (mem_profile_iff_sq_le_targetQ z).1 hzCarrier
    change (p.1 - r / 2) ^ 2 ≤ targetQ p.2 at hzle
    nlinarith

/-- Union of the four actual moving junction traces in the retained recovery
cover. -/
def actualJunctionTrace (epsilon : ℝ) : Set EuclideanPlane :=
  ⋃ i : Fin 4,
    FrozenSquaredRecovery.recoveryCoverCurve epsilon
      (FrozenSquaredRecovery.junctionCoverIndex i) '' Icc (0 : ℝ) 1

/-- Literal frontier domination for the frozen recovery.  Outside the open
junction bands the squared-width equation is the actual canonical boundary
equation.  Inside them it is one of the four source-connected junction traces.
Thus the statement includes both junction endpoints and both poles. -/
theorem realized_frontier_subset_profile_union_actualJunctionTrace
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 16) :
    planeEuclideanHomeomorph ''
        frontier (FrozenSquaredRecovery.domain epsilon) ⊆
      planeEuclideanHomeomorph '' frontier profile.carrier ∪
        actualJunctionTrace epsilon := by
  rintro _ ⟨p, hpfrontier, rfl⟩
  have hpEq : p.1 ^ 2 = FrozenSquaredRecovery.q epsilon p.2 :=
    frontier_lt_subset_eq (continuous_fst.pow 2)
      ((FrozenSquaredRecovery.contDiff_q epsilon).continuous.comp continuous_snd)
      hpfrontier
  by_cases hjunction : 1 - epsilon < |p.2| ∧ |p.2| < 1
  · right
    have hqnonneg : 0 ≤ FrozenSquaredRecovery.q epsilon p.2 := by
      rw [← hpEq]
      positivity
    have hsqrt :
        (√(FrozenSquaredRecovery.q epsilon p.2)) ^ 2 =
          FrozenSquaredRecovery.q epsilon p.2 :=
      Real.sq_sqrt hqnonneg
    have hroot :
        p.1 = √(FrozenSquaredRecovery.q epsilon p.2) ∨
          p.1 = -√(FrozenSquaredRecovery.q epsilon p.2) := by
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
      have hqbridge :=
        FrozenSquaredRecovery.normalizedJunctionQ_eq_q
          (verticalSign := (1 : ℝ)) (t := t) (by norm_num) hepsilon
      rw [hheight, habsy, one_mul] at hqbridge
      rcases hroot with hright | hleft
      · apply Set.mem_iUnion.2
        refine ⟨(3 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change
          FrozenSquaredRecovery.realizedNormalizedJunctionParam
              1 1 (epsilon, t) =
            planeEuclideanHomeomorph p
        unfold FrozenSquaredRecovery.realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hright]
        · simp [hheight, habsy]
      · apply Set.mem_iUnion.2
        refine ⟨(2 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change
          FrozenSquaredRecovery.realizedNormalizedJunctionParam
              (-1) 1 (epsilon, t) =
            planeEuclideanHomeomorph p
        unfold FrozenSquaredRecovery.realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hleft]
        · simp [hheight, habsy]
    · have habsy : |p.2| = -p.2 := abs_of_nonpos hy0
      have hqbridge :=
        FrozenSquaredRecovery.normalizedJunctionQ_eq_q
          (verticalSign := (-1 : ℝ)) (t := t) (by norm_num) hepsilon
      rw [hheight, habsy] at hqbridge
      norm_num at hqbridge
      rcases hroot with hright | hleft
      · apply Set.mem_iUnion.2
        refine ⟨(1 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change
          FrozenSquaredRecovery.realizedNormalizedJunctionParam
              1 (-1) (epsilon, t) =
            planeEuclideanHomeomorph p
        unfold FrozenSquaredRecovery.realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hright]
        · simp [hheight, habsy]
      · apply Set.mem_iUnion.2
        refine ⟨(0 : Fin 4), ?_⟩
        refine ⟨t, ht, ?_⟩
        change
          FrozenSquaredRecovery.realizedNormalizedJunctionParam
              (-1) (-1) (epsilon, t) =
            planeEuclideanHomeomorph p
        unfold FrozenSquaredRecovery.realizedNormalizedJunctionParam
        apply congrArg planeEuclideanHomeomorph
        apply Prod.ext
        · simp [hqbridge, hleft]
        · simp [hheight, habsy]
  · left
    refine ⟨p, ?_, rfl⟩
    apply sq_eq_targetQ_mem_frontier
    rw [← recovery_q_eq_targetQ_outside_junction
      hepsilon hepsilon_le hjunction]
    exact hpEq


/-- `smoothCost` is the nonnegative density integral on the Euclidean
realization of the literal frontier. -/
lemma smoothCost_eq_euclidean_lintegral (lam : ℝ) (U : Set PlanePoint) :
    smoothCost lam U =
      ∫⁻ z in frontier (planeEuclideanHomeomorph '' U),
        ENNReal.ofReal (euclideanStripDensity lam z)
          ∂(μH[1] : Measure EuclideanPlane) := by
  unfold smoothCost FrontierMeasure
  change
    (∫⁻ p, (ENNReal.ofReal ∘ StripDensity lam) p
      ∂Measure.map planeEuclideanHomeomorph.symm
        ((μH[1] : Measure EuclideanPlane).restrict
          (frontier (planeEuclideanHomeomorph '' U)))) = _
  rw [MeasureTheory.lintegral_map
    (ENNReal.continuous_ofReal.measurable.comp (measurable_stripDensity lam))
    planeEuclideanHomeomorph.symm.continuous.measurable]
  rfl

/-- On the actual frozen canonical carrier, the extended nonnegative frontier
cost is exactly the `ENNReal.ofReal` of the retained real weighted perimeter. -/
theorem extended_frontierCost_eq_smoothCost_profile :
    ENNReal.ofReal
        (_root_.WeightedPerimeter 2 (FrontierMeasure profile.carrier)) =
      smoothCost 2 profile.carrier := by
  have hintegrable :
      Integrable (StripDensity 2) (FrontierMeasure profile.carrier) := by
    rw [profile.carrier_eq_candidate_assembly]
    exact FourArcAssembly.integrable_frontierMeasure
      2 profile.toCandidate.assembly
  have hnonneg :
      0 ≤ᵐ[FrontierMeasure profile.carrier] StripDensity 2 :=
    Eventually.of_forall (fun p => by
      unfold StripDensity
      split_ifs <;> norm_num)
  unfold _root_.WeightedPerimeter smoothCost
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hintegrable hnonneg

/-- The frozen smooth recovery pays the exact canonical frontier cost plus a
single vanishing junction error.  The coefficient is finite and independent of
the recovery scale. -/
theorem exists_sharp_smoothCost_domain_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 →
        smoothCost 2 (FrozenSquaredRecovery.domain epsilon) ≤
          ENNReal.ofReal
              (_root_.WeightedPerimeter 2
                (FrontierMeasure profile.carrier)) +
            C * (epsilon.toNNReal : ℝ≥0∞) := by
  rcases
      FrozenSquaredRecovery.exists_scaled_actual_junction_union_hausdorffMeasure
    with ⟨Cj, hCj, hJmeasure⟩
  refine ⟨2 * Cj, ENNReal.mul_lt_top (by norm_num) hCj, ?_⟩
  intro epsilon hepsilon hepsilon_le
  let μ : Measure EuclideanPlane := μH[1]
  let f : EuclideanPlane → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (euclideanStripDensity 2 z)
  have hfrontier :
      frontier
          (planeEuclideanHomeomorph ''
            FrozenSquaredRecovery.domain epsilon) ⊆
        frontier (planeEuclideanHomeomorph '' profile.carrier) ∪
          actualJunctionTrace epsilon := by
    simpa only [planeEuclideanHomeomorph.image_frontier] using
      realized_frontier_subset_profile_union_actualJunctionTrace
        hepsilon hepsilon_le
  have hJmeasure' :
      μ (actualJunctionTrace epsilon) ≤
        Cj * (epsilon.toNNReal : ℝ≥0∞) := by
    simpa only [μ, actualJunctionTrace] using
      hJmeasure hepsilon hepsilon_le
  have hJcost :
      (∫⁻ z in actualJunctionTrace epsilon, f z ∂μ) ≤
        2 * μ (actualJunctionTrace epsilon) := by
    calc
      (∫⁻ z in actualJunctionTrace epsilon, f z ∂μ) ≤
          ∫⁻ _z in actualJunctionTrace epsilon, (2 : ℝ≥0∞) ∂μ := by
        apply MeasureTheory.setLIntegral_mono measurable_const
        intro z _hz
        dsimp [f]
        unfold euclideanStripDensity StripDensity
        split_ifs <;> norm_num
      _ = 2 * μ (actualJunctionTrace epsilon) := by
        simp
  rw [smoothCost_eq_euclidean_lintegral]
  change (∫⁻ z in frontier
      (planeEuclideanHomeomorph ''
        FrozenSquaredRecovery.domain epsilon), f z ∂μ) ≤ _
  calc
    (∫⁻ z in frontier
        (planeEuclideanHomeomorph ''
          FrozenSquaredRecovery.domain epsilon), f z ∂μ) ≤
        ∫⁻ z in
          frontier (planeEuclideanHomeomorph '' profile.carrier) ∪
            actualJunctionTrace epsilon, f z ∂μ :=
      MeasureTheory.lintegral_mono_set hfrontier
    _ ≤
        (∫⁻ z in frontier
            (planeEuclideanHomeomorph '' profile.carrier), f z ∂μ) +
          ∫⁻ z in actualJunctionTrace epsilon, f z ∂μ :=
      MeasureTheory.lintegral_union_le _ _ _
    _ ≤ smoothCost 2 profile.carrier +
          2 * μ (actualJunctionTrace epsilon) := by
      rw [smoothCost_eq_euclidean_lintegral]
      exact add_le_add le_rfl hJcost
    _ =
        ENNReal.ofReal
            (_root_.WeightedPerimeter 2
              (FrontierMeasure profile.carrier)) +
          2 * μ (actualJunctionTrace epsilon) := by
      rw [extended_frontierCost_eq_smoothCost_profile]
    _ ≤
        ENNReal.ofReal
            (_root_.WeightedPerimeter 2
              (FrontierMeasure profile.carrier)) +
          (2 * Cj) * (epsilon.toNNReal : ℝ≥0∞) := by
      apply add_le_add le_rfl
      calc
        2 * μ (actualJunctionTrace epsilon) ≤
            2 * (Cj * (epsilon.toNNReal : ℝ≥0∞)) := by
          gcongr
        _ = (2 * Cj) * (epsilon.toNNReal : ℝ≥0∞) := by ring

/-- The retained frozen recovery sequence has liminf cost no larger than the
actual canonical complete-frontier cost.  The only excess in each term is the
finite junction coefficient times the scale, which tends to zero. -/
theorem recoverySequence_cost_le_frontierCost :
    recoverySequence.cost 2 ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter 2 (FrontierMeasure profile.carrier)) := by
  rcases exists_sharp_smoothCost_domain_bound with ⟨C, hC, hbound⟩
  let P : ℝ≥0∞ :=
    ENNReal.ofReal
      (_root_.WeightedPerimeter 2 (FrontierMeasure profile.carrier))
  have hpoint : ∀ n : ℕ,
      smoothCost 2 (recoverySequence.carrier n) ≤
        P + C * ((recoveryScale n).toNNReal : ℝ≥0∞) := by
    intro n
    simpa only [recoverySequence, P] using
      hbound (recoveryScale_pos n) (recoveryScale_le n)
  have hscalePoint (n : ℕ) :
      ((recoveryScale n).toNNReal : ℝ≥0∞) =
        ENNReal.ofReal (recoveryScale n) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (recoveryScale_pos n).le]
    congr 1
    ext
    exact congrArg (fun x : ℝ≥0 => (x : ℝ))
      (Real.toNNReal_of_nonneg (recoveryScale_pos n).le)
  have hscale :
      Tendsto
        (fun n : ℕ => ((recoveryScale n).toNNReal : ℝ≥0∞))
        atTop (𝓝 0) := by
    simpa only [hscalePoint, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_recoveryScale
  have herror :
      Tendsto
        (fun n : ℕ =>
          C * ((recoveryScale n).toNNReal : ℝ≥0∞))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hscale (Or.inr hC.ne)
  unfold SmoothSequence.cost
  change
    liminf (fun n => smoothCost 2 (recoverySequence.carrier n)) atTop ≤ _
  calc
    liminf (fun n => smoothCost 2 (recoverySequence.carrier n)) atTop ≤
        liminf
          (fun n => P +
            C * ((recoveryScale n).toNNReal : ℝ≥0∞)) atTop :=
      Filter.liminf_le_liminf (Eventually.of_forall hpoint)
    _ = liminf (fun _n : ℕ => P) atTop :=
      ENNReal.liminf_add_of_right_tendsto_zero herror (fun _n : ℕ => P)
    _ = P := by simp
    _ = ENNReal.ofReal
        (_root_.WeightedPerimeter 2
          (FrontierMeasure profile.carrier)) := rfl

/-- Literal frozen relaxed-perimeter upper bound, witnessed by the existing
globally convergent `SmoothSequence`. -/
theorem relaxedPerimeter_le_frontierCost_profile :
    relaxedPerimeter 2 profile.carrier ≤
      ENNReal.ofReal
        (_root_.WeightedPerimeter 2 (FrontierMeasure profile.carrier)) := by
  have hmeasurable : MeasurableSet profile.carrier := by
    rw [profile.carrier_eq_candidate_assembly]
    exact profile.toCandidate.assembly.isClosed_carrier.measurableSet
  apply le_trans ?_ recoverySequence_cost_le_frontierCost
  unfold relaxedPerimeter
  apply sInf_le
  exact ⟨recoverySequence, hmeasurable.nullMeasurableSet,
    recoverySequence_converges, rfl⟩

/-- Exact extended relaxed-perimeter equality for the frozen canonical
profile, obtained by combining the sharp recovery upper bound with the retained
universal four-arc lower bound. -/
theorem relaxedPerimeter_eq_frontierCost_profile :
    relaxedPerimeter 2 profile.carrier =
      ENNReal.ofReal
        (_root_.WeightedPerimeter 2 (FrontierMeasure profile.carrier)) :=
  le_antisymm relaxedPerimeter_le_frontierCost_profile
    (CanonicalFourArc.frontierCost_le_relaxedPerimeter profile)
end CMVRelaxation.FrozenCanonicalCap
