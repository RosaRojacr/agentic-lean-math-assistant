/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVProjectionDefect
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Squared-section-width recovery domains

A domain with centered horizontal sections can be written as
`{(x, y) | x^2 < q y}`.  Keeping the squared width smooth avoids square-root
singularities at the two poles.  The theorem below packages the resulting
single global defining function; regularity at a pole is supplied by the
nonzero derivative of `q` there.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff BigOperators

noncomputable section

namespace CMVRelaxation

/-- The open domain determined by a squared horizontal half-width. -/
def squaredWidthDomain (q : ℝ → ℝ) : Set PlanePoint :=
  {p | p.1 ^ 2 < q p.2}

/-- A globally smooth squared width with simple zeroes gives one global
one-sided regular defining function, including at points where the horizontal
half-width itself has a square-root pole. -/
theorem isSmoothDomain_squaredWidth
    {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q)
    (hregular : ∀ y, q y = 0 → deriv q y ≠ 0) :
    IsSmoothDomain (squaredWidthDomain q) := by
  have hqContinuous : Continuous q := hq.continuous
  constructor
  · exact isOpen_lt (continuous_fst.pow 2)
      (hqContinuous.comp continuous_snd)
  · intro p hp
    have hpEq : p.1 ^ 2 = q p.2 :=
      frontier_lt_subset_eq (continuous_fst.pow 2)
        (hqContinuous.comp continuous_snd) hp
    let D : PlanePoint →L[ℝ] ℝ :=
      (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ -
        (ContinuousLinearMap.toSpanSingleton ℝ (deriv q p.2)).comp
          (ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hqDifferentiable : Differentiable ℝ q :=
      hq.differentiable (by simp)
    have hqDeriv : HasDerivAt q (deriv q p.2) p.2 :=
      (hqDifferentiable p.2).hasDerivAt
    have hderiv :
        HasFDerivAt (fun z : PlanePoint => z.1 ^ 2 - q z.2) D p := by
      change HasFDerivAt
        ((fun z : PlanePoint => z.1 ^ 2) - q ∘ Prod.snd) D p
      simpa [D] using
        ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).sub
          (hqDeriv.hasFDerivAt.comp p
            (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
    have hD : D ≠ 0 := by
      intro hzero
      by_cases hx : p.1 = 0
      · have hqZero : q p.2 = 0 := by
          rw [hx] at hpEq
          simpa using hpEq.symm
        have happ := congrArg
          (fun L : PlanePoint →L[ℝ] ℝ => L (0, 1)) hzero
        have hdZero : deriv q p.2 = 0 := by
          simpa [D, hx] using happ
        exact (hregular p.2 hqZero) hdZero
      · have happ := congrArg
          (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hzero
        have hxZero : 2 * p.1 = 0 := by
          simpa [D] using happ
        exact hx (by linarith)
    refine ⟨Set.univ, (fun z : PlanePoint => z.1 ^ 2 - q z.2), D,
      isOpen_univ, Set.mem_univ p, ?_, ?_, hderiv, hD, ?_⟩
    · exact (contDiff_fst.pow 2).sub (hq.comp contDiff_snd) |>.contDiffOn
    · linarith
    · ext z
      change
        ((z.1 ^ 2 < q z.2) ∧ True) ↔
          (True ∧ z.1 ^ 2 - q z.2 < 0)
      constructor
      · rintro ⟨hz, -⟩
        exact ⟨trivial, sub_neg.mpr hz⟩
      · rintro ⟨-, hz⟩
        exact ⟨sub_neg.mp hz, trivial⟩


namespace FrozenSquaredRecovery

/-- A globally smooth replacement for `|y|` which agrees with it outside
`(-1/2, 1/2)`.  Only the exterior-cap lane uses this function. -/
def smoothAbs (y : ℝ) : ℝ :=
  y * (2 * Real.smoothTransition (y + 1 / 2) - 1)

lemma smoothAbs_eq_of_half_le_abs {y : ℝ} (hy : 1 / 2 ≤ |y|) :
    smoothAbs y = |y| := by
  rcases le_total 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0]
    have hhalf : 1 ≤ y + 1 / 2 := by
      rw [abs_of_nonneg hy0] at hy
      linarith
    rw [smoothAbs, Real.smoothTransition.one_of_one_le hhalf]
    ring
  · rw [abs_of_nonpos hy0]
    have hzero : y + 1 / 2 ≤ 0 := by
      rw [abs_of_nonpos hy0] at hy
      linarith
    rw [smoothAbs, Real.smoothTransition.zero_of_nonpos hzero]
    ring

lemma smoothAbs_eq_of_one_le_abs {y : ℝ} (hy : 1 ≤ |y|) :
    smoothAbs y = |y| :=
  smoothAbs_eq_of_half_le_abs (by linarith)

lemma contDiff_smoothAbs : ContDiff ℝ ∞ smoothAbs := by
  unfold smoothAbs
  have htransition : ContDiff ℝ ∞
      (fun y : ℝ => Real.smoothTransition (y + 1 / 2)) :=
    Real.smoothTransition.contDiff.comp
      (contDiff_id.add contDiff_const)
  have haffine : ContDiff ℝ ∞
      (fun y : ℝ => 2 * Real.smoothTransition (y + 1 / 2) - 1) :=
    (contDiff_const.mul htransition).sub contDiff_const
  exact contDiff_id.mul haffine

/-- The side-circle square coordinate is cut off before its square root could
reach zero.  It agrees with `y^2` throughout `[-3/2, 3/2]`. -/
def safeSquare (y : ℝ) : ℝ :=
  y ^ 2 *
    (1 - Real.smoothTransition (4 * (y ^ 2 - 9 / 4)))

lemma safeSquare_eq_sq {y : ℝ} (hy : y ^ 2 ≤ 9 / 4) :
    safeSquare y = y ^ 2 := by
  have harg : 4 * (y ^ 2 - 9 / 4) ≤ 0 := by linarith
  rw [safeSquare, Real.smoothTransition.zero_of_nonpos harg]
  ring

lemma safeSquare_mem_Icc (y : ℝ) :
    safeSquare y ∈ Icc (0 : ℝ) (5 / 2) := by
  have hχ0 :
      0 ≤ Real.smoothTransition (4 * (y ^ 2 - 9 / 4)) :=
    Real.smoothTransition.nonneg _
  have hχ1 :
      Real.smoothTransition (4 * (y ^ 2 - 9 / 4)) ≤ 1 :=
    Real.smoothTransition.le_one _
  by_cases hy : y ^ 2 ≤ 5 / 2
  · constructor
    · exact mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hχ1)
    · calc
        safeSquare y ≤ y ^ 2 * 1 := by
          unfold safeSquare
          exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg y)
        _ ≤ 5 / 2 := by simpa using hy
  · have harg : 1 ≤ 4 * (y ^ 2 - 9 / 4) := by
      simp only [not_le] at hy
      linarith
    rw [safeSquare, Real.smoothTransition.one_of_one_le harg]
    norm_num

lemma contDiff_safeSquare : ContDiff ℝ ∞ safeSquare := by
  unfold safeSquare
  have harg : ContDiff ℝ ∞ (fun y : ℝ => 4 * (y ^ 2 - 9 / 4)) :=
    contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const)
  have htransition : ContDiff ℝ ∞
      (fun y : ℝ =>
        Real.smoothTransition (4 * (y ^ 2 - 9 / 4))) :=
    Real.smoothTransition.contDiff.comp harg
  exact (contDiff_id.pow 2).mul (contDiff_const.sub htransition)

/-- Horizontal displacement of the frozen side-circle center. -/
def sideOffset : ℝ := √15 / 2 - √3

lemma sideOffset_pos : 0 < sideOffset := by
  have h15 : (√15 : ℝ) ^ 2 = 15 := by norm_num
  have h3 : (√3 : ℝ) ^ 2 = 3 := by norm_num
  have h15nonneg : 0 ≤ (√15 : ℝ) := Real.sqrt_nonneg _
  have h3nonneg : 0 ≤ (√3 : ℝ) := Real.sqrt_nonneg _
  unfold sideOffset
  nlinarith

/-- A globally smooth extension of the frozen strip-side squared half-width. -/
def sideSquare (y : ℝ) : ℝ :=
  (sideOffset + √(4 - safeSquare y)) ^ 2

lemma sideSquare_pos (y : ℝ) : 0 < sideSquare y := by
  have hrad : 0 < 4 - safeSquare y := by
    have := (safeSquare_mem_Icc y).2
    linarith
  unfold sideSquare
  exact sq_pos_of_pos (add_pos sideOffset_pos (Real.sqrt_pos.2 hrad))

lemma contDiff_sideSquare : ContDiff ℝ ∞ sideSquare := by
  have hrad : ∀ y, 4 - safeSquare y ≠ 0 := by
    intro y
    have := (safeSquare_mem_Icc y).2
    linarith
  unfold sideSquare
  exact
    (contDiff_const.add
      ((contDiff_const.sub contDiff_safeSquare).sqrt hrad)).pow 2

/-- Globally smooth exterior-cap squared half-width.  It is the actual cap
formula wherever `|y| ≥ 1`. -/
def capSquare (y : ℝ) : ℝ :=
  4 - (smoothAbs y - 1 / 2) ^ 2

lemma capSquare_eq_of_one_le_abs {y : ℝ} (hy : 1 ≤ |y|) :
    capSquare y = 4 - (|y| - 1 / 2) ^ 2 := by
  rw [capSquare, smoothAbs_eq_of_one_le_abs hy]

lemma contDiff_capSquare : ContDiff ℝ ∞ capSquare := by
  unfold capSquare
  exact contDiff_const.sub
    ((contDiff_smoothAbs.sub contDiff_const).pow 2)

/-- Smooth selector for the two junction bands
`1 - epsilon < |y| < 1`. -/
def junctionWeight (epsilon y : ℝ) : ℝ :=
  Real.smoothTransition
    ((y ^ 2 - (1 - epsilon) ^ 2) /
      (1 - (1 - epsilon) ^ 2))

/-- The frozen squared-width recovery profile. -/
def q (epsilon y : ℝ) : ℝ :=
  sideSquare y +
    junctionWeight epsilon y * (capSquare y - sideSquare y)

lemma junctionWeight_mem_Icc (epsilon y : ℝ) :
    junctionWeight epsilon y ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,
    Real.smoothTransition.le_one _⟩

lemma contDiff_q (epsilon : ℝ) : ContDiff ℝ ∞ (q epsilon) := by
  have hratio : ContDiff ℝ ∞
      (fun y : ℝ =>
        (y ^ 2 - (1 - epsilon) ^ 2) /
          (1 - (1 - epsilon) ^ 2)) :=
    ((contDiff_id.pow 2).sub contDiff_const).div_const _
  have hweight : ContDiff ℝ ∞ (junctionWeight epsilon) := by
    unfold junctionWeight
    exact Real.smoothTransition.contDiff.comp hratio
  unfold q
  exact contDiff_sideSquare.add
    (hweight.mul (contDiff_capSquare.sub contDiff_sideSquare))

lemma junctionDen_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    0 < 1 - (1 - epsilon) ^ 2 := by
  calc
    0 < epsilon * (2 - epsilon) :=
      mul_pos hepsilon (by linarith)
    _ = 1 - (1 - epsilon) ^ 2 := by ring

lemma junctionWeight_eq_zero {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : y ^ 2 ≤ (1 - epsilon) ^ 2) :
    junctionWeight epsilon y = 0 := by
  unfold junctionWeight
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy)
    (junctionDen_pos hepsilon hepsilon_le).le

lemma junctionWeight_eq_one {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : 1 ≤ y ^ 2) :
    junctionWeight epsilon y = 1 := by
  unfold junctionWeight
  apply Real.smoothTransition.one_of_one_le
  rw [one_le_div₀ (junctionDen_pos hepsilon hepsilon_le)]
  linarith

lemma sideSquare_eq_actual {y : ℝ} (hy : y ^ 2 ≤ 9 / 4) :
    sideSquare y = (sideOffset + √(4 - y ^ 2)) ^ 2 := by
  rw [sideSquare, safeSquare_eq_sq hy]

lemma capSquare_eq_of_half_le_abs {y : ℝ} (hy : 1 / 2 ≤ |y|) :
    capSquare y = 4 - (|y| - 1 / 2) ^ 2 := by
  rw [capSquare, smoothAbs_eq_of_half_le_abs hy]

lemma q_eq_side {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : y ^ 2 ≤ (1 - epsilon) ^ 2) :
    q epsilon y = sideSquare y := by
  rw [q, junctionWeight_eq_zero hepsilon hepsilon_le hy]
  ring

lemma q_eq_cap {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : 1 ≤ y ^ 2) :
    q epsilon y = capSquare y := by
  rw [q, junctionWeight_eq_one hepsilon hepsilon_le hy]
  ring

lemma q_pos_of_abs_lt_one {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : |y| < 1) :
    0 < q epsilon y := by
  have honeMinus : 0 ≤ 1 - epsilon := by linarith
  by_cases hcentral : |y| ≤ 1 - epsilon
  · have hsq : y ^ 2 ≤ (1 - epsilon) ^ 2 := by
      have :=
        (sq_le_sq₀ (abs_nonneg y) honeMinus).2 hcentral
      simpa [sq_abs] using this
    rw [q_eq_side hepsilon hepsilon_le hsq]
    exact sideSquare_pos y
  · have hhalf : 1 / 2 ≤ |y| := by
      simp only [not_le] at hcentral
      linarith
    have hcap : 0 < capSquare y := by
      rw [capSquare_eq_of_half_le_abs hhalf]
      nlinarith [sq_nonneg (|y| - 1 / 2)]
    let w := junctionWeight epsilon y
    have hw : w ∈ Icc (0 : ℝ) 1 :=
      junctionWeight_mem_Icc epsilon y
    have hrewrite :
        q epsilon y =
          (1 - w) * sideSquare y + w * capSquare y := by
      unfold q w
      ring
    rw [hrewrite]
    by_cases hwOne : w = 1
    · rw [hwOne]
      simpa using hcap
    · have hwLt : w < 1 := lt_of_le_of_ne hw.2 hwOne
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hwLt) (sideSquare_pos y))
        (mul_nonneg hw.1 hcap.le)

lemma one_le_abs_of_q_eq_zero {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : q epsilon y = 0) :
    1 ≤ |y| := by
  by_contra hnot
  exact (q_pos_of_abs_lt_one hepsilon hepsilon_le
    (lt_of_not_ge hnot)).ne' hy

lemma abs_eq_five_halves_of_q_eq_zero {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : q epsilon y = 0) :
    |y| = 5 / 2 := by
  have habs := one_le_abs_of_q_eq_zero hepsilon hepsilon_le hy
  have hsq : 1 ≤ y ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 habs
    simpa [sq_abs] using hsquare
  rw [q_eq_cap hepsilon hepsilon_le hsq,
    capSquare_eq_of_one_le_abs habs] at hy
  have hnonneg : 0 ≤ |y| - 1 / 2 := by linarith
  nlinarith

lemma q_eq_zero_iff {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    q epsilon y = 0 ↔ y = -(5 / 2) ∨ y = 5 / 2 := by
  constructor
  · intro hy
    have habs :=
      abs_eq_five_halves_of_q_eq_zero hepsilon hepsilon_le hy
    rcases le_total 0 y with hy0 | hy0
    · right
      rwa [abs_of_nonneg hy0] at habs
    · left
      rw [abs_of_nonpos hy0] at habs
      linarith
  · rintro (rfl | rfl)
    · have hsq : 1 ≤ (-(5 / 2 : ℝ)) ^ 2 := by norm_num
      rw [q_eq_cap hepsilon hepsilon_le hsq, capSquare,
        smoothAbs_eq_of_one_le_abs (by norm_num : 1 ≤ |-(5 / 2 : ℝ)|)]
      norm_num
    · have hsq : 1 ≤ (5 / 2 : ℝ) ^ 2 := by norm_num
      rw [q_eq_cap hepsilon hepsilon_le hsq, capSquare,
        smoothAbs_eq_of_one_le_abs (by norm_num : 1 ≤ |(5 / 2 : ℝ)|)]
      norm_num

lemma q_eventuallyEq_upperCap {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    q epsilon =ᶠ[𝓝 (5 / 2 : ℝ)]
      (fun y : ℝ => 4 - (y - 1 / 2) ^ 2) := by
  filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < 5 / 2 by norm_num)] with y hy
  change (1 : ℝ) < y at hy
  have hy0 : 0 ≤ y := by linarith
  have hsquare :
      (1 : ℝ) ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hy0).2 hy.le
  have hsq : 1 ≤ y ^ 2 := by norm_num at hsquare ⊢; exact hsquare
  rw [q_eq_cap hepsilon hepsilon_le hsq, capSquare,
    smoothAbs_eq_of_half_le_abs]
  · rw [abs_of_nonneg hy0]
  · rw [abs_of_nonneg hy0]
    linarith

lemma q_eventuallyEq_lowerCap {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    q epsilon =ᶠ[𝓝 (-(5 / 2) : ℝ)]
      (fun y : ℝ => 4 - (y + 1 / 2) ^ 2) := by
  filter_upwards [Iio_mem_nhds (show (-(5 / 2) : ℝ) < -1 by norm_num)] with y hy
  change y < (-1 : ℝ) at hy
  have hy0 : y ≤ 0 := by linarith
  have hsq : 1 ≤ y ^ 2 := by
    have habs : 1 ≤ |y| := by
      rw [abs_of_nonpos hy0]
      linarith
    have hsquare :
        (1 : ℝ) ^ 2 ≤ |y| ^ 2 :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 habs
    simpa [sq_abs] using hsquare
  rw [q_eq_cap hepsilon hepsilon_le hsq, capSquare,
    smoothAbs_eq_of_half_le_abs]
  · rw [abs_of_nonpos hy0]
    ring
  · rw [abs_of_nonpos hy0]
    linarith

lemma hasDerivAt_q_upperPole {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    HasDerivAt (q epsilon) (-4) (5 / 2) := by
  have hpoly : HasDerivAt
      (fun y : ℝ => 4 - (y - 1 / 2) ^ 2) (-4) (5 / 2) := by
    have hraw := (hasDerivAt_const (5 / 2 : ℝ) (4 : ℝ)).sub
      (((hasDerivAt_id (5 / 2 : ℝ)).sub_const (1 / 2)).pow 2)
    norm_num at hraw ⊢
    simpa only [Pi.sub_apply] using! hraw
  exact hpoly.congr_of_eventuallyEq
    (q_eventuallyEq_upperCap hepsilon hepsilon_le)

lemma hasDerivAt_q_lowerPole {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    HasDerivAt (q epsilon) 4 (-(5 / 2)) := by
  have hpoly : HasDerivAt
      (fun y : ℝ => 4 - (y + 1 / 2) ^ 2) 4 (-(5 / 2)) := by
    have hraw := (hasDerivAt_const (-(5 / 2) : ℝ) (4 : ℝ)).sub
      (((hasDerivAt_id (-(5 / 2) : ℝ)).add_const (1 / 2)).pow 2)
    norm_num at hraw ⊢
    simpa only [Pi.sub_apply] using! hraw
  exact hpoly.congr_of_eventuallyEq
    (q_eventuallyEq_lowerCap hepsilon hepsilon_le)

lemma q_regularZeros {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    ∀ y, q epsilon y = 0 → deriv (q epsilon) y ≠ 0 := by
  intro y hy
  rcases (q_eq_zero_iff hepsilon hepsilon_le).1 hy with rfl | rfl
  · rw [(hasDerivAt_q_lowerPole hepsilon hepsilon_le).deriv]
    norm_num
  · rw [(hasDerivAt_q_upperPole hepsilon hepsilon_le).deriv]
    norm_num

/-- The actual frozen recovery domain. -/
def domain (epsilon : ℝ) : Set PlanePoint :=
  squaredWidthDomain (q epsilon)

/-- Every positive recovery scale through `1/16` gives one actual
`IsSmoothDomain`.  Its global defining function covers both poles and all four
ends of the two smooth transition bands. -/
theorem isSmoothDomain_domain {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    IsSmoothDomain (domain epsilon) := by
  unfold domain
  exact isSmoothDomain_squaredWidth (contDiff_q epsilon)
    (q_regularZeros hepsilon hepsilon_le)

lemma q_pos_iff_abs_lt_five_halves {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    0 < q epsilon y ↔ |y| < 5 / 2 := by
  constructor
  · intro hq
    by_contra hnot
    have habs : 5 / 2 ≤ |y| := le_of_not_gt hnot
    have hone : 1 ≤ |y| := by linarith
    have hsquare :
        (1 : ℝ) ^ 2 ≤ |y| ^ 2 :=
      (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 hone
    have hsq : 1 ≤ y ^ 2 := by simpa [sq_abs] using hsquare
    rw [q_eq_cap hepsilon hepsilon_le hsq,
      capSquare_eq_of_one_le_abs hone] at hq
    nlinarith [sq_nonneg (|y| - 1 / 2)]
  · intro hy
    by_cases hone : |y| < 1
    · exact q_pos_of_abs_lt_one hepsilon hepsilon_le hone
    · have hone' : 1 ≤ |y| := le_of_not_gt hone
      have hsquare :
          (1 : ℝ) ^ 2 ≤ |y| ^ 2 :=
        (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 hone'
      have hsq : 1 ≤ y ^ 2 := by simpa [sq_abs] using hsquare
      rw [q_eq_cap hepsilon hepsilon_le hsq,
        capSquare_eq_of_one_le_abs hone']
      nlinarith [sq_nonneg (|y| - 1 / 2)]

lemma domain_has_point_at_height_iff {epsilon y : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    (∃ x : ℝ, (x, y) ∈ domain epsilon) ↔ |y| < 5 / 2 := by
  rw [← q_pos_iff_abs_lt_five_halves hepsilon hepsilon_le]
  constructor
  · rintro ⟨x, hx⟩
    change x ^ 2 < q epsilon y at hx
    exact (sq_nonneg x).trans_lt hx
  · intro hq
    exact ⟨0, by simpa [domain, squaredWidthDomain] using hq⟩

lemma sideSquare_one : sideSquare 1 = 15 / 4 := by
  rw [sideSquare_eq_actual (by norm_num : (1 : ℝ) ^ 2 ≤ 9 / 4)]
  unfold sideOffset
  norm_num
  rw [div_pow]
  norm_num

lemma sideSquare_neg_one : sideSquare (-1) = 15 / 4 := by
  rw [sideSquare_eq_actual (by norm_num : (-1 : ℝ) ^ 2 ≤ 9 / 4)]
  unfold sideOffset
  norm_num
  rw [div_pow]
  norm_num

lemma capSquare_one : capSquare 1 = 15 / 4 := by
  rw [capSquare_eq_of_half_le_abs (by norm_num : 1 / 2 ≤ |(1 : ℝ)|)]
  norm_num

lemma capSquare_neg_one : capSquare (-1) = 15 / 4 := by
  rw [capSquare_eq_of_half_le_abs (by norm_num : 1 / 2 ≤ |(-1 : ℝ)|)]
  norm_num

/-- The quotient introduced by an epsilon-scaled cutoff stays uniformly
bounded when the two blended functions agree at the junction.  This is the
value cancellation required by the recovery construction; no estimate of
`1 / epsilon` is discarded. -/
theorem junction_value_cancellation
    {f g : ℝ → ℝ} {center epsilon y Lf Lg : ℝ}
    (hepsilon : 0 < epsilon) (hLf : 0 ≤ Lf) (hLg : 0 ≤ Lg)
    (hy : |y - center| ≤ epsilon)
    (hf : |f y - f center| ≤ Lf * |y - center|)
    (hg : |g y - g center| ≤ Lg * |y - center|)
    (hjoin : f center = g center) :
    |(g y - f y) / epsilon| ≤ Lf + Lg := by
  rw [abs_div, abs_of_pos hepsilon, div_le_iff₀ hepsilon]
  calc
    |g y - f y| =
        |(g y - g center) - (f y - f center)| := by
          rw [hjoin]
          ring
    _ ≤ |g y - g center| + |f y - f center| := abs_sub _ _
    _ ≤ Lg * |y - center| + Lf * |y - center| :=
      add_le_add hg hf
    _ = (Lf + Lg) * |y - center| := by ring
    _ ≤ (Lf + Lg) * epsilon :=
      mul_le_mul_of_nonneg_left hy (add_nonneg hLf hLg)
    _ = (Lf + Lg) * epsilon := rfl

/-- Right branch of the recovery boundary level. -/
def rightBoundaryParam (epsilon y : ℝ) : PlanePoint := (√(q epsilon y), y)

/-- Left branch of the recovery boundary level. -/
def leftBoundaryParam (epsilon y : ℝ) : PlanePoint := (-√(q epsilon y), y)

/-- The complete frontier lies in two compact square-root graph traces. -/
theorem frontier_domain_subset_boundaryParams {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 16) :
    frontier (domain epsilon) ⊆
      leftBoundaryParam epsilon '' Icc (-(5 / 2)) (5 / 2) ∪
      rightBoundaryParam epsilon '' Icc (-(5 / 2)) (5 / 2) := by
  intro p hp
  have hpEq : p.1 ^ 2 = q epsilon p.2 :=
    frontier_lt_subset_eq (continuous_fst.pow 2)
      ((contDiff_q epsilon).continuous.comp continuous_snd) hp
  have hqnonneg : 0 ≤ q epsilon p.2 := by
    rw [← hpEq]
    positivity
  have hy : p.2 ∈ Icc (-(5 / 2 : ℝ)) (5 / 2) := by
    by_cases hqzero : q epsilon p.2 = 0
    · rcases (q_eq_zero_iff hepsilon hepsilon_le).1 hqzero with hy | hy
      · rw [hy]
        norm_num
      · rw [hy]
        norm_num
    · have hqpos : 0 < q epsilon p.2 :=
        lt_of_le_of_ne hqnonneg (Ne.symm hqzero)
      exact ⟨(abs_lt.mp
        ((q_pos_iff_abs_lt_five_halves hepsilon hepsilon_le).1 hqpos)).1.le,
        (abs_lt.mp
        ((q_pos_iff_abs_lt_five_halves hepsilon hepsilon_le).1 hqpos)).2.le⟩
  have hsqrt : (√(q epsilon p.2)) ^ 2 = q epsilon p.2 :=
    Real.sq_sqrt hqnonneg
  have hroot : p.1 = √(q epsilon p.2) ∨
      p.1 = -√(q epsilon p.2) := by
    rw [← hsqrt] at hpEq
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hpEq
  rcases hroot with hright | hleft
  · right
    refine ⟨p.2, hy, ?_⟩
    ext <;> simp [rightBoundaryParam, hright]
  · left
    refine ⟨p.2, hy, ?_⟩
    ext <;> simp [leftBoundaryParam, hleft]
/-- Height coordinate on a normalized positive junction band. -/
def normalizedJunctionHeight (z : PlanePoint) : ℝ :=
  1 - z.1 + z.1 * z.2

/-- Pole-free argument of the transition cutoff after the junction-band
coordinate is normalized to `[0,1]`. -/
def normalizedJunctionArgument (z : PlanePoint) : ℝ :=
  z.2 * (2 * (1 - z.1) + z.1 * z.2) / (2 - z.1)

/-- Pole-free squared width along either normalized junction band. -/
def normalizedJunctionQ (verticalSign : ℝ) (z : PlanePoint) : ℝ :=
  let y := verticalSign * normalizedJunctionHeight z
  sideSquare y + Real.smoothTransition (normalizedJunctionArgument z) *
    (capSquare y - sideSquare y)

/-- Euclidean realization of one of the four junction-boundary branches. -/
def realizedNormalizedJunctionParam (horizontalSign verticalSign : ℝ)
    (z : PlanePoint) : EuclideanPlane :=
  planeEuclideanHomeomorph
    (horizontalSign * √(normalizedJunctionQ verticalSign z),
      verticalSign * normalizedJunctionHeight z)

lemma normalizedJunctionHeight_mem
    {z : PlanePoint} (hz : z ∈ Icc (0 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1) :
    normalizedJunctionHeight z ∈ Icc (15 / 16 : ℝ) 1 := by
  rcases hz with ⟨he, ht⟩
  simp only [mem_Icc] at he ht ⊢
  unfold normalizedJunctionHeight
  constructor <;> nlinarith

lemma normalizedJunctionArgument_eq
    {epsilon t : ℝ} (hepsilon : 0 < epsilon) :
    normalizedJunctionArgument (epsilon, t) =
      (((1 - epsilon + epsilon * t) ^ 2 - (1 - epsilon) ^ 2) /
        (1 - (1 - epsilon) ^ 2)) := by
  unfold normalizedJunctionArgument
  dsimp only
  rw [show 1 - (1 - epsilon) ^ 2 = epsilon * (2 - epsilon) by ring]
  field_simp [hepsilon.ne']
  ring

lemma normalizedJunctionQ_eq_q
    {verticalSign epsilon t : ℝ}
    (hvertical : verticalSign ^ 2 = 1) (hepsilon : 0 < epsilon) :
    normalizedJunctionQ verticalSign (epsilon, t) =
      q epsilon
        (verticalSign * normalizedJunctionHeight (epsilon, t)) := by
  unfold normalizedJunctionQ q junctionWeight
  dsimp only
  rw [normalizedJunctionArgument_eq hepsilon]
  congr 2
  rw [mul_pow, hvertical, one_mul]
  unfold normalizedJunctionHeight
  dsimp only


/-- The difference of the two junction widths divided by the shrinking band
width is uniformly bounded on both bands.  This is the explicit
junction-value cancellation; no bare `1 / epsilon` estimate is used. -/
theorem exists_uniform_junction_gap_quotient_bound :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ ⦃epsilon y : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 →
        y ∈ Icc (-1 : ℝ) 1 →
        (|y - 1| ≤ epsilon →
          |(capSquare y - sideSquare y) / epsilon| ≤ L) ∧
        (|y - (-1)| ≤ epsilon →
          |(capSquare y - sideSquare y) / epsilon| ≤ L) := by
  have hsmoothSide : ContDiffOn ℝ 1 sideSquare (Icc (-1 : ℝ) 1) :=
    (contDiff_sideSquare.of_le (by simp)).contDiffOn
  have hsmoothCap : ContDiffOn ℝ 1 capSquare (Icc (-1 : ℝ) 1) :=
    (contDiff_capSquare.of_le (by simp)).contDiffOn
  rcases hsmoothSide.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (-1 : ℝ) 1) isCompact_Icc with ⟨Ks, hKs⟩
  rcases hsmoothCap.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (-1 : ℝ) 1) isCompact_Icc with ⟨Kc, hKc⟩
  refine ⟨(Ks : ℝ) + (Kc : ℝ), by positivity, ?_⟩
  intro epsilon y hepsilon _hepsilon_le hy
  have hsideUpper :
      |sideSquare y - sideSquare 1| ≤
        (Ks : ℝ) * |y - 1| := by
    simpa [Real.dist_eq] using
      hKs.dist_le_mul y hy 1 (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
  have hcapUpper :
      |capSquare y - capSquare 1| ≤
        (Kc : ℝ) * |y - 1| := by
    simpa [Real.dist_eq] using
      hKc.dist_le_mul y hy 1 (by norm_num : (1 : ℝ) ∈ Icc (-1) 1)
  have hsideLower :
      |sideSquare y - sideSquare (-1)| ≤
        (Ks : ℝ) * |y - (-1)| := by
    simpa [Real.dist_eq] using
      hKs.dist_le_mul y hy (-1 : ℝ)
        (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)
  have hcapLower :
      |capSquare y - capSquare (-1)| ≤
        (Kc : ℝ) * |y - (-1)| := by
    simpa [Real.dist_eq] using
      hKc.dist_le_mul y hy (-1 : ℝ)
        (by norm_num : (-1 : ℝ) ∈ Icc (-1) 1)
  constructor
  · intro hyUpper
    simpa only [add_comm] using
      (junction_value_cancellation
        (f := sideSquare) (g := capSquare) (center := (1 : ℝ))
        hepsilon (by positivity) (by positivity) hyUpper
        hsideUpper hcapUpper
        (sideSquare_one.trans capSquare_one.symm))
  · intro hyLower
    simpa only [add_comm] using
      (junction_value_cancellation
        (f := sideSquare) (g := capSquare) (center := (-1 : ℝ))
        hepsilon (by positivity) (by positivity) hyLower
        hsideLower hcapLower
        (sideSquare_neg_one.trans capSquare_neg_one.symm))
def normalizedJunctionBox : Set PlanePoint :=
  Icc (0 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1

lemma normalizedJunctionQ_pos
    {verticalSign : ℝ} (hvertical : |verticalSign| = 1)
    {z : PlanePoint} (hz : z ∈ normalizedJunctionBox) :
    0 < normalizedJunctionQ verticalSign z := by
  have hh := normalizedJunctionHeight_mem hz
  have hhpos : 0 < normalizedJunctionHeight z :=
    lt_of_lt_of_le (by norm_num) hh.1
  have habsy :
      |verticalSign * normalizedJunctionHeight z| ∈
        Icc (15 / 16 : ℝ) 1 := by
    rw [abs_mul, hvertical, one_mul, abs_of_pos hhpos]
    exact hh
  have hcap : 0 < capSquare
      (verticalSign * normalizedJunctionHeight z) := by
    rw [capSquare_eq_of_half_le_abs (by linarith [habsy.1])]
    nlinarith [habsy.1, habsy.2,
      sq_nonneg (|verticalSign * normalizedJunctionHeight z| - 1 / 2)]
  let w := Real.smoothTransition (normalizedJunctionArgument z)
  have hw : w ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _,
      Real.smoothTransition.le_one _⟩
  have hside := sideSquare_pos
    (verticalSign * normalizedJunctionHeight z)
  rw [show normalizedJunctionQ verticalSign z =
      (1 - w) * sideSquare
          (verticalSign * normalizedJunctionHeight z) +
        w * capSquare
          (verticalSign * normalizedJunctionHeight z) by
    unfold normalizedJunctionQ w
    ring]
  by_cases hwOne : w = 1
  · rw [hwOne]
    simpa using hcap
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hw.2 hwOne)) hside)
      (mul_nonneg hw.1 hcap.le)

lemma contDiff_normalizedJunctionHeight :
    ContDiff ℝ ∞ normalizedJunctionHeight := by
  unfold normalizedJunctionHeight
  exact (contDiff_const.sub contDiff_fst).add
    (contDiff_fst.mul contDiff_snd)

lemma contDiffOn_normalizedJunctionArgument :
    ContDiffOn ℝ 1 normalizedJunctionArgument normalizedJunctionBox := by
  unfold normalizedJunctionArgument normalizedJunctionBox
  apply ContDiffOn.div
  · exact (contDiff_snd.mul
      ((contDiff_const.mul (contDiff_const.sub contDiff_fst)).add
        (contDiff_fst.mul contDiff_snd))).contDiffOn
  · exact (contDiff_const.sub contDiff_fst).contDiffOn
  · rintro z ⟨hepsilon, _⟩
    simp only [mem_Icc] at hepsilon
    linarith

lemma contDiffOn_normalizedJunctionQ
    {verticalSign : ℝ} :
    ContDiffOn ℝ 1 (normalizedJunctionQ verticalSign)
      normalizedJunctionBox := by
  have hy : ContDiff ℝ 1
      (fun z : PlanePoint =>
        verticalSign * normalizedJunctionHeight z) :=
    contDiff_const.mul
      (contDiff_normalizedJunctionHeight.of_le (by simp))
  have hs : ContDiff ℝ 1
      (fun z : PlanePoint =>
        sideSquare (verticalSign * normalizedJunctionHeight z)) :=
    (contDiff_sideSquare.of_le (by simp)).comp hy
  have hc : ContDiff ℝ 1
      (fun z : PlanePoint =>
        capSquare (verticalSign * normalizedJunctionHeight z)) :=
    (contDiff_capSquare.of_le (by simp)).comp hy
  have hw : ContDiffOn ℝ 1
      (fun z : PlanePoint =>
        Real.smoothTransition (normalizedJunctionArgument z))
      normalizedJunctionBox :=
    Real.smoothTransition.contDiff.comp_contDiffOn
      contDiffOn_normalizedJunctionArgument
  unfold normalizedJunctionQ
  exact hs.contDiffOn.add
    (hw.mul (hc.contDiffOn.sub hs.contDiffOn))

lemma contDiffOn_realizedNormalizedJunctionParam
    {horizontalSign verticalSign : ℝ}
    (hvertical : |verticalSign| = 1) :
    ContDiffOn ℝ 1
      (realizedNormalizedJunctionParam horizontalSign verticalSign)
      normalizedJunctionBox := by
  have hq : ContDiffOn ℝ 1
      (fun z : PlanePoint => √(normalizedJunctionQ verticalSign z))
      normalizedJunctionBox :=
    contDiffOn_normalizedJunctionQ.sqrt
      (fun z hz => (normalizedJunctionQ_pos hvertical hz).ne')
  have hy : ContDiff ℝ 1
      (fun z : PlanePoint =>
        verticalSign * normalizedJunctionHeight z) :=
    contDiff_const.mul
      (contDiff_normalizedJunctionHeight.of_le (by simp))
  unfold realizedNormalizedJunctionParam
  rw [show (fun z : PlanePoint =>
      planeEuclideanHomeomorph
        (horizontalSign * √(normalizedJunctionQ verticalSign z),
          verticalSign * normalizedJunctionHeight z)) =
      WithLp.toLp 2 ∘
        (fun z : PlanePoint =>
          (horizontalSign * √(normalizedJunctionQ verticalSign z),
            verticalSign * normalizedJunctionHeight z)) by rfl]
  exact WithLp.contDiff_toLp.comp_contDiffOn
    ((contDiff_const.contDiffOn.mul hq).prodMk hy.contDiffOn)

lemma exists_uniform_junction_lipschitz
    {horizontalSign verticalSign : ℝ}
    (hvertical : |verticalSign| = 1) :
    ∃ K : ℝ≥0, ∀ epsilon ∈ Icc (0 : ℝ) (1 / 16),
      LipschitzOnWith K
        (fun t : ℝ =>
          realizedNormalizedJunctionParam horizontalSign verticalSign
            (epsilon, t))
        (Icc (0 : ℝ) 1) := by
  rcases
      (contDiffOn_realizedNormalizedJunctionParam
        (horizontalSign := horizontalSign) hvertical)
        |>.exists_lipschitzOnWith (by norm_num)
          (by
            simpa [normalizedJunctionBox] using
              (Convex.prod (𝕜 := ℝ)
                (convex_Icc (0 : ℝ) (1 / 16))
                (convex_Icc (0 : ℝ) 1) :
                Convex ℝ
                  (Icc (0 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1)))
          (by
            simpa [normalizedJunctionBox] using
              (isCompact_Icc.prod isCompact_Icc :
                IsCompact
                  (Icc (0 : ℝ) (1 / 16) ×ˢ Icc (0 : ℝ) 1))) with
    ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro epsilon hepsilon
  rw [lipschitzOnWith_iff_dist_le_mul] at hK ⊢
  intro t ht u hu
  simpa using hK (epsilon, t) ⟨hepsilon, ht⟩
    (epsilon, u) ⟨hepsilon, hu⟩

/-- Fixed strip-side boundary, normalized to the parameter interval `[0,1]`. -/
def realizedNormalizedSideParam (horizontalSign t : ℝ) : EuclideanPlane :=
  let y := -1 + 2 * t
  planeEuclideanHomeomorph
    (horizontalSign * √(sideSquare y), y)

lemma contDiff_realizedNormalizedSideParam (horizontalSign : ℝ) :
    ContDiff ℝ 1 (realizedNormalizedSideParam horizontalSign) := by
  have hy : ContDiff ℝ ∞ (fun t : ℝ => -1 + 2 * t) :=
    contDiff_const.add (contDiff_const.mul contDiff_id)
  have hq : ContDiff ℝ ∞
      (fun t : ℝ => √(sideSquare (-1 + 2 * t))) :=
    (contDiff_sideSquare.comp hy).sqrt
      (fun t => (sideSquare_pos (-1 + 2 * t)).ne')
  unfold realizedNormalizedSideParam
  rw [show (fun t : ℝ =>
      planeEuclideanHomeomorph
        (horizontalSign * √(sideSquare (-1 + 2 * t)),
          -1 + 2 * t)) =
      WithLp.toLp 2 ∘
        (fun t : ℝ =>
          (horizontalSign * √(sideSquare (-1 + 2 * t)),
            -1 + 2 * t)) by rfl]
  exact WithLp.contDiff_toLp.comp
    ((contDiff_const.mul hq).prodMk hy) |>.of_le (by simp)

lemma exists_side_lipschitz (horizontalSign : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (realizedNormalizedSideParam horizontalSign) (Icc (0 : ℝ) 1) :=
  (contDiff_realizedNormalizedSideParam horizontalSign).contDiffOn
    |>.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (0 : ℝ) 1) isCompact_Icc

/-- Coordinate isometry used only to realize fixed circles in the Euclidean
plane carrying Hausdorff measure. -/
def recoveryComplexToEuclidean (z : ℂ) : EuclideanPlane :=
  WithLp.toLp 2 (z.re, z.im)

/-- A complete radius-two circle centered on the vertical axis, normalized to
the parameter interval `[0,1]`. -/
def realizedNormalizedCircleParam (centerY t : ℝ) : EuclideanPlane :=
  recoveryComplexToEuclidean
    (circleMap ((centerY : ℂ) * Complex.I) 2 (2 * Real.pi * t))

lemma contDiff_realizedNormalizedCircleParam (centerY : ℝ) :
    ContDiff ℝ 1 (realizedNormalizedCircleParam centerY) := by
  let c : ℂ := (centerY : ℂ) * Complex.I
  have hangle : ContDiff ℝ 1 (fun t : ℝ => 2 * Real.pi * t) :=
    contDiff_const.mul contDiff_id
  have hcircle : ContDiff ℝ 1
      (fun t : ℝ => circleMap c 2 (2 * Real.pi * t)) :=
    (contDiff_circleMap c 2).comp hangle
  have hre : ContDiff ℝ 1
      (fun t : ℝ => (circleMap c 2 (2 * Real.pi * t)).re) :=
    Complex.reCLM.contDiff.comp hcircle
  have him : ContDiff ℝ 1
      (fun t : ℝ => (circleMap c 2 (2 * Real.pi * t)).im) :=
    Complex.imCLM.contDiff.comp hcircle
  unfold realizedNormalizedCircleParam recoveryComplexToEuclidean
  change ContDiff ℝ 1
    (WithLp.toLp 2 ∘
      fun t : ℝ =>
        ((circleMap c 2 (2 * Real.pi * t)).re,
          (circleMap c 2 (2 * Real.pi * t)).im))
  exact WithLp.contDiff_toLp.comp (hre.prodMk him)

lemma exists_circle_lipschitz (centerY : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (realizedNormalizedCircleParam centerY) (Icc (0 : ℝ) 1) :=
  (contDiff_realizedNormalizedCircleParam centerY).contDiffOn
    |>.exists_lipschitzOnWith (by norm_num)
      (convex_Icc (0 : ℝ) 1) isCompact_Icc

lemma mem_realizedNormalizedCircleParam_image
    {centerY : ℝ} {p : PlanePoint}
    (hp : p.1 ^ 2 + (p.2 - centerY) ^ 2 = 4) :
    planeEuclideanHomeomorph p ∈
      realizedNormalizedCircleParam centerY '' Icc (0 : ℝ) 1 := by
  let z : ℂ := ⟨p.1, p.2⟩
  have hzsphere :
      z ∈ Metric.sphere ((centerY : ℂ) * Complex.I) 2 := by
    rw [Metric.mem_sphere, Complex.dist_eq, Complex.norm_def]
    have hnormSq :
        Complex.normSq (z - (centerY : ℂ) * Complex.I) = 4 := by
      simp only [Complex.normSq_apply]
      dsimp [z]
      norm_num
      nlinarith
    rw [hnormSq]
    norm_num
  have hcircleImage :
      circleMap ((centerY : ℂ) * Complex.I) 2 '' Ioc 0 (2 * Real.pi) =
        Metric.sphere ((centerY : ℂ) * Complex.I) 2 := by
    simp [image_circleMap_Ioc]
  rw [← hcircleImage] at hzsphere
  rcases hzsphere with ⟨theta, htheta, hcircle⟩
  let t := theta / (2 * Real.pi)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    dsimp [t]
    constructor
    · exact div_nonneg htheta.1.le (mul_nonneg (by norm_num) Real.pi_pos.le)
    · rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
      exact htheta.2
  refine ⟨t, ht, ?_⟩
  unfold realizedNormalizedCircleParam recoveryComplexToEuclidean
  rw [show 2 * Real.pi * t = theta by
    dsimp [t]
    field_simp [Real.pi_ne_zero]]
  rw [hcircle]
  rfl

/-- Eight normalized curves cover the complete recovery frontier: two fixed
strip-side traces, four moving junction traces, and two fixed complete circles
covering the exterior caps. -/
def recoveryCoverCurve (epsilon : ℝ) (i : Fin 8) (t : ℝ) :
    EuclideanPlane :=
  match i.1 with
  | 0 => realizedNormalizedSideParam (-1) t
  | 1 => realizedNormalizedSideParam 1 t
  | 2 => realizedNormalizedJunctionParam (-1) (-1) (epsilon, t)
  | 3 => realizedNormalizedJunctionParam 1 (-1) (epsilon, t)
  | 4 => realizedNormalizedJunctionParam (-1) 1 (epsilon, t)
  | 5 => realizedNormalizedJunctionParam 1 1 (epsilon, t)
  | 6 => realizedNormalizedCircleParam (-(1 / 2)) t
  | _ => realizedNormalizedCircleParam (1 / 2) t



/-- Euclidean realization of the complete recovery frontier is covered by the
eight normalized curves. -/
theorem realized_frontier_subset_recoveryCover
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 16) :
    planeEuclideanHomeomorph '' frontier (domain epsilon) ⊆
      ⋃ i : Fin 8, recoveryCoverCurve epsilon i '' Icc (0 : ℝ) 1 := by
  rintro z ⟨p, hp, rfl⟩
  have hpEq : p.1 ^ 2 = q epsilon p.2 :=
    frontier_lt_subset_eq (continuous_fst.pow 2)
      ((contDiff_q epsilon).continuous.comp continuous_snd) hp
  have hqnonneg : 0 ≤ q epsilon p.2 := by
    rw [← hpEq]
    positivity
  have hsqrt : (√(q epsilon p.2)) ^ 2 = q epsilon p.2 :=
    Real.sq_sqrt hqnonneg
  have hroot :
      p.1 = √(q epsilon p.2) ∨ p.1 = -√(q epsilon p.2) := by
    rw [← hsqrt] at hpEq
    exact (sq_eq_sq_iff_eq_or_eq_neg).mp hpEq
  have honeMinus : 0 ≤ 1 - epsilon := by linarith
  by_cases hcentral : |p.2| ≤ 1 - epsilon
  · have hyOne : |p.2| ≤ 1 := hcentral.trans (by linarith)
    have hysq : p.2 ^ 2 ≤ (1 - epsilon) ^ 2 := by
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg p.2) honeMinus).2 hcentral
      simpa [sq_abs] using hsquare
    have hqside := q_eq_side hepsilon hepsilon_le hysq
    let t := (p.2 + 1) / 2
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      have hyBounds := abs_le.mp hyOne
      dsimp [t]
      constructor <;> linarith
    rcases hroot with hright | hleft
    · apply Set.mem_iUnion.2
      refine ⟨(1 : Fin 8), ?_⟩
      refine ⟨t, ht, ?_⟩
      change realizedNormalizedSideParam 1 t =
        planeEuclideanHomeomorph p
      unfold realizedNormalizedSideParam
      dsimp only
      apply congrArg planeEuclideanHomeomorph
      apply Prod.ext
      · rw [show -1 + 2 * t = p.2 by
          dsimp [t]
          ring]
        rw [← hqside]
        simp only [one_mul]
        exact hright.symm
      · dsimp [t]
        ring
    · apply Set.mem_iUnion.2
      refine ⟨(0 : Fin 8), ?_⟩
      refine ⟨t, ht, ?_⟩
      change realizedNormalizedSideParam (-1) t =
        planeEuclideanHomeomorph p
      unfold realizedNormalizedSideParam
      dsimp only
      apply congrArg planeEuclideanHomeomorph
      apply Prod.ext
      · rw [show -1 + 2 * t = p.2 by
          dsimp [t]
          ring]
        rw [← hqside]
        simp only [neg_one_mul]
        exact hleft.symm
      · dsimp [t]
        ring
  · by_cases hjunction : 1 - epsilon < |p.2| ∧ |p.2| < 1
    · let t := (|p.2| - (1 - epsilon)) / epsilon
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor
        · exact div_nonneg (by linarith [hjunction.1]) hepsilon.le
        · rw [div_le_one hepsilon]
          linarith [hjunction.2]
      have hheight :
          normalizedJunctionHeight (epsilon, t) = |p.2| := by
        unfold normalizedJunctionHeight
        dsimp only
        dsimp [t]
        field_simp [hepsilon.ne']
        ring
      rcases le_total 0 p.2 with hy0 | hy0
      · have habsy : |p.2| = p.2 := abs_of_nonneg hy0
        have hqbridge :=
          normalizedJunctionQ_eq_q
            (verticalSign := (1 : ℝ)) (t := t) (by norm_num) hepsilon
        rw [hheight, habsy, one_mul] at hqbridge
        rcases hroot with hright | hleft
        · apply Set.mem_iUnion.2
          refine ⟨(5 : Fin 8), ?_⟩
          refine ⟨t, ht, ?_⟩
          change realizedNormalizedJunctionParam 1 1 (epsilon, t) =
            planeEuclideanHomeomorph p
          unfold realizedNormalizedJunctionParam
          apply congrArg planeEuclideanHomeomorph
          apply Prod.ext
          · simp [hqbridge, hright]
          · simp [hheight, habsy]
        · apply Set.mem_iUnion.2
          refine ⟨(4 : Fin 8), ?_⟩
          refine ⟨t, ht, ?_⟩
          change realizedNormalizedJunctionParam (-1) 1 (epsilon, t) =
            planeEuclideanHomeomorph p
          unfold realizedNormalizedJunctionParam
          apply congrArg planeEuclideanHomeomorph
          apply Prod.ext
          · simp [hqbridge, hleft]
          · simp [hheight, habsy]
      · have habsy : |p.2| = -p.2 := abs_of_nonpos hy0
        have hqbridge :=
          normalizedJunctionQ_eq_q
            (verticalSign := (-1 : ℝ)) (t := t) (by norm_num) hepsilon
        rw [hheight, habsy] at hqbridge
        norm_num at hqbridge
        rcases hroot with hright | hleft
        · apply Set.mem_iUnion.2
          refine ⟨(3 : Fin 8), ?_⟩
          refine ⟨t, ht, ?_⟩
          change realizedNormalizedJunctionParam 1 (-1) (epsilon, t) =
            planeEuclideanHomeomorph p
          unfold realizedNormalizedJunctionParam
          apply congrArg planeEuclideanHomeomorph
          apply Prod.ext
          · simp [hqbridge, hright]
          · simp [hheight, habsy]
        · apply Set.mem_iUnion.2
          refine ⟨(2 : Fin 8), ?_⟩
          refine ⟨t, ht, ?_⟩
          change realizedNormalizedJunctionParam (-1) (-1) (epsilon, t) =
            planeEuclideanHomeomorph p
          unfold realizedNormalizedJunctionParam
          apply congrArg planeEuclideanHomeomorph
          apply Prod.ext
          · simp [hqbridge, hleft]
          · simp [hheight, habsy]
    · have honeAbs : 1 ≤ |p.2| := by
        by_contra hnot
        exact hjunction
          ⟨lt_of_not_ge hcentral, lt_of_not_ge hnot⟩
      have hysq : 1 ≤ p.2 ^ 2 := by
        have hsquare :=
          (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg p.2)).2
            honeAbs
        simpa [sq_abs] using hsquare
      have hqcap := q_eq_cap hepsilon hepsilon_le hysq
      rw [hqcap, capSquare_eq_of_one_le_abs honeAbs] at hpEq
      rcases le_total 0 p.2 with hy0 | hy0
      · have habsy : |p.2| = p.2 := abs_of_nonneg hy0
        apply Set.mem_iUnion.2
        refine ⟨(7 : Fin 8), ?_⟩
        change planeEuclideanHomeomorph p ∈
          realizedNormalizedCircleParam (1 / 2) '' Icc (0 : ℝ) 1
        apply mem_realizedNormalizedCircleParam_image
        rw [habsy] at hpEq
        nlinarith
      · have habsy : |p.2| = -p.2 := abs_of_nonpos hy0
        apply Set.mem_iUnion.2
        refine ⟨(6 : Fin 8), ?_⟩
        change planeEuclideanHomeomorph p ∈
          realizedNormalizedCircleParam (-(1 / 2)) '' Icc (0 : ℝ) 1
        apply mem_realizedNormalizedCircleParam_image
        rw [habsy] at hpEq
        nlinarith

lemma exists_uniform_recoveryCoverCurve_lipschitz :
    ∃ K : Fin 8 → ℝ≥0,
      ∀ epsilon ∈ Icc (0 : ℝ) (1 / 16), ∀ i : Fin 8,
        LipschitzOnWith (K i) (recoveryCoverCurve epsilon i)
          (Icc (0 : ℝ) 1) := by
  rcases exists_side_lipschitz (-1) with ⟨K0, hK0⟩
  rcases exists_side_lipschitz 1 with ⟨K1, hK1⟩
  rcases exists_uniform_junction_lipschitz
      (horizontalSign := -1) (verticalSign := -1) (by norm_num) with
    ⟨K2, hK2⟩
  rcases exists_uniform_junction_lipschitz
      (horizontalSign := 1) (verticalSign := -1) (by norm_num) with
    ⟨K3, hK3⟩
  rcases exists_uniform_junction_lipschitz
      (horizontalSign := -1) (verticalSign := 1) (by norm_num) with
    ⟨K4, hK4⟩
  rcases exists_uniform_junction_lipschitz
      (horizontalSign := 1) (verticalSign := 1) (by norm_num) with
    ⟨K5, hK5⟩
  rcases exists_circle_lipschitz (-(1 / 2)) with ⟨K6, hK6⟩
  rcases exists_circle_lipschitz (1 / 2) with ⟨K7, hK7⟩
  let K : Fin 8 → ℝ≥0 := fun i =>
    match i.1 with
    | 0 => K0
    | 1 => K1
    | 2 => K2
    | 3 => K3
    | 4 => K4
    | 5 => K5
    | 6 => K6
    | _ => K7
  refine ⟨K, ?_⟩
  intro epsilon hepsilon i
  fin_cases i
  · change LipschitzOnWith K0
      (realizedNormalizedSideParam (-1)) (Icc (0 : ℝ) 1)
    exact hK0
  · change LipschitzOnWith K1
      (realizedNormalizedSideParam 1) (Icc (0 : ℝ) 1)
    exact hK1
  · change LipschitzOnWith K2
      (fun t : ℝ =>
        realizedNormalizedJunctionParam (-1) (-1) (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK2 epsilon hepsilon
  · change LipschitzOnWith K3
      (fun t : ℝ =>
        realizedNormalizedJunctionParam 1 (-1) (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK3 epsilon hepsilon
  · change LipschitzOnWith K4
      (fun t : ℝ =>
        realizedNormalizedJunctionParam (-1) 1 (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK4 epsilon hepsilon
  · change LipschitzOnWith K5
      (fun t : ℝ =>
        realizedNormalizedJunctionParam 1 1 (epsilon, t))
      (Icc (0 : ℝ) 1)
    exact hK5 epsilon hepsilon
  · change LipschitzOnWith K6
      (realizedNormalizedCircleParam (-(1 / 2))) (Icc (0 : ℝ) 1)
    exact hK6
  · change LipschitzOnWith K7
      (realizedNormalizedCircleParam (1 / 2)) (Icc (0 : ℝ) 1)
    exact hK7

/-- The frozen recovery domains have a weighted Euclidean frontier cost bounded
by one finite constant independent of the junction width. -/
theorem smoothCost_domain_uniformly_bounded :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ⦃epsilon : ℝ⦄, 0 < epsilon → epsilon ≤ 1 / 16 →
        smoothCost 2 (domain epsilon) ≤ C := by
  rcases exists_uniform_recoveryCoverCurve_lipschitz with ⟨K, hK⟩
  let C : ℝ≥0∞ := 2 * ∑ i : Fin 8, (K i : ℝ≥0∞)
  refine ⟨C, by
    dsimp [C]
    apply ENNReal.mul_lt_top
    · norm_num
    · rw [ENNReal.sum_lt_top]
      intro i hi
      exact ENNReal.coe_lt_top, ?_⟩
  intro epsilon hepsilon hepsilon_le
  have hepsilon_mem : epsilon ∈ Icc (0 : ℝ) (1 / 16) :=
    ⟨hepsilon.le, hepsilon_le⟩
  have hmeasure :
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' frontier (domain epsilon)) ≤
        ∑ i : Fin 8, (K i : ℝ≥0∞) := by
    calc
      (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' frontier (domain epsilon)) ≤
          (μH[1] : Measure EuclideanPlane)
            (⋃ i : Fin 8,
              recoveryCoverCurve epsilon i '' Icc (0 : ℝ) 1) :=
        measure_mono
          (realized_frontier_subset_recoveryCover
            hepsilon hepsilon_le)
      _ ≤ ∑' i : Fin 8,
          (μH[1] : Measure EuclideanPlane)
            (recoveryCoverCurve epsilon i '' Icc (0 : ℝ) 1) :=
        measure_iUnion_le _
      _ ≤ ∑' i : Fin 8, (K i : ℝ≥0∞) := by
        apply ENNReal.tsum_le_tsum
        intro i
        have hi :=
          (hK epsilon hepsilon_mem i).hausdorffMeasure_image_le
            (d := (1 : ℝ)) (by norm_num)
        simpa [ENNReal.rpow_one, hausdorffMeasure_real,
          Real.volume_Icc] using hi
      _ = ∑ i : Fin 8, (K i : ℝ≥0∞) := by
        simp
  unfold smoothCost
  calc
    (∫⁻ p, ENNReal.ofReal (StripDensity 2 p)
        ∂FrontierMeasure (domain epsilon)) ≤
        ∫⁻ _p, (2 : ℝ≥0∞) ∂FrontierMeasure (domain epsilon) := by
      apply lintegral_mono
      intro p
      by_cases hp : |p.2| ≤ 1 <;> simp [StripDensity, hp]
    _ = 2 * FrontierMeasure (domain epsilon) Set.univ := by
      rw [lintegral_const]
    _ = 2 * (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' frontier (domain epsilon)) := by
      rw [frontierMeasure_apply_eq_euclidean
        (domain epsilon) Set.univ MeasurableSet.univ]
      simp only [inter_univ]
    _ ≤ 2 * ∑ i : Fin 8, (K i : ℝ≥0∞) := by
      gcongr
    _ = C := rfl
end FrozenSquaredRecovery
namespace FrozenCanonicalCap

/-- Piecewise squared half-width of the closed frozen canonical carrier. -/
def targetQ (y : ℝ) : ℝ :=
  if |y| ≤ 1 then FrozenSquaredRecovery.sideSquare y
  else FrozenSquaredRecovery.capSquare y

/-- The five-piece frozen carrier is exactly the non-strict sublevel of its
piecewise squared half-width. -/
theorem mem_profile_iff_sq_le_targetQ (p : PlanePoint) :
    p ∈ profile.carrier ↔ p.1 ^ 2 ≤ targetQ p.2 := by
  have hR : profile.radius = 2 := by
    norm_num [profile, CanonicalTypeIVProfile.radius]
  have hW : profile.outerHalfWidth = √15 / 2 := by
    rw [CanonicalTypeIVProfile.outerHalfWidth, hR]
    rw [show Real.sin profile.alpha = √15 / 4 by
      rw [CanonicalTypeIVProfile.alpha]
      simp only [profile]
      rw [Real.sin_arccos]
      · rw [show (1 : ℝ) - (1 / 2 / 2) ^ 2 = 15 / 16 by norm_num,
          show (15 / 16 : ℝ) = 15 / 4 ^ 2 by ring]
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 15)]
        norm_num
      ]
    ring
  have hC : profile.sideCenterOffset =
      FrozenSquaredRecovery.sideOffset := by
    rw [CanonicalTypeIVProfile.sideCenterOffset,
      CanonicalTypeIVProfile.radius, CanonicalTypeIVProfile.innerRadial,
      CanonicalTypeIVProfile.alpha, FrozenSquaredRecovery.sideOffset]
    simp only [profile]
    rw [show Real.sin (Real.arccos (1 / 2 / 2)) = √15 / 4 by
      rw [Real.sin_arccos]
      · rw [show (1 : ℝ) - (1 / 2 / 2) ^ 2 = 15 / 16 by norm_num,
          show (15 / 16 : ℝ) = 15 / 4 ^ 2 by ring]
        rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 15)]
        norm_num
      ]
    rw [show √(1 - (1 / 2 : ℝ) ^ 2) = √3 / 2 by
      rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num,
        show (3 / 4 : ℝ) = 3 / 2 ^ 2 by ring,
        Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num]
    ring
  have hL : profile.leftCenter =
      (-FrozenSquaredRecovery.sideOffset, 0) := by
    rw [CanonicalTypeIVProfile.leftCenter, hC]
  have hRt : profile.rightCenter =
      (FrozenSquaredRecovery.sideOffset, 0) := by
    rw [CanonicalTypeIVProfile.rightCenter, hC]
  have hU : profile.upperCenter = (0, 1 / 2) := by
    rw [CanonicalTypeIVProfile.upperCenter]
    simp only [CanonicalTypeIVProfile.radius, CanonicalTypeIVProfile.alpha, profile]
    rw [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ (1 / 2) / 2)
      (by norm_num : (1 / 2 : ℝ) / 2 ≤ 1)]
    norm_num
  have hD : profile.lowerCenter = (0, -1 / 2) := by
    rw [CanonicalTypeIVProfile.lowerCenter]
    simp only [CanonicalTypeIVProfile.radius, CanonicalTypeIVProfile.alpha, profile]
    rw [Real.cos_arccos (by norm_num : (-1 : ℝ) ≤ (1 / 2) / 2)
      (by norm_num : (1 / 2 : ℝ) / 2 ≤ 1)]
    norm_num
  simp only [CanonicalTypeIVProfile.carrier,
    CanonicalTypeIVProfile.rectangleCarrier,
    CanonicalTypeIVProfile.leftSegmentCarrier,
    CanonicalTypeIVProfile.rightSegmentCarrier,
    CanonicalTypeIVProfile.upperCapCarrier,
    CanonicalTypeIVProfile.lowerCapCarrier,
    Set.mem_union, Set.mem_ofPred_eq, hR, hW, hL, hRt, hU, hD,
    sub_zero, targetQ]
  by_cases hy : |p.2| ≤ 1
  · rw [if_pos hy]
    have hysq : p.2 ^ 2 ≤ 1 := by
      have hsquare :=
        (sq_le_sq₀ (abs_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 1)).2 hy
      simpa [sq_abs] using hsquare
    rw [FrozenSquaredRecovery.sideSquare_eq_actual]
    · have h15sq : (√15 : ℝ) ^ 2 = 15 := by norm_num
      have h3sq : (√3 : ℝ) ^ 2 = 3 := by norm_num
      have h15nonneg : 0 ≤ (√15 : ℝ) := Real.sqrt_nonneg _
      have h3nonneg : 0 ≤ (√3 : ℝ) := Real.sqrt_nonneg _
      have hsnonneg : 0 ≤ √(4 - p.2 ^ 2) := Real.sqrt_nonneg _
      have hrad : 0 ≤ 4 - p.2 ^ 2 := by linarith
      have hssq : (√(4 - p.2 ^ 2)) ^ 2 = 4 - p.2 ^ 2 :=
        Real.sq_sqrt hrad
      have hbridge : √3 ≤ √(4 - p.2 ^ 2) := by nlinarith
      have hwidth : 0 ≤
          FrozenSquaredRecovery.sideOffset + √(4 - p.2 ^ 2) := by
        exact add_nonneg FrozenSquaredRecovery.sideOffset_pos.le hsnonneg
      constructor
      · rintro ((((hrect | hleft) | hright) | hupper) | hlower)
        · rcases hrect with ⟨hxlo, hxhi, _⟩
          unfold FrozenSquaredRecovery.sideOffset
          nlinarith
        · rcases hleft with ⟨hdisk, hxside, _⟩
          have hx0 : p.1 ≤ 0 := by nlinarith
          have hshift0 :
              p.1 + (√15 / 2 - √3) ≤ 0 := by nlinarith
          unfold FrozenSquaredRecovery.sideOffset at hdisk
          have hshiftSq :
              (p.1 + (√15 / 2 - √3)) ^ 2 ≤
                (√(4 - p.2 ^ 2)) ^ 2 := by
            nlinarith [hdisk]
          have hshiftAbs :
              |p.1 + (√15 / 2 - √3)| ≤ √(4 - p.2 ^ 2) := by
            exact (sq_le_sq₀ (abs_nonneg _ ) hsnonneg).mp
              (by simpa [sq_abs] using hshiftSq)
          rw [abs_of_nonpos hshift0] at hshiftAbs
          have habsx :
              |p.1| ≤ FrozenSquaredRecovery.sideOffset +
                √(4 - p.2 ^ 2) := by
            rw [abs_of_nonpos hx0]
            unfold FrozenSquaredRecovery.sideOffset
            linarith
          have hsquared := (sq_le_sq₀ (abs_nonneg p.1) hwidth).mpr habsx
          simpa [sq_abs] using hsquared
        · rcases hright with ⟨hdisk, hxside, _⟩
          have hx0 : 0 ≤ p.1 := by nlinarith
          have hshift0 :
              0 ≤ p.1 - (√15 / 2 - √3) := by nlinarith
          unfold FrozenSquaredRecovery.sideOffset at hdisk
          have hshiftSq :
              (p.1 - (√15 / 2 - √3)) ^ 2 ≤
                (√(4 - p.2 ^ 2)) ^ 2 := by
            nlinarith [hdisk]
          have hshiftAbs :
              |p.1 - (√15 / 2 - √3)| ≤ √(4 - p.2 ^ 2) := by
            exact (sq_le_sq₀ (abs_nonneg _ ) hsnonneg).mp
              (by simpa [sq_abs] using hshiftSq)
          rw [abs_of_nonneg hshift0] at hshiftAbs
          have habsx :
              |p.1| ≤ FrozenSquaredRecovery.sideOffset +
                √(4 - p.2 ^ 2) := by
            rw [abs_of_nonneg hx0]
            unfold FrozenSquaredRecovery.sideOffset
            linarith
          have hsquared := (sq_le_sq₀ (abs_nonneg p.1) hwidth).mpr habsx
          simpa [sq_abs] using hsquared
        · rcases hupper with ⟨hdisk, hyupper⟩
          have hyeq : p.2 = 1 := by
            have := (le_abs_self p.2).trans hy
            linarith
          rw [hyeq] at hdisk ⊢
          unfold FrozenSquaredRecovery.sideOffset
          norm_num at hdisk ⊢
          nlinarith
        · rcases hlower with ⟨hdisk, hylower⟩
          have hyeq : p.2 = -1 := by
            have := (neg_le_abs p.2).trans hy
            linarith
          rw [hyeq] at hdisk ⊢
          unfold FrozenSquaredRecovery.sideOffset
          norm_num at hdisk ⊢
          nlinarith
      · intro hx
        have habsx :
            |p.1| ≤ FrozenSquaredRecovery.sideOffset +
              √(4 - p.2 ^ 2) := by
          have hsquared := (sq_le_sq₀ (abs_nonneg p.1) hwidth).mp
            (by simpa only [sq_abs] using hx)
          exact hsquared
        by_cases hxleft : p.1 ≤ -(√15 / 2)
        · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
          refine ⟨?_, hxleft, hy⟩
          have hxlower :
              -(FrozenSquaredRecovery.sideOffset + √(4 - p.2 ^ 2)) ≤
                p.1 := (neg_le_of_abs_le habsx)
          have hshift0 :
              p.1 + FrozenSquaredRecovery.sideOffset ≤ 0 := by
            unfold FrozenSquaredRecovery.sideOffset
            nlinarith
          have hshiftAbs :
              |p.1 + FrozenSquaredRecovery.sideOffset| ≤
                √(4 - p.2 ^ 2) := by
            rw [abs_of_nonpos hshift0]
            linarith
          have hshiftSq :
              (p.1 + FrozenSquaredRecovery.sideOffset) ^ 2 ≤
                (√(4 - p.2 ^ 2)) ^ 2 := by
            have hsquared :=
              (sq_le_sq₀
                (abs_nonneg (p.1 + FrozenSquaredRecovery.sideOffset))
                hsnonneg).mpr hshiftAbs
            simpa only [sq_abs] using hsquared
          nlinarith
        · by_cases hxright : √15 / 2 ≤ p.1
          · refine Or.inl (Or.inl (Or.inr ?_))
            refine ⟨?_, hxright, hy⟩
            have hxupper :
                p.1 ≤ FrozenSquaredRecovery.sideOffset +
                  √(4 - p.2 ^ 2) := (le_of_abs_le habsx)
            have hshift0 :
                0 ≤ p.1 - FrozenSquaredRecovery.sideOffset := by
              unfold FrozenSquaredRecovery.sideOffset
              nlinarith
            have hshiftAbs :
                |p.1 - FrozenSquaredRecovery.sideOffset| ≤
                  √(4 - p.2 ^ 2) := by
              rw [abs_of_nonneg hshift0]
              linarith
            have hshiftSq :
                (p.1 - FrozenSquaredRecovery.sideOffset) ^ 2 ≤
                  (√(4 - p.2 ^ 2)) ^ 2 := by
              have hsquared :=
                (sq_le_sq₀
                  (abs_nonneg (p.1 - FrozenSquaredRecovery.sideOffset))
                  hsnonneg).mpr hshiftAbs
              simpa only [sq_abs] using hsquared
            nlinarith
          · refine Or.inl (Or.inl (Or.inl (Or.inl ?_)))
            exact ⟨le_of_not_ge hxleft, le_of_not_ge hxright, hy⟩
    · linarith
  · rw [if_neg hy]
    have hy' : 1 < |p.2| := lt_of_not_ge hy
    rw [FrozenSquaredRecovery.capSquare_eq_of_one_le_abs hy'.le]
    simp only [hy, and_false, or_false]
    rcases le_total 0 p.2 with hy0 | hy0
    · have hpos : 1 < p.2 := by
        rw [abs_of_nonneg hy0] at hy'
        exact hy'
      have hnotLower : ¬p.2 ≤ -1 := by linarith
      simp only [hpos.le, hnotLower, and_false, or_false, false_or, and_true,
        abs_of_nonneg hy0]
      constructor <;> intro h <;> nlinarith
    · have hneg : p.2 < -1 := by
        rw [abs_of_nonpos hy0] at hy'
        linarith
      have hnotUpper : ¬1 ≤ p.2 := by linarith
      simp only [hneg.le, hnotUpper, and_false, false_or, or_false, and_true,
        abs_of_nonpos hy0]
      constructor <;> intro h <;> nlinarith

/-- Away from the two junction bands, the recovery squared width is exactly
the frozen piecewise squared width. -/
lemma recovery_q_eq_targetQ_outside_junction
    {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 16)
    (hy : ¬(1 - epsilon < |y| ∧ |y| < 1)) :
    FrozenSquaredRecovery.q epsilon y = targetQ y := by
  by_cases hlow : |y| ≤ 1 - epsilon
  · have honeMinus : 0 ≤ 1 - epsilon := by linarith
    have hone : |y| ≤ 1 := hlow.trans (by linarith)
    rw [targetQ, if_pos hone]
    apply FrozenSquaredRecovery.q_eq_side hepsilon hepsilon_le
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg y) honeMinus).2 hlow
    simpa [sq_abs] using hsquare
  · have hhigh : 1 ≤ |y| := by
      by_contra hnot
      exact hy ⟨lt_of_not_ge hlow, lt_of_not_ge hnot⟩
    have hsq : 1 ≤ y ^ 2 := by
      have hsquare :=
        (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg y)).2 hhigh
      simpa [sq_abs] using hsquare
    rw [FrozenSquaredRecovery.q_eq_cap hepsilon hepsilon_le hsq]
    by_cases hone : |y| ≤ 1
    · have habs : |y| = 1 := le_antisymm hone hhigh
      have hyEq : y = -1 ∨ y = 1 := by
        rcases le_total 0 y with hy0 | hy0
        · right
          rwa [abs_of_nonneg hy0] at habs
        · left
          rw [abs_of_nonpos hy0] at habs
          linarith
      rcases hyEq with rfl | rfl
      · rw [targetQ, if_pos (by norm_num),
          FrozenSquaredRecovery.sideSquare_neg_one,
          FrozenSquaredRecovery.capSquare_neg_one]
      · rw [targetQ, if_pos (by norm_num),
          FrozenSquaredRecovery.sideSquare_one,
          FrozenSquaredRecovery.capSquare_one]
    · rw [targetQ, if_neg hone]


lemma sideOffset_lt_one : FrozenSquaredRecovery.sideOffset < 1 := by
  have h15sq : (√15 : ℝ) ^ 2 = 15 := by norm_num
  have h3sq : (√3 : ℝ) ^ 2 = 3 := by norm_num
  have h15nonneg : 0 ≤ (√15 : ℝ) := Real.sqrt_nonneg _
  have h3nonneg : 0 ≤ (√3 : ℝ) := Real.sqrt_nonneg _
  unfold FrozenSquaredRecovery.sideOffset
  nlinarith

lemma sideSquare_lt_nine (y : ℝ) :
    FrozenSquaredRecovery.sideSquare y < 9 := by
  have hsafe := FrozenSquaredRecovery.safeSquare_mem_Icc y
  have hsafe0 := hsafe.1
  have hsafeUpper := hsafe.2
  have hrad : 0 ≤ 4 - FrozenSquaredRecovery.safeSquare y := by linarith
  have hsqrtSq :
      (√(4 - FrozenSquaredRecovery.safeSquare y)) ^ 2 =
        4 - FrozenSquaredRecovery.safeSquare y :=
    Real.sq_sqrt hrad
  have hsqrt0 : 0 ≤ √(4 - FrozenSquaredRecovery.safeSquare y) :=
    Real.sqrt_nonneg _
  have hsqrt_le : √(4 - FrozenSquaredRecovery.safeSquare y) ≤ 2 := by
    nlinarith
  have hsum0 : 0 ≤ FrozenSquaredRecovery.sideOffset +
      √(4 - FrozenSquaredRecovery.safeSquare y) :=
    add_nonneg FrozenSquaredRecovery.sideOffset_pos.le hsqrt0
  rw [FrozenSquaredRecovery.sideSquare]
  nlinarith [sideOffset_lt_one]

lemma capSquare_le_four (y : ℝ) :
    FrozenSquaredRecovery.capSquare y ≤ 4 := by
  unfold FrozenSquaredRecovery.capSquare
  nlinarith [sq_nonneg (FrozenSquaredRecovery.smoothAbs y - 1 / 2)]

lemma recovery_q_le_nine (epsilon y : ℝ) :
    FrozenSquaredRecovery.q epsilon y ≤ 9 := by
  let w := FrozenSquaredRecovery.junctionWeight epsilon y
  have hw := FrozenSquaredRecovery.junctionWeight_mem_Icc epsilon y
  have hs := sideSquare_lt_nine y
  have hc := capSquare_le_four y
  have hleft : 0 ≤ (1 - w) *
      (9 - FrozenSquaredRecovery.sideSquare y) :=
    mul_nonneg (sub_nonneg.mpr hw.2) (sub_nonneg.mpr hs.le)
  have hright : 0 ≤ w *
      (9 - FrozenSquaredRecovery.capSquare y) :=
    mul_nonneg hw.1 (by linarith)
  change FrozenSquaredRecovery.sideSquare y +
      w * (FrozenSquaredRecovery.capSquare y -
        FrozenSquaredRecovery.sideSquare y) ≤ 9
  nlinarith

lemma targetQ_le_nine (y : ℝ) : targetQ y ≤ 9 := by
  rw [targetQ]
  split_ifs
  · exact (sideSquare_lt_nine y).le
  · exact (capSquare_le_four y).trans (by norm_num)

/-- Open strict-sublevel representative of the frozen carrier. -/
def openTarget : Set PlanePoint := squaredWidthDomain targetQ

lemma continuous_targetQ : Continuous targetQ := by
  unfold targetQ
  apply continuous_if_le continuous_id.abs continuous_const
    FrozenSquaredRecovery.contDiff_sideSquare.continuous.continuousOn
    FrozenSquaredRecovery.contDiff_capSquare.continuous.continuousOn
  intro y hy
  change |y| = 1 at hy
  have hyEq : y = -1 ∨ y = 1 := by
    rcases le_total 0 y with hy0 | hy0
    · right
      rw [abs_of_nonneg hy0] at hy
      exact hy
    · left
      rw [abs_of_nonpos hy0] at hy
      linarith
  rcases hyEq with rfl | rfl
  · rw [FrozenSquaredRecovery.sideSquare_neg_one,
      FrozenSquaredRecovery.capSquare_neg_one]
  · rw [FrozenSquaredRecovery.sideSquare_one,
      FrozenSquaredRecovery.capSquare_one]

lemma isOpen_openTarget : IsOpen openTarget := by
  exact isOpen_lt (continuous_fst.pow 2)
    (continuous_targetQ.comp continuous_snd)

/-- A continuous squared-width boundary is a measurable closed set. -/
lemma measurableSet_squaredWidthBoundary (q : ℝ → ℝ) (hq : Continuous q) :
    MeasurableSet {p : PlanePoint | p.1 ^ 2 = q p.2} := by
  exact (isClosed_eq (continuous_fst.pow 2)
    (hq.comp continuous_snd)).measurableSet

/-- A continuous squared-width level has zero planar volume because every
horizontal fiber has at most two points. -/
lemma volume_squaredWidthBoundary (q : ℝ → ℝ) (hq : Continuous q) :
    volume {p : PlanePoint | p.1 ^ 2 = q p.2} = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm (measurableSet_squaredWidthBoundary q hq)]
  have hfiber : ∀ y : ℝ,
      volume ((fun x : ℝ => (x, y)) ⁻¹'
        {p : PlanePoint | p.1 ^ 2 = q p.2}) = 0 := by
    intro y
    change volume {x : ℝ | x ^ 2 = q y} = 0
    by_cases hqy : 0 ≤ q y
    · apply Set.Finite.measure_zero
      refine ({√(q y), -√(q y)} : Set ℝ).toFinite.subset ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have hsqrt : (√(q y)) ^ 2 = q y := Real.sq_sqrt hqy
      have hroot : x = √(q y) ∨ x = -√(q y) := by
        rw [← hsqrt] at hx
        exact (sq_eq_sq_iff_eq_or_eq_neg).mp hx
      exact hroot
    · have hempty : {x : ℝ | x ^ 2 = q y} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        exact hqy (by nlinarith [sq_nonneg x])
      simp [hempty]
  simp_rw [hfiber]
  simp


/-- The actual closed five-piece carrier and its open squared-width
representative agree almost everywhere. -/
theorem carrier_ae_eq_openTarget :
    profile.carrier =ᵐ[volume] openTarget := by
  have hboundary :
      volume {p : PlanePoint | p.1 ^ 2 = targetQ p.2} = 0 :=
    volume_squaredWidthBoundary targetQ continuous_targetQ
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null
      (t := {p : PlanePoint | p.1 ^ 2 = targetQ p.2})
    · rintro p ⟨hpProfile, hpNotOpen⟩
      have hle := (mem_profile_iff_sq_le_targetQ p).1 hpProfile
      change ¬p.1 ^ 2 < targetQ p.2 at hpNotOpen
      exact le_antisymm hle (le_of_not_gt hpNotOpen)
    · exact hboundary
  · apply measure_mono_null (t := ∅)
    · rintro p ⟨hpOpen, hpNotProfile⟩
      change p.1 ^ 2 < targetQ p.2 at hpOpen
      exact (hpNotProfile
        ((mem_profile_iff_sq_le_targetQ p).2 hpOpen.le)).elim
    · exact measure_empty

/-- The recovery differs from the actual frozen carrier only in two
`epsilon`-height junction boxes, modulo its null squared-width boundary. -/
theorem characteristicDistance_domain_profile_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 16) :
    characteristicDistance (FrozenSquaredRecovery.domain epsilon)
        profile.carrier ≤
      (12 : ℝ≥0∞) * ENNReal.ofReal epsilon := by
  let L : Set PlanePoint :=
    Icc (-3 : ℝ) 3 ×ˢ Icc (-1) (-(1 - epsilon))
  let U : Set PlanePoint :=
    Icc (-3 : ℝ) 3 ×ˢ Icc (1 - epsilon) 1
  let B : Set PlanePoint :=
    {p | p.1 ^ 2 = FrozenSquaredRecovery.q epsilon p.2}
  have hsubset :
      FrozenSquaredRecovery.domain epsilon ∆ profile.carrier ⊆
        (L ∪ U) ∪ B := by
    intro p hp
    by_cases hband : 1 - epsilon < |p.2| ∧ |p.2| < 1
    · have hx : p.1 ∈ Icc (-3 : ℝ) 3 := by
        rcases hp with ⟨hpD, _hnotP⟩ | ⟨hpP, _hnotD⟩
        · change p.1 ^ 2 < FrozenSquaredRecovery.q epsilon p.2 at hpD
          have hq9 := recovery_q_le_nine epsilon p.2
          constructor <;> nlinarith
        · have hpTarget : p.1 ^ 2 ≤ targetQ p.2 :=
            (mem_profile_iff_sq_le_targetQ p).1 hpP
          have ht9 := targetQ_le_nine p.2
          constructor <;> nlinarith
      rcases le_total 0 p.2 with hy0 | hy0
      · left
        right
        exact ⟨hx, by
          rw [abs_of_nonneg hy0] at hband
          exact ⟨hband.1.le, hband.2.le⟩⟩
      · left
        left
        exact ⟨hx, by
          rw [abs_of_nonpos hy0] at hband
          constructor <;> linarith [hband.1, hband.2]⟩
    · right
      have hqeq :=
        recovery_q_eq_targetQ_outside_junction hepsilon hepsilon_le hband
      rcases hp with ⟨hpD, hnotP⟩ | ⟨hpP, hnotD⟩
      · exfalso
        change p.1 ^ 2 < FrozenSquaredRecovery.q epsilon p.2 at hpD
        exact hnotP ((mem_profile_iff_sq_le_targetQ p).2
          (by rw [hqeq] at hpD
              exact hpD.le))
      · change p.1 ^ 2 = FrozenSquaredRecovery.q epsilon p.2
        have hle := (mem_profile_iff_sq_le_targetQ p).1 hpP
        have hnlt :
            ¬p.1 ^ 2 < FrozenSquaredRecovery.q epsilon p.2 := by
          exact hnotD
        rw [hqeq]
        rw [hqeq] at hnlt
        exact le_antisymm hle (le_of_not_gt hnlt)
  have hB : volume B = 0 := by
    exact volume_squaredWidthBoundary
      (FrozenSquaredRecovery.q epsilon)
      (FrozenSquaredRecovery.contDiff_q epsilon).continuous
  have hL :
      volume L = (6 : ℝ≥0∞) * ENNReal.ofReal epsilon := by
    dsimp only [L]
    rw [Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    norm_num
  have hU :
      volume U = (6 : ℝ≥0∞) * ENNReal.ofReal epsilon := by
    dsimp only [U]
    rw [Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    norm_num
  change volume
      (FrozenSquaredRecovery.domain epsilon ∆ profile.carrier) ≤ _
  calc
    volume (FrozenSquaredRecovery.domain epsilon ∆ profile.carrier) ≤
        volume ((L ∪ U) ∪ B) := measure_mono hsubset
    _ ≤ volume (L ∪ U) + volume B := measure_union_le _ _
    _ ≤ (volume L + volume U) + volume B :=
      add_le_add (measure_union_le L U) le_rfl
    _ = (12 : ℝ≥0∞) * ENNReal.ofReal epsilon := by
      rw [hL, hU, hB]
      ring
/-- Positive recovery scale tending to zero. -/
def recoveryScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 16)

lemma recoveryScale_pos (n : ℕ) : 0 < recoveryScale n := by
  unfold recoveryScale
  positivity

lemma recoveryScale_le (n : ℕ) : recoveryScale n ≤ 1 / 16 := by
  unfold recoveryScale
  have hn : 0 ≤ (n : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity : 0 < (n : ℝ) + 16)]
  nlinarith

lemma tendsto_recoveryScale : Tendsto recoveryScale atTop (𝓝 0) := by
  unfold recoveryScale
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right atTop 16 tendsto_natCast_atTop_atTop)

/-- The frozen squared-width approximants as an actual smooth sequence. -/
def recoverySequence : SmoothSequence where
  carrier n := FrozenSquaredRecovery.domain (recoveryScale n)
  smooth n := FrozenSquaredRecovery.isSmoothDomain_domain
    (recoveryScale_pos n) (recoveryScale_le n)

/-- The squared-width recovery sequence converges globally in characteristic
function distance to the actual frozen carrier. -/
theorem recoverySequence_converges :
    recoverySequence.ConvergesTo profile.carrier := by
  unfold SmoothSequence.ConvergesTo
  have hbound : Tendsto
      (fun n : ℕ => (12 : ℝ≥0∞) * ENNReal.ofReal (recoveryScale n))
      atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun n : ℕ => (12 : ℝ≥0∞) * ENNReal.ofReal (recoveryScale n))
        atTop (𝓝 ((12 : ℝ≥0∞) * ENNReal.ofReal 0)) :=
      ENNReal.Tendsto.mul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (12 : ℝ≥0∞)) atTop (𝓝 12))
        (by norm_num) (ENNReal.tendsto_ofReal tendsto_recoveryScale) (by simp)
    simpa using hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall (fun _ => bot_le)
  · exact Eventually.of_forall (fun n =>
      characteristicDistance_domain_profile_le
        (recoveryScale_pos n) (recoveryScale_le n))
end FrozenCanonicalCap
end CMVRelaxation
