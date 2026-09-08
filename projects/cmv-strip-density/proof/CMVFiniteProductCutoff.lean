/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxationSelector
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Explicit finite-product cutoffs

This module is the first gate in the source-wide finite-variation route.  Its
estimates do not use disjointness or an overlap multiplicity: differentiation
of the finite product is bounded term-by-term using factors in `[0,1]`.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology BigOperators

noncomputable section

namespace CMVRelaxation
namespace FiniteProductCutoff

/-- The fixed scalar cutoff used throughout the finite-cover construction. -/
def beta (t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t ^ 2 - 1) / 3)

lemma contDiff_beta : ContDiff ℝ ∞ beta := by
  unfold beta
  exact contDiff_const.sub <|
    Real.smoothTransition.contDiff.comp
      (((contDiff_id.pow 2).sub contDiff_const).div_const 3)

lemma beta_mem_Icc (t : ℝ) : beta t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (Real.smoothTransition.le_one _)
  · linarith [Real.smoothTransition.nonneg ((t ^ 2 - 1) / 3)]

lemma beta_eq_one_of_abs_le_one {t : ℝ} (ht : |t| ≤ 1) : beta t = 1 := by
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [sq_abs t]
  rw [beta, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma beta_eq_zero_of_two_le_abs {t : ℝ} (ht : 2 ≤ |t|) : beta t = 0 := by
  have ht2 : 4 ≤ t ^ 2 := by nlinarith [sq_abs t]
  rw [beta, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

lemma support_beta_subset : Function.support beta ⊆ Icc (-2 : ℝ) 2 := by
  intro t ht
  by_contra hmem
  have habs : 2 ≤ |t| := by
    rw [abs_le] at hmem
    push_neg at hmem
    rcases hmem with h | h <;> linarith
  exact ht (beta_eq_zero_of_two_le_abs habs)

lemma deriv_beta_eq_zero_of_two_lt_abs {t : ℝ} (ht : 2 < |t|) :
    deriv beta t = 0 := by
  rcases lt_or_ge 0 t with ht0 | ht0
  · have ht2 : 2 < t := by rw [abs_of_pos ht0] at ht; exact ht
    have heq : beta =ᶠ[𝓝 t] fun _ : ℝ => 0 :=
      (Ioi_mem_nhds ht2).mono fun u hu => by
        exact beta_eq_zero_of_two_le_abs (by rw [abs_of_pos (lt_trans (by norm_num) hu)]; exact hu.le)
    simpa using heq.deriv_eq
  · have ht2 : t < -2 := by rw [abs_of_nonpos ht0] at ht; linarith
    have heq : beta =ᶠ[𝓝 t] fun _ : ℝ => 0 :=
      (Iio_mem_nhds ht2).mono fun u hu => by
        exact beta_eq_zero_of_two_le_abs (by rw [abs_of_neg (lt_trans hu (by norm_num))]; linarith)
    simpa using heq.deriv_eq

/-- A finite derivative bound constructed from compactness, not supplied by a caller. -/
theorem exists_deriv_bound :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ t : ℝ, |deriv beta t| ≤ D := by
  have hc : Continuous (fun t : ℝ => |deriv beta t|) :=
    (contDiff_beta.continuous_deriv (by simp)).abs
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hc.continuousOn)
  refine ⟨max 1 M, le_max_left _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (-2 : ℝ) 2
  · exact (hM (mem_image_of_mem _ ht)).trans (le_max_right _ _)
  · have hle : 2 ≤ |t| := by
      rw [mem_Icc, not_and_or] at ht
      rcases ht with ht | ht <;> linarith [le_abs_self t, neg_le_abs t]
    rcases hle.eq_or_lt with heq | hlt
    · subst heq
      exact (hM (mem_image_of_mem _ <| by simp)).trans (le_max_right _ _)
    · rw [deriv_beta_eq_zero_of_two_lt_abs hlt, abs_zero]
      exact le_trans (by norm_num) (le_max_left _ _)

variable {ι : Type*} [DecidableEq ι]

/-- The closed coordinate square controlling one product factor. -/
def square (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  Icc (c.1 - 2 * r) (c.1 + 2 * r) ×ˢ
    Icc (c.2 - 2 * r) (c.2 + 2 * r)

/-- One tensor-product bump. -/
def bump (c : ℝ × ℝ) (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  beta ((p.1 - c.1) / r) * beta ((p.2 - c.2) / r)

/-- The overlap-independent union cutoff `1 - ∏ᵢ (1 - ψᵢ)`. -/
def cutoff (s : Finset ι) (c : ι → ℝ × ℝ) (r : ι → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  1 - ∏ i ∈ s, (1 - bump (c i) (r i) p)

lemma contDiff_bump (c : ℝ × ℝ) {r : ℝ} (hr : r ≠ 0) :
    ContDiff ℝ ∞ (bump c r) := by
  unfold bump
  fun_prop

lemma contDiff_cutoff (s : Finset ι) (c : ι → ℝ × ℝ) (r : ι → ℝ)
    (hr : ∀ i ∈ s, r i ≠ 0) : ContDiff ℝ ∞ (cutoff s c r) := by
  unfold cutoff
  fun_prop

lemma cutoff_mem_Icc (s : Finset ι) (c : ι → ℝ × ℝ) (r : ι → ℝ)
    (p : ℝ × ℝ) : cutoff s c r p ∈ Icc (0 : ℝ) 1 := by
  have hf : ∀ i ∈ s, 1 - bump (c i) (r i) p ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    have hx := beta_mem_Icc ((p.1 - (c i).1) / r i)
    have hy := beta_mem_Icc ((p.2 - (c i).2) / r i)
    constructor <;> dsimp [bump] <;> nlinarith [mul_nonneg hx.1 hy.1,
      mul_le_mul hx.2 hy.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1)]
  have hp : (∏ i ∈ s, (1 - bump (c i) (r i) p)) ∈ Icc (0 : ℝ) 1 := by
    simpa only [Finset.prod_filter] using Finset.prod_mem_Icc hf
  exact ⟨sub_nonneg.mpr hp.2, by linarith [hp.1]⟩

private lemma scaled_abs_two_of_not_mem_Icc
    {x a r : ℝ} (hr : 0 < r) (hx : x ∉ Icc (a - 2 * r) (a + 2 * r)) :
    2 ≤ |(x - a) / r| := by
  rw [mem_Icc, not_and_or] at hx
  rw [abs_div, abs_of_pos hr, le_div_iff₀ hr]
  rcases hx with hx | hx <;> nlinarith [le_abs_self (x - a), neg_le_abs (x - a)]

lemma bump_eq_zero_of_not_mem_square
    (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ}
    (hp : p ∉ square c r) : bump c r p = 0 := by
  rw [square, mem_prod] at hp
  push_neg at hp
  rcases hp with hx | hy
  · rw [bump, beta_eq_zero_of_two_le_abs (scaled_abs_two_of_not_mem_Icc hr hx), zero_mul]
  · rw [bump, beta_eq_zero_of_two_le_abs (scaled_abs_two_of_not_mem_Icc hr hy), mul_zero]

lemma cutoff_eq_one_of_mem_ball
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) {i : ι} (hi : i ∈ s) {p : ℝ × ℝ}
    (hp : p ∈ ball (c i) (r i)) : cutoff s c r p = 1 := by
  have hcoord : |(p.1 - (c i).1) / r i| ≤ 1 ∧
      |(p.2 - (c i).2) / r i| ≤ 1 := by
    have hd : max |p.1 - (c i).1| |p.2 - (c i).2| < r i := by
      simpa [Prod.dist_eq, Real.dist_eq] using hp
    constructor <;> rw [abs_div, abs_of_pos (hr i hi), div_le_one (hr i hi)] <;>
      exact le_trans (le_max_left _ _) hd.le
  have hb : bump (c i) (r i) p = 1 := by
    rw [bump, beta_eq_one_of_abs_le_one hcoord.1,
      beta_eq_one_of_abs_le_one hcoord.2, one_mul]
  rw [cutoff, Finset.prod_eq_zero hi]
  simp [hb]

lemma support_cutoff_subset_squares
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) :
    Function.support (cutoff s c r) ⊆ ⋃ i ∈ s, square (c i) (r i) := by
  intro p hp
  by_contra hmem
  simp only [mem_iUnion, exists_prop, not_exists] at hmem
  have hz : ∀ i ∈ s, bump (c i) (r i) p = 0 := fun i hi =>
    bump_eq_zero_of_not_mem_square (c i) (hr i hi) (hmem i hi)
  exact hp (by simp [cutoff, hz])

lemma tsupport_cutoff_subset_squares
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) :
    tsupport (cutoff s c r) ⊆ ⋃ i ∈ s, square (c i) (r i) := by
  apply closure_minimal (support_cutoff_subset_squares s c hr)
  exact s.isClosed_biUnion fun i _ => isClosed_Icc.prod isClosed_Icc

lemma volume_square (c : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (square c r) = ENNReal.ofReal (16 * r ^ 2) := by
  rw [square, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc, Real.volume_Icc]
  rw [show c.1 + 2 * r - (c.1 - 2 * r) = 4 * r by ring,
    show c.2 + 2 * r - (c.2 - 2 * r) = 4 * r by ring,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The support-volume estimate, valid for arbitrary overlaps and the empty family. -/
theorem volume_tsupport_cutoff_le
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) :
    volume (tsupport (cutoff s c r)) ≤
      ENNReal.ofReal (16 * ∑ i ∈ s, (r i) ^ 2) := by
  calc
    volume (tsupport (cutoff s c r)) ≤
        volume (⋃ i ∈ s, square (c i) (r i)) :=
      measure_mono (tsupport_cutoff_subset_squares s c hr)
    _ ≤ ∑ i ∈ s, volume (square (c i) (r i)) :=
      measure_biUnion_finset_le s _
    _ = ∑ i ∈ s, ENNReal.ofReal (16 * (r i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact volume_square (c i) (hr i hi).le
    _ = ENNReal.ofReal (16 * ∑ i ∈ s, (r i) ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · congr 1
        rw [Finset.mul_sum]
      · intro i hi
        positivity

/-- Algebraic x-coordinate derivative of the finite-product cutoff. -/
def dx (s : Finset ι) (c : ι → ℝ × ℝ) (r : ι → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ∑ i ∈ s, ((deriv beta ((p.1 - (c i).1) / r i) / r i) *
      beta ((p.2 - (c i).2) / r i)) *
    ∏ j ∈ s.erase i, (1 - bump (c j) (r j) p)

/-- Algebraic y-coordinate derivative of the finite-product cutoff. -/
def dy (s : Finset ι) (c : ι → ℝ × ℝ) (r : ι → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  ∑ i ∈ s, (beta ((p.1 - (c i).1) / r i) *
      (deriv beta ((p.2 - (c i).2) / r i) / r i)) *
    ∏ j ∈ s.erase i, (1 - bump (c j) (r j) p)

lemma hasDerivAt_cutoff_fst
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, r i ≠ 0) (p : ℝ × ℝ) :
    HasDerivAt (fun x : ℝ => cutoff s c r (x, p.2)) (dx s c r p) p.1 := by
  have hb (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun x : ℝ => 1 - bump (c i) (r i) (x, p.2))
        (-((deriv beta ((p.1 - (c i).1) / r i) / r i) *
          beta ((p.2 - (c i).2) / r i))) p.1 := by
    convert (hasDerivAt_const p.1 1).sub
      (((contDiff_beta.differentiable (by simp) _).hasDerivAt.comp p.1
        (((hasDerivAt_id p.1).sub_const _).div_const (r i))).mul_const
          (beta ((p.2 - (c i).2) / r i))) using 1 <;> ring
  have hp := HasDerivAt.fun_finsetProd hb
  convert (hasDerivAt_const p.1 1).sub hp using 1
  · simp [cutoff]
  · simp only [dx, neg_sum, neg_mul, neg_neg]
    apply Finset.sum_congr rfl
    intro i hi
    ring

lemma hasDerivAt_cutoff_snd
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, r i ≠ 0) (p : ℝ × ℝ) :
    HasDerivAt (fun y : ℝ => cutoff s c r (p.1, y)) (dy s c r p) p.2 := by
  have hb (i : ι) (hi : i ∈ s) :
      HasDerivAt (fun y : ℝ => 1 - bump (c i) (r i) (p.1, y))
        (-(beta ((p.1 - (c i).1) / r i) *
          (deriv beta ((p.2 - (c i).2) / r i) / r i))) p.2 := by
    convert (hasDerivAt_const p.2 1).sub
      ((hasDerivAt_const p.2 (beta ((p.1 - (c i).1) / r i))).mul
        ((contDiff_beta.differentiable (by simp) _).hasDerivAt.comp p.2
          (((hasDerivAt_id p.2).sub_const _).div_const (r i)))) using 1 <;> ring
  have hp := HasDerivAt.fun_finsetProd hb
  convert (hasDerivAt_const p.2 1).sub hp using 1
  · simp [cutoff]
  · simp only [dy, neg_sum, neg_mul, neg_neg]
    apply Finset.sum_congr rfl
    intro i hi
    ring

private def majorant (D : ℝ) (c : ℝ × ℝ) (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  (square c r).indicator (fun _ => D / r) p

private lemma majorant_integrable {D : ℝ} (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (majorant D c r) := by
  unfold majorant
  exact (integrableOn_const (C := D / r)
    (by rw [volume_square c hr.le]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      (isClosed_Icc.prod isClosed_Icc).measurableSet

private lemma integral_majorant {D : ℝ} (c : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ p, majorant D c r p = 16 * D * r := by
  unfold majorant
  rw [integral_indicator (isClosed_Icc.prod isClosed_Icc).measurableSet,
    setIntegral_const, smul_eq_mul, measureReal_def, volume_square c hr.le,
    ENNReal.toReal_ofReal (by positivity)]
  field_simp
  ring

private lemma abs_dx_le_majorant_sum
    {D : ℝ} (hD : ∀ t : ℝ, |deriv beta t| ≤ D)
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) (p : ℝ × ℝ) :
    |dx s c r p| ≤ ∑ i ∈ s, majorant D (c i) (r i) p := by
  rw [dx, abs_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : p ∈ square (c i) (r i)
  · rw [majorant, indicator_of_mem hp]
    have hβx := beta_mem_Icc ((p.1 - (c i).1) / r i)
    have hβy := beta_mem_Icc ((p.2 - (c i).2) / r i)
    have hfac : ∀ j ∈ s.erase i,
        |1 - bump (c j) (r j) p| ≤ 1 := by
      intro j hj
      have hx := beta_mem_Icc ((p.1 - (c j).1) / r j)
      have hy := beta_mem_Icc ((p.2 - (c j).2) / r j)
      rw [abs_of_nonneg]
      · nlinarith [mul_nonneg hx.1 hy.1,
          mul_le_mul hx.2 hy.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1)]
      · dsimp [bump]
        nlinarith [mul_le_mul hx.2 hy.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1)]
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (hr i hi),
      abs_prod]
    calc
      (|deriv beta ((p.1 - (c i).1) / r i)| / r i *
          |beta ((p.2 - (c i).2) / r i)|) *
          ∏ j ∈ s.erase i, |1 - bump (c j) (r j) p| ≤
          (D / r i * 1) * 1 := by
        gcongr
        · exact hD _
        · simpa [abs_of_nonneg hβy.1] using hβy.2
        · exact Finset.prod_le_one (fun _ _ => abs_nonneg _) hfac
      _ = D / r i := by ring
  · rw [majorant, indicator_of_not_mem hp]
    simp only [le_zero_iff, abs_eq_zero]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hji : j = i
    · subst j
      rw [bump_eq_zero_of_not_mem_square (c i) (hr i hi) hp]
      simp [bump]
    · have hiErase : i ∈ s.erase j := Finset.mem_erase.mpr ⟨Ne.symm hji, hi⟩
      rw [Finset.prod_eq_zero hiErase]
      simp [bump_eq_zero_of_not_mem_square (c i) (hr i hi) hp]

private lemma abs_dy_le_majorant_sum
    {D : ℝ} (hD : ∀ t : ℝ, |deriv beta t| ≤ D)
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) (p : ℝ × ℝ) :
    |dy s c r p| ≤ ∑ i ∈ s, majorant D (c i) (r i) p := by
  simpa [dy, dx, bump, mul_comm, mul_left_comm, mul_assoc, Prod.swap_prod_mk] using
    abs_dx_le_majorant_sum (ι := ι) hD s (fun i => ((c i).2, (c i).1)) hr (p.2, p.1)

/-- Both actual coordinate derivatives satisfy the overlap-independent integral
bound.  The empty family is included definitionally. -/
theorem integral_abs_coordinateDerivatives_le
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ t : ℝ, |deriv beta t| ≤ D)
    (s : Finset ι) (c : ι → ℝ × ℝ) {r : ι → ℝ}
    (hr : ∀ i ∈ s, 0 < r i) :
    (∫ p, |dx s c r p|) + (∫ p, |dy s c r p|) ≤
      32 * D * ∑ i ∈ s, r i := by
  let g : ℝ × ℝ → ℝ := fun p => ∑ i ∈ s, majorant D (c i) (r i) p
  have hg : Integrable g := integrable_finset_sum s fun i hi =>
    majorant_integrable (D := D) (c i) (hr i hi)
  have hdxm : AEStronglyMeasurable (fun p => |dx s c r p|) := by
    apply Continuous.aestronglyMeasurable
    unfold dx bump
    fun_prop
  have hdym : AEStronglyMeasurable (fun p => |dy s c r p|) := by
    apply Continuous.aestronglyMeasurable
    unfold dy bump
    fun_prop
  have hdxi : Integrable (fun p => |dx s c r p|) :=
    hg.mono' hdxm (ae_of_all _ fun p => by
      simpa [g] using abs_dx_le_majorant_sum hD s c hr p)
  have hdyi : Integrable (fun p => |dy s c r p|) :=
    hg.mono' hdym (ae_of_all _ fun p => by
      simpa [g] using abs_dy_le_majorant_sum hD s c hr p)
  calc
    (∫ p, |dx s c r p|) + (∫ p, |dy s c r p|) ≤
        (∫ p, g p) + (∫ p, g p) := by
      gcongr
      · exact integral_mono hdxi hg fun p => abs_dx_le_majorant_sum hD s c hr p
      · exact integral_mono hdyi hg fun p => abs_dy_le_majorant_sum hD s c hr p
    _ = 32 * D * ∑ i ∈ s, r i := by
      rw [show (∫ p, g p) = ∑ i ∈ s, ∫ p, majorant D (c i) (r i) p by
        exact integral_finsetSum s fun i hi => majorant_integrable (D := D) (c i) (hr i hi)]
      simp_rw [integral_majorant (D := D) (hr := hr _ ‹_›)]
      rw [← Finset.mul_sum]
      ring

/-- Milestone-1 package: one internally constructed derivative constant controls
both required finite-product estimates, with no overlap or cardinality term. -/
theorem exists_universal_cutoff_constant :
    ∃ D : ℝ, 1 ≤ D ∧
      (∀ (s : Finset ι) (c : ι → ℝ × ℝ) (r : ι → ℝ),
        (∀ i ∈ s, 0 < r i) →
        volume (tsupport (cutoff s c r)) ≤
          ENNReal.ofReal (16 * ∑ i ∈ s, (r i) ^ 2) ∧
        (∫ p, |dx s c r p|) + (∫ p, |dy s c r p|) ≤
          32 * D * ∑ i ∈ s, r i) := by
  obtain ⟨D, hD1, hD⟩ := exists_deriv_bound
  exact ⟨D, hD1, fun s c r hr =>
    ⟨volume_tsupport_cutoff_le s c hr,
      integral_abs_coordinateDerivatives_le hD1.trans (hD) s c hr⟩⟩

end FiniteProductCutoff
end CMVRelaxation
