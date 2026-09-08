/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import NearOneRescaledSecondRowContinuity
import BoxPoincareMiranda

/-!
# First exact near-one endpoint cell

This module fixes a rational box around the exact endpoint seed of the
quadratically rescaled near-one map. It proves all six strict endpoint face
signs and upgrades all three rows to uniform strict face signs for all
sufficiently small `s`. In particular, one exact positive reciprocal-natural
slice below `1/100` satisfies all six face conditions simultaneously.  The
three-dimensional Poincare--Miranda theorem then gives a simultaneous zero of
the complete rescaled map and, through the exact rescaling equivalence, a zero
of the corrected near-one root map.
-/

namespace NearOneRegularizedThirdRow

open NearOneNormalizedFlow NearOneAnalyticSystem Polynomial Real Set
open Filter
open scoped Topology

noncomputable section
set_option maxRecDepth 10000

namespace NearOneRescaledFirstCell

private lemma pi_bounds :
    (3.14159265358979323846 : ℝ) < π ∧
      π < (3.14159265358979323847 : ℝ) :=
  ⟨Real.pi_gt_d20, Real.pi_lt_d20⟩

/-- The first endpoint seed coordinate lies strictly between its rational
faces. -/
theorem seed_zero_bounds :
    (52 : ℝ) < exactRescaledOrientedNearOneSeed 0 ∧
      exactRescaledOrientedNearOneSeed 0 < 54 := by
  rw [show exactRescaledOrientedNearOneSeed 0 = π ^ 3 + 7 * π by
    simp [exactRescaledOrientedNearOneSeed]]
  rcases pi_bounds with ⟨hlo, hhi⟩
  constructor
  · have hp3 : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
      pow_lt_pow_left₀ hlo (by norm_num) (by norm_num)
    norm_num at hp3 ⊢
    nlinarith
  · have hp3 : π ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
    norm_num at hp3 ⊢
    nlinarith

/-- The second endpoint seed coordinate lies strictly between its rational
faces. -/
theorem seed_one_bounds :
    (27 : ℝ) < exactRescaledOrientedNearOneSeed 1 ∧
      exactRescaledOrientedNearOneSeed 1 < 28 := by
  rw [show exactRescaledOrientedNearOneSeed 1 =
      (110880 * π - 2087 * π ^ 3) / 10368 by
    simp [exactRescaledOrientedNearOneSeed]]
  rcases pi_bounds with ⟨hlo, hhi⟩
  have hlo0 : 0 < (3.14159265358979323846 : ℝ) := by norm_num
  have hpi3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ hlo hlo0.le (by norm_num)
  have hpi3hi : π ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  constructor <;> norm_num at hpi3lo hpi3hi ⊢ <;> nlinarith

/-- The third endpoint seed coordinate lies strictly between its rational
faces. -/
theorem seed_two_bounds :
    (-3822 : ℝ) < exactRescaledOrientedNearOneSeed 2 ∧
      exactRescaledOrientedNearOneSeed 2 < -3821 := by
  rw [show exactRescaledOrientedNearOneSeed 2 =
      (1193 * π ^ 4 + 2748816 * π ^ 2 - 146105856) / 31104 by
    simp [exactRescaledOrientedNearOneSeed]]
  rcases pi_bounds with ⟨hlo, hhi⟩
  have hp2lo : (3.14159265358979323846 : ℝ) ^ 2 < π ^ 2 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by norm_num)
  have hp2hi : π ^ 2 < (3.14159265358979323847 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  have hp4lo : (3.14159265358979323846 : ℝ) ^ 4 < π ^ 4 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by norm_num)
  have hp4hi : π ^ 4 < (3.14159265358979323847 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ hhi Real.pi_pos.le (by norm_num)
  constructor <;> norm_num at hp2lo hp2hi hp4lo hp4hi ⊢ <;> nlinarith

/-- Exact rational lower faces of the endpoint test box. -/
def endpointBoxLower : Fin 3 → ℝ := ![52, 27, -3822]

/-- Exact rational upper faces of the endpoint test box. -/
def endpointBoxUpper : Fin 3 → ℝ := ![54, 28, -3821]

/-- Membership in the exact rational endpoint test box. -/
def InEndpointBox (q : Fin 3 → ℝ) : Prop :=
  ∀ i, q i ∈ Icc (endpointBoxLower i) (endpointBoxUpper i)

/-- The exact rescaled endpoint seed is in the strict interior of the rational
box. -/
theorem exactSeed_strictly_inside_endpointBox :
    ∀ i, endpointBoxLower i < exactRescaledOrientedNearOneSeed i ∧
      exactRescaledOrientedNearOneSeed i < endpointBoxUpper i := by
  intro i
  fin_cases i
  · simpa [endpointBoxLower, endpointBoxUpper] using seed_zero_bounds
  · simpa [endpointBoxLower, endpointBoxUpper] using seed_one_bounds
  · simpa [endpointBoxLower, endpointBoxUpper] using seed_two_bounds

/-- The endpoint map is exactly its positive diagonal applied to displacement
from the endpoint seed. -/
theorem endpoint_eq_diagonal_seed_difference (q : Fin 3 → ℝ) :
    rescaledOrientedNearOneEndpoint q =
      ![2 * (q 0 - exactRescaledOrientedNearOneSeed 0),
        96 * (q 1 - exactRescaledOrientedNearOneSeed 1),
        4 * π * (q 2 - exactRescaledOrientedNearOneSeed 2)] := by
  have hpi : π ≠ 0 := ne_of_gt Real.pi_pos
  ext i
  fin_cases i <;>
    simp [rescaledOrientedNearOneEndpoint,
      exactRescaledOrientedNearOneSeed] <;>
    field_simp [hpi] <;>
    ring

/-- Every lower endpoint-box face has a strict negative corresponding row, and
every upper face has a strict positive corresponding row. -/
theorem endpointBox_strict_opposite_faces (q : Fin 3 → ℝ)
    (_hq : InEndpointBox q) (i : Fin 3) :
    (q i = endpointBoxLower i →
      rescaledOrientedNearOneMap 0 q i < 0) ∧
    (q i = endpointBoxUpper i →
      0 < rescaledOrientedNearOneMap 0 q i) := by
  have hinside := exactSeed_strictly_inside_endpointBox i
  rw [rescaledOrientedNearOneMap_zero,
    endpoint_eq_diagonal_seed_difference]
  fin_cases i <;>
    simp [endpointBoxLower, endpointBoxUpper] at hinside ⊢
  · constructor <;> intro hface
    · rw [hface]
      exact mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hinside.1)
    · rw [hface]
      exact hinside.2
  · constructor <;> intro hface
    · rw [hface]
      exact mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hinside.1)
    · rw [hface]
      exact hinside.2
  · constructor <;> intro hface
    · rw [hface]
      exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos)
        (sub_neg.mpr hinside.1)
    · rw [hface]
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (sub_pos.mpr hinside.2)

/-- The endpoint third-row faces have explicit margins.  These are the fixed
budgets that a quantitative positive-scale third-row estimate must preserve. -/
theorem endpointBox_third_face_margins (q : Fin 3 → ℝ)
    (_hq : InEndpointBox q) :
    (q 2 = endpointBoxLower 2 →
      rescaledOrientedNearOneMap 0 q 2 < -7) ∧
    (q 2 = endpointBoxUpper 2 →
      4 < rescaledOrientedNearOneMap 0 q 2) := by
  rcases pi_bounds with ⟨hpiLo, hpiHi⟩
  have hpi3Lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
    pow_lt_pow_left₀ hpiLo (by norm_num) (by norm_num)
  have hpi3Hi : π ^ 3 < (3.14159265358979323847 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hpiHi Real.pi_pos.le (by norm_num)
  have hpi5Lo : (3.14159265358979323846 : ℝ) ^ 5 < π ^ 5 :=
    pow_lt_pow_left₀ hpiLo (by norm_num) (by norm_num)
  have hpi5Hi : π ^ 5 < (3.14159265358979323847 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hpiHi Real.pi_pos.le (by norm_num)
  rw [rescaledOrientedNearOneMap_zero,
    endpoint_eq_diagonal_seed_difference]
  constructor
  · intro hface
    simp only [endpointBoxLower, Matrix.cons_val_two] at hface
    rw [hface]
    simp only [exactRescaledOrientedNearOneSeed, Matrix.cons_val_two]
    norm_num at hpiHi hpi3Lo hpi5Lo ⊢
    nlinarith
  · intro hface
    simp only [endpointBoxUpper, Matrix.cons_val_two] at hface
    rw [hface]
    simp only [exactRescaledOrientedNearOneSeed, Matrix.cons_val_two]
    norm_num at hpiLo hpi3Hi hpi5Hi ⊢
    nlinarith

/-- A uniform four-unit perturbation estimate from the cusp slice is sufficient
for both strict third-row face signs. -/
theorem third_face_signs_of_endpoint_perturbation {s : ℝ}
    (hperturb : ∀ q, InEndpointBox q →
      |rescaledOrientedNearOneMap s q 2 -
        rescaledOrientedNearOneMap 0 q 2| < 4) :
    ∀ q, InEndpointBox q →
      (q 2 = endpointBoxLower 2 →
        rescaledOrientedNearOneMap s q 2 < 0) ∧
      (q 2 = endpointBoxUpper 2 →
        0 < rescaledOrientedNearOneMap s q 2) := by
  intro q hq
  have hmargins := endpointBox_third_face_margins q hq
  have hdelta := abs_lt.mp (hperturb q hq)
  constructor
  · intro hface
    have hzero := hmargins.1 hface
    nlinarith
  · intro hface
    have hzero := hmargins.2 hface
    nlinarith

/-- The first rescaled row is jointly continuous in `s` and all box
coordinates at every endpoint point. -/
theorem continuousAt_rescaledOrientedNearOneMap_first_joint_zero
    (q : Fin 3 → ℝ) :
    ContinuousAt (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 0) (0, q) := by
  have hpair : ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) => (p.1, p.2 0)) (0, q) := by
    fun_prop
  have hpole : ContinuousAt
      (fun p : ℝ × ℝ => poleFreeFirstRescaledRow p.1 p.2) (0, q 0) := by
    have hangle : ContinuousAt (fun p : ℝ × ℝ =>
        typeFourAngleBar p.1
          (rescaledFirstPhysicalCoordinate p.1 p.2)) (0, q 0) := by
      unfold typeFourAngleBar densityCubeQuotient density
        typeFourAngleIncrement halfCos yCoord aCoord
        rescaledFirstPhysicalCoordinate
      fun_prop (disch := norm_num)
    unfold poleFreeFirstRescaledRow firstRescaledAlgebraicFactor
      yCoord aCoord rescaledFirstPhysicalCoordinate
    fun_prop (disch := first | exact hangle | norm_num)
  have hcomp := hpole.comp_of_eq hpair rfl
  apply hcomp.congr_of_eventuallyEq
  filter_upwards
  intro p
  simpa only [Function.comp_apply] using
    rescaledOrientedNearOneMap_first_eq_poleFree p.1 p.2

/-- Some exact reciprocal natural slice below `1/100` retains the first-row
endpoint face signs. -/
theorem exists_positive_rational_first_faces :
    ∃ n : ℕ,
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧
        poleFreeFirstRescaledRow s 52 < 0 ∧
        0 < poleFreeFirstRescaledRow s 54 := by
  have hlo0 : poleFreeFirstRescaledRow 0 52 < 0 := by
    rw [poleFreeFirstRescaledRow_zero]
    have hseed : (52 : ℝ) < π ^ 3 + 7 * π := by
      simpa [exactRescaledOrientedNearOneSeed] using seed_zero_bounds.1
    linarith
  have hhi0 : 0 < poleFreeFirstRescaledRow 0 54 := by
    rw [poleFreeFirstRescaledRow_zero]
    have hseed : π ^ 3 + 7 * π < (54 : ℝ) := by
      simpa [exactRescaledOrientedNearOneSeed] using seed_zero_bounds.2
    linarith
  have hlo : ∀ᶠ s in 𝓝 (0 : ℝ), poleFreeFirstRescaledRow s 52 < 0 :=
    (continuousAt_poleFreeFirstRescaledRow_zero 52).eventually_lt_const hlo0
  have hhi : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < poleFreeFirstRescaledRow s 54 :=
    (continuousAt_poleFreeFirstRescaledRow_zero 54).eventually_const_lt hhi0
  have hseq : ∀ᶠ n : ℕ in atTop,
      (poleFreeFirstRescaledRow (1 / (n + 1 : ℝ)) 52 < 0 ∧
        0 < poleFreeFirstRescaledRow (1 / (n + 1 : ℝ)) 54) ∧
        1 / (n + 1 : ℝ) < 1 / 100 :=
    tendsto_one_div_add_atTop_nhds_zero_nat
      ((hlo.and hhi).and
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 100)))
  rcases Filter.Eventually.exists hseq with ⟨n, hn⟩
  refine ⟨n, by positivity, hn.2, hn.1.1, hn.1.2⟩

/-- A positive exact rational `s` slice on which the first coordinate has
strict opposite signs on its two complete rational box faces. -/
theorem exists_positive_rational_first_face_cell :
    ∃ n : ℕ,
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧
        ∀ q, InEndpointBox q →
          (q 0 = endpointBoxLower 0 →
            rescaledOrientedNearOneMap s q 0 < 0) ∧
          (q 0 = endpointBoxUpper 0 →
            0 < rescaledOrientedNearOneMap s q 0) := by
  rcases exists_positive_rational_first_faces with
    ⟨n, hs0, hs, hlo, hhi⟩
  refine ⟨n, hs0, hs, ?_⟩
  intro q _hq
  constructor <;> intro hface
  · rw [rescaledOrientedNearOneMap_first_eq_poleFree, hface]
    simpa [endpointBoxLower] using hlo
  · rw [rescaledOrientedNearOneMap_first_eq_poleFree, hface]
    simpa [endpointBoxUpper] using hhi

/-- A compact family of strict inequalities at `s = 0` remains uniformly
strict for all sufficiently small `s`. -/
private lemma compact_eventually_forall_lt
    {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    {f : ℝ × (Fin 3 → ℝ) → ℝ} (hf : Continuous f) {c : ℝ}
    (h0 : ∀ q ∈ K, f (0, q) < c) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q ∈ K, f (s, q) < c := by
  let U : Set ((Fin 3 → ℝ) × ℝ) := {p | f (p.2, p.1) < c}
  have hUlocal : ∀ q ∈ K, U ∈ 𝓝 q ×ˢ 𝓝 (0 : ℝ) := by
    intro q hq
    rw [← nhds_prod_eq]
    exact ((hf.comp (by fun_prop :
        Continuous (fun p : (Fin 3 → ℝ) × ℝ => (p.2, p.1)))).continuousAt
      |>.eventually_lt_const (h0 q hq))
  have hU : U ∈ 𝓝ˢ K ×ˢ 𝓝 (0 : ℝ) :=
    hK.mem_nhdsSet_prod_of_forall hUlocal
  rcases mem_prod_iff.mp hU with ⟨V, hV, W, hW, hVW⟩
  filter_upwards [hW] with s hs
  intro q hq
  have hqs : (q, s) ∈ V ×ˢ W :=
    ⟨subset_of_mem_nhdsSet hV hq, hs⟩
  exact hVW hqs

/-- Pointwise continuity at the compact endpoint slice is enough for the same
uniform persistence conclusion. -/
private lemma compact_eventually_forall_lt_of_continuousAt
    {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    {f : ℝ × (Fin 3 → ℝ) → ℝ} {c : ℝ}
    (hf : ∀ q ∈ K, ContinuousAt f (0, q))
    (h0 : ∀ q ∈ K, f (0, q) < c) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q ∈ K, f (s, q) < c := by
  let U : Set ((Fin 3 → ℝ) × ℝ) := {p | f (p.2, p.1) < c}
  have hUlocal : ∀ q ∈ K, U ∈ 𝓝 q ×ˢ 𝓝 (0 : ℝ) := by
    intro q hq
    rw [← nhds_prod_eq]
    have hswap : ContinuousAt
        (fun p : (Fin 3 → ℝ) × ℝ => (p.2, p.1)) (q, 0) := by
      fun_prop
    exact (((hf q hq).comp_of_eq hswap rfl).eventually_lt_const (h0 q hq))
  have hU : U ∈ 𝓝ˢ K ×ˢ 𝓝 (0 : ℝ) :=
    hK.mem_nhdsSet_prod_of_forall hUlocal
  rcases mem_prod_iff.mp hU with ⟨V, hV, W, hW, hVW⟩
  filter_upwards [hW] with s hs
  intro q hq
  have hqs : (q, s) ∈ V ×ˢ W :=
    ⟨subset_of_mem_nhdsSet hV hq, hs⟩
  exact hVW hqs

private lemma endpointBox_isCompact :
    IsCompact {q : Fin 3 → ℝ | InEndpointBox q} := by
  rw [show {q : Fin 3 → ℝ | InEndpointBox q} =
      Set.pi Set.univ
        (fun i => Set.Icc (endpointBoxLower i) (endpointBoxUpper i)) by
    ext q
    simp only [InEndpointBox, Set.mem_ofPred_eq, Set.mem_pi,
      Set.mem_univ, true_implies]]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

/-- Uniformly near the endpoint, the first row retains opposite signs on its
complete pair of endpoint-box faces. -/
theorem eventually_first_face_cell :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q, InEndpointBox q →
      (q 0 = endpointBoxLower 0 →
        rescaledOrientedNearOneMap s q 0 < 0) ∧
      (q 0 = endpointBoxUpper 0 →
        0 < rescaledOrientedNearOneMap s q 0) := by
  have hlo0 : poleFreeFirstRescaledRow 0 52 < 0 := by
    rw [poleFreeFirstRescaledRow_zero]
    have hseed : (52 : ℝ) < π ^ 3 + 7 * π := by
      simpa [exactRescaledOrientedNearOneSeed] using seed_zero_bounds.1
    linarith
  have hhi0 : 0 < poleFreeFirstRescaledRow 0 54 := by
    rw [poleFreeFirstRescaledRow_zero]
    have hseed : π ^ 3 + 7 * π < (54 : ℝ) := by
      simpa [exactRescaledOrientedNearOneSeed] using seed_zero_bounds.2
    linarith
  have hlo : ∀ᶠ s in 𝓝 (0 : ℝ), poleFreeFirstRescaledRow s 52 < 0 :=
    (continuousAt_poleFreeFirstRescaledRow_zero 52).eventually_lt_const hlo0
  have hhi : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < poleFreeFirstRescaledRow s 54 :=
    (continuousAt_poleFreeFirstRescaledRow_zero 54).eventually_const_lt hhi0
  filter_upwards [hlo, hhi] with s hslo hshi
  intro q _hq
  constructor <;> intro hface
  · rw [rescaledOrientedNearOneMap_first_eq_poleFree, hface]
    simpa [endpointBoxLower] using hslo
  · rw [rescaledOrientedNearOneMap_first_eq_poleFree, hface]
    simpa [endpointBoxUpper] using hshi

/-- Uniformly near the endpoint, the second row retains opposite signs on its
complete pair of endpoint-box faces. -/
theorem eventually_second_face_cell :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q, InEndpointBox q →
      (q 1 = endpointBoxLower 1 →
        rescaledOrientedNearOneMap s q 1 < 0) ∧
      (q 1 = endpointBoxUpper 1 →
        0 < rescaledOrientedNearOneMap s q 1) := by
  let Klo : Set (Fin 3 → ℝ) :=
    {q | InEndpointBox q ∧ q 1 = endpointBoxLower 1}
  let Khi : Set (Fin 3 → ℝ) :=
    {q | InEndpointBox q ∧ q 1 = endpointBoxUpper 1}
  have hKlo : IsCompact Klo := by
    change IsCompact
      ({q : Fin 3 → ℝ | InEndpointBox q} ∩
        {q | q 1 = endpointBoxLower 1})
    exact endpointBox_isCompact.inter_right
      (isClosed_eq (continuous_apply 1) continuous_const)
  have hKhi : IsCompact Khi := by
    change IsCompact
      ({q : Fin 3 → ℝ | InEndpointBox q} ∩
        {q | q 1 = endpointBoxUpper 1})
    exact endpointBox_isCompact.inter_right
      (isClosed_eq (continuous_apply 1) continuous_const)
  have hmap : Continuous (fun p : ℝ × (Fin 3 → ℝ) =>
      rescaledOrientedNearOneMap p.1 p.2 1) := by
    simpa only [rescaledOrientedNearOneMap_second_eq_poleFree] using
      continuous_poleFreeSecondRescaledRow_joint
  have hlo : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ q ∈ Klo, rescaledOrientedNearOneMap s q 1 < 0 :=
    compact_eventually_forall_lt hKlo hmap (by
      intro q hq
      exact (endpointBox_strict_opposite_faces q hq.1 1).1 hq.2)
  have hhiNeg : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ q ∈ Khi, -rescaledOrientedNearOneMap s q 1 < 0 :=
    compact_eventually_forall_lt hKhi hmap.neg (by
      intro q hq
      exact neg_lt_zero.mpr
        ((endpointBox_strict_opposite_faces q hq.1 1).2 hq.2))
  filter_upwards [hlo, hhiNeg] with s hslo hshi
  intro q hq
  constructor
  · intro hface
    exact hslo q ⟨hq, hface⟩
  · intro hface
    exact neg_lt_zero.mp (hshi q ⟨hq, hface⟩)

/-- Uniformly near the endpoint, the third row retains opposite signs on its
complete pair of endpoint-box faces. -/
theorem eventually_third_face_cell :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ q, InEndpointBox q →
      (q 2 = endpointBoxLower 2 →
        rescaledOrientedNearOneMap s q 2 < 0) ∧
      (q 2 = endpointBoxUpper 2 →
        0 < rescaledOrientedNearOneMap s q 2) := by
  let Klo : Set (Fin 3 → ℝ) :=
    {q | InEndpointBox q ∧ q 2 = endpointBoxLower 2}
  let Khi : Set (Fin 3 → ℝ) :=
    {q | InEndpointBox q ∧ q 2 = endpointBoxUpper 2}
  have hKlo : IsCompact Klo := by
    change IsCompact
      ({q : Fin 3 → ℝ | InEndpointBox q} ∩
        {q | q 2 = endpointBoxLower 2})
    exact endpointBox_isCompact.inter_right
      (isClosed_eq (continuous_apply 2) continuous_const)
  have hKhi : IsCompact Khi := by
    change IsCompact
      ({q : Fin 3 → ℝ | InEndpointBox q} ∩
        {q | q 2 = endpointBoxUpper 2})
    exact endpointBox_isCompact.inter_right
      (isClosed_eq (continuous_apply 2) continuous_const)
  have hmap : ∀ q : Fin 3 → ℝ, ContinuousAt
      (fun p : ℝ × (Fin 3 → ℝ) =>
        rescaledOrientedNearOneMap p.1 p.2 2) (0, q) :=
    continuousAt_rescaledOrientedNearOneMap_third_joint
  have hlo : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ q ∈ Klo, rescaledOrientedNearOneMap s q 2 < 0 :=
    compact_eventually_forall_lt_of_continuousAt hKlo
      (fun q _ => hmap q) (by
        intro q hq
        exact (endpointBox_strict_opposite_faces q hq.1 2).1 hq.2)
  have hhiNeg : ∀ᶠ s in 𝓝 (0 : ℝ),
      ∀ q ∈ Khi, -rescaledOrientedNearOneMap s q 2 < 0 :=
    compact_eventually_forall_lt_of_continuousAt hKhi
      (fun q _ => (hmap q).neg) (by
        intro q hq
        exact neg_lt_zero.mpr
          ((endpointBox_strict_opposite_faces q hq.1 2).2 hq.2))
  filter_upwards [hlo, hhiNeg] with s hslo hshi
  intro q hq
  constructor
  · intro hface
    exact hslo q ⟨hq, hface⟩
  · intro hface
    exact neg_lt_zero.mp (hshi q ⟨hq, hface⟩)

/-- One exact positive reciprocal-natural slice retains all four complete face
signs for the first two rows of the rescaled map. -/
theorem exists_positive_rational_first_second_face_cell :
    ∃ n : ℕ,
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧
        (∀ q, InEndpointBox q →
          (q 0 = endpointBoxLower 0 →
            rescaledOrientedNearOneMap s q 0 < 0) ∧
          (q 0 = endpointBoxUpper 0 →
            0 < rescaledOrientedNearOneMap s q 0)) ∧
        (∀ q, InEndpointBox q →
          (q 1 = endpointBoxLower 1 →
            rescaledOrientedNearOneMap s q 1 < 0) ∧
          (q 1 = endpointBoxUpper 1 →
            0 < rescaledOrientedNearOneMap s q 1)) := by
  have hfaces : ∀ᶠ s in 𝓝 (0 : ℝ),
      (∀ q, InEndpointBox q →
        (q 0 = endpointBoxLower 0 →
          rescaledOrientedNearOneMap s q 0 < 0) ∧
        (q 0 = endpointBoxUpper 0 →
          0 < rescaledOrientedNearOneMap s q 0)) ∧
      (∀ q, InEndpointBox q →
        (q 1 = endpointBoxLower 1 →
          rescaledOrientedNearOneMap s q 1 < 0) ∧
        (q 1 = endpointBoxUpper 1 →
          0 < rescaledOrientedNearOneMap s q 1)) :=
    eventually_first_face_cell.and eventually_second_face_cell
  have hseq : ∀ᶠ n : ℕ in atTop,
      ((∀ q, InEndpointBox q →
        (q 0 = endpointBoxLower 0 →
          rescaledOrientedNearOneMap (1 / (n + 1 : ℝ)) q 0 < 0) ∧
        (q 0 = endpointBoxUpper 0 →
          0 < rescaledOrientedNearOneMap (1 / (n + 1 : ℝ)) q 0)) ∧
      (∀ q, InEndpointBox q →
        (q 1 = endpointBoxLower 1 →
          rescaledOrientedNearOneMap (1 / (n + 1 : ℝ)) q 1 < 0) ∧
        (q 1 = endpointBoxUpper 1 →
          0 < rescaledOrientedNearOneMap (1 / (n + 1 : ℝ)) q 1))) ∧
      1 / (n + 1 : ℝ) < 1 / 100 :=
    tendsto_one_div_add_atTop_nhds_zero_nat
      (hfaces.and
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 100)))
  rcases Filter.Eventually.exists hseq with ⟨n, hn⟩
  exact ⟨n, by positivity, hn.2, hn.1.1, hn.1.2⟩

/-- All six opposite-face inequalities for the exact rational endpoint box at
the scale `s`. -/
def HasEndpointBoxFaceSigns (s : ℝ) : Prop :=
  ∀ q, InEndpointBox q → ∀ i,
    (q i = endpointBoxLower i →
      rescaledOrientedNearOneMap s q i < 0) ∧
    (q i = endpointBoxUpper i →
      0 < rescaledOrientedNearOneMap s q i)

/-- All six complete face signs persist simultaneously near the cusp. -/
theorem eventually_all_face_cell :
    ∀ᶠ s in 𝓝 (0 : ℝ), HasEndpointBoxFaceSigns s := by
  filter_upwards [eventually_first_face_cell, eventually_second_face_cell,
    eventually_third_face_cell] with s hfirst hsecond hthird
  intro q hq i
  fin_cases i
  · exact hfirst q hq
  · exact hsecond q hq
  · exact hthird q hq

/-- One exact positive reciprocal-natural scale below `1/100` validates all
six complete faces of the rational endpoint box simultaneously. -/
theorem exists_positive_rational_all_face_cell :
    ∃ n : ℕ,
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ HasEndpointBoxFaceSigns s := by
  have hseq : ∀ᶠ n : ℕ in atTop,
      HasEndpointBoxFaceSigns (1 / (n + 1 : ℝ)) ∧
        1 / (n + 1 : ℝ) < 1 / 100 :=
    tendsto_one_div_add_atTop_nhds_zero_nat
      (eventually_all_face_cell.and
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 100)))
  rcases Filter.Eventually.exists hseq with ⟨n, hn⟩
  exact ⟨n, by positivity, hn.2, hn.1⟩

private lemma first_row_continuousOn {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) :
    ContinuousOn (fun q0 => poleFreeFirstRescaledRow s q0) (Icc 52 54) := by
  intro q0 hq0
  have hqpos : 0 ≤ q0 := by linarith [hq0.1]
  have hsle : s ≤ 1 / 100 := hs.le
  have hy0 : 0 ≤ yCoord s (rescaledFirstPhysicalCoordinate s q0) := by
    simp only [yCoord, aCoord, rescaledFirstPhysicalCoordinate]
    positivity
  have hyhi : yCoord s (rescaledFirstPhysicalCoordinate s q0) < 1 := by
    simp only [yCoord, aCoord, rescaledFirstPhysicalCoordinate]
    have hqterm0 : 0 ≤ s ^ 2 * q0 := by positivity
    have hinner : 1 + s * (π + s * π ^ 2 + s ^ 2 * q0) < 2 := by
      have hp : π < 4 := Real.pi_lt_four
      have hp0 : 0 < π := Real.pi_pos
      have hs2 : s ^ 2 < (1 / 100 : ℝ) ^ 2 := by nlinarith
      have hs2q : s ^ 2 * q0 ≤ (1 / 100 : ℝ) ^ 2 * 54 :=
        mul_le_mul hs2.le hq0.2 hqpos (by positivity)
      have hsppi : s * π < (1 / 100 : ℝ) * 4 := calc
        s * π < s * 4 := mul_lt_mul_of_pos_left hp hs0
        _ < (1 / 100 : ℝ) * 4 := mul_lt_mul_of_pos_right hs (by norm_num)
      have hs2pi2 : s ^ 2 * π ^ 2 < (1 / 100 : ℝ) ^ 2 * 16 := by
        have hp2 : π ^ 2 < (4 : ℝ) ^ 2 :=
          pow_lt_pow_left₀ hp hp0.le (by norm_num)
        calc
          s ^ 2 * π ^ 2 < (1 / 100 : ℝ) ^ 2 * π ^ 2 :=
            mul_lt_mul_of_pos_right hs2 (sq_pos_of_pos hp0)
          _ < (1 / 100 : ℝ) ^ 2 * 16 := by
            have hp2' : π ^ 2 < (16 : ℝ) := by
              norm_num at hp2 ⊢
              exact hp2
            exact mul_lt_mul_of_pos_left hp2' (by norm_num)
      nlinarith
    nlinarith [mul_lt_mul_of_pos_left hinner hs0]
  have hyne :
      1 - yCoord s (rescaledFirstPhysicalCoordinate s q0) ^ 2 ≠ 0 := by
    have hy2 : yCoord s (rescaledFirstPhysicalCoordinate s q0) ^ 2 < 1 := by
      nlinarith
    nlinarith
  have hfourden : 1 + s * yCoord s
      (rescaledFirstPhysicalCoordinate s q0) ≠ 0 := by positivity
  have hangle : ContinuousAt (fun x : ℝ =>
      typeFourAngleBar s (rescaledFirstPhysicalCoordinate s x)) q0 := by
    unfold typeFourAngleBar densityCubeQuotient density typeFourAngleIncrement
      halfCos yCoord aCoord rescaledFirstPhysicalCoordinate
    fun_prop (disch := first | exact hyne | exact hfourden | positivity)
  have hrow : ContinuousAt
      (fun x : ℝ => poleFreeFirstRescaledRow s x) q0 := by
    unfold poleFreeFirstRescaledRow firstRescaledAlgebraicFactor
      yCoord aCoord rescaledFirstPhysicalCoordinate
    fun_prop (disch := first | exact hangle | positivity)
  exact hrow.continuousWithinAt

set_option maxHeartbeats 0 in
-- The complete three-row denominator proof exceeds the default elaboration budget.
/-- The complete rescaled oriented map is continuous on the rational endpoint
box at every sufficiently small positive scale. -/
theorem continuousOn_rescaledOrientedNearOneMap_endpointBox {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100) :
    ContinuousOn (rescaledOrientedNearOneMap s) {q | InEndpointBox q} := by
  have hsne : s ≠ 0 := ne_of_gt hs0
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · change ContinuousOn
      (fun q => rescaledOrientedNearOneMap s q 0) {q | InEndpointBox q}
    intro q hq
    have hq0 : q 0 ∈ Icc (52 : ℝ) 54 := hq 0
    have happly : ContinuousWithinAt (fun x : Fin 3 → ℝ => x 0)
        {x | InEndpointBox x} q :=
      (continuous_apply 0).continuousAt.continuousWithinAt
    have hcomp := ContinuousWithinAt.comp
      (f := fun x : Fin 3 → ℝ => x 0)
      ((first_row_continuousOn hs0 hs) (q 0) hq0) happly
      (fun x hx => hx 0)
    simpa only [Function.comp_def,
      rescaledOrientedNearOneMap_first_eq_poleFree] using hcomp
  · change ContinuousOn
      (fun q => rescaledOrientedNearOneMap s q 1) {q | InEndpointBox q}
    intro q _hq
    have hpair : Continuous (fun x : Fin 3 → ℝ => (s, x)) := by
      fun_prop
    rw [show (fun q => rescaledOrientedNearOneMap s q 1) =
        fun q => poleFreeSecondRescaledRow s q by
      funext x
      exact rescaledOrientedNearOneMap_second_eq_poleFree s x]
    exact
      (continuous_poleFreeSecondRescaledRow_joint.comp hpair).continuousAt.continuousWithinAt
  · change ContinuousOn
      (fun q => rescaledOrientedNearOneMap s q 2) {q | InEndpointBox q}
    intro q hq
    let Z : (Fin 3 → ℝ) → ℝ := fun x =>
      tangentCenteredPoint s (fun j => s ^ 2 * x j) 0
    let Af : (Fin 3 → ℝ) → ℝ := fun x =>
      tangentCenteredPoint s (fun j => s ^ 2 * x j) 1
    let Bf : (Fin 3 → ℝ) → ℝ := fun x =>
      tangentCenteredPoint s (fun j => s ^ 2 * x j) 2
    have hZ : ContinuousAt Z q := by
      rw [show Z = fun x : Fin 3 → ℝ =>
          π + s * π ^ 2 + s ^ 2 * x 0 by
        funext x
        simp [Z, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
          exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]]
      have h0 := continuousAt_apply 0 q
      have hc : ContinuousAt
          (fun _ : Fin 3 → ℝ => π + s * π ^ 2) q := continuousAt_const
      have hm : ContinuousAt
          (fun x : Fin 3 → ℝ => s ^ 2 * x 0) q :=
        continuousAt_const.mul h0
      exact hc.add hm
    have hA : ContinuousAt Af q := by
      rw [show Af = fun x : Fin 3 → ℝ =>
          5 * π / 12 + s * ((43 * π ^ 2 + 1056) / 144) +
            s ^ 2 * (5 * x 0 / 12 + x 1) by
        funext x
        simp [Af, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
          exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring]
      have h0 := continuousAt_apply 0 q
      have h1 := continuousAt_apply 1 q
      fun_prop (disch := assumption)
    have hB : ContinuousAt Bf q := by
      rw [show Bf = fun x : Fin 3 → ℝ =>
          -44 + 19 * π ^ 2 / 24 +
            s * (π * (295 * π ^ 2 - 14256) / 216) +
            s ^ 2 * ((109 * π ^ 2 - 5376) / (72 * π) * x 0 +
              (2880 - 7 * π ^ 2) / (6 * π) * x 1 + x 2) by
        funext x
        simp [Bf, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
          exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        ring]
      have h0 := continuousAt_apply 0 q
      have h1 := continuousAt_apply 1 q
      have h2 := continuousAt_apply 2 q
      fun_prop (disch := first | assumption | positivity)
    have hq0 := hq (0 : Fin 3)
    have hq1 := hq (1 : Fin 3)
    have hq2 := hq (2 : Fin 3)
    change 52 ≤ q 0 ∧ q 0 ≤ 54 at hq0
    change 27 ≤ q 1 ∧ q 1 ≤ 28 at hq1
    change -3822 ≤ q 2 ∧ q 2 ≤ -3821 at hq2
    have hq0pos : 0 ≤ q 0 := by linarith [hq0.1]
    have hq1pos : 0 ≤ q 1 := by linarith [hq1.1]
    have hs2 : s ^ 2 < (1 / 100 : ℝ) ^ 2 := by nlinarith
    have hp2 : π ^ 2 < (4 : ℝ) ^ 2 :=
      pow_lt_pow_left₀ Real.pi_lt_four Real.pi_pos.le (by norm_num)
    have hZeq : Z q = π + s * π ^ 2 + s ^ 2 * q 0 := by
      simp [Z, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
        exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have hp2' : π ^ 2 < (16 : ℝ) := by
      norm_num at hp2 ⊢
      exact hp2
    have hZpos : 0 < Z q := by
      rw [hZeq]
      positivity
    have hZ0 : 0 ≤ Z q := hZpos.le
    have hsPi2 : s * π ^ 2 < (1 / 100 : ℝ) * 16 :=
      mul_lt_mul hs hp2'.le (sq_pos_of_pos Real.pi_pos) (by norm_num)
    have hq0pos' : 0 < q 0 := by linarith [hq0.1]
    have hs2q0 : s ^ 2 * q 0 < (1 / 100 : ℝ) ^ 2 * 54 :=
      mul_lt_mul hs2 hq0.2 hq0pos' (by norm_num)
    have hZ4 : Z q < 4 := by
      rw [hZeq]
      have hpihi := Real.pi_lt_d20
      norm_num at hsPi2 hs2q0 hpihi ⊢
      nlinarith
    have hAeq : Af q = 5 * π / 12 +
        s * ((43 * π ^ 2 + 1056) / 144) +
        s ^ 2 * (5 * q 0 / 12 + q 1) := by
      simp [Af, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
        exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      ring
    have hA0 : 0 ≤ Af q := by
      rw [hAeq]
      positivity
    let T : ℝ := π * (295 * π ^ 2 - 14256) / 216
    let C0 : ℝ := (109 * π ^ 2 - 5376) / (72 * π)
    let C1 : ℝ := (2880 - 7 * π ^ 2) / (6 * π)
    have hTlo : (-200 : ℝ) < T := by
      have hp3lo : (3.14159265358979323846 : ℝ) ^ 3 < π ^ 3 :=
        pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)
      have hpihi := Real.pi_lt_d20
      dsimp only [T]
      rw [show π * (295 * π ^ 2 - 14256) / 216 =
        (295 * π ^ 3 - 14256 * π) / 216 by ring]
      norm_num at hp3lo hpihi ⊢
      nlinarith
    have hTneg : T < 0 := by
      dsimp only [T]
      have hinner : 295 * π ^ 2 - 14256 < 0 := by
        norm_num at hp2 ⊢
        nlinarith
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos hinner)
        (by norm_num)
    have hC0lo : (-25 : ℝ) < C0 := by
      dsimp only [C0]
      rw [lt_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
      have hp2lo : (3 : ℝ) ^ 2 < π ^ 2 :=
        pow_lt_pow_left₀ (by nlinarith [Real.pi_gt_three])
          (by norm_num) (by norm_num)
      nlinarith [Real.pi_gt_three]
    have hC0neg : C0 < 0 := by
      dsimp only [C0]
      exact div_neg_of_neg_of_pos (by nlinarith [hp2])
        (mul_pos (by norm_num) Real.pi_pos)
    have hC1pos : 0 < C1 := by
      dsimp only [C1]
      exact div_pos (by nlinarith [hp2])
        (mul_pos (by norm_num) Real.pi_pos)
    have hC0q0 : (-1350 : ℝ) < C0 * q 0 := calc
      (-1350 : ℝ) = (-25) * 54 := by norm_num
      _ < C0 * 54 := mul_lt_mul_of_pos_right hC0lo (by norm_num)
      _ ≤ C0 * q 0 := mul_le_mul_of_nonpos_left hq0.2 hC0neg.le
    have hQ : (-5200 : ℝ) <
        C0 * q 0 + C1 * q 1 + q 2 := by
      have hC1q1 : 0 ≤ C1 * q 1 :=
        mul_nonneg hC1pos.le hq1pos
      linarith [hq2.1]
    have hsT : (-2 : ℝ) < s * T := by
      have h₁ : (-200 : ℝ) * s < T * s :=
        mul_lt_mul_of_pos_right hTlo hs0
      have h₂ : (-2 : ℝ) < (-200) * s := by
        norm_num at hs ⊢
        nlinarith
      nlinarith
    have hs2Q : (-1 : ℝ) <
        s ^ 2 * (C0 * q 0 + C1 * q 1 + q 2) := by
      have h₁ := mul_lt_mul_of_pos_left hQ (sq_pos_of_pos hs0)
      have h₂ : (-1 : ℝ) < (-5200) * s ^ 2 := by
        norm_num at hs2 ⊢
        nlinarith
      nlinarith
    have hBeq : Bf q =
        -44 + 19 * π ^ 2 / 24 + s * T +
          s ^ 2 * (C0 * q 0 + C1 * q 1 + q 2) := by
      simp [Bf, tangentCenteredPoint, exactCuspPoint, exactCuspTangent,
        exactCuspShear, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        T, C0, C1]
      ring
    have hBlo : (-50 : ℝ) < Bf q := by
      rw [hBeq]
      have : 0 < 19 * π ^ 2 / 24 := by positivity
      linarith
    have hy0 : 0 ≤ yCoord s (Z q) := by
      simp only [yCoord, aCoord]
      positivity
    have hylt : yCoord s (Z q) < 1 := by
      have hsZ : s * Z q < (1 / 100 : ℝ) * 4 :=
        mul_lt_mul hs hZ4.le hZpos (by norm_num)
      simp only [yCoord, aCoord]
      have hinner : 1 + s * Z q < 2 := by nlinarith
      have hinner0 : 0 < 1 + s * Z q := by positivity
      have hmul := mul_lt_mul hs hinner.le hinner0 (by norm_num)
      nlinarith
    have hy : 1 - yCoord s (Z q) ^ 2 ≠ 0 := by
      have : yCoord s (Z q) ^ 2 < 1 := by nlinarith
      nlinarith
    have hyprod :
        (1 + s ^ 2) * (1 - yCoord s (Z q) ^ 2) ≠ 0 :=
      mul_ne_zero (by positivity) hy
    have hhalfY : halfCos (yCoord s (Z q)) ≠ 0 := by
      unfold halfCos
      exact div_ne_zero hy (by positivity)
    have hdFour : 1 + s * yCoord s (Z q) ≠ 0 := by positivity
    have hsZ : s * Z q < (1 / 100 : ℝ) * 4 :=
      mul_lt_mul hs hZ4.le hZpos (by norm_num)
    have hs2B : (-1 : ℝ) < s ^ 2 * Bf q := by
      by_cases hBsign : 0 ≤ Bf q
      · nlinarith [mul_nonneg (sq_nonneg s) hBsign]
      · have h₁ := mul_lt_mul_of_pos_left hBlo (sq_pos_of_pos hs0)
        have h₂ : (-1 : ℝ) < (-50) * s ^ 2 := by
          norm_num at hs2 ⊢
          nlinarith
        nlinarith
    have hrv : 0 < rCoord s (Af q) +
        s * eCoord s (Z q) (Af q) (Bf q) := by
      rw [show rCoord s (Af q) +
          s * eCoord s (Z q) (Af q) (Bf q) =
        2 + 7 * s * Af q - 2 * s * Z q + s ^ 2 * Bf q by
        simp only [rCoord, eCoord]
        ring]
      have : 0 ≤ 7 * s * Af q := by positivity
      nlinarith
    have hw : 0 < wCoord s (Af q) := by
      simp only [wCoord]
      exact mul_pos hs0 (by simp [rCoord]; positivity)
    have hv : 0 < vCoord s (Z q) (Af q) (Bf q) := by
      simp only [vCoord]
      exact mul_pos hs0 hrv
    have hdThree :
        1 + wCoord s (Af q) * vCoord s (Z q) (Af q) (Bf q) ≠ 0 := by
      positivity
    have hpoly : ContinuousAt
        (fun x => H3hatPolynomial s (Z x) (Af x) (Bf x) π) q :=
      continuousAt_H3hatPolynomial_comp s π hZ hA hB
    have hK : ContinuousAt
        (fun x => (NearOneNormalizedFlow.K (Af x)).eval s) q := by
      simp [NearOneNormalizedFlow.K, NearOneNormalizedFlow.R,
        NearOneNormalizedFlow.A]
      fun_prop (disch := positivity)
    have hremFour : ContinuousAt
        (fun x => atanQuotientSqRemainder
          (s ^ 2 * Z x / (1 + s * yCoord s (Z x)))) q :=
      continuous_atanQuotientSqRemainder.continuousAt.comp (by
        unfold yCoord aCoord
        fun_prop (disch := exact hdFour))
    have hremThree : ContinuousAt
        (fun x => atanQuotientSqRemainder
          (s ^ 2 * eCoord s (Z x) (Af x) (Bf x) /
            (1 + wCoord s (Af x) *
              vCoord s (Z x) (Af x) (Bf x)))) q :=
      continuous_atanQuotientSqRemainder.continuousAt.comp (by
        unfold wCoord vCoord rCoord eCoord
        fun_prop (disch := exact hdThree))
    have hatanW : ContinuousAt
        (fun x => atanQuotient (wCoord s (Af x))) q :=
      continuous_atanQuotient.continuousAt.comp (by
        unfold wCoord rCoord
        fun_prop)
    have hregular : ContinuousAt
        (fun x => regularizedThirdRow s (Z x) (Af x) (Bf x) π) q := by
      unfold regularizedThirdRow areaAngleCorrectionBar
        foldAngleCorrectionBar typeFourAngleBar typeThreeAngleBar2
        typeFourAngleBar2 typeThreeAngleIncrementBar2
        typeFourAngleIncrementBar2 typeFourAngleIncrement densityCubeQuotient
        density halfCos foldDenominator typeFourSineProductBar areaDenominator
        areaPiWeight yCoord wCoord vCoord aCoord rCoord eCoord
      fun_prop (disch := first | assumption | positivity)
    have hout : ContinuousWithinAt
        (fun x => -(regularizedThirdRow s (Z x) (Af x) (Bf x) π / s ^ 2))
        {x | InEndpointBox x} q :=
      (hregular.div_const (s ^ 2)).neg.continuousWithinAt
    apply hout.congr
    · intro x _hx
      dsimp only [Z, Af, Bf]
      rw [rescaledOrientedNearOneMap_third_eq_neg_poleFree,
        poleFreeThirdRescaledRow, if_neg hsne]
    · dsimp only [Z, Af, Bf]
      rw [rescaledOrientedNearOneMap_third_eq_neg_poleFree,
        poleFreeThirdRescaledRow, if_neg hsne]

/-- On one positive exact rational slice, the first rescaled equation has a
root between the two certified rational faces. -/
theorem positive_rational_first_row_root :
    ∃ (n : ℕ) (q0 : ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ q0 ∈ Icc (52 : ℝ) 54 ∧
        poleFreeFirstRescaledRow s q0 = 0 := by
  rcases exists_positive_rational_first_faces with ⟨n, hs0, hs, hlo, hhi⟩
  let s : ℝ := 1 / (n + 1 : ℝ)
  have hcont := first_row_continuousOn hs0 hs
  have himage := intermediate_value_Icc
    (show (52 : ℝ) ≤ 54 by norm_num) hcont
    (show (0 : ℝ) ∈ Icc (poleFreeFirstRescaledRow s 52)
        (poleFreeFirstRescaledRow s 54) from ⟨hlo.le, hhi.le⟩)
  rcases himage with ⟨q0, hq0, hroot⟩
  exact ⟨n, q0, hs0, hs, hq0, hroot⟩

/-- The first face certificate yields a genuine first-row zero of the rescaled
map at a positive exact rational `s`, with all three coordinates in the
rational endpoint box. -/
theorem positive_rational_rescaled_first_row_root :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q 0 = 0 := by
  rcases positive_rational_first_row_root with
    ⟨n, q0, hs0, hs, hq0, hroot⟩
  let q : Fin 3 → ℝ := ![q0, 27, -3822]
  have hq : InEndpointBox q := by
    intro i
    fin_cases i <;>
      simp [q, endpointBoxLower, endpointBoxUpper, hq0] <;>
      norm_num
  refine ⟨n, q, hs0, hs, hq, ?_⟩
  rw [rescaledOrientedNearOneMap_first_eq_poleFree]
  simpa [q] using hroot

/-- Poincare--Miranda turns complete opposite-face signs at any sufficiently
small positive scale into a simultaneous root in the endpoint box. -/
theorem rescaled_all_rows_root_of_face_signs {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1 / 100)
    (hfaces : HasEndpointBoxFaceSigns s) :
    ∃ q : Fin 3 → ℝ,
      InEndpointBox q ∧ rescaledOrientedNearOneMap s q = 0 := by
  have hab : ∀ i, endpointBoxLower i < endpointBoxUpper i := by
    intro i
    fin_cases i <;> norm_num [endpointBoxLower, endpointBoxUpper]
  have hboxToPredicate :
      ∀ q ∈ Icc endpointBoxLower endpointBoxUpper, InEndpointBox q := by
    intro q hq i
    exact ⟨hq.1 i, hq.2 i⟩
  have hcontinuous : ContinuousOn (rescaledOrientedNearOneMap s)
      (Icc endpointBoxLower endpointBoxUpper) :=
    (continuousOn_rescaledOrientedNearOneMap_endpointBox hs0 hs).mono
      hboxToPredicate
  have hlower : ∀ q ∈ Icc endpointBoxLower endpointBoxUpper, ∀ i,
      q i = endpointBoxLower i →
        rescaledOrientedNearOneMap s q i ≤ 0 := by
    intro q hq i hqi
    exact ((hfaces q (hboxToPredicate q hq) i).1 hqi).le
  have hupper : ∀ q ∈ Icc endpointBoxLower endpointBoxUpper, ∀ i,
      q i = endpointBoxUpper i →
        0 ≤ rescaledOrientedNearOneMap s q i := by
    intro q hq i hqi
    exact ((hfaces q (hboxToPredicate q hq) i).2 hqi).le
  obtain ⟨q, hq, hroot⟩ :=
    BoxPoincareMiranda.poincareMiranda hab
      (rescaledOrientedNearOneMap s) hcontinuous hlower hupper
  exact ⟨q, hboxToPredicate q hq, hroot⟩

/-- One exact positive reciprocal-natural scale below `1/100` has a
simultaneous zero of all three rescaled equations inside the rational endpoint
box. -/
theorem positive_rational_rescaled_all_rows_root :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        rescaledOrientedNearOneMap s q = 0 := by
  rcases exists_positive_rational_all_face_cell with
    ⟨n, hs0, hs, hfaces⟩
  obtain ⟨q, hq, hroot⟩ :=
    rescaled_all_rows_root_of_face_signs hs0 hs hfaces
  exact ⟨n, q, hs0, hs, hq, hroot⟩

/-- The validated positive rescaled cell yields a genuine zero of the complete
corrected near-one analytic system in tangent-centered coordinates. -/
theorem positive_rational_corrected_nearOneRoot :
    ∃ (n : ℕ) (q : Fin 3 → ℝ),
      let s : ℝ := 1 / (n + 1 : ℝ)
      0 < s ∧ s < 1 / 100 ∧ InEndpointBox q ∧
        nearOneRootMap s π
          (tangentCenteredPoint s (fun j => s ^ 2 * q j)) = 0 := by
  rcases positive_rational_rescaled_all_rows_root with
    ⟨n, q, hs0, hs, hq, hroot⟩
  refine ⟨n, q, hs0, hs, hq, ?_⟩
  exact (rescaledOrientedNearOneMap_eq_zero_iff (ne_of_gt hs0) q).mp hroot

end NearOneRescaledFirstCell

end

end NearOneRegularizedThirdRow
