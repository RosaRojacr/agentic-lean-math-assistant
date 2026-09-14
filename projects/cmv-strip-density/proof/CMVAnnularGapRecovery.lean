/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVRelaxedMinimizingSequence
import CMVSmoothAmbientTransport
import CMVRelativeLevelTraceAveraging
import CMVFiniteBandCosts
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A non-minimizing smooth recovery sequence with persistent hidden frontier

Cañete, Section 2 (printed pages 2--3), defines the relaxed perimeter by an
infimum over smooth domains converging globally in characteristic-function
`L¹`.  Global convergence alone does not say that an arbitrary recovery
sequence realizes that infimum.  This module tests that precise quantifier with
the actual density-two target `CMVRelaxation.unitDisk`.

The approximants delete a shrinking closed annulus around radius `1/4`.  Their
literal complete frontiers are three disjoint circles.  The deleted area tends
to zero, while the two hidden circles retain total length `π`.
-/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology NNReal symmDiff ContDiff BigOperators

noncomputable section

namespace CMVRelaxation.AnnularGapRecovery

/-- Squared Euclidean radius in the coordinate plane. -/
def radiusSq (p : PlanePoint) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- Inner edge of the deleted annulus. -/
def innerRadius (epsilon : ℝ) : ℝ := 1 / 4 - epsilon

/-- Outer edge of the deleted annulus. -/
def outerRadius (epsilon : ℝ) : ℝ := 1 / 4 + epsilon

/-- A coordinate circle of radius `r`. -/
def radialCircle (r : ℝ) : Set PlanePoint := {p | radiusSq p = r ^ 2}

/-- The unit disk with the closed annulus
`innerRadius epsilon ≤ |p| ≤ outerRadius epsilon` deleted. -/
def domain (epsilon : ℝ) : Set PlanePoint :=
  {p | radiusSq p < innerRadius epsilon ^ 2 ∨
    (outerRadius epsilon ^ 2 < radiusSq p ∧ radiusSq p < 1)}

lemma radiusSq_nonneg (p : PlanePoint) : 0 ≤ radiusSq p := by
  unfold radiusSq
  positivity

lemma radiusSq_eq_norm_sq (p : PlanePoint) :
    radiusSq p = ‖planeEuclideanHomeomorph p‖ ^ 2 := by
  symm
  simpa [radiusSq, sq_abs] using
    WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 p)

lemma innerRadius_pos {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) : 0 < innerRadius epsilon := by
  unfold innerRadius
  norm_num at hepsilon_le ⊢
  linarith

lemma innerRadius_lt_outerRadius {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    innerRadius epsilon < outerRadius epsilon := by
  unfold innerRadius outerRadius
  linarith

lemma outerRadius_lt_one {epsilon : ℝ} (hepsilon_le : epsilon ≤ 1 / 64) :
    outerRadius epsilon < 1 := by
  unfold outerRadius
  norm_num at hepsilon_le ⊢
  linarith

lemma radiusSq_lt_sq_iff_norm_lt {p : PlanePoint} {r : ℝ} (hr : 0 ≤ r) :
    radiusSq p < r ^ 2 ↔ ‖planeEuclideanHomeomorph p‖ < r := by
  rw [radiusSq_eq_norm_sq]
  exact sq_lt_sq₀ (norm_nonneg (planeEuclideanHomeomorph p)) hr

lemma sq_lt_radiusSq_iff_lt_norm {p : PlanePoint} {r : ℝ} (hr : 0 ≤ r) :
    r ^ 2 < radiusSq p ↔ r < ‖planeEuclideanHomeomorph p‖ := by
  rw [radiusSq_eq_norm_sq]
  exact sq_lt_sq₀ hr (norm_nonneg (planeEuclideanHomeomorph p))

/-- Euclidean presentation used only to calculate the complete frontier. -/
def euclideanDomain (a b : ℝ) : Set EuclideanPlane :=
  ball 0 a ∪ ((closedBall 0 b)ᶜ ∩ ball 0 1)

lemma domain_eq_preimage_euclideanDomain {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 64) :
    domain epsilon = planeEuclideanHomeomorph ⁻¹'
      euclideanDomain (innerRadius epsilon) (outerRadius epsilon) := by
  have ha := (innerRadius_pos hepsilon hepsilon_le).le
  have hb : 0 ≤ outerRadius epsilon :=
    (innerRadius_pos hepsilon hepsilon_le).le.trans
      (innerRadius_lt_outerRadius hepsilon).le
  ext p
  have hone :
      radiusSq p < 1 ↔ ‖planeEuclideanHomeomorph p‖ < 1 := by
    simpa only [one_pow] using
      (radiusSq_lt_sq_iff_norm_lt
        (p := p) (r := 1) (by norm_num : (0 : ℝ) ≤ 1))
  simp only [domain, euclideanDomain, mem_ofPred_eq, mem_preimage, mem_union,
    mem_inter_iff, mem_compl_iff, mem_ball, mem_closedBall, dist_zero_right]
  rw [radiusSq_lt_sq_iff_norm_lt ha, sq_lt_radiusSq_iff_lt_norm hb, hone]
  simp only [not_le]

lemma radialCircle_eq_preimage_sphere {r : ℝ} (hr : 0 ≤ r) :
    radialCircle r = planeEuclideanHomeomorph ⁻¹' sphere 0 r := by
  ext p
  simp only [radialCircle, mem_ofPred_eq, mem_preimage, mem_sphere, dist_zero_right]
  rw [radiusSq_eq_norm_sq]
  exact sq_eq_sq₀ (norm_nonneg (planeEuclideanHomeomorph p)) hr

private lemma frontier_euclideanDomain {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb1 : b < 1) :
    frontier (euclideanDomain a b) = sphere 0 a ∪ sphere 0 b ∪ sphere 0 1 := by
  have hb : 0 < b := ha.trans hab
  have hopen : IsOpen (euclideanDomain a b) :=
    isOpen_ball.union (isClosed_closedBall.isOpen_compl.inter isOpen_ball)
  apply Subset.antisymm
  · intro p hp
    rcases frontier_union_subset (ball 0 a) ((closedBall 0 b)ᶜ ∩ ball 0 1) hp with
      hpInner | hpAnnulus
    · exact Or.inl (Or.inl (by
        rw [frontier_ball (0 : EuclideanPlane) ha.ne'] at hpInner
        exact hpInner.1))
    · rcases frontier_inter_subset (closedBall 0 b)ᶜ (ball 0 1) hpAnnulus.2 with
        hpB | hpOne
      · exact Or.inl (Or.inr (by
          rw [frontier_compl, frontier_closedBall (0 : EuclideanPlane) hb.ne'] at hpB
          exact hpB.1))
      · exact Or.inr (by
          rw [frontier_ball (0 : EuclideanPlane) one_ne_zero] at hpOne
          exact hpOne.2)
  · rintro p ((hpA | hpB) | hpOne)
    · rw [hopen.frontier_eq]
      refine ⟨closure_mono (show ball 0 a ⊆ euclideanDomain a b from
        subset_union_left) ?_, ?_⟩
      · rw [← frontier_ball (0 : EuclideanPlane) ha.ne'] at hpA
        exact frontier_subset_closure hpA
      · rw [euclideanDomain]
        simp only [mem_union, mem_inter_iff, mem_compl_iff]
        rw [mem_sphere, dist_zero_right] at hpA
        simp only [mem_ball, mem_closedBall, dist_zero_right, hpA, lt_self_iff_false,
          false_or, not_le]
        exact fun h => (not_lt_of_ge hab.le) h.1
    · rw [hopen.frontier_eq]
      let T : Set EuclideanPlane := (closedBall 0 b)ᶜ ∩ ball 0 1
      have hpDist : dist p 0 = b := by
        simpa only [mem_sphere] using hpB
      have hpClosureOutside : p ∈ closure (closedBall 0 b)ᶜ := by
        rw [closure_compl, interior_closedBall (0 : EuclideanPlane) hb.ne']
        simp [hpDist]
      have hpBallOne : p ∈ ball 0 1 := by
        rw [mem_ball, hpDist]
        exact hb1
      have hpClosureT : p ∈ closure T :=
        isOpen_ball.closure_inter ⟨hpClosureOutside, hpBallOne⟩
      refine ⟨closure_mono (show T ⊆ euclideanDomain a b from
        subset_union_right) hpClosureT, ?_⟩
      rw [euclideanDomain]
      simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_ball,
        mem_closedBall, hpDist]
      exact fun h => h.elim (not_lt_of_ge hab.le) (fun h' => h'.1 le_rfl)
    · rw [hopen.frontier_eq]
      let T : Set EuclideanPlane := (closedBall 0 b)ᶜ ∩ ball 0 1
      have hpDist : dist p 0 = 1 := by
        simpa only [mem_sphere] using hpOne
      have hpClosureBall : p ∈ closure (ball 0 1) := by
        rw [← frontier_ball (0 : EuclideanPlane) one_ne_zero] at hpOne
        exact frontier_subset_closure hpOne
      have hpOutside : p ∈ (closedBall 0 b)ᶜ := by
        simp only [mem_compl_iff, mem_closedBall, hpDist, not_le]
        exact hb1
      have hpClosureT' : p ∈ closure (ball 0 1 ∩ (closedBall 0 b)ᶜ) :=
        isClosed_closedBall.isOpen_compl.closure_inter ⟨hpClosureBall, hpOutside⟩
      have hpClosureT : p ∈ closure T := by
        simpa only [T, inter_comm] using hpClosureT'
      refine ⟨closure_mono (show T ⊆ euclideanDomain a b from
        subset_union_right) hpClosureT, ?_⟩
      rw [euclideanDomain]
      simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_ball,
        mem_closedBall, hpDist, lt_self_iff_false, and_false, or_false]
      exact not_lt_of_ge (hab.trans hb1).le

/-- The complete frontier consists of all three circles, not only the outer
unit circle. -/
theorem frontier_domain {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    frontier (domain epsilon) =
      radialCircle (innerRadius epsilon) ∪
        radialCircle (outerRadius epsilon) ∪ radialCircle 1 := by
  rw [domain_eq_preimage_euclideanDomain hepsilon hepsilon_le,
    ← planeEuclideanHomeomorph.preimage_frontier,
    frontier_euclideanDomain (innerRadius_pos hepsilon hepsilon_le)
      (innerRadius_lt_outerRadius hepsilon) (outerRadius_lt_one hepsilon_le),
    preimage_union, preimage_union,
    ← radialCircle_eq_preimage_sphere
      (innerRadius_pos hepsilon hepsilon_le).le,
    ← radialCircle_eq_preimage_sphere
      ((innerRadius_pos hepsilon hepsilon_le).trans
        (innerRadius_lt_outerRadius hepsilon)).le,
    ← radialCircle_eq_preimage_sphere (by norm_num : (0 : ℝ) ≤ 1)]

private theorem radialSublevelCertificate
    {U V : Set PlanePoint} {p : PlanePoint} {r : ℝ}
    (hr : 0 < r) (hp : radiusSq p = r ^ 2)
    (hV : IsOpen V) (hpV : p ∈ V)
    (hlocal : U ∩ V = V ∩ {q | radiusSq q - r ^ 2 < 0}) :
    ∃ (W : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧ U ∩ W = W ∩ {q | g q < 0} := by
  let g : PlanePoint → ℝ := fun q => radiusSq q - r ^ 2
  let D : PlanePoint →L[ℝ] ℝ :=
    (2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hderiv : HasFDerivAt g D p := by
    simpa [g, D, radiusSq, Pi.add_apply] using
      ((((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).add
        ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2)).sub_const (r ^ 2))
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg (fun L : PlanePoint →L[ℝ] ℝ => L p) hzero
    simp [D] at happ
    unfold radiusSq at hp
    nlinarith [sq_pos_of_pos hr]
  refine ⟨V, g, D, hV, hpV, ?_, ?_, hderiv, hD, ?_⟩
  · unfold g radiusSq
    fun_prop
  · dsimp only [g]
    linarith
  · simpa only [g] using hlocal

private theorem radialSuperlevelCertificate
    {U V : Set PlanePoint} {p : PlanePoint} {r : ℝ}
    (hr : 0 < r) (hp : radiusSq p = r ^ 2)
    (hV : IsOpen V) (hpV : p ∈ V)
    (hlocal : U ∩ V = V ∩ {q | r ^ 2 - radiusSq q < 0}) :
    ∃ (W : Set PlanePoint) (g : PlanePoint → ℝ)
        (D : PlanePoint →L[ℝ] ℝ),
      IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ g W ∧ g p = 0 ∧
      HasFDerivAt g D p ∧ D ≠ 0 ∧ U ∩ W = W ∩ {q | g q < 0} := by
  let g : PlanePoint → ℝ := fun q => r ^ 2 - radiusSq q
  let D : PlanePoint →L[ℝ] ℝ :=
    -((2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hbase : HasFDerivAt (fun q : PlanePoint => radiusSq q - r ^ 2)
      ((2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
    simpa [radiusSq, Pi.add_apply] using
      ((((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).add
        ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2)).sub_const (r ^ 2))
  have hderiv : HasFDerivAt g D p := by
    change HasFDerivAt (fun q : PlanePoint => r ^ 2 - radiusSq q)
      (-((2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)) p
    rw [show (fun q : PlanePoint => r ^ 2 - radiusSq q) =
        -(fun q : PlanePoint => radiusSq q - r ^ 2) by
      funext q
      simp only [Pi.neg_apply]
      ring]
    exact hbase.neg
  have hD : D ≠ 0 := by
    intro hzero
    have happ := congrArg (fun L : PlanePoint →L[ℝ] ℝ => L p) hzero
    simp [D] at happ
    unfold radiusSq at hp
    nlinarith [sq_pos_of_pos hr]
  refine ⟨V, g, D, hV, hpV, ?_, ?_, hderiv, hD, ?_⟩
  · unfold g radiusSq
    fun_prop
  · dsimp only [g]
    linarith
  · simpa only [g] using hlocal

/-- Each annular-gap approximant is an actual smooth domain.  Connectedness is
not part of `IsSmoothDomain`; all three circular components are checked through
the literal local defining-function contract. -/
theorem isSmoothDomain_domain {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) : IsSmoothDomain (domain epsilon) := by
  let a := innerRadius epsilon
  let b := outerRadius epsilon
  have ha : 0 < a := innerRadius_pos hepsilon hepsilon_le
  have hab : a < b := innerRadius_lt_outerRadius hepsilon
  have hb1 : b < 1 := outerRadius_lt_one hepsilon_le
  have hsqab : a ^ 2 < b ^ 2 := (sq_lt_sq₀ ha.le (ha.trans hab).le).2 hab
  have hsqb1 : b ^ 2 < 1 := by
    have := (sq_lt_sq₀ (ha.trans hab).le
      (by norm_num : (0 : ℝ) ≤ 1)).2 hb1
    norm_num at this ⊢
    exact this
  have hradiusContinuous : Continuous radiusSq := by
    unfold radiusSq
    fun_prop
  constructor
  · unfold domain
    exact (isOpen_lt hradiusContinuous continuous_const).union
      ((isOpen_lt continuous_const hradiusContinuous).inter
        (isOpen_lt hradiusContinuous continuous_const))
  · intro p hp
    rw [frontier_domain hepsilon hepsilon_le] at hp
    rcases hp with (hpA | hpB) | hpOne
    · let V : Set PlanePoint := {q | radiusSq q < b ^ 2}
      change radiusSq p = innerRadius epsilon ^ 2 at hpA
      have hpAeq : radiusSq p = a ^ 2 := by
        simpa only [a] using hpA
      refine radialSublevelCertificate (U := domain epsilon) (V := V)
        (r := a) ha hpAeq ?_ ?_ ?_
      · exact isOpen_lt hradiusContinuous continuous_const
      · change radiusSq p < b ^ 2
        rw [hpAeq]
        exact hsqab
      · ext q
        simp only [domain, V, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨hq | hq, hqV⟩
          · exact ⟨hqV, by linarith⟩
          · exfalso
            linarith [hq.1]
        · rintro ⟨hqV, hq⟩
          exact ⟨Or.inl (by linarith), hqV⟩
    · let V : Set PlanePoint := {q | a ^ 2 < radiusSq q ∧ radiusSq q < 1}
      change radiusSq p = outerRadius epsilon ^ 2 at hpB
      have hpBeq : radiusSq p = b ^ 2 := by
        simpa only [b] using hpB
      refine radialSuperlevelCertificate (U := domain epsilon) (V := V)
        (r := b) (ha.trans hab) hpBeq ?_ ?_ ?_
      · exact (isOpen_lt continuous_const hradiusContinuous).inter
          (isOpen_lt hradiusContinuous continuous_const)
      · exact ⟨by rw [hpBeq]; exact hsqab, by rw [hpBeq]; exact hsqb1⟩
      · ext q
        simp only [domain, V, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨hq | hq, hqV⟩
          · exfalso
            linarith [hqV.1]
          · exact ⟨hqV, by linarith [hq.1]⟩
        · rintro ⟨hqV, hq⟩
          exact ⟨Or.inr ⟨by linarith, hqV.2⟩, hqV⟩
    · let V : Set PlanePoint := {q | b ^ 2 < radiusSq q}
      change radiusSq p = (1 : ℝ) ^ 2 at hpOne
      have hpOneEq : radiusSq p = (1 : ℝ) ^ 2 := hpOne
      refine radialSublevelCertificate (U := domain epsilon) (V := V)
        (r := 1) (by norm_num) hpOneEq ?_ ?_ ?_
      · exact isOpen_lt continuous_const hradiusContinuous
      · change b ^ 2 < radiusSq p
        rw [hpOneEq]
        simpa only [one_pow] using hsqb1
      · ext q
        simp only [domain, V, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨hq | hq, hqV⟩
          · exfalso
            linarith [hsqab, hqV]
          · exact ⟨hqV, by linarith [hq.2]⟩
        · rintro ⟨hqV, hq⟩
          exact ⟨Or.inr ⟨hqV, by linarith⟩, hqV⟩


/-! ## Exact circle accounting -/

private lemma complexSphere_eq_unitCircleArc_image {r : ℝ} (hr : 0 < r) :
    sphere (0 : ℂ) r =
      unitCircleArc r '' Icc (-r * Real.pi) (r * Real.pi) := by
  ext z
  constructor
  · intro hz
    have hnorm : ‖z‖ = r := by
      simpa only [mem_sphere, dist_zero_right] using hz
    let s : ℝ := r * z.arg
    have hs : s ∈ Icc (-r * Real.pi) (r * Real.pi) := by
      dsimp only [s]
      constructor
      · nlinarith [Complex.neg_pi_lt_arg z]
      · exact mul_le_mul_of_nonneg_left (Complex.arg_le_pi z) hr.le
    refine ⟨s, hs, ?_⟩
    simpa [s, unitCircleArc, hr.ne', hnorm, mul_comm] using
      Complex.norm_mul_exp_arg_mul_I z
  · intro hz
    rcases hz with ⟨s, hs, rfl⟩
    rw [mem_sphere, dist_zero_right, unitCircleArc, norm_mul,
      Complex.norm_exp]
    simp [abs_of_pos hr]

private def thetaApprox (n : ℕ) : ℝ :=
  Real.pi * (1 - 1 / ((n : ℝ) + 2))

private lemma thetaApprox_pos (n : ℕ) : 0 < thetaApprox n := by
  have hnNat : 1 < n + 2 := by omega
  have hn : (1 : ℝ) < (n : ℝ) + 2 := by exact_mod_cast hnNat
  have hinv : 1 / ((n : ℝ) + 2) < 1 := by
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hn
  unfold thetaApprox
  exact mul_pos Real.pi_pos (sub_pos.mpr hinv)

private lemma thetaApprox_lt_pi (n : ℕ) : thetaApprox n < Real.pi := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hinv : 0 < 1 / ((n : ℝ) + 2) := one_div_pos.mpr hden
  unfold thetaApprox
  nlinarith [Real.pi_pos]

private lemma tendsto_thetaApprox :
    Tendsto thetaApprox atTop (𝓝 Real.pi) := by
  have hinvBase :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    convert hinvBase.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    congr 1
    push_cast
    ring
  have hsub :
      Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hinv
  change Tendsto
    (fun n : ℕ => Real.pi * (1 - 1 / ((n : ℝ) + 2)))
      atTop (𝓝 Real.pi)
  simpa only [mul_one] using tendsto_const_nhds.mul hsub

/-- Exact Euclidean `H¹` mass of a complete positive-radius circle in `ℂ`.
The lower bound exhausts it by injective arcs with angle increasing to `π`;
the upper bound uses one complete Lipschitz parametrization. -/
private theorem hausdorffMeasure_complexSphere_eq {r : ℝ} (hr : 0 < r) :
    (μH[1] : Measure ℂ) (sphere 0 r) =
      ENNReal.ofReal (2 * Real.pi * r) := by
  apply le_antisymm
  · rw [complexSphere_eq_unitCircleArc_image hr]
    calc
      (μH[1] : Measure ℂ)
          (unitCircleArc r '' Icc (-r * Real.pi) (r * Real.pi)) ≤
          ENNReal.ofReal (r * Real.pi - (-r * Real.pi)) :=
        hausdorffMeasure_unitCircleArc_image_le hr
      _ = ENNReal.ofReal (2 * Real.pi * r) := by
        congr 1
        ring
  · have hlower : ∀ n : ℕ,
        ENNReal.ofReal (2 * r * thetaApprox n) ≤
          (μH[1] : Measure ℂ) (sphere 0 r) := by
      intro n
      rw [← hausdorffMeasure_unitCircleArc_image_eq hr
        ⟨thetaApprox_pos n, thetaApprox_lt_pi n⟩]
      rw [complexSphere_eq_unitCircleArc_image hr]
      apply measure_mono
      apply image_mono
      intro s hs
      constructor
      · nlinarith [hs.1, thetaApprox_lt_pi n]
      · nlinarith [hs.2, thetaApprox_lt_pi n]
    have hreal :
        Tendsto (fun n : ℕ => 2 * r * thetaApprox n) atTop
          (𝓝 (2 * Real.pi * r)) := by
      convert tendsto_const_nhds.mul tendsto_thetaApprox using 1 <;>
        ring
    exact le_of_tendsto' (ENNReal.tendsto_ofReal hreal) hlower

/-- Exact Euclidean `H¹` mass of a complete positive-radius circle in the
repository's `L²` realization. -/
private theorem hausdorffMeasure_euclideanSphere_eq {r : ℝ} (hr : 0 < r) :
    (μH[1] : Measure EuclideanPlane) (sphere 0 r) =
      ENNReal.ofReal (2 * Real.pi * r) := by
  let e : EuclideanPlane ≃ᵢ ℂ := tangentComplexEquiv
  calc
    (μH[1] : Measure EuclideanPlane) (sphere 0 r) =
        (μH[1] : Measure ℂ) (e '' sphere 0 r) :=
      (e.hausdorffMeasure_image 1 (sphere 0 r)).symm
    _ = (μH[1] : Measure ℂ) (sphere 0 r) := by
      rw [e.image_sphere]
      congr
    _ = ENNReal.ofReal (2 * Real.pi * r) :=
      hausdorffMeasure_complexSphere_eq hr

lemma isCompact_radialCircle (r : ℝ) : IsCompact (radialCircle r) := by
  by_cases hr : 0 ≤ r
  · rw [radialCircle_eq_preimage_sphere hr]
    exact planeEuclideanHomeomorph.isCompact_preimage.mpr
      (isCompact_sphere 0 r)
  · have hneg : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
    have heq : radialCircle r = radialCircle (-r) := by
      ext p
      simp only [radialCircle, mem_ofPred_eq]
      ring_nf
    rw [heq, radialCircle_eq_preimage_sphere hneg]
    exact planeEuclideanHomeomorph.isCompact_preimage.mpr
      (isCompact_sphere 0 (-r))

lemma euclidean_image_radialCircle {r : ℝ} (hr : 0 ≤ r) :
    planeEuclideanHomeomorph '' radialCircle r = sphere 0 r := by
  rw [radialCircle_eq_preimage_sphere hr]
  exact planeEuclideanHomeomorph.surjective.image_preimage _

theorem hausdorffMeasure_radialCircle_eq {r : ℝ} (hr : 0 < r) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' radialCircle r) =
      ENNReal.ofReal (2 * Real.pi * r) := by
  rw [euclidean_image_radialCircle hr.le]
  exact hausdorffMeasure_euclideanSphere_eq hr

lemma radialCircle_stripDensity_eq_one {r : ℝ} (hr : 0 ≤ r)
    (hr1 : r ≤ 1) {p : PlanePoint} (hp : p ∈ radialCircle r) :
    StripDensity 2 p = 1 := by
  change radiusSq p = r ^ 2 at hp
  have hp2sq : p.2 ^ 2 ≤ 1 ^ 2 := by
    unfold radiusSq at hp
    nlinarith [sq_nonneg p.1, sq_nonneg r]
  have habs : |p.2| ≤ 1 := by
    apply (sq_le_sq₀ (abs_nonneg p.2) (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [sq_abs] using hp2sq
  simp [StripDensity, habs]

/-- Every positive circle contained in the closed unit disk has its exact
literal density-one trace cost. -/
theorem weightedTraceCost_radialCircle {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    weightedTraceCost 2 (radialCircle r) =
      ENNReal.ofReal (2 * Real.pi * r) := by
  rw [weightedTraceCost_eq_const_mul_hausdorff 2 1
    (isCompact_radialCircle r)
    (fun _ hp => radialCircle_stripDensity_eq_one hr.le hr1 hp),
    hausdorffMeasure_radialCircle_eq hr]
  simp

lemma disjoint_radialCircle {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≠ s) : Disjoint (radialCircle r) (radialCircle s) := by
  rw [Set.disjoint_left]
  intro p hpr hps
  change radiusSq p = r ^ 2 at hpr
  change radiusSq p = s ^ 2 at hps
  apply hrs
  exact (sq_eq_sq₀ hr hs).mp (hpr.symm.trans hps)

/-- The three circles in `frontier_domain` are pairwise disjoint. -/
theorem domain_frontier_circles_pairwise_disjoint {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 64) :
    Disjoint (radialCircle (innerRadius epsilon))
        (radialCircle (outerRadius epsilon)) ∧
      Disjoint (radialCircle (innerRadius epsilon)) (radialCircle 1) ∧
      Disjoint (radialCircle (outerRadius epsilon)) (radialCircle 1) := by
  have ha := innerRadius_pos hepsilon hepsilon_le
  have hab := innerRadius_lt_outerRadius hepsilon
  have hb1 := outerRadius_lt_one hepsilon_le
  exact ⟨disjoint_radialCircle ha.le (ha.trans hab).le hab.ne,
    disjoint_radialCircle ha.le (by norm_num) (hab.trans hb1).ne,
    disjoint_radialCircle (ha.trans hab).le (by norm_num) hb1.ne⟩

/-- Exact literal weighted complete-frontier cost.  The inner and outer hidden
circles contribute `π`, independently of the gap width. -/
theorem smoothCost_domain {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    smoothCost 2 (domain epsilon) = ENNReal.ofReal (3 * Real.pi) := by
  let a := innerRadius epsilon
  let b := outerRadius epsilon
  have ha : 0 < a := innerRadius_pos hepsilon hepsilon_le
  have hab : a < b := innerRadius_lt_outerRadius hepsilon
  have hb1 : b < 1 := outerRadius_lt_one hepsilon_le
  have hAB : Disjoint (radialCircle a) (radialCircle b) :=
    disjoint_radialCircle ha.le (ha.trans hab).le hab.ne
  have hABC : Disjoint (radialCircle a ∪ radialCircle b) (radialCircle 1) := by
    rw [Set.disjoint_left]
    intro p hpAB hpOne
    rcases hpAB with hpA | hpB
    · exact Set.disjoint_left.mp
        (disjoint_radialCircle ha.le (by norm_num) (hab.trans hb1).ne)
          hpA hpOne
    · exact Set.disjoint_left.mp
        (disjoint_radialCircle (ha.trans hab).le (by norm_num) hb1.ne)
          hpB hpOne
  rw [smoothCost_eq_weightedTraceCost_frontier,
    frontier_domain hepsilon hepsilon_le,
    FiniteBandRearrangement.weightedTraceCost_union_eq 2
      (isCompact_radialCircle 1).measurableSet hABC,
    FiniteBandRearrangement.weightedTraceCost_union_eq 2
      (isCompact_radialCircle b).measurableSet hAB,
    weightedTraceCost_radialCircle ha (hab.trans hb1).le,
    weightedTraceCost_radialCircle (ha.trans hab) hb1.le,
    weightedTraceCost_radialCircle (by norm_num : (0 : ℝ) < 1) le_rfl]
  have hTwoPi : 0 ≤ 2 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  have hA : 0 ≤ 2 * Real.pi * a := mul_nonneg hTwoPi ha.le
  have hB : 0 ≤ 2 * Real.pi * b := mul_nonneg hTwoPi (ha.trans hab).le
  have hOne : 0 ≤ 2 * Real.pi * (1 : ℝ) :=
    mul_nonneg hTwoPi (by norm_num)
  rw [← ENNReal.ofReal_add hA hB,
    ← ENNReal.ofReal_add (add_nonneg hA hB) hOne]
  simp only [a, b, innerRadius, outerRadius]
  ring

/-! ## Exact characteristic-function error -/

def radialOpenDisk (r : ℝ) : Set PlanePoint :=
  {p | radiusSq p < r ^ 2}

def radialClosedDisk (r : ℝ) : Set PlanePoint :=
  {p | radiusSq p ≤ r ^ 2}

private lemma radialOpenDisk_eq_preimage_ball {r : ℝ} (hr : 0 ≤ r) :
    radialOpenDisk r = planeEuclideanHomeomorph ⁻¹' ball 0 r := by
  ext p
  simp only [radialOpenDisk, mem_ofPred_eq, mem_preimage, mem_ball,
    dist_zero_right]
  exact radiusSq_lt_sq_iff_norm_lt hr

private lemma radialClosedDisk_eq_preimage_closedBall {r : ℝ} (hr : 0 ≤ r) :
    radialClosedDisk r = planeEuclideanHomeomorph ⁻¹' closedBall 0 r := by
  ext p
  simp only [radialClosedDisk, mem_ofPred_eq, mem_preimage, mem_closedBall,
    dist_zero_right]
  rw [radiusSq_eq_norm_sq]
  exact sq_le_sq₀ (norm_nonneg _) hr

private lemma finrank_euclideanPlane :
    Module.finrank ℝ EuclideanPlane = 2 := by
  rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq]
  simp

private theorem volume_radialOpenDisk {r : ℝ} (hr : 0 ≤ r) :
    volume (radialOpenDisk r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [radialOpenDisk_eq_preimage_ball hr]
  change volume (WithLp.toLp 2 ⁻¹' ball (0 : EuclideanPlane) r) =
    ENNReal.ofReal (Real.pi * r ^ 2)
  rw [(WithLp.volume_preserving_toLp ℝ ℝ).measure_preimage
      measurableSet_ball.nullMeasurableSet,
    InnerProductSpace.volume_ball_of_dim_even (k := 1)
      finrank_euclideanPlane (0 : EuclideanPlane) r]
  rw [finrank_euclideanPlane]
  norm_num
  rw [← ENNReal.ofReal_pow hr 2,
    ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private theorem volume_radialClosedDisk {r : ℝ} (hr : 0 ≤ r) :
    volume (radialClosedDisk r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [radialClosedDisk_eq_preimage_closedBall hr]
  change volume (WithLp.toLp 2 ⁻¹' closedBall (0 : EuclideanPlane) r) =
    ENNReal.ofReal (Real.pi * r ^ 2)
  rw [(WithLp.volume_preserving_toLp ℝ ℝ).measure_preimage
      measurableSet_closedBall.nullMeasurableSet,
    InnerProductSpace.volume_closedBall_of_dim_even (k := 1)
      finrank_euclideanPlane (0 : EuclideanPlane) r]
  rw [finrank_euclideanPlane]
  norm_num
  rw [← ENNReal.ofReal_pow hr 2,
    ← ENNReal.ofReal_mul (sq_nonneg r)]
  congr 1
  ring

private lemma domain_subset_unitDisk {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    domain epsilon ⊆ unitDisk := by
  intro p hp
  rcases hp with hp | hp
  · have ha := innerRadius_pos hepsilon hepsilon_le
    have hab := innerRadius_lt_outerRadius hepsilon
    have hb1 := outerRadius_lt_one hepsilon_le
    change radiusSq p < 1
    change radiusSq p < innerRadius epsilon ^ 2 at hp
    nlinarith
  · exact hp.2

private lemma unitDisk_sdiff_domain {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    unitDisk \ domain epsilon =
      radialClosedDisk (outerRadius epsilon) \
        radialOpenDisk (innerRadius epsilon) := by
  ext p
  simp only [Set.mem_sdiff, unitDisk, domain, radialClosedDisk, radialOpenDisk,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp1, hpNot⟩
    have ha : innerRadius epsilon ^ 2 ≤ radiusSq p := by
      apply le_of_not_gt
      intro h
      exact hpNot (Or.inl h)
    have hb : radiusSq p ≤ outerRadius epsilon ^ 2 := by
      apply le_of_not_gt
      intro h
      exact hpNot (Or.inr ⟨h, hp1⟩)
    exact ⟨hb, not_lt.mpr ha⟩
  · rintro ⟨hb, ha⟩
    have hb1 := outerRadius_lt_one hepsilon_le
    have hbpos := (innerRadius_pos hepsilon hepsilon_le).trans
      (innerRadius_lt_outerRadius hepsilon)
    have hp1 : radiusSq p < 1 := by nlinarith
    refine ⟨hp1, ?_⟩
    intro hp
    rcases hp with hp | hp
    · exact ha hp
    · exact (not_lt_of_ge hb) hp.1

/-- The deleted closed annulus has exactly area `π ε`; this is the literal
`characteristicDistance`, not an asymptotic estimate. -/
theorem characteristicDistance_domain {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    characteristicDistance (domain epsilon) unitDisk =
      ENNReal.ofReal (Real.pi * epsilon) := by
  have hinner : 0 ≤ innerRadius epsilon :=
    (innerRadius_pos hepsilon hepsilon_le).le
  have houter : 0 ≤ outerRadius epsilon :=
    hinner.trans (innerRadius_lt_outerRadius hepsilon).le
  have hdisks :
      radialOpenDisk (innerRadius epsilon) ⊆
        radialClosedDisk (outerRadius epsilon) := by
    intro p hp
    change radiusSq p ≤ outerRadius epsilon ^ 2
    change radiusSq p < innerRadius epsilon ^ 2 at hp
    nlinarith [innerRadius_lt_outerRadius hepsilon]
  unfold characteristicDistance
  rw [symmDiff_of_le (domain_subset_unitDisk hepsilon hepsilon_le),
    unitDisk_sdiff_domain hepsilon hepsilon_le,
    measure_sdiff hdisks]
  · rw [volume_radialClosedDisk houter, volume_radialOpenDisk hinner,
      ← ENNReal.ofReal_sub]
    · congr 1
      simp only [innerRadius, outerRadius]
      ring
    · exact mul_nonneg Real.pi_pos.le (sq_nonneg _)
  · rw [radialOpenDisk_eq_preimage_ball hinner]
    exact (planeEuclideanHomeomorph.continuous.measurable
      measurableSet_ball).nullMeasurableSet
  · rw [volume_radialOpenDisk hinner]
    exact ENNReal.ofReal_ne_top


/-! ## A smooth recovery sequence with persistent hidden frontier -/

/-- Literal shrinking half-width `1 / (64 (n+1))`. -/
def epsilon (n : ℕ) : ℝ :=
  1 / (64 * ((n : ℝ) + 1))

lemma epsilon_pos (n : ℕ) : 0 < epsilon n := by
  unfold epsilon
  positivity

lemma epsilon_le (n : ℕ) : epsilon n ≤ 1 / 64 := by
  have hnNat : 1 ≤ n + 1 := by omega
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hnNat
  have hden : (64 : ℝ) ≤ 64 * ((n : ℝ) + 1) := by nlinarith
  exact one_div_le_one_div_of_le (by norm_num) hden

private lemma tendsto_epsilon :
    Tendsto epsilon atTop (𝓝 0) := by
  have hbase :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 / 64 : ℝ)) atTop (𝓝 (1 / 64))).mul hbase
  change Tendsto (fun n : ℕ => 1 / (64 * ((n : ℝ) + 1))) atTop (𝓝 0)
  simpa [one_div, mul_inv_rev, mul_comm] using hscaled

/-- The actual smooth annular-gap recovery sequence. -/
def sequence : SmoothSequence where
  carrier n := domain (epsilon n)
  smooth n := isSmoothDomain_domain (epsilon_pos n) (epsilon_le n)

@[simp] theorem sequence_carrier (n : ℕ) :
    sequence.carrier n = domain (epsilon n) := rfl

/-- Every member has the same complete-frontier weighted cost, including both
hidden annular interfaces. -/
theorem sequence_termCost (n : ℕ) :
    smoothCost 2 (sequence.carrier n) =
      ENNReal.ofReal (3 * Real.pi) := by
  exact smoothCost_domain (epsilon_pos n) (epsilon_le n)

/-- The exact annulus area tends to zero, hence this sequence recovers the unit
disk in the relaxation's literal characteristic distance. -/
theorem sequence_converges :
    sequence.ConvergesTo unitDisk := by
  unfold SmoothSequence.ConvergesTo
  have hreal :
      Tendsto (fun n => Real.pi * epsilon n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_epsilon
  have hENN := ENNReal.tendsto_ofReal hreal
  simpa only [sequence_carrier,
    characteristicDistance_domain (epsilon_pos _) (epsilon_le _),
    ENNReal.ofReal_zero] using hENN

/-- Persistent hidden frontier makes the recovery cost exactly `3π`. -/
theorem sequence_cost :
    sequence.cost 2 = ENNReal.ofReal (3 * Real.pi) := by
  unfold SmoothSequence.cost
  have hfun :
      (fun n => smoothCost 2 (sequence.carrier n)) =
        fun _ : ℕ => ENNReal.ofReal (3 * Real.pi) := by
    funext n
    exact sequence_termCost n
  rw [hfun]
  simp

theorem frontier_unitDisk :
    frontier unitDisk = radialCircle 1 := by
  have hunit : unitDisk = radialOpenDisk 1 := by
    ext p
    simp only [unitDisk, radialOpenDisk, radiusSq, mem_ofPred_eq, one_pow]
  rw [hunit, radialOpenDisk_eq_preimage_ball (by norm_num),
    ← planeEuclideanHomeomorph.preimage_frontier,
    frontier_ball (0 : EuclideanPlane) one_ne_zero,
    ← radialCircle_eq_preimage_sphere (by norm_num : (0 : ℝ) ≤ 1)]

/-- Exact literal outer-circle weighted cost. -/
theorem smoothCost_unitDisk_eq :
    smoothCost 2 unitDisk = ENNReal.ofReal (2 * Real.pi) := by
  rw [smoothCost_eq_weightedTraceCost_frontier, frontier_unitDisk,
    weightedTraceCost_radialCircle (by norm_num : (0 : ℝ) < 1) le_rfl]
  congr 1
  ring

private theorem two_pi_lt_three_pi :
    ENNReal.ofReal (2 * Real.pi) < ENNReal.ofReal (3 * Real.pi) := by
  rw [ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by norm_num : (0 : ℝ) < 3) Real.pi_pos)]
  nlinarith [Real.pi_pos]

/-- The relaxation is bounded above by the smooth disk itself.  No equality
between relaxed and smooth disk perimeter is assumed. -/
theorem relaxedPerimeter_le_smoothCost_unitDisk :
    relaxedPerimeter 2 unitDisk ≤ smoothCost 2 unitDisk := by
  unfold relaxedPerimeter
  apply sInf_le
  exact ⟨unitDiskConstantSequence,
    isOpen_unitDisk.measurableSet.nullMeasurableSet,
    unitDiskConstantSequence_converges, unitDiskConstantSequence_cost 2⟩

/-- The requested strict comparison:
`relaxedPerimeter 2 unitDisk ≤ smoothCost 2 unitDisk < sequence.cost 2`. -/
theorem unitDisk_relaxed_le_smoothCost_lt_sequenceCost :
    relaxedPerimeter 2 unitDisk ≤ smoothCost 2 unitDisk ∧
      smoothCost 2 unitDisk < sequence.cost 2 := by
  constructor
  · exact relaxedPerimeter_le_smoothCost_unitDisk
  · rw [smoothCost_unitDisk_eq, sequence_cost]
    exact two_pi_lt_three_pi

/-- The explicit annular-gap recovery is not an exact minimizing recovery. -/
theorem sequence_cost_ne_relaxedPerimeter :
    sequence.cost 2 ≠ relaxedPerimeter 2 unitDisk := by
  apply ne_of_gt
  exact lt_of_le_of_lt unitDisk_relaxed_le_smoothCost_lt_sequenceCost.1
    unitDisk_relaxed_le_smoothCost_lt_sequenceCost.2

/-- The overstrong implication under investigation: *every* globally
convergent smooth sequence would have to attain the relaxed infimum.  This is
not the exact-minimizing-selector theorem and is not a relaxed-level transport
estimate. -/
def GlobalConvergenceForcesExactRecovery (lam : ℝ)
    (E : Set PlanePoint) : Prop :=
  ∀ A : SmoothSequence, A.ConvergesTo E →
    A.cost lam = relaxedPerimeter lam E

/-- Cañete, Section 2 (printed pp. 2–3), defines the relaxed value by an
infimum.  The annular-gap sequence refutes only the replacement of that
infimum by the cost of an arbitrary global `L¹` recovery.  It does not refute
existence of an exact minimizing selector, nor any desired inequality stated
directly at the relaxed level. -/
theorem not_globalConvergenceForcesExactRecovery_unitDisk :
    ¬ GlobalConvergenceForcesExactRecovery 2 unitDisk := by
  intro hglobal
  have heq := hglobal sequence sequence_converges
  have hstrict : relaxedPerimeter 2 unitDisk < sequence.cost 2 :=
    lt_of_le_of_lt unitDisk_relaxed_le_smoothCost_lt_sequenceCost.1
      unitDisk_relaxed_le_smoothCost_lt_sequenceCost.2
  rw [heq] at hstrict
  exact lt_irrefl _ hstrict

/-- The exact-minimizing selector remains available for the same unit-disk
target; unlike `sequence`, its termwise costs converge to the infimum. -/
theorem unitDisk_has_exactMinimizing_sequence :
    ∃ A : SmoothSequence,
      NullMeasurableSet unitDisk volume ∧
      A.ConvergesTo unitDisk ∧
      Tendsto (fun n => smoothCost 2 (A.carrier n))
        atTop (𝓝 (relaxedPerimeter 2 unitDisk)) ∧
      A.cost 2 = relaxedPerimeter 2 unitDisk ∧
      ∀ n, smoothCost 2 (A.carrier n) < ⊤ :=
  exists_exactMinimizing_smoothSequence
    (relaxedPerimeter_unitDisk_lt_top 2)



/-! ## A fixed-target compactly supported radial deformation -/

/-- Closed core on which the ambient field is literal radial dilation.  It
contains both hidden circles for every term of `sequence`. -/
def dilationCore : Set PlanePoint := radialClosedDisk (1 / 2)

/-- Open support region for the ambient field.  Its closure stays strictly
inside the density-one unit disk. -/
def dilationSupportRegion : Set PlanePoint := radialOpenDisk (3 / 4)

lemma isCompact_dilationCore : IsCompact dilationCore := by
  rw [dilationCore, radialClosedDisk_eq_preimage_closedBall (by norm_num)]
  exact planeEuclideanHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (0 : EuclideanPlane) (1 / 2))

lemma isOpen_dilationSupportRegion : IsOpen dilationSupportRegion := by
  rw [dilationSupportRegion, radialOpenDisk_eq_preimage_ball (by norm_num)]
  exact isOpen_ball.preimage planeEuclideanHomeomorph.continuous

lemma dilationCore_subset_supportRegion :
    dilationCore ⊆ dilationSupportRegion := by
  intro p hp
  change radiusSq p ≤ (1 / 2 : ℝ) ^ 2 at hp
  change radiusSq p < (3 / 4 : ℝ) ^ 2
  nlinarith

private theorem exists_dilationCutoff :
    ∃ beta : PlanePoint → ℝ,
      ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
        tsupport beta ⊆ dilationSupportRegion ∧
        EqOn beta 1 dilationCore :=
  exists_smoothCompactCutoff isCompact_dilationCore
    isOpen_dilationSupportRegion dilationCore_subset_supportRegion

/-- A chosen smooth cutoff equal to one on the complete half-radius core and
supported in the strict three-quarter-radius disk. -/
noncomputable def dilationCutoff : PlanePoint → ℝ :=
  exists_dilationCutoff.choose

lemma dilationCutoff_contDiff : ContDiff ℝ ∞ dilationCutoff :=
  exists_dilationCutoff.choose_spec.1

lemma dilationCutoff_hasCompactSupport : HasCompactSupport dilationCutoff :=
  exists_dilationCutoff.choose_spec.2.1

lemma dilationCutoff_tsupport_subset :
    tsupport dilationCutoff ⊆ dilationSupportRegion :=
  exists_dilationCutoff.choose_spec.2.2.1

lemma dilationCutoff_eq_one {p : PlanePoint} (hp : p ∈ dilationCore) :
    dilationCutoff p = 1 :=
  exists_dilationCutoff.choose_spec.2.2.2 hp

/-- The compactly supported field whose flow parameter is realized by the
small-perturbation ambient equivalence. -/
def dilationField (p : PlanePoint) : PlanePoint := dilationCutoff p • p

lemma dilationField_contDiff : ContDiff ℝ ∞ dilationField := by
  unfold dilationField
  exact dilationCutoff_contDiff.smul contDiff_id

lemma tsupport_dilationField_subset :
    tsupport dilationField ⊆ tsupport dilationCutoff := by
  apply closure_mono
  intro p hp hzero
  apply hp
  simp [dilationField, hzero]

lemma dilationField_hasCompactSupport : HasCompactSupport dilationField :=
  IsCompact.of_isClosed_subset dilationCutoff_hasCompactSupport
    (isClosed_tsupport dilationField) tsupport_dilationField_subset

lemma dilationField_tsupport_subset :
    tsupport dilationField ⊆ dilationSupportRegion :=
  tsupport_dilationField_subset.trans dilationCutoff_tsupport_subset

lemma dilationField_eq_self {p : PlanePoint} (hp : p ∈ dilationCore) :
    dilationField p = p := by
  rw [dilationField, dilationCutoff_eq_one hp, one_smul]

private theorem exists_dilationL :
    ∃ L : ℝ≥0, LipschitzWith L dilationField :=
  dilationField_contDiff.lipschitzWith_of_hasCompactSupport
    dilationField_hasCompactSupport (by simp)

/-- A fixed global Lipschitz bound for the radial field. -/
noncomputable def dilationL : ℝ≥0 := exists_dilationL.choose

lemma dilationField_lipschitz : LipschitzWith dilationL dilationField :=
  exists_dilationL.choose_spec

/-- A nonempty two-sided parameter radius satisfying both the geometric
positivity bound and the small-perturbation inverse bound. -/
noncomputable def deformationRadius : ℝ :=
  min (1 / 2) (1 / ((dilationL : ℝ) + 1))

lemma deformationRadius_pos : 0 < deformationRadius := by
  unfold deformationRadius
  exact lt_min (by norm_num) (one_div_pos.mpr (by positivity))

lemma deformationRadius_le_half : deformationRadius ≤ 1 / 2 := by
  unfold deformationRadius
  exact min_le_left _ _

lemma one_add_parameter_pos {t : ℝ} (ht : |t| < deformationRadius) :
    0 < 1 + t := by
  have htHalf : |t| < 1 / 2 :=
    ht.trans_le deformationRadius_le_half
  have htLower := neg_abs_le t
  linarith

lemma one_add_parameter_lt_three_halves {t : ℝ}
    (ht : |t| < deformationRadius) :
    1 + t < 3 / 2 := by
  have htHalf : |t| < 1 / 2 :=
    ht.trans_le deformationRadius_le_half
  have htUpper := le_abs_self t
  linarith

lemma deformation_small {t : ℝ} (ht : |t| < deformationRadius) :
    ‖t‖₊ * dilationL < 1 := by
  have htBound : |t| < 1 / ((dilationL : ℝ) + 1) :=
    ht.trans_le (by
      unfold deformationRadius
      exact min_le_right _ _)
  have hden : 0 < (dilationL : ℝ) + 1 := by positivity
  have hsmallReal : |t| * (dilationL : ℝ) < 1 := by
    calc
      |t| * (dilationL : ℝ) ≤ |t| * ((dilationL : ℝ) + 1) := by
        gcongr
        linarith
      _ < (1 / ((dilationL : ℝ) + 1)) *
          ((dilationL : ℝ) + 1) :=
        mul_lt_mul_of_pos_right htBound hden
      _ = 1 := by field_simp
  exact_mod_cast hsmallReal

/-- The genuine global `C∞` ambient equivalence
`p ↦ p + t • dilationField p`. -/
noncomputable def deformation (t : ℝ) (ht : |t| < deformationRadius) :
    SmoothAmbientEquiv :=
  SmoothAmbientEquiv.ofSmallPerturbation dilationField_lipschitz
    dilationField_contDiff dilationField_hasCompactSupport
    (deformation_small ht)

@[simp] theorem deformation_apply (t : ℝ)
    (ht : |t| < deformationRadius) (p : PlanePoint) :
    deformation t ht p = p + t • dilationField p := rfl

theorem deformation_zero_apply (p : PlanePoint) :
    deformation 0 (by simpa using deformationRadius_pos) p = p := by
  simp

/-- The moved set is compactly supported strictly inside the unit disk. -/
theorem deformation_movedSet_subset (t : ℝ)
    (ht : |t| < deformationRadius) :
    (deformation t ht).movedSet ⊆ dilationSupportRegion :=
  (SmoothAmbientEquiv.movedSet_ofSmallPerturbation_subset
    dilationField_lipschitz dilationField_contDiff
      dilationField_hasCompactSupport (deformation_small ht)).trans
    dilationField_tsupport_subset


lemma dilationField_eq_zero_of_not_mem_supportRegion {p : PlanePoint}
    (hp : p ∉ dilationSupportRegion) :
    dilationField p = 0 := by
  by_contra hne
  exact hp (dilationField_tsupport_subset (subset_tsupport dilationField hne))

theorem deformation_fixed_of_not_mem_supportRegion (t : ℝ)
    (ht : |t| < deformationRadius) {p : PlanePoint}
    (hp : p ∉ dilationSupportRegion) :
    deformation t ht p = p := by
  rw [deformation_apply, dilationField_eq_zero_of_not_mem_supportRegion hp]
  simp

lemma dilationSupportRegion_subset_unitDisk :
    dilationSupportRegion ⊆ unitDisk := by
  intro p hp
  change radiusSq p < (3 / 4 : ℝ) ^ 2 at hp
  change p.1 ^ 2 + p.2 ^ 2 < 1
  unfold radiusSq at hp
  nlinarith
theorem deformation_compactlySupported_in_unitDisk (t : ℝ)
    (ht : |t| < deformationRadius) :
    IsCompact (deformation t ht).movedSet ∧
      (deformation t ht).movedSet ⊆ unitDisk :=
  ⟨(deformation t ht).movedSet_isCompact,
    (deformation_movedSet_subset t ht).trans
      dilationSupportRegion_subset_unitDisk⟩

/-- The literal region on which `StripDensity 2` has value one. -/
def densityOneRegion : Set PlanePoint := {p | |p.2| ≤ 1}

@[simp] theorem mem_densityOneRegion_iff_stripDensity_two_eq_one
    (p : PlanePoint) :
    p ∈ densityOneRegion ↔ StripDensity 2 p = 1 := by
  simp [densityOneRegion, StripDensity]

lemma dilationSupportRegion_subset_densityOneRegion :
    dilationSupportRegion ⊆ densityOneRegion := by
  intro p hp
  have hpDisk := dilationSupportRegion_subset_unitDisk hp
  change p.1 ^ 2 + p.2 ^ 2 < 1 at hpDisk
  change |p.2| ≤ 1
  have hySq : p.2 ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg p.1]
  exact (sq_le_sq₀ (abs_nonneg p.2) (by norm_num)).mp
    (by simpa only [sq_abs] using hySq)

private theorem image_eq_self_of_fixed_compl
    (Φ : SmoothAmbientEquiv) (E : Set PlanePoint)
    (hfix : ∀ p, p ∉ E → Φ p = p) :
    Φ '' E = E := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    by_contra hnot
    have hfixed := hfix (Φ p) hnot
    have heq : Φ p = p := Φ.toHomeomorph.injective hfixed
    exact hnot (heq.symm ▸ hp)
  · intro q hq
    let p := Φ.toHomeomorph.symm q
    have hmap : Φ p = q := Φ.toHomeomorph.apply_symm_apply q
    have hp : p ∈ E := by
      by_contra hpNot
      have hfixed := hfix p hpNot
      have hpq : p = q := hfixed.symm.trans hmap
      exact hpNot (hpq ▸ hq)
    exact ⟨p, hp, hmap⟩

/-- The compactly supported deformation leaves the target disk exactly fixed,
not merely almost everywhere fixed. -/
theorem deformation_image_unitDisk (t : ℝ)
    (ht : |t| < deformationRadius) :
    deformation t ht '' unitDisk = unitDisk := by
  apply image_eq_self_of_fixed_compl
  intro p hp
  apply deformation_fixed_of_not_mem_supportRegion
  exact fun hsupport => hp (dilationSupportRegion_subset_unitDisk hsupport)

/-- The complete density-one region is likewise preserved exactly. -/
theorem deformation_image_densityOneRegion (t : ℝ)
    (ht : |t| < deformationRadius) :
    deformation t ht '' densityOneRegion = densityOneRegion := by
  apply image_eq_self_of_fixed_compl
  intro p hp
  apply deformation_fixed_of_not_mem_supportRegion
  exact fun hsupport =>
    hp (dilationSupportRegion_subset_densityOneRegion hsupport)


lemma radiusSq_smul (c : ℝ) (p : PlanePoint) :
    radiusSq (c • p) = c ^ 2 * radiusSq p := by
  rcases p with ⟨x, y⟩
  simp only [radiusSq, Prod.smul_mk, smul_eq_mul]
  ring

lemma radialCircle_subset_dilationCore {r : ℝ} (hr : 0 ≤ r)
    (hrHalf : r ≤ 1 / 2) :
    radialCircle r ⊆ dilationCore := by
  intro p hp
  change radiusSq p = r ^ 2 at hp
  change radiusSq p ≤ (1 / 2 : ℝ) ^ 2
  nlinarith

theorem deformation_on_core (t : ℝ)
    (ht : |t| < deformationRadius) {p : PlanePoint}
    (hp : p ∈ dilationCore) :
    deformation t ht p = (1 + t) • p := by
  rw [deformation_apply, dilationField_eq_self hp]
  simp [add_smul]

/-- Every circle in the dilation core is sent to the literal circle with
radius multiplied by `1 + t`. -/
theorem deformation_image_radialCircle {t r : ℝ}
    (ht : |t| < deformationRadius) (hr : 0 ≤ r)
    (hrHalf : r ≤ 1 / 2) :
    deformation t ht '' radialCircle r =
      radialCircle ((1 + t) * r) := by
  have hc : 0 < 1 + t := one_add_parameter_pos ht
  have hcne : 1 + t ≠ 0 := hc.ne'
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [deformation_on_core t ht
      (radialCircle_subset_dilationCore hr hrHalf hp)]
    change radiusSq ((1 + t) • p) = ((1 + t) * r) ^ 2
    rw [radiusSq_smul]
    change radiusSq p = r ^ 2 at hp
    rw [hp]
    ring
  · intro q hq
    let p : PlanePoint := (1 / (1 + t)) • q
    have hp : p ∈ radialCircle r := by
      change radiusSq p = r ^ 2
      rw [show radiusSq p =
          (1 / (1 + t)) ^ 2 * radiusSq q by
        exact radiusSq_smul (1 / (1 + t)) q]
      change radiusSq q = ((1 + t) * r) ^ 2 at hq
      rw [hq]
      field_simp
    refine ⟨p, hp, ?_⟩
    rw [deformation_on_core t ht
      (radialCircle_subset_dilationCore hr hrHalf hp)]
    dsimp only [p]
    rw [smul_smul]
    simp [hcne]

lemma radialCircle_one_not_mem_supportRegion {p : PlanePoint}
    (hp : p ∈ radialCircle 1) :
    p ∉ dilationSupportRegion := by
  change radiusSq p = (1 : ℝ) ^ 2 at hp
  change ¬ radiusSq p < (3 / 4 : ℝ) ^ 2
  nlinarith

/-- The outer unit circle is fixed pointwise and as a literal set. -/
theorem deformation_image_radialCircle_one (t : ℝ)
    (ht : |t| < deformationRadius) :
    deformation t ht '' radialCircle 1 = radialCircle 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨p, hp, rfl⟩
    rw [deformation_fixed_of_not_mem_supportRegion t ht
      (radialCircle_one_not_mem_supportRegion hp)]
    exact hp
  · intro p hp
    refine ⟨p, hp, ?_⟩
    exact deformation_fixed_of_not_mem_supportRegion t ht
      (radialCircle_one_not_mem_supportRegion hp)

lemma outerRadius_le_seventeen_sixtyfour {epsilon : ℝ}
    (hepsilon_le : epsilon ≤ 1 / 64) :
    outerRadius epsilon ≤ 17 / 64 := by
  unfold outerRadius
  linarith

lemma annularRadii_le_half {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    innerRadius epsilon ≤ 1 / 2 ∧ outerRadius epsilon ≤ 1 / 2 := by
  have houter := outerRadius_le_seventeen_sixtyfour hepsilon_le
  constructor
  · exact (innerRadius_lt_outerRadius hepsilon).le.trans (by
      nlinarith)
  · nlinarith

/-- Exact complete-frontier image: both hidden circles dilate while the outer
unit circle is fixed. -/
theorem frontier_deformation_image_domain {t epsilon : ℝ}
    (ht : |t| < deformationRadius) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    frontier (deformation t ht '' domain epsilon) =
      radialCircle ((1 + t) * innerRadius epsilon) ∪
        radialCircle ((1 + t) * outerRadius epsilon) ∪
          radialCircle 1 := by
  have ha := innerRadius_pos hepsilon hepsilon_le
  have hrHalf := annularRadii_le_half hepsilon hepsilon_le
  rw [← (deformation t ht).toHomeomorph.image_frontier,
    frontier_domain hepsilon hepsilon_le, image_union, image_union,
    deformation_image_radialCircle ht ha.le hrHalf.1,
    deformation_image_radialCircle ht
      (ha.trans (innerRadius_lt_outerRadius hepsilon)).le hrHalf.2,
    deformation_image_radialCircle_one]

/-- Exact weighted cost after fixed-target radial deformation. -/
theorem smoothCost_deformation_image_domain {t epsilon : ℝ}
    (ht : |t| < deformationRadius) (hepsilon : 0 < epsilon)
    (hepsilon_le : epsilon ≤ 1 / 64) :
    smoothCost 2 (deformation t ht '' domain epsilon) =
      ENNReal.ofReal ((3 + t) * Real.pi) := by
  let c := 1 + t
  let a := innerRadius epsilon
  let b := outerRadius epsilon
  have hc : 0 < c := one_add_parameter_pos ht
  have hcUpper : c < 3 / 2 := one_add_parameter_lt_three_halves ht
  have ha : 0 < a := innerRadius_pos hepsilon hepsilon_le
  have hab : a < b := innerRadius_lt_outerRadius hepsilon
  have hbBound : b ≤ 17 / 64 :=
    outerRadius_le_seventeen_sixtyfour hepsilon_le
  have hca : 0 < c * a := mul_pos hc ha
  have hcab : c * a < c * b := mul_lt_mul_of_pos_left hab hc
  have hcb1 : c * b < 1 := by
    calc
      c * b < (3 / 2) * b := mul_lt_mul_of_pos_right hcUpper (ha.trans hab)
      _ ≤ (3 / 2) * (17 / 64) :=
        mul_le_mul_of_nonneg_left hbBound (by norm_num)
      _ < 1 := by norm_num
  have hAB : Disjoint (radialCircle (c * a)) (radialCircle (c * b)) :=
    disjoint_radialCircle hca.le (hca.trans hcab).le hcab.ne
  have hABC :
      Disjoint (radialCircle (c * a) ∪ radialCircle (c * b))
        (radialCircle 1) := by
    rw [Set.disjoint_left]
    intro p hpAB hpOne
    rcases hpAB with hpA | hpB
    · exact Set.disjoint_left.mp
        (disjoint_radialCircle hca.le (by norm_num) (hcab.trans hcb1).ne)
          hpA hpOne
    · exact Set.disjoint_left.mp
        (disjoint_radialCircle (hca.trans hcab).le (by norm_num) hcb1.ne)
          hpB hpOne
  rw [smoothCost_eq_weightedTraceCost_frontier,
    frontier_deformation_image_domain ht hepsilon hepsilon_le,
    show (1 + t) * innerRadius epsilon = c * a by rfl,
    show (1 + t) * outerRadius epsilon = c * b by rfl,
    FiniteBandRearrangement.weightedTraceCost_union_eq 2
      (isCompact_radialCircle 1).measurableSet hABC,
    FiniteBandRearrangement.weightedTraceCost_union_eq 2
      (isCompact_radialCircle (c * b)).measurableSet hAB,
    weightedTraceCost_radialCircle hca (hcab.trans hcb1).le,
    weightedTraceCost_radialCircle (hca.trans hcab) hcb1.le,
    weightedTraceCost_radialCircle (by norm_num : (0 : ℝ) < 1) le_rfl]
  have hA : 0 ≤ 2 * Real.pi * (c * a) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hca.le
  have hB : 0 ≤ 2 * Real.pi * (c * b) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (hca.trans hcab).le
  have hOne : 0 ≤ 2 * Real.pi * (1 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by norm_num)
  rw [← ENNReal.ofReal_add hA hB,
    ← ENNReal.ofReal_add (add_nonneg hA hB) hOne]
  congr 1
  simp only [c, a, b, innerRadius, outerRadius]
  ring

/-- Termwise literal ambient image of the annular-gap recovery. -/
noncomputable def transportedSequence (t : ℝ)
    (ht : |t| < deformationRadius) : SmoothSequence :=
  (deformation t ht).ambientImage sequence

@[simp] theorem transportedSequence_carrier (t : ℝ)
    (ht : |t| < deformationRadius) (n : ℕ) :
    (transportedSequence t ht).carrier n =
      deformation t ht '' domain (epsilon n) := rfl

/-- The deformed sequence still converges globally to the unchanged literal
unit disk. -/
theorem transportedSequence_converges (t : ℝ)
    (ht : |t| < deformationRadius) :
    (transportedSequence t ht).ConvergesTo unitDisk := by
  have h := (deformation t ht).convergesTo_ambientImage
    sequence unitDisk sequence_converges
  rw [deformation_image_unitDisk t ht] at h
  exact h

/-- Every recovery index has the same exact deformed cost. -/
theorem transportedSequence_termCost (t : ℝ)
    (ht : |t| < deformationRadius) (n : ℕ) :
    smoothCost 2 ((transportedSequence t ht).carrier n) =
      ENNReal.ofReal ((3 + t) * Real.pi) := by
  rw [transportedSequence_carrier]
  exact smoothCost_deformation_image_domain ht (epsilon_pos n) (epsilon_le n)

/-- The exact positive increment holds at every recovery index before taking
any sequence liminf. -/
theorem transportedSequence_termCost_eq_add {t : ℝ}
    (ht : |t| < deformationRadius) (htPos : 0 < t) (n : ℕ) :
    smoothCost 2 ((transportedSequence t ht).carrier n) =
      smoothCost 2 (sequence.carrier n) +
        ENNReal.ofReal (Real.pi * t) := by
  rw [transportedSequence_termCost, sequence_termCost,
    ← ENNReal.ofReal_add
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le)
      (mul_nonneg Real.pi_pos.le htPos.le)]
  congr 1
  ring

/-- No recovery/deformation limit is interchanged: for each fixed admissible
parameter, the complete sequence cost is calculated directly. -/
theorem transportedSequence_cost (t : ℝ)
    (ht : |t| < deformationRadius) :
    (transportedSequence t ht).cost 2 =
      ENNReal.ofReal ((3 + t) * Real.pi) := by
  unfold SmoothSequence.cost
  have hfun :
      (fun n => smoothCost 2 ((transportedSequence t ht).carrier n)) =
        fun _ : ℕ => ENNReal.ofReal ((3 + t) * Real.pi) := by
    funext n
    exact transportedSequence_termCost t ht n
  rw [hfun]
  simp

/-- For a positive parameter, the exact finite extended-cost increment is
`pi * t`. -/
theorem transportedSequence_cost_eq_add {t : ℝ}
    (ht : |t| < deformationRadius) (htPos : 0 < t) :
    (transportedSequence t ht).cost 2 =
      sequence.cost 2 + ENNReal.ofReal (Real.pi * t) := by
  rw [transportedSequence_cost, sequence_cost,
    ← ENNReal.ofReal_add
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) Real.pi_pos.le)
      (mul_nonneg Real.pi_pos.le htPos.le)]
  congr 1
  ring

theorem transportedSequence_cost_lt_top (t : ℝ)
    (ht : |t| < deformationRadius) :
    (transportedSequence t ht).cost 2 < ⊤ := by
  rw [transportedSequence_cost]
  exact ENNReal.ofReal_lt_top

theorem sequence_cost_lt_top :
    sequence.cost 2 < ⊤ := by
  rw [sequence_cost]
  exact ENNReal.ofReal_lt_top

theorem transportedSequence_termCost_lt_top (t : ℝ)
    (ht : |t| < deformationRadius) (n : ℕ) :
    smoothCost 2 ((transportedSequence t ht).carrier n) < ⊤ := by
  rw [transportedSequence_termCost]
  exact ENNReal.ofReal_lt_top

/-- Real-valued finite-cost normalization of the same exact increment. -/
theorem transportedSequence_normalizedCost_eq_pi {t : ℝ}
    (ht : |t| < deformationRadius) (htPos : 0 < t) :
    (((transportedSequence t ht).cost 2).toReal -
        (sequence.cost 2).toReal) / t = Real.pi := by
  have hnew : 0 ≤ (3 + t) * Real.pi := by
    have hc := one_add_parameter_pos ht
    exact mul_nonneg (by linarith) Real.pi_pos.le
  have hold : 0 ≤ 3 * Real.pi :=
    mul_nonneg (by norm_num) Real.pi_pos.le
  rw [transportedSequence_cost, sequence_cost,
    ENNReal.toReal_ofReal hnew, ENNReal.toReal_ofReal hold]
  field_simp [htPos.ne']
  ring

/-- Positive parameters tending to zero inside the certified two-sided
neighborhood. -/
noncomputable def positiveStep (k : ℕ) : ℝ :=
  deformationRadius / ((k : ℝ) + 2)

lemma positiveStep_pos (k : ℕ) : 0 < positiveStep k := by
  unfold positiveStep
  exact div_pos deformationRadius_pos (by positivity)

lemma positiveStep_abs_lt (k : ℕ) :
    |positiveStep k| < deformationRadius := by
  rw [abs_of_pos (positiveStep_pos k)]
  unfold positiveStep
  exact div_lt_self deformationRadius_pos (by
    have hkNat : 1 < k + 2 := by omega
    exact_mod_cast hkNat)

lemma positiveStep_tendsto_zero :
    Tendsto positiveStep atTop (𝓝 0) := by
  have hinvBase :
      Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hinv :
      Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2)) atTop (𝓝 0) := by
    convert hinvBase.comp (tendsto_add_atTop_nat 1) using 1
    funext k
    congr 1
    push_cast
    ring
  have hmul :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => deformationRadius) atTop
        (𝓝 deformationRadius)).mul hinv
  change Tendsto
    (fun k : ℕ => deformationRadius / ((k : ℝ) + 2)) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, one_mul, mul_zero] using hmul

/-- The concrete one-sided deformation family. -/
noncomputable def positiveDeformation (k : ℕ) : SmoothAmbientEquiv :=
  deformation (positiveStep k) (positiveStep_abs_lt k)

/-- Apply the fixed positive deformation family to any smooth sequence. -/
noncomputable def positiveAmbientImage (A : SmoothSequence) (k : ℕ) :
    SmoothSequence :=
  (positiveDeformation k).ambientImage A

theorem positiveAmbientImage_sequence_converges (k : ℕ) :
    (positiveAmbientImage sequence k).ConvergesTo unitDisk := by
  change (transportedSequence (positiveStep k)
    (positiveStep_abs_lt k)).ConvergesTo unitDisk
  exact transportedSequence_converges _ _

/-- The normalized transported cost is literally `pi` at every positive
deformation scale. -/
theorem positiveAmbientImage_sequence_normalizedCost (k : ℕ) :
    (((positiveAmbientImage sequence k).cost 2).toReal -
        (sequence.cost 2).toReal) / positiveStep k = Real.pi := by
  change (((transportedSequence (positiveStep k)
      (positiveStep_abs_lt k)).cost 2).toReal -
        (sequence.cost 2).toReal) / positiveStep k = Real.pi
  exact transportedSequence_normalizedCost_eq_pi
    (positiveStep_abs_lt k) (positiveStep_pos k)

/-- The positive one-sided normalized cost limit is nonzero. -/
theorem positiveAmbientImage_sequence_normalizedCost_tendsto :
    Tendsto
      (fun k => (((positiveAmbientImage sequence k).cost 2).toReal -
        (sequence.cost 2).toReal) / positiveStep k)
      atTop (𝓝 Real.pi) := by
  simpa only [positiveAmbientImage_sequence_normalizedCost] using
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Real.pi) atTop (𝓝 Real.pi))

/-- The precise overstrong transported-cost identification tested here:
global characteristic convergence alone would force zero normalized cost
change under this target-preserving ambient family. -/
def GlobalConvergenceForcesZeroFixedTargetTransport : Prop :=
  ∀ A : SmoothSequence, A.ConvergesTo unitDisk →
    Tendsto
      (fun k => (((positiveAmbientImage A k).cost 2).toReal -
        (A.cost 2).toReal) / positiveStep k)
      atTop (𝓝 0)

/-- The annular-gap recovery refutes the global-convergence-only
transported-cost identification.  The target is fixed exactly, every ambient
map is globally invertible and smooth, and every cost used above is finite.
This says nothing about exact minimizing recovery or an infimum-level relaxed
cost inequality. -/
theorem not_globalConvergenceForcesZeroFixedTargetTransport :
    ¬ GlobalConvergenceForcesZeroFixedTargetTransport := by
  intro hglobal
  have hzero := hglobal sequence sequence_converges
  have heq : Real.pi = 0 :=
    tendsto_nhds_unique
      positiveAmbientImage_sequence_normalizedCost_tendsto hzero
  exact Real.pi_ne_zero heq

end CMVRelaxation.AnnularGapRecovery
