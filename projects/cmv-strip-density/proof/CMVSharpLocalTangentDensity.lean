/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVCompactCoreEnergyLimit
import CMVRelativeLevelTraceAveraging
import CMVFiniteCornerRepair
import CMVFigureFiveSourceGeometry
import CMVFiniteBandGraphProjection
import CMVAELocalChartPreservation

open Set Function Filter MeasureTheory Metric
open CMVRelaxation.FiniteJunctionRepair
open CMVRelaxation.LocalChartPreservation
open scoped ENNReal MeasureTheory Topology NNReal symmDiff

noncomputable section

namespace CMVRelaxation
namespace CompactCoreEnergy

/-- A closed ball for the Euclidean metric used by `FrontierMeasure`, pulled
back to the source coordinate plane. -/
def euclideanClosedBall (p : PlanePoint) (r : ℝ) : Set PlanePoint :=
  planeEuclideanHomeomorph ⁻¹' Metric.closedBall (planeEuclideanHomeomorph p) r

lemma isClosed_euclideanClosedBall (p : PlanePoint) (r : ℝ) :
    IsClosed (euclideanClosedBall p r) :=
  isClosed_closedBall.preimage planeEuclideanHomeomorph.continuous

@[simp] lemma euclideanRigidMap_graphTangentFrame_zero
    (x0 y0 slope : ℝ) :
    euclideanRigidMap (graphTangentFrame x0 y0 slope) (0, 0) = (x0, y0) := by
  simp [euclideanRigidMap_graphTangentFrame]

@[simp] lemma euclideanRigidMap_supergraphTangentFrame_zero
    (x0 y0 slope : ℝ) :
    euclideanRigidMap (supergraphTangentFrame x0 y0 slope) (0, 0) = (x0, y0) := by
  simp [euclideanRigidMap_supergraphTangentFrame]

lemma rigidProjectionBox_subset_euclideanClosedBall_of_sq
    (e : EuclideanPlane ≃ᵢ EuclideanPlane) (p : PlanePoint)
    {h rho r : ℝ} (hh : 0 ≤ h) (hrho : 0 ≤ rho) (hr : 0 ≤ r)
    (he0 : euclideanRigidMap e (0, 0) = p)
    (hsq : h ^ 2 + (2 * rho) ^ 2 ≤ r ^ 2) :
    rigidProjectionBox e (-h) h 0 rho ⊆ euclideanClosedBall p r := by
  rintro q ⟨z, hz, rfl⟩
  change dist
    (planeEuclideanHomeomorph (euclideanRigidMap e z))
    (planeEuclideanHomeomorph p) ≤ r
  rw [← he0, planeEuclideanHomeomorph_euclideanRigidMap,
    planeEuclideanHomeomorph_euclideanRigidMap, e.dist_eq]
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change Real.sqrt (dist z.1 0 ^ 2 + dist z.2 0 ^ 2) ≤ r
  rw [Real.sqrt_le_iff]
  constructor
  · exact hr
  change z.1 ∈ Icc (-h) h ∧ z.2 ∈ Icc (0 - 2 * rho) (0 + 2 * rho) at hz
  rw [Real.dist_eq, Real.dist_eq]
  simp only [sub_zero]
  have hz1 : |z.1| ≤ h := abs_le.mpr hz.1
  have hz2 : |z.2| ≤ 2 * rho :=
    abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hz1sq : |z.1| ^ 2 ≤ h ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz1)
      (add_nonneg hh (abs_nonneg z.1))]
  have hz2sq : |z.2| ^ 2 ≤ (2 * rho) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz2)
      (add_nonneg (by positivity : 0 ≤ 2 * rho) (abs_nonneg z.2))]
  nlinarith


/-- The fixed loss parameter chooses a tangent half-width asymptotic to the
Euclidean radius and a lower-order normal collar. -/
def tangentHalfWidth (k r : ℝ) : ℝ := k * r

def tangentCollar (k r : ℝ) : ℝ := (1 - k) * r / 4

lemma tangent_box_sq_le
    {k r : ℝ} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    tangentHalfWidth k r ^ 2 + (2 * tangentCollar k r) ^ 2 ≤ r ^ 2 := by
  unfold tangentHalfWidth tangentCollar
  nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk1),
    sq_nonneg (1 - k), sq_nonneg r]

/-- A local strict subgraph with only `C¹` regularity produces shrinking
tangent-aligned rigid projection patches. -/
theorem eventually_exists_subgraph_C1_tangent_patch
    {lam w : ℝ} {E K : Set PlanePoint} {p : PlanePoint} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hφp : φ p.1 = p.2)
    (hgraph : ∀ᶠ q in 𝓝 p, q ∈ E ↔ q.2 < φ q.1)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ P : RigidProjectionPatch lam E,
      P.weight = w ∧
      P.a = -tangentHalfWidth k r ∧
      P.b = tangentHalfWidth k r ∧
      P.window ⊆ euclideanClosedBall p r ∧ P.window ⊆ K := by
  have hK : ∀ᶠ q in 𝓝 p, q ∈ K := by
    filter_upwards [isOpen_interior.mem_nhds hpK] with q hq
    exact interior_subset hq
  have hlocal :
      ∀ᶠ q in 𝓝 p,
        (q ∈ E ↔ q.2 < φ q.1) ∧
          w ≤ StripDensity lam q ∧ q ∈ K :=
    hgraph.and (hdensity.and hK)
  have hlocalE :
      ∀ᶠ z in 𝓝 (planeEuclideanHomeomorph p),
        ((planeEuclideanHomeomorph.symm z ∈ E ↔
            (planeEuclideanHomeomorph.symm z).2 <
              φ (planeEuclideanHomeomorph.symm z).1) ∧
          w ≤ StripDensity lam (planeEuclideanHomeomorph.symm z) ∧
          planeEuclideanHomeomorph.symm z ∈ K) := by
    simpa only [planeEuclideanHomeomorph_apply,
      planeEuclideanHomeomorph.symm_apply_apply] using
      planeEuclideanHomeomorph.symm.continuous.continuousAt.tendsto.eventually hlocal
  obtain ⟨δlocal, hδlocal, hlocalBall⟩ :=
    Metric.eventually_nhds_iff.mp hlocalE
  let ε : ℝ := (1 - k) / 8
  have hε : 0 < ε := div_pos (sub_pos.mpr hk1) (by norm_num)
  obtain ⟨δderiv, hδderiv, htangent⟩ :=
    FiniteBandRearrangement.HeightGraphProjection.Patch.exists_uniform_tangent_remainder_on_Icc_C1
      φ hφ
        (a := p.1 - 1) (b := p.1 + 1) hε
  let R : ℝ := min (δlocal / 2) (min (δderiv / 2) (1 / 2))
  have hR : 0 < R := by
    exact lt_min (half_pos hδlocal)
      (lt_min (half_pos hδderiv) (by norm_num))
  filter_upwards [Ioc_mem_nhdsGT hR] with r hr
  have hr0 : 0 < r := hr.1
  have hrLocal : r < δlocal := by
    have := hr.2.trans (min_le_left (δlocal / 2)
      (min (δderiv / 2) (1 / 2)))
    linarith
  have hrDeriv : r < δderiv := by
    have := hr.2.trans ((min_le_right (δlocal / 2)
      (min (δderiv / 2) (1 / 2))).trans
        (min_le_left (δderiv / 2) (1 / 2)))
    linarith
  have hrOne : r < 1 := by
    have := hr.2.trans ((min_le_right (δlocal / 2)
      (min (δderiv / 2) (1 / 2))).trans
        (min_le_right (δderiv / 2) (1 / 2)))
    linarith
  let h := tangentHalfWidth k r
  let rho := tangentCollar k r
  have hh : 0 < h := mul_pos hk0 hr0
  have hrho : 0 < rho :=
    div_pos (mul_pos (sub_pos.mpr hk1) hr0) (by norm_num)
  have hsum : h + 2 * rho ≤ r := by
    dsimp only [h, rho, tangentHalfWidth, tangentCollar]
    nlinarith [mul_pos (sub_pos.mpr hk1) hr0]
  have htangent' : ∀ x, |x - p.1| ≤ h + 2 * rho →
      |φ x - φ p.1 - deriv φ p.1 * (x - p.1)| ≤
        ε * |x - p.1| := by
    intro x hx
    apply htangent p.1 (by simp) x
    · rw [mem_Icc]
      have hxr : |x - p.1| ≤ r := hx.trans hsum
      constructor <;> rw [abs_le] at hxr <;> linarith
    · exact (hx.trans hsum).trans_lt hrDeriv
  have hsmall : ε * (h + 2 * rho) < rho := by
    have hle := mul_le_mul_of_nonneg_left hsum hε.le
    dsimp only [ε, rho, tangentCollar]
    have hkr : 0 < (1 - k) * r := mul_pos (sub_pos.mpr hk1) hr0
    nlinarith
  let frame := graphTangentFrame p.1 (φ p.1) (deriv φ p.1)
  have hresidual :
      ∀ z ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
        |φ (euclideanRigidMap frame z).1 - φ p.1 -
            deriv φ p.1 * ((euclideanRigidMap frame z).1 - p.1)| <
          rho * Real.sqrt (1 + deriv φ p.1 ^ 2) := by
    apply tangentBox_residual_lt_of_bound φ p.1 (deriv φ p.1)
      h rho ε hrho hε.le
    · exact abs_graphTangentFrame_fst_sub_le p.1 (φ p.1) (deriv φ p.1)
    · exact htangent'
    · exact hsmall
  have hboxBall :
      rigidProjectionBox frame (-h) h 0 rho ⊆ euclideanClosedBall p r := by
    apply rigidProjectionBox_subset_euclideanClosedBall_of_sq frame p
      hh.le hrho.le hr0.le
    · simpa only [frame, hφp] using
        euclideanRigidMap_graphTangentFrame_zero p.1 (φ p.1) (deriv φ p.1)
    · exact tangent_box_sq_le hk0.le hk1.le
  have hnear (q : PlanePoint) (hq : q ∈ euclideanClosedBall p r) :
      (q ∈ E ↔ q.2 < φ q.1) ∧
        w ≤ StripDensity lam q ∧ q ∈ K := by
    have hdist :
        planeEuclideanHomeomorph q ∈
          Metric.ball (planeEuclideanHomeomorph p) δlocal := by
      change dist (planeEuclideanHomeomorph q)
        (planeEuclideanHomeomorph p) < δlocal
      change dist (planeEuclideanHomeomorph q)
        (planeEuclideanHomeomorph p) ≤ r at hq
      exact hq.trans_lt hrLocal
    simpa only [planeEuclideanHomeomorph.symm_apply_apply] using
      hlocalBall hdist
  have hdensityBox :
      ∀ q ∈ rigidProjectionBox frame (-h) h 0 rho,
        w ≤ StripDensity lam q :=
    fun q hq => (hnear q (hboxBall hq)).2.1
  let P0 : RigidProjectionPatch lam {q : PlanePoint | q.2 < φ q.1} :=
    subgraphTangentPatch lam w φ p.1 (-h) h rho hrho
      hresidual hdensityBox
  have hP0window :
      P0.window = rigidProjectionBox frame (-h) h 0 rho := rfl
  have hchange : ∀ q ∈ P0.window,
      q ∈ {q : PlanePoint | q.2 < φ q.1} ↔ q ∈ E := by
    intro q hq
    exact (hnear q (hboxBall (hP0window ▸ hq))).1.symm
  let P : RigidProjectionPatch lam E := P0.changeCarrierOnWindow hchange
  refine ⟨P, rfl, rfl, rfl, ?_, ?_⟩
  · intro q hq
    change q ∈ P0.window at hq
    rw [hP0window] at hq
    exact hboxBall hq
  · intro q hq
    change q ∈ P0.window at hq
    rw [hP0window] at hq
    exact (hnear q (hboxBall hq)).2.2


/-- The corresponding `C¹` construction for a local strict supergraph. -/
theorem eventually_exists_supergraph_C1_tangent_patch
    {lam w : ℝ} {E K : Set PlanePoint} {p : PlanePoint} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hφp : φ p.1 = p.2)
    (hgraph : ∀ᶠ q in 𝓝 p, q ∈ E ↔ φ q.1 < q.2)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ P : RigidProjectionPatch lam E,
      P.weight = w ∧
      P.a = -tangentHalfWidth k r ∧
      P.b = tangentHalfWidth k r ∧
      P.window ⊆ euclideanClosedBall p r ∧ P.window ⊆ K := by
  have hK : ∀ᶠ q in 𝓝 p, q ∈ K := by
    filter_upwards [isOpen_interior.mem_nhds hpK] with q hq
    exact interior_subset hq
  have hlocal :
      ∀ᶠ q in 𝓝 p,
        (q ∈ E ↔ φ q.1 < q.2) ∧
          w ≤ StripDensity lam q ∧ q ∈ K :=
    hgraph.and (hdensity.and hK)
  have hlocalE :
      ∀ᶠ z in 𝓝 (planeEuclideanHomeomorph p),
        ((planeEuclideanHomeomorph.symm z ∈ E ↔
            φ (planeEuclideanHomeomorph.symm z).1 <
              (planeEuclideanHomeomorph.symm z).2) ∧
          w ≤ StripDensity lam (planeEuclideanHomeomorph.symm z) ∧
          planeEuclideanHomeomorph.symm z ∈ K) := by
    simpa only [planeEuclideanHomeomorph_apply,
      planeEuclideanHomeomorph.symm_apply_apply] using
      planeEuclideanHomeomorph.symm.continuous.continuousAt.tendsto.eventually hlocal
  obtain ⟨δlocal, hδlocal, hlocalBall⟩ :=
    Metric.eventually_nhds_iff.mp hlocalE
  let ε : ℝ := (1 - k) / 8
  have hε : 0 < ε := div_pos (sub_pos.mpr hk1) (by norm_num)
  obtain ⟨δderiv, hδderiv, htangent⟩ :=
    FiniteBandRearrangement.HeightGraphProjection.Patch.exists_uniform_tangent_remainder_on_Icc_C1
      φ hφ
        (a := p.1 - 1) (b := p.1 + 1) hε
  let R : ℝ := min (δlocal / 2) (min (δderiv / 2) (1 / 2))
  have hR : 0 < R := by
    exact lt_min (half_pos hδlocal)
      (lt_min (half_pos hδderiv) (by norm_num))
  filter_upwards [Ioc_mem_nhdsGT hR] with r hr
  have hr0 : 0 < r := hr.1
  have hrLocal : r < δlocal := by
    have := hr.2.trans (min_le_left (δlocal / 2)
      (min (δderiv / 2) (1 / 2)))
    linarith
  have hrDeriv : r < δderiv := by
    have := hr.2.trans ((min_le_right (δlocal / 2)
      (min (δderiv / 2) (1 / 2))).trans
        (min_le_left (δderiv / 2) (1 / 2)))
    linarith
  have hrOne : r < 1 := by
    have := hr.2.trans ((min_le_right (δlocal / 2)
      (min (δderiv / 2) (1 / 2))).trans
        (min_le_right (δderiv / 2) (1 / 2)))
    linarith
  let h := tangentHalfWidth k r
  let rho := tangentCollar k r
  have hh : 0 < h := mul_pos hk0 hr0
  have hrho : 0 < rho :=
    div_pos (mul_pos (sub_pos.mpr hk1) hr0) (by norm_num)
  have hsum : h + 2 * rho ≤ r := by
    dsimp only [h, rho, tangentHalfWidth, tangentCollar]
    nlinarith [mul_pos (sub_pos.mpr hk1) hr0]
  have htangent' : ∀ x, |x - p.1| ≤ h + 2 * rho →
      |φ x - φ p.1 - deriv φ p.1 * (x - p.1)| ≤
        ε * |x - p.1| := by
    intro x hx
    apply htangent p.1 (by simp) x
    · rw [mem_Icc]
      have hxr : |x - p.1| ≤ r := hx.trans hsum
      constructor <;> rw [abs_le] at hxr <;> linarith
    · exact (hx.trans hsum).trans_lt hrDeriv
  have hsmall : ε * (h + 2 * rho) < rho := by
    have hle := mul_le_mul_of_nonneg_left hsum hε.le
    dsimp only [ε, rho, tangentCollar]
    have hkr : 0 < (1 - k) * r := mul_pos (sub_pos.mpr hk1) hr0
    nlinarith
  let frame := supergraphTangentFrame p.1 (φ p.1) (deriv φ p.1)
  have hresidual :
      ∀ z ∈ Icc (-h) h ×ˢ Icc (-2 * rho) (2 * rho),
        |φ (euclideanRigidMap frame z).1 - φ p.1 -
            deriv φ p.1 * ((euclideanRigidMap frame z).1 - p.1)| <
          rho * Real.sqrt (1 + deriv φ p.1 ^ 2) := by
    apply tangentBox_residual_lt_of_bound φ p.1 (deriv φ p.1)
      h rho ε hrho hε.le
    · exact abs_supergraphTangentFrame_fst_sub_le
        p.1 (φ p.1) (deriv φ p.1)
    · exact htangent'
    · exact hsmall
  have hboxBall :
      rigidProjectionBox frame (-h) h 0 rho ⊆ euclideanClosedBall p r := by
    apply rigidProjectionBox_subset_euclideanClosedBall_of_sq frame p
      hh.le hrho.le hr0.le
    · simpa only [frame, hφp] using
        euclideanRigidMap_supergraphTangentFrame_zero
          p.1 (φ p.1) (deriv φ p.1)
    · exact tangent_box_sq_le hk0.le hk1.le
  have hnear (q : PlanePoint) (hq : q ∈ euclideanClosedBall p r) :
      (q ∈ E ↔ φ q.1 < q.2) ∧
        w ≤ StripDensity lam q ∧ q ∈ K := by
    have hdist :
        planeEuclideanHomeomorph q ∈
          Metric.ball (planeEuclideanHomeomorph p) δlocal := by
      change dist (planeEuclideanHomeomorph q)
        (planeEuclideanHomeomorph p) < δlocal
      change dist (planeEuclideanHomeomorph q)
        (planeEuclideanHomeomorph p) ≤ r at hq
      exact hq.trans_lt hrLocal
    simpa only [planeEuclideanHomeomorph.symm_apply_apply] using
      hlocalBall hdist
  have hdensityBox :
      ∀ q ∈ rigidProjectionBox frame (-h) h 0 rho,
        w ≤ StripDensity lam q :=
    fun q hq => (hnear q (hboxBall hq)).2.1
  let P0 : RigidProjectionPatch lam {q : PlanePoint | φ q.1 < q.2} :=
    supergraphTangentPatch lam w φ p.1 (-h) h rho hrho
      hresidual hdensityBox
  have hP0window :
      P0.window = rigidProjectionBox frame (-h) h 0 rho := rfl
  have hchange : ∀ q ∈ P0.window,
      q ∈ {q : PlanePoint | φ q.1 < q.2} ↔ q ∈ E := by
    intro q hq
    exact (hnear q (hboxBall (hP0window ▸ hq))).1.symm
  let P : RigidProjectionPatch lam E := P0.changeCarrierOnWindow hchange
  refine ⟨P, rfl, rfl, rfl, ?_, ?_⟩
  · intro q hq
    change q ∈ P0.window at hq
    rw [hP0window] at hq
    exact hboxBall hq
  · intro q hq
    change q ∈ P0.window at hq
    rw [hP0window] at hq
    exact (hnear q (hboxBall hq)).2.2

/-- A genuine local one-sided smooth graph produces tangent-aligned projection
rectangles whose width is asymptotic to the diameter of a shrinking Euclidean
ball.  The rectangles stay inside both that ball and the fixed compact core. -/
theorem eventually_exists_vertical_tangent_patch
    {lam w : ℝ} {E K : Set PlanePoint} {p : PlanePoint}
    {side : SpliceGraphOccupiedSide}
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide .vertical side E p)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), ∃ P : RigidProjectionPatch lam E,
      P.weight = w ∧
      P.a = -tangentHalfWidth k r ∧
      P.b = tangentHalfWidth k r ∧
      P.window ⊆ euclideanClosedBall p r ∧ P.window ⊆ K := by
  cases side with
  | negative =>
      obtain ⟨φ, hφ, hφp, hgraph⟩ :=
        germ.exists_vertical_graphDomain_germ
      apply eventually_exists_subgraph_C1_tangent_patch
        (hφ.of_le (by
          calc
            (1 : WithTop ℕ∞) = ↑(1 : ℕ∞) := by norm_num
            _ ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top))
        hφp hgraph hdensity hpK hk0 hk1
  | positive =>
      obtain ⟨φ, hφ, hφp, hgraph⟩ :=
        germ.exists_vertical_graphDomain_germ
      apply eventually_exists_supergraph_C1_tangent_patch
        (hφ.of_le (by
          calc
            (1 : WithTop ℕ∞) = ↑(1 : ℕ∞) := by norm_num
            _ ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top))
        hφp hgraph hdensity hpK hk0 hk1


/-- The compact-core limit energy normalized by the Euclidean diameter of a
closed ball. -/
def euclideanClosedBallDensity
    {lam : ℝ} {A : SmoothSequence} {K : Set PlanePoint}
    (L : Limit lam A K) (p : PlanePoint) (r : ℝ) : ℝ≥0∞ :=
  (L.limitEnergy : Measure PlanePoint) (euclideanClosedBall p r) /
    ENNReal.ofReal (2 * r)

/-- Any eventual family of tangent patches with width `2*k*r` transfers to
the corresponding fixed-`k` Euclidean ball-density bound. -/
theorem eventually_mul_le_euclideanClosedBallDensity_of_tangent_patches
    {lam w : ℝ} {A : SmoothSequence} {E K : Set PlanePoint} {p : PlanePoint}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E) (hw : 0 ≤ w)
    {k : ℝ} (hk0 : 0 < k)
    (hpatches : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ P : RigidProjectionPatch lam E,
        P.weight = w ∧
        P.a = -tangentHalfWidth k r ∧
        P.b = tangentHalfWidth k r ∧
        P.window ⊆ euclideanClosedBall p r ∧ P.window ⊆ K) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal w * ENNReal.ofReal k ≤
        euclideanClosedBallDensity L p r := by
  filter_upwards [hpatches, self_mem_nhdsWithin] with r hpatch hr
  obtain ⟨P, hweight, ha, hb, hPball, hPcore⟩ := hpatch
  have hr0 : 0 < r := hr
  have hpay :=
    rigid_projection_payoff_le_limit L hconv P.frame hE P.rho_pos
      P.lower_collar P.upper_collar P.weight P.density_lower hPcore
  have hpayBall :
      ENNReal.ofReal w * ENNReal.ofReal (2 * k * r) ≤
        (L.limitEnergy : Measure PlanePoint) (euclideanClosedBall p r) := by
    calc
      ENNReal.ofReal w * ENNReal.ofReal (2 * k * r) =
          ENNReal.ofReal P.weight * ENNReal.ofReal (P.b - P.a) := by
            rw [hweight, ha, hb]
            congr 2
            dsimp only [tangentHalfWidth]
            ring_nf
      _ ≤ (L.limitEnergy : Measure PlanePoint) P.window := hpay
      _ ≤ (L.limitEnergy : Measure PlanePoint) (euclideanClosedBall p r) :=
        measure_mono hPball
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hr0)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).2
  calc
    (ENNReal.ofReal w * ENNReal.ofReal k) * ENNReal.ofReal (2 * r) =
        ENNReal.ofReal (w * k) * ENNReal.ofReal (2 * r) := by
          rw [ENNReal.ofReal_mul hw]
    _ = ENNReal.ofReal ((w * k) * (2 * r)) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hw hk0.le)]
    _ = ENNReal.ofReal (w * (2 * k * r)) := by ring_nf
    _ = ENNReal.ofReal w * ENNReal.ofReal (2 * k * r) :=
      ENNReal.ofReal_mul hw
    _ ≤ (L.limitEnergy : Measure PlanePoint) (euclideanClosedBall p r) :=
      hpayBall

/-- Every fixed tangential width fraction gives a lower bound for all
sufficiently small Euclidean balls.  The projection estimate is first passed
to the fixed compact-core limit measure and only then is the radius varied. -/
theorem eventually_mul_le_euclideanClosedBallDensity
    {lam w : ℝ} {A : SmoothSequence} {E K : Set PlanePoint} {p : PlanePoint}
    {side : SpliceGraphOccupiedSide}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E)
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide .vertical side E p)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) (hw : 0 ≤ w)
    {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal w * ENNReal.ofReal k ≤
        euclideanClosedBallDensity L p r := by
  exact eventually_mul_le_euclideanClosedBallDensity_of_tangent_patches
    L hconv hE hw hk0
    (eventually_exists_vertical_tangent_patch germ hdensity hpK hk0 hk1)

/-- Remove a real multiplicative loss after establishing every fixed fraction
strictly below one. -/
lemma ofReal_le_of_mul_ofReal_le_all_lt_one
    {w : ℝ} {D : ℝ≥0∞} (hw : 0 ≤ w)
    (hk : ∀ k : ℝ, 0 < k → k < 1 →
      ENNReal.ofReal w * ENNReal.ofReal k ≤ D) :
    ENNReal.ofReal w ≤ D := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro z hz
  have hw0 : 0 < w := by
    by_contra hn
    have hwle : w ≤ 0 := le_of_not_gt hn
    have : ENNReal.ofReal w = 0 := ENNReal.ofReal_eq_zero.mpr hwle
    rw [this] at hz
    exact (not_lt_of_ge bot_le) hz
  have hzw : (z : ℝ) < w := by
    simpa using ENNReal.toReal_lt_of_lt_ofReal hz
  let k : ℝ := ((z : ℝ) + w) / (2 * w)
  have hk0 : 0 < k := by
    dsimp only [k]
    positivity
  have hk1 : k < 1 := by
    dsimp only [k]
    rw [div_lt_one (mul_pos (by norm_num) hw0)]
    linarith
  have hzwk : (z : ℝ) ≤ w * k := by
    dsimp only [k]
    calc
      (z : ℝ) ≤ ((z : ℝ) + w) / 2 := by linarith
      _ = w * (((z : ℝ) + w) / (2 * w)) := by
        field_simp [hw0.ne']
  calc
    (z : ℝ≥0∞) = ENNReal.ofReal (z : ℝ) := by simp
    _ ≤ ENNReal.ofReal (w * k) := ENNReal.ofReal_le_ofReal hzwk
    _ = ENNReal.ofReal w * ENNReal.ofReal k := ENNReal.ofReal_mul hw
    _ ≤ D := hk k hk0 hk1

/-- Sharp lower Euclidean ball density at a genuine one-sided smooth boundary
germ.  All tangential-width and collar losses are removed after the
approximating sequence has already been passed to `L.limitEnergy`. -/
theorem sharp_lower_euclideanClosedBallDensity
    {lam w : ℝ} {A : SmoothSequence} {E K : Set PlanePoint} {p : PlanePoint}
    {side : SpliceGraphOccupiedSide}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E)
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide .vertical side E p)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) (hw : 0 ≤ w) :
    ENNReal.ofReal w ≤
      liminf (euclideanClosedBallDensity L p) (𝓝[>] (0 : ℝ)) := by
  let D : ℝ≥0∞ :=
    liminf (euclideanClosedBallDensity L p) (𝓝[>] (0 : ℝ))
  have hk (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
      ENNReal.ofReal w * ENNReal.ofReal k ≤ D := by
    exact le_liminf_of_le (by isBoundedDefault)
      (eventually_mul_le_euclideanClosedBallDensity L hconv hE germ
        hdensity hpK hw hk0 hk1)
  exact ofReal_le_of_mul_ofReal_le_all_lt_one hw hk

/-- Sharp density from a genuine local one-sided `C¹` subgraph, with no global
boundary model and no assumed density conclusion. -/
theorem sharp_lower_euclideanClosedBallDensity_of_subgraph_C1
    {lam w : ℝ} {A : SmoothSequence} {E K : Set PlanePoint}
    {p : PlanePoint} {φ : ℝ → ℝ}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E) (hφ : ContDiff ℝ 1 φ)
    (hφp : φ p.1 = p.2)
    (hgraph : ∀ᶠ q in 𝓝 p, q ∈ E ↔ q.2 < φ q.1)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) (hw : 0 ≤ w) :
    ENNReal.ofReal w ≤
      liminf (euclideanClosedBallDensity L p) (𝓝[>] (0 : ℝ)) := by
  apply ofReal_le_of_mul_ofReal_le_all_lt_one hw
  intro k hk0 hk1
  apply le_liminf_of_le (by isBoundedDefault)
  exact eventually_mul_le_euclideanClosedBallDensity_of_tangent_patches
    L hconv hE hw hk0
    (eventually_exists_subgraph_C1_tangent_patch hφ hφp hgraph
      hdensity hpK hk0 hk1)

/-- Sharp density from the corresponding local one-sided `C¹` supergraph. -/
theorem sharp_lower_euclideanClosedBallDensity_of_supergraph_C1
    {lam w : ℝ} {A : SmoothSequence} {E K : Set PlanePoint}
    {p : PlanePoint} {φ : ℝ → ℝ}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E) (hφ : ContDiff ℝ 1 φ)
    (hφp : φ p.1 = p.2)
    (hgraph : ∀ᶠ q in 𝓝 p, q ∈ E ↔ φ q.1 < q.2)
    (hdensity : ∀ᶠ q in 𝓝 p, w ≤ StripDensity lam q)
    (hpK : p ∈ interior K) (hw : 0 ≤ w) :
    ENNReal.ofReal w ≤
      liminf (euclideanClosedBallDensity L p) (𝓝[>] (0 : ℝ)) := by
  apply ofReal_le_of_mul_ofReal_le_all_lt_one hw
  intro k hk0 hk1
  apply le_liminf_of_le (by isBoundedDefault)
  exact eventually_mul_le_euclideanClosedBallDensity_of_tangent_patches
    L hconv hE hw hk0
    (eventually_exists_supergraph_C1_tangent_patch hφ hφp hgraph
      hdensity hpK hk0 hk1)



/-- A horizontal regular trace has exactly coefficient-one Euclidean
`H¹` density.  This is an equality for every radius, not an upper estimate. -/
theorem hausdorffMeasure_horizontalLine_inter_closedBall_eq
    (x₀ y r : ℝ) :
    (μH[1] : Measure EuclideanPlane)
        (Set.range (euclideanGraphParam (fun _ : ℝ => y)) ∩
          Metric.closedBall (planeEuclideanHomeomorph (x₀, y)) r) =
      ENNReal.ofReal (2 * r) := by
  have hg : ContDiff ℝ 1 (fun _ : ℝ => y) := contDiff_const
  rw [hausdorffMeasure_euclideanGraph_inter_eq_setLIntegral hg
    measurableSet_closedBall]
  have hpre :
      euclideanGraphParam (fun _ : ℝ => y) ⁻¹'
          Metric.closedBall (planeEuclideanHomeomorph (x₀, y)) r =
        Icc (x₀ - r) (x₀ + r) := by
    ext x
    rw [mem_preimage, Metric.mem_closedBall, mem_Icc]
    change dist (planeEuclideanHomeomorph (x, y))
      (planeEuclideanHomeomorph (x₀, y)) ≤ r ↔ _
    rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
      WithLp.prod_dist_eq_of_L2]
    change Real.sqrt (dist x x₀ ^ 2 + dist y y ^ 2) ≤ r ↔ _
    rw [dist_self, zero_pow, add_zero, Real.sqrt_sq_eq_abs,
      abs_of_nonneg dist_nonneg, Real.dist_eq, abs_le]
    constructor
    · intro hx
      constructor <;> linarith [hx.1, hx.2]
    · rintro ⟨hx, hx'⟩
      constructor <;> linarith
    all_goals norm_num
  rw [hpre]
  simp only [deriv_const, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, Real.sqrt_one, ENNReal.ofReal_one]
  rw [setLIntegral_one, Real.volume_Icc]
  congr 1
  ring_nf

/-- Diameter normalization of the preceding exact horizontal-line identity. -/
theorem hausdorffMeasure_horizontalLine_closedBall_density_eq_one
    (x₀ y r : ℝ) (hr : 0 < r) :
    (μH[1] : Measure EuclideanPlane)
          (Set.range (euclideanGraphParam (fun _ : ℝ => y)) ∩
            Metric.closedBall (planeEuclideanHomeomorph (x₀, y)) r) /
        ENNReal.ofReal (2 * r) = 1 := by
  rw [hausdorffMeasure_horizontalLine_inter_closedBall_eq x₀ y r]
  exact ENNReal.div_self
    (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hr)).ne'
    ENNReal.ofReal_ne_top

/-- The same coefficient-one identity for an interior point of a finite
horizontal trace, provided the ball has not reached either endpoint. -/
theorem hausdorffMeasure_horizontalSegment_inter_closedBall_eq
    {left x₀ right y r : ℝ}
    (hrleft : r ≤ x₀ - left) (hrright : r ≤ right - x₀) :
    (μH[1] : Measure EuclideanPlane)
        (euclideanGraphParam (fun _ : ℝ => y) '' Icc left right ∩
          Metric.closedBall (planeEuclideanHomeomorph (x₀, y)) r) =
      ENNReal.ofReal (2 * r) := by
  have hset :
      euclideanGraphParam (fun _ : ℝ => y) '' Icc left right ∩
          Metric.closedBall (planeEuclideanHomeomorph (x₀, y)) r =
        Set.range (euclideanGraphParam (fun _ : ℝ => y)) ∩
          Metric.closedBall (planeEuclideanHomeomorph (x₀, y)) r := by
    apply Subset.antisymm
    · rintro z ⟨⟨x, hx, rfl⟩, hz⟩
      exact ⟨⟨x, rfl⟩, hz⟩
    · rintro z ⟨⟨x, rfl⟩, hxball⟩
      have hcoord := WithLp.dist_fst_le
        (planeEuclideanHomeomorph (x, y))
        (planeEuclideanHomeomorph (x₀, y))
      change dist x x₀ ≤
        dist (planeEuclideanHomeomorph (x, y))
          (planeEuclideanHomeomorph (x₀, y)) at hcoord
      have hxr : dist x x₀ ≤ r :=
        hcoord.trans (by
          simpa only [Metric.mem_closedBall, euclideanGraphParam] using hxball)
      rw [Real.dist_eq, abs_le] at hxr
      refine ⟨⟨x, ?_, rfl⟩, hxball⟩
      exact ⟨by linarith [hxr.1, hrleft], by linarith [hxr.2, hrright]⟩
  rw [hset]
  exact hausdorffMeasure_horizontalLine_inter_closedBall_eq x₀ y r


/-- For `lam ≥ 1`, the strip density is lower semicontinuous in the exact
pointwise form needed by a shrinking tangent patch.  At either closed
interface the retained value is therefore exactly one. -/
theorem eventually_stripDensity_point_le {lam : ℝ} (hlam : 1 ≤ lam)
    (p : PlanePoint) :
    ∀ᶠ q in 𝓝 p, StripDensity lam p ≤ StripDensity lam q := by
  by_cases hp : |p.2| ≤ 1
  · have hglobal : ∀ q : PlanePoint, 1 ≤ StripDensity lam q := by
      intro q
      simp only [StripDensity]
      split
      · exact le_rfl
      · exact hlam
    simpa only [StripDensity, if_pos hp] using Eventually.of_forall hglobal
  · have hpout : 1 < |p.2| := lt_of_not_ge hp
    have hnear : ∀ᶠ q : PlanePoint in 𝓝 p, 1 < |q.2| :=
      (continuous_abs.comp continuous_snd).continuousAt.eventually
        (Ioi_mem_nhds hpout)
    filter_upwards [hnear] with q hq
    simp only [StripDensity, if_neg hp, if_neg (not_le.mpr hq)]
    exact le_rfl

/-- Sharp weighted lower density using the strip weight at the boundary point
itself. -/
theorem sharp_lower_density_of_vertical_smooth_germ
    {lam : ℝ} (hlam : 1 ≤ lam)
    {A : SmoothSequence} {E K : Set PlanePoint} {p : PlanePoint}
    {side : SpliceGraphOccupiedSide}
    (L : Limit lam A K) (hconv : A.ConvergesTo E)
    (hE : MeasurableSet E)
    (germ : HasOrientedSmoothBoundaryGraphGermOnSide .vertical side E p)
    (hpK : p ∈ interior K) :
    ENNReal.ofReal (StripDensity lam p) ≤
      liminf (euclideanClosedBallDensity L p) (𝓝[>] (0 : ℝ)) := by
  apply sharp_lower_euclideanClosedBallDensity L hconv hE germ
    (eventually_stripDensity_point_le hlam p) hpK
  simp only [StripDensity]
  split
  · norm_num
  · exact zero_le_one.trans hlam

end CompactCoreEnergy
end CMVRelaxation

namespace CMVFigureFive
namespace SourceGeometry

/-- At an interior point of an exposed lower Figure-5 interface, the occupied
side is forced by the retained pointwise horizontal sections: it is the side
strictly above `y = -1`.  No occupied-side field is added to `SourceGeometry`. -/
theorem lowerExposed_eventually_mem_iff_above
    {lam : ℝ} (g : SourceGeometry lam)
    (b : ExposedInterface g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .exposed b)
    {x : ℝ} (hxleft : g.leftStripCenter.1 < x)
    (hxright : x < g.rightStripCenter.1) :
    ∀ᶠ q in 𝓝 ((x, -1) : PlanePoint),
      q ∈ g.representative ↔ -1 < q.2 := by
  have hxnear :
      ∀ᶠ q : PlanePoint in 𝓝 (x, -1),
        q.1 ∈ Ioo g.leftStripCenter.1 g.rightStripCenter.1 := by
    simpa using continuous_fst.continuousAt.eventually
      (Ioo_mem_nhds hxleft hxright)
  have hynear :
      ∀ᶠ q : PlanePoint in 𝓝 (x, -1), q.2 ∈ Ioo (-2 : ℝ) 0 := by
    simpa using continuous_snd.continuousAt.eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hxnear, hynear] with q hx hy
  constructor
  · intro hq
    by_contra hn
    have hle : q.2 ≤ -1 := le_of_not_gt hn
    rcases hle.eq_or_lt with heq | hlt
    · have hseg : q ∈ b.segment.carrier := by
        change q.2 = b.segment.baseY ∧
          b.segment.leftX ≤ q.1 ∧ q.1 ≤ b.segment.rightX
        constructor
        · rw [b.segment_base]
          simpa only [interfaceY] using heq
        · rw [b.segment_starts_at_left_tangency,
            b.segment_ends_at_right_tangency]
          exact ⟨hx.1.le, hx.2.le⟩
      have hfrontier : q ∈ frontier g.representative := by
        rw [g.frontier_eq_components]
        refine Or.inr (Or.inr (Or.inr ?_))
        rw [hBoundary]
        exact hseg
      have hcontra : q ∈ g.representative ∩ frontier g.representative :=
        ⟨hq, hfrontier⟩
      rw [g.sourceRepresentative.representative_open.inter_frontier_eq] at hcontra
      exact hcontra
    · have hsection :=
        g.actual_lowerExposedSection_empty b hBoundary hlt
      have hmem :
          q.1 ∈ CMVSourceClassification.horizontalSection
            g.representative q.2 := by
        simpa [CMVSourceClassification.horizontalSection] using hq
      rw [hsection] at hmem
      exact hmem
  · intro hqy
    have habs : |q.2| < 1 := abs_lt.mpr ⟨hqy, by linarith [hy.2]⟩
    change q.1 ∈ CMVSourceClassification.horizontalSection
      g.representative q.2
    rw [g.actual_strictStripSection habs]
    constructor
    · unfold leftStripBoundaryPoint
      dsimp only
      exact (sub_le_self _ (Real.sqrt_nonneg _)).trans_lt hx.1
    · unfold rightStripBoundaryPoint
      dsimp only
      exact hx.2.trans_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))

/-- The retained exposed-lower section data yields a genuine smooth
positive-side graph germ at every nonjunction point of the segment. -/
theorem lowerExposed_orientedSmoothGraphGerm
    {lam : ℝ} (g : SourceGeometry lam)
    (b : ExposedInterface g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .exposed b)
    {x : ℝ} (hxleft : g.leftStripCenter.1 < x)
    (hxright : x < g.rightStripCenter.1) :
    CMVRelaxation.FiniteJunctionRepair.HasOrientedSmoothBoundaryGraphGermOnSide
      .vertical .positive g.representative (x, -1) := by
  let defining : PlanePoint → ℝ := fun q => -q.2 - 1
  let graph : ℝ → ℝ := fun _ => -1
  have hdefining :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) defining := by
    dsimp only [defining]
    fun_prop
  have hderiv :
      fderiv ℝ defining (x, -1) (0, 1) = -1 := by
    have h : HasFDerivAt (fun q : PlanePoint => -q.2 - 1)
        (-(ContinuousLinearMap.snd ℝ ℝ ℝ)) (x, -1) := by
      fun_prop
    dsimp only [defining]
    rw [h.fderiv]
    norm_num
  refine ⟨defining, graph, hdefining.contDiffAt, ?_,
    contDiff_const, rfl, ?_, ?_⟩
  · rw [hderiv]
    norm_num
  · filter_upwards [
      g.lowerExposed_eventually_mem_iff_above b hBoundary hxleft hxright]
      with q hq
    constructor
    · constructor <;> intro h
      · dsimp only [defining]
        linarith [hq.mp h]
      · apply hq.mpr
        dsimp only [defining] at h
        linarith
    · dsimp only [defining, graph]
      constructor <;> intro h <;> linarith
  · rw [hderiv]
    norm_num

/-- Existing circle-side data on a capped upper interface exposes the genuine
smooth graph germ needed by tangent density, rather than only a continuous
chart, whenever the vertical graph orientation is regular. -/
theorem upperCapped_exists_verticalOrientedSmoothGraphGerm
    {lam : ℝ} (g : SourceGeometry lam)
    (b : CappedInterface lam g.sourceRadius
      g.leftStripCenter.1 g.rightStripCenter.1 .upper)
    (hBoundary : g.upperBoundary = .capped b)
    {p : PlanePoint} (hp : p ∈ b.cap.arcTrace)
    (hleft : p ≠ b.cap.leftEndpoint) (hright : p ≠ b.cap.rightEndpoint)
    (hy : p.2 ≠ b.cap.center.2) :
    ∃ side : CMVRelaxation.FiniteJunctionRepair.SpliceGraphOccupiedSide,
      CMVRelaxation.FiniteJunctionRepair.HasOrientedSmoothBoundaryGraphGermOnSide
        .vertical side g.representative p := by
  have hcircle :
      CMVFigureFour.circleValue b.cap.center g.sourceRadius p = 0 := by
    change b.cap.radiusSquaredAt p - g.sourceRadius ^ 2 = 0
    rw [hp.1]
    exact sub_eq_zero.mpr (congrArg (fun z : ℝ => z ^ 2) b.cap_radius)
  have hlocal :
      CMVFigureFour.LocallyOneSided g.representative
        b.cap.center g.sourceRadius p := by
    have h := g.upper_cap_one_sided
    rw [hBoundary] at h
    exact h p hp hleft hright
  exact exists_verticalOrientedSmoothGraphGerm_of_locallyOneSided_circle
    hcircle hy hlocal


/-- The lower exposed Figure-5 segment exercises the sharp limit theorem with
the closed-interface weight `w = 1`. -/
theorem lowerExposed_sharp_limitDensity
    {lam : ℝ} (g : SourceGeometry lam)
    (b : ExposedInterface g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    (hBoundary : g.lowerBoundary = .exposed b)
    {x : ℝ} (hxleft : g.leftStripCenter.1 < x)
    (hxright : x < g.rightStripCenter.1)
    {A : CMVRelaxation.SmoothSequence} {K : Set PlanePoint}
    (L : CMVRelaxation.CompactCoreEnergy.Limit lam A K)
    (hconv : A.ConvergesTo g.representative)
    (hpK : (x, -1) ∈ interior K) :
    (1 : ℝ≥0∞) ≤
      liminf
        (CMVRelaxation.CompactCoreEnergy.euclideanClosedBallDensity
          L (x, -1)) (𝓝[>] (0 : ℝ)) := by
  have hsharp :=
    CMVRelaxation.CompactCoreEnergy.sharp_lower_density_of_vertical_smooth_germ
      g.density_jump.le L hconv
      g.sourceRepresentative.representative_open.measurableSet
      (g.lowerExposed_orientedSmoothGraphGerm b hBoundary hxleft hxright)
      hpK
  simpa only [stripDensity_lower_interface, ENNReal.ofReal_one] using hsharp

/-- Exact coefficient-one Euclidean `H¹` density on the same exposed segment,
away from its two junction endpoints. -/
theorem lowerExposed_euclideanH1_inter_closedBall_eq
    {lam : ℝ} (g : SourceGeometry lam)
    (b : ExposedInterface g.leftStripCenter.1 g.rightStripCenter.1 .lower)
    {x r : ℝ}
    (hrleft : r ≤ x - g.leftStripCenter.1)
    (hrright : r ≤ g.rightStripCenter.1 - x) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' b.segment.carrier ∩
          Metric.closedBall (planeEuclideanHomeomorph (x, -1)) r) =
      ENNReal.ofReal (2 * r) := by
  have hcarrier :
      b.segment.carrier =
        (fun t : ℝ => (t, (-1 : ℝ))) ''
          Icc g.leftStripCenter.1 g.rightStripCenter.1 := by
    ext q
    constructor
    · intro hq
      refine ⟨q.1, ?_, ?_⟩
      · rw [mem_Icc]
        constructor
        · exact b.segment_starts_at_left_tangency ▸ hq.2.1
        · exact b.segment_ends_at_right_tangency ▸ hq.2.2
      · apply Prod.ext
        · rfl
        · rw [hq.1, b.segment_base]
          simp only [interfaceY]
    · rintro ⟨t, ht, rfl⟩
      change (-1 : ℝ) = b.segment.baseY ∧
        b.segment.leftX ≤ t ∧ t ≤ b.segment.rightX
      constructor
      · rw [b.segment_base]
        simp only [interfaceY]
      · constructor
        · exact b.segment_starts_at_left_tangency.symm ▸ ht.1
        · exact b.segment_ends_at_right_tangency.symm ▸ ht.2
  rw [hcarrier, Set.image_image]
  exact CMVRelaxation.CompactCoreEnergy.hausdorffMeasure_horizontalSegment_inter_closedBall_eq
      hrleft hrright

end SourceGeometry
end CMVFigureFive
