/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import Mathlib

/-!
# Local graph flux through a triangular shear

This module isolates the first, purely Euclidean part of the CMV graph-flux
argument.  The auxiliary bottom of the rectangle is derived from compact
support and compactness of the graph; it is not supplied as a face-vanishing
hypothesis.
-/

open Set Filter MeasureTheory Metric
open scoped Topology

noncomputable section

namespace CMVShearGraphFlux

abbrev Plane := ℝ × ℝ

/-- The unit-Jacobian triangular shear that flattens the graph of `g`. -/
def shear (g : ℝ → ℝ) (p : Plane) : Plane :=
  (p.1, p.2 + g p.1)

/-- Horizontal component after triangular shear. -/
def pulledHorizontal (g : ℝ → ℝ) (F₁ : Plane → ℝ) (p : Plane) : ℝ :=
  F₁ (shear g p)

/-- Vertical component after triangular shear, including the slope correction. -/
def pulledVertical (g : ℝ → ℝ) (F₁ F₂ : Plane → ℝ) (p : Plane) : ℝ :=
  F₂ (shear g p) - deriv g p.1 * F₁ (shear g p)

@[simp] theorem shear_apply (g : ℝ → ℝ) (x t : ℝ) :
    shear g (x, t) = (x, t + g x) := rfl

/-- Chain rule in the horizontal direction of the triangular shear. -/
theorem hasDerivAt_pulledHorizontal_first
    {g : ℝ → ℝ} {F₁ : Plane → ℝ} {D₁ : Plane →L[ℝ] ℝ}
    {x t g' : ℝ} (hg : HasDerivAt g g' x)
    (hF₁ : HasFDerivAt F₁ D₁ (x, t + g x)) :
    HasDerivAt (fun u => pulledHorizontal g F₁ (u, t))
      (D₁ (1, g')) x := by
  have hpath : HasDerivAt (fun u : ℝ => (u, t + g u)) (1, g') x := by
    convert (hasDerivAt_id x).prodMk ((hasDerivAt_const x t).add hg) using 1 <;>
      simp
  simpa [pulledHorizontal, shear, Function.comp_def] using
    hF₁.comp_hasDerivAt x hpath

/-- Chain rule in the vertical direction of the triangular shear. -/
theorem hasDerivAt_pulledHorizontal_second
    {g : ℝ → ℝ} {F₁ : Plane → ℝ} {D₁ : Plane →L[ℝ] ℝ}
    {x t : ℝ} (hF₁ : HasFDerivAt F₁ D₁ (x, t + g x)) :
    HasDerivAt (fun v => pulledHorizontal g F₁ (x, v))
      (D₁ (0, 1)) t := by
  have hpath : HasDerivAt (fun v : ℝ => (x, v + g x)) (0, 1) t := by
    convert (hasDerivAt_const t x).prodMk
      ((hasDerivAt_id t).add_const (g x)) using 1 <;> simp
  simpa [pulledHorizontal, shear, Function.comp_def] using
    hF₁.comp_hasDerivAt t hpath

/-- The corrected vertical component has the expected vertical derivative. -/
theorem deriv_pulledVertical_second
    {g : ℝ → ℝ} {F₁ F₂ : Plane → ℝ}
    {D₁ D₂ : Plane →L[ℝ] ℝ} {x t : ℝ}
    (hF₁ : HasFDerivAt F₁ D₁ (x, t + g x))
    (hF₂ : HasFDerivAt F₂ D₂ (x, t + g x)) :
    deriv (fun v => pulledVertical g F₁ F₂ (x, v)) t =
      D₂ (0, 1) - deriv g x * D₁ (0, 1) := by
  have h₂ := hasDerivAt_pulledHorizontal_second (g := g) hF₂
  have h₁ := hasDerivAt_pulledHorizontal_second (g := g) hF₁
  have hmul := h₁.const_mul (deriv g x)
  have heq :
      (fun v => pulledVertical g F₁ F₂ (x, v)) =
        (fun v => pulledHorizontal g F₂ (x, v) -
          deriv g x * pulledHorizontal g F₁ (x, v)) := rfl
  rw [heq]
  exact (h₂.sub hmul).deriv

/-- Exact diagonal-derivative cancellation for the triangular shear.

The term created by differentiating `F₁ (x, t + g x)` in `x` is cancelled by
`-g'(x) F₁` in the transformed vertical component. -/
theorem triangularShear_derivative_cancellation
    {g : ℝ → ℝ} {F₁ F₂ : Plane → ℝ}
    {D₁ D₂ : Plane →L[ℝ] ℝ} {x t : ℝ}
    (hg : HasDerivAt g (deriv g x) x)
    (hF₁ : HasFDerivAt F₁ D₁ (x, t + g x))
    (hF₂ : HasFDerivAt F₂ D₂ (x, t + g x)) :
    deriv (fun u => pulledHorizontal g F₁ (u, t)) x +
        deriv (fun v => pulledVertical g F₁ F₂ (x, v)) t =
      D₁ (1, 0) + D₂ (0, 1) := by
  rw [(hasDerivAt_pulledHorizontal_first hg hF₁).deriv,
    deriv_pulledVertical_second hF₁ hF₂]
  have hDsplit :
      D₁ (1, deriv g x) =
        D₁ (1, 0) + deriv g x * D₁ (0, 1) := by
    calc
      D₁ (1, deriv g x) =
          D₁ (((1 : ℝ), 0) + deriv g x • ((0 : ℝ), 1)) := by
            congr 1
            ext <;> simp
      _ = D₁ (1, 0) + deriv g x * D₁ (0, 1) := by
        rw [map_add, map_smul]
        simp
  rw [hDsplit]
  ring

/-- `C²` graph data and a `C¹` field make both transformed components `C¹`.
The extra graph derivative is exactly why the rectangular divergence theorem
requires one more graph derivative than the final diagonal identity does. -/
theorem contDiff_pulled_components
    {g : ℝ → ℝ} {F₁ F₂ : Plane → ℝ}
    (hg : ContDiff ℝ 2 g) (hF₁ : ContDiff ℝ 1 F₁)
    (hF₂ : ContDiff ℝ 1 F₂) :
    ContDiff ℝ 1 (pulledHorizontal g F₁) ∧
      ContDiff ℝ 1 (pulledVertical g F₁ F₂) := by
  have hg₁ : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hshear : ContDiff ℝ 1 (shear g) := by
    unfold shear
    exact contDiff_fst.prodMk
      (contDiff_snd.add (hg₁.comp contDiff_fst))
  have hhorizontal : ContDiff ℝ 1 (pulledHorizontal g F₁) := by
    change ContDiff ℝ 1 (F₁ ∘ shear g)
    exact hF₁.comp hshear
  refine ⟨hhorizontal, ?_⟩
  have hvertical : ContDiff ℝ 1 (F₂ ∘ shear g) :=
    hF₂.comp hshear
  have hg₂ : ContDiff ℝ (1 + 1) g := by
    convert hg using 1 <;> norm_num
  have hgderiv : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp hg₂).2.2
  have hderiv : ContDiff ℝ 1
      (deriv g ∘ (fun p : Plane => p.1)) :=
    hgderiv.comp contDiff_fst
  change ContDiff ℝ 1
    ((F₂ ∘ shear g) -
      (deriv g ∘ (fun p : Plane => p.1)) * (F₁ ∘ shear g))
  exact hvertical.sub (hderiv.mul (hF₁.comp hshear))

/-- Exact support contract for a graph rectangle.  Only the horizontal room is
part of the contract.  The auxiliary lower face is derived below from compact
support and compactness of the graph. -/
structure RectangleSupport (g : ℝ → ℝ) (F : Plane → Plane)
    (a b : ℝ) : Prop where
  left_lt_right : a < b
  graph_continuous : ContinuousOn g (Icc a b)
  field_compact : HasCompactSupport F
  support_horizontal : tsupport F ⊆ Ioo a b ×ˢ (univ : Set ℝ)

/-- A compact field support and a compact graph admit one common, strictly
lower auxiliary depth. -/
theorem exists_auxiliaryDepth
    {K : Set Plane} (hK : IsCompact K) {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    ∃ c : ℝ, (∀ p ∈ K, c < p.2) ∧ (∀ x ∈ Icc a b, c < g x) := by
  let graph : Set Plane := (fun x : ℝ => (x, g x)) '' Icc a b
  have hgraph : IsCompact graph :=
    isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hg)
  have hcompact : IsCompact (K ∪ graph) := hK.union hgraph
  obtain ⟨r, hr, hbound⟩ :=
    hcompact.isBounded.subset_closedBall_lt 0 (0 : Plane)
  refine ⟨-r - 1, ?_, ?_⟩
  · intro p hp
    have hpball := hbound (Or.inl hp)
    have hpnorm : ‖p‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using hpball
    have hpcoord : |p.2| ≤ r := by
      simpa only [Real.norm_eq_abs] using (norm_snd_le p).trans hpnorm
    nlinarith [neg_le_abs p.2]
  · intro x hx
    have hpball := hbound (Or.inr ⟨x, hx, rfl⟩)
    have hpnorm : ‖(x, g x)‖ ≤ r := by
      simpa only [mem_closedBall, dist_zero_right] using hpball
    have hpcoord : |g x| ≤ r := by
      simpa only [Real.norm_eq_abs] using
        (norm_snd_le (x, g x)).trans hpnorm
    nlinarith [neg_le_abs (g x)]

/-- The support contract produces a common auxiliary depth; no bottom-face
vanishing data is accepted from the caller. -/
theorem RectangleSupport.exists_auxiliaryDepth
    {g : ℝ → ℝ} {F : Plane → Plane} {a b : ℝ}
    (h : RectangleSupport g F a b) :
    ∃ c : ℝ,
      (∀ p ∈ tsupport F, c < p.2) ∧
      (∀ x ∈ Icc a b, c < g x) :=
  CMVShearGraphFlux.exists_auxiliaryDepth h.field_compact h.graph_continuous

/-- Below the derived depth, the complete vector field vanishes.  This is the
bottom artificial-face cancellation used by the forthcoming rectangle proof. -/
theorem field_eq_zero_below_auxiliaryDepth
    {F : Plane → Plane} {c x y : ℝ}
    (hdepth : ∀ p ∈ tsupport F, c < p.2) (hy : y ≤ c) :
    F (x, y) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_lt_of_ge hy) (hdepth (x, y) hmem)

end CMVShearGraphFlux
