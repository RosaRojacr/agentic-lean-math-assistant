/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import SameCurvatureArea
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Equal-area envelope reduction

This bounded module isolates the real-calculus step which promotes negativity at
the stationary type-(iv) fold to negativity at every modeled type-(iv)
curvature.  It deliberately does not mention certificate cells or geometric
realization.

The theorem is stated for an explicitly selected descending equal-area root.
Root existence, equal area, and the negative type-(iii) fold sign are the
independent analytic interfaces.  Compact branch trapping derives continuity,
including the one-sided closure endpoint.  Strict root order, all-root
classification, simple-root nonvanishing, interior root differentiability,
the envelope derivative identity, and the sign change of the actual type-(iv)
area derivative are also derived rather than assumed.
-/

open Real Set Filter
open scoped Topology

noncomputable section

namespace LeanSuffixAnalytic

/-- The genuine modeled perimeter gap along a selected equal-area root. -/
def equalAreaPerimeterGap (lam : ℝ) (root : ℝ → ℝ) (h₄ : ℝ) : ℝ :=
  typeThreePerimeter lam (root h₄) - typeFourPerimeter lam h₄

/-- A function selected as the unique zero in a compact branch is continuous.
Compactness is used only for the branch: the zero graph is closed, and its
projection along the compact factor is closed. -/
private theorem continuous_of_compact_unique_eq
    {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace Z] [T2Space Z]
    {F : X → Y → Z} {root : X → Y} {z : Z}
    (hF : Continuous (fun p : X × Y => F p.1 p.2))
    (hroot : ∀ x, F x (root x) = z)
    (hunique : ∀ x y, F x y = z → y = root x) :
    Continuous root := by
  rw [continuous_iff_isClosed]
  intro C hC
  let G : Set (X × Y) := {p | F p.1 p.2 = z}
  have hG : IsClosed G := isClosed_singleton.preimage hF
  have hpreimage : root ⁻¹' C = Prod.fst '' (G ∩ Prod.snd ⁻¹' C) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, root x), ⟨hroot x, hx⟩, rfl⟩
    · rintro ⟨p, ⟨hpzero, hpC⟩, rfl⟩
      change p.2 ∈ C at hpC
      change root p.1 ∈ C
      rw [← hunique p.1 p.2 hpzero]
      exact hpC
  rw [hpreimage]
  exact isClosedMap_fst_of_compactSpace _
    (hG.inter (hC.preimage continuous_snd))

/-- A selected regular equal-area root contained in a compact branch is
continuous provided it is the unique equal-area point of that branch.  The
source may include the closure endpoint `h = 1`; only the selected type-(iii)
root interval must remain regular. -/
theorem equalAreaRoot_continuousOn_of_compact_unique
    {lam : ℝ} {s K : Set ℝ} {root : ℝ → ℝ}
    (hlam : 1 < lam)
    (hK : IsCompact K)
    (hs_domain : s ⊆ Ioc 0 1)
    (hK_regular : K ⊆ Ioo 0 1)
    (hroot_mem : MapsTo root s K)
    (hequalArea : ∀ h ∈ s,
      typeThreeArea lam (root h) = typeFourArea lam h)
    (hunique : ∀ h ∈ s, ∀ y ∈ K,
      typeThreeArea lam y = typeFourArea lam h → y = root h) :
    ContinuousOn root s := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : s → K := hroot_mem.restrict root s K
  have hA3 : ContinuousOn (typeThreeArea lam) K := by
    intro y hy
    exact (typeThree_variational_hasDerivAt hlam
      (hK_regular hy).1 (hK_regular hy).2).1.continuousAt.continuousWithinAt
  have hA4 : ContinuousOn (typeFourArea lam) s := by
    intro h hh
    have hh0 : h ≠ 0 := ne_of_gt (hs_domain hh).1
    unfold typeFourArea typeFourAngle typeFourDelta
    fun_prop (disch := simp_all)
  have hr : Continuous r := continuous_of_compact_unique_eq
    (F := fun h : s => fun y : K =>
      typeThreeArea lam y - typeFourArea lam h)
    (z := 0)
    ((hA3.domRestrict.comp continuous_snd).sub
      (hA4.domRestrict.comp continuous_fst))
    (fun h => sub_eq_zero.mpr (hequalArea h h.property))
    (fun h y hy => Subtype.ext
      (hunique h h.property y y.property (sub_eq_zero.mp hy)))
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_subtype_val.comp hr

/-- The type-(iii) area is strictly decreasing on a compact regular interval
when its derivative is negative throughout the interval's interior. -/
theorem typeThreeArea_strictAntiOn_Icc
    {lam a b : ℝ}
    (hlam : 1 < lam) (ha : 0 < a) (hb : b < 1)
    (hderiv : ∀ y ∈ Ioo a b,
      deriv (typeThreeArea lam) y < 0) :
    StrictAntiOn (typeThreeArea lam) (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b)
  · intro y hy
    exact (typeThree_variational_hasDerivAt hlam
      (ha.trans_le hy.1) (hy.2.trans_lt hb)).1.continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact hderiv y hy

/-- A negative fold at the right endpoint forces strict decrease of the
type-(iii) area on the entire preceding regular interval. -/
theorem typeThreeArea_strictAntiOn_Icc_of_fold_neg_right
    {lam a b : ℝ} (hlam : 1 < lam) (ha : 0 < a) (hb : b < 1)
    (hb_pos : 0 < b) (hfoldb : typeThreeFold lam b < 0) :
    StrictAntiOn (typeThreeArea lam) (Icc a b) := by
  apply typeThreeArea_strictAntiOn_Icc hlam ha hb
  intro y hy
  rw [(hasDerivAt_typeThreeArea hlam
    (ha.trans hy.1) (hy.2.trans hb)).deriv]
  apply div_neg_of_neg_of_pos _ (pow_pos (ha.trans hy.1) 3)
  exact (typeThreeFold_strictMonoOn hlam
    ⟨ha.trans hy.1, hy.2.trans hb⟩ ⟨hb_pos, hb⟩ hy.2).trans hfoldb

/-- Certificate-facing specialization for a root contained in a compact
curvature interval.  Uniform derivative negativity supplies both uniqueness
and continuity of the selected equal-area branch. -/
theorem equalAreaRoot_continuousOn_of_Icc_deriv_neg
    {lam a b : ℝ} {s : Set ℝ} {root : ℝ → ℝ}
    (hlam : 1 < lam)
    (hs_regular : s ⊆ Ioo 0 1)
    (ha : 0 < a) (hb : b < 1)
    (hroot_mem : MapsTo root s (Icc a b))
    (hequalArea : ∀ h ∈ s,
      typeThreeArea lam (root h) = typeFourArea lam h)
    (hderiv : ∀ y ∈ Ioo a b,
      deriv (typeThreeArea lam) y < 0) :
    ContinuousOn root s := by
  have hanti := typeThreeArea_strictAntiOn_Icc hlam ha hb hderiv
  exact equalAreaRoot_continuousOn_of_compact_unique
    hlam isCompact_Icc
    (fun h hh => ⟨(hs_regular hh).1, (hs_regular hh).2.le⟩)
    (fun _ hy => ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩)
    hroot_mem hequalArea
    (fun h hh y hy heq =>
      hanti.injOn hy (hroot_mem hh)
        (heq.trans (hequalArea h hh).symm))


/-- A continuous simple equal-area root is differentiable.  This is the
certificate-facing converse to the chain rule: interval arguments need only
establish continuity of the selected branch and nonvanishing of the
type-(iii) area derivative. -/
theorem equalAreaRoot_hasDerivAt
    {lam h : ℝ} {root : ℝ → ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1)
    (hroot_pos : 0 < root h) (hroot_lt_one : root h < 1)
    (hroot_continuous : ContinuousAt root h)
    (hareaThree_ne : deriv (typeThreeArea lam) (root h) ≠ 0)
    (hequalArea : ∀ ⦃x : ℝ⦄, 0 < x → x ≤ 1 →
      typeThreeArea lam (root x) = typeFourArea lam x) :
    HasDerivAt root
      (deriv (typeFourArea lam) h /
        deriv (typeThreeArea lam) (root h)) h := by
  have hareaThree :=
    (typeThree_variational_hasDerivAt hlam hroot_pos hroot_lt_one).1
  have hareaFour := (typeFour_variational_hasDerivAt hlam hh hh1).1
  apply hareaThree.of_comp_left hroot_continuous hareaFour hareaThree_ne
  filter_upwards [Ioo_mem_nhds hh hh1] with x hx
  exact hequalArea hx.1 hx.2.le
/-- Differentiating the equal-area constraint and applying the exact
type-(iii) and type-(iv) variational identities gives the envelope identity. -/
theorem equalAreaPerimeterGap_hasDerivAt
    {lam h : ℝ} {root : ℝ → ℝ}
    (hlam : 1 < lam) (hh : 0 < h) (hh1 : h < 1)
    (hroot_pos : 0 < root h) (hroot_lt_one : root h < 1)
    (hroot_differentiable : DifferentiableAt ℝ root h)
    (hequalArea : ∀ ⦃x : ℝ⦄, 0 < x → x ≤ 1 →
      typeThreeArea lam (root x) = typeFourArea lam x) :
    HasDerivAt (equalAreaPerimeterGap lam root)
      ((root h - h) * deriv (typeFourArea lam) h) h := by
  rcases typeThree_variational_hasDerivAt hlam hroot_pos hroot_lt_one with
    ⟨hareaThree, hperimeterThree⟩
  rcases typeFour_variational_hasDerivAt hlam hh hh1 with
    ⟨hareaFour, hperimeterFour⟩
  have hroot := hroot_differentiable.hasDerivAt
  have harea_comp := hareaThree.comp h hroot
  have hequalArea_eventually :
      (typeThreeArea lam ∘ root) =ᶠ[nhds h] typeFourArea lam := by
    filter_upwards [Ioo_mem_nhds hh hh1] with x hx
    exact hequalArea hx.1 hx.2.le
  have harea_comp_from_equalArea :
      HasDerivAt (typeThreeArea lam ∘ root)
        (deriv (typeFourArea lam) h) h :=
    hareaFour.congr_of_eventuallyEq hequalArea_eventually
  have hchain :
      deriv (typeThreeArea lam) (root h) * deriv root h =
        deriv (typeFourArea lam) h :=
    harea_comp.unique harea_comp_from_equalArea
  have hgap :=
    (hperimeterThree.comp h hroot).sub hperimeterFour
  have hgap' : HasDerivAt
      (typeThreePerimeter lam ∘ root - typeFourPerimeter lam)
      ((root h - h) * deriv (typeFourArea lam) h) h :=
    hgap.congr_deriv (by
      rw [mul_assoc, hchain]
      ring)
  apply hgap'.congr_of_eventuallyEq
  filter_upwards
  intro x
  rfl

/-- The canonical descending equal-area root selected from one certified
stationary pair.  Values outside `0 < h₄ ≤ 1` are deliberately irrelevant. -/
noncomputable def StationaryEqualAreaPair.descendingRoot {lam : ℝ}
    (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0) :
    ℝ → ℝ := fun h₄ =>
  if hh₄ : h₄ ∈ Ioc (0 : ℝ) 1 then
    Classical.choose
      (typeThreeArea_descending_root_existsUnique_of_stationary_pair
        hlam ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
        ⟨pair.h₄_pos, pair.h₄_lt_one⟩ hh₄ hfoldThree
        pair.stationary pair.equalArea)
  else 0

/-- The selected root is regular, equal-area, and on the negative-fold branch. -/
theorem StationaryEqualAreaPair.descendingRoot_spec {lam : ℝ}
    (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0)
    {h₄ : ℝ} (hh₄ : h₄ ∈ Ioc (0 : ℝ) 1) :
    pair.descendingRoot hlam hfoldThree h₄ ∈ Ioo (0 : ℝ) 1 ∧
      typeThreeArea lam (pair.descendingRoot hlam hfoldThree h₄) =
        typeFourArea lam h₄ ∧
      typeThreeFold lam (pair.descendingRoot hlam hfoldThree h₄) < 0 := by
  rw [StationaryEqualAreaPair.descendingRoot, dif_pos hh₄]
  exact (Classical.choose_spec
    (typeThreeArea_descending_root_existsUnique_of_stationary_pair
      hlam ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
      ⟨pair.h₄_pos, pair.h₄_lt_one⟩ hh₄ hfoldThree
      pair.stationary pair.equalArea)).1

/-- At the stationary curvature, the canonical root is the certified
type-(iii) member of the pair. -/
theorem StationaryEqualAreaPair.descendingRoot_at_stationary {lam : ℝ}
    (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0) :
    pair.descendingRoot hlam hfoldThree pair.h₄ = pair.h₃ := by
  let hexists :=
    typeThreeArea_descending_root_existsUnique_of_stationary_pair
      hlam ⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩
      ⟨pair.h₄_pos, pair.h₄_lt_one⟩
      (show pair.h₄ ∈ Ioc (0 : ℝ) 1 from
        ⟨pair.h₄_pos, pair.h₄_lt_one.le⟩)
      hfoldThree pair.stationary pair.equalArea
  rw [StationaryEqualAreaPair.descendingRoot,
    dif_pos (show pair.h₄ ∈ Ioc (0 : ℝ) 1 from
      ⟨pair.h₄_pos, pair.h₄_lt_one.le⟩)]
  exact ((Classical.choose_spec hexists).2 pair.h₃
    ⟨⟨lt_trans (by norm_num) pair.h₃_gt_half, pair.h₃_lt_one⟩,
      pair.equalArea, hfoldThree⟩).symm

/-- Minimal, explicit analytic interfaces for the descending equal-area
branch.  The negative fold sign proves global descending-root identification,
compact branch trapping, continuity through the one-sided closure endpoint,
and the simple-root condition.  The same-curvature area comparison proves the
strict root order. -/
structure DescendingEqualAreaEnvelope (lam : ℝ) where
  /-- The unique type-(iv) fold selected by the retained fold-gap statement. -/
  fold : ℝ
  /-- The descending type-(iii) equal-area root for every modeled curvature. -/
  root : ℝ → ℝ
  density_jump : 1 < lam
  fold_pos : 0 < fold
  fold_lt_one : fold < 1
  fold_stationary : typeFourFold lam fold = 0
  root_pos : ∀ ⦃h₄ : ℝ⦄, 0 < h₄ → h₄ ≤ 1 → 0 < root h₄
  root_lt_one : ∀ ⦃h₄ : ℝ⦄, 0 < h₄ → h₄ ≤ 1 → root h₄ < 1
  equalArea : ∀ ⦃h₄ : ℝ⦄, 0 < h₄ → h₄ ≤ 1 →
    typeThreeArea lam (root h₄) = typeFourArea lam h₄
  /-- Every selected type-(iii) root lies on the strictly descending branch.
  This identifies it globally as the least equal-area root and implies the
  simple-root condition used by the inverse-function argument. -/
  root_fold_neg : ∀ ⦃h₄ : ℝ⦄, 0 < h₄ → h₄ ≤ 1 →
    typeThreeFold lam (root h₄) < 0

/-- Every selected descending root is bounded above by the root at the
stationary type-(iv) fold.  This fixed regular anchor supplies the compactness
needed for branch continuity. -/
theorem DescendingEqualAreaEnvelope.root_le_foldRoot {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    env.root h₄ ≤ env.root env.fold := by
  have harea_le :
      typeThreeArea lam (env.root env.fold) ≤
        typeThreeArea lam (env.root h₄) := by
    rw [env.equalArea env.fold_pos env.fold_lt_one.le,
      env.equalArea hh₄ hh₄_one]
    exact typeFourArea_fold_le env.density_jump
      ⟨env.fold_pos, env.fold_lt_one⟩ env.fold_stationary ⟨hh₄, hh₄_one⟩
  apply le_of_not_gt
  intro hlt
  have hanti := typeThreeArea_strictAntiOn_Icc_of_fold_neg_right
    env.density_jump
    (env.root_pos env.fold_pos env.fold_lt_one.le)
    (env.root_lt_one hh₄ hh₄_one)
    (env.root_pos hh₄ hh₄_one)
    (env.root_fold_neg hh₄ hh₄_one)
  exact (not_lt_of_ge harea_le)
    (hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt)

/-- Equal area and the negative-fold branch trap the selected root locally in
a compact interval.  Closed-graph uniqueness then gives continuity on the
whole modeled domain, including one-sided continuity at `h₄ = 1`. -/
theorem DescendingEqualAreaEnvelope.root_continuousOn {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) :
    ContinuousOn env.root (Ioc (0 : ℝ) 1) := by
  intro h₀ hh₀
  let r₀ := env.root h₀
  let anchor := env.root env.fold
  let a := r₀ / 2
  let K := Icc a anchor
  let s := Ioc (0 : ℝ) 1 ∩
    {h | typeFourArea lam h < typeThreeArea lam a}
  have hr₀_pos : 0 < r₀ := env.root_pos hh₀.1 hh₀.2
  have hr₀_lt_one : r₀ < 1 := env.root_lt_one hh₀.1 hh₀.2
  have hr₀_fold : typeThreeFold lam r₀ < 0 :=
    env.root_fold_neg hh₀.1 hh₀.2
  have hanchor_pos : 0 < anchor :=
    env.root_pos env.fold_pos env.fold_lt_one.le
  have hanchor_lt_one : anchor < 1 :=
    env.root_lt_one env.fold_pos env.fold_lt_one.le
  have hanchor_fold : typeThreeFold lam anchor < 0 :=
    env.root_fold_neg env.fold_pos env.fold_lt_one.le
  have hr₀_le_anchor : r₀ ≤ anchor :=
    env.root_le_foldRoot hh₀.1 hh₀.2
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have ha_lt_r₀ : a < r₀ := by
    dsimp [a]
    linarith
  have ha_lt_one : a < 1 := ha_lt_r₀.trans hr₀_lt_one
  have hfolda : typeThreeFold lam a < 0 :=
    (typeThreeFold_strictMonoOn env.density_jump
      ⟨ha_pos, ha_lt_one⟩ ⟨hr₀_pos, hr₀_lt_one⟩ ha_lt_r₀).trans hr₀_fold
  have hantiK : StrictAntiOn (typeThreeArea lam) K :=
    typeThreeArea_strictAntiOn_Icc_of_fold_neg_right
      env.density_jump ha_pos hanchor_lt_one hanchor_pos hanchor_fold
  have hr₀a : typeThreeArea lam r₀ < typeThreeArea lam a := by
    have hanti := typeThreeArea_strictAntiOn_Icc_of_fold_neg_right
      env.density_jump ha_pos hr₀_lt_one hr₀_pos hr₀_fold
    exact hanti ⟨le_rfl, ha_lt_r₀.le⟩
      ⟨ha_lt_r₀.le, le_rfl⟩ ha_lt_r₀
  have hroot_mem : MapsTo env.root s K := by
    intro h hh
    have hroot_pos := env.root_pos hh.1.1 hh.1.2
    have hroot_lt_one := env.root_lt_one hh.1.1 hh.1.2
    refine ⟨?_, env.root_le_foldRoot hh.1.1 hh.1.2⟩
    apply le_of_not_gt
    intro hra
    have hanti := typeThreeArea_strictAntiOn_Icc_of_fold_neg_right
      env.density_jump hroot_pos ha_lt_one ha_pos hfolda
    have hlt := hanti ⟨le_rfl, hra.le⟩
      ⟨hra.le, le_rfl⟩ hra
    rw [env.equalArea hh.1.1 hh.1.2] at hlt
    exact (not_lt_of_ge hh.2.le) hlt
  have hs_domain : s ⊆ Ioc (0 : ℝ) 1 := fun _ hh => hh.1
  have ht₀ : typeFourArea lam h₀ < typeThreeArea lam a := by
    rw [← env.equalArea hh₀.1 hh₀.2]
    exact hr₀a
  have hK_regular : K ⊆ Ioo (0 : ℝ) 1 := by
    intro y hy
    exact ⟨ha_pos.trans_le hy.1, hy.2.trans_lt hanchor_lt_one⟩
  have hequal : ∀ h ∈ s,
      typeThreeArea lam (env.root h) = typeFourArea lam h := by
    intro h hh
    exact env.equalArea hh.1.1 hh.1.2
  have hunique : ∀ h ∈ s, ∀ y ∈ K,
      typeThreeArea lam y = typeFourArea lam h → y = env.root h := by
    intro h hh y hy heq
    exact hantiK.injOn hy (hroot_mem hh)
      (heq.trans (hequal h hh).symm)
  have hconts : ContinuousOn env.root s :=
    equalAreaRoot_continuousOn_of_compact_unique
      env.density_jump isCompact_Icc hs_domain hK_regular
      hroot_mem hequal hunique
  have hh₀s : h₀ ∈ s := ⟨hh₀, ht₀⟩
  apply (hconts h₀ hh₀s).mono_of_mem_nhdsWithin
  have hA4 : ContinuousAt (typeFourArea lam) h₀ := by
    have hh0 : h₀ ≠ 0 := ne_of_gt hh₀.1
    have hlam0 : lam ≠ 0 :=
      ne_of_gt (lt_trans (by norm_num) env.density_jump)
    unfold typeFourArea typeFourAngle typeFourDelta
    fun_prop (disch := simp_all)
  have hU : {h | typeFourArea lam h < typeThreeArea lam a} ∈ 𝓝 h₀ :=
    hA4.tendsto.eventually_lt_const ht₀
  exact inter_mem self_mem_nhdsWithin
    (Filter.Eventually.filter_mono inf_le_left hU)

/-- Interior continuity is a theorem, not an envelope hypothesis. -/
theorem DescendingEqualAreaEnvelope.root_continuousAt {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    ContinuousAt env.root h₄ :=
  (env.root_continuousOn h₄ ⟨hh₄, hh₄_one.le⟩).continuousAt
    (Ioc_mem_nhds hh₄ hh₄_one)

/-- The genuine perimeter gap is continuous from the modeled side at the
closure endpoint.  No behavior of the arbitrary total root function above
`h₄ = 1` is required. -/
theorem DescendingEqualAreaEnvelope.gap_continuousWithinAt_one {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) :
    ContinuousWithinAt (equalAreaPerimeterGap lam env.root)
      (Ioc (0 : ℝ) 1) 1 := by
  have hP3 : ContinuousAt (typeThreePerimeter lam) (env.root 1) :=
    (typeThree_variational_hasDerivAt env.density_jump
      (env.root_pos (by norm_num) (by norm_num))
      (env.root_lt_one (by norm_num) (by norm_num))).2.continuousAt
  have hP4 : ContinuousAt (typeFourPerimeter lam) 1 := by
    have hlam0 : lam ≠ 0 :=
      ne_of_gt (lt_trans (by norm_num) env.density_jump)
    unfold typeFourPerimeter typeFourAngle
    fun_prop (disch := simp_all)
  change ContinuousWithinAt
    ((typeThreePerimeter lam ∘ env.root) - typeFourPerimeter lam)
      (Ioc (0 : ℝ) 1) 1
  exact (hP3.comp_continuousWithinAt
    (env.root_continuousOn 1 ⟨by norm_num, le_rfl⟩)).sub
      hP4.continuousWithinAt

/-- A certified stationary pair with a negative type-(iii) fold supplies the
complete descending envelope.  No continuity data are inputs. -/
noncomputable def StationaryEqualAreaPair.descendingEnvelope {lam : ℝ}
    (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0) :
    DescendingEqualAreaEnvelope lam where
  fold := pair.h₄
  root := pair.descendingRoot hlam hfoldThree
  density_jump := hlam
  fold_pos := pair.h₄_pos
  fold_lt_one := pair.h₄_lt_one
  fold_stationary := pair.stationary
  root_pos := fun {_h₄} hh₄ hh₄_one =>
    (pair.descendingRoot_spec hlam hfoldThree ⟨hh₄, hh₄_one⟩).1.1
  root_lt_one := fun {_h₄} hh₄ hh₄_one =>
    (pair.descendingRoot_spec hlam hfoldThree ⟨hh₄, hh₄_one⟩).1.2
  equalArea := fun {_h₄} hh₄ hh₄_one =>
    (pair.descendingRoot_spec hlam hfoldThree ⟨hh₄, hh₄_one⟩).2.1
  root_fold_neg := fun {_h₄} hh₄ hh₄_one =>
    (pair.descendingRoot_spec hlam hfoldThree ⟨hh₄, hh₄_one⟩).2.2

/-- The canonical root selected from a stationary pair is continuous on the
entire modeled domain. -/
theorem StationaryEqualAreaPair.descendingRoot_continuousOn {lam : ℝ}
    (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0) :
    ContinuousOn (pair.descendingRoot hlam hfoldThree) (Ioc (0 : ℝ) 1) := by
  simpa [StationaryEqualAreaPair.descendingEnvelope] using
    (pair.descendingEnvelope hlam hfoldThree).root_continuousOn

/-- The canonical pair's perimeter gap is continuous from the modeled side at
the closure endpoint. -/
theorem StationaryEqualAreaPair.gap_continuousWithinAt_one {lam : ℝ}
    (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0) :
    ContinuousWithinAt
      (equalAreaPerimeterGap lam (pair.descendingRoot hlam hfoldThree))
      (Ioc (0 : ℝ) 1) 1 := by
  simpa [StationaryEqualAreaPair.descendingEnvelope] using
    (pair.descendingEnvelope hlam hfoldThree).gap_continuousWithinAt_one

/-- The descending root lies strictly below its type-(iv) curvature.  This is
derived from equal area and the negative-fold branch, rather than retained as
an independent envelope hypothesis. -/
theorem DescendingEqualAreaEnvelope.root_lt_curvature {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    env.root h₄ < h₄ :=
  typeThreeArea_descending_root_lt env.density_jump
    ⟨env.root_pos hh₄ hh₄_one, env.root_lt_one hh₄ hh₄_one⟩
    hh₄ hh₄_one (env.root_fold_neg hh₄ hh₄_one)
    (env.equalArea hh₄ hh₄_one)

/-- The selected descending root is the least regular-or-endpoint root of its
equal-area level, not merely the root isolated by one certificate slab. -/
theorem DescendingEqualAreaEnvelope.root_le_of_equalArea {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ y : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) (hy : y ∈ Ioc (0 : ℝ) 1)
    (hareaY : typeThreeArea lam y = typeFourArea lam h₄) :
    env.root h₄ ≤ y :=
  typeThreeArea_root_le_of_fold_neg env.density_jump
    ⟨env.root_pos hh₄ hh₄_one, env.root_lt_one hh₄ hh₄_one⟩ hy
    (env.root_fold_neg hh₄ hh₄_one)
    ((env.equalArea hh₄ hh₄_one).trans hareaY.symm)

/-- There is at most one upper equal-area root above the selected descending
root.  Together with `root_le_of_equalArea`, this is the complete all-root
classification: the selected root and at most one upper root. -/
theorem DescendingEqualAreaEnvelope.upper_root_unique {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ y z : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1)
    (hy : y ∈ Ioc (0 : ℝ) 1) (hz : z ∈ Ioc (0 : ℝ) 1)
    (hrootY : env.root h₄ < y) (hrootZ : env.root h₄ < z)
    (hareaY : typeThreeArea lam y = typeFourArea lam h₄)
    (hareaZ : typeThreeArea lam z = typeFourArea lam h₄) :
    y = z :=
  typeThreeArea_upper_root_unique env.density_jump
    ⟨env.root_pos hh₄ hh₄_one, (env.root_lt_one hh₄ hh₄_one).le⟩
    hy hz hrootY hrootZ
    ((env.equalArea hh₄ hh₄_one).trans hareaY.symm)
    ((env.equalArea hh₄ hh₄_one).trans hareaZ.symm)

/-- The descending-root fold sign gives strict negativity of the actual
type-(iii) area derivative. -/
theorem DescendingEqualAreaEnvelope.typeThreeArea_deriv_neg {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    deriv (typeThreeArea lam) (env.root h₄) < 0 := by
  rw [(hasDerivAt_typeThreeArea env.density_jump
    (env.root_pos hh₄ hh₄_one.le)
    (env.root_lt_one hh₄ hh₄_one.le)).deriv]
  exact div_neg_of_neg_of_pos (env.root_fold_neg hh₄ hh₄_one.le)
    (pow_pos (env.root_pos hh₄ hh₄_one.le) 3)

/-- Every selected regular descending root is simple. -/
theorem DescendingEqualAreaEnvelope.typeThreeArea_deriv_ne_zero {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    deriv (typeThreeArea lam) (env.root h₄) ≠ 0 :=
  ne_of_lt (env.typeThreeArea_deriv_neg hh₄ hh₄_one)

/-- The selected root's derivative is forced by the equal-area equation. -/
theorem DescendingEqualAreaEnvelope.root_hasDerivAt {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    HasDerivAt env.root
      (deriv (typeFourArea lam) h₄ /
        deriv (typeThreeArea lam) (env.root h₄)) h₄ :=
  equalAreaRoot_hasDerivAt env.density_jump hh₄ hh₄_one
    (env.root_pos hh₄ hh₄_one.le) (env.root_lt_one hh₄ hh₄_one.le)
    (env.root_continuousAt hh₄ hh₄_one)
    (env.typeThreeArea_deriv_ne_zero hh₄ hh₄_one) env.equalArea

/-- Interior differentiability is not an independent envelope hypothesis. -/
theorem DescendingEqualAreaEnvelope.root_differentiableAt {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    DifferentiableAt ℝ env.root h₄ :=
  (env.root_hasDerivAt hh₄ hh₄_one).differentiableAt

/-- The envelope derivative is a consequence of root differentiability,
equal area, and the exact variational identities. -/
theorem DescendingEqualAreaEnvelope.gap_hasDerivAt {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    HasDerivAt (equalAreaPerimeterGap lam env.root)
      ((env.root h₄ - h₄) * deriv (typeFourArea lam) h₄) h₄ :=
  equalAreaPerimeterGap_hasDerivAt env.density_jump hh₄ hh₄_one
    (env.root_pos hh₄ hh₄_one.le) (env.root_lt_one hh₄ hh₄_one.le)
    (env.root_differentiableAt hh₄ hh₄_one) env.equalArea

/-- The real fold-gap proposition attached to explicit analytic envelope data.
It is exactly a strict inequality between the modeled perimeters at the fold;
it contains no all-curvature conclusion. -/
def FoldGapNegative {lam : ℝ} (env : DescendingEqualAreaEnvelope lam) : Prop :=
  equalAreaPerimeterGap lam env.root env.fold < 0

/-- L12, including the closure endpoint: the stationary fold is the strict
maximum of the genuine perimeter gap along the selected equal-area branch. -/
theorem equalAreaPerimeterGap_lt_fold {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) (hne : h₄ ≠ env.fold) :
    equalAreaPerimeterGap lam env.root h₄ <
      equalAreaPerimeterGap lam env.root env.fold := by
  have hfold_mem_right : env.fold ∈ Icc env.fold (1 : ℝ) :=
    ⟨le_rfl, env.fold_lt_one.le⟩
  by_cases hside : h₄ < env.fold
  · have hleft : StrictMonoOn (equalAreaPerimeterGap lam env.root)
        (Icc h₄ env.fold) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc h₄ env.fold)
      · intro h hh
        exact (env.gap_hasDerivAt (hh₄.trans_le hh.1)
          (hh.2.trans_lt env.fold_lt_one)).continuousAt.continuousWithinAt
      · intro h hh
        rw [interior_Icc] at hh
        rw [(env.gap_hasDerivAt (hh₄.trans hh.1)
          (hh.2.trans env.fold_lt_one)).deriv]
        exact mul_pos_of_neg_of_neg
          (sub_neg.mpr (env.root_lt_curvature (hh₄.trans hh.1)
            (hh.2.trans env.fold_lt_one).le))
          (typeFourArea_deriv_neg_before_zero env.density_jump
            ⟨env.fold_pos, env.fold_lt_one⟩ env.fold_stationary
            ⟨hh₄.trans hh.1, hh.2.trans env.fold_lt_one⟩ hh.2)
    exact hleft ⟨le_rfl, hside.le⟩ ⟨hside.le, le_rfl⟩ hside
  · have hfold_lt : env.fold < h₄ := lt_of_le_of_ne
      (le_of_not_gt hside) (Ne.symm hne)
    have hright : StrictAntiOn (equalAreaPerimeterGap lam env.root)
        (Icc env.fold (1 : ℝ)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc env.fold 1)
      · intro h hh
        by_cases hh_one : h = 1
        · simpa [hh_one] using env.gap_continuousWithinAt_one.mono
            (fun x hx => ⟨env.fold_pos.trans_le hx.1, hx.2⟩)
        · exact (env.gap_hasDerivAt
            (env.fold_pos.trans_le hh.1) (lt_of_le_of_ne hh.2 hh_one)
          ).continuousAt.continuousWithinAt
      · intro h hh
        rw [interior_Icc] at hh
        rw [(env.gap_hasDerivAt (env.fold_pos.trans hh.1) hh.2).deriv]
        exact mul_neg_of_neg_of_pos
          (sub_neg.mpr (env.root_lt_curvature (env.fold_pos.trans hh.1)
            hh.2.le))
          (typeFourArea_deriv_pos_after_zero env.density_jump
            ⟨env.fold_pos, env.fold_lt_one⟩ env.fold_stationary
            ⟨env.fold_pos.trans hh.1, hh.2⟩ hh.1)
    exact hright hfold_mem_right ⟨hfold_lt.le, hh₄_one⟩ hfold_lt

/-- Non-strict form of the global fold maximum, convenient when only fold-gap
negativity is needed downstream. -/
theorem equalAreaPerimeterGap_le_fold {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) {h₄ : ℝ}
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    equalAreaPerimeterGap lam env.root h₄ ≤
      equalAreaPerimeterGap lam env.root env.fold := by
  by_cases h : h₄ = env.fold
  · subst h₄
    exact le_rfl
  · exact (equalAreaPerimeterGap_lt_fold env hh₄ hh₄_one h).le

/-- L14 at the modeled scalar level.  A negative genuine fold gap yields an
improving equal-area type-(iii) scalar for every `0 < h₄ ≤ 1`, including the
modeled endpoint `h₄ = 1`. -/
theorem allCurvature_typeThreeImprovement_of_envelope {lam h₄ : ℝ}
    (env : DescendingEqualAreaEnvelope lam) (hfoldGap : FoldGapNegative env)
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    ∃ h₃ : ℝ, 0 < h₃ ∧ h₃ < 1 ∧
      typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
      typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄ := by
  refine ⟨env.root h₄, env.root_pos hh₄ hh₄_one,
    env.root_lt_one hh₄ hh₄_one, env.equalArea hh₄ hh₄_one, ?_⟩
  rw [← sub_lt_zero]
  exact lt_of_le_of_lt (equalAreaPerimeterGap_le_fold env hh₄ hh₄_one) hfoldGap

/-- One certified stationary pair with negative type-(iii) fold and strict
perimeter improvement supplies an improving equal-area type-(iii) scalar at
every regular or endpoint type-(iv) curvature. -/
theorem StationaryEqualAreaPair.allCurvature_typeThreeImprovement
    {lam h₄ : ℝ} (pair : StationaryEqualAreaPair lam)
    (hlam : 1 < lam) (hfoldThree : typeThreeFold lam pair.h₃ < 0)
    (hperimeter :
      typeThreePerimeter lam pair.h₃ < typeFourPerimeter lam pair.h₄)
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    ∃ h₃ : ℝ, 0 < h₃ ∧ h₃ < 1 ∧
      typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
      typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄ := by
  let env := pair.descendingEnvelope hlam hfoldThree
  apply allCurvature_typeThreeImprovement_of_envelope env
  · unfold FoldGapNegative equalAreaPerimeterGap
    change typeThreePerimeter lam
        (pair.descendingRoot hlam hfoldThree pair.h₄) -
      typeFourPerimeter lam pair.h₄ < 0
    rw [pair.descendingRoot_at_stationary hlam hfoldThree]
    linarith
  · exact hh₄
  · exact hh₄_one

/-- The envelope reduction with every independent analytic hypothesis exposed
as an argument.  Fold stationarity and the selected negative-fold equal-area
root derive branch continuity, closure-endpoint continuity, strict root order,
simple-root nonvanishing, and the envelope derivative identity.  No remaining
hypothesis contains the desired comparison. -/
theorem allCurvature_typeThreeImprovement_of_analytic_hypotheses
    {lam fold h₄ : ℝ} {root : ℝ → ℝ}
    (hlam : 1 < lam)
    (hfold_pos : 0 < fold) (hfold_lt_one : fold < 1)
    (hfold_stationary : typeFourFold lam fold = 0)
    (hroot_pos : ∀ ⦃h : ℝ⦄, 0 < h → h ≤ 1 → 0 < root h)
    (hroot_lt_one : ∀ ⦃h : ℝ⦄, 0 < h → h ≤ 1 → root h < 1)
    (hequalArea : ∀ ⦃h : ℝ⦄, 0 < h → h ≤ 1 →
      typeThreeArea lam (root h) = typeFourArea lam h)
    (hroot_fold_neg : ∀ ⦃h : ℝ⦄, 0 < h → h ≤ 1 →
      typeThreeFold lam (root h) < 0)
    (hfoldGap : equalAreaPerimeterGap lam root fold < 0)
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    ∃ h₃ : ℝ, 0 < h₃ ∧ h₃ < 1 ∧
      typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
      typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄ := by
  let env : DescendingEqualAreaEnvelope lam :=
    { fold := fold
      root := root
      density_jump := hlam
      fold_pos := hfold_pos
      fold_lt_one := hfold_lt_one
      fold_stationary := hfold_stationary
      root_pos := hroot_pos
      root_lt_one := hroot_lt_one
      equalArea := hequalArea
      root_fold_neg := hroot_fold_neg }
  exact allCurvature_typeThreeImprovement_of_envelope env hfoldGap hh₄ hh₄_one

/-- Regular-curvature specialization (`h₄ < 1`). -/
theorem regular_typeThreeImprovement_of_envelope {lam h₄ : ℝ}
    (env : DescendingEqualAreaEnvelope lam) (hfoldGap : FoldGapNegative env)
    (hh₄ : 0 < h₄) (hh₄_one : h₄ < 1) :
    ∃ h₃ : ℝ, 0 < h₃ ∧ h₃ < 1 ∧
      typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
      typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄ :=
  allCurvature_typeThreeImprovement_of_envelope env hfoldGap hh₄ hh₄_one.le

/-- Modeled closure-endpoint specialization.  This makes explicit that endpoint
handling is analytic and does not assert that `h₄ = 1` is a regular CMV source
profile. -/
theorem endpoint_typeThreeImprovement_of_envelope {lam : ℝ}
    (env : DescendingEqualAreaEnvelope lam) (hfoldGap : FoldGapNegative env) :
    ∃ h₃ : ℝ, 0 < h₃ ∧ h₃ < 1 ∧
      typeThreeArea lam h₃ = typeFourArea lam 1 ∧
      typeThreePerimeter lam h₃ < typeFourPerimeter lam 1 :=
  allCurvature_typeThreeImprovement_of_envelope env hfoldGap (by norm_num)
    (by norm_num)

/-- Exact remaining concrete interface for the retained suffix.  Proving this
requires only L01--L07 and L12 for the formulas in `LeanSuffixAnalytic`; it does
not contain any perimeter-improvement conclusion. -/
def HasDescendingEqualAreaEnvelopeOnRetainedSuffix : Prop :=
  ∀ (lam : ℝ), InRetainedSuffix lam → Nonempty (DescendingEqualAreaEnvelope lam)

/-- Genuine retained fold-gap negativity, quantified over the explicit
descending-envelope data.  The separate existence proposition above is the
remaining analytic root-selection interface. -/
def RetainedFoldGapNegative : Prop :=
  ∀ (lam : ℝ), InRetainedSuffix lam →
    ∀ env : DescendingEqualAreaEnvelope lam, FoldGapNegative env

/-- Direct retained-suffix consumer with the unresolved analytic existence
interface kept separate from the real fold-gap proposition. -/
theorem allCurvature_typeThreeImprovement
    (henvelope : HasDescendingEqualAreaEnvelopeOnRetainedSuffix)
    (hfoldGap : RetainedFoldGapNegative)
    {lam h₄ : ℝ} (hlam : InRetainedSuffix lam)
    (hh₄ : 0 < h₄) (hh₄_one : h₄ ≤ 1) :
    ∃ h₃ : ℝ, 0 < h₃ ∧ h₃ < 1 ∧
      typeThreeArea lam h₃ = typeFourArea lam h₄ ∧
      typeThreePerimeter lam h₃ < typeFourPerimeter lam h₄ := by
  rcases henvelope lam hlam with ⟨env⟩
  exact allCurvature_typeThreeImprovement_of_envelope env
    (hfoldGap lam hlam env) hh₄ hh₄_one

end LeanSuffixAnalytic
