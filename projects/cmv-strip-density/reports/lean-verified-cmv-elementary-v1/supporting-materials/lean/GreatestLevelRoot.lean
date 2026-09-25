import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Ring

namespace CMVElementary

open Set

/-- The final crossing of a continuous level has a strict one-sided barrier.
No monotonicity or uniqueness of the level set is assumed. -/
theorem exists_greatest_level_root
    {F : ℝ → ℝ} {a b V : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b))
    (ha : V < F a) (hb : F b < V) :
    ∃ r ∈ Ioo a b, F r = V ∧
      IsGreatest (Icc a b ∩ F ⁻¹' {V}) r ∧
      ∀ t ∈ Ioc r b, F t < V := by
  obtain ⟨x, hx, hxV⟩ := intermediate_value_Icc' hab.le hF ⟨hb.le, ha.le⟩
  have hcompact : IsCompact (Icc a b ∩ F ⁻¹' {V}) :=
    isCompact_Icc.of_isClosed_subset
      (hF.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  obtain ⟨r, hr, hmax⟩ := hcompact.exists_isGreatest ⟨x, hx, hxV⟩
  have hrV : F r = V := hr.2
  have hne_a : r ≠ a := by
    intro h
    subst r
    exact (ne_of_gt ha) hrV
  have hne_b : r ≠ b := by
    intro h
    subst r
    exact (ne_of_lt hb) hrV
  have har : a < r := lt_of_le_of_ne hr.1.1 hne_a.symm
  have hrb : r < b := lt_of_le_of_ne hr.1.2 hne_b
  refine ⟨r, ⟨har, hrb⟩, hrV, ⟨hr, hmax⟩, ?_⟩
  intro t ht
  by_contra h
  have hVt : V ≤ F t := le_of_not_gt h
  have hFt : ContinuousOn F (Icc t b) := hF.mono (by
    intro z hz
    exact ⟨hr.1.1.trans (ht.1.le.trans hz.1), hz.2⟩)
  obtain ⟨z, hz, hzV⟩ := intermediate_value_Icc' ht.2 hFt ⟨hb.le, hVt⟩
  have hzr : z ≤ r := hmax ⟨⟨hr.1.1.trans (ht.1.le.trans hz.1), hz.2⟩, hzV⟩
  exact (not_le_of_gt (ht.1.trans_le hz.1)) hzr

/-- A variational identity converts a strict area barrier into a strict
support comparison. Differentiability at the endpoints is not required. -/
theorem strict_support_comparison
    {A P : ℝ → ℝ} {a b V : ℝ}
    (hab : a < b)
    (hA : ContinuousOn A (Icc a b))
    (hP : ContinuousOn P (Icc a b))
    (ha : A a = V)
    (hbelow : ∀ t ∈ Ioo a b, A t < V)
    (hvar : ∀ t ∈ Ioo a b,
      ∃ d : ℝ, HasDerivAt A d t ∧ HasDerivAt P (t * d) t) :
    P a < P b + b * (V - A b) := by
  let Q : ℝ → ℝ := fun t => P t + t * (V - A t)
  have hQ : ContinuousOn Q (Icc a b) :=
    hP.add (continuousOn_id.mul (continuousOn_const.sub hA))
  have hQderiv : ∀ t ∈ Ioo a b, HasDerivAt Q (V - A t) t := by
    intro t ht
    obtain ⟨d, hAd, hPd⟩ := hvar t ht
    have hcalc : HasDerivAt Q (t * d + (1 * (V - A t) + t * (0 - d))) t :=
      hPd.add ((hasDerivAt_id t).mul ((hasDerivAt_const t V).sub hAd))
    convert hcalc using 1
    ring
  have hmono : StrictMonoOn Q (Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) hQ (by
      intro t ht
      have ht' : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
      rw [(hQderiv t ht').deriv]
      exact sub_pos.mpr (hbelow t ht'))
  have hcompare := hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  simpa only [Q, ha, sub_self, mul_zero, add_zero] using hcompare

/-- The greatest-root argument followed by the variational comparison.
Neither uniqueness of the level nor global monotonicity of area is assumed. -/
theorem exists_equal_area_strict_support_comparison
    {A P : ℝ → ℝ} {a h V : ℝ}
    (hah : a < h)
    (hA : ContinuousOn A (Icc a h))
    (hP : ContinuousOn P (Icc a h))
    (ha : V < A a) (hh : A h < V)
    (hvar : ∀ t ∈ Ioo a h,
      ∃ d : ℝ, HasDerivAt A d t ∧ HasDerivAt P (t * d) t) :
    ∃ r ∈ Ioo a h, A r = V ∧ P r < P h + h * (V - A h) := by
  obtain ⟨r, hr, hrV, _, hbelow⟩ :=
    exists_greatest_level_root hah hA ha hh
  have hsubset : Icc r h ⊆ Icc a h := by
    intro t ht
    exact ⟨hr.1.le.trans ht.1, ht.2⟩
  refine ⟨r, hr, hrV, strict_support_comparison hr.2
    (hA.mono hsubset) (hP.mono hsubset) hrV ?_ ?_⟩
  · intro t ht
    exact hbelow t ⟨ht.1, ht.2.le⟩
  · intro t ht
    exact hvar t ⟨hr.1.trans ht.1, ht.2⟩

end CMVElementary

#print axioms CMVElementary.exists_greatest_level_root
#print axioms CMVElementary.strict_support_comparison
#print axioms CMVElementary.exists_equal_area_strict_support_comparison
