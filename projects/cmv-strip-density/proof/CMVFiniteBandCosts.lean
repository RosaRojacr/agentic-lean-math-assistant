import CMVFiniteBandFrontier
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators symmDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteBandRearrangement

/-- Nested compact exhaustion of an open height band.  The first member is the
midpoint singleton; subsequent members approach both endpoints. -/
def interiorCompact (a b : ℝ) (n : ℕ) : Set ℝ :=
  Icc (a + (b - a) / (n + 2 : ℝ)) (b - (b - a) / (n + 2 : ℝ))

lemma interiorCompact_subset_Ioo {a b : ℝ} (hab : a < b) (n : ℕ) :
    interiorCompact a b n ⊆ Ioo a b := by
  intro y hy
  have hn : (0 : ℝ) < n + 2 := by positivity
  have heps : 0 < (b - a) / (n + 2 : ℝ) := div_pos (sub_pos.mpr hab) hn
  exact ⟨lt_of_lt_of_le (by linarith) hy.1,
    lt_of_le_of_lt hy.2 (by linarith)⟩

lemma monotone_interiorCompact {a b : ℝ} (hab : a ≤ b) :
    Monotone (interiorCompact a b) := by
  intro n m hnm y hy
  have hden : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
    norm_cast
    omega
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hfrac : (b - a) / (m + 2 : ℝ) ≤ (b - a) / (n + 2 : ℝ) :=
    div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hn hden
  exact ⟨by dsimp [interiorCompact] at hy ⊢; linarith [hy.1],
    by dsimp [interiorCompact] at hy ⊢; linarith [hy.2]⟩

lemma iUnion_interiorCompact {a b : ℝ} (hab : a < b) :
    (⋃ n : ℕ, interiorCompact a b n) = Ioo a b := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun n => interiorCompact_subset_Ioo hab n
  · intro y hy
    let δ : ℝ := min (y - a) (b - y)
    have hδ : 0 < δ := lt_min (sub_pos.mpr hy.1) (sub_pos.mpr hy.2)
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((b - a) / δ)
    have hden : (0 : ℝ) < N + 2 := by positivity
    have hcross : b - a < (N : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hN
    have heps : (b - a) / (N + 2 : ℝ) < δ :=
      (div_lt_iff₀ hden).mpr (by nlinarith)
    rw [mem_iUnion]
    refine ⟨N, ?_⟩
    change a + (b - a) / (N + 2 : ℝ) ≤ y ∧
      y ≤ b - (b - a) / (N + 2 : ℝ)
    have hδleft : δ ≤ y - a := min_le_left _ _
    have hδright : δ ≤ b - y := min_le_right _ _
    constructor <;> linarith

lemma interiorCompact_nonempty {a b : ℝ} (hab : a < b) (n : ℕ) :
    a + (b - a) / (n + 2 : ℝ) ≤ b - (b - a) / (n + 2 : ℝ) := by
  have hn : (2 : ℝ) ≤ n + 2 := by norm_cast; omega
  have hnpos : (0 : ℝ) < n + 2 := by positivity
  have hratio : 2 / (n + 2 : ℝ) ≤ 1 := (div_le_one hnpos).mpr hn
  have hfrac : 2 * ((b - a) / (n + 2 : ℝ)) ≤ b - a := by
    calc
      2 * ((b - a) / (n + 2 : ℝ)) =
          (b - a) * (2 / (n + 2 : ℝ)) := by ring
      _ ≤ (b - a) * 1 :=
        mul_le_mul_of_nonneg_left hratio (sub_pos.mpr hab).le
      _ = b - a := mul_one _
  linarith

/-- Exact Euclidean `H¹` length of a height-oriented graph whose endpoint
representative is continuous, `C¹` only in the open band, and has integrable
speed.  Endpoint slope blow-up is allowed. -/
theorem hausdorffMeasure_verticalGraph_Icc_eq_setLIntegral
    {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : Continuous g)
    (hgC1 : ContDiffOn ℝ 1 g (Ioo a b))
    (hspeed : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) (Ioo a b)) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' ((fun y : ℝ => (g y, y)) '' Icc a b)) =
      ENNReal.ofReal
        (∫ y in Ioo a b, Real.sqrt (1 + deriv g y ^ 2)) := by
  let K : ℕ → Set ℝ := interiorCompact a b
  let G : ℝ → EuclideanPlane := fun y => planeEuclideanHomeomorph (g y, y)
  have hKmono : Monotone K := monotone_interiorCompact hab.le
  have hKunion : (⋃ n, K n) = Ioo a b := iUnion_interiorCompact hab
  have hGinj : Function.Injective G := by
    intro x y hxy
    have := congrArg (fun z : EuclideanPlane => (planeEuclideanHomeomorph.symm z).2) hxy
    simpa [G] using this
  have hcompact (n : ℕ) : IsCompact (K n) := isCompact_Icc
  have hformula (n : ℕ) :
      (μH[1] : Measure EuclideanPlane) (G '' K n) =
        ENNReal.ofReal
          (∫ y in K n, Real.sqrt (1 + deriv g y ^ 2)) := by
    let c := a + (b - a) / (n + 2 : ℝ)
    let d := b - (b - a) / (n + 2 : ℝ)
    have hcd : c ≤ d := interiorCompact_nonempty hab n
    have hKsub : Icc c d ⊆ Ioo a b := interiorCompact_subset_Ioo hab n
    have hnhd : Ioo a b ∈ 𝓝ˢ (Icc c d) := isOpen_Ioo.mem_nhdsSet.2 hKsub
    obtain ⟨g', hg'C1, _happrox, hg'eq, _hsupport⟩ :=
      hg.exists_contDiff_approx_and_eqOn 1 continuous_const (fun _ => zero_lt_one)
        isClosed_Icc hnhd hgC1
    have hgraphEq : G '' K n =
        planeEuclideanHomeomorph '' ((fun y : ℝ => (g' y, y)) '' Icc c d) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨(g' y, y), ⟨y, ?_, rfl⟩, ?_⟩
        · simpa [K, interiorCompact, c, d] using hy
        · simp only [G]
          rw [hg'eq (by simpa [K, interiorCompact, c, d] using hy)]
      · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, ?_, ?_⟩
        · simpa [K, interiorCompact, c, d] using hy
        · simp only [G]
          rw [hg'eq hy]
    rw [hgraphEq]
    have hmass :=
      hausdorffMeasure_euclideanHorizontalGraph_image_eq_setLIntegral
        (s := Icc c d) hg'C1 measurableSet_Icc
    unfold euclideanHorizontalGraphParam at hmass
    rw [show planeEuclideanHomeomorph '' ((fun y : ℝ => (g' y, y)) '' Icc c d) =
        (fun y : ℝ => planeEuclideanHomeomorph (g' y, y)) '' Icc c d by
      rw [Set.image_image], hmass]
    have hKn : K n = Icc c d := by
      simp only [K, interiorCompact, c, d]
    rw [hKn]
    have hspeedIcc :
        IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) (Icc c d) :=
      hspeed.mono_set hKsub
    rw [ofReal_integral_eq_lintegral_ofReal hspeedIcc
      (Filter.Eventually.of_forall fun y => Real.sqrt_nonneg _)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) c),
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) d)] with y hy hyc hyd
    have hyOpen : y ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hyc), lt_of_le_of_ne hy.2 hyd⟩
    rw [(hg'eq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hyOpen]
  have hmeasureTendsto : Tendsto
      (fun n => (μH[1] : Measure EuclideanPlane) (G '' K n)) atTop
      (𝓝 ((μH[1] : Measure EuclideanPlane) (G '' Ioo a b))) := by
    have hmono : Monotone (fun n => G '' K n) := fun n m hnm =>
      image_mono (hKmono hnm)
    change Tendsto ((μH[1] : Measure EuclideanPlane) ∘
      fun n => G '' K n) atTop
      (𝓝 ((μH[1] : Measure EuclideanPlane) (G '' Ioo a b)))
    simpa only [← image_iUnion, hKunion] using
      (tendsto_measure_iUnion_atTop (μ := (μH[1] : Measure EuclideanPlane)) hmono)
  have hintegralTendsto : Tendsto
      (fun n => ∫ y in K n, Real.sqrt (1 + deriv g y ^ 2)) atTop
      (𝓝 (∫ y in Ioo a b, Real.sqrt (1 + deriv g y ^ 2))) := by
    have hunionIntegrable :
        IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) (⋃ n, K n) := by
      rw [hKunion]
      exact hspeed
    simpa only [hKunion] using tendsto_setIntegral_of_monotone
      (fun n => (hcompact n).measurableSet) hKmono hunionIntegrable
  have hofRealTendsto : Tendsto
      (fun n => ENNReal.ofReal
        (∫ y in K n, Real.sqrt (1 + deriv g y ^ 2))) atTop
      (𝓝 (ENNReal.ofReal
        (∫ y in Ioo a b, Real.sqrt (1 + deriv g y ^ 2)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hintegralTendsto
  have hopen : (μH[1] : Measure EuclideanPlane) (G '' Ioo a b) =
      ENNReal.ofReal (∫ y in Ioo a b, Real.sqrt (1 + deriv g y ^ 2)) :=
    tendsto_nhds_unique hmeasureTendsto
      (hofRealTendsto.congr' (Eventually.of_forall fun n => (hformula n).symm))
  have hend : (μH[1] : Measure EuclideanPlane)
      (G '' ({a, b} : Set ℝ)) = 0 := by
    let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
      Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
    exact (Set.toFinite {a, b}).image G |>.measure_zero μH[1]
  have hdecomp : G '' Icc a b = G '' Ioo a b ∪ G '' ({a, b} : Set ℝ) := by
    rw [← image_union]
    congr 1
    ext y
    simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hy
      rcases hy.1.eq_or_lt with rfl | hya
      · exact Or.inr (Or.inl rfl)
      · rcases hy.2.eq_or_lt with rfl | hyb
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl ⟨hya, hyb⟩
    · rintro (hy | rfl | rfl)
      · exact ⟨hy.1.le, hy.2.le⟩
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
  rw [show planeEuclideanHomeomorph '' ((fun y : ℝ => (g y, y)) '' Icc a b) =
      G '' Icc a b by rw [Set.image_image]]
  rw [hdecomp]
  calc
    (μH[1] : Measure EuclideanPlane) (G '' Ioo a b ∪ G '' {a, b}) =
        (μH[1] : Measure EuclideanPlane) (G '' Ioo a b) := by
      apply measure_congr
      have hnull : ∀ᵐ z ∂(μH[1] : Measure EuclideanPlane),
          z ∉ G '' ({a, b} : Set ℝ) := by
        rw [ae_iff]
        simpa only [Set.ofPred_mem_eq, not_not] using hend
      filter_upwards [hnull] with z hz
      apply propext
      constructor
      · intro hzUnion
        exact hzUnion.resolve_right hz
      · exact Or.inl
    _ = _ := hopen

/-- Interior measurable-set form of the endpoint-singular graph formula.  This
is the pullback identity needed to weight a graph by height zones. -/
theorem hausdorffMeasure_verticalGraph_image_eq_setLIntegral
    {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : Continuous g)
    (hgC1 : ContDiffOn ℝ 1 g (Ioo a b))
    (hspeed : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) (Ioo a b))
    {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Ioo a b) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' ((fun y : ℝ => (g y, y)) '' s)) =
      ∫⁻ y in s, ENNReal.ofReal (Real.sqrt (1 + deriv g y ^ 2)) := by
  let K : ℕ → Set ℝ := interiorCompact a b
  let G : ℝ → EuclideanPlane := fun y => planeEuclideanHomeomorph (g y, y)
  have hKmono : Monotone K := monotone_interiorCompact hab.le
  have hKunion : (⋃ n, K n) = Ioo a b := iUnion_interiorCompact hab
  have hcompact (n : ℕ) : IsCompact (K n) := isCompact_Icc
  have hformula (n : ℕ) :
      (μH[1] : Measure EuclideanPlane) (G '' (s ∩ K n)) =
        ENNReal.ofReal
          (∫ y in s ∩ K n, Real.sqrt (1 + deriv g y ^ 2)) := by
    let c := a + (b - a) / (n + 2 : ℝ)
    let d := b - (b - a) / (n + 2 : ℝ)
    have hKsub : Icc c d ⊆ Ioo a b := interiorCompact_subset_Ioo hab n
    have hnhd : Ioo a b ∈ 𝓝ˢ (Icc c d) := isOpen_Ioo.mem_nhdsSet.2 hKsub
    obtain ⟨g', hg'C1, _happrox, hg'eq, _hsupport⟩ :=
      hg.exists_contDiff_approx_and_eqOn 1 continuous_const (fun _ => zero_lt_one)
        isClosed_Icc hnhd hgC1
    have hKn : K n = Icc c d := by
      simp only [K, interiorCompact, c, d]
    have hsourceMeas : MeasurableSet (s ∩ K n) :=
      hs.inter (hcompact n).measurableSet
    have hgraphEq :
        G '' (s ∩ K n) =
          planeEuclideanHomeomorph '' ((fun y : ℝ => (g' y, y)) '' (s ∩ K n)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩
        refine ⟨(g' y, y), ⟨y, hy, rfl⟩, ?_⟩
        simp only [G]
        rw [hg'eq (by rw [← hKn]; exact hy.2)]
      · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        simp only [G]
        rw [hg'eq (by rw [← hKn]; exact hy.2)]
    rw [hgraphEq]
    have hmass :=
      hausdorffMeasure_euclideanHorizontalGraph_image_eq_setLIntegral
        (s := s ∩ K n) hg'C1 hsourceMeas
    unfold euclideanHorizontalGraphParam at hmass
    rw [show planeEuclideanHomeomorph ''
        ((fun y : ℝ => (g' y, y)) '' (s ∩ K n)) =
          (fun y : ℝ => planeEuclideanHomeomorph (g' y, y)) '' (s ∩ K n) by
      rw [Set.image_image], hmass]
    have hspeedSource :
        IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) (s ∩ K n) :=
      hspeed.mono_set fun y hy => hKsub (by rw [← hKn]; exact hy.2)
    rw [ofReal_integral_eq_lintegral_ofReal hspeedSource
      (Filter.Eventually.of_forall fun y => Real.sqrt_nonneg _)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hsourceMeas,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) c),
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) d)] with y hy hyc hyd
    have hyIcc : y ∈ Icc c d := by rw [← hKn]; exact hy.2
    have hyOpen : y ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hyIcc.1 (Ne.symm hyc), lt_of_le_of_ne hyIcc.2 hyd⟩
    rw [(hg'eq.mono Ioo_subset_Icc_self).deriv isOpen_Ioo hyOpen]
  have hsetMono : Monotone (fun n => s ∩ K n) := fun n m hnm =>
    inter_subset_inter_right s (hKmono hnm)
  have hsetUnion : (⋃ n, s ∩ K n) = s := by
    rw [← inter_iUnion, hKunion, inter_eq_left.mpr hsub]
  have hmeasureTendsto : Tendsto
      (fun n => (μH[1] : Measure EuclideanPlane) (G '' (s ∩ K n))) atTop
      (𝓝 ((μH[1] : Measure EuclideanPlane) (G '' s))) := by
    have hmono : Monotone (fun n => G '' (s ∩ K n)) := fun n m hnm =>
      image_mono (hsetMono hnm)
    change Tendsto ((μH[1] : Measure EuclideanPlane) ∘
      fun n => G '' (s ∩ K n)) atTop
      (𝓝 ((μH[1] : Measure EuclideanPlane) (G '' s)))
    simpa only [← image_iUnion, hsetUnion] using
      (tendsto_measure_iUnion_atTop (μ := (μH[1] : Measure EuclideanPlane)) hmono)
  have hintegralTendsto : Tendsto
      (fun n => ∫ y in s ∩ K n, Real.sqrt (1 + deriv g y ^ 2)) atTop
      (𝓝 (∫ y in s, Real.sqrt (1 + deriv g y ^ 2))) := by
    have hsIntegrable :
        IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) s :=
      hspeed.mono_set hsub
    have hunionIntegrable :
        IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2))
          (⋃ n, s ∩ K n) := by
      rw [hsetUnion]
      exact hsIntegrable
    simpa only [hsetUnion] using tendsto_setIntegral_of_monotone
      (fun n => hs.inter (hcompact n).measurableSet) hsetMono hunionIntegrable
  have hofRealTendsto : Tendsto
      (fun n => ENNReal.ofReal
        (∫ y in s ∩ K n, Real.sqrt (1 + deriv g y ^ 2))) atTop
      (𝓝 (ENNReal.ofReal
        (∫ y in s, Real.sqrt (1 + deriv g y ^ 2)))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hintegralTendsto
  have hmass :
      (μH[1] : Measure EuclideanPlane) (G '' s) =
        ENNReal.ofReal (∫ y in s, Real.sqrt (1 + deriv g y ^ 2)) :=
    tendsto_nhds_unique hmeasureTendsto
      (hofRealTendsto.congr' (Eventually.of_forall fun n => (hformula n).symm))
  rw [show planeEuclideanHomeomorph '' ((fun y : ℝ => (g y, y)) '' s) =
      G '' s by rw [Set.image_image], hmass]
  exact ofReal_integral_eq_lintegral_ofReal (hspeed.mono_set hsub)
    (Filter.Eventually.of_forall fun y => Real.sqrt_nonneg _)

lemma measurableSet_verticalGraph_image {g : ℝ → ℝ} (hg : Continuous g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet ((fun y : ℝ => (g y, y)) '' s) :=
  ((hg.prodMk continuous_id).measurableEmbedding fun x y hxy => by
    simpa using congrArg Prod.snd hxy).measurableSet_image' hs

lemma weightedTraceCost_union_eq (lam : ℝ) {S T : Set PlanePoint}
    (hT : MeasurableSet T) (hdisjoint : Disjoint S T) :
    weightedTraceCost lam (S ∪ T) =
      weightedTraceCost lam S + weightedTraceCost lam T := by
  unfold weightedTraceCost
  rw [Set.image_union, lintegral_union]
  · exact (planeEuclideanHomeomorph.continuous.measurableEmbedding
      planeEuclideanHomeomorph.injective).measurableSet_image' hT
  · exact hdisjoint.image planeEuclideanHomeomorph.injective.injOn
      (subset_univ S) (subset_univ T)

lemma weightedTraceCost_eq_zero_of_hausdorffMeasure_zero (lam : ℝ)
    {S : Set PlanePoint}
    (hzero : (μH[1] : Measure EuclideanPlane)
      (planeEuclideanHomeomorph '' S) = 0) :
    weightedTraceCost lam S = 0 := by
  unfold weightedTraceCost
  exact setLIntegral_measure_zero _ _ hzero

/-- Exact density-weighted cost of an endpoint-singular vertical graph.  The
two displayed terms are the actual graph-speed integrals in the density-one
strip and its complement. -/
theorem weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals
    (lam : ℝ) {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : Continuous g)
    (hgC1 : ContDiffOn ℝ 1 g (Ioo a b))
    (hspeed : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) (Ioo a b)) :
    weightedTraceCost lam ((fun y : ℝ => (g y, y)) '' Icc a b) =
      (∫⁻ y in Ioo a b ∩ {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal (Real.sqrt (1 + deriv g y ^ 2))) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo a b \ {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal (Real.sqrt (1 + deriv g y ^ 2)) := by
  let V : ℝ → PlanePoint := fun y => (g y, y)
  let inside : Set ℝ := Ioo a b ∩ {y : ℝ | |y| ≤ 1}
  let outside : Set ℝ := Ioo a b \ {y : ℝ | |y| ≤ 1}
  have hzoneMeas : MeasurableSet {y : ℝ | |y| ≤ 1} :=
    measurableSet_le measurable_abs measurable_const
  have hinsideMeas : MeasurableSet inside := measurableSet_Ioo.inter hzoneMeas
  have houtsideMeas : MeasurableSet outside := measurableSet_Ioo.diff hzoneMeas
  have hinsideSub : inside ⊆ Ioo a b := inter_subset_left
  have houtsideSub : outside ⊆ Ioo a b := Set.sdiff_subset
  have hunion : inside ∪ outside = Ioo a b := by
    ext y
    simp only [inside, outside, mem_union, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
    tauto
  have hsourceDisjoint : Disjoint inside outside := by
    rw [Set.disjoint_left]
    intro y hyin hyout
    exact hyout.2 hyin.2
  have hVinj : Function.Injective V := by
    intro x y hxy
    simpa [V] using congrArg Prod.snd hxy
  have hinsideGraphMeas : MeasurableSet (V '' inside) := by
    exact measurableSet_verticalGraph_image hg hinsideMeas
  have houtsideGraphMeas : MeasurableSet (V '' outside) := by
    exact measurableSet_verticalGraph_image hg houtsideMeas
  have hendSourceMeas : MeasurableSet ({a, b} : Set ℝ) :=
    (Set.toFinite {a, b}).measurableSet
  have hendGraphMeas : MeasurableSet (V '' ({a, b} : Set ℝ)) := by
    exact measurableSet_verticalGraph_image hg hendSourceMeas
  have hinsideOutside :
      weightedTraceCost lam (V '' Ioo a b) =
        weightedTraceCost lam (V '' inside) +
          weightedTraceCost lam (V '' outside) := by
    rw [show V '' Ioo a b = V '' inside ∪ V '' outside by
      rw [← Set.image_union, hunion]]
    exact weightedTraceCost_union_eq lam houtsideGraphMeas
      (hsourceDisjoint.image hVinj.injOn (subset_univ _) (subset_univ _))
  have hendsDisjoint : Disjoint (Ioo a b) ({a, b} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro y hy hopen
    simp only [mem_insert_iff, mem_singleton_iff] at hopen
    rcases hopen with h | h
    · exact (ne_of_gt hy.1) h
    · exact (ne_of_lt hy.2) h
  have hclosedDecomp : V '' Icc a b =
      V '' Ioo a b ∪ V '' ({a, b} : Set ℝ) := by
    rw [← Set.image_union]
    congr 1
    ext y
    simp only [mem_Icc, mem_union, mem_Ioo, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hy
      rcases hy.1.eq_or_lt with rfl | hya
      · exact Or.inr (Or.inl rfl)
      · rcases hy.2.eq_or_lt with rfl | hyb
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl ⟨hya, hyb⟩
    · rintro (hy | rfl | rfl)
      · exact ⟨hy.1.le, hy.2.le⟩
      · exact ⟨le_rfl, hab.le⟩
      · exact ⟨hab.le, le_rfl⟩
  have hendMass :
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' (V '' ({a, b} : Set ℝ))) = 0 := by
    let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
      Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
    exact ((Set.toFinite {a, b}).image V).image planeEuclideanHomeomorph
      |>.measure_zero μH[1]
  have hendCost : weightedTraceCost lam (V '' ({a, b} : Set ℝ)) = 0 :=
    weightedTraceCost_eq_zero_of_hausdorffMeasure_zero lam hendMass
  have hinsideDensity :
      ∀ p ∈ V '' inside, StripDensity lam p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [V, StripDensity]
    rw [if_pos (by
      have h := hy.2
      change |y| ≤ 1 at h
      exact h)]
  have houtsideDensity :
      ∀ p ∈ V '' outside, StripDensity lam p = lam := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [V, StripDensity]
    rw [if_neg (by
      have h := hy.2
      change ¬|y| ≤ 1 at h
      exact h)]
  have hinsideCost :
      weightedTraceCost lam (V '' inside) =
        ∫⁻ y in inside,
          ENNReal.ofReal (Real.sqrt (1 + deriv g y ^ 2)) := by
    rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam 1 hinsideGraphMeas hinsideDensity,
      show planeEuclideanHomeomorph '' (V '' inside) =
          planeEuclideanHomeomorph '' ((fun y : ℝ => (g y, y)) '' inside) by
        rfl,
      hausdorffMeasure_verticalGraph_image_eq_setLIntegral hab hg hgC1 hspeed
        hinsideMeas hinsideSub]
    simp
  have houtsideCost :
      weightedTraceCost lam (V '' outside) =
        ENNReal.ofReal lam *
          ∫⁻ y in outside,
            ENNReal.ofReal (Real.sqrt (1 + deriv g y ^ 2)) := by
    rw [weightedTraceCost_eq_const_mul_hausdorff_of_measurable
      lam lam houtsideGraphMeas houtsideDensity,
      show planeEuclideanHomeomorph '' (V '' outside) =
          planeEuclideanHomeomorph '' ((fun y : ℝ => (g y, y)) '' outside) by
        rfl,
      hausdorffMeasure_verticalGraph_image_eq_setLIntegral hab hg hgC1 hspeed
        houtsideMeas houtsideSub]
  rw [show (fun y : ℝ => (g y, y)) = V by rfl, hclosedDecomp,
    weightedTraceCost_union_eq lam hendGraphMeas
      (hendsDisjoint.image hVinj.injOn (subset_univ _) (subset_univ _)),
    hendCost, add_zero, hinsideOutside, hinsideCost, houtsideCost]

/-- Exact cost of a measurable horizontal trace. -/
theorem weightedTraceCost_horizontal_image (lam h : ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    weightedTraceCost lam ((fun x : ℝ => (x, h)) '' s) =
      ENNReal.ofReal (StripDensity lam (0, h)) * volume s := by
  have hdensity :
      ∀ p ∈ (fun x : ℝ => (x, (fun _ : ℝ => h) x)) '' s,
        StripDensity lam p = StripDensity lam (0, h) := by
    rintro _ ⟨x, _hx, rfl⟩
    simp only [StripDensity]
  have hcost :=
    weightedTraceCost_graph_image_eq_const_mul_setLIntegral
      lam (StripDensity lam (0, h)) (g := fun _ : ℝ => h)
        contDiff_const hs hdensity
  simpa using hcost

/-- Exact graph-speed cost of one original left endpoint trace. -/
theorem Region.weightedTraceCost_leftGraphTrace (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    weightedTraceCost lam (R.leftGraphTrace i j) =
      (∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩ {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal (Real.sqrt (1 + deriv (R.left i j) y ^ 2))) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
            {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal (Real.sqrt (1 + deriv (R.left i j) y ^ 2)) := by
  unfold leftGraphTrace
  exact weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals lam
    (R.cuts_strict Fin.castSucc_lt_succ) (R.left_continuous i j)
      (R.left_contDiffOn i j) (R.left_speed_integrable i j)

/-- Exact graph-speed cost of one original right endpoint trace. -/
theorem Region.weightedTraceCost_rightGraphTrace (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) (j : Fin (R.componentCount i)) :
    weightedTraceCost lam (R.rightGraphTrace i j) =
      (∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩ {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal (Real.sqrt (1 + deriv (R.right i j) y ^ 2))) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
            {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal (Real.sqrt (1 + deriv (R.right i j) y ^ 2)) := by
  unfold rightGraphTrace
  exact weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals lam
    (R.cuts_strict Fin.castSucc_lt_succ) (R.right_continuous i j)
      (R.right_contDiffOn i j) (R.right_speed_integrable i j)

theorem Region.totalWidth_contDiffOn (R : Region) (i : Fin R.bandCount) :
    ContDiffOn ℝ 1 (R.totalWidth i)
      (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
  unfold totalWidth
  apply ContDiffOn.sum
  intro j _hj
  exact (R.right_contDiffOn i j).sub (R.left_contDiffOn i j)

lemma integrableOn_abs_deriv_of_speed_integrable {g : ℝ → ℝ} {s : Set ℝ}
    (h : IntegrableOn (fun y => Real.sqrt (1 + deriv g y ^ 2)) s) :
    IntegrableOn (fun y => |deriv g y|) s := by
  apply h.mono' ((measurable_deriv g).abs.aestronglyMeasurable.restrict)
  filter_upwards with y
  simp only [Real.norm_eq_abs, abs_abs]
  exact Real.abs_le_sqrt (by nlinarith)

theorem Region.totalWidth_speed_integrable (R : Region) (i : Fin R.bandCount) :
    IntegrableOn (fun y => Real.sqrt (1 + deriv (R.totalWidth i) y ^ 2))
      (Ioo (R.cuts i.castSucc) (R.cuts i.succ)) := by
  let S := Ioo (R.cuts i.castSucc) (R.cuts i.succ)
  have hright (j : Fin (R.componentCount i)) :
      IntegrableOn (fun y => |deriv (R.right i j) y|) S :=
    integrableOn_abs_deriv_of_speed_integrable (R.right_speed_integrable i j)
  have hleft (j : Fin (R.componentCount i)) :
      IntegrableOn (fun y => |deriv (R.left i j) y|) S :=
    integrableOn_abs_deriv_of_speed_integrable (R.left_speed_integrable i j)
  have hsum :
      IntegrableOn
        (fun y => ∑ j : Fin (R.componentCount i),
          (|deriv (R.right i j) y| + |deriv (R.left i j) y|)) S := by
    exact integrable_finsetSum Finset.univ fun j _ =>
      (hright j).add (hleft j)
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) S := by
    dsimp only [S]
    exact integrableOn_const measure_Ioo_lt_top.ne
  have hdom :
      IntegrableOn
        (fun y => 1 + ∑ j : Fin (R.componentCount i),
          (|deriv (R.right i j) y| + |deriv (R.left i j) y|)) S :=
    hone.add hsum
  apply hdom.mono'
  · exact (by fun_prop : Measurable
      (fun y => Real.sqrt (1 + deriv (R.totalWidth i) y ^ 2)))
      |>.aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hrightDiff (j : Fin (R.componentCount i)) :
        DifferentiableAt ℝ (R.right i j) y :=
      ((R.right_contDiffOn i j).differentiableOn (by norm_num) y hy)
        |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
    have hleftDiff (j : Fin (R.componentCount i)) :
        DifferentiableAt ℝ (R.left i j) y :=
      ((R.left_contDiffOn i j).differentiableOn (by norm_num) y hy)
        |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
    have hwidthDeriv :
        deriv (R.totalWidth i) y =
          ∑ j : Fin (R.componentCount i),
            (deriv (R.right i j) y - deriv (R.left i j) y) := by
      have hhas :
          HasDerivAt (R.totalWidth i)
            (∑ j : Fin (R.componentCount i),
              (deriv (R.right i j) y - deriv (R.left i j) y)) y := by
        rw [show R.totalWidth i =
            ∑ j : Fin (R.componentCount i),
              fun z => R.right i j z - R.left i j z by
          funext z
          simp only [Region.totalWidth, Finset.sum_apply]]
        exact HasDerivAt.sum (u := Finset.univ) (fun j _ =>
          (hrightDiff j).hasDerivAt.sub (hleftDiff j).hasDerivAt)
      exact hhas.deriv
    have hdomNonneg :
        0 ≤ 1 + ∑ j : Fin (R.componentCount i),
          (|deriv (R.right i j) y| + |deriv (R.left i j) y|) := by positivity
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      Real.sqrt (1 + deriv (R.totalWidth i) y ^ 2) ≤
          1 + |deriv (R.totalWidth i) y| := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          sqrt_one_add_norm_sq_le (deriv (R.totalWidth i) y)
      _ = 1 + |∑ j : Fin (R.componentCount i),
            (deriv (R.right i j) y - deriv (R.left i j) y)| := by
        rw [hwidthDeriv]
      _ ≤ 1 + ∑ j : Fin (R.componentCount i),
            |deriv (R.right i j) y - deriv (R.left i j) y| :=
        add_le_add_right (Finset.abs_sum_le_sum_abs
          (fun j : Fin (R.componentCount i) =>
            deriv (R.right i j) y - deriv (R.left i j) y) Finset.univ) 1
      _ ≤ 1 + ∑ j : Fin (R.componentCount i),
            (|deriv (R.right i j) y| + |deriv (R.left i j) y|) := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro j _hj
        exact abs_sub _ _

theorem Region.weightedTraceCost_centeredLeftGraphTrace (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) :
    weightedTraceCost lam (R.centeredLeftGraphTrace i) =
      (∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩ {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal
          (Real.sqrt (1 + deriv (fun y => -R.totalWidth i y / 2) y ^ 2))) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
            {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal
            (Real.sqrt (1 + deriv (fun y => -R.totalWidth i y / 2) y ^ 2)) := by
  unfold centeredLeftGraphTrace
  apply weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals lam
    (R.cuts_strict Fin.castSucc_lt_succ)
  · exact (R.continuous_totalWidth i).neg.div_const 2
  · exact (R.totalWidth_contDiffOn i).neg.div_const 2
  · have hspeed := R.totalWidth_speed_integrable i
    apply hspeed.mono'
    · exact (by fun_prop : Measurable
        (fun y => Real.sqrt
          (1 + deriv (fun y => -R.totalWidth i y / 2) y ^ 2)))
        |>.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      have hdiff :=
        ((R.totalWidth_contDiffOn i).differentiableOn (by norm_num) y hy)
          |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
      have hscaled :
          HasDerivAt (fun y => -R.totalWidth i y / 2)
            (-deriv (R.totalWidth i) y / 2) y :=
        hdiff.hasDerivAt.neg.div_const 2
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hscaled.deriv]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (deriv (R.totalWidth i) y)]

theorem Region.weightedTraceCost_centeredRightGraphTrace (R : Region) (lam : ℝ)
    (i : Fin R.bandCount) :
    weightedTraceCost lam (R.centeredRightGraphTrace i) =
      (∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) ∩ {y : ℝ | |y| ≤ 1},
        ENNReal.ofReal
          (Real.sqrt (1 + deriv (fun y => R.totalWidth i y / 2) y ^ 2))) +
      ENNReal.ofReal lam *
        ∫⁻ y in Ioo (R.cuts i.castSucc) (R.cuts i.succ) \
            {y : ℝ | |y| ≤ 1},
          ENNReal.ofReal
            (Real.sqrt (1 + deriv (fun y => R.totalWidth i y / 2) y ^ 2)) := by
  unfold centeredRightGraphTrace
  apply weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals lam
    (R.cuts_strict Fin.castSucc_lt_succ)
  · exact (R.continuous_totalWidth i).div_const 2
  · exact (R.totalWidth_contDiffOn i).div_const 2
  · have hspeed := R.totalWidth_speed_integrable i
    apply hspeed.mono'
    · exact (by fun_prop : Measurable
        (fun y => Real.sqrt
          (1 + deriv (fun y => R.totalWidth i y / 2) y ^ 2)))
        |>.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      have hdiff :=
        ((R.totalWidth_contDiffOn i).differentiableOn (by norm_num) y hy)
          |>.differentiableAt (isOpen_Ioo.mem_nhds hy)
      have hscaled :
          HasDerivAt (fun y => R.totalWidth i y / 2)
            (deriv (R.totalWidth i) y / 2) y :=
        hdiff.hasDerivAt.div_const 2
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [hscaled.deriv]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (deriv (R.totalWidth i) y)]

/-- A graph band over a compact height set is bounded whenever both endpoint
graphs are continuous. -/
lemma isBounded_closedHorizontalGraphBand {g h : ℝ → ℝ} {s : Set ℝ}
    (hg : Continuous g) (hh : Continuous h) (hs : IsCompact s) :
    Bornology.IsBounded
      (FiniteJunctionRepair.closedHorizontalGraphBand g h s) := by
  obtain ⟨Mg, hMg⟩ := bddAbove_def.mp
    (hs.bddAbove_image hg.abs.continuousOn)
  obtain ⟨Mh, hMh⟩ := bddAbove_def.mp
    (hs.bddAbove_image hh.abs.continuousOn)
  let M := max 0 (max Mg Mh)
  have hsub :
      FiniteJunctionRepair.closedHorizontalGraphBand g h s ⊆
        Icc (-M) M ×ˢ s := by
    intro p hp
    change p.2 ∈ s ∧
      p.1 ∈ Icc (min (g p.2) (h p.2)) (max (g p.2) (h p.2)) at hp
    have hgM : |g p.2| ≤ M :=
      (hMg _ ⟨p.2, hp.1, rfl⟩).trans
        ((le_max_left Mg Mh).trans (le_max_right 0 (max Mg Mh)))
    have hhM : |h p.2| ≤ M :=
      (hMh _ ⟨p.2, hp.1, rfl⟩).trans
        ((le_max_right Mg Mh).trans (le_max_right 0 (max Mg Mh)))
    exact ⟨⟨(le_min (abs_le.mp hgM).1 (abs_le.mp hhM).1).trans hp.2.1,
      hp.2.2.trans (max_le (abs_le.mp hgM).2 (abs_le.mp hhM).2)⟩, hp.1⟩
  exact (isCompact_Icc.prod hs).isBounded.subset hsub

theorem Region.isBounded_componentCarrier (R : Region) (i : Fin R.bandCount)
    (j : Fin (R.componentCount i)) :
    Bornology.IsBounded (R.componentCarrier i j) :=
  isBounded_closedHorizontalGraphBand (R.left_continuous i j)
    (R.right_continuous i j) isCompact_Icc

theorem Region.isBounded_bandCarrier (R : Region) (i : Fin R.bandCount) :
    Bornology.IsBounded (R.bandCarrier i) := by
  rw [Region.bandCarrier, Bornology.isBounded_iUnion]
  exact fun j => R.isBounded_componentCarrier i j

theorem Region.isBounded_carrier (R : Region) :
    Bornology.IsBounded R.carrier := by
  rw [Region.carrier, Bornology.isBounded_iUnion]
  exact R.isBounded_bandCarrier

theorem Region.isBounded_centeredBandCarrier (R : Region)
    (i : Fin R.bandCount) :
    Bornology.IsBounded (R.centeredBandCarrier i) := by
  apply isBounded_closedHorizontalGraphBand
      (s := Icc (R.cuts i.castSucc) (R.cuts i.succ))
  · exact (R.continuous_totalWidth i).neg.div_const 2
  · exact (R.continuous_totalWidth i).div_const 2
  · exact isCompact_Icc

theorem Region.isBounded_centeredCarrier (R : Region) :
    Bornology.IsBounded R.centeredCarrier := by
  rw [Region.centeredCarrier, Bornology.isBounded_iUnion]
  exact R.isBounded_centeredBandCarrier

/-- Every finite-band carrier has finite weighted area.  Boundedness is derived
from the finite family of continuous endpoint graphs; no perimeter or source
minimality premise is used. -/
theorem Region.integrableOn_carrier (R : Region) (lam : ℝ) :
    IntegrableOn (StripDensity lam) R.carrier :=
  stripDensity_integrableOn_of_volume_ne_top lam
    R.isBounded_carrier.measure_lt_top.ne

/-- The centered finite-band competitor likewise has finite weighted area. -/
theorem Region.integrableOn_centeredCarrier (R : Region) (lam : ℝ) :
    IntegrableOn (StripDensity lam) R.centeredCarrier :=
  stripDensity_integrableOn_of_volume_ne_top lam
    R.isBounded_centeredCarrier.measure_lt_top.ne

/-- Fubini formula for strip density: because the density depends only on
height, the planar weighted area is the integral of density times horizontal
section measure. -/
theorem weightedArea_eq_integral_horizontalSections (lam : ℝ) {s : Set PlanePoint}
    (hs : MeasurableSet s) (hfinite : volume s ≠ ⊤) :
    WeightedArea lam s =
      ∫ y : ℝ, StripDensity lam (0, y) *
        volume.real (horizontalSection s y) := by
  have hint : Integrable (s.indicator (StripDensity lam)) :=
    (stripDensity_integrableOn_of_volume_ne_top lam hfinite).integrable_indicator hs
  rw [WeightedArea, ← integral_indicator hs, Measure.volume_eq_prod ℝ ℝ,
    ← integral_prod_swap]
  change (∫ z : ℝ × ℝ,
      (s.indicator (StripDensity lam) ∘ Prod.swap) z ∂volume.prod volume) = _
  have hswap :
      Integrable (s.indicator (StripDensity lam) ∘ Prod.swap)
        (volume.prod volume) :=
    Measure.measurePreserving_swap.integrable_comp_of_integrable hint
  rw [integral_prod _ hswap]
  apply integral_congr_ae
  filter_upwards with y
  have hsection : MeasurableSet (horizontalSection s y) :=
    hs.preimage (by fun_prop)
  have hfun :
      (fun x : ℝ => s.indicator (StripDensity lam) (x, y)) =
        (horizontalSection s y).indicator
          (fun _ : ℝ => StripDensity lam (0, y)) := by
    funext x
    by_cases hx : (x, y) ∈ s
    · simp only [Set.indicator_of_mem hx]
      rw [Set.indicator_of_mem]
      · simp only [StripDensity]
      · exact hx
    · simp only [Set.indicator_of_notMem hx]
      rw [Set.indicator_of_notMem]
      exact hx
  change (∫ x : ℝ, s.indicator (StripDensity lam) (x, y)) =
    StripDensity lam (0, y) * volume.real (horizontalSection s y)
  rw [hfun, integral_indicator_const _ hsection]
  simp only [smul_eq_mul]
  ring

/-- At an interior height, distinct component intervals are genuinely disjoint;
the endpoint inequalities are strict there. -/
lemma pairwise_disjoint_componentIntervals (R : Region) (i : Fin R.bandCount)
    {y : ℝ} (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    Pairwise (Disjoint on fun j : Fin (R.componentCount i) =>
      Icc (R.left i j y) (R.right i j y)) := by
  intro j k hjk
  change Disjoint (Icc (R.left i j y) (R.right i j y))
    (Icc (R.left i k y) (R.right i k y))
  rw [Set.disjoint_left]
  intro x hxj hxk
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · have hsep := R.components_strict i hjk y hy
    exact (not_lt_of_ge hxk.1) (lt_of_le_of_lt hxj.2 hsep)
  · have hsep := R.components_strict i hkj y hy
    exact (not_lt_of_ge hxj.1) (lt_of_le_of_lt hxk.2 hsep)

/-- The interior horizontal section measure is exactly the componentwise total
width. -/
theorem volume_fiber (R : Region) (i : Fin R.bandCount) {y : ℝ}
    (hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    volume (R.fiber i y) = ENNReal.ofReal (R.totalWidth i y) := by
  rw [Region.fiber, measure_iUnion (pairwise_disjoint_componentIntervals R i hy)
    (fun _ => measurableSet_Icc), tsum_fintype]
  simp_rw [Real.volume_Icc]
  rw [Region.totalWidth, ENNReal.ofReal_sum_of_nonneg]
  intro j _
  exact sub_nonneg.mpr (R.width_nonneg i j y ⟨hy.1.le, hy.2.le⟩)

/-- Centering preserves the exact interior horizontal section measure. -/
theorem volume_centeredFiber (R : Region) (i : Fin R.bandCount) {y : ℝ}
    (_hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ)) :
    volume (R.centeredFiber i y) = ENNReal.ofReal (R.totalWidth i y) := by
  rw [Region.centeredFiber, Real.volume_Icc]
  congr 1
  ring

/-- Away from the finite cut set, two distinct closed height bands cannot both
be active. -/
lemma not_mem_both_bandIntervals_of_not_mem_cuts (R : Region) {y : ℝ}
    (hcuts : y ∉ Set.range R.cuts) {i k : Fin R.bandCount} (hik : i ≠ k) :
    ¬(y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) ∧
      y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ)) := by
  rintro ⟨hi, hk⟩
  rcases lt_or_gt_of_ne hik with hik | hki
  · have hidx : i.succ ≤ k.castSucc := by
      apply Fin.mk_le_mk.mpr
      omega
    have hicut : y < R.cuts i.succ := lt_of_le_of_ne hi.2 fun h => by
      apply hcuts
      exact ⟨i.succ, h.symm⟩
    have hkcut : R.cuts k.castSucc < y := lt_of_le_of_ne hk.1 fun h => by
      apply hcuts
      exact ⟨k.castSucc, h⟩
    linarith [R.cuts_strict.monotone hidx]
  · have hidx : k.succ ≤ i.castSucc := by
      apply Fin.mk_le_mk.mpr
      omega
    have hkcut : y < R.cuts k.succ := lt_of_le_of_ne hk.2 fun h => by
      apply hcuts
      exact ⟨k.succ, h.symm⟩
    have hicut : R.cuts i.castSucc < y := lt_of_le_of_ne hi.1 fun h => by
      apply hcuts
      exact ⟨i.castSucc, h⟩
    linarith [R.cuts_strict.monotone hidx]

lemma pairwise_disjoint_activeBandSets (R : Region) {y : ℝ}
    (hcuts : y ∉ Set.range R.cuts)
    (A : (i : Fin R.bandCount) → Set ℝ) :
    Pairwise (Disjoint on fun i =>
      if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then A i else ∅) := by
  intro i k hik
  change Disjoint
    (if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then A i else ∅)
    (if y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ) then A k else ∅)
  by_cases hi : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)
  · by_cases hk : y ∈ Icc (R.cuts k.castSucc) (R.cuts k.succ)
    · exact (not_mem_both_bandIntervals_of_not_mem_cuts R hcuts hik
        ⟨hi, hk⟩).elim
    · simp only [hi, hk, if_true, if_false, disjoint_empty]
  · simp only [hi, if_false, empty_disjoint]

/-- Original and centered carriers have equal horizontal section measure at
every height except the finite cut set. -/
theorem volume_horizontalSection_carrier_eq_centeredCarrier (R : Region) {y : ℝ}
    (hcuts : y ∉ Set.range R.cuts) :
    volume (horizontalSection R.carrier y) =
      volume (horizontalSection R.centeredCarrier y) := by
  let O : Fin R.bandCount → Set ℝ := fun i =>
    if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then R.fiber i y else ∅
  let C : Fin R.bandCount → Set ℝ := fun i =>
    if y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ) then R.centeredFiber i y else ∅
  have hOdisjoint : Pairwise (Disjoint on O) :=
    pairwise_disjoint_activeBandSets R hcuts (fun i => R.fiber i y)
  have hCdisjoint : Pairwise (Disjoint on C) :=
    pairwise_disjoint_activeBandSets R hcuts (fun i => R.centeredFiber i y)
  have hOmeas : ∀ i, MeasurableSet (O i) := by
    intro i
    dsimp only [O]
    split_ifs
    · exact (R.isClosed_fiber i y).measurableSet
    · exact MeasurableSet.empty
  have hCmeas : ∀ i, MeasurableSet (C i) := by
    intro i
    dsimp only [C]
    split_ifs
    · exact measurableSet_Icc
    · exact MeasurableSet.empty
  have hterm : ∀ i, volume (O i) = volume (C i) := by
    intro i
    by_cases hi : y ∈ Icc (R.cuts i.castSucc) (R.cuts i.succ)
    · have hy : y ∈ Ioo (R.cuts i.castSucc) (R.cuts i.succ) := by
        refine ⟨lt_of_le_of_ne hi.1 ?_, lt_of_le_of_ne hi.2 ?_⟩
        · intro h
          apply hcuts
          exact ⟨i.castSucc, h⟩
        · intro h
          apply hcuts
          exact ⟨i.succ, h.symm⟩
      dsimp only [O, C]
      rw [if_pos hi, if_pos hi, volume_fiber R i hy,
        volume_centeredFiber R i hy]
    · simp only [O, C, hi, if_false]
  calc
    volume (horizontalSection R.carrier y) =
        volume (⋃ i, O i) := by rw [R.horizontalSection_carrier]
    _ = ∑' i, volume (O i) := measure_iUnion hOdisjoint hOmeas
    _ = ∑' i, volume (C i) := tsum_congr hterm
    _ = volume (⋃ i, C i) := (measure_iUnion hCdisjoint hCmeas).symm
    _ = volume (horizontalSection R.centeredCarrier y) := by
      rw [R.horizontalSection_centeredCarrier]

/-- Exact weighted-area preservation for the literal finite-band carrier and
its centered rearrangement. -/
theorem weightedArea_carrier_eq_centeredCarrier (R : Region) (lam : ℝ) :
    WeightedArea lam R.carrier = WeightedArea lam R.centeredCarrier := by
  rw [weightedArea_eq_integral_horizontalSections lam R.isClosed_carrier.measurableSet
      R.isBounded_carrier.measure_lt_top.ne,
    weightedArea_eq_integral_horizontalSections lam
      R.isClosed_centeredCarrier.measurableSet
      R.isBounded_centeredCarrier.measure_lt_top.ne]
  apply integral_congr_ae
  have hcutsZero : volume (Set.range R.cuts) = 0 :=
    (Set.finite_range R.cuts).measure_zero volume
  have hcutsAE : ∀ᵐ y : ℝ ∂volume, y ∉ Set.range R.cuts := by
    rw [ae_iff]
    simpa only [Set.ofPred_mem_eq, not_not] using hcutsZero
  filter_upwards [hcutsAE] with y hy
  simp only [measureReal_def]
  rw [volume_horizontalSection_carrier_eq_centeredCarrier R hy]

/-- Right half of the unit circle as a height-oriented graph.  Its endpoint
slopes are singular although its graph speed is integrable. -/
def circularPoleGraph (y : ℝ) : ℝ := Real.sqrt (1 - y ^ 2)

lemma continuous_circularPoleGraph : Continuous circularPoleGraph := by
  unfold circularPoleGraph
  fun_prop

lemma circularPoleGraph_contDiffOn :
    ContDiffOn ℝ 1 circularPoleGraph (Ioo (-1) 1) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro y hy
  have hpos : 0 < 1 - y ^ 2 := by
    have hleft : 0 < y + 1 := by linarith [hy.1]
    have hright : 0 < 1 - y := by linarith [hy.2]
    nlinarith [mul_pos hleft hright]
  unfold circularPoleGraph
  have hinner : ContDiffAt ℝ 1 (fun z : ℝ => 1 - z ^ 2) y := by fun_prop
  exact hinner.sqrt (ne_of_gt hpos)

lemma deriv_circularPoleGraph {y : ℝ} (hy : y ∈ Ioo (-1) 1) :
    deriv circularPoleGraph y = -y / Real.sqrt (1 - y ^ 2) := by
  have hpos : 0 < 1 - y ^ 2 := by
    have hleft : 0 < y + 1 := by linarith [hy.1]
    have hright : 0 < 1 - y := by linarith [hy.2]
    nlinarith [mul_pos hleft hright]
  have hinner : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * y) y := by
    change HasDerivAt ((fun _ : ℝ => 1) - id ^ 2) (-2 * y) y
    simpa [mul_comm] using
      (hasDerivAt_const y 1).sub ((hasDerivAt_id y).pow 2)
  have hsqrt := hinner.sqrt (ne_of_gt hpos)
  rw [show circularPoleGraph = fun z : ℝ => Real.sqrt (1 - z ^ 2) by rfl,
    hsqrt.deriv]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hpos)]

lemma circularPoleGraph_speed {y : ℝ} (hy : y ∈ Ioo (-1) 1) :
    Real.sqrt (1 + deriv circularPoleGraph y ^ 2) =
      Real.sqrt ((1 - y ^ 2)⁻¹) := by
  rw [Real.sqrt_inv]
  rw [deriv_circularPoleGraph hy]
  have hq : 0 ≤ 1 - y ^ 2 := by
    have hleft : 0 ≤ y + 1 := by linarith [hy.1]
    have hright : 0 ≤ 1 - y := by linarith [hy.2]
    nlinarith [mul_nonneg hleft hright]
  have hspos : 0 < Real.sqrt (1 - y ^ 2) :=
    Real.sqrt_pos.2 (lt_of_le_of_ne hq (by nlinarith [hy.1, hy.2]))
  have hinside :
      1 + (-y / Real.sqrt (1 - y ^ 2)) ^ 2 =
        ((Real.sqrt (1 - y ^ 2))⁻¹) ^ 2 := by
    field_simp [ne_of_gt hspos]
    nlinarith [Real.sq_sqrt hq]
  rw [hinside, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hspos)]

lemma circularPoleGraph_speed_integrable :
    IntegrableOn (fun y => Real.sqrt (1 + deriv circularPoleGraph y ^ 2))
      (Ioo (-1) 1) := by
  have hinv : IntegrableOn (fun y : ℝ => Real.sqrt ((1 - y ^ 2)⁻¹))
      (Ioo (-1) 1) := by
    have h := Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
    exact h.mono_set Ioo_subset_Icc_self
  apply hinv.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (circularPoleGraph_speed hy).symm

/-- The concrete circular graph instantiates the compact-exhaustion theorem,
so endpoint slope singularities are not silently excluded. -/
theorem hausdorffMeasure_circularPoleGraph :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun y : ℝ => (circularPoleGraph y, y)) '' Icc (-1) 1)) =
      ENNReal.ofReal
        (∫ y in Ioo (-1) 1,
          Real.sqrt (1 + deriv circularPoleGraph y ^ 2)) :=
  hausdorffMeasure_verticalGraph_Icc_eq_setLIntegral (by norm_num)
    continuous_circularPoleGraph circularPoleGraph_contDiffOn
    circularPoleGraph_speed_integrable

/-- The circular-pole graph lies entirely in the density-one strip, so its
exact weighted cost is independent of the exterior density. -/
theorem weightedTraceCost_circularPoleGraph (lam : ℝ) :
    weightedTraceCost lam
        ((fun y : ℝ => (circularPoleGraph y, y)) '' Icc (-1) 1) =
      ∫⁻ y in Ioo (-1) 1,
        ENNReal.ofReal (Real.sqrt (1 + deriv circularPoleGraph y ^ 2)) := by
  have hsub : Ioo (-1 : ℝ) 1 ⊆ {y : ℝ | |y| ≤ 1} := by
    intro y hy
    exact abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  have hinside :
      Ioo (-1 : ℝ) 1 ∩ {y : ℝ | |y| ≤ 1} = Ioo (-1) 1 :=
    inter_eq_left.mpr hsub
  have houtside :
      Ioo (-1 : ℝ) 1 \ {y : ℝ | |y| ≤ 1} = ∅ :=
    sdiff_eq_empty.2 hsub
  simpa only [hinside, houtside, setLIntegral_empty, mul_zero, add_zero] using
    weightedTraceCost_verticalGraph_Icc_eq_zoneIntegrals lam
      (g := circularPoleGraph) (by norm_num) continuous_circularPoleGraph
        circularPoleGraph_contDiffOn circularPoleGraph_speed_integrable

/-- The circular graph's right-end slope diverges to negative infinity. -/
theorem neg_deriv_circularPoleGraph_tendsto_atTop :
    Tendsto (fun y : ℝ => -deriv circularPoleGraph y) (𝓝[<] (1 : ℝ)) atTop := by
  have hnum : Tendsto (fun y : ℝ => y) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
    Tendsto.mono_left tendsto_id nhdsWithin_le_nhds
  have hpos : ∀ᶠ y : ℝ in 𝓝[<] (1 : ℝ), 0 < y :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds
  have hlt : ∀ᶠ y : ℝ in 𝓝[<] (1 : ℝ), y < 1 :=
    eventually_mem_nhdsWithin
  have hq : Tendsto (fun y : ℝ => 1 - y ^ 2)
      (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      exact (continuous_const.sub (continuous_id.pow 2)).tendsto' 1 0 (by norm_num)
    · filter_upwards [hpos, hlt] with y hy0 hy1
      simp only [mem_Ioi]
      nlinarith [mul_pos hy0 (by linarith : 0 < 1 + y)]
  have hsqrt : Tendsto (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · change Tendsto
        ((fun x : ℝ => Real.sqrt x) ∘ (fun y : ℝ => 1 - y ^ 2))
        (𝓝[<] (1 : ℝ)) (𝓝 0)
      simpa only [Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp
          (hq.mono_right nhdsWithin_le_nhds)
    · filter_upwards [hpos, hlt] with y hy0 hy1
      simp only [mem_Ioi]
      exact Real.sqrt_pos.2 (by
        nlinarith [mul_pos hy0 (by linarith : 0 < 1 + y)])
  have hprod := Filter.Tendsto.pos_mul_atTop (by norm_num : (0 : ℝ) < 1)
    hnum hsqrt.inv_tendsto_nhdsGT_zero
  apply hprod.congr'
  filter_upwards [hpos, hlt] with y hy0 hy1
  rw [deriv_circularPoleGraph ⟨by linarith, hy1⟩]
  simp only [Pi.inv_apply, neg_div, neg_neg]
  rw [div_eq_mul_inv]
end FiniteBandRearrangement
end CMVRelaxation
