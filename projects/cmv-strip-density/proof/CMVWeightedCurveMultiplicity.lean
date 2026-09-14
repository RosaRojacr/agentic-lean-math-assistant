import CMVRelativeLevelTraceAveraging
import Mathlib.Topology.Bases

/-!
# Weighted projection multiplicity for regular curve pieces

This module develops the one-dimensional area-formula core used by the sharp
Crofton route.  Critical parameters are removed only after their Jacobian is
proved to vanish.  The remaining source is covered by countably many genuinely
injective derivative-sign windows and then measurably disjointized, so repeated
projection crossings survive as separate summands.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology ContDiff BigOperators

noncomputable section

namespace CMVRelaxation
namespace WeightedCurveMultiplicity

/-- Parameters at which the scalar projection has nonzero derivative. -/
def regularSource (f : ℝ → ℝ) : Set ℝ :=
  {x | deriv f x ≠ 0}

/-- Source parameters in a fixed scalar projection fiber. -/
def projectionFiber (f : ℝ → ℝ) (source : Set ℝ) (y : ℝ) : Set ℝ :=
  source ∩ f ⁻¹' {y}

/-- Intrinsic weighted crossing multiplicity.  The fiber-indexed `ENNReal`
sum retains infinite critical fibers instead of mapping them to zero. -/
noncomputable def weightedFiberMultiplicity
    (f : ℝ → ℝ) (source : Set ℝ) (weight : ℝ → ℝ≥0∞)
    (y : ℝ) : ℝ≥0∞ :=
  ∑' x : projectionFiber f source y, weight x

lemma isOpen_regularSource {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    IsOpen (regularSource f) := by
  change IsOpen ((deriv f) ⁻¹' {y : ℝ | y ≠ 0})
  exact isOpen_ne.preimage (hf.continuous_deriv (by norm_num))

/-- A countable, measurable, disjoint decomposition of a measurable parameter
set away from critical parameters.  Injectivity is derived from local strict
monotonicity; it is not a premise of the eventual multiplicity formula. -/
theorem exists_countable_disjoint_injective_decomposition
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∃ branch : ℕ → Set ℝ,
      (∀ n, MeasurableSet (branch n)) ∧
      Pairwise (Disjoint on branch) ∧
      (⋃ n, branch n) = s ∩ regularSource f ∧
      (∀ n, InjOn f (branch n)) := by
  classical
  let R : Set ℝ := regularSource f
  have hRopen : IsOpen R := isOpen_regularSource hf
  by_cases hRne : R.Nonempty
  · let localSign : R → Set ℝ := fun x =>
      if 0 < deriv f x then {y | 0 < deriv f y} else {y | deriv f y < 0}
    have hlocalOpen : ∀ x : R, IsOpen (localSign x) := by
      intro x
      by_cases hx : 0 < deriv f x
      · simp only [localSign, if_pos hx]
        exact isOpen_lt continuous_const (hf.continuous_deriv (by norm_num))
      · simp only [localSign, if_neg hx]
        exact isOpen_lt (hf.continuous_deriv (by norm_num)) continuous_const
    have hxlocal : ∀ x : R, (x : ℝ) ∈ localSign x := by
      intro x
      by_cases hx : 0 < deriv f x
      · simpa only [localSign, if_pos hx, mem_ofPred_eq] using hx
      · have hxneg : deriv f x < 0 :=
          lt_of_le_of_ne (le_of_not_gt hx) x.property
        simpa only [localSign, if_neg hx, mem_ofPred_eq] using hxneg
    have hinterval : ∀ x : R, ∃ a b : ℝ,
        (x : ℝ) ∈ Ioo a b ∧ Ioo a b ⊆ localSign x := by
      intro x
      exact mem_nhds_iff_exists_Ioo_subset.mp
        ((hlocalOpen x).mem_nhds (hxlocal x))
    choose a b hxab hab using hinterval
    let window : R → Set ℝ := fun x => Ioo (a x) (b x)
    have hwindowOpen : ∀ x : R, IsOpen (window x) := fun _ => isOpen_Ioo
    have hxwindow : ∀ x : R, (x : ℝ) ∈ window x := fun x => hxab x
    have hwindowR : ∀ x : R, window x ⊆ R := by
      intro x y hy
      have hysign := hab x hy
      by_cases hx : 0 < deriv f x
      · have : 0 < deriv f y := by
          simpa only [localSign, if_pos hx, mem_ofPred_eq] using hysign
        exact this.ne'
      · have : deriv f y < 0 := by
          simpa only [localSign, if_neg hx, mem_ofPred_eq] using hysign
        exact this.ne
    have hwindowInj : ∀ x : R, InjOn f (window x) := by
      intro x
      by_cases hx : 0 < deriv f x
      · have hpos : ∀ y ∈ interior (window x), 0 < deriv f y := by
          intro y hy
          have hysign := hab x (show y ∈ window x by simpa [window] using hy)
          simpa only [localSign, if_pos hx, mem_ofPred_eq] using hysign
        exact (strictMonoOn_of_deriv_pos (convex_Ioo (a x) (b x))
          hf.continuous.continuousOn hpos).injOn
      · have hneg : ∀ y ∈ interior (window x), deriv f y < 0 := by
          intro y hy
          have hysign := hab x (show y ∈ window x by simpa [window] using hy)
          simpa only [localSign, if_neg hx, mem_ofPred_eq] using hysign
        exact (strictAntiOn_of_deriv_neg (convex_Ioo (a x) (b x))
          hf.continuous.continuousOn hneg).injOn
    have hUnionWindow : (⋃ x : R, window x) = R := by
      apply Subset.antisymm
      · exact iUnion_subset hwindowR
      · intro x hx
        exact mem_iUnion.2 ⟨⟨x, hx⟩, hxwindow ⟨x, hx⟩⟩
    obtain ⟨T, hTcount, hTunion⟩ :=
      TopologicalSpace.isOpen_iUnion_countable window hwindowOpen
    let _ : Nonempty R := hRne.to_subtype
    obtain ⟨e : ℕ → R, he⟩ :=
      Set.countable_iff_exists_subset_range.mp hTcount
    have hUnionEnum : (⋃ n : ℕ, window (e n)) = R := by
      apply Subset.antisymm
      · exact iUnion_subset fun n => hwindowR (e n)
      · rw [← hUnionWindow, ← hTunion]
        intro x hx
        simp only [mem_iUnion] at hx ⊢
        obtain ⟨i, hiT, hxi⟩ := hx
        obtain ⟨n, hn⟩ := he hiT
        exact ⟨n, hn ▸ hxi⟩
    let base : ℕ → Set ℝ := fun n => s ∩ window (e n)
    let branch : ℕ → Set ℝ := disjointed base
    refine ⟨branch, ?_, disjoint_disjointed base, ?_, ?_⟩
    · intro n
      exact MeasurableSet.disjointed
        (fun m => hs.inter (hwindowOpen (e m)).measurableSet) n
    · rw [show (⋃ n, branch n) = ⋃ n, base n by
          exact iUnion_disjointed]
      simp only [base, ← inter_iUnion, hUnionEnum]
      rfl
    · intro n
      exact (hwindowInj (e n)).mono
        ((disjointed_subset base n).trans inter_subset_right)
  · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hRne
    refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, ?_, ?_, ?_⟩
    · intro i j hij
      simp only [onFun]
      exact Set.disjoint_empty (∅ : Set ℝ)
    · change (⋃ _n : ℕ, (∅ : Set ℝ)) = s ∩ R
      simp only [iUnion_empty, hRempty, inter_empty]
    · intro n
      change InjOn f ∅
      exact injOn_empty f

/-- The critical projection values are Lebesgue-null.  This is a one-dimensional
Jacobian theorem, not an assertion that the critical part of the curve has
zero Hausdorff length. -/
theorem volume_image_criticalSource_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (s : Set ℝ) :
    volume (f '' (s ∩ (regularSource f)ᶜ)) = 0 := by
  apply CMVRelaxation.volume_image_critical_eq_zero
  · intro x hx
    exact (hf.differentiable (by norm_num) x).hasDerivAt.hasDerivWithinAt
  · intro x hx
    simpa only [regularSource, mem_inter_iff, mem_compl_iff,
      mem_ofPred_eq, not_not] using hx.2

/-- The measurable contribution of one injective projection branch.  On the
branch image it is the source weight transported by the unique inverse; it is
zero off that image. -/
noncomputable def branchCrossingWeight
    (f : ℝ → ℝ) (branch : Set ℝ) (weight : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  Function.extend (branch.domRestrict f)
    (fun x : branch => weight x) (fun _ => 0)

lemma branchCrossingWeight_apply
    {f : ℝ → ℝ} {branch : Set ℝ} {weight : ℝ → ℝ≥0∞}
    (hinj : InjOn f branch) {x : ℝ} (hx : x ∈ branch) :
    branchCrossingWeight f branch weight (f x) = weight x := by
  have hdom : Function.Injective (branch.domRestrict f) :=
    injOn_iff_injective.mp hinj
  change Function.extend (branch.domRestrict f)
      (fun z : branch => weight z) (fun _ => 0)
      (branch.domRestrict f ⟨x, hx⟩) = weight x
  exact hdom.extend_apply (fun z : branch => weight z) (fun _ => 0) ⟨x, hx⟩

lemma branchCrossingWeight_eq_zero_of_not_mem_image
    {f : ℝ → ℝ} {branch : Set ℝ} {weight : ℝ → ℝ≥0∞}
    {y : ℝ} (hy : y ∉ f '' branch) :
    branchCrossingWeight f branch weight y = 0 := by
  have hnone : ¬ ∃ x : branch, branch.domRestrict f x = y := by
    rintro ⟨⟨x, hx⟩, hxy⟩
    exact hy ⟨x, hx, hxy⟩
  exact Function.extend_apply' _ _ _ hnone

lemma branchCrossingWeight_support_subset
    (f : ℝ → ℝ) (branch : Set ℝ) (weight : ℝ → ℝ≥0∞) :
    Function.support (branchCrossingWeight f branch weight) ⊆ f '' branch := by
  intro y hy
  by_contra hnot
  exact hy (branchCrossingWeight_eq_zero_of_not_mem_image hnot)

lemma measurable_branchCrossingWeight
    {f : ℝ → ℝ} (hf : Continuous f) {branch : Set ℝ}
    (hbranch : MeasurableSet branch) (hinj : InjOn f branch)
    {weight : ℝ → ℝ≥0∞} (hweight : Measurable weight) :
    Measurable (branchCrossingWeight f branch weight) := by
  have hembed : MeasurableEmbedding (branch.domRestrict f) :=
    hf.continuousOn.measurableEmbedding hbranch hinj
  exact (hembed.stronglyMeasurable_extend
    (hweight.comp measurable_subtype_coe).stronglyMeasurable
    stronglyMeasurable_const).measurable

lemma branchCrossingWeight_eq_fiber_tsum
    {f : ℝ → ℝ} {branch : Set ℝ} {weight : ℝ → ℝ≥0∞}
    (hinj : InjOn f branch) (y : ℝ) :
    branchCrossingWeight f branch weight y =
      ∑' x : projectionFiber f branch y, weight x := by
  classical
  by_cases hfiber : ∃ x, x ∈ branch ∧ f x = y
  · obtain ⟨x, hx, hxy⟩ := hfiber
    calc
      branchCrossingWeight f branch weight y = weight x := by
        rw [← hxy]
        exact branchCrossingWeight_apply hinj hx
      _ = ∑' z : projectionFiber f branch y, weight z := by
        symm
        rw [tsum_eq_single (⟨x, hx, by simpa using hxy⟩ :
          projectionFiber f branch y)]
        intro z hz
        exfalso
        apply hz
        apply Subtype.ext
        apply hinj z.property.1 hx
        have hzy : f z = y := by simpa using z.property.2
        exact hzy.trans hxy.symm
  · rw [branchCrossingWeight_eq_zero_of_not_mem_image]
    · have hempty : projectionFiber f branch y = ∅ := by
        ext z
        simp only [projectionFiber, mem_inter_iff, mem_preimage,
          mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun hz hzy => hfiber ⟨z, hz, hzy⟩
      rw [hempty]
      simp
    · rintro ⟨x, hx, hxy⟩
      exact hfiber ⟨x, hx, hxy⟩

/-- Exact weighted one-dimensional area formula on one injective branch. -/
theorem lintegral_branchCrossingWeight
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {branch : Set ℝ}
    (hbranch : MeasurableSet branch) (hinj : InjOn f branch)
    (weight : ℝ → ℝ≥0∞) :
    ∫⁻ y, branchCrossingWeight f branch weight y =
      ∫⁻ x in branch, ENNReal.ofReal |deriv f x| * weight x := by
  rw [← setLIntegral_eq_of_support_subset
    (branchCrossingWeight_support_subset f branch weight)]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hbranch
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt.hasDerivWithinAt)
    hinj]
  apply setLIntegral_congr_fun hbranch
  intro x hx
  change ENNReal.ofReal |deriv f x| *
      branchCrossingWeight f branch weight (f x) =
    ENNReal.ofReal |deriv f x| * weight x
  rw [branchCrossingWeight_apply hinj hx]

/-- A branch-resolved multiplicity integrand.  Every repeated crossing is kept:
different disjoint source branches contribute different terms at the same
offset. -/
noncomputable def crossingMultiplicity
    (f : ℝ → ℝ) (branch : ℕ → Set ℝ) (weight : ℝ → ℝ≥0∞)
    (y : ℝ) : ℝ≥0∞ :=
  ∑' n, branchCrossingWeight f (branch n) weight y

lemma measurable_crossingMultiplicity
    {f : ℝ → ℝ} (hf : Continuous f) {branch : ℕ → Set ℝ}
    (hbranch : ∀ n, MeasurableSet (branch n))
    (hinj : ∀ n, InjOn f (branch n))
    {weight : ℝ → ℝ≥0∞} (hweight : Measurable weight) :
    Measurable (crossingMultiplicity f branch weight) := by
  exact Measurable.tsum fun n =>
    measurable_branchCrossingWeight hf (hbranch n) (hinj n) hweight

/-- Away from the derived critical-value image, the branch-resolved integrand
is exactly the intrinsic fiber-indexed multiplicity. -/
theorem crossingMultiplicity_eq_weightedFiberMultiplicity_of_not_mem_criticalImage
    {f : ℝ → ℝ} {s : Set ℝ} {branch : ℕ → Set ℝ}
    (hpair : Pairwise (Disjoint on branch))
    (hunion : (⋃ n, branch n) = s ∩ regularSource f)
    (hinj : ∀ n, InjOn f (branch n))
    (weight : ℝ → ℝ≥0∞) {y : ℝ}
    (hy : y ∉ f '' (s ∩ (regularSource f)ᶜ)) :
    crossingMultiplicity f branch weight y =
      weightedFiberMultiplicity f s weight y := by
  classical
  let fiber : ℕ → Set ℝ := fun n => projectionFiber f (branch n) y
  have hfiberPair : Set.univ.PairwiseDisjoint fiber := by
    intro i hi j hj hij
    exact (hpair hij).mono inter_subset_left inter_subset_left
  have hfiberUnion :
      (⋃ n, fiber n) = projectionFiber f s y := by
    ext x
    simp only [fiber, projectionFiber, mem_iUnion, mem_inter_iff,
      mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨n, hxn, hxy⟩
      have hxUnion : x ∈ ⋃ n, branch n := mem_iUnion.2 ⟨n, hxn⟩
      have hxsreg : x ∈ s ∩ regularSource f := hunion ▸ hxUnion
      exact ⟨hxsreg.1, hxy⟩
    · rintro ⟨hxs, hxy⟩
      have hxreg : x ∈ regularSource f := by
        by_contra hxcritical
        exact hy ⟨x, ⟨hxs, hxcritical⟩, hxy⟩
      have hxUnion : x ∈ ⋃ n, branch n := by
        rw [hunion]
        exact ⟨hxs, hxreg⟩
      obtain ⟨n, hxn⟩ := mem_iUnion.1 hxUnion
      exact ⟨n, hxn, hxy⟩
  calc
    crossingMultiplicity f branch weight y =
        ∑' n, ∑' x : fiber n, weight x := by
      unfold crossingMultiplicity
      apply tsum_congr
      intro n
      exact branchCrossingWeight_eq_fiber_tsum (hinj n) y
    _ = ∑' x : ⋃ n, fiber n, weight x :=
      (ENNReal.tsum_biUnion hfiberPair).symm
    _ = weightedFiberMultiplicity f s weight y := by
      rw [hfiberUnion]
      rfl

/-- Exact weighted multiplicity formula for a scalar `C¹` projection on an
arbitrary measurable parameter set.  The countable injective decomposition,
critical-source removal, and offset measurability are conclusions. -/
theorem exists_crossingMultiplicity_lintegral_eq
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {s : Set ℝ}
    (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    ∃ branch : ℕ → Set ℝ,
      (∀ n, MeasurableSet (branch n)) ∧
      Pairwise (Disjoint on branch) ∧
      (⋃ n, branch n) = s ∩ regularSource f ∧
      (∀ n, InjOn f (branch n)) ∧
      Measurable (crossingMultiplicity f branch weight) ∧
      (∫⁻ y, crossingMultiplicity f branch weight y) =
        ∫⁻ x in s, ENNReal.ofReal |deriv f x| * weight x := by
  obtain ⟨branch, hbranch, hpair, hunion, hinj⟩ :=
    exists_countable_disjoint_injective_decomposition hf hs
  refine ⟨branch, hbranch, hpair, hunion, hinj,
    measurable_crossingMultiplicity hf.continuous hbranch hinj hweight, ?_⟩
  change (∫⁻ y, ∑' n, branchCrossingWeight f (branch n) weight y) =
    ∫⁻ x in s, ENNReal.ofReal |deriv f x| * weight x
  rw [lintegral_tsum (fun n =>
    (measurable_branchCrossingWeight hf.continuous (hbranch n)
      (hinj n) hweight).aemeasurable)]
  simp_rw [lintegral_branchCrossingWeight hf (hbranch _) (hinj _)]
  rw [← lintegral_iUnion hbranch hpair, hunion]
  let integrand : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal |deriv f x| * weight x
  have hR : MeasurableSet (regularSource f) :=
    (isOpen_regularSource hf).measurableSet
  have hzero : ∫⁻ x in s \ regularSource f, integrand x = 0 := by
    apply setLIntegral_eq_zero (hs.diff hR)
    intro x hx
    change integrand x = 0
    have hdx : deriv f x = 0 := by
      simpa only [regularSource, mem_ofPred_eq, not_not] using hx.2
    simp only [integrand, hdx, abs_zero, ENNReal.ofReal_zero, zero_mul]
  calc
    (∫⁻ x in s ∩ regularSource f, integrand x) =
        (∫⁻ x in s ∩ regularSource f, integrand x) +
          (∫⁻ x in s \ regularSource f, integrand x) := by rw [hzero, add_zero]
    _ = ∫⁻ x in (s ∩ regularSource f) ∪ (s \ regularSource f), integrand x := by
      have hdisj : Disjoint (s ∩ regularSource f) (s \ regularSource f) := by
        exact Set.disjoint_left.2 (by aesop)
      exact (lintegral_union (hs.diff hR) hdisj).symm
    _ = ∫⁻ x in s, integrand x := by
      have hset : (s ∩ regularSource f) ∪ (s \ regularSource f) = s := by
        aesop
      rw [hset]

/-- The intrinsic fiber-indexed multiplicity is measurable modulo the null set
of critical values. -/
theorem aemeasurable_weightedFiberMultiplicity
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {s : Set ℝ}
    (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    AEMeasurable (weightedFiberMultiplicity f s weight) := by
  obtain ⟨branch, hbranch, hpair, hunion, hinj, hmeas, hformula⟩ :=
    exists_crossingMultiplicity_lintegral_eq hf hs hweight
  have hcritical :
      volume (f '' (s ∩ (regularSource f)ᶜ)) = 0 :=
    volume_image_criticalSource_eq_zero hf s
  have hnotCritical :
      ∀ᵐ y ∂volume, y ∉ f '' (s ∩ (regularSource f)ᶜ) :=
    measure_eq_zero_iff_ae_notMem.mp hcritical
  have heq :
      crossingMultiplicity f branch weight =ᵐ[volume]
        weightedFiberMultiplicity f s weight :=
    hnotCritical.mono fun y hy =>
      crossingMultiplicity_eq_weightedFiberMultiplicity_of_not_mem_criticalImage
        hpair hunion hinj weight hy
  exact hmeas.aemeasurable.congr heq

/-- One-dimensional weighted area formula with the actual source-fiber
multiplicity.  Critical fibers are retained pointwise and affect neither side
because their set of offsets is null. -/
theorem lintegral_weightedFiberMultiplicity
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {s : Set ℝ}
    (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    (∫⁻ y, weightedFiberMultiplicity f s weight y) =
      ∫⁻ x in s, ENNReal.ofReal |deriv f x| * weight x := by
  obtain ⟨branch, hbranch, hpair, hunion, hinj, hmeas, hformula⟩ :=
    exists_crossingMultiplicity_lintegral_eq hf hs hweight
  have hcritical :
      volume (f '' (s ∩ (regularSource f)ᶜ)) = 0 :=
    volume_image_criticalSource_eq_zero hf s
  have hnotCritical :
      ∀ᵐ y ∂volume, y ∉ f '' (s ∩ (regularSource f)ᶜ) :=
    measure_eq_zero_iff_ae_notMem.mp hcritical
  have heq :
      weightedFiberMultiplicity f s weight =ᵐ[volume]
        crossingMultiplicity f branch weight :=
    hnotCritical.mono fun y hy =>
      (crossingMultiplicity_eq_weightedFiberMultiplicity_of_not_mem_criticalImage
        hpair hunion hinj weight hy).symm
  calc
    (∫⁻ y, weightedFiberMultiplicity f s weight y) =
        ∫⁻ y, crossingMultiplicity f branch weight y :=
      lintegral_congr_ae heq
    _ = ∫⁻ x in s, ENNReal.ofReal |deriv f x| * weight x := hformula


/-- Scalar projection of an arbitrary parametrized plane curve onto an
oriented line direction.  Unit normalization is deliberately not required. -/
def curveProjection (direction : PlanePoint) (curve : ℝ → PlanePoint)
    (t : ℝ) : ℝ :=
  direction.1 * (curve t).1 + direction.2 * (curve t).2

lemma contDiff_curveProjection (direction : PlanePoint)
    {curve : ℝ → PlanePoint} (hcurve : ContDiff ℝ 1 curve) :
    ContDiff ℝ 1 (curveProjection direction curve) :=
  (contDiff_const.mul hcurve.fst).add (contDiff_const.mul hcurve.snd)

lemma deriv_curveProjection (direction : PlanePoint)
    {curve : ℝ → PlanePoint} (hcurve : ContDiff ℝ 1 curve) (t : ℝ) :
    deriv (curveProjection direction curve) t =
      direction.1 * deriv (fun z => (curve z).1) t +
        direction.2 * deriv (fun z => (curve z).2) t := by
  have hleft : DifferentiableAt ℝ
      (fun z : ℝ => direction.1 * (curve z).1) t :=
    (hcurve.fst.differentiable (by norm_num) t).const_mul direction.1
  have hright : DifferentiableAt ℝ
      (fun z : ℝ => direction.2 * (curve z).2) t :=
    (hcurve.snd.differentiable (by norm_num) t).const_mul direction.2
  change deriv ((fun z : ℝ => direction.1 * (curve z).1) +
    (fun z : ℝ => direction.2 * (curve z).2)) t = _
  rw [deriv_add hleft hright, deriv_const_mul_field,
    deriv_const_mul_field]

/-- Literal strip-density weight pulled back to an arbitrary curve. -/
def curveStripWeight (lam : ℝ) (curve : ℝ → PlanePoint)
    (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (StripDensity lam (curve t))

lemma measurable_curveStripWeight (lam : ℝ) {curve : ℝ → PlanePoint}
    (hcurve : Measurable curve) :
    Measurable (curveStripWeight lam curve) :=
  ENNReal.continuous_ofReal.measurable.comp
    ((measurable_stripDensity lam).comp hcurve)

/-- Weighted projection-multiplicity formula for an arbitrary `C¹` plane
curve and oriented line direction. -/
theorem lintegral_curve_weightedFiberMultiplicity
    (direction : PlanePoint) {curve : ℝ → PlanePoint}
    (hcurve : ContDiff ℝ 1 curve) {s : Set ℝ}
    (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    (∫⁻ y, weightedFiberMultiplicity
        (curveProjection direction curve) s weight y) =
      ∫⁻ t in s,
        ENNReal.ofReal
            |direction.1 * deriv (fun z => (curve z).1) t +
              direction.2 * deriv (fun z => (curve z).2) t| *
          weight t := by
  simpa only [deriv_curveProjection direction hcurve] using
    lintegral_weightedFiberMultiplicity
      (contDiff_curveProjection direction hcurve) hs hweight

/-- Arbitrary-curve formula with the literal project strip density retained
at every source crossing. -/
theorem lintegral_curve_stripDensity_weightedFiberMultiplicity
    (lam : ℝ) (direction : PlanePoint) {curve : ℝ → PlanePoint}
    (hcurve : ContDiff ℝ 1 curve) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (∫⁻ y, weightedFiberMultiplicity
        (curveProjection direction curve) s
        (curveStripWeight lam curve) y) =
      ∫⁻ t in s,
        ENNReal.ofReal
            |direction.1 * deriv (fun z => (curve z).1) t +
              direction.2 * deriv (fun z => (curve z).2) t| *
          ENNReal.ofReal (StripDensity lam (curve t)) := by
  exact lintegral_curve_weightedFiberMultiplicity direction hcurve hs
    (measurable_curveStripWeight lam hcurve.continuous.measurable)

/-- Offset-integrated multiplicity as a function of the oriented direction. -/
noncomputable def curveDirectionalMultiplicityCost
    (curve : ℝ → PlanePoint) (s : Set ℝ) (weight : ℝ → ℝ≥0∞)
    (direction : PlanePoint) : ℝ≥0∞ :=
  ∫⁻ y, weightedFiberMultiplicity
    (curveProjection direction curve) s weight y

/-- Direction measurability of the exact offset-integrated multiplicity for
an arbitrary `C¹` plane curve. -/
theorem measurable_curveDirectionalMultiplicityCost
    {curve : ℝ → PlanePoint} (hcurve : ContDiff ℝ 1 curve)
    {s : Set ℝ} (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    Measurable (curveDirectionalMultiplicityCost curve s weight) := by
  let joint : PlanePoint × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
        |q.1.1 * deriv (fun z => (curve z).1) q.2 +
          q.1.2 * deriv (fun z => (curve z).2) q.2| *
      weight q.2
  have hscalar : Measurable (fun q : PlanePoint × ℝ =>
      q.1.1 * deriv (fun z => (curve z).1) q.2 +
        q.1.2 * deriv (fun z => (curve z).2) q.2) := by
    exact (((continuous_fst.comp continuous_fst).mul
      ((hcurve.fst.continuous_deriv (by norm_num)).comp continuous_snd)).add
      ((continuous_snd.comp continuous_fst).mul
        ((hcurve.snd.continuous_deriv (by norm_num)).comp
          continuous_snd))).measurable
  have hjoint : Measurable joint :=
    (ENNReal.continuous_ofReal.measurable.comp hscalar.abs).mul
      (hweight.comp measurable_snd)
  let T : Set (PlanePoint × ℝ) := Set.univ ×ˢ s
  have hT : MeasurableSet T :=
    (MeasurableSet.univ :
      MeasurableSet (Set.univ : Set PlanePoint)).prod hs
  have hjoint' : Measurable (Function.uncurry (fun direction t =>
      T.indicator joint (direction, t))) := by
    change Measurable (T.indicator joint)
    exact hjoint.indicator hT
  have hsections :
      Measurable (fun direction : PlanePoint =>
        ∫⁻ t : ℝ, T.indicator joint (direction, t)) :=
    hjoint'.lintegral_prod_right
  have hrepr :
      curveDirectionalMultiplicityCost curve s weight =
        fun direction : PlanePoint =>
          ∫⁻ t : ℝ, T.indicator joint (direction, t) := by
    funext direction
    rw [curveDirectionalMultiplicityCost,
      lintegral_curve_weightedFiberMultiplicity direction hcurve hs hweight,
      ← lintegral_indicator hs]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ s <;> simp [T, joint, ht]
  rw [hrepr]
  exact hsections

theorem measurable_curveStripDirectionalMultiplicityCost
    (lam : ℝ) {curve : ℝ → PlanePoint}
    (hcurve : ContDiff ℝ 1 curve) {s : Set ℝ}
    (hs : MeasurableSet s) :
    Measurable
      (curveDirectionalMultiplicityCost curve s
        (curveStripWeight lam curve)) :=
  measurable_curveDirectionalMultiplicityCost hcurve hs
    (measurable_curveStripWeight lam hcurve.continuous.measurable)

/-- Exact averaging identity against any measure on oriented directions. -/
theorem lintegral_curveDirectionalMultiplicityCost
    {curve : ℝ → PlanePoint} (hcurve : ContDiff ℝ 1 curve)
    {s : Set ℝ} (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) (ν : Measure PlanePoint) :
    (∫⁻ direction, curveDirectionalMultiplicityCost curve s weight direction ∂ν) =
      ∫⁻ direction, (∫⁻ t in s,
        ENNReal.ofReal
            |direction.1 * deriv (fun z => (curve z).1) t +
              direction.2 * deriv (fun z => (curve z).2) t| *
          weight t) ∂ν := by
  apply lintegral_congr
  intro direction
  exact lintegral_curve_weightedFiberMultiplicity
    direction hcurve hs hweight

/-- Direction average with literal project strip-density crossing weights. -/
theorem lintegral_curveStripDirectionalMultiplicityCost
    (lam : ℝ) {curve : ℝ → PlanePoint}
    (hcurve : ContDiff ℝ 1 curve) {s : Set ℝ}
    (hs : MeasurableSet s) (ν : Measure PlanePoint) :
    (∫⁻ direction,
        curveDirectionalMultiplicityCost curve s
          (curveStripWeight lam curve) direction ∂ν) =
      ∫⁻ direction, (∫⁻ t in s,
        ENNReal.ofReal
            |direction.1 * deriv (fun z => (curve z).1) t +
              direction.2 * deriv (fun z => (curve z).2) t| *
          ENNReal.ofReal (StripDensity lam (curve t))) ∂ν := by
  simpa only [curveStripWeight] using
    lintegral_curveDirectionalMultiplicityCost hcurve hs
      (measurable_curveStripWeight lam hcurve.continuous.measurable) ν

/-- Orthogonal scalar projection of the graph `(t, g t)` onto the unit vector
of angle `theta`. -/
def graphProjection (theta : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.cos theta * t + Real.sin theta * g t

lemma contDiff_graphProjection (theta : ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (graphProjection theta g) := by
  exact (contDiff_const.mul contDiff_id).add (contDiff_const.mul hg)
lemma hasDerivAt_graphProjection (theta : ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (t : ℝ) :
    HasDerivAt (graphProjection theta g)
      (Real.cos theta + Real.sin theta * deriv g t) t := by
  have hd : DifferentiableAt ℝ (graphProjection theta g) t :=
    (contDiff_graphProjection theta hg).differentiable (by norm_num) t
  have hderiv : deriv (graphProjection theta g) t =
      Real.cos theta + Real.sin theta * deriv g t := by
    change deriv ((fun z : ℝ => Real.cos theta * z) +
      (fun z : ℝ => Real.sin theta * g z)) t =
        Real.cos theta + Real.sin theta * deriv g t
    have hdleft : DifferentiableAt ℝ (fun z : ℝ => Real.cos theta * z) t := by
      fun_prop
    have hdright : DifferentiableAt ℝ (fun z : ℝ => Real.sin theta * g z) t := by
      exact (hg.differentiable (by norm_num) t).const_mul (Real.sin theta)
    rw [deriv_add hdleft hdright,
      deriv_const_mul_field, deriv_const_mul_field, deriv_id'']
    simp only [mul_one]
  rw [← hderiv]
  exact hd.hasDerivAt

lemma deriv_graphProjection (theta : ℝ) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (t : ℝ) :
    deriv (graphProjection theta g) t =
      Real.cos theta + Real.sin theta * deriv g t :=
  (hasDerivAt_graphProjection theta hg t).deriv

/-- Graph point in the project plane model. -/
def graphPoint (g : ℝ → ℝ) (t : ℝ) : PlanePoint :=
  (t, g t)

/-- The literal project strip-density weight pulled back to a graph. -/
def graphStripWeight (lam : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (StripDensity lam (graphPoint g t))

lemma measurable_graphStripWeight (lam : ℝ) {g : ℝ → ℝ}
    (hg : Measurable g) :
    Measurable (graphStripWeight lam g) := by
  exact ENNReal.continuous_ofReal.measurable.comp
    ((measurable_stripDensity lam).comp (measurable_id.prodMk hg))

/-- Intrinsic graph-fiber multiplicity formula in an arbitrary oriented unit
direction. -/
theorem lintegral_graph_weightedFiberMultiplicity
    (theta : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    (∫⁻ y, weightedFiberMultiplicity (graphProjection theta g) s weight y) =
      ∫⁻ t in s,
        ENNReal.ofReal
          |Real.cos theta + Real.sin theta * deriv g t| * weight t := by
  simpa only [deriv_graphProjection theta hg] using
    lintegral_weightedFiberMultiplicity
      (contDiff_graphProjection theta hg) hs hweight

/-- Offset-integrated crossing cost for a graph projection direction. -/
noncomputable def graphDirectionalMultiplicityCost
    (g : ℝ → ℝ) (s : Set ℝ) (weight : ℝ → ℝ≥0∞)
    (theta : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, weightedFiberMultiplicity (graphProjection theta g) s weight y

/-- Offset measurability in every fixed direction. -/
theorem aemeasurable_graph_weightedFiberMultiplicity
    (theta : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    AEMeasurable
      (weightedFiberMultiplicity (graphProjection theta g) s weight) :=
  aemeasurable_weightedFiberMultiplicity
    (contDiff_graphProjection theta hg) hs hweight

/-- Direction measurability after integrating the offset.  Together with
`aemeasurable_graph_weightedFiberMultiplicity`, this is the measurability
contract needed to average the exact directional crossing costs. -/
theorem measurable_graphDirectionalMultiplicityCost
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    Measurable (graphDirectionalMultiplicityCost g s weight) := by
  let joint : ℝ × ℝ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
        |Real.cos q.1 + Real.sin q.1 * deriv g q.2| *
      weight q.2
  have hscalar : Measurable (fun q : ℝ × ℝ =>
      Real.cos q.1 + Real.sin q.1 * deriv g q.2) := by
    exact ((Real.continuous_cos.comp continuous_fst).add
      ((Real.continuous_sin.comp continuous_fst).mul
        ((hg.continuous_deriv (by norm_num)).comp continuous_snd))).measurable
  have hjoint : Measurable joint := by
    exact (ENNReal.continuous_ofReal.measurable.comp hscalar.abs).mul
      (hweight.comp measurable_snd)
  let T : Set (ℝ × ℝ) := Set.univ ×ˢ s
  have hT : MeasurableSet T :=
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ)).prod hs
  have hjoint' : Measurable (Function.uncurry (fun theta t =>
      T.indicator joint (theta, t))) := by
    change Measurable (T.indicator joint)
    exact hjoint.indicator hT
  have hsections :
      Measurable (fun theta : ℝ =>
        ∫⁻ t : ℝ, T.indicator joint (theta, t)) :=
    hjoint'.lintegral_prod_right
  have hrepr :
      graphDirectionalMultiplicityCost g s weight =
        fun theta : ℝ => ∫⁻ t : ℝ, T.indicator joint (theta, t) := by
    funext theta
    rw [graphDirectionalMultiplicityCost,
      lintegral_graph_weightedFiberMultiplicity theta hg hs hweight,
      ← lintegral_indicator hs]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ s <;> simp [T, joint, ht]
  rw [hrepr]
  exact hsections

/-- Exact direction average of the offset-integrated graph crossing cost. -/
theorem setLIntegral_graphDirectionalMultiplicityCost
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s angles : Set ℝ} (hs : MeasurableSet s)
    (hangles : MeasurableSet angles) {weight : ℝ → ℝ≥0∞}
    (hweight : Measurable weight) :
    (∫⁻ theta in angles, graphDirectionalMultiplicityCost g s weight theta) =
      ∫⁻ theta in angles, ∫⁻ t in s,
        ENNReal.ofReal
          |Real.cos theta + Real.sin theta * deriv g t| * weight t := by
  apply setLIntegral_congr_fun hangles
  intro theta _htheta
  exact lintegral_graph_weightedFiberMultiplicity theta hg hs hweight

/-- Project-weighted graph specialization.  Each fiber contribution carries
the literal `StripDensity` value of its source graph point. -/
theorem lintegral_graph_stripDensity_weightedFiberMultiplicity
    (lam theta : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (∫⁻ y, weightedFiberMultiplicity (graphProjection theta g) s
        (graphStripWeight lam g) y) =
      ∫⁻ t in s,
        ENNReal.ofReal
            |Real.cos theta + Real.sin theta * deriv g t| *
          ENNReal.ofReal (StripDensity lam (graphPoint g t)) := by
  exact lintegral_graph_weightedFiberMultiplicity theta hg hs
    (measurable_graphStripWeight lam hg.continuous.measurable)

theorem measurable_graphStripDirectionalMultiplicityCost
    (lam : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set ℝ} (hs : MeasurableSet s) :
    Measurable
      (graphDirectionalMultiplicityCost g s (graphStripWeight lam g)) :=
  measurable_graphDirectionalMultiplicityCost hg hs
    (measurable_graphStripWeight lam hg.continuous.measurable)

/-- Direction-averaged projection multiplicity with literal strip-density
weights. -/
theorem setLIntegral_graphStripDirectionalMultiplicityCost
    (lam : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {s angles : Set ℝ} (hs : MeasurableSet s)
    (hangles : MeasurableSet angles) :
    (∫⁻ theta in angles,
        graphDirectionalMultiplicityCost g s (graphStripWeight lam g) theta) =
      ∫⁻ theta in angles, ∫⁻ t in s,
        ENNReal.ofReal
            |Real.cos theta + Real.sin theta * deriv g t| *
          ENNReal.ofReal (StripDensity lam (graphPoint g t)) := by
  simpa only [graphStripWeight] using
    setLIntegral_graphDirectionalMultiplicityCost hg hs hangles
      (measurable_graphStripWeight lam hg.continuous.measurable)




/-- The nonmonotone quadratic projection on an interval has two distinct
source crossings at the regular offset `1 / 4`. -/
theorem weightedFiberMultiplicity_sq_Icc :
    weightedFiberMultiplicity (fun t : ℝ => t ^ 2)
      (Icc (-1) 1) (fun _ => (1 : ℝ≥0∞)) (1 / 4) = 2 := by
  have hfiber :
      projectionFiber (fun t : ℝ => t ^ 2) (Icc (-1) 1) (1 / 4) =
        ({-(1 / 2), 1 / 2} : Set ℝ) := by
    ext x
    simp only [projectionFiber, mem_inter_iff, mem_Icc, mem_preimage,
      mem_singleton_iff, mem_insert_iff]
    constructor
    · rintro ⟨hxIcc, hxpow⟩
      have hsq : x ^ 2 = (1 / 2 : ℝ) ^ 2 := by
        nlinarith
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
      · exact Or.inr hpos
      · exact Or.inl hneg
    · rintro (hneg | hpos)
      · subst x
        norm_num
      · subst x
        norm_num
  unfold weightedFiberMultiplicity
  rw [hfiber]
  let _ : Fintype ({-(1 / 2), 1 / 2} : Set ℝ) :=
    Set.Finite.fintype (by simp)
  rw [tsum_fintype]
  norm_num



/-- The intrinsic definition retains an infinite critical fiber.  A horizontal
interface segment projected vertically has infinite pointwise multiplicity at
its interface offset, although that singleton offset is Lebesgue-null. -/
theorem weightedFiberMultiplicity_upperInterface_vertical_eq_top
    (lam : ℝ) :
    weightedFiberMultiplicity
        (graphProjection (Real.pi / 2) (fun _ : ℝ => 1))
        (Icc (-1) 1) (graphStripWeight lam (fun _ : ℝ => 1)) 1 = ⊤ := by
  have hprojection :
      graphProjection (Real.pi / 2) (fun _ : ℝ => 1) =
        fun _ : ℝ => 1 := by
    funext t
    simp [graphProjection]
  have hweight :
      graphStripWeight lam (fun _ : ℝ => 1) =
        fun _ : ℝ => 1 := by
    funext t
    simp [graphStripWeight, graphPoint]
  rw [hprojection, hweight]
  let _ : Infinite (Icc (-1 : ℝ) 1) := Icc.infinite (by norm_num)
  simp [weightedFiberMultiplicity, projectionFiber]

/-- Interface-exact segment example: the closed-strip convention gives weight
`1` on the upper interface, including in every projection direction. -/
theorem lintegral_upperInterface_segment_multiplicity
    (lam theta a b : ℝ) :
    (∫⁻ y, weightedFiberMultiplicity
        (graphProjection theta (fun _ : ℝ => 1)) (Icc a b)
        (graphStripWeight lam (fun _ : ℝ => 1)) y) =
      ∫⁻ _t in Icc a b, ENNReal.ofReal |Real.cos theta| := by
  simpa [graphStripWeight, graphPoint] using
    lintegral_graph_stripDensity_weightedFiberMultiplicity
      lam theta (g := fun _ : ℝ => 1) contDiff_const measurableSet_Icc

end WeightedCurveMultiplicity
end CMVRelaxation
