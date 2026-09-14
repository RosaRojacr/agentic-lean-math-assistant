/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVLocalGraphSurgery

/-!
# Quantitative neighborhoods for finite splice junctions

The cut geometry is selected separately for every smooth approximant, so its
finite set of junctions need not have a uniform cardinality.  This module
selects pairwise-disjoint shrinking neighborhoods only after that geometry is
known, measures all affected old frontier with the actual strip-density weight,
and globally bounds the candidate spherical boundary allowance.  Its final
theorems package any supplied quantitative local repair into a smooth sequence;
the geometric construction of that local repair remains explicit.
-/

open Set Function Filter MeasureTheory Metric
open scoped ENNReal MeasureTheory Topology BigOperators symmDiff ContDiff

noncomputable section

namespace CMVRelaxation
namespace FiniteJunctionRepair

/-- The Euclidean weighted trace measure underlying `weightedTraceCost`. -/
def euclideanWeightedTraceMeasure (lam : ℝ) : Measure EuclideanPlane :=
  (μH[1] : Measure EuclideanPlane).withDensity
    (fun z => ENNReal.ofReal (euclideanStripDensity lam z))

/-- On a closed coordinate trace, `weightedTraceCost` is literally the value of
one measure.  This exposes continuity from above at finite junction sets. -/
theorem weightedTraceCost_eq_euclideanWeightedTraceMeasure
    (lam : ℝ) {S : Set PlanePoint} (hS : IsClosed S) :
    weightedTraceCost lam S =
      euclideanWeightedTraceMeasure lam (planeEuclideanHomeomorph '' S) := by
  unfold weightedTraceCost euclideanWeightedTraceMeasure
  rw [withDensity_apply _
    ((planeEuclideanHomeomorph.isClosedMap S hS).measurableSet)]

/-- A coordinate-plane neighborhood obtained by pulling back one genuine
Euclidean closed ball. -/
def junctionBall (p : PlanePoint) (r : ℝ) : Set PlanePoint :=
  planeEuclideanHomeomorph ⁻¹'
    closedBall (planeEuclideanHomeomorph p) r

lemma isClosed_junctionBall (p : PlanePoint) (r : ℝ) :
    IsClosed (junctionBall p r) :=
  isClosed_closedBall.preimage planeEuclideanHomeomorph.continuous

lemma isCompact_junctionBall (p : PlanePoint) (r : ℝ) :
    IsCompact (junctionBall p r) := by
  exact planeEuclideanHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall _ _)

lemma euclidean_image_inter_junctionBall
    (S : Set PlanePoint) (p : PlanePoint) (r : ℝ) :
    planeEuclideanHomeomorph '' (S ∩ junctionBall p r) =
      planeEuclideanHomeomorph '' S ∩
        closedBall (planeEuclideanHomeomorph p) r := by
  rw [Set.image_inter planeEuclideanHomeomorph.injective]
  congr 1
  exact planeEuclideanHomeomorph.surjective.image_preimage _

/-- The canonical reciprocal radius used for junction repairs. -/
def junctionRadius (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

lemma junctionRadius_pos (n : ℕ) : 0 < junctionRadius n := by
  exact one_div_pos.mpr (by positivity)

lemma antitone_junctionRadius : Antitone junctionRadius := by
  intro m n hmn
  apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 1)
  exact_mod_cast Nat.add_le_add_right hmn 1

lemma tendsto_junctionRadius_zero :
    Tendsto junctionRadius atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The complete weighted mass of a closed trace in a shrinking ball around one
point tends to zero.  Finiteness is required only for that trace's actual
weighted cost, not for an unweighted ambient perimeter. -/
theorem tendsto_weightedTraceCost_inter_junctionBall_zero
    (lam : ℝ) {S : Set PlanePoint} (hS : IsClosed S)
    (hfinite : weightedTraceCost lam S ≠ ⊤) (p : PlanePoint) :
    Tendsto (fun n =>
      weightedTraceCost lam (S ∩ junctionBall p (junctionRadius n)))
      atTop (𝓝 0) := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  let ν : Measure EuclideanPlane := euclideanWeightedTraceMeasure lam
  let T : ℕ → Set EuclideanPlane := fun n =>
    planeEuclideanHomeomorph '' S ∩
      closedBall (planeEuclideanHomeomorph p) (junctionRadius n)
  have hTclosed : ∀ n, IsClosed (T n) := by
    intro n
    exact (planeEuclideanHomeomorph.isClosedMap S hS).inter isClosed_closedBall
  have hTanti : Antitone T := by
    intro m n hmn z hz
    change z ∈ planeEuclideanHomeomorph '' S ∩
      closedBall (planeEuclideanHomeomorph p) (junctionRadius n) at hz
    change z ∈ planeEuclideanHomeomorph '' S ∩
      closedBall (planeEuclideanHomeomorph p) (junctionRadius m)
    exact ⟨hz.1, (mem_closedBall.mp hz.2).trans
      (antitone_junctionRadius hmn)⟩
  have hTfinite : ν (T 0) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfinite
    calc
      ν (T 0) ≤ ν (planeEuclideanHomeomorph '' S) :=
        measure_mono inter_subset_left
      _ = weightedTraceCost lam S :=
        (weightedTraceCost_eq_euclideanWeightedTraceMeasure lam hS).symm
  have hInterSubset : (⋂ n, T n) ⊆ {planeEuclideanHomeomorph p} := by
    intro z hz
    have hzall : ∀ n, z ∈ T n := mem_iInter.mp hz
    have hdist : dist z (planeEuclideanHomeomorph p) ≤ 0 :=
      ge_of_tendsto tendsto_junctionRadius_zero
        (Eventually.of_forall fun n => by
          simpa only [mem_closedBall] using (hzall n).2)
    have hzEq : z = planeEuclideanHomeomorph p :=
      dist_eq_zero.mp (le_antisymm hdist dist_nonneg)
    simpa only [mem_singleton_iff] using hzEq
  have hsingleton : ν {planeEuclideanHomeomorph p} = 0 := by
    dsimp only [ν, euclideanWeightedTraceMeasure]
    rw [withDensity_apply _ (measurableSet_singleton _)]
    exact setLIntegral_measure_zero _ _ (measure_singleton _)
  have hInterZero : ν (⋂ n, T n) = 0 :=
    measure_mono_null hInterSubset hsingleton
  have hlim : Tendsto (ν ∘ T) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (fun n => (hTclosed n).measurableSet.nullMeasurableSet)
      hTanti ⟨0, hTfinite⟩
    simpa only [hInterZero] using h
  have hcost : ∀ n,
      weightedTraceCost lam (S ∩ junctionBall p (junctionRadius n)) =
        ν (T n) := by
    intro n
    rw [weightedTraceCost_eq_euclideanWeightedTraceMeasure lam
      (hS.inter (isClosed_junctionBall p (junctionRadius n)))]
    exact congrArg ν
      (euclidean_image_inter_junctionBall S p (junctionRadius n))
  have hfun :
      (fun n => weightedTraceCost lam
        (S ∩ junctionBall p (junctionRadius n))) =
        fun n => ν (T n) :=
    funext hcost
  rw [hfun]
  change Tendsto (fun n => ν (T n)) atTop (𝓝 0) at hlim
  exact hlim

/-- Planar area of a shrinking junction ball tends to zero. -/
theorem tendsto_volume_junctionBall_zero (p : PlanePoint) :
    Tendsto (fun n => volume (junctionBall p (junctionRadius n)))
      atTop (𝓝 0) := by
  let T : ℕ → Set PlanePoint := fun n =>
    junctionBall p (junctionRadius n)
  have hTmeas : ∀ n, NullMeasurableSet (T n) volume := by
    intro n
    exact (isClosed_junctionBall p (junctionRadius n)).measurableSet.nullMeasurableSet
  have hTanti : Antitone T := by
    intro m n hmn q hq
    change dist (planeEuclideanHomeomorph q)
      (planeEuclideanHomeomorph p) ≤ junctionRadius n at hq
    change dist (planeEuclideanHomeomorph q)
      (planeEuclideanHomeomorph p) ≤ junctionRadius m
    exact hq.trans (antitone_junctionRadius hmn)
  have hTfinite : volume (T 0) ≠ ⊤ :=
    (isCompact_junctionBall p (junctionRadius 0)).measure_lt_top.ne
  have hInterSubset : (⋂ n, T n) ⊆ {p} := by
    intro q hq
    have hqall : ∀ n, q ∈ T n := mem_iInter.mp hq
    have hdist : dist (planeEuclideanHomeomorph q)
        (planeEuclideanHomeomorph p) ≤ 0 := by
      apply ge_of_tendsto tendsto_junctionRadius_zero
      exact Eventually.of_forall (fun n => by
        have hn := hqall n
        change dist (planeEuclideanHomeomorph q)
          (planeEuclideanHomeomorph p) ≤ junctionRadius n at hn
        exact hn)
    have heq : planeEuclideanHomeomorph q =
        planeEuclideanHomeomorph p :=
      dist_eq_zero.mp (le_antisymm hdist dist_nonneg)
    simpa only [mem_singleton_iff] using planeEuclideanHomeomorph.injective heq
  have hInterZero : volume (⋂ n, T n) = 0 :=
    measure_mono_null hInterSubset (measure_singleton p)
  have hlim := tendsto_measure_iInter_atTop hTmeas hTanti ⟨0, hTfinite⟩
  rw [hInterZero] at hlim
  exact hlim
/-- Union of the repair neighborhoods selected for one finite junction family. -/
def neighborhood (J : Finset PlanePoint) (r : ℝ) : Set PlanePoint :=
  ⋃ p ∈ J, junctionBall p r

lemma isClosed_neighborhood (J : Finset PlanePoint) (r : ℝ) :
    IsClosed (neighborhood J r) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [neighborhood]
  | @insert p J hp ih =>
      simpa only [neighborhood, Finset.mem_insert, iUnion_iUnion_eq_or_left,
        iUnion_true, iUnion_false, union_comm] using
        ih.union (isClosed_junctionBall p r)

/-- Planar area of a fixed finite union of shrinking junction balls vanishes. -/
theorem tendsto_volume_neighborhood_zero (J : Finset PlanePoint) :
    Tendsto (fun n => volume (neighborhood J (junctionRadius n)))
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n =>
      ∑ p ∈ J, volume (junctionBall p (junctionRadius n)))
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J
      (fun p _ => tendsto_volume_junctionBall_zero p)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  exact MeasureTheory.measure_biUnion_finset_le J
    (fun p => junctionBall p (junctionRadius n))

/-- A finite family of shrinking Euclidean junction balls eventually lies in
any prescribed open neighborhood of all its centers.  This is the locality
input used after the approximant-dependent junction geometry is known. -/
theorem eventually_neighborhood_subset_open
    (J : Finset PlanePoint) {Q : Set PlanePoint} (hQ : IsOpen Q)
    (hJQ : (↑J : Set PlanePoint) ⊆ Q) :
    ∀ᶠ n : ℕ in atTop, neighborhood J (junctionRadius n) ⊆ Q := by
  classical
  have hball : ∀ p ∈ J, ∀ᶠ n : ℕ in atTop,
      junctionBall p (junctionRadius n) ⊆ Q := by
    intro p hpJ
    have hpQ : p ∈ Q := hJQ (by simpa only [Finset.mem_coe] using hpJ)
    have hImageOpen : IsOpen (planeEuclideanHomeomorph '' Q) :=
      planeEuclideanHomeomorph.isOpenMap Q hQ
    have hpImage :
        planeEuclideanHomeomorph p ∈ planeEuclideanHomeomorph '' Q :=
      ⟨p, hpQ, rfl⟩
    have hballs :
        ∀ᶠ r : ℝ in 𝓝 0,
          closedBall (planeEuclideanHomeomorph p) r ⊆
            planeEuclideanHomeomorph '' Q :=
      eventually_closedBall_subset (hImageOpen.mem_nhds hpImage)
    have hselected :
        ∀ᶠ n : ℕ in atTop,
          closedBall (planeEuclideanHomeomorph p) (junctionRadius n) ⊆
            planeEuclideanHomeomorph '' Q :=
      tendsto_junctionRadius_zero.eventually hballs
    filter_upwards [hselected] with n hn
    intro q hq
    change planeEuclideanHomeomorph q ∈
      closedBall (planeEuclideanHomeomorph p) (junctionRadius n) at hq
    rcases hn hq with ⟨q', hq'Q, hq'eq⟩
    have hqq' : q' = q := planeEuclideanHomeomorph.injective hq'eq
    simpa only [hqq'] using hq'Q
  have hall : ∀ᶠ n : ℕ in atTop, ∀ p ∈ J,
      junctionBall p (junctionRadius n) ⊆ Q := by
    rw [eventually_all_finset]
    exact hball
  filter_upwards [hall] with n hn
  intro q hq
  simp only [neighborhood, mem_iUnion] at hq
  rcases hq with ⟨p, hpJ, hqp⟩
  exact hn p hpJ hqp

/-- Weighted trace cost is subadditive over an arbitrary finite family. -/
theorem weightedTraceCost_biUnion_finset_le
    {ι : Type*} (lam : ℝ) (s : Finset ι) (A : ι → Set PlanePoint) :
    weightedTraceCost lam (⋃ i ∈ s, A i) ≤
      ∑ i ∈ s, weightedTraceCost lam (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedTraceCost]
  | @insert a s ha ih =>
      calc
        weightedTraceCost lam (⋃ i ∈ insert a s, A i) =
            weightedTraceCost lam (A a ∪ ⋃ i ∈ s, A i) := by
          congr 1
          ext p
          simp only [mem_iUnion, Finset.mem_insert, mem_union]
          constructor
          · rintro ⟨i, hi, hpA⟩
            rcases hi with rfl | hi
            · exact Or.inl hpA
            · exact Or.inr ⟨i, hi, hpA⟩
          · rintro (hpA | ⟨i, hi, hpA⟩)
            · exact ⟨a, Or.inl rfl, hpA⟩
            · exact ⟨i, Or.inr hi, hpA⟩
        _ ≤ weightedTraceCost lam (A a) +
              weightedTraceCost lam (⋃ i ∈ s, A i) :=
          weightedTraceCost_union_le lam _ _
        _ ≤ weightedTraceCost lam (A a) +
              ∑ i ∈ s, weightedTraceCost lam (A i) :=
          add_le_add le_rfl ih
        _ = ∑ i ∈ insert a s, weightedTraceCost lam (A i) := by
          rw [Finset.sum_insert ha]

/-- For one finite junction family, the entire old weighted trace inside the
union of shrinking repair balls tends to zero. -/
theorem tendsto_weightedTraceCost_inter_neighborhood_zero
    (lam : ℝ) {S : Set PlanePoint} (hS : IsClosed S)
    (hfinite : weightedTraceCost lam S ≠ ⊤) (J : Finset PlanePoint) :
    Tendsto (fun n =>
      weightedTraceCost lam (S ∩ neighborhood J (junctionRadius n)))
      atTop (𝓝 0) := by
  classical
  have hmember : ∀ p ∈ J, Tendsto (fun n =>
      weightedTraceCost lam (S ∩ junctionBall p (junctionRadius n)))
      atTop (𝓝 0) := by
    intro p _hp
    exact tendsto_weightedTraceCost_inter_junctionBall_zero lam hS hfinite p
  have hsum : Tendsto (fun n =>
      ∑ p ∈ J, weightedTraceCost lam
        (S ∩ junctionBall p (junctionRadius n))) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum J (fun p hp => hmember p hp)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  calc
    weightedTraceCost lam (S ∩ neighborhood J (junctionRadius n)) ≤
        weightedTraceCost lam
          (⋃ p ∈ J, S ∩ junctionBall p (junctionRadius n)) := by
      apply weightedTraceCost_mono
      intro q hq
      rcases hq with ⟨hqS, hqN⟩
      simp only [neighborhood, mem_iUnion] at hqN ⊢
      rcases hqN with ⟨p, hpJ, hqBall⟩
      exact ⟨p, hpJ, hqS, hqBall⟩
    _ ≤ ∑ p ∈ J, weightedTraceCost lam
          (S ∩ junctionBall p (junctionRadius n)) :=
      weightedTraceCost_biUnion_finset_le lam J
        (fun p => S ∩ junctionBall p (junctionRadius n))

/-- The spherical boundary of one pulled-back Euclidean repair ball. -/
def junctionSphere (p : PlanePoint) (r : ℝ) : Set PlanePoint :=
  planeEuclideanHomeomorph ⁻¹'
    sphere (planeEuclideanHomeomorph p) r

lemma euclidean_image_junctionSphere (p : PlanePoint) (r : ℝ) :
    planeEuclideanHomeomorph '' junctionSphere p r =
      sphere (planeEuclideanHomeomorph p) r := by
  exact planeEuclideanHomeomorph.surjective.image_preimage _

/-- Euclidean `H¹` of a sphere is at most its usual circumference.  The proof
uses the complete circle parametrization, so no measurability or injectivity
premise is exported. -/
lemma hausdorffMeasure_sphere_le (c : EuclideanPlane) {r : ℝ} (hr : 0 ≤ r) :
    (μH[1] : Measure EuclideanPlane) (sphere c r) ≤
      ENNReal.ofReal (2 * Real.pi * r) := by
  let e : EuclideanPlane ≃ᵢ ℂ := tangentComplexEquiv
  calc
    (μH[1] : Measure EuclideanPlane) (sphere c r) =
        (μH[1] : Measure ℂ) (e '' sphere c r) := by
      symm
      exact e.hausdorffMeasure_image 1 (sphere c r)
    _ = (μH[1] : Measure ℂ) (sphere (e c) r) := by
      rw [e.image_sphere]
    _ = (μH[1] : Measure ℂ)
        (circleMap (e c) r '' Ioc 0 (2 * Real.pi)) := by
      rw [image_circleMap_Ioc, abs_of_nonneg hr]
    _ ≤ ((Real.nnabs r : NNReal) : ENNReal) ^ (1 : ℝ) *
        (μH[1] : Measure ℝ) (Ioc 0 (2 * Real.pi)) :=
      (lipschitzWith_circleMap (e c) r).hausdorffMeasure_image_le
        (show (0 : ℝ) ≤ 1 by norm_num) _
    _ = ENNReal.ofReal r * ENNReal.ofReal (2 * Real.pi) := by
      rw [hausdorffMeasure_real, Real.volume_Ioc]
      simp [ENNReal.coe_nnreal_eq, Real.coe_nnabs, abs_of_nonneg hr]
    _ = ENNReal.ofReal (r * (2 * Real.pi)) :=
      (ENNReal.ofReal_mul hr).symm
    _ = ENNReal.ofReal (2 * Real.pi * r) := by
      congr 1
      ring

/-- The complete density-weighted cost of one spherical candidate boundary is
bounded above linearly in its radius.  The global density bound is used because
a junction ball need not remain in either graph's constant-density tube. -/
theorem weightedTraceCost_junctionSphere_le
    {lam : ℝ} (hlam : 1 < lam) (p : PlanePoint) {r : ℝ} (hr : 0 ≤ r) :
    weightedTraceCost lam (junctionSphere p r) ≤
      ENNReal.ofReal lam * ENNReal.ofReal (2 * Real.pi * r) := by
  calc
    weightedTraceCost lam (junctionSphere p r) ≤
        ENNReal.ofReal lam * (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' junctionSphere p r) :=
      weightedTraceCost_le_density_mul_hausdorff hlam _
    _ = ENNReal.ofReal lam * (μH[1] : Measure EuclideanPlane)
          (sphere (planeEuclideanHomeomorph p) r) := by
      rw [euclidean_image_junctionSphere]
    _ ≤ ENNReal.ofReal lam * ENNReal.ofReal (2 * Real.pi * r) := by
      exact mul_le_mul_right (hausdorffMeasure_sphere_le _ hr) _

/-- The complete finite union of candidate spherical boundaries around the
junction centers. -/
def junctionSpheres (J : Finset PlanePoint) (r : ℝ) : Set PlanePoint :=
  ⋃ p ∈ J, junctionSphere p r

lemma junctionSphere_subset_junctionBall (p : PlanePoint) (r : ℝ) :
    junctionSphere p r ⊆ junctionBall p r :=
  preimage_mono sphere_subset_closedBall

/-- Every charged spherical boundary remains inside the same closed repair
neighborhood; the global density bound changes only its cost estimate, not its
locality. -/
lemma junctionSpheres_subset_neighborhood
    (J : Finset PlanePoint) (r : ℝ) :
    junctionSpheres J r ⊆ neighborhood J r :=
  iUnion_mono fun p => iUnion_mono fun _hp =>
    junctionSphere_subset_junctionBall p r

private lemma frontier_biUnion_finset_subset
    {ι X : Type*} [TopologicalSpace X]
    (J : Finset ι) (T : ι → Set X) :
    frontier (⋃ p ∈ J, T p) ⊆ ⋃ p ∈ J, frontier (T p) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert p J hp ih =>
      have hsets :
          (⋃ q ∈ insert p J, T q) = T p ∪ ⋃ q ∈ J, T q := by
        ext x
        simp only [mem_iUnion, Finset.mem_insert, mem_union]
        constructor
        · rintro ⟨q, hq, hxq⟩
          rcases hq with rfl | hq
          · exact Or.inl hxq
          · exact Or.inr ⟨q, hq, hxq⟩
        · rintro (hxp | ⟨q, hq, hxq⟩)
          · exact ⟨p, Or.inl rfl, hxp⟩
          · exact ⟨q, Or.inr hq, hxq⟩
      rw [hsets]
      intro x hx
      rcases frontier_union_subset (T p) (⋃ q ∈ J, T q) hx with hx | hx
      · simp only [mem_iUnion, Finset.mem_insert]
        exact ⟨p, Or.inl rfl, hx.1⟩
      · have hxJ := ih hx.2
        simp only [mem_iUnion, Finset.mem_insert] at hxJ ⊢
        rcases hxJ with ⟨q, hqJ, hxq⟩
        exact ⟨q, Or.inr hqJ, hxq⟩

lemma frontier_junctionBall_subset_junctionSphere
    (p : PlanePoint) (r : ℝ) :
    frontier (junctionBall p r) ⊆ junctionSphere p r := by
  rw [junctionBall, junctionSphere,
    ← planeEuclideanHomeomorph.preimage_frontier]
  exact preimage_mono frontier_closedBall_subset_sphere

/-- The complete frontier of the finite closed-ball neighborhood is contained
in the already charged finite union of candidate spherical boundaries. -/
lemma frontier_neighborhood_subset_junctionSpheres
    (J : Finset PlanePoint) (r : ℝ) :
    frontier (neighborhood J r) ⊆ junctionSpheres J r := by
  apply (frontier_biUnion_finset_subset J fun p => junctionBall p r).trans
  exact iUnion_mono fun p => iUnion_mono fun _hp =>
    frontier_junctionBall_subset_junctionSphere p r

/-- Any fixed finite junction family has pairwise-disjoint closed repair balls
at every sufficiently small reciprocal radius. -/
lemma eventually_pairwiseDisjoint_junctionBalls (J : Finset PlanePoint) :
    ∀ᶠ n : ℕ in atTop,
      Set.Pairwise (↑J : Set PlanePoint)
        (Function.onFun Disjoint fun p =>
          junctionBall p (junctionRadius n)) := by
  have hradius : Tendsto (fun n => 2 * junctionRadius n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_junctionRadius_zero
  have hpairs : ∀ p ∈ J, ∀ q ∈ J,
      ∀ᶠ n : ℕ in atTop, p ≠ q →
        2 * junctionRadius n <
          dist (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q) := by
    intro p hp q hq
    by_cases hpq : p = q
    · exact Filter.Eventually.of_forall fun _ hpq' => (hpq' hpq).elim
    · have hdist : 0 <
          dist (planeEuclideanHomeomorph p) (planeEuclideanHomeomorph q) :=
        dist_pos.2 (planeEuclideanHomeomorph.injective.ne hpq)
      exact (hradius.eventually (Iio_mem_nhds hdist)).mono
        fun _ hn _ => hn
  filter_upwards [J.eventually_all.2 fun p hp =>
      J.eventually_all.2 fun q hq => hpairs p hp q hq] with n hn
  intro p hp q hq hpq
  have hdisjoint : Disjoint
      (closedBall (planeEuclideanHomeomorph p) (junctionRadius n))
      (closedBall (planeEuclideanHomeomorph q) (junctionRadius n)) := by
    apply closedBall_disjoint_closedBall
    simpa [two_mul] using hn p hp q hq hpq
  exact hdisjoint.preimage planeEuclideanHomeomorph

/-- Cardinality-sensitive upper budget for every spherical repair boundary.
Keeping this as a finite sum avoids any hidden uniform bound on junction count. -/
def junctionSphereCostBudget
    (lam : ℝ) (J : Finset PlanePoint) (r : ℝ) : ENNReal :=
  ∑ _p ∈ J, ENNReal.ofReal lam * ENNReal.ofReal (2 * Real.pi * r)

lemma weightedTraceCost_junctionSpheres_le_budget
    {lam : ℝ} (hlam : 1 < lam) (J : Finset PlanePoint)
    {r : ℝ} (hr : 0 ≤ r) :
    weightedTraceCost lam (junctionSpheres J r) ≤
      junctionSphereCostBudget lam J r := by
  calc
    weightedTraceCost lam (junctionSpheres J r) ≤
        ∑ p ∈ J, weightedTraceCost lam (junctionSphere p r) :=
      weightedTraceCost_biUnion_finset_le lam J (fun p => junctionSphere p r)
    _ ≤ ∑ _p ∈ J,
        ENNReal.ofReal lam * ENNReal.ofReal (2 * Real.pi * r) := by
      exact Finset.sum_le_sum fun p _hp =>
        weightedTraceCost_junctionSphere_le hlam p hr
    _ = junctionSphereCostBudget lam J r := rfl

lemma tendsto_junctionSphereCostBudget_zero
    (lam : ℝ) (J : Finset PlanePoint) :
    Tendsto (fun n => junctionSphereCostBudget lam J (junctionRadius n))
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => 2 * Real.pi * junctionRadius n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul tendsto_junctionRadius_zero
  have hunit : Tendsto (fun n =>
      ENNReal.ofReal lam * ENNReal.ofReal (2 * Real.pi * junctionRadius n))
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hreal)
      (Or.inr ENNReal.ofReal_ne_top)
  simpa [junctionSphereCostBudget] using
    tendsto_finsetSum J (fun _p _hp => hunit)

/-- A varying finite junction family has vanishing spherical trace once its
full cardinality-sensitive budget is selected to vanish.  Radius convergence
alone would be insufficient when the junction counts are unbounded. -/
theorem tendsto_weightedTraceCost_junctionSpheres_zero_of_budget
    {lam : ℝ} (hlam : 1 < lam) (J : ℕ → Finset PlanePoint)
    (k : ℕ → ℕ) (budget : ℕ → ENNReal)
    (hbudget : Tendsto budget atTop (𝓝 0))
    (hselected : ∀ n,
      junctionSphereCostBudget lam (J n) (junctionRadius (k n)) ≤ budget n) :
    Tendsto (fun n =>
      weightedTraceCost lam
        (junctionSpheres (J n) (junctionRadius (k n)))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hbudget
  · exact fun _ => bot_le
  · intro n
    exact (weightedTraceCost_junctionSpheres_le_budget hlam (J n)
      (junctionRadius_pos (k n)).le).trans (hselected n)

/-- Choose a repair scale only after each approximant's finite junction family
is known.  The junction count may vary without a uniform bound.  The chosen
radii, neighborhood areas, and complete weighted old traces all vanish. -/
theorem exists_approximantDependent_neighborhoods
    (lam : ℝ) (S : ℕ → Set PlanePoint) (hS : ∀ n, IsClosed (S n))
    (hfinite : ∀ n, weightedTraceCost lam (S n) ≠ ⊤)
    (J : ℕ → Finset PlanePoint) :
    ∃ k : ℕ → ℕ,
      (∀ n, n ≤ k n) ∧
      Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (S n ∩ neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        volume (neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      ∀ n,
        weightedTraceCost lam
            (S n ∩ neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) ∧
        volume (neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) := by
  have hexists : ∀ n, ∃ q : ℕ, n ≤ q ∧
      weightedTraceCost lam
          (S n ∩ neighborhood (J n) (junctionRadius q)) <
        ENNReal.ofReal (junctionRadius n) ∧
      volume (neighborhood (J n) (junctionRadius q)) <
        ENNReal.ofReal (junctionRadius n) := by
    intro n
    have hpos : 0 < ENNReal.ofReal (junctionRadius n) :=
      ENNReal.ofReal_pos.2 (junctionRadius_pos n)
    have hsmallTrace :=
      (tendsto_weightedTraceCost_inter_neighborhood_zero
        lam (hS n) (hfinite n) (J n)).eventually (Iio_mem_nhds hpos)
    have hsmallVolume :=
      (tendsto_volume_neighborhood_zero (J n)).eventually
        (Iio_mem_nhds hpos)
    have hlarge : ∀ᶠ q : ℕ in atTop, n ≤ q := eventually_ge_atTop n
    rcases (hlarge.and (hsmallTrace.and hsmallVolume)).exists with
      ⟨q, hnq, hqTrace, hqVolume⟩
    exact ⟨q, hnq, hqTrace, hqVolume⟩
  choose k hk hcost hvolume using hexists
  have hradius : Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds tendsto_junctionRadius_zero
    · exact fun n => (junctionRadius_pos (k n)).le
    · exact fun n => antitone_junctionRadius (hk n)
  have hbudget : Tendsto (fun n => ENNReal.ofReal (junctionRadius n))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_junctionRadius_zero
  have htrace : Tendsto (fun n =>
      weightedTraceCost lam
        (S n ∩ neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbudget
    · exact fun _ => bot_le
    · exact fun n => (hcost n).le
  have harea : Tendsto (fun n =>
      volume (neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbudget
    · exact fun _ => bot_le
    · exact fun n => (hvolume n).le
  exact ⟨k, hk, hradius, htrace, harea,
    fun n => ⟨(hcost n).le, (hvolume n).le⟩⟩

/-- The approximant-dependent choice may simultaneously enforce a certified
open localization.  In particular, taking `Q n` to be the complement of a
closed payoff core keeps every repair neighborhood away from the trace that
must cancel against the old approximant. -/
theorem exists_approximantDependent_neighborhoods_inside
    (lam : ℝ) (S : ℕ → Set PlanePoint) (hS : ∀ n, IsClosed (S n))
    (hfinite : ∀ n, weightedTraceCost lam (S n) ≠ ⊤)
    (J : ℕ → Finset PlanePoint) (Q : ℕ → Set PlanePoint)
    (hQ : ∀ n, IsOpen (Q n))
    (hJQ : ∀ n, (↑(J n) : Set PlanePoint) ⊆ Q n) :
    ∃ k : ℕ → ℕ,
      (∀ n, n ≤ k n) ∧
      Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (S n ∩ neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        volume (neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      (∀ n, neighborhood (J n) (junctionRadius (k n)) ⊆ Q n) ∧
      ∀ n,
        weightedTraceCost lam
            (S n ∩ neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) ∧
        volume (neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) := by
  have hexists : ∀ n, ∃ q : ℕ, n ≤ q ∧
      weightedTraceCost lam
          (S n ∩ neighborhood (J n) (junctionRadius q)) <
        ENNReal.ofReal (junctionRadius n) ∧
      volume (neighborhood (J n) (junctionRadius q)) <
        ENNReal.ofReal (junctionRadius n) ∧
      neighborhood (J n) (junctionRadius q) ⊆ Q n := by
    intro n
    have hpos : 0 < ENNReal.ofReal (junctionRadius n) :=
      ENNReal.ofReal_pos.2 (junctionRadius_pos n)
    have hsmallTrace :=
      (tendsto_weightedTraceCost_inter_neighborhood_zero
        lam (hS n) (hfinite n) (J n)).eventually (Iio_mem_nhds hpos)
    have hsmallVolume :=
      (tendsto_volume_neighborhood_zero (J n)).eventually
        (Iio_mem_nhds hpos)
    have hlocal :=
      eventually_neighborhood_subset_open (J n) (hQ n) (hJQ n)
    have hlarge : ∀ᶠ q : ℕ in atTop, n ≤ q := eventually_ge_atTop n
    rcases
        (hlarge.and (hsmallTrace.and (hsmallVolume.and hlocal))).exists with
      ⟨q, hnq, hqTrace, hqVolume, hqLocal⟩
    exact ⟨q, hnq, hqTrace, hqVolume, hqLocal⟩
  choose k hk hcost hvolume hlocal using hexists
  have hradius : Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds tendsto_junctionRadius_zero
    · exact fun n => (junctionRadius_pos (k n)).le
    · exact fun n => antitone_junctionRadius (hk n)
  have hbudget : Tendsto (fun n => ENNReal.ofReal (junctionRadius n))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_junctionRadius_zero
  have htrace : Tendsto (fun n =>
      weightedTraceCost lam
        (S n ∩ neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbudget
    · exact fun _ => bot_le
    · exact fun n => (hcost n).le
  have harea : Tendsto (fun n =>
      volume (neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbudget
    · exact fun _ => bot_le
    · exact fun n => (hvolume n).le
  exact ⟨k, hk, hradius, htrace, harea, hlocal,
    fun n => ⟨(hcost n).le, (hvolume n).le⟩⟩

/-- Select candidate localization radii after each finite junction family is
known, controlling old trace, area, open-set locality, pairwise disjointness,
and the cardinality-sensitive spherical allowance.  This theorem does not
assert sphere transversality or construct a repaired smooth domain. -/
theorem exists_approximantDependent_neighborhoods_inside_with_sphericalBudget
    (lam : ℝ) (hlam : 1 < lam)
    (S : ℕ → Set PlanePoint) (hS : ∀ n, IsClosed (S n))
    (hfinite : ∀ n, weightedTraceCost lam (S n) ≠ ⊤)
    (J : ℕ → Finset PlanePoint) (Q : ℕ → Set PlanePoint)
    (hQ : ∀ n, IsOpen (Q n))
    (hJQ : ∀ n, (↑(J n) : Set PlanePoint) ⊆ Q n) :
    ∃ k : ℕ → ℕ,
      (∀ n, n ≤ k n) ∧
      Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (S n ∩ neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        volume (neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (junctionSpheres (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      (∀ n, neighborhood (J n) (junctionRadius (k n)) ⊆ Q n) ∧
      (∀ n, Set.Pairwise (↑(J n) : Set PlanePoint)
        (Function.onFun Disjoint fun p =>
          junctionBall p (junctionRadius (k n)))) ∧
      (∀ n,
        junctionSphereCostBudget lam (J n) (junctionRadius (k n)) ≤
          ENNReal.ofReal (junctionRadius n)) ∧
      ∀ n,
        weightedTraceCost lam
            (S n ∩ neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) ∧
        volume (neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) := by
  have hexists : ∀ n, ∃ q : ℕ, n ≤ q ∧
      weightedTraceCost lam
          (S n ∩ neighborhood (J n) (junctionRadius q)) <
        ENNReal.ofReal (junctionRadius n) ∧
      volume (neighborhood (J n) (junctionRadius q)) <
        ENNReal.ofReal (junctionRadius n) ∧
      junctionSphereCostBudget lam (J n) (junctionRadius q) <
        ENNReal.ofReal (junctionRadius n) ∧
      Set.Pairwise (↑(J n) : Set PlanePoint)
        (Function.onFun Disjoint fun p =>
          junctionBall p (junctionRadius q)) ∧
      neighborhood (J n) (junctionRadius q) ⊆ Q n := by
    intro n
    have hpos : 0 < ENNReal.ofReal (junctionRadius n) :=
      ENNReal.ofReal_pos.2 (junctionRadius_pos n)
    have hsmallTrace :=
      (tendsto_weightedTraceCost_inter_neighborhood_zero
        lam (hS n) (hfinite n) (J n)).eventually (Iio_mem_nhds hpos)
    have hsmallVolume :=
      (tendsto_volume_neighborhood_zero (J n)).eventually
        (Iio_mem_nhds hpos)
    have hsmallSphere :=
      (tendsto_junctionSphereCostBudget_zero lam (J n)).eventually
        (Iio_mem_nhds hpos)
    have hdisjoint := eventually_pairwiseDisjoint_junctionBalls (J n)
    have hlocal :=
      eventually_neighborhood_subset_open (J n) (hQ n) (hJQ n)
    have hlarge : ∀ᶠ q : ℕ in atTop, n ≤ q := eventually_ge_atTop n
    rcases
        (hlarge.and
          (hsmallTrace.and
            (hsmallVolume.and
              (hsmallSphere.and (hdisjoint.and hlocal))))).exists with
      ⟨q, hnq, hqTrace, hqVolume, hqSphere, hqDisjoint, hqLocal⟩
    exact
      ⟨q, hnq, hqTrace, hqVolume, hqSphere, hqDisjoint, hqLocal⟩
  choose k hk hcost hvolume hsphere hdisjoint hlocal using hexists
  have hradius : Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds tendsto_junctionRadius_zero
    · exact fun n => (junctionRadius_pos (k n)).le
    · exact fun n => antitone_junctionRadius (hk n)
  have hbudget : Tendsto (fun n => ENNReal.ofReal (junctionRadius n))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_junctionRadius_zero
  have htrace : Tendsto (fun n =>
      weightedTraceCost lam
        (S n ∩ neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbudget
    · exact fun _ => bot_le
    · exact fun n => (hcost n).le
  have harea : Tendsto (fun n =>
      volume (neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hbudget
    · exact fun _ => bot_le
    · exact fun n => (hvolume n).le
  have hsphereBudget : ∀ n,
      junctionSphereCostBudget lam (J n) (junctionRadius (k n)) ≤
        ENNReal.ofReal (junctionRadius n) :=
    fun n => (hsphere n).le
  have hsphereCost : Tendsto (fun n =>
      weightedTraceCost lam
        (junctionSpheres (J n) (junctionRadius (k n))))
      atTop (𝓝 0) :=
    tendsto_weightedTraceCost_junctionSpheres_zero_of_budget
      hlam J k (fun n => ENNReal.ofReal (junctionRadius n))
      hbudget hsphereBudget
  exact ⟨k, hk, hradius, htrace, harea, hsphereCost, hlocal,
    hdisjoint, hsphereBudget,
    fun n => ⟨(hcost n).le, (hvolume n).le⟩⟩

/-- A repair cost audit needs only a complete frontier inclusion: unchanged raw
trace outside the closed repair region plus the entire auxiliary trace inside.
No tube or density-zone assumption appears. -/
theorem smoothCost_le_outside_add_auxiliary_of_frontier_subset
    (lam : ℝ) {raw repaired Q R : Set PlanePoint} (hQ : IsClosed Q)
    (hfrontier :
      frontier repaired ⊆ (frontier raw ∩ Qᶜ) ∪ R) :
    smoothCost lam repaired ≤
      smoothCostOn lam raw Qᶜ + weightedTraceCost lam R := by
  rw [smoothCost_eq_weightedTraceCost_frontier,
    smoothCostOn_eq_weightedTraceCost_frontier_inter
      lam raw hQ.isOpen_compl.measurableSet]
  exact (weightedTraceCost_mono lam hfrontier).trans
    (weightedTraceCost_union_le lam _ _)

/-- A sharp raw-splice bound with finite old costs, finite inserted cost, and a
vanishing seam is eventually finite term by term.  This is the tail-finiteness
needed before selecting shrinking neighborhoods of the complete raw frontier;
it does not replace the quantitative repair. -/
theorem eventually_smoothCost_ne_top_of_outside_add_seam
    (lam : ℝ) (old raw : ℕ → Set PlanePoint) (W : Set PlanePoint)
    (insertedCost : ENNReal) (seam : ℕ → ENNReal)
    (hold : ∀ n, smoothCost lam (old n) < ⊤)
    (hinserted : insertedCost < ⊤)
    (hseam : Tendsto seam atTop (𝓝 0))
    (hbound : ∀ n, smoothCost lam (raw n) ≤
      smoothCostOn lam (old n) W + insertedCost + seam n) :
    ∀ᶠ n : ℕ in atTop, smoothCost lam (raw n) < ⊤ := by
  have hseamFinite : ∀ᶠ n : ℕ in atTop, seam n < ⊤ :=
    hseam.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  filter_upwards [hseamFinite] with n hn
  have hlocal :
      smoothCostOn lam (old n) W ≤ smoothCost lam (old n) := by
    calc
      smoothCostOn lam (old n) W ≤
          smoothCostOn lam (old n) univ :=
        smoothCostOn_mono lam (old n) (subset_univ W)
      _ = smoothCost lam (old n) := by
        simp only [smoothCostOn, smoothCost, Measure.restrict_univ]
  have hlocalFinite : smoothCostOn lam (old n) W < ⊤ :=
    hlocal.trans_lt (hold n)
  exact (hbound n).trans_lt
    (ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨hlocalFinite, hinserted⟩, hn⟩)

/-- Modifying each smooth approximant only in a region of vanishing area
preserves its target convergence. -/
theorem SmoothSequence.convergesTo_of_vanishing_modification
    (A B : SmoothSequence) {E : Set PlanePoint}
    (hA : A.ConvergesTo E) (Q : ℕ → Set PlanePoint)
    (hQ : Tendsto (fun n => volume (Q n)) atTop (𝓝 0))
    (hmodify : ∀ n, (B.carrier n ∆ A.carrier n) ⊆ Q n) :
    B.ConvergesTo E := by
  unfold SmoothSequence.ConvergesTo at hA ⊢
  have hupper : Tendsto (fun n =>
      volume (Q n) +
        characteristicDistance (A.carrier n) E) atTop (𝓝 0) := by
    simpa using hQ.add hA
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
  · exact fun _ => bot_le
  · intro n
    calc
      characteristicDistance (B.carrier n) E ≤
          characteristicDistance (B.carrier n) (A.carrier n) +
            characteristicDistance (A.carrier n) E :=
        measure_symmDiff_le _ _ _
      _ ≤ volume (Q n) +
            characteristicDistance (A.carrier n) E :=
        add_le_add (measure_mono (hmodify n)) le_rfl

/-- Auxiliary replacement traces may leave every protected graph tube.  Their
complete weighted cost still vanishes whenever their global Euclidean `H¹`
length vanishes; this uses the global density bound rather than a constant-zone
shortcut. -/
theorem tendsto_weightedTraceCost_of_global_auxiliaryLength_zero
    {lam : ℝ} (hlam : 1 < lam) (R : ℕ → Set PlanePoint)
    (hR : Tendsto (fun n =>
      (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph '' R n)) atTop (𝓝 0)) :
    Tendsto (fun n => weightedTraceCost lam (R n)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n =>
      ENNReal.ofReal lam *
        (μH[1] : Measure EuclideanPlane)
          (planeEuclideanHomeomorph '' R n)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hR
      (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => bot_le)
      (fun n => weightedTraceCost_le_density_mul_hausdorff hlam (R n))

/-- All possible nonsmooth junctions of a rectangular raw splice: old/new
frontier crossings on the cut and the four rectangle corners. -/
def spliceJunctionSet (U G : Set PlanePoint) (l r d u : ℝ) :
    Set PlanePoint :=
  ((frontier U ∪ frontier G) ∩
      frontier (closedCutRectangle l r d u)) ∪
    {(l, d), (l, u), (r, d), (r, u)}

lemma openSpliceIn_inter_interior
    {U G W : Set PlanePoint} (hG : IsOpen G) :
    openSpliceIn U G W ∩ interior W = G ∩ interior W := by
  rw [openSpliceIn]
  calc
    interior (spliceIn U G W) ∩ interior W =
        interior (spliceIn U G W ∩ interior W) := by
      rw [interior_inter, interior_interior]
    _ = interior (G ∩ interior W) := by
      rw [spliceIn_inter_interior]
    _ = G ∩ interior W :=
      interior_eq_iff_isOpen.mpr (hG.inter isOpen_interior)

lemma openSpliceIn_inter_interior_compl
    {U G W : Set PlanePoint} (hU : IsOpen U) :
    openSpliceIn U G W ∩ interior Wᶜ = U ∩ interior Wᶜ := by
  rw [openSpliceIn]
  calc
    interior (spliceIn U G W) ∩ interior Wᶜ =
        interior (spliceIn U G W ∩ interior Wᶜ) := by
      rw [interior_inter, interior_interior]
    _ = interior (U ∩ interior Wᶜ) := by
      rw [spliceIn_inter_interior_compl]
    _ = U ∩ interior Wᶜ :=
      interior_eq_iff_isOpen.mpr (hU.inter isOpen_interior)

lemma openSpliceIn_inter_eq_interior_window_of_local_labels
    {U G W N : Set PlanePoint} (hN : IsOpen N)
    (hU : N ⊆ Uᶜ) (hG : N ⊆ G) :
    openSpliceIn U G W ∩ N = interior W ∩ N := by
  have hraw : spliceIn U G W ∩ N = W ∩ N := by
    ext q
    constructor
    · rintro ⟨hq, hqN⟩
      rcases hq with hq | hq
      · exact False.elim ((hU hqN) hq.1)
      · exact ⟨hq.2, hqN⟩
    · rintro ⟨hqW, hqN⟩
      exact ⟨Or.inr ⟨hG hqN, hqW⟩, hqN⟩
  rw [openSpliceIn]
  calc
    interior (spliceIn U G W) ∩ N =
        interior (spliceIn U G W) ∩ interior N := by
      rw [interior_eq_iff_isOpen.mpr hN]
    _ = interior (spliceIn U G W ∩ N) := interior_inter.symm
    _ = interior (W ∩ N) := congrArg interior hraw
    _ = interior W ∩ interior N := interior_inter
    _ = interior W ∩ N := by rw [interior_eq_iff_isOpen.mpr hN]

lemma openSpliceIn_inter_eq_interior_compl_window_of_local_labels
    {U G W N : Set PlanePoint} (hN : IsOpen N)
    (hU : N ⊆ U) (hG : N ⊆ Gᶜ) :
    openSpliceIn U G W ∩ N = interior Wᶜ ∩ N := by
  have hraw : spliceIn U G W ∩ N = Wᶜ ∩ N := by
    ext q
    constructor
    · rintro ⟨hq, hqN⟩
      rcases hq with hq | hq
      · exact ⟨hq.2, hqN⟩
      · exact False.elim ((hG hqN) hq.1)
    · rintro ⟨hqW, hqN⟩
      exact ⟨Or.inl ⟨hU hqN, hqW⟩, hqN⟩
  rw [openSpliceIn]
  calc
    interior (spliceIn U G W) ∩ N =
        interior (spliceIn U G W) ∩ interior N := by
      rw [interior_eq_iff_isOpen.mpr hN]
    _ = interior (spliceIn U G W ∩ N) := interior_inter.symm
    _ = interior (Wᶜ ∩ N) := congrArg interior hraw
    _ = interior Wᶜ ∩ interior N := interior_inter
    _ = interior Wᶜ ∩ N := by rw [interior_eq_iff_isOpen.mpr hN]

lemma isSmoothDomain_fst_lt (c : ℝ) :
    IsSmoothDomain {p : PlanePoint | p.1 < c} := by
  rw [show {p : PlanePoint | p.1 < c} =
      {p | p.1 - c < 0} by ext; simp]
  apply isSmoothDomain_sublevel_of_regular
  · fun_prop
  · intro p _hp hzero
    have hder : HasFDerivAt (fun q : PlanePoint => q.1 - c)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
      simpa using (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sub_const c
    rw [hder.fderiv] at hzero
    have heval := congrArg
      (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hzero
    simpa using heval

lemma isSmoothDomain_lt_fst (c : ℝ) :
    IsSmoothDomain {p : PlanePoint | c < p.1} := by
  rw [show {p : PlanePoint | c < p.1} =
      {p | c - p.1 < 0} by ext; simp]
  apply isSmoothDomain_sublevel_of_regular
  · fun_prop
  · intro p _hp hzero
    have hder : HasFDerivAt (fun q : PlanePoint => c - q.1)
        (-(ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
      convert (hasFDerivAt_const (x := p) (c := c)).sub
        (hasFDerivAt_fst (𝕜 := ℝ) (p := p)) using 1 <;> ext <;> simp
    rw [hder.fderiv] at hzero
    have heval := congrArg
      (fun L : PlanePoint →L[ℝ] ℝ => L (1, 0)) hzero
    simpa using heval

lemma isSmoothDomain_snd_lt (c : ℝ) :
    IsSmoothDomain {p : PlanePoint | p.2 < c} := by
  simpa only using isSmoothDomain_subgraph
    (f := fun _ : ℝ => c) contDiff_const

lemma isSmoothDomain_lt_snd (c : ℝ) :
    IsSmoothDomain {p : PlanePoint | c < p.2} := by
  simpa only using isSmoothDomain_supergraph
    (f := fun _ : ℝ => c) contDiff_const

/-- At a non-corner point of a rectangular boundary, the rectangle and its
exterior have opposite smooth half-plane models on one common neighborhood. -/
lemma exists_local_halfplane_models_closedCutRectangle
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u) {p : PlanePoint}
    (hp : p ∈ frontier (closedCutRectangle l r d u))
    (hpCorners : p ∉ ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint)) :
    ∃ (V inside outside : Set PlanePoint),
      IsOpen V ∧ p ∈ V ∧ IsSmoothDomain inside ∧ IsSmoothDomain outside ∧
      interior (closedCutRectangle l r d u) ∩ V = inside ∩ V ∧
      interior ((closedCutRectangle l r d u)ᶜ) ∩ V = outside ∩ V := by
  have hpW : p ∈ closedCutRectangle l r d u :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset hp
  rcases hpW with ⟨hpx, hpy⟩
  have hfaces := frontier_closedCutRectangle_subset_lines hlr hdu hp
  rcases hfaces with ((hpL | hpR) | hpD) | hpU
  · change p.1 = l at hpL
    have hpDne : p.2 ≠ d := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inl (Prod.ext hpL h)
    have hpUne : p.2 ≠ u := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inl (Prod.ext hpL h))
    have hpyd : d < p.2 := lt_of_le_of_ne hpy.1 hpDne.symm
    have hpyu : p.2 < u := lt_of_le_of_ne hpy.2 hpUne
    let V : Set PlanePoint :=
      Prod.fst ⁻¹' Iio r ∩ Prod.snd ⁻¹' Ioo d u
    let inside : Set PlanePoint := {q | l < q.1}
    let outside : Set PlanePoint := {q | q.1 < l}
    refine ⟨V, inside, outside,
      (isOpen_Iio.preimage continuous_fst).inter
        (isOpen_Ioo.preimage continuous_snd), ?_,
      isSmoothDomain_lt_fst l, isSmoothDomain_fst_lt l, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Iio, hpL] using hlr,
        by simpa only [mem_preimage, mem_Ioo] using ⟨hpyd, hpyu⟩⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [V, inside, mem_inter_iff, mem_prod, mem_Ioo,
        mem_preimage, mem_Iio, mem_ofPred_eq]
      tauto
    · rw [closedCutRectangle,
        (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      change
        ((¬ ((l ≤ q.1 ∧ q.1 ≤ r) ∧ (d ≤ q.2 ∧ q.2 ≤ u))) ∧
            (q.1 < r ∧ (d < q.2 ∧ q.2 < u))) ↔
          q.1 < l ∧ (q.1 < r ∧ (d < q.2 ∧ q.2 < u))
      constructor
      · rintro ⟨hnot, hxr, hyd, hyu⟩
        refine ⟨?_, hxr, hyd, hyu⟩
        by_contra hxl
        exact hnot ⟨⟨le_of_not_gt hxl, hxr.le⟩, ⟨hyd.le, hyu.le⟩⟩
      · rintro ⟨hxl, hxr, hyd, hyu⟩
        exact ⟨fun hW => (not_lt_of_ge hW.1.1) hxl, hxr, hyd, hyu⟩
  · change p.1 = r at hpR
    have hpDne : p.2 ≠ d := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inl (Prod.ext hpR h)))
    have hpUne : p.2 ≠ u := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inr (Prod.ext hpR h)))
    have hpyd : d < p.2 := lt_of_le_of_ne hpy.1 hpDne.symm
    have hpyu : p.2 < u := lt_of_le_of_ne hpy.2 hpUne
    let V : Set PlanePoint :=
      Prod.fst ⁻¹' Ioi l ∩ Prod.snd ⁻¹' Ioo d u
    let inside : Set PlanePoint := {q | q.1 < r}
    let outside : Set PlanePoint := {q | r < q.1}
    refine ⟨V, inside, outside,
      (isOpen_Ioi.preimage continuous_fst).inter
        (isOpen_Ioo.preimage continuous_snd), ?_,
      isSmoothDomain_fst_lt r, isSmoothDomain_lt_fst r, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Ioi, hpR] using hlr,
        by simpa only [mem_preimage, mem_Ioo] using ⟨hpyd, hpyu⟩⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [V, inside, mem_inter_iff, mem_prod, mem_Ioo,
        mem_preimage, mem_Ioi, mem_ofPred_eq]
      tauto
    · rw [closedCutRectangle,
        (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      change
        ((¬ ((l ≤ q.1 ∧ q.1 ≤ r) ∧ (d ≤ q.2 ∧ q.2 ≤ u))) ∧
            (l < q.1 ∧ (d < q.2 ∧ q.2 < u))) ↔
          r < q.1 ∧ (l < q.1 ∧ (d < q.2 ∧ q.2 < u))
      constructor
      · rintro ⟨hnot, hlx, hyd, hyu⟩
        refine ⟨?_, hlx, hyd, hyu⟩
        by_contra hxr
        exact hnot ⟨⟨hlx.le, le_of_not_gt hxr⟩, ⟨hyd.le, hyu.le⟩⟩
      · rintro ⟨hxr, hlx, hyd, hyu⟩
        exact ⟨fun hW => (not_lt_of_ge hW.1.2) hxr, hlx, hyd, hyu⟩
  · change p.2 = d at hpD
    have hpLne : p.1 ≠ l := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inl (Prod.ext h hpD)
    have hpRne : p.1 ≠ r := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inl (Prod.ext h hpD)))
    have hplx : l < p.1 := lt_of_le_of_ne hpx.1 hpLne.symm
    have hpxr : p.1 < r := lt_of_le_of_ne hpx.2 hpRne
    let V : Set PlanePoint :=
      Prod.fst ⁻¹' Ioo l r ∩ Prod.snd ⁻¹' Iio u
    let inside : Set PlanePoint := {q | d < q.2}
    let outside : Set PlanePoint := {q | q.2 < d}
    refine ⟨V, inside, outside,
      (isOpen_Ioo.preimage continuous_fst).inter
        (isOpen_Iio.preimage continuous_snd), ?_,
      isSmoothDomain_lt_snd d, isSmoothDomain_snd_lt d, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Ioo] using ⟨hplx, hpxr⟩,
        by simpa only [mem_preimage, mem_Iio, hpD] using hdu⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [V, inside, mem_inter_iff, mem_prod, mem_Ioo,
        mem_preimage, mem_Iio, mem_ofPred_eq]
      tauto
    · rw [closedCutRectangle,
        (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      change
        ((¬ ((l ≤ q.1 ∧ q.1 ≤ r) ∧ (d ≤ q.2 ∧ q.2 ≤ u))) ∧
            ((l < q.1 ∧ q.1 < r) ∧ q.2 < u)) ↔
          q.2 < d ∧ ((l < q.1 ∧ q.1 < r) ∧ q.2 < u)
      constructor
      · rintro ⟨hnot, ⟨hlx, hxr⟩, hyu⟩
        refine ⟨?_, ⟨hlx, hxr⟩, hyu⟩
        by_contra hyd
        exact hnot ⟨⟨hlx.le, hxr.le⟩, ⟨le_of_not_gt hyd, hyu.le⟩⟩
      · rintro ⟨hyd, ⟨hlx, hxr⟩, hyu⟩
        exact ⟨fun hW => (not_lt_of_ge hW.2.1) hyd, ⟨hlx, hxr⟩, hyu⟩
  · change p.2 = u at hpU
    have hpLne : p.1 ≠ l := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inl (Prod.ext h hpU))
    have hpRne : p.1 ≠ r := by
      intro h
      apply hpCorners
      simp only [mem_insert_iff, mem_singleton_iff]
      exact Or.inr (Or.inr (Or.inr (Prod.ext h hpU)))
    have hplx : l < p.1 := lt_of_le_of_ne hpx.1 hpLne.symm
    have hpxr : p.1 < r := lt_of_le_of_ne hpx.2 hpRne
    let V : Set PlanePoint :=
      Prod.fst ⁻¹' Ioo l r ∩ Prod.snd ⁻¹' Ioi d
    let inside : Set PlanePoint := {q | q.2 < u}
    let outside : Set PlanePoint := {q | u < q.2}
    refine ⟨V, inside, outside,
      (isOpen_Ioo.preimage continuous_fst).inter
        (isOpen_Ioi.preimage continuous_snd), ?_,
      isSmoothDomain_snd_lt u, isSmoothDomain_lt_snd u, ?_, ?_⟩
    · exact ⟨by simpa only [mem_preimage, mem_Ioo] using ⟨hplx, hpxr⟩,
        by simpa only [mem_preimage, mem_Ioi, hpU] using hdu⟩
    · rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
      ext q
      simp only [V, inside, mem_inter_iff, mem_prod, mem_Ioo,
        mem_preimage, mem_Ioi, mem_ofPred_eq]
      tauto
    · rw [closedCutRectangle,
        (isClosed_Icc.prod isClosed_Icc).isOpen_compl.interior_eq]
      ext q
      change
        ((¬ ((l ≤ q.1 ∧ q.1 ≤ r) ∧ (d ≤ q.2 ∧ q.2 ≤ u))) ∧
            ((l < q.1 ∧ q.1 < r) ∧ d < q.2)) ↔
          u < q.2 ∧ ((l < q.1 ∧ q.1 < r) ∧ d < q.2)
      constructor
      · rintro ⟨hnot, ⟨hlx, hxr⟩, hyd⟩
        refine ⟨?_, ⟨hlx, hxr⟩, hyd⟩
        by_contra hyu
        exact hnot ⟨⟨hlx.le, hxr.le⟩, ⟨hyd.le, le_of_not_gt hyu⟩⟩
      · rintro ⟨hyu, ⟨hlx, hxr⟩, hyd⟩
        exact ⟨fun hW => (not_lt_of_ge hW.2.2) hyu, ⟨hlx, hxr⟩, hyd⟩


/-- The canonical rectangular splice is already a literal smooth domain at
all of its frontier points except input-boundary/cut crossings and rectangle
corners. Thus every possible smoothness defect is contained in the exact finite
junction set used by the quantitative repair selector. -/
theorem openSpliceIn_locally_smooth_away_from_spliceJunctionSet
    {U G : Set PlanePoint} (hU : IsSmoothDomain U) (hG : IsSmoothDomain G)
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u) {p : PlanePoint}
    (hp : p ∈ frontier
      (openSpliceIn U G (closedCutRectangle l r d u)))
    (hpJ : p ∉ spliceJunctionSet U G l r d u) :
    ∃ (M V : Set PlanePoint),
      IsSmoothDomain M ∧ IsOpen V ∧ p ∈ V ∧
      openSpliceIn U G (closedCutRectangle l r d u) ∩ V = M ∩ V := by
  let W := closedCutRectangle l r d u
  let O := openSpliceIn U G W
  by_cases hpCut : p ∈ frontier W
  · have hpNotU : p ∉ frontier U := by
      intro hpU
      apply hpJ
      exact Or.inl ⟨Or.inl hpU, hpCut⟩
    have hpNotG : p ∉ frontier G := by
      intro hpG
      apply hpJ
      exact Or.inl ⟨Or.inr hpG, hpCut⟩
    have hpNotCorners :
        p ∉ ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint) := by
      intro hpCorner
      apply hpJ
      exact Or.inr hpCorner
    obtain ⟨V₀, Minside, Moutside, hV₀, hpV₀,
        hMinside, hMoutside, hinside, houtside⟩ :=
      exists_local_halfplane_models_closedCutRectangle
        hlr hdu hpCut hpNotCorners
    have hpUregion : p ∈ interior U ∪ interior Uᶜ := by
      have hp' : p ∈ (frontier U)ᶜ := hpNotU
      rwa [compl_frontier_eq_union_interior] at hp'
    have hpGregion : p ∈ interior G ∪ interior Gᶜ := by
      have hp' : p ∈ (frontier G)ᶜ := hpNotG
      rwa [compl_frontier_eq_union_interior] at hp'
    rcases hpUregion with hpUint | hpUout
    · rcases hpGregion with hpGint | hpGout
      · exfalso
        let N := interior U ∩ interior G
        have hNopen : IsOpen N := isOpen_interior.inter isOpen_interior
        have hNsub : N ⊆ O := by
          intro q hq
          change q ∈ interior (spliceIn U G W)
          apply interior_maximal (t := N) _ hNopen hq
          intro z hz
          by_cases hzW : z ∈ W
          · exact Or.inr ⟨interior_subset hz.2, hzW⟩
          · exact Or.inl ⟨interior_subset hz.1, hzW⟩
        have hpInt : p ∈ interior O :=
          interior_maximal hNsub hNopen ⟨hpUint, hpGint⟩
        exact Set.disjoint_left.1 disjoint_interior_frontier hpInt hp
      · let N := interior U ∩ interior Gᶜ
        have hNopen : IsOpen N := isOpen_interior.inter isOpen_interior
        have hlabel : O ∩ N = interior Wᶜ ∩ N := by
          exact openSpliceIn_inter_eq_interior_compl_window_of_local_labels
            hNopen (fun _ hq => interior_subset hq.1)
              (fun _ hq => interior_subset hq.2)
        let V := N ∩ V₀
        refine ⟨Moutside, V, hMoutside, hNopen.inter hV₀,
          ⟨⟨hpUint, hpGout⟩, hpV₀⟩, ?_⟩
        ext q
        have hlabelIff (hqN : q ∈ N) :
            q ∈ O ↔ q ∈ interior Wᶜ := by
          have h := Set.ext_iff.mp hlabel q
          simp only [mem_inter_iff] at h
          tauto
        have houtsideIff (hqV₀ : q ∈ V₀) :
            q ∈ interior Wᶜ ↔ q ∈ Moutside := by
          have h := Set.ext_iff.mp houtside q
          simp only [mem_inter_iff] at h
          tauto
        constructor
        · rintro ⟨hqO, hqN, hqV₀⟩
          exact ⟨(houtsideIff hqV₀).mp ((hlabelIff hqN).mp hqO),
            hqN, hqV₀⟩
        · rintro ⟨hqM, hqN, hqV₀⟩
          exact ⟨(hlabelIff hqN).mpr ((houtsideIff hqV₀).mpr hqM),
            hqN, hqV₀⟩
    · rcases hpGregion with hpGint | hpGout
      · let N := interior Uᶜ ∩ interior G
        have hNopen : IsOpen N := isOpen_interior.inter isOpen_interior
        have hlabel : O ∩ N = interior W ∩ N := by
          exact openSpliceIn_inter_eq_interior_window_of_local_labels
            hNopen (fun _ hq => interior_subset hq.1)
              (fun _ hq => interior_subset hq.2)
        let V := N ∩ V₀
        refine ⟨Minside, V, hMinside, hNopen.inter hV₀,
          ⟨⟨hpUout, hpGint⟩, hpV₀⟩, ?_⟩
        ext q
        have hlabelIff (hqN : q ∈ N) :
            q ∈ O ↔ q ∈ interior W := by
          have h := Set.ext_iff.mp hlabel q
          simp only [mem_inter_iff] at h
          tauto
        have hinsideIff (hqV₀ : q ∈ V₀) :
            q ∈ interior W ↔ q ∈ Minside := by
          have h := Set.ext_iff.mp hinside q
          simp only [mem_inter_iff] at h
          tauto
        constructor
        · rintro ⟨hqO, hqN, hqV₀⟩
          exact ⟨(hinsideIff hqV₀).mp ((hlabelIff hqN).mp hqO),
            hqN, hqV₀⟩
        · rintro ⟨hqM, hqN, hqV₀⟩
          exact ⟨(hlabelIff hqN).mpr ((hinsideIff hqV₀).mpr hqM),
            hqN, hqV₀⟩
      · exfalso
        let N := interior Uᶜ ∩ interior Gᶜ
        have hNopen : IsOpen N := isOpen_interior.inter isOpen_interior
        have hNsub : N ⊆ Oᶜ := by
          intro q hq hqO
          have hqRaw : q ∈ spliceIn U G W :=
            openSpliceIn_subset_spliceIn U G W hqO
          rcases hqRaw with hqRaw | hqRaw
          · exact (interior_subset hq.1) hqRaw.1
          · exact (interior_subset hq.2) hqRaw.1
        have hpInt : p ∈ interior Oᶜ :=
          interior_maximal hNsub hNopen ⟨hpUout, hpGout⟩
        have hpFront : p ∈ frontier Oᶜ := by
          simpa only [frontier_compl] using hp
        exact Set.disjoint_left.1 disjoint_interior_frontier hpInt hpFront
  · have hpRegion : p ∈ interior W ∪ interior Wᶜ := by
      have hp' : p ∈ (frontier W)ᶜ := hpCut
      rwa [compl_frontier_eq_union_interior] at hp'
    rcases hpRegion with hpInside | hpOutside
    · refine ⟨G, interior W, hG, isOpen_interior, hpInside, ?_⟩
      exact openSpliceIn_inter_interior hG.isOpen
    · refine ⟨U, interior Wᶜ, hU, isOpen_interior, hpOutside, ?_⟩
      exact openSpliceIn_inter_interior_compl hU.isOpen


/-- Every declared splice junction lies on the cutting rectangle itself. The
four corners are retained even when no input frontier crosses there. -/
theorem spliceJunctionSet_subset_frontier_closedCutRectangle
    {U G : Set PlanePoint} {l r d u : ℝ}
    (hlr : l < r) (hdu : d < u) :
    spliceJunctionSet U G l r d u ⊆
      frontier (closedCutRectangle l r d u) := by
  intro p hp
  rcases hp with hpCross | hpCorner
  · exact hpCross.2
  · simp only [mem_insert_iff, mem_singleton_iff] at hpCorner
    rcases hpCorner with rfl | rfl | rfl | rfl <;>
      rw [closedCutRectangle, frontier_prod_eq, closure_Icc, closure_Icc,
        frontier_Icc hlr.le, frontier_Icc hdu.le] <;> simp [hlr.le, hdu.le]

/-- A core strictly inside the selected rectangle contains no splice junction.
This is the center-exclusion fact needed before choosing closed repair balls. -/
theorem spliceJunctionSet_subset_compl_of_core
    {U G K : Set PlanePoint} {l r d u : ℝ}
    (hlr : l < r) (hdu : d < u)
    (hK : K ⊆ interior (closedCutRectangle l r d u)) :
    spliceJunctionSet U G l r d u ⊆ Kᶜ := by
  intro p hpJ hpK
  exact Set.disjoint_left.1 disjoint_interior_frontier
    (hK hpK) (spliceJunctionSet_subset_frontier_closedCutRectangle
      hlr hdu hpJ)

/-- Once the exact junction locus is contained in an open repair region, every
frontier point outside that region already has a literal local smooth-domain
model. No smoothness or defining-function premise remains for the exterior. -/
theorem openSpliceIn_locally_smooth_outside_junctionNeighborhood
    {U G Q : Set PlanePoint} (hU : IsSmoothDomain U) (hG : IsSmoothDomain G)
    {l r d u : ℝ} (hlr : l < r) (hdu : d < u)
    (hJQ : spliceJunctionSet U G l r d u ⊆ Q)
    {p : PlanePoint}
    (hp : p ∈ frontier
      (openSpliceIn U G (closedCutRectangle l r d u)))
    (hpQ : p ∈ Qᶜ) :
    ∃ (M V : Set PlanePoint),
      IsSmoothDomain M ∧ IsOpen V ∧ p ∈ V ∧
      openSpliceIn U G (closedCutRectangle l r d u) ∩ V = M ∩ V := by
  exact openSpliceIn_locally_smooth_away_from_spliceJunctionSet
    hU hG hlr hdu hp (fun hpJ => hpQ (hJQ hpJ))

/-- Finite face crossings imply a finite complete junction set.  No
generic-position assumption is used, so coincident crossings and corners are
retained. -/
theorem finite_spliceJunctionSet
    {U G : Set PlanePoint} {l r d u : ℝ}
    (hlr : l < r) (hdu : d < u)
    (hUl : (frontier U ∩ closedCutRectangle l r d u ∩
      verticalLine l).Finite)
    (hUr : (frontier U ∩ closedCutRectangle l r d u ∩
      verticalLine r).Finite)
    (hUd : (frontier U ∩ closedCutRectangle l r d u ∩
      horizontalLine d).Finite)
    (hUu : (frontier U ∩ closedCutRectangle l r d u ∩
      horizontalLine u).Finite)
    (hGl : (frontier G ∩ closedCutRectangle l r d u ∩
      verticalLine l).Finite)
    (hGr : (frontier G ∩ closedCutRectangle l r d u ∩
      verticalLine r).Finite)
    (hGd : (frontier G ∩ closedCutRectangle l r d u ∩
      horizontalLine d).Finite)
    (hGu : (frontier G ∩ closedCutRectangle l r d u ∩
      horizontalLine u).Finite) :
    (spliceJunctionSet U G l r d u).Finite := by
  have hside : ∀ (F : Set PlanePoint),
      (F ∩ closedCutRectangle l r d u ∩ verticalLine l).Finite →
      (F ∩ closedCutRectangle l r d u ∩ verticalLine r).Finite →
      (F ∩ closedCutRectangle l r d u ∩ horizontalLine d).Finite →
      (F ∩ closedCutRectangle l r d u ∩ horizontalLine u).Finite →
      (F ∩ frontier (closedCutRectangle l r d u)).Finite := by
    intro F hFl hFr hFd hFu
    apply (((hFl.union hFr).union hFd).union hFu).subset
    rintro p ⟨hpF, hpBoundary⟩
    have hpWindow : p ∈ closedCutRectangle l r d u :=
      (isClosed_Icc.prod isClosed_Icc).frontier_subset hpBoundary
    have hlines :=
      frontier_closedCutRectangle_subset_lines hlr hdu hpBoundary
    rcases hlines with ((hpL | hpR) | hpD) | hpU
    · exact Or.inl (Or.inl (Or.inl ⟨⟨hpF, hpWindow⟩, hpL⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨⟨hpF, hpWindow⟩, hpR⟩))
    · exact Or.inl (Or.inr ⟨⟨hpF, hpWindow⟩, hpD⟩)
    · exact Or.inr ⟨⟨hpF, hpWindow⟩, hpU⟩
  have hU := hside (frontier U) hUl hUr hUd hUu
  have hG := hside (frontier G) hGl hGr hGd hGu
  have hcrossings :
      ((frontier U ∪ frontier G) ∩
        frontier (closedCutRectangle l r d u)).Finite := by
    apply (hU.union hG).subset
    rintro p ⟨hpUG, hpBoundary⟩
    rcases hpUG with hpU | hpG
    · exact Or.inl ⟨hpU, hpBoundary⟩
    · exact Or.inr ⟨hpG, hpBoundary⟩
  have hcorners :
      ({(l, d), (l, u), (r, d), (r, u)} : Set PlanePoint).Finite := by
    simp
  exact hcrossings.union hcorners

/-- The regular-finite cut certificates produced by the raw-splice selector
therefore yield a finite junction set whenever the selected rectangle face is
contained in the corresponding selection collar. -/
theorem finite_spliceJunctionSet_of_regularFiniteCuts
    {A B KL KR KD KU : Set PlanePoint} {l r d u : ℝ}
    (hlr : l < r) (hdu : d < u)
    (hL : IsRegularFiniteVerticalSpliceCut A B KL l)
    (hR : IsRegularFiniteVerticalSpliceCut A B KR r)
    (hD : IsRegularFiniteHorizontalSpliceCut A B KD d)
    (hU : IsRegularFiniteHorizontalSpliceCut A B KU u)
    (hWL : closedCutRectangle l r d u ∩ verticalLine l ⊆ KL)
    (hWR : closedCutRectangle l r d u ∩ verticalLine r ⊆ KR)
    (hWD : closedCutRectangle l r d u ∩ horizontalLine d ⊆ KD)
    (hWU : closedCutRectangle l r d u ∩ horizontalLine u ⊆ KU) :
    (spliceJunctionSet A B l r d u).Finite := by
  have hsubVertical (F K : Set PlanePoint) (x : ℝ)
      (hWK : closedCutRectangle l r d u ∩ verticalLine x ⊆ K)
      (hfinite : (frontier F ∩ K ∩ verticalLine x).Finite) :
      (frontier F ∩ closedCutRectangle l r d u ∩
        verticalLine x).Finite := by
    apply hfinite.subset
    rintro p ⟨⟨hpF, hpW⟩, hpLine⟩
    exact ⟨⟨hpF, hWK ⟨hpW, hpLine⟩⟩, hpLine⟩
  have hsubHorizontal (F K : Set PlanePoint) (y : ℝ)
      (hWK : closedCutRectangle l r d u ∩ horizontalLine y ⊆ K)
      (hfinite : (frontier F ∩ K ∩ horizontalLine y).Finite) :
      (frontier F ∩ closedCutRectangle l r d u ∩
        horizontalLine y).Finite := by
    apply hfinite.subset
    rintro p ⟨⟨hpF, hpW⟩, hpLine⟩
    exact ⟨⟨hpF, hWK ⟨hpW, hpLine⟩⟩, hpLine⟩
  exact finite_spliceJunctionSet hlr hdu
    (hsubVertical A KL l hWL hL.2.2.2.2.1)
    (hsubVertical A KR r hWR hR.2.2.2.2.1)
    (hsubHorizontal A KD d hWD hD.2.2.2.2.1)
    (hsubHorizontal A KU u hWU hU.2.2.2.2.1)
    (hsubVertical B KL l hWL hL.2.2.2.2.2)
    (hsubVertical B KR r hWR hR.2.2.2.2.2)
    (hsubHorizontal B KD d hWD hD.2.2.2.2.2)
    (hsubHorizontal B KU u hWU hU.2.2.2.2.2)

/-- Exact bridge from the four-collar output of
`exists_finiteCost_regularFinite_rawSplices` to finite junction geometry. -/
theorem finite_spliceJunctionSet_of_selected_regularFinite_closedCutRectangle
    {A B : Set PlanePoint}
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ l r d u : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : l ∈ Ioo a₀ a₁) (hr : r ∈ Ioo b₀ b₁)
    (hd : d ∈ Ioo c₀ c₁) (hu : u ∈ Ioo d₀ d₁)
    (hL : IsRegularFiniteVerticalSpliceCut A B
      (closedCutRectangle a₀ a₁ c₀ d₁) l)
    (hR : IsRegularFiniteVerticalSpliceCut A B
      (closedCutRectangle b₀ b₁ c₀ d₁) r)
    (hD : IsRegularFiniteHorizontalSpliceCut A B
      (closedCutRectangle a₀ b₁ c₀ c₁) d)
    (hU : IsRegularFiniteHorizontalSpliceCut A B
      (closedCutRectangle a₀ b₁ d₀ d₁) u) :
    (spliceJunctionSet A B l r d u).Finite := by
  apply finite_spliceJunctionSet_of_regularFiniteCuts
    (hl.2.trans (hab.trans hr.1)) (hd.2.trans (hcd.trans hu.1))
    hL hR hD hU
  · rintro p ⟨hpWindow, hpLine⟩
    rcases hpWindow with ⟨hpx, hpy⟩
    rcases hpx with ⟨hpxl, hpxr⟩
    rcases hpy with ⟨hpyd, hpyu⟩
    change p.1 = l at hpLine
    exact ⟨⟨by linarith [hl.1], by linarith [hl.2]⟩,
      ⟨by linarith [hd.1], by linarith [hu.2]⟩⟩
  · rintro p ⟨hpWindow, hpLine⟩
    rcases hpWindow with ⟨hpx, hpy⟩
    rcases hpx with ⟨hpxl, hpxr⟩
    rcases hpy with ⟨hpyd, hpyu⟩
    change p.1 = r at hpLine
    exact ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩,
      ⟨by linarith [hd.1], by linarith [hu.2]⟩⟩
  · rintro p ⟨hpWindow, hpLine⟩
    rcases hpWindow with ⟨hpx, hpy⟩
    rcases hpx with ⟨hpxl, hpxr⟩
    rcases hpy with ⟨hpyd, hpyu⟩
    change p.2 = d at hpLine
    exact ⟨⟨by linarith [hl.1], by linarith [hr.2]⟩,
      ⟨by linarith [hd.1], by linarith [hd.2]⟩⟩
  · rintro p ⟨hpWindow, hpLine⟩
    rcases hpWindow with ⟨hpx, hpy⟩
    rcases hpx with ⟨hpxl, hpxr⟩
    rcases hpy with ⟨hpyd, hpyu⟩
    change p.2 = u at hpLine
    exact ⟨⟨by linarith [hl.1], by linarith [hr.2]⟩,
      ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩

/-- The canonical open splice selected at one approximant index. -/
def selectedRawSplice
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ) (n : ℕ) :
    Set PlanePoint :=
  openSpliceIn (A n) (G n)
    (closedCutRectangle (l n) (r n) (d n) (u n))

/-- Every possible nonsmooth junction of a selected rectangular splice. -/
def selectedSpliceJunctions
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ) (n : ℕ) :
    Set PlanePoint :=
  spliceJunctionSet (A n) (G n) (l n) (r n) (d n) (u n)

/-- For an approximant-dependent selected splice, every exact junction avoids
any fixed core already contained in the rectangle interior. -/
theorem selectedSpliceJunctions_subset_compl_of_core
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ) (K : Set PlanePoint)
    (hlr : ∀ n, l n < r n) (hdu : ∀ n, d n < u n)
    (hK : ∀ n, K ⊆ interior
      (closedCutRectangle (l n) (r n) (d n) (u n))) :
    ∀ n, selectedSpliceJunctions A G l r d u n ⊆ Kᶜ := by
  intro n
  unfold selectedSpliceJunctions
  exact spliceJunctionSet_subset_compl_of_core (hlr n) (hdu n) (hK n)

/-- The exact regular-finite output of the raw-splice selector supplies
approximant-dependent finite junction families and quantitatively certified
candidate repair neighborhoods.  Their complete weighted raw frontier, planar
area, and spherical-boundary allowance vanish; the closed balls are pairwise
disjoint and remain in the certified open sets `Q n`.  No geometric repair
inside those neighborhoods is constructed here. -/
theorem exists_selected_regularFinite_rawSplice_repairScales
    (lam : ℝ) (hlam : 1 < lam)
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : ∀ n, l n ∈ Ioo a₀ a₁) (hr : ∀ n, r n ∈ Ioo b₀ b₁)
    (hd : ∀ n, d n ∈ Ioo c₀ c₁) (hu : ∀ n, u n ∈ Ioo d₀ d₁)
    (hL : ∀ n, IsRegularFiniteVerticalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ a₁ c₀ d₁) (l n))
    (hR : ∀ n, IsRegularFiniteVerticalSpliceCut (A n) (G n)
      (closedCutRectangle b₀ b₁ c₀ d₁) (r n))
    (hD : ∀ n, IsRegularFiniteHorizontalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ b₁ c₀ c₁) (d n))
    (hU : ∀ n, IsRegularFiniteHorizontalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ b₁ d₀ d₁) (u n))
    (hrawFinite : ∀ n,
      smoothCost lam (selectedRawSplice A G l r d u n) ≠ ⊤)
    (Q : ℕ → Set PlanePoint) (hQ : ∀ n, IsOpen (Q n))
    (hJQ : ∀ n, selectedSpliceJunctions A G l r d u n ⊆ Q n) :
    ∃ (J : ℕ → Finset PlanePoint) (k : ℕ → ℕ),
      (∀ n, (↑(J n) : Set PlanePoint) =
        selectedSpliceJunctions A G l r d u n) ∧
      (∀ n, n ≤ k n) ∧
      Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (frontier (selectedRawSplice A G l r d u n) ∩
            neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        volume (neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (junctionSpheres (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      (∀ n, neighborhood (J n) (junctionRadius (k n)) ⊆ Q n) ∧
      (∀ n, Set.Pairwise (↑(J n) : Set PlanePoint)
        (Function.onFun Disjoint fun p =>
          junctionBall p (junctionRadius (k n)))) ∧
      (∀ n,
        junctionSphereCostBudget lam (J n) (junctionRadius (k n)) ≤
          ENNReal.ofReal (junctionRadius n)) ∧
      ∀ n,
        weightedTraceCost lam
            (frontier (selectedRawSplice A G l r d u n) ∩
              neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) ∧
        volume (neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) := by
  classical
  have hfiniteJ : ∀ n,
      (selectedSpliceJunctions A G l r d u n).Finite := by
    intro n
    unfold selectedSpliceJunctions
    exact finite_spliceJunctionSet_of_selected_regularFinite_closedCutRectangle
      hab hcd (hl n) (hr n) (hd n) (hu n)
        (hL n) (hR n) (hD n) (hU n)
  let J : ℕ → Finset PlanePoint := fun n => (hfiniteJ n).toFinset
  have hJ : ∀ n, (↑(J n) : Set PlanePoint) =
      selectedSpliceJunctions A G l r d u n := by
    intro n
    exact (hfiniteJ n).coe_toFinset
  have htraceFinite : ∀ n,
      weightedTraceCost lam
        (frontier (selectedRawSplice A G l r d u n)) ≠ ⊤ := by
    intro n
    simpa only [smoothCost_eq_weightedTraceCost_frontier] using hrawFinite n
  have hJQ' : ∀ n, (↑(J n) : Set PlanePoint) ⊆ Q n := by
    intro n
    rw [hJ n]
    exact hJQ n
  obtain
      ⟨k, hk, hradius, htrace, harea, hsphere, hlocal, hdisjoint,
        hsphereBudget, hbudget⟩ :=
    exists_approximantDependent_neighborhoods_inside_with_sphericalBudget
      lam hlam (fun n => frontier (selectedRawSplice A G l r d u n))
      (fun _ => isClosed_frontier) htraceFinite J Q hQ hJQ'
  exact ⟨J, k, hJ, hk, hradius, htrace, harea, hsphere, hlocal,
    hdisjoint, hsphereBudget, hbudget⟩

/-- The regular-finite selector can choose all closed repair neighborhoods away
from any fixed closed payoff core strictly inside the common replacement core.
Center exclusion and neighborhood locality are derived internally. -/
theorem exists_selected_regularFinite_rawSplice_repairScales_avoiding_core
    (lam : ℝ) (hlam : 1 < lam)
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ : ℝ}
    (hab : a₁ < b₀) (hcd : c₁ < d₀)
    (hl : ∀ n, l n ∈ Ioo a₀ a₁) (hr : ∀ n, r n ∈ Ioo b₀ b₁)
    (hd : ∀ n, d n ∈ Ioo c₀ c₁) (hu : ∀ n, u n ∈ Ioo d₀ d₁)
    (hL : ∀ n, IsRegularFiniteVerticalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ a₁ c₀ d₁) (l n))
    (hR : ∀ n, IsRegularFiniteVerticalSpliceCut (A n) (G n)
      (closedCutRectangle b₀ b₁ c₀ d₁) (r n))
    (hD : ∀ n, IsRegularFiniteHorizontalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ b₁ c₀ c₁) (d n))
    (hU : ∀ n, IsRegularFiniteHorizontalSpliceCut (A n) (G n)
      (closedCutRectangle a₀ b₁ d₀ d₁) (u n))
    (hrawFinite : ∀ n,
      smoothCost lam (selectedRawSplice A G l r d u n) ≠ ⊤)
    (K : Set PlanePoint) (hKclosed : IsClosed K)
    (hKcore : K ⊆ Ioo a₁ b₀ ×ˢ Ioo c₁ d₀) :
    ∃ (J : ℕ → Finset PlanePoint) (k : ℕ → ℕ),
      (∀ n, (↑(J n) : Set PlanePoint) =
        selectedSpliceJunctions A G l r d u n) ∧
      (∀ n, n ≤ k n) ∧
      Tendsto (fun n => junctionRadius (k n)) atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (frontier (selectedRawSplice A G l r d u n) ∩
            neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        volume (neighborhood (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (junctionSpheres (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      (∀ n, neighborhood (J n) (junctionRadius (k n)) ⊆ Kᶜ) ∧
      (∀ n, Set.Pairwise (↑(J n) : Set PlanePoint)
        (Function.onFun Disjoint fun p =>
          junctionBall p (junctionRadius (k n)))) ∧
      (∀ n,
        junctionSphereCostBudget lam (J n) (junctionRadius (k n)) ≤
          ENNReal.ofReal (junctionRadius n)) ∧
      ∀ n,
        weightedTraceCost lam
            (frontier (selectedRawSplice A G l r d u n) ∩
              neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) ∧
        volume (neighborhood (J n) (junctionRadius (k n))) ≤
          ENNReal.ofReal (junctionRadius n) := by
  have hlr : ∀ n, l n < r n := fun n =>
    (hl n).2.trans (hab.trans (hr n).1)
  have hdu : ∀ n, d n < u n := fun n =>
    (hd n).2.trans (hcd.trans (hu n).1)
  have hKinside : ∀ n, K ⊆ interior
      (closedCutRectangle (l n) (r n) (d n) (u n)) := by
    intro n p hpK
    have hpC := hKcore hpK
    rw [closedCutRectangle, interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨(hl n).2.trans hpC.1.1, hpC.1.2.trans (hr n).1⟩,
      ⟨(hd n).2.trans hpC.2.1, hpC.2.2.trans (hu n).1⟩⟩
  have hJQ : ∀ n, selectedSpliceJunctions A G l r d u n ⊆ Kᶜ :=
    selectedSpliceJunctions_subset_compl_of_core
      A G l r d u K hlr hdu hKinside
  simpa only using
    (exists_selected_regularFinite_rawSplice_repairScales
      lam hlam A G l r d u hab hcd hl hr hd hu hL hR hD hU hrawFinite
      (fun _ => Kᶜ) (fun _ => hKclosed.isOpen_compl) hJQ)

/-- Once a termwise quantitative finite-junction repair is available, package
the repaired sets as a smooth sequence and discharge every global convergence,
complete weighted-cost, and additive finite-patch bookkeeping obligation.  The
local premise records the remaining geometric construction exactly: all
changes occur in the selected neighborhood, the complete repaired frontier is
covered by unchanged raw trace plus globally charged auxiliary trace, and that
trace costs at most the removed raw trace plus a vanishing rounding error.
This conditional theorem neither constructs the repairs nor derives the
caller-supplied `roundError` from the preceding spherical allowance. -/
theorem exists_repairedSequence_cost_add_finset_payoff_le
    {lam : ℝ} {E F : Set PlanePoint} (A : SmoothSequence)
    (hAconv : A.ConvergesTo E)
    {ι : Type*} (s : Finset ι)
    (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    {W : Set PlanePoint} (hW : MeasurableSet W)
    (hsub : ∀ i ∈ s, (P i).window ⊆ W)
    (hE : MeasurableSet E) (newCost : ENNReal)
    (raw : ℕ → Set PlanePoint) (J : ℕ → Finset PlanePoint)
    (k : ℕ → ℕ)
    (hrawConv : Tendsto (fun n => characteristicDistance (raw n) F)
      atTop (𝓝 0))
    (harea : Tendsto (fun n =>
      volume (neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0))
    (rawSeam roundError : ℕ → ENNReal)
    (hrawSeam : Tendsto rawSeam atTop (𝓝 0))
    (htrace : Tendsto (fun n =>
      weightedTraceCost lam
        (frontier (raw n) ∩ neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0))
    (hroundError : Tendsto roundError atTop (𝓝 0))
    (hrawOutside : ∀ n,
      smoothCostOn lam (raw n)
          (neighborhood (J n) (junctionRadius (k n)))ᶜ ≤
        smoothCostOn lam (A.carrier n) Wᶜ + newCost + rawSeam n)
    (hlocalRepair : ∀ n, ∃ (U R : Set PlanePoint),
      IsSmoothDomain U ∧
      U ∆ raw n ⊆ neighborhood (J n) (junctionRadius (k n)) ∧
      frontier U ⊆
        (frontier (raw n) ∩
          (neighborhood (J n) (junctionRadius (k n)))ᶜ) ∪ R ∧
      weightedTraceCost lam R ≤
        weightedTraceCost lam
          (frontier (raw n) ∩
            neighborhood (J n) (junctionRadius (k n))) + roundError n) :
    ∃ B : SmoothSequence,
      B.ConvergesTo F ∧
      Tendsto (fun n =>
        (rawSeam n + weightedTraceCost lam
          (frontier (raw n) ∩
            neighborhood (J n) (junctionRadius (k n)))) + roundError n)
        atTop (𝓝 0) ∧
      (∀ n, smoothCost lam (B.carrier n) ≤
        smoothCostOn lam (A.carrier n) Wᶜ + newCost +
          ((rawSeam n + weightedTraceCost lam
            (frontier (raw n) ∩
              neighborhood (J n) (junctionRadius (k n)))) + roundError n)) ∧
      B.cost lam + ∑ i ∈ s, (P i).payoff ≤ A.cost lam + newCost := by
  classical
  choose U R hUsmooth hmodify hfrontier hRcost using hlocalRepair
  let B : SmoothSequence :=
    { carrier := U
      smooth := hUsmooth }
  have hBconv : B.ConvergesTo F := by
    unfold SmoothSequence.ConvergesTo
    have hupper : Tendsto (fun n =>
        volume (neighborhood (J n) (junctionRadius (k n))) +
          characteristicDistance (raw n) F) atTop (𝓝 0) := by
      simpa using harea.add hrawConv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper
    · exact fun _ => bot_le
    · intro n
      calc
        characteristicDistance (B.carrier n) F ≤
            characteristicDistance (B.carrier n) (raw n) +
              characteristicDistance (raw n) F :=
          measure_symmDiff_le _ _ _
        _ ≤ volume (neighborhood (J n) (junctionRadius (k n))) +
              characteristicDistance (raw n) F :=
          add_le_add (measure_mono (hmodify n)) le_rfl
  let seam : ℕ → ENNReal := fun n =>
    (rawSeam n + weightedTraceCost lam
      (frontier (raw n) ∩ neighborhood (J n) (junctionRadius (k n)))) +
      roundError n
  have hseam : Tendsto seam atTop (𝓝 0) := by
    simpa only [seam, add_zero] using (hrawSeam.add htrace).add hroundError
  have hpoint : ∀ n, smoothCost lam (B.carrier n) ≤
      smoothCostOn lam (A.carrier n) Wᶜ + newCost + seam n := by
    intro n
    calc
      smoothCost lam (B.carrier n) ≤
          smoothCostOn lam (raw n)
              (neighborhood (J n) (junctionRadius (k n)))ᶜ +
            weightedTraceCost lam (R n) := by
        exact smoothCost_le_outside_add_auxiliary_of_frontier_subset
          lam (isClosed_neighborhood _ _) (hfrontier n)
      _ ≤ (smoothCostOn lam (A.carrier n) Wᶜ + newCost + rawSeam n) +
            (weightedTraceCost lam
              (frontier (raw n) ∩
                neighborhood (J n) (junctionRadius (k n))) + roundError n) :=
        add_le_add (hrawOutside n) (hRcost n)
      _ = smoothCostOn lam (A.carrier n) Wᶜ + newCost + seam n := by
        simp only [seam]
        ac_rfl
  refine ⟨B, hBconv, hseam, hpoint, ?_⟩
  exact SmoothSequence.cost_add_finset_payoff_le_of_outside_repair
    A B hAconv s P hpair hW hsub hE newCost hseam hpoint

/-- If the remaining local construction gives a smooth repair whose new
frontier consists only of removed raw trace and the selected candidate spheres,
the global density-aware spherical estimate supplies the vanishing rounding
error automatically.  This remains conditional on constructing that structural
repair; unlike `exists_repairedSequence_cost_add_finset_payoff_le`, it assumes
no separate weighted auxiliary-cost inequality. -/
theorem exists_repairedSequence_cost_add_finset_payoff_le_of_spherical_frontier
    {lam : ℝ} {E F : Set PlanePoint} (A : SmoothSequence)
    (hAconv : A.ConvergesTo E)
    {ι : Type*} (s : Finset ι)
    (P : ι → RigidProjectionPatch lam E)
    (hpair : Set.Pairwise (↑s)
      (Function.onFun Disjoint fun i => (P i).window))
    {W : Set PlanePoint} (hW : MeasurableSet W)
    (hsub : ∀ i ∈ s, (P i).window ⊆ W)
    (hE : MeasurableSet E) (newCost : ENNReal)
    (raw : ℕ → Set PlanePoint) (J : ℕ → Finset PlanePoint)
    (k : ℕ → ℕ)
    (hrawConv : Tendsto (fun n => characteristicDistance (raw n) F)
      atTop (𝓝 0))
    (harea : Tendsto (fun n =>
      volume (neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0))
    (rawSeam : ℕ → ENNReal)
    (hrawSeam : Tendsto rawSeam atTop (𝓝 0))
    (htrace : Tendsto (fun n =>
      weightedTraceCost lam
        (frontier (raw n) ∩ neighborhood (J n) (junctionRadius (k n))))
      atTop (𝓝 0))
    (hsphere : Tendsto (fun n =>
      weightedTraceCost lam
        (junctionSpheres (J n) (junctionRadius (k n))))
      atTop (𝓝 0))
    (hrawOutside : ∀ n,
      smoothCostOn lam (raw n)
          (neighborhood (J n) (junctionRadius (k n)))ᶜ ≤
        smoothCostOn lam (A.carrier n) Wᶜ + newCost + rawSeam n)
    (hlocalRepair : ∀ n, ∃ U : Set PlanePoint,
      IsSmoothDomain U ∧
      U ∆ raw n ⊆ neighborhood (J n) (junctionRadius (k n)) ∧
      frontier U ⊆
        (frontier (raw n) ∩
          (neighborhood (J n) (junctionRadius (k n)))ᶜ) ∪
        ((frontier (raw n) ∩
          neighborhood (J n) (junctionRadius (k n))) ∪
          junctionSpheres (J n) (junctionRadius (k n)))) :
    ∃ B : SmoothSequence,
      B.ConvergesTo F ∧
      Tendsto (fun n =>
        (rawSeam n + weightedTraceCost lam
          (frontier (raw n) ∩
            neighborhood (J n) (junctionRadius (k n)))) +
          weightedTraceCost lam
            (junctionSpheres (J n) (junctionRadius (k n))))
        atTop (𝓝 0) ∧
      (∀ n, smoothCost lam (B.carrier n) ≤
        smoothCostOn lam (A.carrier n) Wᶜ + newCost +
          ((rawSeam n + weightedTraceCost lam
            (frontier (raw n) ∩
              neighborhood (J n) (junctionRadius (k n)))) +
            weightedTraceCost lam
              (junctionSpheres (J n) (junctionRadius (k n))))) ∧
      B.cost lam + ∑ i ∈ s, (P i).payoff ≤ A.cost lam + newCost := by
  apply exists_repairedSequence_cost_add_finset_payoff_le
    A hAconv s P hpair hW hsub hE newCost raw J k hrawConv harea
    rawSeam (fun n => weightedTraceCost lam
      (junctionSpheres (J n) (junctionRadius (k n))))
    hrawSeam htrace hsphere hrawOutside
  intro n
  obtain ⟨U, hUsmooth, hmodify, hfrontier⟩ := hlocalRepair n
  exact ⟨U,
    (frontier (raw n) ∩ neighborhood (J n) (junctionRadius (k n))) ∪
      junctionSpheres (J n) (junctionRadius (k n)),
    hUsmooth, hmodify, hfrontier,
    weightedTraceCost_union_le lam _ _⟩

open CMVTwoPatchGraphVariation

/-- A flat one-sided cutoff for a graph connector. -/
def graphConnectorCutoff (a b x : ℝ) : ℝ :=
  Real.smoothTransition ((x - a) / (b - a))

/-- Join `f` on the left to `g` on the right. -/
def connectGraphs (a b : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x + graphConnectorCutoff a b x * (g x - f x)

theorem contDiff_graphConnectorCutoff (a b : ℝ) :
    ContDiff ℝ ∞ (graphConnectorCutoff a b) := by
  unfold graphConnectorCutoff
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const _)

theorem graphConnectorCutoff_nonneg (a b x : ℝ) :
    0 ≤ graphConnectorCutoff a b x :=
  Real.smoothTransition.nonneg _

theorem graphConnectorCutoff_le_one (a b x : ℝ) :
    graphConnectorCutoff a b x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem graphConnectorCutoff_eq_zero_of_le
    {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    graphConnectorCutoff a b x = 0 := by
  unfold graphConnectorCutoff
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
    (sub_nonneg.mpr hab.le)

theorem graphConnectorCutoff_eq_one_of_le
    {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    graphConnectorCutoff a b x = 1 := by
  unfold graphConnectorCutoff
  apply Real.smoothTransition.one_of_one_le
  exact (one_le_div₀ (sub_pos.mpr hab)).2 (by linarith)

theorem contDiff_connectGraphs
    {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (connectGraphs a b f g) := by
  unfold connectGraphs
  exact hf.add ((contDiff_graphConnectorCutoff a b).mul (hg.sub hf))

theorem connectGraphs_eq_left
    {a b x : ℝ} {f g : ℝ → ℝ} (hab : a < b) (hx : x ≤ a) :
    connectGraphs a b f g x = f x := by
  rw [connectGraphs, graphConnectorCutoff_eq_zero_of_le hab hx]
  ring

theorem connectGraphs_eq_right
    {a b x : ℝ} {f g : ℝ → ℝ} (hab : a < b) (hx : b ≤ x) :
    connectGraphs a b f g x = g x := by
  rw [connectGraphs, graphConnectorCutoff_eq_one_of_le hab hx]
  ring

theorem deriv_graphConnectorCutoff
    {a b x : ℝ} :
    deriv (graphConnectorCutoff a b) x =
      deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a) := by
  have hinner : HasDerivAt (fun y : ℝ => (y - a) / (b - a))
      (1 / (b - a)) x := by
    simpa only [id_eq, one_div, one_mul] using
      ((hasDerivAt_id x).sub_const a).div_const (b - a)
  have hsmoothCD : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hsmooth : DifferentiableAt ℝ Real.smoothTransition
      ((x - a) / (b - a)) :=
    hsmoothCD.differentiable (by simp) _
  have hcomp := hsmooth.hasDerivAt.comp x hinner
  change deriv (Real.smoothTransition ∘ fun y => (y - a) / (b - a)) x = _
  rw [hcomp.deriv]
  ring

theorem deriv_connectGraphs
    {a b x : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    deriv (connectGraphs a b f g) x =
      deriv f x +
        (deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) *
          (g x - f x) +
        graphConnectorCutoff a b x * (deriv g x - deriv f x) := by
  have hcut : DifferentiableAt ℝ (graphConnectorCutoff a b) x :=
    (contDiff_graphConnectorCutoff a b).differentiable (by simp) x
  have hfd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have hgd : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
  unfold connectGraphs
  change deriv (f + graphConnectorCutoff a b * (g - f)) x = _
  rw [deriv_add hfd (hcut.mul (hgd.sub hfd)),
    deriv_mul hcut (hgd.sub hfd), deriv_sub hgd hfd,
    deriv_graphConnectorCutoff]
  simp only [Pi.sub_apply]
  ring

/-- The flat transition has one global derivative bound, including its
constant exterior pieces. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ D := by
  have hsmoothCD : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hcontinuous : Continuous
      (fun x : ℝ => |deriv Real.smoothTransition x|) :=
    (hsmoothCD.continuous_deriv (by simp)).abs
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcontinuous.continuousOn)
  refine ⟨max 0 M, le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hM _ (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  · rw [mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [Iio_mem_nhds (lt_of_not_ge hx)] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [heq.deriv_eq, deriv_const, abs_zero]
      exact le_max_left _ _
    · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ : ℝ => 1 := by
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge hx)] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [heq.deriv_eq, deriv_const, abs_zero]
      exact le_max_left _ _

/-- A common value at the cut converts local derivative bounds into the
scale-cancelling value bound needed by a shrinking connector. -/
theorem abs_connecting_graphs_sub_le
    {a b c x M : ℝ} {f g : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hM : 0 ≤ M)
    (hfM : ∀ y ∈ Icc a b, |deriv f y| ≤ M)
    (hgM : ∀ y ∈ Icc a b, |deriv g y| ≤ M)
    (hfg : f c = g c) :
    |g x - f x| ≤ 2 * M * (b - a) := by
  have hfb :
      |f x - f c| ≤ M * |x - c| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy => (hf y).hasDerivAt.hasDerivWithinAt)
        (fun y hy => by simpa only [Real.norm_eq_abs] using hfM y hy)
        hc hx
  have hgb :
      |g x - g c| ≤ M * |x - c| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun y hy => (hg y).hasDerivAt.hasDerivWithinAt)
        (fun y hy => by simpa only [Real.norm_eq_abs] using hgM y hy)
        hc hx
  have hxc : |x - c| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hc.1, hc.2]
  calc
    |g x - f x| =
        |(g x - g c) - (f x - f c)| := by rw [hfg]; ring
    _ ≤ |g x - g c| + |f x - f c| := abs_sub _ _
    _ ≤ M * |x - c| + M * |x - c| := add_le_add hgb hfb
    _ ≤ M * (b - a) + M * (b - a) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxc hM)
        (mul_le_mul_of_nonneg_left hxc hM)
    _ = 2 * M * (b - a) := by ring

/-- The scaled cutoff does not create a slope blow-up when its two incident
graphs have the same cut value. -/
theorem abs_deriv_connectGraphs_le
    {a b c x M D : ℝ} {f g : ℝ → ℝ}
    (hab : a < b) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hfM : ∀ y ∈ Icc a b, |deriv f y| ≤ M)
    (hgM : ∀ y ∈ Icc a b, |deriv g y| ≤ M)
    (htransition : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ D)
    (hfg : f c = g c) :
    |deriv (connectGraphs a b f g) x| ≤ 3 * M + 2 * D * M := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hsep : |g x - f x| ≤ 2 * M * (b - a) :=
    abs_connecting_graphs_sub_le
      (hf.differentiable (by simp)) (hg.differentiable (by simp))
      hc hx hM hfM hgM hfg
  have hcut :
      |deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)| ≤
        D / (b - a) := by
    rw [abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right
      (htransition ((x - a) / (b - a))) hden.le
  have hcutTerm :
      |(deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) *
          (g x - f x)| ≤ 2 * D * M := by
    rw [abs_mul]
    calc
      |deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)| *
          |g x - f x| ≤
          (D / (b - a)) * (2 * M * (b - a)) :=
        mul_le_mul hcut hsep (abs_nonneg _) (by positivity)
      _ = 2 * D * M := by field_simp [hden.ne']
  have hdiff : |deriv g x - deriv f x| ≤ 2 * M := by
    calc
      |deriv g x - deriv f x| ≤ |deriv g x| + |deriv f x| :=
        abs_sub _ _
      _ ≤ M + M := add_le_add (hgM x hx) (hfM x hx)
      _ = 2 * M := by ring
  have hconvex :
      |graphConnectorCutoff a b x * (deriv g x - deriv f x)| ≤
        2 * M := by
    rw [abs_mul, abs_of_nonneg (graphConnectorCutoff_nonneg _ _ _)]
    calc
      graphConnectorCutoff a b x * |deriv g x - deriv f x| ≤
          graphConnectorCutoff a b x * (2 * M) :=
        mul_le_mul_of_nonneg_left hdiff
          (graphConnectorCutoff_nonneg _ _ _)
      _ ≤ 1 * (2 * M) :=
        mul_le_mul_of_nonneg_right
          (graphConnectorCutoff_le_one _ _ _) (mul_nonneg (by norm_num) hM)
      _ = 2 * M := one_mul _
  rw [deriv_connectGraphs hf hg]
  have htri :
      |deriv f x +
          (deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) *
            (g x - f x) +
          graphConnectorCutoff a b x * (deriv g x - deriv f x)| ≤
        |deriv f x| +
          |(deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) *
            (g x - f x)| +
          |graphConnectorCutoff a b x * (deriv g x - deriv f x)| := by
    exact (abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  calc
    |deriv f x +
        (deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) *
          (g x - f x) +
        graphConnectorCutoff a b x * (deriv g x - deriv f x)| ≤
        |deriv f x| +
          |(deriv Real.smoothTransition ((x - a) / (b - a)) / (b - a)) *
            (g x - f x)| +
          |graphConnectorCutoff a b x * (deriv g x - deriv f x)| := htri
    _ ≤ M + 2 * D * M + 2 * M :=
      add_le_add (add_le_add (hfM x hx) hcutTerm) hconvex
    _ = 3 * M + 2 * D * M := by ring
/-- Every smooth graph has a finite Euclidean speed bound on one compact
connector interval. -/
theorem exists_graphSpeed_bound_Icc
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (a b : ℝ) :
    ∃ K : NNReal, ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ) := by
  have hcontinuous : Continuous
      (fun x : ℝ => Real.sqrt (1 + (deriv g x) ^ 2)) :=
    (continuous_const.add ((hg.continuous_deriv (by simp)).pow 2)).sqrt
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcontinuous.continuousOn)
  let K : NNReal := ⟨max 0 M, le_max_left _ _⟩
  refine ⟨K, fun x hx => ?_⟩
  exact (hM _ (mem_image_of_mem _ hx)).trans (le_max_right _ _)

/-- Two fixed smooth incident graphs have one common derivative bound on a
compact chart. -/
theorem exists_common_deriv_bound_Icc
    {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (a b : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x ∈ Icc a b, |deriv f x| ≤ M) ∧
      ∀ x ∈ Icc a b, |deriv g x| ≤ M := by
  obtain ⟨Kf, hKf⟩ := exists_graphSpeed_bound_Icc hf a b
  obtain ⟨Kg, hKg⟩ := exists_graphSpeed_bound_Icc hg a b
  let M : ℝ := max (Kf : ℝ) (Kg : ℝ)
  have hderiv_le_speed (q : ℝ) :
      |q| ≤ Real.sqrt (1 + q ^ 2) := by
    have hsqrt := Real.sqrt_nonneg (1 + q ^ 2)
    have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + q ^ 2)
    nlinarith [sq_abs q]
  refine ⟨M, le_trans Kf.coe_nonneg (le_max_left _ _), ?_, ?_⟩
  · intro x hx
    exact (hderiv_le_speed (deriv f x)).trans
      ((hKf x hx).trans (le_max_left _ _))
  · intro x hx
    exact (hderiv_le_speed (deriv g x)).trans
      ((hKg x hx).trans (le_max_right _ _))

/-- Radius used by the symmetric connector family. -/
def symmetricConnectorRadius (R : ℝ) (n : ℕ) : ℝ :=
  R * junctionRadius n

lemma symmetricConnectorRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < symmetricConnectorRadius R n :=
  mul_pos hR (junctionRadius_pos n)

lemma symmetricConnectorRadius_le {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    symmetricConnectorRadius R n ≤ R := by
  unfold symmetricConnectorRadius junctionRadius
  have hn : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hfrac : 1 / (n + 1 : ℝ) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hn
  nlinarith

lemma tendsto_symmetricConnectorRadius_zero (R : ℝ) :
    Tendsto (symmetricConnectorRadius R) atTop (𝓝 0) := by
  change Tendsto (fun n => R * junctionRadius n) atTop (𝓝 0)
  simpa only [mul_zero] using
    tendsto_const_nhds.mul tendsto_junctionRadius_zero

/-- Global-density weighted bound for a graph segment. -/
theorem weightedTraceCost_graph_Icc_le_global
    {lam : ℝ} (hlam : 1 < lam) {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ x ∈ Icc a b,
      Real.sqrt (1 + (deriv g x) ^ 2) ≤ (K : ℝ)) :
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc a b) ≤
      ENNReal.ofReal lam * (K : ENNReal) * ENNReal.ofReal (b - a) := by
  calc
    weightedTraceCost lam
        ((fun x : ℝ => (x, g x)) '' Icc a b) ≤
        ENNReal.ofReal lam *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              ((fun x : ℝ => (x, g x)) '' Icc a b)) :=
      weightedTraceCost_le_density_mul_hausdorff hlam _
    _ ≤ ENNReal.ofReal lam *
          ((K : ENNReal) * ENNReal.ofReal (b - a)) := by
      gcongr
      exact hausdorffMeasure_euclideanGraph_Icc_le hg hK
    _ = _ := by rw [mul_assoc]
/-- Shrinking a connector around a common incident point makes its complete
density-weighted graph trace vanish. The slope bound is derived after the two
actual incident graphs are known; no uniform chart constant is assumed. -/
theorem tendsto_weightedTraceCost_symmetricGraphConnectors_zero
    {lam : ℝ} (hlam : 1 < lam)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    Tendsto (fun n =>
      let r := symmetricConnectorRadius R n
      weightedTraceCost lam
        ((fun x : ℝ =>
          (x, connectGraphs (c - r) (c + r) f g x)) ''
            Icc (c - r) (c + r))) atTop (𝓝 0) := by
  obtain ⟨D, hD, hDbound⟩ := exists_smoothTransition_deriv_bound
  obtain ⟨M, hM, hfM, hgM⟩ :=
    exists_common_deriv_bound_Icc
      (hf.of_le (by simp)) (hg.of_le (by simp)) (c - R) (c + R)
  have hKnonneg : 0 ≤ 1 + (3 * M + 2 * D * M) := by positivity
  let K : NNReal := ⟨1 + (3 * M + 2 * D * M), hKnonneg⟩
  let width : ℕ → ℝ := fun n => 2 * symmetricConnectorRadius R n
  have hwidthReal : Tendsto width atTop (𝓝 0) := by
    simpa only [width, mul_zero] using
      tendsto_const_nhds.mul (tendsto_symmetricConnectorRadius_zero R)
  have hwidth : Tendsto (fun n => ENNReal.ofReal (width n))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hwidthReal
  have hupper : Tendsto
      (fun n => (ENNReal.ofReal lam * (K : ENNReal)) *
        ENNReal.ofReal (width n)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hwidth
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
  · intro n
    exact bot_le
  · intro n
    let r := symmetricConnectorRadius R n
    have hr : 0 < r := symmetricConnectorRadius_pos hR n
    have hrle : r ≤ R := symmetricConnectorRadius_le hR.le n
    have hsub : Icc (c - r) (c + r) ⊆ Icc (c - R) (c + R) := by
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hc : c ∈ Icc (c - r) (c + r) := by
      constructor <;> linarith
    have hspeed : ∀ x ∈ Icc (c - r) (c + r),
        Real.sqrt
          (1 + (deriv (connectGraphs (c - r) (c + r) f g) x) ^ 2) ≤
          (K : ℝ) := by
      intro x hx
      have hslope :
          |deriv (connectGraphs (c - r) (c + r) f g) x| ≤
            3 * M + 2 * D * M :=
        abs_deriv_connectGraphs_le (by linarith) hc hx hf hg hM hD
          (fun y hy => hfM y (hsub hy))
          (fun y hy => hgM y (hsub hy)) hDbound hfg
      calc
        Real.sqrt
            (1 + (deriv (connectGraphs (c - r) (c + r) f g) x) ^ 2) ≤
            1 + |deriv (connectGraphs (c - r) (c + r) f g) x| := by
          let q := deriv (connectGraphs (c - r) (c + r) f g) x
          have hsqrt := Real.sqrt_nonneg (1 + q ^ 2)
          have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + q ^ 2)
          have habs := abs_nonneg q
          change Real.sqrt (1 + q ^ 2) ≤ 1 + |q|
          nlinarith [sq_abs q]
        _ ≤ 1 + (3 * M + 2 * D * M) := add_le_add le_rfl hslope
        _ = (K : ℝ) := rfl
    have hcost := weightedTraceCost_graph_Icc_le_global hlam
      ((contDiff_connectGraphs hf hg).differentiable (by simp)) hspeed
    simpa only [width, r, add_sub_sub_cancel, add_sub_cancel_left,
      show c + r - (c - r) = 2 * r by ring] using hcost

/-- Face-labelled old/new graph switch.  Unlike two strict half-slab pieces,
this occupied-domain representation retains the cutting line and therefore
does not create an unbounded artificial crack. -/
def filledVerticalGraphSwitch
    (P : GraphPatch) (f g : ℝ → ℝ) (c : ℝ) : Set PlanePoint :=
  P.occupiedGraphDomain (fun x => if x ≤ c then f x else g x)

/-- The filled switch is exactly the canonical open raw splice across a closed
right halfspace when the two same-side incident graphs meet on the cut. -/
theorem openSpliceIn_occupiedGraphDomains_rightHalfspace_eq_filledVerticalGraphSwitch
    (P : GraphPatch) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c : ℝ} (hfg : f c = g c) :
    openSpliceIn (P.occupiedGraphDomain f) (P.occupiedGraphDomain g)
        {p : PlanePoint | c ≤ p.1} =
      filledVerticalGraphSwitch P f g c := by
  have hsplice :
      spliceIn (P.occupiedGraphDomain f) (P.occupiedGraphDomain g)
          {p : PlanePoint | c ≤ p.1} =
        filledVerticalGraphSwitch P f g c := by
    ext p
    rcases p with ⟨x, y⟩
    cases hside : P.side
    · by_cases hxc : x < c
      · have hnotcx : ¬c ≤ x := not_le_of_gt hxc
        simp only [spliceIn, filledVerticalGraphSwitch,
          GraphPatch.occupiedGraphDomain, hside, mem_union, Set.mem_sdiff,
          Set.mem_ofPred_eq, hnotcx, not_false_eq_true, and_true,
          mem_inter_iff, and_false, or_false, if_pos hxc.le]
      · have hcx : c ≤ x := le_of_not_gt hxc
        by_cases heq : x = c
        · subst x
          simp only [spliceIn, filledVerticalGraphSwitch,
            GraphPatch.occupiedGraphDomain, hside, mem_union, Set.mem_sdiff,
            Set.mem_ofPred_eq, le_rfl, not_true_eq_false, and_false,
            mem_inter_iff, and_true, false_or, if_pos, hfg]
        · have hnotxc : ¬x ≤ c :=
            not_le_of_gt (lt_of_le_of_ne hcx (Ne.symm heq))
          simp only [spliceIn, filledVerticalGraphSwitch,
            GraphPatch.occupiedGraphDomain, hside, mem_union, Set.mem_sdiff,
            Set.mem_ofPred_eq, hcx, not_true_eq_false, and_false,
            mem_inter_iff, and_true, false_or, if_neg hnotxc]
    · by_cases hxc : x < c
      · have hnotcx : ¬c ≤ x := not_le_of_gt hxc
        simp only [spliceIn, filledVerticalGraphSwitch,
          GraphPatch.occupiedGraphDomain, hside, mem_union, Set.mem_sdiff,
          Set.mem_ofPred_eq, hnotcx, not_false_eq_true, and_true,
          mem_inter_iff, and_false, or_false, if_pos hxc.le]
      · have hcx : c ≤ x := le_of_not_gt hxc
        by_cases heq : x = c
        · subst x
          simp only [spliceIn, filledVerticalGraphSwitch,
            GraphPatch.occupiedGraphDomain, hside, mem_union, Set.mem_sdiff,
            Set.mem_ofPred_eq, le_rfl, not_true_eq_false, and_false,
            mem_inter_iff, and_true, false_or, if_pos, hfg]
        · have hnotxc : ¬x ≤ c :=
            not_le_of_gt (lt_of_le_of_ne hcx (Ne.symm heq))
          simp only [spliceIn, filledVerticalGraphSwitch,
            GraphPatch.occupiedGraphDomain, hside, mem_union, Set.mem_sdiff,
            Set.mem_ofPred_eq, hcx, not_true_eq_false, and_false,
            mem_inter_iff, and_true, false_or, if_neg hnotxc]
  have hcontinuous :
      Continuous (fun x => if x ≤ c then f x else g x) := by
    apply continuous_if_le continuous_id continuous_const
      hf.continuousOn hg.continuousOn
    intro x hx
    change x = c at hx
    subst x
    exact hfg
  rw [openSpliceIn, hsplice]
  exact (P.isOpen_occupiedGraphDomain hcontinuous).interior_eq

theorem mem_occupiedGraphDomain_connectGraphs_iff_left
    (P : GraphPatch) {a b : ℝ} {f g : ℝ → ℝ} {p : PlanePoint}
    (hab : a < b) (hp : p.1 ≤ a) :
    p ∈ P.occupiedGraphDomain (connectGraphs a b f g) ↔
      p ∈ P.occupiedGraphDomain f := by
  have heq := connectGraphs_eq_left (f := f) (g := g) hab hp
  cases hside : P.side <;>
    simp only [GraphPatch.occupiedGraphDomain, hside, Set.mem_ofPred_eq, heq]

theorem mem_occupiedGraphDomain_connectGraphs_iff_right
    (P : GraphPatch) {a b : ℝ} {f g : ℝ → ℝ} {p : PlanePoint}
    (hab : a < b) (hp : b ≤ p.1) :
    p ∈ P.occupiedGraphDomain (connectGraphs a b f g) ↔
      p ∈ P.occupiedGraphDomain g := by
  have heq := connectGraphs_eq_right (f := f) (g := g) hab hp
  cases hside : P.side <;>
    simp only [GraphPatch.occupiedGraphDomain, hside, Set.mem_ofPred_eq, heq]

/-- Every changed point lies in the bounded vertical band between the smooth
connector and the face-labelled raw graph. -/
theorem occupiedGraphDomain_connectGraphs_symmDiff_filledSwitch_subset_closedGraphBand
    (P : GraphPatch) {a b c : ℝ} {f g : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) :
    P.occupiedGraphDomain (connectGraphs a b f g) ∆
        filledVerticalGraphSwitch P f g c ⊆
      closedGraphBand
        (connectGraphs a b f g)
        (fun x => if x ≤ c then f x else g x)
        (Icc a b) := by
  let s : ℝ → ℝ := fun x => if x ≤ c then f x else g x
  have hbase :
      P.occupiedGraphDomain (connectGraphs a b f g) ∆
          P.occupiedGraphDomain s ⊆
        Icc a b ×ˢ (univ : Set ℝ) := by
    intro p hp
    have hxp : p.1 ∈ Icc a b := by
      by_contra hx
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hxa | hxb
      · have hxc : p.1 ≤ c := (hxa.le.trans hac.le)
        have hconn :=
          mem_occupiedGraphDomain_connectGraphs_iff_left P hxa.le
            (hab := hac.trans hcb) (f := f) (g := g)
        have hswitch :
            p ∈ P.occupiedGraphDomain s ↔
              p ∈ P.occupiedGraphDomain f := by
          cases hside : P.side <;>
            simp only [GraphPatch.occupiedGraphDomain, hside,
              Set.mem_ofPred_eq, s, if_pos hxc]
        simp only [Set.mem_symmDiff] at hp
        rcases hp with ⟨hpConn, hpNotSwitch⟩ | ⟨hpSwitch, hpNotConn⟩
        · exact hpNotSwitch (hswitch.mpr (hconn.mp hpConn))
        · exact hpNotConn (hconn.mpr (hswitch.mp hpSwitch))
      · have hxc : ¬p.1 ≤ c := not_le_of_gt (hcb.trans hxb)
        have hconn :=
          mem_occupiedGraphDomain_connectGraphs_iff_right P hxb.le
            (hab := hac.trans hcb) (f := f) (g := g)
        have hswitch :
            p ∈ P.occupiedGraphDomain s ↔
              p ∈ P.occupiedGraphDomain g := by
          cases hside : P.side <;>
            simp only [GraphPatch.occupiedGraphDomain, hside,
              Set.mem_ofPred_eq, s, if_neg hxc]
        simp only [Set.mem_symmDiff] at hp
        rcases hp with ⟨hpConn, hpNotSwitch⟩ | ⟨hpSwitch, hpNotConn⟩
        · exact hpNotSwitch (hswitch.mpr (hconn.mp hpConn))
        · exact hpNotConn (hconn.mpr (hswitch.mp hpSwitch))
    exact ⟨hxp, mem_univ p.2⟩
  intro p hp
  apply P.occupiedGraphDomain_symmDiff_inter_prod_subset_closedGraphBand
    (connectGraphs a b f g) s (Icc a b)
  exact ⟨by simpa only [filledVerticalGraphSwitch, s] using hp, hbase (by
    simpa only [filledVerticalGraphSwitch, s] using hp)⟩

theorem frontier_occupiedGraphDomain_connectGraphs_inter_slab_subset
    (P : GraphPatch) {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    frontier (P.occupiedGraphDomain (connectGraphs a b f g)) ∩
        {p : PlanePoint | p.1 ∈ Icc a b} ⊆
      (fun x : ℝ => (x, connectGraphs a b f g x)) '' Icc a b := by
  rw [P.frontier_occupiedGraphDomain (contDiff_connectGraphs hf hg).continuous]
  rintro _ ⟨⟨x, _hx, rfl⟩, hx⟩
  exact ⟨x, hx, rfl⟩



/-- A connector value is a convex combination of its endpoint graph values. -/
theorem connectGraphs_mem_Icc
    (a b : ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    connectGraphs a b f g x ∈ Icc
      (min (f x) (g x)) (max (f x) (g x)) := by
  let θ := graphConnectorCutoff a b x
  have hθ0 : 0 ≤ θ := graphConnectorCutoff_nonneg a b x
  have hθ1 : θ ≤ 1 := graphConnectorCutoff_le_one a b x
  change min (f x) (g x) ≤ f x + θ * (g x - f x) ∧
    f x + θ * (g x - f x) ≤ max (f x) (g x)
  rcases le_total (f x) (g x) with hfg | hgf
  · rw [min_eq_left hfg, max_eq_right hfg]
    constructor
    · nlinarith [mul_nonneg hθ0 (sub_nonneg.mpr hfg)]
    · have hmul :=
        mul_le_mul_of_nonneg_right hθ1 (sub_nonneg.mpr hfg)
      nlinarith
  · rw [min_eq_right hgf, max_eq_left hgf]
    constructor
    · have hmul :=
        mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hgf)
      nlinarith
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hθ0 (sub_nonpos.mpr hgf)]

/-- Euclidean product distance is bounded by the sum of coordinate distances. -/
lemma dist_planeEuclideanHomeomorph_le_coordinate_sum
    (x₁ y₁ x₂ y₂ : ℝ) :
    dist (planeEuclideanHomeomorph (x₁, y₁))
        (planeEuclideanHomeomorph (x₂, y₂)) ≤
      dist x₁ x₂ + dist y₁ y₂ := by
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2]
  change Real.sqrt (dist x₁ x₂ ^ 2 + dist y₁ y₂ ^ 2) ≤
    dist x₁ x₂ + dist y₁ y₂
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [mul_nonneg (dist_nonneg : 0 ≤ dist x₁ x₂)
      (dist_nonneg : 0 ≤ dist y₁ y₂)]

/-- For incident continuous graphs, the entire bounded mismatch band—not only
its new frontier—eventually lies in every prescribed Euclidean junction ball. -/
theorem eventually_symmetricConnector_closedGraphBand_subset_junctionBall
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c R rho : ℝ} (hfg : f c = g c) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      closedGraphBand
          (connectGraphs
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) f g)
          (fun x => if x ≤ c then f x else g x)
          (Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n)) ⊆
        junctionBall (c, f c) rho := by
  let η := rho / 4
  have hη : 0 < η := by dsimp only [η]; positivity
  have hfNear : f ⁻¹' ball (f c) η ∈ 𝓝 c :=
    hf.continuousAt (ball_mem_nhds _ hη)
  have hgNear : g ⁻¹' ball (f c) η ∈ 𝓝 c := by
    rw [hfg]
    exact hg.continuousAt (ball_mem_nhds (g c) hη)
  obtain ⟨δ, hδ, hδsub⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem hfNear hgNear)
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        symmetricConnectorRadius R n < min δ η :=
    (tendsto_symmetricConnectorRadius_zero R).eventually
      (Iio_mem_nhds (lt_min hδ hη))
  filter_upwards [hevent] with n hn
  intro p hp
  simp only [closedGraphBand, Set.mem_ofPred_eq] at hp
  have hxdist_le :
      dist p.1 c ≤ symmetricConnectorRadius R n := by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hp.1.1, hp.1.2]
  have hxdist : dist p.1 c < min δ η := hxdist_le.trans_lt hn
  have hxδ : p.1 ∈ ball c δ := by
    rw [mem_ball]
    exact hxdist.trans_le (min_le_left δ η)
  have hvalues := hδsub hxδ
  have hfdist : dist (f p.1) (f c) < η := by
    exact (mem_ball.mp hvalues.1)
  have hgdist : dist (g p.1) (f c) < η := by
    exact (mem_ball.mp hvalues.2)
  rw [Real.dist_eq, abs_lt] at hfdist hgdist
  have hfLower : f c - η < f p.1 := by linarith [hfdist.1]
  have hfUpper : f p.1 < f c + η := by linarith [hfdist.2]
  have hgLower : f c - η < g p.1 := by linarith [hgdist.1]
  have hgUpper : g p.1 < f c + η := by linarith [hgdist.2]
  have hconnector :=
    connectGraphs_mem_Icc
      (c - symmetricConnectorRadius R n)
      (c + symmetricConnectorRadius R n) f g p.1
  have hconnectorLower :
      f c - η <
        connectGraphs
          (c - symmetricConnectorRadius R n)
          (c + symmetricConnectorRadius R n) f g p.1 :=
    (lt_min hfLower hgLower).trans_le hconnector.1
  have hconnectorUpper :
      connectGraphs
          (c - symmetricConnectorRadius R n)
          (c + symmetricConnectorRadius R n) f g p.1 <
        f c + η :=
    hconnector.2.trans_lt (max_lt hfUpper hgUpper)
  have hswitchLower :
      f c - η < (if p.1 ≤ c then f p.1 else g p.1) := by
    split_ifs <;> assumption
  have hswitchUpper :
      (if p.1 ≤ c then f p.1 else g p.1) < f c + η := by
    split_ifs <;> assumption
  have hyLower : f c - η < p.2 :=
    (lt_min hconnectorLower hswitchLower).trans_le hp.2.1
  have hyUpper : p.2 < f c + η :=
    hp.2.2.trans_lt (max_lt hconnectorUpper hswitchUpper)
  have hydist : dist p.2 (f c) < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  change dist (planeEuclideanHomeomorph p)
      (planeEuclideanHomeomorph (c, f c)) ≤ rho
  exact (dist_planeEuclideanHomeomorph_le_coordinate_sum
    p.1 p.2 c (f c)).trans (by
      have hxη : dist p.1 c < η := hxdist.trans_le (min_le_right δ η)
      dsimp only [η] at hxη hydist
      linarith)

/-- An actual `C∞` occupied-side connector, with exact old and new exterior
graphs, localized carrier modification, and complete density-weighted altered
frontier control. -/
theorem exists_smoothGraphConnector
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {a b c : ℝ} (hac : a < c) (hcb : c < b)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ∃ (h : ℝ → ℝ) (K : NNReal),
      ContDiff ℝ ∞ h ∧
      IsSmoothDomain (P.occupiedGraphDomain h) ∧
      (∀ x, x ≤ a → h x = f x) ∧
      (∀ x, b ≤ x → h x = g x) ∧
      P.occupiedGraphDomain h ∆ filledVerticalGraphSwitch P f g c ⊆
        closedGraphBand h (fun x => if x ≤ c then f x else g x) (Icc a b) ∧
      weightedTraceCost lam
          (frontier (P.occupiedGraphDomain h) ∩
            {p : PlanePoint | p.1 ∈ Icc a b}) ≤
        ENNReal.ofReal lam * (K : ENNReal) * ENNReal.ofReal (b - a) := by
  let h := connectGraphs a b f g
  have hh : ContDiff ℝ ∞ h := contDiff_connectGraphs hf hg
  obtain ⟨K, hK⟩ := exists_graphSpeed_bound_Icc (hh.of_le (by simp)) a b
  refine ⟨h, K, hh, P.isSmoothDomain_occupiedGraphDomain hh,
    fun x hx => connectGraphs_eq_left (hac.trans hcb) hx,
    fun x hx => connectGraphs_eq_right (hac.trans hcb) hx,
    occupiedGraphDomain_connectGraphs_symmDiff_filledSwitch_subset_closedGraphBand
      P hac hcb, ?_⟩
  exact (weightedTraceCost_mono lam
    (frontier_occupiedGraphDomain_connectGraphs_inter_slab_subset P hf hg)).trans
      (weightedTraceCost_graph_Icc_le_global hlam
        (hh.differentiable (by simp)) hK)

/-- A common incident point turns the graph connector into an actual
quantitative local repair family.  Every member is a literal `C∞` smooth
domain, agrees with the face-labelled old/new switch off a shrinking compact
graph band, and the complete new frontier there has vanishing weighted cost.
No regularity, cost, or convergence property of the repaired family is
supplied by the caller. -/
theorem exists_vanishing_smoothVerticalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    ∃ U : ℕ → Set PlanePoint,
      (∀ n, IsSmoothDomain (U n)) ∧
      (∀ n,
        U n ∆ filledVerticalGraphSwitch P f g c ⊆
          closedGraphBand
            (connectGraphs
              (c - symmetricConnectorRadius R n)
              (c + symmetricConnectorRadius R n) f g)
            (fun x => if x ≤ c then f x else g x)
            (Icc
              (c - symmetricConnectorRadius R n)
              (c + symmetricConnectorRadius R n))) ∧
      (∀ rho, 0 < rho →
        ∀ᶠ n : ℕ in atTop,
          U n ∆ filledVerticalGraphSwitch P f g c ⊆
            junctionBall (c, f c) rho) ∧
      Tendsto (fun n =>
        volume (U n ∆ filledVerticalGraphSwitch P f g c))
        atTop (𝓝 0) ∧
      (∀ n p,
        p.1 ∉ Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) →
          (p ∈ U n ↔ p ∈ filledVerticalGraphSwitch P f g c)) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (frontier (U n) ∩
            {p : PlanePoint |
              p.1 ∈ Icc
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n)}))
        atTop (𝓝 0) := by
  let h : ℕ → ℝ → ℝ := fun n =>
    connectGraphs
      (c - symmetricConnectorRadius R n)
      (c + symmetricConnectorRadius R n) f g
  let U : ℕ → Set PlanePoint := fun n => P.occupiedGraphDomain (h n)
  have hUsmooth : ∀ n, IsSmoothDomain (U n) := by
    intro n
    exact P.isSmoothDomain_occupiedGraphDomain (contDiff_connectGraphs hf hg)
  have hmodify : ∀ n,
      U n ∆ filledVerticalGraphSwitch P f g c ⊆
        closedGraphBand
          (connectGraphs
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) f g)
          (fun x => if x ≤ c then f x else g x)
          (Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n)) := by
    intro n
    exact
      occupiedGraphDomain_connectGraphs_symmDiff_filledSwitch_subset_closedGraphBand
        P
        (by
          have hr := symmetricConnectorRadius_pos hR n
          linarith)
        (by
          have hr := symmetricConnectorRadius_pos hR n
          linarith)
  have hball : ∀ rho, 0 < rho →
      ∀ᶠ n : ℕ in atTop,
        U n ∆ filledVerticalGraphSwitch P f g c ⊆
          junctionBall (c, f c) rho := by
    intro rho hrho
    filter_upwards [
      eventually_symmetricConnector_closedGraphBand_subset_junctionBall
        hf.continuous hg.continuous hfg hrho] with n hn
    exact (hmodify n).trans hn
  have hvolume :
      Tendsto (fun n =>
        volume (U n ∆ filledVerticalGraphSwitch P f g c))
        atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    have hballVolume := tendsto_volume_junctionBall_zero (c, f c)
    rw [ENNReal.tendsto_atTop_zero] at hballVolume
    obtain ⟨m, hm⟩ := hballVolume ε hε
    have hevent :=
      hball (junctionRadius m) (junctionRadius_pos m)
    rcases eventually_atTop.1 hevent with ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (measure_mono (hN n hn)).trans (hm m le_rfl)⟩
  have hexterior : ∀ n p,
      p.1 ∉ Icc
          (c - symmetricConnectorRadius R n)
          (c + symmetricConnectorRadius R n) →
        (p ∈ U n ↔ p ∈ filledVerticalGraphSwitch P f g c) := by
    intro n p hp
    have hnot :
        p ∉ U n ∆ filledVerticalGraphSwitch P f g c :=
      fun hmem => hp (hmodify n hmem).1
    simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hnot
    exact ⟨hnot.1, hnot.2⟩
  have hconnector :
      Tendsto (fun n =>
        weightedTraceCost lam
          ((fun x : ℝ => (x, h n x)) ''
            Icc
              (c - symmetricConnectorRadius R n)
              (c + symmetricConnectorRadius R n)))
        atTop (𝓝 0) := by
    simpa only [h] using
      tendsto_weightedTraceCost_symmetricGraphConnectors_zero
        hlam hf hg hR hfg
  have hcost :
      Tendsto (fun n =>
        weightedTraceCost lam
          (frontier (U n) ∩
            {p : PlanePoint |
              p.1 ∈ Icc
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n)}))
        atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hconnector
    · intro n
      exact bot_le
    · intro n
      apply weightedTraceCost_mono lam
      simpa only [U, h] using
        (frontier_occupiedGraphDomain_connectGraphs_inter_slab_subset
          P hf hg :
          frontier
                (P.occupiedGraphDomain
                  (connectGraphs
                    (c - symmetricConnectorRadius R n)
                    (c + symmetricConnectorRadius R n) f g)) ∩
              {p : PlanePoint |
                p.1 ∈ Icc
                  (c - symmetricConnectorRadius R n)
                  (c + symmetricConnectorRadius R n)} ⊆
            (fun x : ℝ =>
              (x, connectGraphs
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n) f g x)) ''
              Icc
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n))
  exact ⟨U, hUsmooth, hmodify, hball, hvolume, hexterior, hcost⟩

/-- Arbitrarily small one-shot form of
`exists_vanishing_smoothVerticalGraphSwitchRepair`.  The selected radius and
all chart-dependent cost constants are chosen internally after the two actual
incident graphs are known. -/
theorem exists_smoothVerticalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ r < rho ∧
      ∃ U : Set PlanePoint,
        IsSmoothDomain U ∧
        U ∆ filledVerticalGraphSwitch P f g c ⊆
          closedGraphBand
            (connectGraphs (c - r) (c + r) f g)
            (fun x => if x ≤ c then f x else g x)
            (Icc (c - r) (c + r)) ∧
        U ∆ filledVerticalGraphSwitch P f g c ⊆
          junctionBall (c, f c) rho ∧
        (∀ p, p.1 ∉ Icc (c - r) (c + r) →
          (p ∈ U ↔ p ∈ filledVerticalGraphSwitch P f g c)) ∧
        weightedTraceCost lam
            (frontier U ∩
              {p : PlanePoint | p.1 ∈ Icc (c - r) (c + r)}) <
          ENNReal.ofReal epsilon := by
  obtain ⟨U, hUsmooth, hmodify, hball, _hvolume, hexterior, hcost⟩ :=
    exists_vanishing_smoothVerticalGraphSwitchRepair
      hlam P hf hg hR hfg
  have hradius :
      Tendsto (symmetricConnectorRadius R) atTop (𝓝 0) :=
    tendsto_symmetricConnectorRadius_zero R
  have heventRadius :
      ∀ᶠ n : ℕ in atTop, symmetricConnectorRadius R n < rho :=
    hradius.eventually (Iio_mem_nhds hrho)
  have heventCost :
      ∀ᶠ n : ℕ in atTop,
        weightedTraceCost lam
            (frontier (U n) ∩
              {p : PlanePoint |
                p.1 ∈ Icc
                  (c - symmetricConnectorRadius R n)
                  (c + symmetricConnectorRadius R n)}) <
          ENNReal.ofReal epsilon :=
    hcost.eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon))
  have heventBall :
      ∀ᶠ n : ℕ in atTop,
        U n ∆ filledVerticalGraphSwitch P f g c ⊆
          junctionBall (c, f c) rho :=
    hball rho hrho
  obtain ⟨n, hnRadius, hnCost, hnBall⟩ :=
    (heventRadius.and (heventCost.and heventBall)).exists
  let r := symmetricConnectorRadius R n
  exact ⟨r, symmetricConnectorRadius_pos hR n, hnRadius, U n,
    hUsmooth n, hmodify n, hnBall, hexterior n, hnCost⟩

/-- Occupied side of a graph written with the second coordinate as parameter.
It is the exact coordinate-swap pullback of `GraphPatch.occupiedGraphDomain`,
so the existing occupied-side orientation is retained. -/
def horizontalOccupiedGraphDomain
    (P : GraphPatch) (g : ℝ → ℝ) : Set PlanePoint :=
  let e := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  e ⁻¹' P.occupiedGraphDomain g

theorem isSmoothDomain_horizontalOccupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    IsSmoothDomain (horizontalOccupiedGraphDomain P g) := by
  simpa only [horizontalOccupiedGraphDomain] using
    (P.isSmoothDomain_occupiedGraphDomain hg).coordinateSwap_preimage

/-- Face-labelled horizontal old/new graph switch. -/
def filledHorizontalGraphSwitch
    (P : GraphPatch) (f g : ℝ → ℝ) (c : ℝ) : Set PlanePoint :=
  horizontalOccupiedGraphDomain P (fun y => if y ≤ c then f y else g y)

/-- Closed horizontal band between two graphs over a base set. -/
def closedHorizontalGraphBand
    (g h : ℝ → ℝ) (s : Set ℝ) : Set PlanePoint :=
  {p | p.2 ∈ s ∧
    p.1 ∈ Icc (min (g p.2) (h p.2)) (max (g p.2) (h p.2))}

theorem mem_horizontalOccupiedGraphDomain_connectGraphs_iff_lower
    (P : GraphPatch) {a b : ℝ} {f g : ℝ → ℝ} {p : PlanePoint}
    (hab : a < b) (hp : p.2 ≤ a) :
    p ∈ horizontalOccupiedGraphDomain P (connectGraphs a b f g) ↔
      p ∈ horizontalOccupiedGraphDomain P f := by
  rcases p with ⟨x, y⟩
  have heq := connectGraphs_eq_left (f := f) (g := g) hab hp
  cases hside : P.side <;>
    simpa only [horizontalOccupiedGraphDomain,
      GraphPatch.occupiedGraphDomain, hside, Set.mem_preimage,
      ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk,
      Set.mem_ofPred_eq, heq]

theorem mem_horizontalOccupiedGraphDomain_connectGraphs_iff_upper
    (P : GraphPatch) {a b : ℝ} {f g : ℝ → ℝ} {p : PlanePoint}
    (hab : a < b) (hp : b ≤ p.2) :
    p ∈ horizontalOccupiedGraphDomain P (connectGraphs a b f g) ↔
      p ∈ horizontalOccupiedGraphDomain P g := by
  rcases p with ⟨x, y⟩
  have heq := connectGraphs_eq_right (f := f) (g := g) hab hp
  cases hside : P.side <;>
    simpa only [horizontalOccupiedGraphDomain,
      GraphPatch.occupiedGraphDomain, hside, Set.mem_preimage,
      ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk,
      Set.mem_ofPred_eq, heq]

/-- Coordinate-swapped bounded-band locality for a horizontal connector. -/
theorem horizontalOccupiedGraphDomain_connectGraphs_symmDiff_filledSwitch_subset
    (P : GraphPatch) {a b c : ℝ} {f g : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) :
    horizontalOccupiedGraphDomain P (connectGraphs a b f g) ∆
        filledHorizontalGraphSwitch P f g c ⊆
      closedHorizontalGraphBand
        (connectGraphs a b f g)
        (fun y => if y ≤ c then f y else g y)
        (Icc a b) := by
  rintro ⟨x, y⟩ hp
  have hp' :
      (y, x) ∈
        P.occupiedGraphDomain (connectGraphs a b f g) ∆
          filledVerticalGraphSwitch P f g c := by
    simpa only [horizontalOccupiedGraphDomain, filledHorizontalGraphSwitch,
      filledVerticalGraphSwitch, Set.mem_symmDiff, Set.mem_preimage,
      ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk] using hp
  have hband :=
    occupiedGraphDomain_connectGraphs_symmDiff_filledSwitch_subset_closedGraphBand
      P hac hcb hp'
  simpa only [closedGraphBand, closedHorizontalGraphBand, Set.mem_ofPred_eq]
    using hband

/-- Horizontal graph bands inherit the same shrinking-ball locality by the
coordinate-swap isometry. -/
theorem eventually_symmetricHorizontalConnector_closedGraphBand_subset_junctionBall
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c R rho : ℝ} (hfg : f c = g c) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      closedHorizontalGraphBand
          (connectGraphs
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) f g)
          (fun y => if y ≤ c then f y else g y)
          (Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n)) ⊆
        junctionBall (f c, c) rho := by
  filter_upwards [
    eventually_symmetricConnector_closedGraphBand_subset_junctionBall
      hf hg hfg hrho] with n hn
  rintro ⟨x, y⟩ hp
  have hswap :
      (y, x) ∈
        closedGraphBand
          (connectGraphs
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) f g)
          (fun z => if z ≤ c then f z else g z)
          (Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n)) := by
    simpa only [closedHorizontalGraphBand, closedGraphBand,
      Set.mem_ofPred_eq] using hp
  have hb := hn hswap
  change dist (planeEuclideanHomeomorph (y, x))
      (planeEuclideanHomeomorph (c, f c)) ≤ rho at hb
  change dist (planeEuclideanHomeomorph (x, y))
      (planeEuclideanHomeomorph (f c, c)) ≤ rho
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2] at hb ⊢
  change Real.sqrt (dist y c ^ 2 + dist x (f c) ^ 2) ≤ rho at hb
  change Real.sqrt (dist x (f c) ^ 2 + dist y c ^ 2) ≤ rho
  rwa [add_comm]

/-- The Euclidean realization of a horizontal graph. -/
def euclideanHorizontalGraph (g : ℝ → ℝ) (y : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (g y, y)

lemma euclideanHorizontalGraph_eq (g : ℝ → ℝ) :
    euclideanHorizontalGraph g =
      tangentComplexEquiv.symm ∘
        (fun y : ℝ => Complex.ofRealCLM y + g y • Complex.I) := by
  funext y
  apply tangentComplexEquiv.injective
  apply Complex.ext <;> simp [euclideanHorizontalGraph]

lemma hasDerivAt_horizontalComplexGraph
    {g : ℝ → ℝ} {y : ℝ} (hg : DifferentiableAt ℝ g y) :
    HasDerivAt
      (fun z : ℝ => Complex.ofRealCLM z + g z • Complex.I)
      (Complex.ofRealCLM 1 + deriv g y • Complex.I) y := by
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y
    (hasDerivAt_id y) |>.add (hg.hasDerivAt.smul_const Complex.I)

lemma norm_horizontalComplexGraph_deriv {g : ℝ → ℝ} {y : ℝ} :
    ‖Complex.ofRealCLM 1 + deriv g y • Complex.I‖ =
      Real.sqrt (1 + (deriv g y) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma lipschitzOnWith_euclideanHorizontalGraph_Icc
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ y ∈ Icc a b,
      Real.sqrt (1 + (deriv g y) ^ 2) ≤ (K : ℝ)) :
    LipschitzOnWith K (euclideanHorizontalGraph g) (Icc a b) := by
  rw [euclideanHorizontalGraph_eq]
  simpa only [one_mul] using
    LipschitzWith.comp_lipschitzOnWith
      tangentComplexEquiv.symm.isometry.lipschitz
      (by
        refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
          (f' := fun y => Complex.ofRealCLM 1 + deriv g y • Complex.I)
          (convex_Icc a b) ?_ ?_
        · intro y hy
          exact (hasDerivAt_horizontalComplexGraph (hg y)).hasDerivWithinAt
        · intro y hy
          rw [← NNReal.coe_le_coe, coe_nnnorm,
            norm_horizontalComplexGraph_deriv]
          exact hK y hy)
theorem hausdorffMeasure_euclideanHorizontalGraph_Icc_le
    {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ y ∈ Icc a b,
      Real.sqrt (1 + (deriv g y) ^ 2) ≤ (K : ℝ)) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun y : ℝ => (g y, y)) '' Icc a b)) ≤
      (K : ENNReal) * ENNReal.ofReal (b - a) := by
  rw [image_image]
  change (μH[1] : Measure EuclideanPlane)
      (euclideanHorizontalGraph g '' Icc a b) ≤ _
  simpa [ENNReal.rpow_one, hausdorffMeasure_real, Real.volume_Icc] using
    (lipschitzOnWith_euclideanHorizontalGraph_Icc hg hK).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num)

/-- Global-density weighted bound for a horizontal graph segment. -/
theorem weightedTraceCost_horizontalGraph_Icc_le_global
    {lam : ℝ} (hlam : 1 < lam) {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ y ∈ Icc a b,
      Real.sqrt (1 + (deriv g y) ^ 2) ≤ (K : ℝ)) :
    weightedTraceCost lam
        ((fun y : ℝ => (g y, y)) '' Icc a b) ≤
      ENNReal.ofReal lam * (K : ENNReal) * ENNReal.ofReal (b - a) := by
  calc
    weightedTraceCost lam
        ((fun y : ℝ => (g y, y)) '' Icc a b) ≤
        ENNReal.ofReal lam *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              ((fun y : ℝ => (g y, y)) '' Icc a b)) :=
      weightedTraceCost_le_density_mul_hausdorff hlam _
    _ ≤ ENNReal.ofReal lam *
          ((K : ENNReal) * ENNReal.ofReal (b - a)) := by
      gcongr
      exact hausdorffMeasure_euclideanHorizontalGraph_Icc_le hg hK
    _ = _ := by rw [mul_assoc]

theorem frontier_horizontalOccupiedGraphDomain_connectGraphs_inter_slab_subset
    (P : GraphPatch) {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    frontier
          (horizontalOccupiedGraphDomain P (connectGraphs a b f g)) ∩
        {p : PlanePoint | p.2 ∈ Icc a b} ⊆
      (fun y : ℝ => (connectGraphs a b f g y, y)) '' Icc a b := by
  let e : PlanePoint ≃L[ℝ] PlanePoint :=
    ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  rintro ⟨x, y⟩ ⟨hpFrontier, hpSlab⟩
  have hpFrontier' :
      e (x, y) ∈ frontier
        (P.occupiedGraphDomain (connectGraphs a b f g)) := by
    change (x, y) ∈ frontier
      (e.toHomeomorph ⁻¹'
        P.occupiedGraphDomain (connectGraphs a b f g)) at hpFrontier
    rwa [← e.toHomeomorph.preimage_frontier] at hpFrontier
  have hpSlab' : (e (x, y)).1 ∈ Icc a b := by
    simpa only [e, ContinuousLinearEquiv.prodComm_apply,
      Prod.swap_prod_mk, Set.mem_ofPred_eq] using hpSlab
  have hpImage :=
    frontier_occupiedGraphDomain_connectGraphs_inter_slab_subset
      P hf hg ⟨hpFrontier', hpSlab'⟩
  rcases hpImage with ⟨z, hz, heq⟩
  refine ⟨z, hz, ?_⟩
  have heq' := congrArg e heq
  simpa only [e, ContinuousLinearEquiv.prodComm_apply,
    Prod.swap_prod_mk] using heq'

/-- The actual horizontal connector trace has vanishing complete weighted
cost around a common incident point. -/
theorem tendsto_weightedTraceCost_symmetricHorizontalGraphConnectors_zero
    {lam : ℝ} (hlam : 1 < lam)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    Tendsto (fun n =>
      let r := symmetricConnectorRadius R n
      weightedTraceCost lam
        ((fun y : ℝ =>
          (connectGraphs (c - r) (c + r) f g y, y)) ''
            Icc (c - r) (c + r))) atTop (𝓝 0) := by
  obtain ⟨D, hD, hDbound⟩ := exists_smoothTransition_deriv_bound
  obtain ⟨M, hM, hfM, hgM⟩ :=
    exists_common_deriv_bound_Icc
      (hf.of_le (by simp)) (hg.of_le (by simp)) (c - R) (c + R)
  have hKnonneg : 0 ≤ 1 + (3 * M + 2 * D * M) := by positivity
  let K : NNReal := ⟨1 + (3 * M + 2 * D * M), hKnonneg⟩
  let width : ℕ → ℝ := fun n => 2 * symmetricConnectorRadius R n
  have hwidthReal : Tendsto width atTop (𝓝 0) := by
    simpa only [width, mul_zero] using
      tendsto_const_nhds.mul (tendsto_symmetricConnectorRadius_zero R)
  have hwidth : Tendsto (fun n => ENNReal.ofReal (width n))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hwidthReal
  have hupper : Tendsto
      (fun n => (ENNReal.ofReal lam * (K : ENNReal)) *
        ENNReal.ofReal (width n)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hwidth
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
  · intro n
    exact bot_le
  · intro n
    let r := symmetricConnectorRadius R n
    have hr : 0 < r := symmetricConnectorRadius_pos hR n
    have hrle : r ≤ R := symmetricConnectorRadius_le hR.le n
    have hsub : Icc (c - r) (c + r) ⊆ Icc (c - R) (c + R) := by
      intro y hy
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hc : c ∈ Icc (c - r) (c + r) := by
      constructor <;> linarith
    have hspeed : ∀ y ∈ Icc (c - r) (c + r),
        Real.sqrt
          (1 + (deriv (connectGraphs (c - r) (c + r) f g) y) ^ 2) ≤
          (K : ℝ) := by
      intro y hy
      have hslope :
          |deriv (connectGraphs (c - r) (c + r) f g) y| ≤
            3 * M + 2 * D * M :=
        abs_deriv_connectGraphs_le (by linarith) hc hy hf hg hM hD
          (fun z hz => hfM z (hsub hz))
          (fun z hz => hgM z (hsub hz)) hDbound hfg
      calc
        Real.sqrt
            (1 + (deriv (connectGraphs (c - r) (c + r) f g) y) ^ 2) ≤
            1 + |deriv (connectGraphs (c - r) (c + r) f g) y| := by
          let q := deriv (connectGraphs (c - r) (c + r) f g) y
          have hsqrt := Real.sqrt_nonneg (1 + q ^ 2)
          have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 1 + q ^ 2)
          have habs := abs_nonneg q
          change Real.sqrt (1 + q ^ 2) ≤ 1 + |q|
          nlinarith [sq_abs q]
        _ ≤ 1 + (3 * M + 2 * D * M) := add_le_add le_rfl hslope
        _ = (K : ℝ) := rfl
    have hcost := weightedTraceCost_horizontalGraph_Icc_le_global hlam
      ((contDiff_connectGraphs hf hg).differentiable (by simp)) hspeed
    simpa only [width, r, add_sub_sub_cancel, add_sub_cancel_left,
      show c + r - (c - r) = 2 * r by ring] using hcost

/-- Horizontal-cut counterpart of the vertical quantitative repair family. -/
theorem exists_vanishing_smoothHorizontalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    ∃ U : ℕ → Set PlanePoint,
      (∀ n, IsSmoothDomain (U n)) ∧
      (∀ n,
        U n ∆ filledHorizontalGraphSwitch P f g c ⊆
          closedHorizontalGraphBand
            (connectGraphs
              (c - symmetricConnectorRadius R n)
              (c + symmetricConnectorRadius R n) f g)
            (fun y => if y ≤ c then f y else g y)
            (Icc
              (c - symmetricConnectorRadius R n)
              (c + symmetricConnectorRadius R n))) ∧
      (∀ rho, 0 < rho →
        ∀ᶠ n : ℕ in atTop,
          U n ∆ filledHorizontalGraphSwitch P f g c ⊆
            junctionBall (f c, c) rho) ∧
      Tendsto (fun n =>
        volume (U n ∆ filledHorizontalGraphSwitch P f g c))
        atTop (𝓝 0) ∧
      (∀ n p,
        p.2 ∉ Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) →
          (p ∈ U n ↔ p ∈ filledHorizontalGraphSwitch P f g c)) ∧
      Tendsto (fun n =>
        weightedTraceCost lam
          (frontier (U n) ∩
            {p : PlanePoint |
              p.2 ∈ Icc
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n)}))
        atTop (𝓝 0) := by
  let h : ℕ → ℝ → ℝ := fun n =>
    connectGraphs
      (c - symmetricConnectorRadius R n)
      (c + symmetricConnectorRadius R n) f g
  let U : ℕ → Set PlanePoint := fun n => horizontalOccupiedGraphDomain P (h n)
  have hUsmooth : ∀ n, IsSmoothDomain (U n) := by
    intro n
    exact isSmoothDomain_horizontalOccupiedGraphDomain P
      (contDiff_connectGraphs hf hg)
  have hmodify : ∀ n,
      U n ∆ filledHorizontalGraphSwitch P f g c ⊆
        closedHorizontalGraphBand
          (connectGraphs
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n) f g)
          (fun y => if y ≤ c then f y else g y)
          (Icc
            (c - symmetricConnectorRadius R n)
            (c + symmetricConnectorRadius R n)) := by
    intro n
    exact
      horizontalOccupiedGraphDomain_connectGraphs_symmDiff_filledSwitch_subset
        P
        (by
          have hr := symmetricConnectorRadius_pos hR n
          linarith)
        (by
          have hr := symmetricConnectorRadius_pos hR n
          linarith)
  have hball : ∀ rho, 0 < rho →
      ∀ᶠ n : ℕ in atTop,
        U n ∆ filledHorizontalGraphSwitch P f g c ⊆
          junctionBall (f c, c) rho := by
    intro rho hrho
    filter_upwards [
      eventually_symmetricHorizontalConnector_closedGraphBand_subset_junctionBall
        hf.continuous hg.continuous hfg hrho] with n hn
    exact (hmodify n).trans hn
  have hvolume :
      Tendsto (fun n =>
        volume (U n ∆ filledHorizontalGraphSwitch P f g c))
        atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    have hballVolume := tendsto_volume_junctionBall_zero (f c, c)
    rw [ENNReal.tendsto_atTop_zero] at hballVolume
    obtain ⟨m, hm⟩ := hballVolume ε hε
    have hevent :=
      hball (junctionRadius m) (junctionRadius_pos m)
    rcases eventually_atTop.1 hevent with ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (measure_mono (hN n hn)).trans (hm m le_rfl)⟩
  have hexterior : ∀ n p,
      p.2 ∉ Icc
          (c - symmetricConnectorRadius R n)
          (c + symmetricConnectorRadius R n) →
        (p ∈ U n ↔ p ∈ filledHorizontalGraphSwitch P f g c) := by
    intro n p hp
    have hnot :
        p ∉ U n ∆ filledHorizontalGraphSwitch P f g c :=
      fun hmem => hp (hmodify n hmem).1
    simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hnot
    exact ⟨hnot.1, hnot.2⟩
  have hconnector :
      Tendsto (fun n =>
        weightedTraceCost lam
          ((fun y : ℝ => (h n y, y)) ''
            Icc
              (c - symmetricConnectorRadius R n)
              (c + symmetricConnectorRadius R n)))
        atTop (𝓝 0) := by
    simpa only [h] using
      tendsto_weightedTraceCost_symmetricHorizontalGraphConnectors_zero
        hlam hf hg hR hfg
  have hcost :
      Tendsto (fun n =>
        weightedTraceCost lam
          (frontier (U n) ∩
            {p : PlanePoint |
              p.2 ∈ Icc
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n)}))
        atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hconnector
    · intro n
      exact bot_le
    · intro n
      apply weightedTraceCost_mono lam
      simpa only [U, h] using
        (frontier_horizontalOccupiedGraphDomain_connectGraphs_inter_slab_subset
          P hf hg :
          frontier
                (horizontalOccupiedGraphDomain P
                  (connectGraphs
                    (c - symmetricConnectorRadius R n)
                    (c + symmetricConnectorRadius R n) f g)) ∩
              {p : PlanePoint |
                p.2 ∈ Icc
                  (c - symmetricConnectorRadius R n)
                  (c + symmetricConnectorRadius R n)} ⊆
            (fun y : ℝ =>
              (connectGraphs
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n) f g y, y)) ''
              Icc
                (c - symmetricConnectorRadius R n)
                (c + symmetricConnectorRadius R n))
  exact ⟨U, hUsmooth, hmodify, hball, hvolume, hexterior, hcost⟩

/-- One-shot horizontal repair with compact ball locality and arbitrarily
small complete altered-frontier cost. -/
theorem exists_smoothHorizontalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ r < rho ∧
      ∃ U : Set PlanePoint,
        IsSmoothDomain U ∧
        U ∆ filledHorizontalGraphSwitch P f g c ⊆
          closedHorizontalGraphBand
            (connectGraphs (c - r) (c + r) f g)
            (fun y => if y ≤ c then f y else g y)
            (Icc (c - r) (c + r)) ∧
        U ∆ filledHorizontalGraphSwitch P f g c ⊆
          junctionBall (f c, c) rho ∧
        (∀ p, p.2 ∉ Icc (c - r) (c + r) →
          (p ∈ U ↔ p ∈ filledHorizontalGraphSwitch P f g c)) ∧
        weightedTraceCost lam
            (frontier U ∩
              {p : PlanePoint | p.2 ∈ Icc (c - r) (c + r)}) <
          ENNReal.ofReal epsilon := by
  obtain ⟨U, hUsmooth, hmodify, hball, _hvolume, hexterior, hcost⟩ :=
    exists_vanishing_smoothHorizontalGraphSwitchRepair
      hlam P hf hg hR hfg
  have hradius :
      Tendsto (symmetricConnectorRadius R) atTop (𝓝 0) :=
    tendsto_symmetricConnectorRadius_zero R
  have heventRadius :
      ∀ᶠ n : ℕ in atTop, symmetricConnectorRadius R n < rho :=
    hradius.eventually (Iio_mem_nhds hrho)
  have heventCost :
      ∀ᶠ n : ℕ in atTop,
        weightedTraceCost lam
            (frontier (U n) ∩
              {p : PlanePoint |
                p.2 ∈ Icc
                  (c - symmetricConnectorRadius R n)
                  (c + symmetricConnectorRadius R n)}) <
          ENNReal.ofReal epsilon :=
    hcost.eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon))
  have heventBall :
      ∀ᶠ n : ℕ in atTop,
        U n ∆ filledHorizontalGraphSwitch P f g c ⊆
          junctionBall (f c, c) rho :=
    hball rho hrho
  obtain ⟨n, hnRadius, hnCost, hnBall⟩ :=
    (heventRadius.and (heventCost.and heventBall)).exists
  let r := symmetricConnectorRadius R n
  exact ⟨r, symmetricConnectorRadius_pos hR n, hnRadius, U n,
    hUsmooth n, hmodify n, hnBall, hexterior n, hnCost⟩
/-- Compact scalar bump used to round a four-sector crossing. -/
def oppositeCrossingBump (r t : ℝ) : ℝ :=
  1 - Real.smoothTransition ((t ^ 2 - r ^ 2) / (3 * r ^ 2))

lemma contDiff_oppositeCrossingBump (r : ℝ) :
    ContDiff ℝ ∞ (oppositeCrossingBump r) := by
  unfold oppositeCrossingBump
  fun_prop

lemma oppositeCrossingBump_mem_Icc (r t : ℝ) :
    oppositeCrossingBump r t ∈ Icc (0 : ℝ) 1 := by
  unfold oppositeCrossingBump
  constructor
  · exact sub_nonneg.mpr (Real.smoothTransition.le_one _)
  · exact sub_le_self 1 (Real.smoothTransition.nonneg _)

lemma oppositeCrossingBump_eq_one_of_abs_le
    {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r) :
    oppositeCrossingBump r t = 1 := by
  have ht2 : t ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using
      ((sq_le_sq₀ (abs_nonneg t) hr.le).2 ht)
  rw [oppositeCrossingBump, Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht2) (by positivity)

lemma oppositeCrossingBump_eq_zero_of_two_mul_le_abs
    {r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ |t|) :
    oppositeCrossingBump r t = 0 := by
  have ht2 : 4 * r ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  rw [oppositeCrossingBump, Real.smoothTransition.one_of_one_le]
  · ring
  · rw [one_le_div₀ (by positivity : 0 < 3 * r ^ 2)]
    nlinarith

/-- A positive smooth replacement of `t^2`, equal to it outside `[-2r,2r]`. -/
def roundedCrossingSquare (r t : ℝ) : ℝ :=
  t ^ 2 + r ^ 2 * oppositeCrossingBump r t

lemma contDiff_roundedCrossingSquare (r : ℝ) :
    ContDiff ℝ ∞ (roundedCrossingSquare r) := by
  unfold roundedCrossingSquare
  exact (contDiff_id.pow 2).add
    (contDiff_const.mul (contDiff_oppositeCrossingBump r))

lemma roundedCrossingSquare_pos {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < roundedCrossingSquare r t := by
  by_cases ht : t = 0
  · subst t
    rw [roundedCrossingSquare,
      oppositeCrossingBump_eq_one_of_abs_le hr (by simpa using hr.le)]
    positivity
  · have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hb := (oppositeCrossingBump_mem_Icc r t).1
    unfold roundedCrossingSquare
    positivity

lemma roundedCrossingSquare_eq_sq_of_two_mul_le_abs
    {r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ |t|) :
    roundedCrossingSquare r t = t ^ 2 := by
  rw [roundedCrossingSquare,
    oppositeCrossingBump_eq_zero_of_two_mul_le_abs hr ht, mul_zero, add_zero]

/-- Signed normal coordinate relative to a smooth incident graph. -/
def oppositeCrossingNormal (h : ℝ → ℝ) (p : PlanePoint) : ℝ :=
  p.2 - h p.1

/-- First diagonal coordinate at a vertical splice face. -/
def oppositeCrossingT (c : ℝ) (h : ℝ → ℝ) (p : PlanePoint) : ℝ :=
  (p.1 - c) - oppositeCrossingNormal h p

/-- Second diagonal coordinate at a vertical splice face. -/
def oppositeCrossingS (c : ℝ) (h : ℝ → ℝ) (p : PlanePoint) : ℝ :=
  (p.1 - c) + oppositeCrossingNormal h p

/-- Smooth defining function for a rounded opposite-side crossing. -/
def roundedOppositeCrossingValue
    (side : OccupiedSide) (c r : ℝ) (h : ℝ → ℝ) (p : PlanePoint) : ℝ :=
  side.areaSign *
    (roundedCrossingSquare r (oppositeCrossingT c h p) -
      (oppositeCrossingS c h p) ^ 2)

lemma contDiff_roundedOppositeCrossingValue
    (side : OccupiedSide) (c r : ℝ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (roundedOppositeCrossingValue side c r h) := by
  unfold roundedOppositeCrossingValue roundedCrossingSquare
    oppositeCrossingT oppositeCrossingS oppositeCrossingNormal
    oppositeCrossingBump
  fun_prop

lemma roundedOppositeCrossingValue_regular
    (side : OccupiedSide) (c : ℝ) {r : ℝ} (hr : 0 < r)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ∀ p, roundedOppositeCrossingValue side c r h p = 0 →
      fderiv ℝ (roundedOppositeCrossingValue side c r h) p ≠ 0 := by
  rintro ⟨px, py⟩ hp hzero
  let m := deriv h px
  let curve : ℝ → PlanePoint := fun a =>
    (a + px, (m + 1) * a + py)
  have hhderiv : HasDerivAt h m px :=
    (hh.differentiable (by simp) px).hasDerivAt
  have hx : HasDerivAt (fun a : ℝ => a + px) 1 0 :=
    (hasDerivAt_id 0).add_const px
  have hy : HasDerivAt (fun a : ℝ => (m + 1) * a + py) (m + 1) 0 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id 0).const_mul (m + 1)).add_const py
  have hcurve : HasDerivAt curve (1, m + 1) 0 := by
    exact hx.prodMk hy
  have hHcomp : HasDerivAt (fun a => h (a + px)) m 0 := by
    have hhderiv' : HasDerivAt h m ((fun a : ℝ => a + px) 0) := by
      simpa using hhderiv
    change HasDerivAt (h ∘ fun a : ℝ => a + px) m 0
    simpa only [mul_one] using hhderiv'.comp 0 hx
  have hnormal : HasDerivAt
      (fun a => oppositeCrossingNormal h (curve a)) 1 0 := by
    change HasDerivAt
      ((fun a => (m + 1) * a + py) - fun a => h (a + px)) 1 0
    have hz := hy.sub hHcomp
    have hm : m + 1 - m = 1 := by ring
    rw [hm] at hz
    exact hz
  have hX : HasDerivAt (fun a => (curve a).1 - c) 1 0 := by
    change HasDerivAt (fun a => (a + px) - c) 1 0
    exact hx.sub_const c
  have ht : HasDerivAt
      (fun a => oppositeCrossingT c h (curve a)) 0 0 := by
    change HasDerivAt
      ((fun a => (curve a).1 - c) -
        fun a => oppositeCrossingNormal h (curve a)) 0 0
    simpa only [sub_self] using hX.sub hnormal
  have hs : HasDerivAt
      (fun a => oppositeCrossingS c h (curve a)) 2 0 := by
    change HasDerivAt
      ((fun a => (curve a).1 - c) +
        fun a => oppositeCrossingNormal h (curve a)) 2 0
    have hs' := hX.add hnormal
    norm_num at hs'
    exact hs'
  have hrounded : HasDerivAt
      (fun a => roundedCrossingSquare r
        (oppositeCrossingT c h (curve a))) 0 0 := by
    have hq : HasDerivAt (roundedCrossingSquare r)
        (deriv (roundedCrossingSquare r)
          (oppositeCrossingT c h (curve 0)))
        (oppositeCrossingT c h (curve 0)) :=
      (contDiff_roundedCrossingSquare r).differentiable
        (by simp) _ |>.hasDerivAt
    change HasDerivAt
      (roundedCrossingSquare r ∘
        fun a => oppositeCrossingT c h (curve a)) 0 0
    simpa only [mul_zero] using hq.comp 0 ht
  have hsquare : HasDerivAt
      (fun a => (oppositeCrossingS c h (curve a)) ^ 2)
      (4 * oppositeCrossingS c h (px, py)) 0 := by
    have hsq := hs.pow 2
    change HasDerivAt
      ((fun a => oppositeCrossingS c h (curve a)) ^ 2)
      (4 * oppositeCrossingS c h (px, py)) 0
    have hder :
        (2 : ℝ) * oppositeCrossingS c h (curve 0) ^ (2 - 1) * 2 =
          4 * oppositeCrossingS c h (px, py) := by
      simp [curve, oppositeCrossingS, oppositeCrossingNormal]
      ring
    rw [← hder]
    exact hsq
  have hcomposition : HasDerivAt
      (fun a => roundedOppositeCrossingValue side c r h (curve a))
      (-4 * side.areaSign * oppositeCrossingS c h (px, py)) 0 := by
    unfold roundedOppositeCrossingValue
    have hcomp := (hrounded.sub hsquare).const_mul side.areaSign
    have hder :
        side.areaSign * (0 - 4 * oppositeCrossingS c h (px, py)) =
          -4 * side.areaSign * oppositeCrossingS c h (px, py) := by ring
    rw [← hder]
    simpa only [Pi.sub_apply] using hcomp
  have hzeroComposition : HasDerivAt
      (fun a => roundedOppositeCrossingValue side c r h (curve a)) 0 0 := by
    have hF := (contDiff_roundedOppositeCrossingValue side c r hh).differentiable
      (by simp) (px, py) |>.hasFDerivAt
    rw [hzero] at hF
    have hF' : HasFDerivAt
        (roundedOppositeCrossingValue side c r h)
        (0 : PlanePoint →L[ℝ] ℝ) (curve 0) := by
      simpa [curve] using hF
    change HasDerivAt
      (roundedOppositeCrossingValue side c r h ∘ curve) 0 0
    simpa only [zero_apply] using hF'.comp_hasDerivAt 0 hcurve
  have hderivZero :
      -4 * side.areaSign * oppositeCrossingS c h (px, py) = 0 :=
    hcomposition.unique hzeroComposition
  have hsne : oppositeCrossingS c h (px, py) ≠ 0 := by
    intro hs0
    unfold roundedOppositeCrossingValue at hp
    rw [hs0] at hp
    norm_num only [zero_pow, sub_zero] at hp
    have hprod := mul_eq_zero.mp hp
    have hroundzero :=
      hprod.resolve_left (OccupiedSide.areaSign_ne_zero side)
    exact (roundedCrossingSquare_pos hr _).ne' hroundzero
  have hprod := mul_eq_zero.mp hderivZero
  exact hsne (hprod.resolve_left
    (mul_ne_zero (by norm_num) (OccupiedSide.areaSign_ne_zero side)))

/-- The rounded four-sector carrier is a literal smooth domain. -/
theorem isSmoothDomain_roundedOppositeCrossing
    (side : OccupiedSide) (c : ℝ) {r : ℝ} (hr : 0 < r)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    IsSmoothDomain {p | roundedOppositeCrossingValue side c r h p < 0} := by
  exact isSmoothDomain_sublevel_of_regular
    (contDiff_roundedOppositeCrossingValue side c r hh)
    (roundedOppositeCrossingValue_regular side c hr hh)

/-- The occupied side opposite to a graph patch's declared side. -/
def oppositeOccupiedGraphDomain
    (P : GraphPatch) (g : ℝ → ℝ) : Set PlanePoint :=
  match P.side with
  | .below => {p | g p.1 < p.2}
  | .above => {p | p.2 < g p.1}

/-- The literal open four-sector carrier at an opposite-side vertical splice. -/
def filledOppositeVerticalGraphSwitch
    (P : GraphPatch) (f g : ℝ → ℝ) (c : ℝ) : Set PlanePoint :=
  ({p : PlanePoint | p.1 < c} ∩ P.occupiedGraphDomain f) ∪
    ({p : PlanePoint | c < p.1} ∩ oppositeOccupiedGraphDomain P g)

lemma isOpen_oppositeOccupiedGraphDomain
    (P : GraphPatch) {g : ℝ → ℝ} (hg : Continuous g) :
    IsOpen (oppositeOccupiedGraphDomain P g) := by
  have hgc : Continuous (fun p : PlanePoint => g p.1) :=
    hg.comp continuous_fst
  cases hside : P.side with
  | below =>
      simpa only [oppositeOccupiedGraphDomain, hside] using
        isOpen_lt hgc continuous_snd
  | above =>
      simpa only [oppositeOccupiedGraphDomain, hside] using
        isOpen_lt continuous_snd hgc

lemma isOpen_filledOppositeVerticalGraphSwitch
    (P : GraphPatch) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (c : ℝ) :
    IsOpen (filledOppositeVerticalGraphSwitch P f g c) := by
  unfold filledOppositeVerticalGraphSwitch
  apply IsOpen.union
  · apply (isOpen_lt continuous_fst continuous_const).inter
    have hfc : Continuous (fun p : PlanePoint => f p.1) :=
      hf.comp continuous_fst
    cases hside : P.side with
    | below =>
        simpa only [GraphPatch.occupiedGraphDomain, hside] using
          isOpen_lt continuous_snd hfc
    | above =>
        simpa only [GraphPatch.occupiedGraphDomain, hside] using
          isOpen_lt hfc continuous_snd
  · exact (isOpen_lt continuous_const continuous_fst).inter
      (isOpen_oppositeOccupiedGraphDomain P hg)

lemma filledOppositeVerticalGraphSwitch_subset_spliceIn
    (P : GraphPatch) (f g : ℝ → ℝ) (c : ℝ) :
    filledOppositeVerticalGraphSwitch P f g c ⊆
      spliceIn (P.occupiedGraphDomain f) (oppositeOccupiedGraphDomain P g)
        {p : PlanePoint | c ≤ p.1} := by
  intro p hp
  rcases hp with hp | hp
  · apply Or.inl
    exact ⟨hp.2, by simpa only [Set.mem_ofPred_eq] using not_le_of_gt hp.1⟩
  · apply Or.inr
    exact ⟨hp.2, by simpa only [Set.mem_ofPred_eq] using hp.1.le⟩

/-- Opposite occupied sides produce the genuine four-sector topology: the
canonical `openSpliceIn` has no residual cutting-line points. -/
theorem openSpliceIn_oppositeOccupiedGraphDomains_rightHalfspace_eq
    (P : GraphPatch) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c : ℝ} (hfg : f c = g c) :
    openSpliceIn (P.occupiedGraphDomain f) (oppositeOccupiedGraphDomain P g)
        {p : PlanePoint | c ≤ p.1} =
      filledOppositeVerticalGraphSwitch P f g c := by
  apply Subset.antisymm
  · intro p hp
    have hpRaw :
        p ∈ spliceIn (P.occupiedGraphDomain f)
          (oppositeOccupiedGraphDomain P g) {q : PlanePoint | c ≤ q.1} :=
      interior_subset hp
    rcases lt_trichotomy p.1 c with hpc | hpc | hpc
    · left
      refine ⟨hpc, ?_⟩
      rcases hpRaw with hpRaw | hpRaw
      · exact hpRaw.1
      · exact False.elim ((not_le_of_gt hpc) hpRaw.2)
    · rcases p with ⟨px, py⟩
      change px = c at hpc
      subst px
      exfalso
      have hpInterior :
          ((c, py) : PlanePoint) ∈ interior
            (spliceIn (P.occupiedGraphDomain f)
              (oppositeOccupiedGraphDomain P g)
              {q : PlanePoint | c ≤ q.1}) := hp
      obtain ⟨epsilon, hepsilon, hball⟩ :=
        Metric.mem_nhds_iff.mp (IsOpen.mem_nhds isOpen_interior hpInterior)
      cases hside : P.side with
      | below =>
          have hpy : f c < py := by
            simpa only [spliceIn, oppositeOccupiedGraphDomain,
              GraphPatch.occupiedGraphDomain, hside, Set.mem_union,
              Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, le_rfl,
              not_true_eq_false, and_false, false_or, and_true, hfg] using hpRaw
          have hfNear : f ⁻¹' Iio py ∈ 𝓝 c :=
            hf.continuousAt (Iio_mem_nhds hpy)
          obtain ⟨delta, hdelta, hdeltaBall⟩ :=
            Metric.mem_nhds_iff.mp hfNear
          let eta := min epsilon delta / 2
          have heta : 0 < eta := by dsimp [eta]; positivity
          let q : PlanePoint := (c - eta, py)
          have hqBall : q ∈ ball ((c, py) : PlanePoint) epsilon := by
            rw [mem_ball]
            change max |c - eta - c| |py - py| < epsilon
            rw [sub_self, abs_zero, max_eq_left (abs_nonneg _),
              show c - eta - c = -eta by ring, abs_neg, abs_of_pos heta]
            dsimp only [eta]
            have hmin : min epsilon delta ≤ epsilon := min_le_left _ _
            linarith
          have hqRaw := interior_subset (hball hqBall)
          have hqf : f (c - eta) < py := by
            have hqDelta : c - eta ∈ ball c delta := by
              rw [mem_ball, Real.dist_eq,
                show |c - eta - c| = eta by
                  rw [show c - eta - c = -eta by ring, abs_neg,
                    abs_of_pos heta]]
              dsimp only [eta]
              have hmin : min epsilon delta ≤ delta := min_le_right _ _
              linarith
            exact hdeltaBall hqDelta
          have hqxc : ¬c ≤ c - eta := by linarith
          dsimp only [q] at hqRaw
          simp only [GraphPatch.occupiedGraphDomain, hside] at hqRaw
          rcases hqRaw with hqRaw | hqRaw
          · exact (not_lt_of_ge hqf.le) hqRaw.1
          · exact hqxc hqRaw.2
      | above =>
          have hpy : py < f c := by
            simpa only [spliceIn, oppositeOccupiedGraphDomain,
              GraphPatch.occupiedGraphDomain, hside, Set.mem_union,
              Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, le_rfl,
              not_true_eq_false, and_false, false_or, and_true, hfg] using hpRaw
          have hfNear : f ⁻¹' Ioi py ∈ 𝓝 c :=
            hf.continuousAt (Ioi_mem_nhds hpy)
          obtain ⟨delta, hdelta, hdeltaBall⟩ :=
            Metric.mem_nhds_iff.mp hfNear
          let eta := min epsilon delta / 2
          have heta : 0 < eta := by dsimp [eta]; positivity
          let q : PlanePoint := (c - eta, py)
          have hqBall : q ∈ ball ((c, py) : PlanePoint) epsilon := by
            rw [mem_ball]
            change max |c - eta - c| |py - py| < epsilon
            rw [sub_self, abs_zero, max_eq_left (abs_nonneg _),
              show c - eta - c = -eta by ring, abs_neg, abs_of_pos heta]
            dsimp only [eta]
            have hmin : min epsilon delta ≤ epsilon := min_le_left _ _
            linarith
          have hqRaw := interior_subset (hball hqBall)
          have hqf : py < f (c - eta) := by
            have hqDelta : c - eta ∈ ball c delta := by
              rw [mem_ball, Real.dist_eq,
                show |c - eta - c| = eta by
                  rw [show c - eta - c = -eta by ring, abs_neg,
                    abs_of_pos heta]]
              dsimp only [eta]
              have hmin : min epsilon delta ≤ delta := min_le_right _ _
              linarith
            exact hdeltaBall hqDelta
          have hqxc : ¬c ≤ c - eta := by linarith
          dsimp only [q] at hqRaw
          simp only [GraphPatch.occupiedGraphDomain, hside] at hqRaw
          rcases hqRaw with hqRaw | hqRaw
          · exact (not_lt_of_ge hqf.le) hqRaw.1
          · exact hqxc hqRaw.2
    · right
      refine ⟨hpc, ?_⟩
      rcases hpRaw with hpRaw | hpRaw
      · exact False.elim (hpRaw.2 hpc.le)
      · exact hpRaw.1
  · apply interior_maximal
    · exact filledOppositeVerticalGraphSwitch_subset_spliceIn P f g c
    · exact isOpen_filledOppositeVerticalGraphSwitch P hf hg c


/-- Defining function for the unrounded opposite-side crossing. -/
def oppositeCrossingValue
    (side : OccupiedSide) (c : ℝ) (h : ℝ → ℝ) (p : PlanePoint) : ℝ :=
  side.areaSign *
    ((oppositeCrossingT c h p) ^ 2 - (oppositeCrossingS c h p) ^ 2)

/-- The four literal occupied sectors are exactly one signed double-cone
sublevel after straightening the common graph. -/
theorem filledOppositeVerticalGraphSwitch_eq_crossingSublevel
    (P : GraphPatch) (h : ℝ → ℝ) (c : ℝ) :
    filledOppositeVerticalGraphSwitch P h h c =
      {p | oppositeCrossingValue P.side c h p < 0} := by
  ext p
  rcases p with ⟨x, y⟩
  cases hside : P.side with
  | below =>
      simp only [filledOppositeVerticalGraphSwitch,
        oppositeOccupiedGraphDomain, GraphPatch.occupiedGraphDomain,
        oppositeCrossingValue, oppositeCrossingT, oppositeCrossingS,
        oppositeCrossingNormal, hside, OccupiedSide.areaSign_below,
        one_mul, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (⟨hxc, hyh⟩ | ⟨hcx, hhy⟩) <;> nlinarith
      · intro hp
        rcases lt_trichotomy x c with hxc | hxc | hcx
        · left
          refine ⟨hxc, ?_⟩
          nlinarith
        · subst x
          nlinarith
        · right
          refine ⟨hcx, ?_⟩
          nlinarith
  | above =>
      simp only [filledOppositeVerticalGraphSwitch,
        oppositeOccupiedGraphDomain, GraphPatch.occupiedGraphDomain,
        oppositeCrossingValue, oppositeCrossingT, oppositeCrossingS,
        oppositeCrossingNormal, hside, OccupiedSide.areaSign_above,
        neg_mul, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro (⟨hxc, hhy⟩ | ⟨hcx, hyh⟩) <;> nlinarith
      · intro hp
        rcases lt_trichotomy x c with hxc | hxc | hcx
        · left
          refine ⟨hxc, ?_⟩
          nlinarith
        · subst x
          nlinarith
        · right
          refine ⟨hcx, ?_⟩
          nlinarith

/-- Coordinate core containing the complete carrier modification introduced
by rounding one double-cone crossing. -/
def roundedOppositeCrossingCore
    (c : ℝ) (h : ℝ → ℝ) (r : ℝ) : Set PlanePoint :=
  {p | |oppositeCrossingT c h p| < 2 * r ∧
    |oppositeCrossingS c h p| ≤ 3 * r}

theorem roundedOppositeCrossing_symmDiff_crossing_subset_core
    (side : OccupiedSide) (c : ℝ) {r : ℝ} (hr : 0 < r)
    (h : ℝ → ℝ) :
    {p | roundedOppositeCrossingValue side c r h p < 0} ∆
        {p | oppositeCrossingValue side c h p < 0} ⊆
      roundedOppositeCrossingCore c h r := by
  intro p hp
  let t := oppositeCrossingT c h p
  let s := oppositeCrossingS c h p
  change
    (side.areaSign * (roundedCrossingSquare r t - s ^ 2) < 0 ∧
        ¬side.areaSign * (t ^ 2 - s ^ 2) < 0) ∨
      (side.areaSign * (t ^ 2 - s ^ 2) < 0 ∧
        ¬side.areaSign * (roundedCrossingSquare r t - s ^ 2) < 0) at hp
  have hb0 : 0 ≤ oppositeCrossingBump r t :=
    (oppositeCrossingBump_mem_Icc r t).1
  have hb1 : oppositeCrossingBump r t ≤ 1 :=
    (oppositeCrossingBump_mem_Icc r t).2
  have ht : |t| < 2 * r := by
    by_contra hnot
    have htwo : 2 * r ≤ |t| := le_of_not_gt hnot
    have heq := roundedCrossingSquare_eq_sq_of_two_mul_le_abs hr htwo
    rcases hp with hp | hp <;>
      exact hp.2 (by simpa only [heq] using hp.1)
  have hs2 : s ^ 2 ≤ roundedCrossingSquare r t := by
    cases hside : side with
    | below =>
        simp only [hside, OccupiedSide.areaSign_below, one_mul] at hp
        rcases hp with hp | hp
        · exfalso
          unfold roundedCrossingSquare at hp
          nlinarith [sq_nonneg r]
        · exact sub_nonneg.mp (le_of_not_gt hp.2)
    | above =>
        simp only [hside, OccupiedSide.areaSign_above, neg_mul, one_mul] at hp
        rcases hp with hp | hp
        · nlinarith
        · exfalso
          unfold roundedCrossingSquare at hp
          nlinarith [sq_nonneg r]
  have htBounds := abs_lt.mp ht
  have hs : |s| ≤ 3 * r := by
    rw [abs_le]
    unfold roundedCrossingSquare at hs2
    constructor <;>
      nlinarith [sq_abs t, sq_abs s, sq_nonneg (s - 3 * r),
        sq_nonneg (s + 3 * r)]
  exact ⟨ht, hs⟩
/-- Positive branch radius of the rounded crossing. -/
def roundedCrossingRadius (r t : ℝ) : ℝ :=
  Real.sqrt (roundedCrossingSquare r t)

lemma contDiff_roundedCrossingRadius {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (roundedCrossingRadius r) := by
  unfold roundedCrossingRadius
  apply ContDiff.sqrt (contDiff_roundedCrossingSquare r)
  intro t
  exact (roundedCrossingSquare_pos hr t).ne'

lemma roundedCrossingRadius_pos {r : ℝ} (hr : 0 < r) (t : ℝ) :
    0 < roundedCrossingRadius r t := by
  exact Real.sqrt_pos.2 (roundedCrossingSquare_pos hr t)

lemma roundedCrossingRadius_sq {r : ℝ} (hr : 0 < r) (t : ℝ) :
    roundedCrossingRadius r t ^ 2 = roundedCrossingSquare r t := by
  exact Real.sq_sqrt (roundedCrossingSquare_pos hr t).le

/-- Unit-scale profile controlling every rounded crossing. -/
def roundedCrossingProfile (t : ℝ) : ℝ := roundedCrossingRadius 1 t

lemma contDiff_roundedCrossingProfile :
    ContDiff ℝ ∞ roundedCrossingProfile := by
  exact contDiff_roundedCrossingRadius (by norm_num)

lemma oppositeCrossingBump_eq_scaled {r : ℝ} (hr : 0 < r) (t : ℝ) :
    oppositeCrossingBump r t = oppositeCrossingBump 1 (t / r) := by
  unfold oppositeCrossingBump
  congr 2
  field_simp [hr.ne']

lemma roundedCrossingSquare_eq_scaled {r : ℝ} (hr : 0 < r) (t : ℝ) :
    roundedCrossingSquare r t =
      r ^ 2 * roundedCrossingSquare 1 (t / r) := by
  rw [roundedCrossingSquare, roundedCrossingSquare,
    oppositeCrossingBump_eq_scaled hr]
  field_simp [hr.ne']

lemma roundedCrossingRadius_eq_scaled {r : ℝ} (hr : 0 < r) (t : ℝ) :
    roundedCrossingRadius r t = r * roundedCrossingProfile (t / r) := by
  rw [roundedCrossingRadius, roundedCrossingProfile, roundedCrossingRadius,
    roundedCrossingSquare_eq_scaled hr,
    Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, abs_of_pos hr]

lemma deriv_roundedCrossingRadius_eq_scaled
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    deriv (roundedCrossingRadius r) t =
      deriv roundedCrossingProfile (t / r) := by
  have hEq : roundedCrossingRadius r =
      fun y => r * roundedCrossingProfile (y / r) := by
    funext y
    exact roundedCrossingRadius_eq_scaled hr y
  rw [hEq]
  have hinner : HasDerivAt (fun y : ℝ => y / r) (1 / r) t :=
    (hasDerivAt_id t).div_const r
  have houter : HasDerivAt roundedCrossingProfile
      (deriv roundedCrossingProfile (t / r)) (t / r) :=
    (contDiff_roundedCrossingProfile.differentiable (by simp) _).hasDerivAt
  have hderiv := (houter.comp t hinner).const_mul r
  have hderiv' : HasDerivAt
      (fun y => r * roundedCrossingProfile (y / r))
      (r * (deriv roundedCrossingProfile (t / r) * (1 / r))) t := by
    simpa only [Function.comp_apply] using hderiv
  rw [hderiv'.deriv]
  field_simp [hr.ne']

/-- One fixed constant controls the speed of every rescaled branch radius. -/
theorem exists_roundedCrossingRadius_deriv_bound :
    ∃ K : NNReal, ∀ {r : ℝ}, 0 < r → ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (K : ℝ) := by
  obtain ⟨K, hK⟩ := exists_graphSpeed_bound_Icc
    (contDiff_roundedCrossingProfile.of_le (by simp)) (-2) 2
  refine ⟨K, ?_⟩
  intro r hr t ht
  rw [deriv_roundedCrossingRadius_eq_scaled hr]
  apply hK
  constructor
  · rw [le_div_iff₀ hr]
    linarith [ht.1]
  · rw [div_le_iff₀ hr]
    linarith [ht.2]


lemma roundedCrossingRadius_eq_abs_of_two_mul_le_abs
    {r t : ℝ} (hr : 0 < r) (ht : 2 * r ≤ |t|) :
    roundedCrossingRadius r t = |t| := by
  rw [roundedCrossingRadius,
    roundedCrossingSquare_eq_sq_of_two_mul_le_abs hr ht,
    Real.sqrt_sq_eq_abs]

/-- One of the two smooth boundary traces resolving the crossing. -/
def roundedOppositeCrossingTrace
    (c r : ℝ) (h : ℝ → ℝ) (σ t : ℝ) : PlanePoint :=
  let R := roundedCrossingRadius r t
  let X := (t + σ * R) / 2
  (c + X, h (c + X) + (σ * R - t) / 2)


@[simp] lemma oppositeCrossingT_roundedOppositeCrossingTrace
    (c r : ℝ) (h : ℝ → ℝ) (σ t : ℝ) :
    oppositeCrossingT c h
        (roundedOppositeCrossingTrace c r h σ t) = t := by
  unfold roundedOppositeCrossingTrace oppositeCrossingT
    oppositeCrossingNormal
  dsimp only
  ring
/-- The complete frontier of a rounded crossing lies on its two explicit
smooth branches. -/
theorem frontier_roundedOppositeCrossing_subset_trace_union
    (side : OccupiedSide) (c : ℝ) {r : ℝ} (hr : 0 < r)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    frontier {p | roundedOppositeCrossingValue side c r h p < 0} ⊆
      roundedOppositeCrossingTrace c r h (-1) '' univ ∪
        roundedOppositeCrossingTrace c r h 1 '' univ := by
  intro p hp
  have hp0 : roundedOppositeCrossingValue side c r h p = 0 :=
    frontier_lt_subset_eq
      (contDiff_roundedOppositeCrossingValue side c r hh).continuous
      continuous_const hp
  have hq :
      roundedCrossingSquare r (oppositeCrossingT c h p) =
        oppositeCrossingS c h p ^ 2 := by
    unfold roundedOppositeCrossingValue at hp0
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hp0).resolve_left
        (OccupiedSide.areaSign_ne_zero side))
  let t := oppositeCrossingT c h p
  let s := oppositeCrossingS c h p
  let R := roundedCrossingRadius r t
  have hR : R ^ 2 = roundedCrossingSquare r t :=
    roundedCrossingRadius_sq hr t
  have hsquare : R ^ 2 = s ^ 2 := by
    rw [hR]
    exact hq
  have hs : s = -R ∨ s = R := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare) with hRs | hRs
    · exact Or.inr hRs.symm
    · exact Or.inl (by linarith)
  have hx : p.1 = c + (t + s) / 2 := by
    dsimp only [t, s]
    unfold oppositeCrossingT oppositeCrossingS oppositeCrossingNormal
    ring
  have hy : p.2 = h p.1 + (s - t) / 2 := by
    dsimp only [t, s]
    unfold oppositeCrossingT oppositeCrossingS oppositeCrossingNormal
    ring
  rcases hs with hs | hs
  · left
    refine ⟨t, mem_univ t, ?_⟩
    apply Prod.ext
    · change c + (t + (-1 : ℝ) * R) / 2 = p.1
      rw [show (-1 : ℝ) * R = s by linarith]
      exact hx.symm
    · change
        h (c + (t + (-1 : ℝ) * R) / 2) +
            ((-1 : ℝ) * R - t) / 2 = p.2
      rw [show (-1 : ℝ) * R = s by linarith, ← hx]
      exact hy.symm
  · right
    refine ⟨t, mem_univ t, ?_⟩
    apply Prod.ext
    · change c + (t + (1 : ℝ) * R) / 2 = p.1
      rw [one_mul, ← hs]
      exact hx.symm
    · change
        h (c + (t + (1 : ℝ) * R) / 2) +
            ((1 : ℝ) * R - t) / 2 = p.2
      rw [one_mul, ← hs, ← hx]
      exact hy.symm

/-- Inside the rounded core, each frontier branch only uses parameters from
the shrinking interval `[-2r,2r]`. -/
theorem frontier_roundedOppositeCrossing_inter_core_subset_trace_union
    (side : OccupiedSide) (c : ℝ) {r : ℝ} (hr : 0 < r)
    {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    frontier {p | roundedOppositeCrossingValue side c r h p < 0} ∩
        roundedOppositeCrossingCore c h r ⊆
      roundedOppositeCrossingTrace c r h (-1) '' Icc (-2 * r) (2 * r) ∪
        roundedOppositeCrossingTrace c r h 1 '' Icc (-2 * r) (2 * r) := by
  intro p hp
  have htrace :=
    frontier_roundedOppositeCrossing_subset_trace_union side c hr hh hp.1
  rcases htrace with ⟨t, _ht, rfl⟩ | ⟨t, _ht, rfl⟩
  · left
    refine ⟨t, ?_, rfl⟩
    have ht : |t| < 2 * r := by
      simpa only [oppositeCrossingT_roundedOppositeCrossingTrace] using hp.2.1
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]
  · right
    refine ⟨t, ?_, rfl⟩
    have ht : |t| < 2 * r := by
      simpa only [oppositeCrossingT_roundedOppositeCrossingTrace] using hp.2.1
    constructor <;> linarith [(abs_lt.mp ht).1, (abs_lt.mp ht).2]


/-- Euclidean realization of a general planar parametrized curve. -/
def euclideanPlaneParam (x y : ℝ → ℝ) (t : ℝ) : EuclideanPlane :=
  planeEuclideanHomeomorph (x t, y t)

lemma euclideanPlaneParam_eq (x y : ℝ → ℝ) :
    euclideanPlaneParam x y =
      tangentComplexEquiv.symm ∘
        (fun t : ℝ => Complex.ofRealCLM (y t) + x t • Complex.I) := by
  funext t
  apply tangentComplexEquiv.injective
  apply Complex.ext <;> simp [euclideanPlaneParam]

lemma hasDerivAt_planeComplexParam
    {x y : ℝ → ℝ} {t : ℝ} (hx : DifferentiableAt ℝ x t)
    (hy : DifferentiableAt ℝ y t) :
    HasDerivAt
      (fun s : ℝ => Complex.ofRealCLM (y s) + x s • Complex.I)
      (Complex.ofRealCLM (deriv y t) + deriv x t • Complex.I) t := by
  exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hy.hasDerivAt
    |>.add (hx.hasDerivAt.smul_const Complex.I)

lemma norm_planeComplexParam_deriv
    {x y : ℝ → ℝ} {t : ℝ} :
    ‖Complex.ofRealCLM (deriv y t) + deriv x t • Complex.I‖ =
      Real.sqrt ((deriv x t) ^ 2 + (deriv y t) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

lemma lipschitzOnWith_euclideanPlaneParam_Icc
    {x y : ℝ → ℝ} (hx : Differentiable ℝ x) (hy : Differentiable ℝ y)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc a b,
      Real.sqrt ((deriv x t) ^ 2 + (deriv y t) ^ 2) ≤ (K : ℝ)) :
    LipschitzOnWith K (euclideanPlaneParam x y) (Icc a b) := by
  rw [euclideanPlaneParam_eq]
  simpa only [one_mul] using
    LipschitzWith.comp_lipschitzOnWith
      tangentComplexEquiv.symm.isometry.lipschitz
      (by
        refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
          (f' := fun t =>
            Complex.ofRealCLM (deriv y t) + deriv x t • Complex.I)
          (convex_Icc a b) ?_ ?_
        · intro t ht
          exact (hasDerivAt_planeComplexParam (hx t) (hy t)).hasDerivWithinAt
        · intro t ht
          rw [← NNReal.coe_le_coe, coe_nnnorm,
            norm_planeComplexParam_deriv]
          exact hK t ht)

theorem hausdorffMeasure_euclideanPlaneParam_Icc_le
    {x y : ℝ → ℝ} (hx : Differentiable ℝ x) (hy : Differentiable ℝ y)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc a b,
      Real.sqrt ((deriv x t) ^ 2 + (deriv y t) ^ 2) ≤ (K : ℝ)) :
    (μH[1] : Measure EuclideanPlane)
        (planeEuclideanHomeomorph ''
          ((fun t : ℝ => (x t, y t)) '' Icc a b)) ≤
      (K : ENNReal) * ENNReal.ofReal (b - a) := by
  rw [image_image]
  change (μH[1] : Measure EuclideanPlane)
      (euclideanPlaneParam x y '' Icc a b) ≤ _
  simpa [ENNReal.rpow_one, hausdorffMeasure_real, Real.volume_Icc] using
    (lipschitzOnWith_euclideanPlaneParam_Icc hx hy hK).hausdorffMeasure_image_le
      (d := (1 : ℝ)) (by norm_num)

theorem weightedTraceCost_planeParam_Icc_le_global
    {lam : ℝ} (hlam : 1 < lam)
    {x y : ℝ → ℝ} (hx : Differentiable ℝ x) (hy : Differentiable ℝ y)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc a b,
      Real.sqrt ((deriv x t) ^ 2 + (deriv y t) ^ 2) ≤ (K : ℝ)) :
    weightedTraceCost lam
        ((fun t : ℝ => (x t, y t)) '' Icc a b) ≤
      ENNReal.ofReal lam * (K : ENNReal) * ENNReal.ofReal (b - a) := by
  calc
    weightedTraceCost lam
        ((fun t : ℝ => (x t, y t)) '' Icc a b) ≤
        ENNReal.ofReal lam *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph ''
              ((fun t : ℝ => (x t, y t)) '' Icc a b)) :=
      weightedTraceCost_le_density_mul_hausdorff hlam _
    _ ≤ ENNReal.ofReal lam *
          ((K : ENNReal) * ENNReal.ofReal (b - a)) := by
      gcongr
      exact hausdorffMeasure_euclideanPlaneParam_Icc_le hx hy hK
    _ = _ := by rw [mul_assoc]


/-- Horizontal and normal components of a rounded crossing branch. -/
def roundedOppositeCrossingTraceX (c r σ t : ℝ) : ℝ :=
  c + (t + σ * roundedCrossingRadius r t) / 2

def roundedOppositeCrossingTraceZ (r σ t : ℝ) : ℝ :=
  (σ * roundedCrossingRadius r t - t) / 2

def roundedOppositeCrossingTraceY
    (c r : ℝ) (h : ℝ → ℝ) (σ t : ℝ) : ℝ :=
  h (roundedOppositeCrossingTraceX c r σ t) +
    roundedOppositeCrossingTraceZ r σ t

lemma roundedOppositeCrossingTrace_eq
    (c r : ℝ) (h : ℝ → ℝ) (σ : ℝ) :
    roundedOppositeCrossingTrace c r h σ =
      fun t => (roundedOppositeCrossingTraceX c r σ t,
        roundedOppositeCrossingTraceY c r h σ t) := by
  funext t
  rfl

lemma contDiff_roundedOppositeCrossingTraceX
    (c : ℝ) {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    ContDiff ℝ ∞ (roundedOppositeCrossingTraceX c r σ) := by
  unfold roundedOppositeCrossingTraceX
  exact contDiff_const.add
    ((contDiff_id.add
      (contDiff_const.mul (contDiff_roundedCrossingRadius hr))).div_const 2)

lemma contDiff_roundedOppositeCrossingTraceZ
    {r : ℝ} (hr : 0 < r) (σ : ℝ) :
    ContDiff ℝ ∞ (roundedOppositeCrossingTraceZ r σ) := by
  unfold roundedOppositeCrossingTraceZ
  exact ((contDiff_const.mul (contDiff_roundedCrossingRadius hr)).sub
    contDiff_id).div_const 2

lemma contDiff_roundedOppositeCrossingTraceY
    (c : ℝ) {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (σ : ℝ) :
    ContDiff ℝ ∞ (roundedOppositeCrossingTraceY c r h σ) := by
  unfold roundedOppositeCrossingTraceY
  exact (hh.comp (contDiff_roundedOppositeCrossingTraceX c hr σ)).add
    (contDiff_roundedOppositeCrossingTraceZ hr σ)

lemma deriv_roundedOppositeCrossingTraceX
    (c : ℝ) {r : ℝ} (hr : 0 < r) (σ t : ℝ) :
    deriv (roundedOppositeCrossingTraceX c r σ) t =
      (1 + σ * deriv (roundedCrossingRadius r) t) / 2 := by
  have hR := (contDiff_roundedCrossingRadius hr).differentiable
    (by simp) t |>.hasDerivAt
  have hderiv :=
    ((hasDerivAt_id t).add (hR.const_mul σ)).div_const 2 |>.const_add c
  exact hderiv.deriv

lemma deriv_roundedOppositeCrossingTraceZ
    {r : ℝ} (hr : 0 < r) (σ t : ℝ) :
    deriv (roundedOppositeCrossingTraceZ r σ) t =
      (σ * deriv (roundedCrossingRadius r) t - 1) / 2 := by
  have hR := (contDiff_roundedCrossingRadius hr).differentiable
    (by simp) t |>.hasDerivAt
  have hderiv := ((hR.const_mul σ).sub (hasDerivAt_id t)).div_const 2
  exact hderiv.deriv

lemma deriv_roundedOppositeCrossingTraceY
    (c : ℝ) {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (σ t : ℝ) :
    deriv (roundedOppositeCrossingTraceY c r h σ) t =
      deriv h (roundedOppositeCrossingTraceX c r σ t) *
          ((1 + σ * deriv (roundedCrossingRadius r) t) / 2) +
        (σ * deriv (roundedCrossingRadius r) t - 1) / 2 := by
  let x := roundedOppositeCrossingTraceX c r σ
  let z := roundedOppositeCrossingTraceZ r σ
  have hx := (contDiff_roundedOppositeCrossingTraceX c hr σ).differentiable
    (by simp) t |>.hasDerivAt
  have hh' := (hh.differentiable (by simp) (x t)).hasDerivAt
  have hz := (contDiff_roundedOppositeCrossingTraceZ hr σ).differentiable
    (by simp) t |>.hasDerivAt
  have hderiv : HasDerivAt
      (fun u => h (x u) + z u)
      (deriv h (x t) * deriv x t + deriv z t) t :=
    (hh'.comp t hx).add hz
  have hEq : roundedOppositeCrossingTraceY c r h σ =
      fun u => h (x u) + z u := rfl
  rw [hEq, hderiv.deriv, deriv_roundedOppositeCrossingTraceX c hr,
    deriv_roundedOppositeCrossingTraceZ hr]

lemma roundedCrossingRadius_le_three_mul
    {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : t ∈ Icc (-2 * r) (2 * r)) :
    roundedCrossingRadius r t ≤ 3 * r := by
  have htAbs : |t| ≤ 2 * r := abs_le.mpr (by
    constructor <;> linarith [ht.1, ht.2])
  have ht2 : t ^ 2 ≤ 4 * r ^ 2 := by
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg t) (by positivity : 0 ≤ 2 * r)).2 htAbs
    nlinarith [sq_abs t]
  have hb := (oppositeCrossingBump_mem_Icc r t).2
  have hR2 := roundedCrossingRadius_sq hr t
  have hR0 := (roundedCrossingRadius_pos hr t).le
  apply (sq_le_sq₀ hR0 (by positivity : 0 ≤ 3 * r)).mp
  unfold roundedCrossingSquare at hR2
  nlinarith [sq_nonneg r]

lemma roundedOppositeCrossingTraceX_mem_Icc
    (c : ℝ) {r : ℝ} (hr : 0 < r) {σ t : ℝ} (hσ : |σ| ≤ 1)
    (ht : t ∈ Icc (-2 * r) (2 * r)) :
    roundedOppositeCrossingTraceX c r σ t ∈
      Icc (c - 3 * r) (c + 3 * r) := by
  have htAbs : |t| ≤ 2 * r := abs_le.mpr (by
    constructor <;> linarith [ht.1, ht.2])
  have hR := roundedCrossingRadius_le_three_mul hr ht
  have hR0 := (roundedCrossingRadius_pos hr t).le
  have hσR : |σ * roundedCrossingRadius r t| ≤ 3 * r := by
    rw [abs_mul, abs_of_nonneg hR0]
    calc
      |σ| * roundedCrossingRadius r t ≤
          1 * roundedCrossingRadius r t :=
        mul_le_mul_of_nonneg_right hσ hR0
      _ ≤ 3 * r := by simpa using hR
  unfold roundedOppositeCrossingTraceX
  rw [mem_Icc]
  constructor <;>
    nlinarith [(abs_le.mp htAbs).1, (abs_le.mp htAbs).2,
      (abs_le.mp hσR).1, (abs_le.mp hσR).2]

/-- A radius-speed bound and a slope bound for the straightening graph give
a uniform speed bound for both rounded crossing branches. -/
theorem roundedOppositeCrossingTrace_speed_le
    (c : ℝ) {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (σ : ℝ) (hσ : |σ| ≤ 1)
    (Kr Mh : NNReal)
    (hKr : ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (Kr : ℝ))
    (hMh : ∀ x ∈ Icc (c - 3 * r) (c + 3 * r),
      |deriv h x| ≤ (Mh : ℝ)) :
    ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt
          ((deriv (roundedOppositeCrossingTraceX c r σ) t) ^ 2 +
            (deriv (roundedOppositeCrossingTraceY c r h σ) t) ^ 2) ≤
        1 + ((Mh : ℝ) + 2) * (1 + (Kr : ℝ)) := by
  intro t ht
  let dR := deriv (roundedCrossingRadius r) t
  let dx := deriv (roundedOppositeCrossingTraceX c r σ) t
  let dz := deriv (roundedOppositeCrossingTraceZ r σ) t
  let dy := deriv (roundedOppositeCrossingTraceY c r h σ) t
  have hKr' := hKr t ht
  have hdR : |dR| ≤ (Kr : ℝ) := by
    have hsqrt0 : 0 ≤ Real.sqrt (1 + dR ^ 2) := Real.sqrt_nonneg _
    have hsqrt2 : Real.sqrt (1 + dR ^ 2) ^ 2 = 1 + dR ^ 2 :=
      Real.sq_sqrt (by positivity)
    nlinarith [sq_abs dR]
  have hdxEq : dx = (1 + σ * dR) / 2 := by
    exact deriv_roundedOppositeCrossingTraceX c hr σ t
  have hdzEq : dz = (σ * dR - 1) / 2 := by
    exact deriv_roundedOppositeCrossingTraceZ hr σ t
  have hσdR : |σ * dR| ≤ (Kr : ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul hσ hdR (abs_nonneg _) (by positivity)).trans_eq
      (one_mul _)
  have hdx : |dx| ≤ 1 + (Kr : ℝ) := by
    have hnum : |1 + σ * dR| ≤ 1 + (Kr : ℝ) :=
      (abs_add_le 1 (σ * dR)).trans (by
        rw [abs_one]
        linarith)
    rw [hdxEq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hdz : |dz| ≤ 1 + (Kr : ℝ) := by
    have hnum : |σ * dR - 1| ≤ (Kr : ℝ) + 1 :=
      (abs_sub_le (σ * dR) 0 1).trans (by
        simpa only [sub_zero, abs_zero, zero_sub, abs_neg, abs_one] using
          add_le_add hσdR (le_refl (1 : ℝ)))
    rw [hdzEq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hxmem := roundedOppositeCrossingTraceX_mem_Icc c hr hσ ht
  have hhSlope := hMh _ hxmem
  have hdyEq :
      dy = deriv h (roundedOppositeCrossingTraceX c r σ t) * dx + dz := by
    dsimp only [dy, dx, dz]
    rw [deriv_roundedOppositeCrossingTraceY c hr hh σ t,
      deriv_roundedOppositeCrossingTraceX c hr,
      deriv_roundedOppositeCrossingTraceZ hr]
  have hdy :
      |dy| ≤ ((Mh : ℝ) + 1) * (1 + (Kr : ℝ)) := by
    rw [hdyEq]
    calc
      |deriv h (roundedOppositeCrossingTraceX c r σ t) * dx + dz| ≤
          |deriv h (roundedOppositeCrossingTraceX c r σ t)| * |dx| +
            |dz| := by
        simpa only [abs_mul] using
          abs_add_le
            (deriv h (roundedOppositeCrossingTraceX c r σ t) * dx) dz
      _ ≤ (Mh : ℝ) * (1 + (Kr : ℝ)) + (1 + (Kr : ℝ)) := by
        gcongr
      _ = ((Mh : ℝ) + 1) * (1 + (Kr : ℝ)) := by ring
  have hsqrt0 : 0 ≤ Real.sqrt (dx ^ 2 + dy ^ 2) := Real.sqrt_nonneg _
  have hsqrt2 : Real.sqrt (dx ^ 2 + dy ^ 2) ^ 2 = dx ^ 2 + dy ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hsum : Real.sqrt (dx ^ 2 + dy ^ 2) ≤ |dx| + |dy| := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [sq_abs dx, sq_abs dy,
        mul_nonneg (abs_nonneg dx) (abs_nonneg dy)]
  exact hsum.trans (by
    have hMh0 : 0 ≤ (Mh : ℝ) := by positivity
    have hKr0 : 0 ≤ (Kr : ℝ) := by positivity
    calc
      |dx| + |dy| ≤
          (1 + (Kr : ℝ)) + ((Mh : ℝ) + 1) * (1 + (Kr : ℝ)) :=
        add_le_add hdx hdy
      _ ≤ 1 + ((Mh : ℝ) + 2) * (1 + (Kr : ℝ)) := by nlinarith)

def roundedOppositeCrossingTraceSpeedConstant (Kr Mh : NNReal) : NNReal :=
  ⟨1 + ((Mh : ℝ) + 2) * (1 + (Kr : ℝ)), by positivity⟩

theorem weightedTraceCost_roundedOppositeCrossingTrace_Icc_le
    {lam : ℝ} (hlam : 1 < lam) (c : ℝ)
    {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (σ : ℝ) (hσ : |σ| ≤ 1) (Kr Mh : NNReal)
    (hKr : ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (Kr : ℝ))
    (hMh : ∀ x ∈ Icc (c - 3 * r) (c + 3 * r),
      |deriv h x| ≤ (Mh : ℝ)) :
    weightedTraceCost lam
        (roundedOppositeCrossingTrace c r h σ ''
          Icc (-2 * r) (2 * r)) ≤
      ENNReal.ofReal lam *
        (roundedOppositeCrossingTraceSpeedConstant Kr Mh : ENNReal) *
          ENNReal.ofReal (4 * r) := by
  rw [roundedOppositeCrossingTrace_eq]
  have hspeed :=
    roundedOppositeCrossingTrace_speed_le c hr hh σ hσ Kr Mh hKr hMh
  have hcost := weightedTraceCost_planeParam_Icc_le_global hlam
    ((contDiff_roundedOppositeCrossingTraceX c hr σ).differentiable (by simp))
    ((contDiff_roundedOppositeCrossingTraceY c hr hh σ).differentiable (by simp))
    (K := roundedOppositeCrossingTraceSpeedConstant Kr Mh) hspeed
  simpa only [roundedOppositeCrossingTraceSpeedConstant,
    show 2 * r - -2 * r = 4 * r by ring] using hcost

/-- The complete altered frontier in the rounded core has an explicit
`O(r)` density-weighted bound. -/
theorem weightedTraceCost_frontier_roundedOppositeCrossing_inter_core_le
    {lam : ℝ} (hlam : 1 < lam) (side : OccupiedSide) (c : ℝ)
    {r : ℝ} (hr : 0 < r) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (Kr Mh : NNReal)
    (hKr : ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (Kr : ℝ))
    (hMh : ∀ x ∈ Icc (c - 3 * r) (c + 3 * r),
      |deriv h x| ≤ (Mh : ℝ)) :
    weightedTraceCost lam
        (frontier {p | roundedOppositeCrossingValue side c r h p < 0} ∩
          roundedOppositeCrossingCore c h r) ≤
      (ENNReal.ofReal lam *
          (roundedOppositeCrossingTraceSpeedConstant Kr Mh : ENNReal) *
            ENNReal.ofReal (4 * r)) +
        (ENNReal.ofReal lam *
          (roundedOppositeCrossingTraceSpeedConstant Kr Mh : ENNReal) *
            ENNReal.ofReal (4 * r)) := by
  exact (weightedTraceCost_mono lam
    (frontier_roundedOppositeCrossing_inter_core_subset_trace_union
      side c hr hh)).trans
    ((weightedTraceCost_union_le lam _ _).trans
      (add_le_add
        (weightedTraceCost_roundedOppositeCrossingTrace_Icc_le
          hlam c hr hh (-1) (by norm_num) Kr Mh hKr hMh)
        (weightedTraceCost_roundedOppositeCrossingTrace_Icc_le
          hlam c hr hh 1 (by norm_num) Kr Mh hKr hMh)))
/-- Replacing the two incident graphs by their common connector only changes
an opposite-side switch inside the closed graph band over the connector slab. -/
theorem filledOppositeVerticalGraphSwitch_connectGraphs_symmDiff_subset_closedGraphBand
    (P : GraphPatch) {a b c : ℝ} {f g : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) :
    filledOppositeVerticalGraphSwitch P (connectGraphs a b f g)
          (connectGraphs a b f g) c ∆
        filledOppositeVerticalGraphSwitch P f g c ⊆
      closedGraphBand (connectGraphs a b f g)
        (fun x => if x ≤ c then f x else g x) (Icc a b) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hab : a < b := hac.trans hcb
  cases hside : P.side with
  | below =>
      simp only [filledOppositeVerticalGraphSwitch,
        oppositeOccupiedGraphDomain, GraphPatch.occupiedGraphDomain,
        hside, Set.mem_symmDiff, Set.mem_union, Set.mem_inter_iff,
        Set.mem_ofPred_eq] at hp
      change x ∈ Icc a b ∧
        y ∈ Icc
          (min (connectGraphs a b f g x) (if x ≤ c then f x else g x))
          (max (connectGraphs a b f g x) (if x ≤ c then f x else g x))
      rcases lt_trichotomy x c with hxc | hxc | hcx
      · have hnotcx : ¬c < x := not_lt_of_ge hxc.le
        simp only [hxc, hnotcx, true_and, false_and, or_false] at hp
        have hxa : a ≤ x := by
          by_contra hnot
          have hxale : x ≤ a := le_of_not_ge hnot
          have heq := connectGraphs_eq_left (f := f) (g := g) hab hxale
          rw [heq] at hp
          exact hp.elim (fun q => q.2 q.1) (fun q => q.2 q.1)
        have hxb : x ≤ b := hxc.le.trans hcb.le
        refine ⟨⟨hxa, hxb⟩, ?_⟩
        rw [if_pos hxc.le]
        rcases hp with hp | hp
        · exact ⟨(min_le_right _ _).trans (le_of_not_gt hp.2),
            hp.1.le.trans (le_max_left _ _)⟩
        · exact ⟨(min_le_left _ _).trans (le_of_not_gt hp.2),
            hp.1.le.trans (le_max_right _ _)⟩
      · subst x
        simp only [lt_self_iff_false, false_and, false_or] at hp
      · have hnotxc : ¬x < c := not_lt_of_ge hcx.le
        simp only [hcx, hnotxc, true_and, false_and, false_or] at hp
        have hxa : a ≤ x := hac.le.trans hcx.le
        have hxb : x ≤ b := by
          by_contra hnot
          have hble : b ≤ x := le_of_not_ge hnot
          have heq := connectGraphs_eq_right (f := f) (g := g) hab hble
          rw [heq] at hp
          exact hp.elim (fun q => q.2 q.1) (fun q => q.2 q.1)
        refine ⟨⟨hxa, hxb⟩, ?_⟩
        rw [if_neg (not_le_of_gt hcx)]
        rcases hp with hp | hp
        · exact ⟨(min_le_left _ _).trans hp.1.le,
            (le_of_not_gt hp.2).trans (le_max_right _ _)⟩
        · exact ⟨(min_le_right _ _).trans hp.1.le,
            (le_of_not_gt hp.2).trans (le_max_left _ _)⟩
  | above =>
      simp only [filledOppositeVerticalGraphSwitch,
        oppositeOccupiedGraphDomain, GraphPatch.occupiedGraphDomain,
        hside, Set.mem_symmDiff, Set.mem_union, Set.mem_inter_iff,
        Set.mem_ofPred_eq] at hp
      change x ∈ Icc a b ∧
        y ∈ Icc
          (min (connectGraphs a b f g x) (if x ≤ c then f x else g x))
          (max (connectGraphs a b f g x) (if x ≤ c then f x else g x))
      rcases lt_trichotomy x c with hxc | hxc | hcx
      · have hnotcx : ¬c < x := not_lt_of_ge hxc.le
        simp only [hxc, hnotcx, true_and, false_and, or_false] at hp
        have hxa : a ≤ x := by
          by_contra hnot
          have hxale : x ≤ a := le_of_not_ge hnot
          have heq := connectGraphs_eq_left (f := f) (g := g) hab hxale
          rw [heq] at hp
          exact hp.elim (fun q => q.2 q.1) (fun q => q.2 q.1)
        have hxb : x ≤ b := hxc.le.trans hcb.le
        refine ⟨⟨hxa, hxb⟩, ?_⟩
        rw [if_pos hxc.le]
        rcases hp with hp | hp
        · exact ⟨(min_le_left _ _).trans hp.1.le,
            (le_of_not_gt hp.2).trans (le_max_right _ _)⟩
        · exact ⟨(min_le_right _ _).trans hp.1.le,
            (le_of_not_gt hp.2).trans (le_max_left _ _)⟩
      · subst x
        simp only [lt_self_iff_false, false_and, false_or] at hp
      · have hnotxc : ¬x < c := not_lt_of_ge hcx.le
        simp only [hcx, hnotxc, true_and, false_and, false_or] at hp
        have hxa : a ≤ x := hac.le.trans hcx.le
        have hxb : x ≤ b := by
          by_contra hnot
          have hble : b ≤ x := le_of_not_ge hnot
          have heq := connectGraphs_eq_right (f := f) (g := g) hab hble
          rw [heq] at hp
          exact hp.elim (fun q => q.2 q.1) (fun q => q.2 q.1)
        refine ⟨⟨hxa, hxb⟩, ?_⟩
        rw [if_neg (not_le_of_gt hcx)]
        rcases hp with hp | hp
        · exact ⟨(min_le_right _ _).trans (le_of_not_gt hp.2),
            hp.1.le.trans (le_max_left _ _)⟩
        · exact ⟨(min_le_left _ _).trans (le_of_not_gt hp.2),
            hp.1.le.trans (le_max_right _ _)⟩


theorem roundedOppositeCrossing_symmDiff_filledSwitch_subset
    (P : GraphPatch) {a b c r : ℝ} (hr : 0 < r)
    {f g : ℝ → ℝ} (hac : a < c) (hcb : c < b) :
    {p | roundedOppositeCrossingValue P.side c r
          (connectGraphs a b f g) p < 0} ∆
        filledOppositeVerticalGraphSwitch P f g c ⊆
      roundedOppositeCrossingCore c (connectGraphs a b f g) r ∪
        closedGraphBand (connectGraphs a b f g)
          (fun x => if x ≤ c then f x else g x) (Icc a b) := by
  let A := {p | roundedOppositeCrossingValue P.side c r
    (connectGraphs a b f g) p < 0}
  let B := filledOppositeVerticalGraphSwitch P
    (connectGraphs a b f g) (connectGraphs a b f g) c
  let C := filledOppositeVerticalGraphSwitch P f g c
  have htriangle : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
    intro p hp
    simp only [Set.mem_symmDiff, Set.mem_union]
    simp only [Set.mem_symmDiff] at hp
    rcases hp with ⟨hpA, hpC⟩ | ⟨hpC, hpA⟩
    · by_cases hpB : p ∈ B
      · right
        exact Or.inl ⟨hpB, hpC⟩
      · left
        exact Or.inl ⟨hpA, hpB⟩
    · by_cases hpB : p ∈ B
      · left
        exact Or.inr ⟨hpB, hpA⟩
      · right
        exact Or.inr ⟨hpC, hpB⟩
  apply htriangle.trans
  apply Set.union_subset_union
  · simpa only [A, B,
      filledOppositeVerticalGraphSwitch_eq_crossingSublevel] using
      (roundedOppositeCrossing_symmDiff_crossing_subset_core
        P.side c hr (connectGraphs a b f g))
  · exact filledOppositeVerticalGraphSwitch_connectGraphs_symmDiff_subset_closedGraphBand
      P hac hcb

lemma roundedOppositeCrossingCore_coordinate_bounds
    {c r : ℝ} {h : ℝ → ℝ} {p : PlanePoint}
    (hp : p ∈ roundedOppositeCrossingCore c h r) :
    |p.1 - c| < 3 * r ∧ |p.2 - h p.1| < 3 * r := by
  have ht := abs_lt.mp hp.1
  have hs := abs_le.mp hp.2
  change -(2 * r) < (p.1 - c) - (p.2 - h p.1) ∧
    (p.1 - c) - (p.2 - h p.1) < 2 * r at ht
  change -(3 * r) ≤ (p.1 - c) + (p.2 - h p.1) ∧
    (p.1 - c) + (p.2 - h p.1) ≤ 3 * r at hs
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]
  · rw [abs_lt]
    constructor <;> nlinarith [ht.1, ht.2, hs.1, hs.2]

/-- The complete rounded coordinate core for shrinking graph connectors lies
eventually in every prescribed junction ball. -/
theorem eventually_symmetricConnector_roundedOppositeCrossingCore_subset_junctionBall
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c R rho : ℝ} (hR : 0 < R) (hfg : f c = g c) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      let r := symmetricConnectorRadius R n
      roundedOppositeCrossingCore c
          (connectGraphs (c - 3 * r) (c + 3 * r) f g) r ⊆
        junctionBall (c, f c) rho := by
  let eta := rho / 4
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hfNear : f ⁻¹' ball (f c) eta ∈ 𝓝 c :=
    hf.continuousAt (ball_mem_nhds _ heta)
  have hgNear : g ⁻¹' ball (f c) eta ∈ 𝓝 c := by
    rw [hfg]
    exact hg.continuousAt (ball_mem_nhds (g c) heta)
  obtain ⟨delta, hdelta, hdeltaSub⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem hfNear hgNear)
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        symmetricConnectorRadius R n < min (delta / 3) (eta / 3) :=
    (tendsto_symmetricConnectorRadius_zero R).eventually
      (Iio_mem_nhds (lt_min (by positivity) (by positivity)))
  filter_upwards [hevent] with n hn
  dsimp only
  let r := symmetricConnectorRadius R n
  have hr : 0 < r := symmetricConnectorRadius_pos hR n
  have hrDelta : 3 * r < delta := by
    dsimp only [r]
    nlinarith [hn.trans_le (min_le_left _ _)]
  have hrEta : 3 * r < eta := by
    dsimp only [r]
    nlinarith [hn.trans_le (min_le_right _ _)]
  intro p hp
  have hcoord := roundedOppositeCrossingCore_coordinate_bounds hp
  have hxDelta : p.1 ∈ ball c delta := by
    rw [mem_ball, Real.dist_eq]
    exact hcoord.1.trans hrDelta
  have hvalues := hdeltaSub hxDelta
  have hfDist : dist (f p.1) (f c) < eta := mem_ball.mp hvalues.1
  have hgDist : dist (g p.1) (f c) < eta := mem_ball.mp hvalues.2
  rw [Real.dist_eq, abs_lt] at hfDist hgDist
  let h := connectGraphs (c - 3 * r) (c + 3 * r) f g
  have hconn := connectGraphs_mem_Icc
    (c - 3 * r) (c + 3 * r) f g p.1
  have hLower : f c - eta < h p.1 :=
    (lt_min (by linarith [hfDist.1]) (by linarith [hgDist.1])).trans_le
      hconn.1
  have hUpper : h p.1 < f c + eta :=
    hconn.2.trans_lt
      (max_lt (by linarith [hfDist.2]) (by linarith [hgDist.2]))
  have hz := abs_lt.mp hcoord.2
  have hyDist : dist p.2 (f c) < 2 * eta := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> nlinarith [hz.1, hz.2]
  have hxDist : dist p.1 c < eta := by
    rw [Real.dist_eq]
    exact hcoord.1.trans hrEta
  change dist (planeEuclideanHomeomorph p)
      (planeEuclideanHomeomorph (c, f c)) ≤ rho
  exact (dist_planeEuclideanHomeomorph_le_coordinate_sum
    p.1 p.2 c (f c)).trans (by
      dsimp only [eta] at hxDist hyDist
      linarith)

theorem eventually_symmetricTripleConnector_closedGraphBand_subset_junctionBall
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c R rho : ℝ} (hfg : f c = g c) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      let r := symmetricConnectorRadius R n
      closedGraphBand
          (connectGraphs (c - 3 * r) (c + 3 * r) f g)
          (fun x => if x ≤ c then f x else g x)
          (Icc (c - 3 * r) (c + 3 * r)) ⊆
        junctionBall (c, f c) rho := by
  have hband :=
    eventually_symmetricConnector_closedGraphBand_subset_junctionBall
      hf hg (R := 3 * R) hfg hrho
  simpa only [symmetricConnectorRadius,
    show ∀ n : ℕ, 3 * R * junctionRadius n =
        3 * (R * junctionRadius n) by intro n; ring] using hband

theorem eventually_roundedOppositeCrossing_symmDiff_filledSwitch_subset_junctionBall
    (P : GraphPatch) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    {c R rho : ℝ} (hR : 0 < R) (hfg : f c = g c) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      let r := symmetricConnectorRadius R n
      {p | roundedOppositeCrossingValue P.side c r
            (connectGraphs (c - 3 * r) (c + 3 * r) f g) p < 0} ∆
          filledOppositeVerticalGraphSwitch P f g c ⊆
        junctionBall (c, f c) rho := by
  have hcore :=
    eventually_symmetricConnector_roundedOppositeCrossingCore_subset_junctionBall
      hf hg hR hfg hrho
  have hband :=
    eventually_symmetricTripleConnector_closedGraphBand_subset_junctionBall
      hf hg (R := R) hfg hrho
  filter_upwards [hcore, hband] with n hnCore hnBand
  dsimp only at hnCore hnBand ⊢
  let r := symmetricConnectorRadius R n
  have hr : 0 < r := symmetricConnectorRadius_pos hR n
  have hsubset :=
    roundedOppositeCrossing_symmDiff_filledSwitch_subset
      (f := f) (g := g) P hr
      (show c - 3 * r < c by linarith)
      (show c < c + 3 * r by linarith)
  exact hsubset.trans (union_subset hnCore hnBand)


/-- In the connector mismatch band, every rounded frontier point outside the
actual rounding core lies on the connector graph; the unbounded cut-line
branch meets the band only at the common incident point. -/
theorem frontier_roundedOppositeCrossing_inter_connectorBand_subset
    (P : GraphPatch) {a b c r : ℝ} (hr : 0 < r)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : f c = g c) :
    let h := connectGraphs a b f g
    frontier {p | roundedOppositeCrossingValue P.side c r h p < 0} ∩
        closedGraphBand h (fun x => if x ≤ c then f x else g x) (Icc a b) ⊆
      (frontier {p | roundedOppositeCrossingValue P.side c r h p < 0} ∩
          roundedOppositeCrossingCore c h r) ∪
        (fun x : ℝ => (x, h x)) '' Icc a b := by
  dsimp only
  let h := connectGraphs a b f g
  have hh : ContDiff ℝ ∞ h := contDiff_connectGraphs hf hg
  have hhCenter : h c = f c := by
    have hvalue : h c ∈ Icc (min (f c) (g c)) (max (f c) (g c)) := by
      exact connectGraphs_mem_Icc a b f g c
    have hhg : h c = g c := by
      rw [hfg, min_self, max_self] at hvalue
      exact le_antisymm hvalue.2 hvalue.1
    exact hhg.trans hfg.symm
  intro p hp
  by_cases hpCore : p ∈ roundedOppositeCrossingCore c h r
  · exact Or.inl ⟨hp.1, hpCore⟩
  · right
    have hp0 : roundedOppositeCrossingValue P.side c r h p = 0 :=
      frontier_lt_subset_eq
        (contDiff_roundedOppositeCrossingValue P.side c r hh).continuous
        continuous_const hp.1
    have hq :
        roundedCrossingSquare r (oppositeCrossingT c h p) =
          oppositeCrossingS c h p ^ 2 := by
      unfold roundedOppositeCrossingValue at hp0
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hp0).resolve_left
          (OccupiedSide.areaSign_ne_zero P.side))
    let t := oppositeCrossingT c h p
    let s := oppositeCrossingS c h p
    have htExterior : 2 * r ≤ |t| := by
      by_contra hnot
      have ht : |t| < 2 * r := lt_of_not_ge hnot
      have htBounds := abs_lt.mp ht
      have ht2 : t ^ 2 < 4 * r ^ 2 := by
        nlinarith [sq_abs t]
      have hb := (oppositeCrossingBump_mem_Icc r t).2
      have hs2 : s ^ 2 < 5 * r ^ 2 := by
        rw [← hq]
        unfold roundedCrossingSquare
        nlinarith [sq_nonneg r]
      have hs : |s| ≤ 3 * r := by
        apply (sq_le_sq₀ (abs_nonneg s) (by positivity : 0 ≤ 3 * r)).mp
        rw [sq_abs]
        nlinarith
      exact hpCore ⟨ht, hs⟩
    have hsquare : t ^ 2 = s ^ 2 := by
      rw [← hq, roundedCrossingSquare_eq_sq_of_two_mul_le_abs hr htExterior]
    have hzero : p.1 = c ∨ p.2 = h p.1 := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hts | hts
      · right
        dsimp only [t, s] at hts
        unfold oppositeCrossingT oppositeCrossingS oppositeCrossingNormal at hts
        nlinarith
      · left
        dsimp only [t, s] at hts
        unfold oppositeCrossingT oppositeCrossingS oppositeCrossingNormal at hts
        nlinarith
    have hx : p.1 ∈ Icc a b := hp.2.1
    refine ⟨p.1, hx, Prod.ext rfl ?_⟩
    rcases hzero with hxc | hpGraph
    · rw [hxc]
      change h c = p.2
      have hyBand := hp.2.2
      change p.2 ∈ Icc
        (min (h p.1) (if p.1 ≤ c then f p.1 else g p.1))
        (max (h p.1) (if p.1 ≤ c then f p.1 else g p.1)) at hyBand
      rw [hxc, if_pos le_rfl, hhCenter, min_self, max_self] at hyBand
      exact hhCenter.trans (le_antisymm hyBand.1 hyBand.2)
    · exact hpGraph.symm


def oppositeConnectorGraphSpeedConstant (M : NNReal) : NNReal :=
  ⟨1 + (M : ℝ), by positivity⟩

/-- Quantitative cost of every new rounded frontier component in the complete
carrier-modification region. -/
theorem weightedTraceCost_roundedOppositeCrossing_alteredFrontier_le
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch) {c r : ℝ} (hr : 0 < r)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfg : f c = g c) (Kr Mh : NNReal)
    (hKr : ∀ t ∈ Icc (-2 * r) (2 * r),
      Real.sqrt (1 + (deriv (roundedCrossingRadius r) t) ^ 2) ≤ (Kr : ℝ))
    (hMh : ∀ x ∈ Icc (c - 3 * r) (c + 3 * r),
      |deriv (connectGraphs (c - 3 * r) (c + 3 * r) f g) x| ≤
        (Mh : ℝ)) :
    let h := connectGraphs (c - 3 * r) (c + 3 * r) f g
    let core := roundedOppositeCrossingCore c h r
    let band := closedGraphBand h
      (fun x => if x ≤ c then f x else g x)
      (Icc (c - 3 * r) (c + 3 * r))
    weightedTraceCost lam
        (frontier {p | roundedOppositeCrossingValue P.side c r h p < 0} ∩
          (core ∪ band)) ≤
      ((ENNReal.ofReal lam *
          (roundedOppositeCrossingTraceSpeedConstant Kr Mh : ENNReal) *
            ENNReal.ofReal (4 * r)) +
        (ENNReal.ofReal lam *
          (roundedOppositeCrossingTraceSpeedConstant Kr Mh : ENNReal) *
            ENNReal.ofReal (4 * r))) +
      ENNReal.ofReal lam * (oppositeConnectorGraphSpeedConstant Mh : ENNReal) *
        ENNReal.ofReal (6 * r) := by
  dsimp only
  let h := connectGraphs (c - 3 * r) (c + 3 * r) f g
  let core := roundedOppositeCrossingCore c h r
  let band := closedGraphBand h
    (fun x => if x ≤ c then f x else g x)
    (Icc (c - 3 * r) (c + 3 * r))
  have hh : ContDiff ℝ ∞ h := contDiff_connectGraphs hf hg
  have hfront :
      frontier {p | roundedOppositeCrossingValue P.side c r h p < 0} ∩
          (core ∪ band) ⊆
        (frontier {p | roundedOppositeCrossingValue P.side c r h p < 0} ∩
          core) ∪
        (fun x : ℝ => (x, h x)) '' Icc (c - 3 * r) (c + 3 * r) := by
    intro p hp
    rcases hp.2 with hpCore | hpBand
    · exact Or.inl ⟨hp.1, hpCore⟩
    · exact frontier_roundedOppositeCrossing_inter_connectorBand_subset
        P hr hf hg hfg ⟨hp.1, hpBand⟩
  have hround :=
    weightedTraceCost_frontier_roundedOppositeCrossing_inter_core_le
      hlam P.side c hr hh Kr Mh hKr hMh
  have hgraphSpeed :
      ∀ x ∈ Icc (c - 3 * r) (c + 3 * r),
        Real.sqrt (1 + (deriv h x) ^ 2) ≤
          (oppositeConnectorGraphSpeedConstant Mh : ℝ) := by
    intro x hx
    have hslope := hMh x hx
    calc
      Real.sqrt (1 + (deriv h x) ^ 2) ≤ 1 + |deriv h x| := by
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · nlinarith [sq_abs (deriv h x), abs_nonneg (deriv h x)]
      _ ≤ 1 + (Mh : ℝ) := add_le_add le_rfl hslope
      _ = (oppositeConnectorGraphSpeedConstant Mh : ℝ) := rfl
  have hgraph := weightedTraceCost_graph_Icc_le_global hlam
    (hh.differentiable (by simp)) hgraphSpeed
  have hgraph' :
      weightedTraceCost lam
          ((fun x : ℝ => (x, h x)) '' Icc (c - 3 * r) (c + 3 * r)) ≤
        ENNReal.ofReal lam *
          (oppositeConnectorGraphSpeedConstant Mh : ENNReal) *
            ENNReal.ofReal (6 * r) := by
    simpa only [show c + 3 * r - (c - 3 * r) = 6 * r by ring] using hgraph
  exact (weightedTraceCost_mono lam hfront).trans
    ((weightedTraceCost_union_le lam _ _).trans
      (add_le_add hround hgraph'))


/-- The complete altered frontier cost for the shrinking opposite-side
crossing repair tends to zero. -/
theorem tendsto_weightedTraceCost_roundedOppositeCrossing_alteredFrontier_zero
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    Tendsto (fun n =>
      let r := symmetricConnectorRadius R n
      let h := connectGraphs (c - 3 * r) (c + 3 * r) f g
      let core := roundedOppositeCrossingCore c h r
      let band := closedGraphBand h
        (fun x => if x ≤ c then f x else g x)
        (Icc (c - 3 * r) (c + 3 * r))
      weightedTraceCost lam
        (frontier {p | roundedOppositeCrossingValue P.side c r h p < 0} ∩
          (core ∪ band))) atTop (𝓝 0) := by
  obtain ⟨Kr, hKr⟩ := exists_roundedCrossingRadius_deriv_bound
  obtain ⟨D, hD, hDbound⟩ := exists_smoothTransition_deriv_bound
  obtain ⟨M, hM, hfM, hgM⟩ :=
    exists_common_deriv_bound_Icc
      (hf.of_le (by simp)) (hg.of_le (by simp)) (c - 3 * R) (c + 3 * R)
  let Mh : NNReal := ⟨3 * M + 2 * D * M, by positivity⟩
  let Cround : ENNReal :=
    ENNReal.ofReal lam *
      (roundedOppositeCrossingTraceSpeedConstant Kr Mh : ENNReal)
  let Cgraph : ENNReal :=
    ENNReal.ofReal lam * (oppositeConnectorGraphSpeedConstant Mh : ENNReal)
  have hrzero := tendsto_symmetricConnectorRadius_zero R
  have hfourReal :
      Tendsto (fun n => 4 * symmetricConnectorRadius R n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrzero
  have hsixReal :
      Tendsto (fun n => 6 * symmetricConnectorRadius R n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrzero
  have hfour :
      Tendsto (fun n => ENNReal.ofReal (4 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hfourReal
  have hsix :
      Tendsto (fun n => ENNReal.ofReal (6 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hsixReal
  have hround :
      Tendsto (fun n =>
        Cround * ENNReal.ofReal (4 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hfour
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  have hgraph :
      Tendsto (fun n =>
        Cgraph * ENNReal.ofReal (6 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hsix
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top))
  have hbound :
      Tendsto (fun n =>
        (Cround * ENNReal.ofReal (4 * symmetricConnectorRadius R n) +
          Cround * ENNReal.ofReal (4 * symmetricConnectorRadius R n)) +
        Cgraph * ENNReal.ofReal (6 * symmetricConnectorRadius R n))
        atTop (𝓝 0) := by
    simpa only [zero_add] using (hround.add hround).add hgraph
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
  · intro n
    exact bot_le
  · intro n
    let r := symmetricConnectorRadius R n
    have hr : 0 < r := symmetricConnectorRadius_pos hR n
    have hrle : r ≤ R := symmetricConnectorRadius_le hR.le n
    have hsub :
        Icc (c - 3 * r) (c + 3 * r) ⊆
          Icc (c - 3 * R) (c + 3 * R) := by
      intro x hx
      constructor <;> nlinarith [hx.1, hx.2]
    have hc : c ∈ Icc (c - 3 * r) (c + 3 * r) := by
      constructor <;> linarith
    have hMh :
        ∀ x ∈ Icc (c - 3 * r) (c + 3 * r),
          |deriv (connectGraphs (c - 3 * r) (c + 3 * r) f g) x| ≤
            (Mh : ℝ) := by
      intro x hx
      exact abs_deriv_connectGraphs_le
        (show c - 3 * r < c + 3 * r by linarith) hc hx hf hg hM hD
        (fun y hy => hfM y (hsub hy))
        (fun y hy => hgM y (hsub hy)) hDbound hfg
    simpa only [Cround, Cgraph, r] using
      (weightedTraceCost_roundedOppositeCrossing_alteredFrontier_le
        hlam P hr hf hg hfg Kr Mh (hKr hr) hMh)


/-- Actual local `C∞` repair family for an opposite-side graph junction.
The carrier modification is confined to an explicit shrinking region, its
volume vanishes, its complete new frontier in that region has vanishing
density-weighted cost, and the exterior carrier is exactly unchanged. -/
theorem exists_vanishing_smoothOppositeVerticalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    ∃ (U modification : ℕ → Set PlanePoint),
      (∀ n, IsSmoothDomain (U n)) ∧
      (∀ n,
        U n ∆ filledOppositeVerticalGraphSwitch P f g c ⊆ modification n) ∧
      (∀ rho, 0 < rho →
        ∀ᶠ n : ℕ in atTop,
          modification n ⊆ junctionBall (c, f c) rho) ∧
      Tendsto (fun n =>
        volume (U n ∆ filledOppositeVerticalGraphSwitch P f g c))
        atTop (𝓝 0) ∧
      (∀ n p,
        p.1 ∉ Icc
            (c - 3 * symmetricConnectorRadius R n)
            (c + 3 * symmetricConnectorRadius R n) →
          (p ∈ U n ↔
            p ∈ filledOppositeVerticalGraphSwitch P f g c)) ∧
      Tendsto (fun n =>
        weightedTraceCost lam (frontier (U n) ∩ modification n))
        atTop (𝓝 0) := by
  let r : ℕ → ℝ := symmetricConnectorRadius R
  let h : ℕ → ℝ → ℝ := fun n =>
    connectGraphs (c - 3 * r n) (c + 3 * r n) f g
  let U : ℕ → Set PlanePoint := fun n =>
    {p | roundedOppositeCrossingValue P.side c (r n) (h n) p < 0}
  let modification : ℕ → Set PlanePoint := fun n =>
    roundedOppositeCrossingCore c (h n) (r n) ∪
      closedGraphBand (h n) (fun x => if x ≤ c then f x else g x)
        (Icc (c - 3 * r n) (c + 3 * r n))
  have hUsmooth : ∀ n, IsSmoothDomain (U n) := by
    intro n
    exact isSmoothDomain_roundedOppositeCrossing P.side c
      (symmetricConnectorRadius_pos hR n) (contDiff_connectGraphs hf hg)
  have hmodify : ∀ n,
      U n ∆ filledOppositeVerticalGraphSwitch P f g c ⊆ modification n := by
    intro n
    exact roundedOppositeCrossing_symmDiff_filledSwitch_subset
      (f := f) (g := g) P (symmetricConnectorRadius_pos hR n)
      (by
        have hr := symmetricConnectorRadius_pos hR n
        linarith)
      (by
        have hr := symmetricConnectorRadius_pos hR n
        linarith)
  have hball : ∀ rho, 0 < rho →
      ∀ᶠ n : ℕ in atTop,
        modification n ⊆ junctionBall (c, f c) rho := by
    intro rho hrho
    have hcore :=
      eventually_symmetricConnector_roundedOppositeCrossingCore_subset_junctionBall
        hf.continuous hg.continuous hR hfg hrho
    have hband :=
      eventually_symmetricTripleConnector_closedGraphBand_subset_junctionBall
        hf.continuous hg.continuous (R := R) hfg hrho
    filter_upwards [hcore, hband] with n hnCore hnBand
    exact union_subset hnCore hnBand
  have hvolume :
      Tendsto (fun n =>
        volume (U n ∆ filledOppositeVerticalGraphSwitch P f g c))
        atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro epsilon hepsilon
    have hballVolume := tendsto_volume_junctionBall_zero (c, f c)
    rw [ENNReal.tendsto_atTop_zero] at hballVolume
    obtain ⟨m, hm⟩ := hballVolume epsilon hepsilon
    have hevent := hball (junctionRadius m) (junctionRadius_pos m)
    rcases eventually_atTop.1 hevent with ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (measure_mono ((hmodify n).trans (hN n hn))).trans (hm m le_rfl)⟩
  have hexterior : ∀ n p,
      p.1 ∉ Icc (c - 3 * symmetricConnectorRadius R n)
          (c + 3 * symmetricConnectorRadius R n) →
        (p ∈ U n ↔ p ∈ filledOppositeVerticalGraphSwitch P f g c) := by
    intro n p hpOutside
    have hpNotModification : p ∉ modification n := by
      intro hp
      apply hpOutside
      rcases hp with hpCore | hpBand
      · have hx :=
          (roundedOppositeCrossingCore_coordinate_bounds hpCore).1
        rw [abs_lt] at hx
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      · exact hpBand.1
    have hpNotDiff :
        p ∉ U n ∆ filledOppositeVerticalGraphSwitch P f g c :=
      fun hp => hpNotModification (hmodify n hp)
    simp only [Set.mem_symmDiff, not_or, not_and, not_not] at hpNotDiff
    exact ⟨hpNotDiff.1, hpNotDiff.2⟩
  have hcost :
      Tendsto (fun n =>
        weightedTraceCost lam (frontier (U n) ∩ modification n))
        atTop (𝓝 0) := by
    simpa only [U, modification, h, r] using
      (tendsto_weightedTraceCost_roundedOppositeCrossing_alteredFrontier_zero
        hlam P hf hg hR hfg)
  exact ⟨U, modification, hUsmooth, hmodify, hball, hvolume,
    hexterior, hcost⟩


/-- Finite-budget form of the opposite-side local repair family. -/
theorem exists_smoothOppositeVerticalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ (r : ℝ) (U modification : Set PlanePoint),
      0 < r ∧ r < R ∧
      IsSmoothDomain U ∧
      U ∆ filledOppositeVerticalGraphSwitch P f g c ⊆ modification ∧
      modification ⊆ junctionBall (c, f c) rho ∧
      (∀ p, p.1 ∉ Icc (c - 3 * r) (c + 3 * r) →
        (p ∈ U ↔ p ∈ filledOppositeVerticalGraphSwitch P f g c)) ∧
      weightedTraceCost lam (frontier U ∩ modification) <
        ENNReal.ofReal epsilon := by
  obtain ⟨U, modification, hUsmooth, hmodify, hball, _hvolume,
    hexterior, hcost⟩ :=
    exists_vanishing_smoothOppositeVerticalGraphSwitchRepair
      hlam P hf hg hR hfg
  have hradius :=
    tendsto_symmetricConnectorRadius_zero R
  have heventRadius :
      ∀ᶠ n : ℕ in atTop, symmetricConnectorRadius R n < R :=
    hradius.eventually (Iio_mem_nhds hR)
  have heventBall := hball rho hrho
  have heventCost :
      ∀ᶠ n : ℕ in atTop,
        weightedTraceCost lam (frontier (U n) ∩ modification n) <
          ENNReal.ofReal epsilon :=
    hcost.eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon))
  obtain ⟨n, hnRadius, hnBall, hnCost⟩ :=
    (heventRadius.and (heventBall.and heventCost)).exists
  let r := symmetricConnectorRadius R n
  exact ⟨r, U n, modification n, symmetricConnectorRadius_pos hR n,
    hnRadius, hUsmooth n, hmodify n, hnBall, hexterior n, hnCost⟩

/-- The same finite-budget repair stated against the canonical open splice,
using the exact opposite-sector identification rather than a surrogate raw
carrier. -/
theorem exists_smoothOppositeVerticalOpenSpliceRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ (r : ℝ) (U modification : Set PlanePoint),
      0 < r ∧ r < R ∧
      IsSmoothDomain U ∧
      U ∆ openSpliceIn (P.occupiedGraphDomain f)
          (oppositeOccupiedGraphDomain P g) {p : PlanePoint | c ≤ p.1} ⊆
        modification ∧
      modification ⊆ junctionBall (c, f c) rho ∧
      (∀ p, p.1 ∉ Icc (c - 3 * r) (c + 3 * r) →
        (p ∈ U ↔
          p ∈ openSpliceIn (P.occupiedGraphDomain f)
            (oppositeOccupiedGraphDomain P g) {q : PlanePoint | c ≤ q.1})) ∧
      weightedTraceCost lam (frontier U ∩ modification) <
        ENNReal.ofReal epsilon := by
  rw [openSpliceIn_oppositeOccupiedGraphDomains_rightHalfspace_eq
    P hf.continuous hg.continuous hfg]
  exact exists_smoothOppositeVerticalGraphSwitchRepair
    hlam P hf hg hR hfg hrho hepsilon

/-- Coordinate exchange on the source plane. -/
noncomputable def planeCoordinateSwap : PlanePoint ≃ₜ PlanePoint :=
  (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toHomeomorph

@[simp] theorem planeCoordinateSwap_apply (p : PlanePoint) :
    planeCoordinateSwap p = (p.2, p.1) := by
  rcases p with ⟨x, y⟩
  rfl

/-- Coordinate exchange commutes with the canonical open-splice operation. -/
theorem planeCoordinateSwap_preimage_openSpliceIn
    (U G W : Set PlanePoint) :
    planeCoordinateSwap ⁻¹' openSpliceIn U G W =
      openSpliceIn (planeCoordinateSwap ⁻¹' U)
        (planeCoordinateSwap ⁻¹' G) (planeCoordinateSwap ⁻¹' W) := by
  unfold openSpliceIn spliceIn
  rw [planeCoordinateSwap.preimage_interior]
  rfl

theorem planeCoordinateSwap_preimage_rightHalfspace (c : ℝ) :
    planeCoordinateSwap ⁻¹' {p : PlanePoint | c ≤ p.1} =
      {p : PlanePoint | c ≤ p.2} := by
  ext p
  simp only [Set.mem_preimage, planeCoordinateSwap_apply, Set.mem_ofPred_eq]

/-- The face-labelled horizontal switch is exactly the canonical open splice
across a closed upper halfspace. -/
theorem openSpliceIn_horizontalOccupiedGraphDomains_upperHalfspace_eq
    (P : GraphPatch) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c : ℝ} (hfg : f c = g c) :
    openSpliceIn (horizontalOccupiedGraphDomain P f)
        (horizontalOccupiedGraphDomain P g) {p : PlanePoint | c ≤ p.2} =
      filledHorizontalGraphSwitch P f g c := by
  have hv := congrArg (fun S : Set PlanePoint => planeCoordinateSwap ⁻¹' S)
    (openSpliceIn_occupiedGraphDomains_rightHalfspace_eq_filledVerticalGraphSwitch
      P hf hg hfg)
  rw [planeCoordinateSwap_preimage_openSpliceIn,
    planeCoordinateSwap_preimage_rightHalfspace] at hv
  change openSpliceIn (planeCoordinateSwap ⁻¹' P.occupiedGraphDomain f)
      (planeCoordinateSwap ⁻¹' P.occupiedGraphDomain g)
      {p : PlanePoint | c ≤ p.2} =
    planeCoordinateSwap ⁻¹' filledVerticalGraphSwitch P f g c
  exact hv

/-- Euclidean coordinate exchange, used only to transport Hausdorff measure.
The strip density itself is not invariant under this map. -/
def euclideanCoordinateSwap : EuclideanPlane ≃ᵢ EuclideanPlane where
  toEquiv :=
    { toFun := fun p =>
        WithLp.toLp 2 ((WithLp.ofLp p).2, (WithLp.ofLp p).1)
      invFun := fun p =>
        WithLp.toLp 2 ((WithLp.ofLp p).2, (WithLp.ofLp p).1)
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro p q
    rw [WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
    change Real.sqrt
        (dist (WithLp.ofLp p).2 (WithLp.ofLp q).2 ^ 2 +
          dist (WithLp.ofLp p).1 (WithLp.ofLp q).1 ^ 2) =
      Real.sqrt
        (dist (WithLp.ofLp p).1 (WithLp.ofLp q).1 ^ 2 +
          dist (WithLp.ofLp p).2 (WithLp.ofLp q).2 ^ 2)
    rw [add_comm]

@[simp] theorem euclideanRigidMap_euclideanCoordinateSwap (p : PlanePoint) :
    euclideanRigidMap euclideanCoordinateSwap p = planeCoordinateSwap p := by
  rcases p with ⟨x, y⟩
  rfl

/-- The complete Euclidean trace measure is bounded by weighted trace cost,
because the strip density is everywhere at least one. -/
theorem hausdorffMeasure_le_weightedTraceCost
    {lam : ℝ} (hlam : 1 < lam) (S : Set PlanePoint) :
    (μH[1] : Measure EuclideanPlane) (planeEuclideanHomeomorph '' S) ≤
      weightedTraceCost lam S := by
  unfold weightedTraceCost
  rw [← MeasureTheory.setLIntegral_one]
  refine MeasureTheory.setLIntegral_mono
    (by
      exact ENNReal.continuous_ofReal.measurable.comp
        ((measurable_stripDensity lam).comp
          planeEuclideanHomeomorph.symm.continuous.measurable)) ?_
  intro z _hz
  rw [ENNReal.one_le_ofReal]
  unfold euclideanStripDensity StripDensity
  split_ifs <;> linarith

/-- Coordinate exchange has a sharp-enough weighted trace estimate in the
original strip coordinates.  The factor `lam` is essential: weighted trace
cost is not invariant under exchanging the strip's horizontal and vertical
coordinates. -/
theorem weightedTraceCost_planeCoordinateSwap_preimage_le
    {lam : ℝ} (hlam : 1 < lam) (S : Set PlanePoint) :
    weightedTraceCost lam (planeCoordinateSwap ⁻¹' S) ≤
      ENNReal.ofReal lam * weightedTraceCost lam S := by
  calc
    weightedTraceCost lam (planeCoordinateSwap ⁻¹' S) ≤
        ENNReal.ofReal lam *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph '' (planeCoordinateSwap ⁻¹' S)) :=
      weightedTraceCost_le_density_mul_hausdorff hlam _
    _ = ENNReal.ofReal lam *
          (μH[1] : Measure EuclideanPlane)
            (planeEuclideanHomeomorph '' S) := by
      congr 1
      have hpre :
          planeCoordinateSwap ⁻¹' S =
            euclideanRigidMap euclideanCoordinateSwap '' S := by
        ext p
        simp only [Set.mem_preimage, Set.mem_image]
        constructor
        · intro hp
          refine ⟨planeCoordinateSwap p, hp, ?_⟩
          simp
        · rintro ⟨q, hq, rfl⟩
          simpa using hq
      rw [hpre]
      have himage :
          planeEuclideanHomeomorph ''
              (euclideanRigidMap euclideanCoordinateSwap '' S) =
            euclideanCoordinateSwap ''
              (planeEuclideanHomeomorph '' S) := by
        ext z
        constructor
        · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
          exact ⟨planeEuclideanHomeomorph q, ⟨q, hq, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
          exact ⟨euclideanRigidMap euclideanCoordinateSwap q,
            ⟨q, hq, rfl⟩, rfl⟩
      rw [himage, euclideanCoordinateSwap.isometry.hausdorffMeasure_image
        (Or.inl (by norm_num : (0 : ℝ) ≤ 1))]
    _ ≤ ENNReal.ofReal lam * weightedTraceCost lam S := by
      gcongr
      exact hausdorffMeasure_le_weightedTraceCost hlam S

theorem planeCoordinateSwap_preimage_junctionBall
    (p : PlanePoint) (rho : ℝ) :
    planeCoordinateSwap ⁻¹' junctionBall p rho =
      junctionBall (planeCoordinateSwap p) rho := by
  ext q
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  change dist (planeEuclideanHomeomorph (qy, qx))
      (planeEuclideanHomeomorph (px, py)) ≤ rho ↔
    dist (planeEuclideanHomeomorph (qx, qy))
      (planeEuclideanHomeomorph (py, px)) ≤ rho
  rw [planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    planeEuclideanHomeomorph_apply, planeEuclideanHomeomorph_apply,
    WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
  change Real.sqrt (dist qy px ^ 2 + dist qx py ^ 2) ≤ rho ↔
    Real.sqrt (dist qx py ^ 2 + dist qy px ^ 2) ≤ rho
  rw [add_comm]

/-- The occupied side opposite to a horizontal graph model. -/
def oppositeHorizontalOccupiedGraphDomain
    (P : GraphPatch) (g : ℝ → ℝ) : Set PlanePoint :=
  planeCoordinateSwap ⁻¹' oppositeOccupiedGraphDomain P g

/-- Coordinate-swapped literal four-sector carrier for an opposite-side
horizontal splice. -/
def filledOppositeHorizontalGraphSwitch
    (P : GraphPatch) (f g : ℝ → ℝ) (c : ℝ) : Set PlanePoint :=
  planeCoordinateSwap ⁻¹' filledOppositeVerticalGraphSwitch P f g c

/-- The canonical horizontal open splice has exactly the coordinate-swapped
four-sector semantics. -/
theorem openSpliceIn_oppositeHorizontalOccupiedGraphDomains_upperHalfspace_eq
    (P : GraphPatch) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {c : ℝ} (hfg : f c = g c) :
    openSpliceIn (horizontalOccupiedGraphDomain P f)
        (oppositeHorizontalOccupiedGraphDomain P g)
        {p : PlanePoint | c ≤ p.2} =
      filledOppositeHorizontalGraphSwitch P f g c := by
  have hv := congrArg (fun S : Set PlanePoint => planeCoordinateSwap ⁻¹' S)
    (openSpliceIn_oppositeOccupiedGraphDomains_rightHalfspace_eq
      P hf hg hfg)
  rw [planeCoordinateSwap_preimage_openSpliceIn,
    planeCoordinateSwap_preimage_rightHalfspace] at hv
  change openSpliceIn (planeCoordinateSwap ⁻¹' P.occupiedGraphDomain f)
      (planeCoordinateSwap ⁻¹' oppositeOccupiedGraphDomain P g)
      {p : PlanePoint | c ≤ p.2} =
    planeCoordinateSwap ⁻¹' filledOppositeVerticalGraphSwitch P f g c
  exact hv

/-- Actual local `C∞` repair family for an opposite-side horizontal graph
junction.  Smoothness and topology are transported from the vertical repair;
the complete weighted trace is re-estimated in the original strip coordinates. -/
theorem exists_vanishing_smoothOppositeHorizontalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R : ℝ} (hR : 0 < R) (hfg : f c = g c) :
    ∃ (U modification : ℕ → Set PlanePoint),
      (∀ n, IsSmoothDomain (U n)) ∧
      (∀ n,
        U n ∆ filledOppositeHorizontalGraphSwitch P f g c ⊆
          modification n) ∧
      (∀ rho, 0 < rho →
        ∀ᶠ n : ℕ in atTop,
          modification n ⊆ junctionBall (f c, c) rho) ∧
      Tendsto (fun n =>
        volume (U n ∆ filledOppositeHorizontalGraphSwitch P f g c))
        atTop (𝓝 0) ∧
      (∀ n p,
        p.2 ∉ Icc
            (c - 3 * symmetricConnectorRadius R n)
            (c + 3 * symmetricConnectorRadius R n) →
          (p ∈ U n ↔
            p ∈ filledOppositeHorizontalGraphSwitch P f g c)) ∧
      Tendsto (fun n =>
        weightedTraceCost lam (frontier (U n) ∩ modification n))
        atTop (𝓝 0) := by
  obtain ⟨Uv, Mv, hUvsmooth, hmodifyv, hballv, _hvolumev,
      hexteriorv, hcostv⟩ :=
    exists_vanishing_smoothOppositeVerticalGraphSwitchRepair
      hlam P hf hg hR hfg
  let U : ℕ → Set PlanePoint := fun n => planeCoordinateSwap ⁻¹' Uv n
  let modification : ℕ → Set PlanePoint :=
    fun n => planeCoordinateSwap ⁻¹' Mv n
  have hUsmooth : ∀ n, IsSmoothDomain (U n) := by
    intro n
    have heq :
        U n = (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ) ⁻¹' Uv n := by
      ext p
      rfl
    rw [heq]
    exact (hUvsmooth n).coordinateSwap_preimage
  have hmodify : ∀ n,
      U n ∆ filledOppositeHorizontalGraphSwitch P f g c ⊆
        modification n := by
    intro n p hp
    exact hmodifyv n hp
  have hball : ∀ rho, 0 < rho →
      ∀ᶠ n : ℕ in atTop,
        modification n ⊆ junctionBall (f c, c) rho := by
    intro rho hrho
    filter_upwards [hballv rho hrho] with n hn
    have hcenter : planeCoordinateSwap (c, f c) = (f c, c) := rfl
    rw [← hcenter, ← planeCoordinateSwap_preimage_junctionBall (c, f c) rho]
    exact preimage_mono hn
  have hvolume :
      Tendsto (fun n =>
        volume (U n ∆ filledOppositeHorizontalGraphSwitch P f g c))
        atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro epsilon hepsilon
    have hballVolume := tendsto_volume_junctionBall_zero (f c, c)
    rw [ENNReal.tendsto_atTop_zero] at hballVolume
    obtain ⟨m, hm⟩ := hballVolume epsilon hepsilon
    have hevent := hball (junctionRadius m) (junctionRadius_pos m)
    rcases eventually_atTop.1 hevent with ⟨N, hN⟩
    exact ⟨N, fun n hn =>
      (measure_mono ((hmodify n).trans (hN n hn))).trans (hm m le_rfl)⟩
  have hexterior : ∀ n p,
      p.2 ∉ Icc
          (c - 3 * symmetricConnectorRadius R n)
          (c + 3 * symmetricConnectorRadius R n) →
        (p ∈ U n ↔
          p ∈ filledOppositeHorizontalGraphSwitch P f g c) := by
    intro n p hp
    simpa only [U, filledOppositeHorizontalGraphSwitch,
      Set.mem_preimage, planeCoordinateSwap_apply] using
      hexteriorv n (planeCoordinateSwap p) hp
  have hupper :
      Tendsto (fun n =>
        ENNReal.ofReal lam *
          weightedTraceCost lam (frontier (Uv n) ∩ Mv n))
        atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hcostv
      (Or.inr ENNReal.ofReal_ne_top)
  have hcost :
      Tendsto (fun n =>
        weightedTraceCost lam (frontier (U n) ∩ modification n))
        atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper
    · intro n
      exact bot_le
    · intro n
      have hle := weightedTraceCost_planeCoordinateSwap_preimage_le
        hlam (frontier (Uv n) ∩ Mv n)
      calc
        weightedTraceCost lam (frontier (U n) ∩ modification n) =
            weightedTraceCost lam
              (planeCoordinateSwap ⁻¹' (frontier (Uv n) ∩ Mv n)) := by
          congr 1
          rw [Set.preimage_inter, planeCoordinateSwap.preimage_frontier]
        _ ≤ ENNReal.ofReal lam *
              weightedTraceCost lam (frontier (Uv n) ∩ Mv n) := hle
  exact ⟨U, modification, hUsmooth, hmodify, hball, hvolume,
    hexterior, hcost⟩

/-- The same-side horizontal repair stated against the canonical open splice,
rather than only its face-labelled switch model. -/
theorem exists_smoothHorizontalOpenSpliceRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ r : ℝ, 0 < r ∧ r < rho ∧
      ∃ U : Set PlanePoint,
        IsSmoothDomain U ∧
        U ∆ openSpliceIn (horizontalOccupiedGraphDomain P f)
            (horizontalOccupiedGraphDomain P g)
            {p : PlanePoint | c ≤ p.2} ⊆
          closedHorizontalGraphBand
            (connectGraphs (c - r) (c + r) f g)
            (fun y => if y ≤ c then f y else g y)
            (Icc (c - r) (c + r)) ∧
        U ∆ openSpliceIn (horizontalOccupiedGraphDomain P f)
            (horizontalOccupiedGraphDomain P g)
            {p : PlanePoint | c ≤ p.2} ⊆
          junctionBall (f c, c) rho ∧
        (∀ p, p.2 ∉ Icc (c - r) (c + r) →
          (p ∈ U ↔
            p ∈ openSpliceIn (horizontalOccupiedGraphDomain P f)
              (horizontalOccupiedGraphDomain P g)
              {q : PlanePoint | c ≤ q.2})) ∧
        weightedTraceCost lam
            (frontier U ∩
              {p : PlanePoint | p.2 ∈ Icc (c - r) (c + r)}) <
          ENNReal.ofReal epsilon := by
  rw [openSpliceIn_horizontalOccupiedGraphDomains_upperHalfspace_eq
    P hf.continuous hg.continuous hfg]
  exact exists_smoothHorizontalGraphSwitchRepair
    hlam P hf hg hR hfg hrho hepsilon

/-- Finite-budget form of the opposite-side horizontal repair family. -/
theorem exists_smoothOppositeHorizontalGraphSwitchRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ (r : ℝ) (U modification : Set PlanePoint),
      0 < r ∧ r < R ∧
      IsSmoothDomain U ∧
      U ∆ filledOppositeHorizontalGraphSwitch P f g c ⊆ modification ∧
      modification ⊆ junctionBall (f c, c) rho ∧
      (∀ p, p.2 ∉ Icc (c - 3 * r) (c + 3 * r) →
        (p ∈ U ↔ p ∈ filledOppositeHorizontalGraphSwitch P f g c)) ∧
      weightedTraceCost lam (frontier U ∩ modification) <
        ENNReal.ofReal epsilon := by
  obtain ⟨U, modification, hUsmooth, hmodify, hball, _hvolume,
      hexterior, hcost⟩ :=
    exists_vanishing_smoothOppositeHorizontalGraphSwitchRepair
      hlam P hf hg hR hfg
  have hradius := tendsto_symmetricConnectorRadius_zero R
  have heventRadius :
      ∀ᶠ n : ℕ in atTop, symmetricConnectorRadius R n < R :=
    hradius.eventually (Iio_mem_nhds hR)
  have heventBall := hball rho hrho
  have heventCost :
      ∀ᶠ n : ℕ in atTop,
        weightedTraceCost lam (frontier (U n) ∩ modification n) <
          ENNReal.ofReal epsilon :=
    hcost.eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.2 hepsilon))
  obtain ⟨n, hnRadius, hnBall, hnCost⟩ :=
    (heventRadius.and (heventBall.and heventCost)).exists
  let r := symmetricConnectorRadius R n
  exact ⟨r, U n, modification n, symmetricConnectorRadius_pos hR n,
    hnRadius, hUsmooth n, hmodify n, hnBall, hexterior n, hnCost⟩

/-- Finite-budget opposite-side horizontal repair against the exact canonical
open splice. -/
theorem exists_smoothOppositeHorizontalOpenSpliceRepair
    {lam : ℝ} (hlam : 1 < lam) (P : GraphPatch)
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {c R rho epsilon : ℝ} (hR : 0 < R) (hfg : f c = g c)
    (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ (r : ℝ) (U modification : Set PlanePoint),
      0 < r ∧ r < R ∧
      IsSmoothDomain U ∧
      U ∆ openSpliceIn (horizontalOccupiedGraphDomain P f)
          (oppositeHorizontalOccupiedGraphDomain P g)
          {p : PlanePoint | c ≤ p.2} ⊆ modification ∧
      modification ⊆ junctionBall (f c, c) rho ∧
      (∀ p, p.2 ∉ Icc (c - 3 * r) (c + 3 * r) →
        (p ∈ U ↔
          p ∈ openSpliceIn (horizontalOccupiedGraphDomain P f)
            (oppositeHorizontalOccupiedGraphDomain P g)
            {q : PlanePoint | c ≤ q.2})) ∧
      weightedTraceCost lam (frontier U ∩ modification) <
        ENNReal.ofReal epsilon := by
  rw [openSpliceIn_oppositeHorizontalOccupiedGraphDomains_upperHalfspace_eq
    P hf.continuous hg.continuous hfg]
  exact exists_smoothOppositeHorizontalGraphSwitchRepair
    hlam P hf hg hR hfg hrho hepsilon

/-- Every actual selected-splice corner is charged by the complete cut trace.
If neither input frontier passes through the corner, the splice is locally
exactly the one-sector rectangle interior or the three-sector rectangle
exterior.  Thus all harder corner repairs necessarily retain at least one
actual input-boundary germ. -/
theorem selectedRawSplice_corner_mem_cutTrace_and_local_cases
    (A G : ℕ → Set PlanePoint) (l r d u : ℕ → ℝ)
    (hA : ∀ n, IsOpen (A n)) (hG : ∀ n, IsOpen (G n))
    (hlr : ∀ n, l n < r n) (hdu : ∀ n, d n < u n)
    {n : ℕ} {p : PlanePoint}
    (hpCorner : p ∈ ({(l n, d n), (l n, u n),
      (r n, d n), (r n, u n)} : Set PlanePoint))
    (hpFront : p ∈ frontier (selectedRawSplice A G l r d u n)) :
    p ∈ spliceCutTrace (A n) (G n)
        (closedCutRectangle (l n) (r n) (d n) (u n)) ∧
      ((p ∈ frontier (A n) ∨ p ∈ frontier (G n)) ∨
       (∃ N : Set PlanePoint, IsOpen N ∧ p ∈ N ∧
          selectedRawSplice A G l r d u n ∩ N =
            interior (closedCutRectangle (l n) (r n) (d n) (u n)) ∩ N) ∨
       (∃ N : Set PlanePoint, IsOpen N ∧ p ∈ N ∧
          selectedRawSplice A G l r d u n ∩ N =
            interior ((closedCutRectangle
              (l n) (r n) (d n) (u n))ᶜ) ∩ N)) := by
  let W := closedCutRectangle (l n) (r n) (d n) (u n)
  have hpW : p ∈ frontier W := by
    apply spliceJunctionSet_subset_frontier_closedCutRectangle
      (U := A n) (G := G n) (hlr n) (hdu n)
    exact Or.inr hpCorner
  have hpFrontRaw : p ∈ frontier (spliceIn (A n) (G n) W) := by
    have heq := frontier_openSpliceIn_eq_frontier_spliceIn
      (hA n) (hG n) (isClosed_Icc.prod isClosed_Icc)
      (closure_interior_closedCutRectangle (hlr n) (hdu n))
    change p ∈ frontier (spliceIn (A n) (G n)
      (closedCutRectangle (l n) (r n) (d n) (u n)))
    unfold closedCutRectangle
    rw [← heq]
    simpa only [selectedRawSplice, closedCutRectangle] using hpFront
  have hpiece :=
    frontier_spliceIn_subset_piecewise (A n) (G n) W hpFrontRaw
  have hcut : p ∈ spliceCutTrace (A n) (G n) W := by
    rcases hpiece with (hOutside | hInside) | hCut
    · have hpWc : p ∈ frontier Wᶜ := by
        simpa only [frontier_compl] using hpW
      exact False.elim
        (Set.disjoint_left.1 disjoint_interior_frontier hOutside.2 hpWc)
    · exact False.elim
        (Set.disjoint_left.1 disjoint_interior_frontier hInside.2 hpW)
    · exact hCut
  refine ⟨hcut, ?_⟩
  by_cases hpA : p ∈ frontier (A n)
  · exact Or.inl (Or.inl hpA)
  by_cases hpG : p ∈ frontier (G n)
  · exact Or.inl (Or.inr hpG)
  have hpDiff : p ∈ A n ∆ G n := by
    rcases hcut.2 with (hpA' | hpG') | hpDiff
    · exact False.elim (hpA hpA')
    · exact False.elim (hpG hpG')
    · exact hpDiff
  rcases hpDiff with hpAG | hpGA
  · have hpGout : p ∈ interior (G n)ᶜ := by
      have hpRegion : p ∈ interior (G n) ∪ interior (G n)ᶜ := by
        have hp' : p ∈ (frontier (G n))ᶜ := hpG
        rwa [compl_frontier_eq_union_interior] at hp'
      rcases hpRegion with hpGin | hpGout
      · exact False.elim (hpAG.2 (interior_subset hpGin))
      · exact hpGout
    let N := A n ∩ interior (G n)ᶜ
    have hNopen : IsOpen N := (hA n).inter isOpen_interior
    refine Or.inr (Or.inr ⟨N, hNopen, ⟨hpAG.1, hpGout⟩, ?_⟩)
    simpa only [selectedRawSplice, W] using
      (openSpliceIn_inter_eq_interior_compl_window_of_local_labels
        (U := A n) (G := G n) (W := W) hNopen
        (fun _ hq => hq.1) (fun _ hq => interior_subset hq.2))
  · have hpAout : p ∈ interior (A n)ᶜ := by
      have hpRegion : p ∈ interior (A n) ∪ interior (A n)ᶜ := by
        have hp' : p ∈ (frontier (A n))ᶜ := hpA
        rwa [compl_frontier_eq_union_interior] at hp'
      rcases hpRegion with hpAin | hpAout
      · exact False.elim (hpGA.2 (interior_subset hpAin))
      · exact hpAout
    let N := interior (A n)ᶜ ∩ G n
    have hNopen : IsOpen N := isOpen_interior.inter (hG n)
    refine Or.inr (Or.inl ⟨N, hNopen, ⟨hpAout, hpGA.1⟩, ?_⟩)
    simpa only [selectedRawSplice, W] using
      (openSpliceIn_inter_eq_interior_window_of_local_labels
        (U := A n) (G := G n) (W := W) hNopen
        (fun _ hq => interior_subset hq.1) (fun _ hq => hq.2))
end FiniteJunctionRepair
end CMVRelaxation
