import CMVPolygonalModTwoRegions
import Mathlib.Topology.Algebra.Affine

/-!
# Literal carriers for finite polygonal one-chains

This file separates two facts that must not be conflated.  Finite iterations of
actual collinear subdivision preserve `GeometricOneChain`, while the literal
Hausdorff mass of a representative is additive only after positive-length
collinear overlaps have been split and cancelled.  The latter condition is
recorded by finite pairwise intersections of the surviving edge carriers.
Pointwise mod-two multiplicity is invariant under the subdivision quotient
away from finitely many cut points.  Consequently every reduced representative
attains `representativeMassInf`, and both its literal length sum and carrier
`H¹` equal `geometricMass`.  This does not assert that `formalMass` is
subdivision invariant before overlap cancellation.
-/

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory BigOperators

noncomputable section

namespace CMVPolygonalModTwo

/-- The closed Euclidean segment carried by an unordered edge. -/
def edgeCarrier (e : Edge) : Set EuclideanPlane :=
  Sym2.lift
    ⟨fun a b => segment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b),
      fun _ _ => segment_symm ℝ _ _⟩ e.pair

@[simp] theorem edgeCarrier_edge (a b : PlanePoint) (hab : a ≠ b) :
    edgeCarrier (edge a b hab) =
      segment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b) := by
  simp [edgeCarrier, edge]

/-- Every edge carrier is Borel measurable in the Euclidean realization. -/
theorem measurableSet_edgeCarrier (e : Edge) : MeasurableSet (edgeCarrier e) := by
  rcases e with ⟨pair, hpair⟩
  induction pair using Sym2.ind with
  | _ a b =>
      change MeasurableSet
        (segment ℝ (planeEuclideanHomeomorph a)
          (planeEuclideanHomeomorph b))
      rw [segment_eq_image_lineMap]
      exact (isCompact_Icc.image AffineMap.lineMap_continuous).measurableSet

/-- The Euclidean `H¹` of one edge carrier is its literal Euclidean length. -/
theorem hausdorffMeasure_edgeCarrier (e : Edge) :
    (μH[1] : Measure EuclideanPlane) (edgeCarrier e) = edgeLength e := by
  rcases e with ⟨pair, hpair⟩
  induction pair using Sym2.ind with
  | _ a b =>
      change (μH[1] : Measure EuclideanPlane)
          (segment ℝ (planeEuclideanHomeomorph a)
            (planeEuclideanHomeomorph b)) =
        euclideanEdist a b
      exact hausdorffMeasure_euclideanSegment a b

/-- Literal union of all surviving coefficient-one edges of a formal chain.
This is a representative-level carrier; before common refinement it need not be
subdivision invariant. -/
def oneCarrier (C : OneChain) : Set EuclideanPlane :=
  ⋃ e ∈ C.support, edgeCarrier e

@[simp] theorem oneCarrier_zero : oneCarrier 0 = ∅ := by
  simp [oneCarrier]

/-- A representative is reduced when distinct surviving edge carriers overlap
in only finitely many points.  Transverse crossings and shared endpoints are
allowed; positive-length collinear overlaps are not. -/
def IsReducedRepresentative (C : OneChain) : Prop :=
  ∀ ⦃e⦄, e ∈ C.support → ∀ ⦃f⦄, f ∈ C.support → e ≠ f →
    (edgeCarrier e ∩ edgeCarrier f).Finite

/-- A reduced representative has exactly the sum of its literal Euclidean edge
lengths as the `H¹` measure of its carrier. -/
theorem hausdorffMeasure_oneCarrier_eq_formalMass
    (C : OneChain) (hC : IsReducedRepresentative C) :
    (μH[1] : Measure EuclideanPlane) (oneCarrier C) = formalMass C := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  have hpair : (↑C.support : Set Edge).Pairwise
      (Function.onFun (AEDisjoint (μH[1] : Measure EuclideanPlane)) edgeCarrier) := by
    intro e he f hf hef
    change (μH[1] : Measure EuclideanPlane)
      (edgeCarrier e ∩ edgeCarrier f) = 0
    exact (hC he hf hef).measure_zero (μH[1] : Measure EuclideanPlane)
  rw [oneCarrier,
    MeasureTheory.measure_biUnion_finset₀ hpair
      (fun e _ => (measurableSet_edgeCarrier e).nullMeasurableSet)]
  exact Finset.sum_congr rfl fun e _ => hausdorffMeasure_edgeCarrier e

/-- The two genuine subedges selected by one strict interior cut. -/
def splitSegmentChain (a b c : PlanePoint) (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) : OneChain :=
  segmentChain a c (by
    intro h
    subst c
    exact hab (by simpa using hc)) +
  segmentChain c b (by
    intro h
    subst c
    exact hab (by simpa using hc))

/-- One strict cut has the same subdivision-quotient class as the long edge. -/
theorem toGeometric_splitSegmentChain (a b c : PlanePoint) (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) :
    toGeometric (segmentChain a b hab) =
      toGeometric (splitSegmentChain a b c hab hc) := by
  exact toGeometric_segment_subdivision a b c hab hc

/-- One strict collinear cut preserves the literal sum of Euclidean lengths.
The proof transports the cut point to the `L²` realization before invoking
metric segment additivity. -/
theorem formalMass_splitSegmentChain (a b c : PlanePoint) (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) :
    formalMass (splitSegmentChain a b c hab hc) = euclideanEdist a b := by
  have hac : a ≠ c := by
    intro h
    subst c
    exact hab (by simpa using hc)
  have hcb : c ≠ b := by
    intro h
    subst c
    exact hab (by simpa using hc)
  let e0 := edge a c hac
  let e1 := edge c b hcb
  have hne : e0 ≠ e1 := by
    intro h
    have hp := congrArg Edge.pair h
    simp [e0, e1, edge] at hp
    rcases hp with hp | hp
    · exact hac hp.1
    · exact hab hp
  have hsupport :
      (Finsupp.single e0 (1 : Coeff) + Finsupp.single e1 1).support =
        {e0, e1} := by
    ext e
    by_cases h0 : e = e0
    · subst e
      simp [Finsupp.mem_support_iff, hne]
    by_cases h1 : e = e1
    · subst e
      simp [Finsupp.mem_support_iff, hne]
    · simp [Finsupp.mem_support_iff, h0, h1]
  have hcE : planeEuclideanHomeomorph c ∈
      segment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b) := by
    rcases hc with ⟨x, y, hx, hy, hxy, hpoint⟩
    refine ⟨x, y, hx.le, hy.le, hxy, ?_⟩
    rw [← hpoint]
    rfl
  have hdist :
      dist (planeEuclideanHomeomorph a) (planeEuclideanHomeomorph c) +
          dist (planeEuclideanHomeomorph c) (planeEuclideanHomeomorph b) =
        dist (planeEuclideanHomeomorph a) (planeEuclideanHomeomorph b) :=
    dist_add_dist_of_mem_segment hcE
  have hedist :
      euclideanEdist a c + euclideanEdist c b = euclideanEdist a b := by
    simp only [euclideanEdist, edist_dist]
    rw [← ENNReal.ofReal_add (dist_nonneg) (dist_nonneg), hdist]
  change formalMass
    (Finsupp.single e0 1 + Finsupp.single e1 1) = euclideanEdist a b
  rw [formalMass, hsupport]
  simpa [hne, e0, e1] using hedist

/-- Finite formal refinements generated only by strict collinear edge cuts,
closed under chain addition and equality. -/
inductive RefinesBySubdivision : OneChain → OneChain → Prop
  | refl (C : OneChain) : RefinesBySubdivision C C
  | ofEq {C D : OneChain} (h : C = D) : RefinesBySubdivision C D
  | split (a b c : PlanePoint) (hab : a ≠ b)
      (hc : c ∈ openSegment ℝ a b) :
      RefinesBySubdivision (segmentChain a b hab)
        (splitSegmentChain a b c hab hc)
  | add {C D E F : OneChain} :
      RefinesBySubdivision C D → RefinesBySubdivision E F →
      RefinesBySubdivision (C + E) (D + F)
  | trans {C D E : OneChain} :
      RefinesBySubdivision C D → RefinesBySubdivision D E →
      RefinesBySubdivision C E

/-- Every certified finite subdivision refinement represents the same geometric
one-chain. -/
theorem RefinesBySubdivision.toGeometric_eq
    {C D : OneChain} (h : RefinesBySubdivision C D) :
    toGeometric C = toGeometric D := by
  induction h with
  | refl => rfl
  | ofEq h => exact congrArg toGeometric h
  | split a b c hab hc => exact toGeometric_splitSegmentChain a b c hab hc
  | add h₁ h₂ ih₁ ih₂ => simpa only [map_add] using congrArg₂ (· + ·) ih₁ ih₂
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
/-- Pointwise mod-two multiplicity of the literal supported segments. -/
def oneParity (p : EuclideanPlane) : OneChain →ₗ[Coeff] Coeff := by
  classical
  exact Finsupp.linearCombination Coeff fun e =>
    if p ∈ edgeCarrier e then 1 else 0

/-- Literal odd-multiplicity support of a representative. -/
def parityCarrier (C : OneChain) : Set EuclideanPlane :=
  {p | oneParity p C = 1}

private theorem segment_eq_union_of_mem_openSegment
    {a b c : EuclideanPlane} (hc : c ∈ openSegment ℝ a b) :
    segment ℝ a b = segment ℝ a c ∪ segment ℝ c b := by
  apply Set.Subset.antisymm
  · intro p hp
    rw [← insert_endpoints_openSegment ℝ a b] at hp
    rcases hp with hpa | hpb | hp
    · subst p
      exact Or.inl (left_mem_segment ℝ a c)
    · subst p
      exact Or.inr (right_mem_segment ℝ c b)
    · have hc' := hc
      rw [openSegment_eq_image_lineMap] at hc'
      rcases hc' with ⟨t, ht, hct⟩
      have hcline :
          c ∈ Set.range (AffineMap.lineMap a b : ℝ → EuclideanPlane) :=
        ⟨t, hct⟩
      rcases openSegment_subset_union a b hcline hp with hpc | hp | hp
      · subst p
        exact Or.inl (right_mem_segment ℝ a c)
      · exact Or.inl (openSegment_subset_segment ℝ a c hp)
      · exact Or.inr (openSegment_subset_segment ℝ c b hp)
  · apply union_subset
    · exact (convex_segment a b).segment_subset
        (left_mem_segment ℝ a b)
        (openSegment_subset_segment ℝ a b hc)
    · exact (convex_segment a b).segment_subset
        (openSegment_subset_segment ℝ a b hc)
        (right_mem_segment ℝ a b)

private theorem segment_inter_segment_subset_cut
    {a b c : EuclideanPlane} (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) :
    segment ℝ a c ∩ segment ℝ c b ⊆ {c} := by
  intro p hp
  have hcS : Sbtw ℝ a c b := by
    refine ⟨mem_segment_iff_wbtw.mp
      (openSegment_subset_segment ℝ a b hc), ?_, ?_⟩
    · intro h
      subst c
      exact hab (left_mem_openSegment_iff.mp hc)
    · intro h
      subst c
      exact hab (right_mem_openSegment_iff.mp hc)
  have hp0 : Wbtw ℝ a p c := mem_segment_iff_wbtw.mp hp.1
  have hp1 : Wbtw ℝ c p b := mem_segment_iff_wbtw.mp hp.2
  have hcp : Wbtw ℝ a c p := hcS.wbtw.trans_right_left hp1
  exact Set.mem_singleton_iff.mpr (hp0.swap_right_iff.mp hcp)

private theorem subdivision_geometry
    (a b c : PlanePoint) (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) :
    edgeCarrier (edge a b hab) =
        edgeCarrier (edge a c (by
          intro h; subst c; exact hab (by simpa using hc))) ∪
      edgeCarrier (edge c b (by
        intro h; subst c; exact hab (by simpa using hc))) ∧
    edgeCarrier (edge a c (by
          intro h; subst c; exact hab (by simpa using hc))) ∩
        edgeCarrier (edge c b (by
          intro h; subst c; exact hab (by simpa using hc))) ⊆
      {planeEuclideanHomeomorph c} := by
  have hcE : planeEuclideanHomeomorph c ∈
      openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b) := by
    rcases hc with ⟨x, y, hx, hy, hxy, hpoint⟩
    refine ⟨x, y, hx, hy, hxy, ?_⟩
    rw [← hpoint]
    rfl
  have habE : planeEuclideanHomeomorph a ≠
      planeEuclideanHomeomorph b :=
    planeEuclideanHomeomorph.injective.ne hab
  simp only [edgeCarrier_edge]
  exact ⟨segment_eq_union_of_mem_openSegment hcE,
    segment_inter_segment_subset_cut habE hcE⟩

/-- An elementary subdivision relation has zero multiplicity away from its cut point. -/
theorem oneParity_subdivisionGenerator_of_ne
    (a b c : PlanePoint) (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) {p : EuclideanPlane}
    (hp : p ≠ planeEuclideanHomeomorph c) :
    oneParity p (subdivisionGenerator a b c hab hc) = 0 := by
  classical
  rcases subdivision_geometry a b c hab hc with ⟨hunion, hinter⟩
  let hac : a ≠ c := by
    intro h; subst c; exact hab (by simpa using hc)
  let hcb : c ≠ b := by
    intro h; subst c; exact hab (by simpa using hc)
  have hnotboth : ¬(p ∈ edgeCarrier (edge a c hac) ∧
      p ∈ edgeCarrier (edge c b hcb)) := by
    intro h
    exact hp (Set.mem_singleton_iff.mp (hinter h))
  have hmem : p ∈ edgeCarrier (edge a b hab) ↔
      p ∈ edgeCarrier (edge a c hac) ∨ p ∈ edgeCarrier (edge c b hcb) := by
    rw [hunion]
    rfl
  simp only [subdivisionGenerator, map_add, oneParity, segmentChain,
    Finsupp.linearCombination_single, one_smul]
  change (if p ∈ edgeCarrier (edge a b hab) then 1 else 0) +
      (if p ∈ edgeCarrier (edge a c hac) then 1 else 0) +
      (if p ∈ edgeCarrier (edge c b hcb) then 1 else 0) = 0
  by_cases hL : p ∈ edgeCarrier (edge a c hac) <;>
    by_cases hR : p ∈ edgeCarrier (edge c b hcb) <;>
      simp_all

/-- An elementary subdivision relation is H1-a.e. zero pointwise. -/
theorem oneParity_subdivisionGenerator_ae
    (a b c : PlanePoint) (hab : a ≠ b)
    (hc : c ∈ openSegment ℝ a b) :
    ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane),
      oneParity p (subdivisionGenerator a b c hab hc) = 0 := by
  have hne : ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane),
      p ≠ planeEuclideanHomeomorph c := by
    rw [ae_iff]
    apply measure_mono_null
      (t := {planeEuclideanHomeomorph c})
    · intro p hp
      simpa only [Set.mem_ofPred_eq, not_not, Set.mem_singleton_iff] using hp
    · exact
        (Measure.nullSingletonClass_hausdorff EuclideanPlane
          (by norm_num)).measure_singleton (planeEuclideanHomeomorph c)
  exact hne.mono fun _ hp => oneParity_subdivisionGenerator_of_ne a b c hab hc hp

/-- Formal chains whose pointwise mod-two multiplicity vanishes H1-a.e. -/
def oneParityAEKernel : AddSubgroup OneChain where
  carrier := {C | ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p C = 0}
  zero_mem' := by
    change ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p 0 = 0
    exact Filter.Eventually.of_forall fun p => by simp
  add_mem' := by
    intro C D hC hD
    change (∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p C = 0) at hC
    change (∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p D = 0) at hD
    change ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p (C + D) = 0
    filter_upwards [hC, hD] with p hpC hpD
    simp only [map_add, hpC, hpD, add_zero]
  neg_mem' := by
    intro C hC
    change (∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p C = 0) at hC
    change ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p (-C) = 0
    filter_upwards [hC] with p hpC
    simp only [map_neg, hpC, neg_zero]
/-- Every finite sum of elementary subdivision relations is pointwise zero
outside an H1-null set. -/
theorem subdivisionSubgroup_le_oneParityAEKernel :
    subdivisionSubgroup ≤ oneParityAEKernel := by
  rw [subdivisionSubgroup, AddSubgroup.closure_le]
  rintro C ⟨a, b, c, hab, hc, rfl⟩
  exact oneParity_subdivisionGenerator_ae a b c hab hc

/-- Pointwise odd multiplicity is H1-a.e. invariant under the actual
subdivision quotient. -/
theorem oneParity_ae_eq_of_toGeometric_eq
    {C D : OneChain} (h : toGeometric C = toGeometric D) :
    (fun p => oneParity p C) =ᵐ[(μH[1] : Measure EuclideanPlane)]
      fun p => oneParity p D := by
  have hsub : C - D ∈ subdivisionSubgroup :=
    QuotientAddGroup.eq_iff_sub_mem.mp h
  have hae :
      ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane), oneParity p (C - D) = 0 :=
    subdivisionSubgroup_le_oneParityAEKernel hsub
  filter_upwards [hae] with p hp
  apply sub_eq_zero.mp
  simpa only [map_sub] using hp

/-- The odd-multiplicity carrier itself is H1-a.e. invariant under
subdivision. -/
theorem parityCarrier_ae_eq_of_toGeometric_eq
    {C D : OneChain} (h : toGeometric C = toGeometric D) :
    parityCarrier C =ᵐ[(μH[1] : Measure EuclideanPlane)] parityCarrier D := by
  filter_upwards [oneParity_ae_eq_of_toGeometric_eq h] with p hp
  apply propext
  change (oneParity p C = 1) ↔ oneParity p D = 1
  rw [hp]

/-- Odd multiplicity can occur only on one of the supported segments. -/
theorem parityCarrier_subset_oneCarrier (C : OneChain) :
    parityCarrier C ⊆ oneCarrier C := by
  classical
  intro p hp
  by_contra hnot
  have hedge (e : Edge) (he : e ∈ C.support) : p ∉ edgeCarrier e := by
    intro hpe
    apply hnot
    refine Set.mem_iUnion_of_mem e ?_
    exact Set.mem_iUnion_of_mem he hpe
  have hzero : oneParity p C = 0 := by
    rw [oneParity, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro e he
    simp [hedge e he]
  exact zero_ne_one (hzero.symm.trans hp)

/-- The H1 mass of the odd-multiplicity support is bounded by every literal
formal representative mass, without a reducedness hypothesis. -/
theorem hausdorffMeasure_parityCarrier_le_formalMass (C : OneChain) :
    (μH[1] : Measure EuclideanPlane) (parityCarrier C) ≤ formalMass C := by
  calc
    (μH[1] : Measure EuclideanPlane) (parityCarrier C) ≤
        (μH[1] : Measure EuclideanPlane) (oneCarrier C) :=
      measure_mono (parityCarrier_subset_oneCarrier C)
    _ ≤ ∑ e ∈ C.support,
          (μH[1] : Measure EuclideanPlane) (edgeCarrier e) := by
      exact measure_biUnion_finset_le C.support edgeCarrier
    _ = formalMass C := by
      apply Finset.sum_congr rfl
      intro e _
      exact hausdorffMeasure_edgeCarrier e

/-- A reduced representative's literal union and odd-multiplicity support
agree H1-a.e.; only its finite pairwise edge intersections are discarded. -/
theorem parityCarrier_ae_eq_oneCarrier_of_reduced
    (C : OneChain) (hC : IsReducedRepresentative C) :
    parityCarrier C =ᵐ[(μH[1] : Measure EuclideanPlane)] oneCarrier C := by
  let _ : NullSingletonClass (μH[1] : Measure EuclideanPlane) :=
    Measure.nullSingletonClass_hausdorff EuclideanPlane (by norm_num)
  classical
  have hpair (e : Edge) (he : e ∈ C.support)
      (f : Edge) (hf : f ∈ C.support) (hef : e ≠ f) :
      ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane),
        ¬(p ∈ edgeCarrier e ∧ p ∈ edgeCarrier f) := by
    rw [ae_iff]
    apply measure_mono_null
      (t := edgeCarrier e ∩ edgeCarrier f)
    · intro p hp
      simpa only [Set.mem_ofPred_eq, not_not, Set.mem_inter_iff] using hp
    · exact (hC he hf hef).measure_zero (μH[1] : Measure EuclideanPlane)
  have hgood :
      ∀ᵐ p ∂(μH[1] : Measure EuclideanPlane),
        ∀ e ∈ C.support, ∀ f ∈ C.support, e ≠ f →
          ¬(p ∈ edgeCarrier e ∧ p ∈ edgeCarrier f) := by
    rw [C.support.eventually_all]
    intro e he
    rw [C.support.eventually_all]
    intro f hf
    by_cases hef : e = f
    · subst f
      exact Filter.Eventually.of_forall fun _ hne => (hne rfl).elim
    · exact (hpair e he f hf hef).mono fun _ hp _ => hp
  filter_upwards [hgood] with p hp
  apply propext
  constructor
  · intro hpC
    exact (parityCarrier_subset_oneCarrier C) hpC
  · intro hpU
    change p ∈ ⋃ e ∈ C.support, edgeCarrier e at hpU
    rw [Set.mem_iUnion] at hpU
    rcases hpU with ⟨e, hpU⟩
    rw [Set.mem_iUnion] at hpU
    rcases hpU with ⟨he, hpe⟩
    change oneParity p C = 1
    rw [oneParity, Finsupp.linearCombination_apply]
    calc
      C.sum (fun i a => a • if p ∈ edgeCarrier i then (1 : Coeff) else 0) =
          C e • (if p ∈ edgeCarrier e then (1 : Coeff) else 0) := by
        apply Finsupp.sum_eq_single e
        · intro f hf0 hfe
          have hf : f ∈ C.support := Finsupp.mem_support_iff.mpr hf0
          have hnmem : p ∉ edgeCarrier f := by
            intro hpf
            exact hp e he f hf hfe.symm ⟨hpe, hpf⟩
          simp [hnmem]
        · intro hzero
          exact (Finsupp.mem_support_iff.mp he hzero).elim
      _ = 1 := by
        have hcoeff : C e = 1 :=
          Fin.eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp he)
        rw [hcoeff]
        simp [hpe]
/-- On every reduced representative, odd-support H1 is the literal edge-length
sum. -/
theorem hausdorffMeasure_parityCarrier_eq_formalMass_of_reduced
    (C : OneChain) (hC : IsReducedRepresentative C) :
    (μH[1] : Measure EuclideanPlane) (parityCarrier C) = formalMass C := by
  calc
    (μH[1] : Measure EuclideanPlane) (parityCarrier C) =
        (μH[1] : Measure EuclideanPlane) (oneCarrier C) :=
      measure_congr (parityCarrier_ae_eq_oneCarrier_of_reduced C hC)
    _ = formalMass C :=
      hausdorffMeasure_oneCarrier_eq_formalMass C hC

/-- A reduced representative attains the infimum over every formal
representative in its subdivision class. -/
theorem formalMass_eq_representativeMassInf_of_reduced
    (D : OneChain) (hD : IsReducedRepresentative D) :
    formalMass D = representativeMassInf (toGeometric D) := by
  apply le_antisymm
  · rw [← hausdorffMeasure_parityCarrier_eq_formalMass_of_reduced D hD]
    unfold representativeMassInf
    apply le_iInf
    intro C
    apply le_iInf
    intro hC
    calc
      (μH[1] : Measure EuclideanPlane) (parityCarrier D) =
          (μH[1] : Measure EuclideanPlane) (parityCarrier C) := by
        exact measure_congr
          (parityCarrier_ae_eq_of_toGeometric_eq hC).symm
      _ ≤ formalMass C :=
        hausdorffMeasure_parityCarrier_le_formalMass C
  · exact representativeMassInf_le_formalMass D

/-- The quotient mass is the literal Euclidean length sum of every reduced
representative; no two-endpoint calibration is used. -/
theorem geometricMass_toGeometric_eq_formalMass_of_reduced
    (D : OneChain) (hD : IsReducedRepresentative D) :
    geometricMass (toGeometric D) = formalMass D := by
  rw [geometricMass_eq_representativeMassInf,
    ← formalMass_eq_representativeMassInf_of_reduced D hD]

/-- The quotient mass is also exactly H1 of every reduced representative's
literal union. -/
theorem geometricMass_toGeometric_eq_hausdorffMeasure_oneCarrier_of_reduced
    (D : OneChain) (hD : IsReducedRepresentative D) :
    geometricMass (toGeometric D) =
      (μH[1] : Measure EuclideanPlane) (oneCarrier D) := by
  rw [geometricMass_toGeometric_eq_formalMass_of_reduced D hD,
    hausdorffMeasure_oneCarrier_eq_formalMass D hD]

/-- Two independently chosen reduced representatives of one geometric chain
have the same literal edge sum and the same literal H1 carrier mass. -/
theorem reduced_representatives_mass_independent
    {C D : OneChain} (hC : IsReducedRepresentative C)
    (hD : IsReducedRepresentative D) (h : toGeometric C = toGeometric D) :
    formalMass C = formalMass D ∧
      (μH[1] : Measure EuclideanPlane) (oneCarrier C) =
        (μH[1] : Measure EuclideanPlane) (oneCarrier D) := by
  have hm : formalMass C = formalMass D := by
    rw [← geometricMass_toGeometric_eq_formalMass_of_reduced C hC,
      ← geometricMass_toGeometric_eq_formalMass_of_reduced D hD, h]
  exact ⟨hm, by
    rw [hausdorffMeasure_oneCarrier_eq_formalMass C hC,
      hausdorffMeasure_oneCarrier_eq_formalMass D hD, hm]⟩


private def euclideanFirst (z : EuclideanPlane) : ℝ :=
  ((WithLp.linearEquiv 2 ℝ (ℝ × ℝ)) z).1

private theorem euclideanFirst_mem_horizontalSegment
    {x0 x1 y : ℝ} (hx : x0 ≤ x1) {z : EuclideanPlane}
    (hz : z ∈ segment ℝ (planeEuclideanHomeomorph (x0, y))
      (planeEuclideanHomeomorph (x1, y))) :
    x0 ≤ euclideanFirst z ∧ euclideanFirst z ≤ x1 := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  change x0 ≤ a * x0 + b * x1 ∧ a * x0 + b * x1 ≤ x1
  constructor
  · calc
      x0 = (a + b) * x0 := by rw [hab]; simp
      _ = a * x0 + b * x0 := by ring
      _ ≤ a * x0 + b * x1 := by gcongr
  · calc
      a * x0 + b * x1 ≤ a * x1 + b * x1 := by gcongr
      _ = (a + b) * x1 := by ring
      _ = x1 := by rw [hab]; simp

private def euclideanSecond (z : EuclideanPlane) : ℝ :=
  ((WithLp.linearEquiv 2 ℝ (ℝ × ℝ)) z).2

private theorem euclideanSecond_mem_horizontalSegment
    {x0 x1 y : ℝ} {z : EuclideanPlane}
    (hz : z ∈ segment ℝ (planeEuclideanHomeomorph (x0, y))
      (planeEuclideanHomeomorph (x1, y))) :
    euclideanSecond z = y := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  change a * y + b * y = y
  calc
    a * y + b * y = (a + b) * y := by ring
    _ = y := by rw [hab]; simp

private theorem euclideanFirst_mem_verticalSegment
    {x y0 y1 : ℝ} {z : EuclideanPlane}
    (hz : z ∈ segment ℝ (planeEuclideanHomeomorph (x, y0))
      (planeEuclideanHomeomorph (x, y1))) :
    euclideanFirst z = x := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  change a * x + b * x = x
  calc
    a * x + b * x = (a + b) * x := by ring
    _ = x := by rw [hab]; simp

private theorem euclidean_eq_planePoint_of_coordinates
    (z : EuclideanPlane) (x y : ℝ)
    (hx : euclideanFirst z = x) (hy : euclideanSecond z = y) :
    z = planeEuclideanHomeomorph (x, y) := by
  apply (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).injective
  apply Prod.ext
  · exact hx
  · exact hy


private theorem horizontalSegments_inter_finite_of_base_ne
    {a b c d y v : ℝ} (hyv : y ≠ v) :
    (segment ℝ (planeEuclideanHomeomorph (a, y))
        (planeEuclideanHomeomorph (b, y)) ∩
      segment ℝ (planeEuclideanHomeomorph (c, v))
        (planeEuclideanHomeomorph (d, v))).Finite := by
  apply Set.finite_empty.subset
  intro z hz
  have hy := euclideanSecond_mem_horizontalSegment hz.1
  have hv := euclideanSecond_mem_horizontalSegment hz.2
  exact hyv (hy.symm.trans hv)

private theorem verticalSegments_inter_finite_of_base_ne
    {a b c d x u : ℝ} (hxu : x ≠ u) :
    (segment ℝ (planeEuclideanHomeomorph (x, a))
        (planeEuclideanHomeomorph (x, b)) ∩
      segment ℝ (planeEuclideanHomeomorph (u, c))
        (planeEuclideanHomeomorph (u, d))).Finite := by
  apply Set.finite_empty.subset
  intro z hz
  have hx := euclideanFirst_mem_verticalSegment hz.1
  have hu := euclideanFirst_mem_verticalSegment hz.2
  exact hxu (hx.symm.trans hu)

private theorem horizontalSegment_inter_verticalSegment_finite
    {a b c d x y : ℝ} :
    (segment ℝ (planeEuclideanHomeomorph (a, y))
        (planeEuclideanHomeomorph (b, y)) ∩
      segment ℝ (planeEuclideanHomeomorph (x, c))
        (planeEuclideanHomeomorph (x, d))).Finite := by
  apply (Set.finite_singleton (planeEuclideanHomeomorph (x, y))).subset
  intro z hz
  exact Set.mem_singleton_iff.mpr
    (euclidean_eq_planePoint_of_coordinates z x y
      (euclideanFirst_mem_verticalSegment hz.2)
      (euclideanSecond_mem_horizontalSegment hz.1))


private theorem verticalSegment_inter_horizontalSegment_finite
    {a b c d x y : ℝ} :
    (segment ℝ (planeEuclideanHomeomorph (x, c))
        (planeEuclideanHomeomorph (x, d)) ∩
      segment ℝ (planeEuclideanHomeomorph (a, y))
        (planeEuclideanHomeomorph (b, y))).Finite := by
  simpa only [inter_comm] using
    (horizontalSegment_inter_verticalSegment_finite
      (a := a) (b := b) (c := c) (d := d) (x := x) (y := y))

namespace PartialOverlap

def p0 : PlanePoint := (0, 0)
def p1 : PlanePoint := (1, 0)
def p2 : PlanePoint := (2, 0)
def p3 : PlanePoint := (3, 0)

theorem p0_ne_p1 : p0 ≠ p1 := by norm_num [p0, p1]
theorem p0_ne_p2 : p0 ≠ p2 := by norm_num [p0, p2]
theorem p1_ne_p2 : p1 ≠ p2 := by norm_num [p1, p2]
theorem p1_ne_p3 : p1 ≠ p3 := by norm_num [p1, p3]
theorem p2_ne_p3 : p2 ≠ p3 := by norm_num [p2, p3]

theorem p1_mem_openSegment_p0_p2 :
    p1 ∈ openSegment ℝ p0 p2 := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [p0, p1, p2]

theorem p2_mem_openSegment_p1_p3 :
    p2 ∈ openSegment ℝ p1 p3 := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [p1, p2, p3]

/-- Two partially overlapping collinear edges before common refinement. -/
def chain : OneChain :=
  segmentChain p0 p2 p0_ne_p2 + segmentChain p1 p3 p1_ne_p3

/-- The two exterior atoms left after both overlap endpoints are inserted and
the coincident middle atom cancels modulo two. -/
def reducedChain : OneChain :=
  segmentChain p0 p1 p0_ne_p1 + segmentChain p2 p3 p2_ne_p3

/-- The positive-length overlap is removed by two actual strict cuts, not by a
two-endpoint calibration or a mass assertion. -/
theorem chain_refines_reducedChain :
    RefinesBySubdivision chain reducedChain := by
  apply RefinesBySubdivision.trans
    (RefinesBySubdivision.add
      (RefinesBySubdivision.split p0 p2 p1 p0_ne_p2
        p1_mem_openSegment_p0_p2)
      (RefinesBySubdivision.split p1 p3 p2 p1_ne_p3
        p2_mem_openSegment_p1_p3))
  apply RefinesBySubdivision.ofEq
  simp only [reducedChain, splitSegmentChain]
  calc
    (segmentChain p0 p1 _ + segmentChain p1 p2 _) +
        (segmentChain p1 p2 _ + segmentChain p2 p3 _) =
      segmentChain p0 p1 _ +
        (segmentChain p1 p2 _ + segmentChain p1 p2 _) +
          segmentChain p2 p3 _ := by abel
    _ = segmentChain p0 p1 _ + segmentChain p2 p3 _ := by simp

theorem toGeometric_chain_eq_reducedChain :
    toGeometric chain = toGeometric reducedChain :=
  chain_refines_reducedChain.toGeometric_eq


theorem formalMass_reducedChain : formalMass reducedChain = 2 := by
  let e0 := edge p0 p1 p0_ne_p1
  let e1 := edge p2 p3 p2_ne_p3
  let edgeCoordSum (e : Edge) : PlanePoint :=
    Sym2.lift
      ⟨fun p q => (p.1 + q.1, p.2 + q.2), by
        intro p q
        simp [add_comm]⟩ e.pair
  have hne : e0 ≠ e1 := by
    intro h
    have hp := congrArg edgeCoordSum h
    norm_num [edgeCoordSum, e0, e1, edge, p0, p1, p2, p3] at hp
  have hsupport :
      (Finsupp.single e0 (1 : Coeff) + Finsupp.single e1 1).support =
        {e0, e1} := by
    ext e
    by_cases h0 : e = e0
    · subst e
      simp [Finsupp.mem_support_iff, hne]
    by_cases h1 : e = e1
    · subst e
      simp [Finsupp.mem_support_iff, hne]
    · simp [Finsupp.mem_support_iff, h0, h1]
  have hlen0 : edgeLength e0 = 1 := by
    norm_num [e0, edgeLength, euclideanEdist, p0, p1, edge,
      planeEuclideanHomeomorph_apply, WithLp.prod_dist_eq_of_L2, Real.dist_eq]
  have hlen1 : edgeLength e1 = 1 := by
    norm_num [e1, edgeLength, euclideanEdist, p2, p3, edge, edist_dist,
      planeEuclideanHomeomorph_apply, WithLp.prod_dist_eq_of_L2, Real.dist_eq]
  change formalMass
    (Finsupp.single e0 1 + Finsupp.single e1 1) = 2
  rw [formalMass, hsupport]
  simp [hne, hlen0, hlen1]
  norm_num

theorem geometricMass_chain_le_two : geometricMass (toGeometric chain) ≤ 2 := by
  rw [geometricMass_eq_representativeMassInf,
    toGeometric_chain_eq_reducedChain]
  exact (representativeMassInf_le_formalMass reducedChain).trans_eq
    formalMass_reducedChain




theorem reducedChain_isReduced : IsReducedRepresentative reducedChain := by
  let e0 := edge p0 p1 p0_ne_p1
  let e1 := edge p2 p3 p2_ne_p3
  let edgeCoordSum (e : Edge) : PlanePoint :=
    Sym2.lift
      ⟨fun p q => (p.1 + q.1, p.2 + q.2), by
        intro p q
        simp [add_comm]⟩ e.pair
  have hne : e0 ≠ e1 := by
    intro h
    have hp := congrArg edgeCoordSum h
    norm_num [edgeCoordSum, e0, e1, edge, p0, p1, p2, p3] at hp
  have hsupport :
      reducedChain.support = {e0, e1} := by
    change (Finsupp.single e0 (1 : Coeff) +
      Finsupp.single e1 1).support = {e0, e1}
    ext e
    by_cases h0 : e = e0
    · subst e
      simp [Finsupp.mem_support_iff, hne]
    by_cases h1 : e = e1
    · subst e
      simp [Finsupp.mem_support_iff, hne]
    · simp [Finsupp.mem_support_iff, h0, h1]
  have hinter : (edgeCarrier e0 ∩ edgeCarrier e1).Finite := by
    apply Set.finite_empty.subset
    intro z hz
    rcases hz with ⟨hz0, hz1⟩
    have h0 := euclideanFirst_mem_horizontalSegment
      (x0 := 0) (x1 := 1) (y := 0) (by norm_num) (z := z) (by
        simpa [e0, p0, p1] using hz0)
    have h1 := euclideanFirst_mem_horizontalSegment
      (x0 := 2) (x1 := 3) (y := 0) (by norm_num) (z := z) (by
        simpa [e1, p2, p3] using hz1)
    linarith
  intro e he f hf hef
  rw [hsupport] at he hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact (hef rfl).elim
  · exact hinter
  · simpa only [inter_comm] using hinter
  · exact (hef rfl).elim

theorem hausdorffMeasure_oneCarrier_reducedChain :
    (μH[1] : Measure EuclideanPlane) (oneCarrier reducedChain) = 2 := by
  rw [hausdorffMeasure_oneCarrier_eq_formalMass reducedChain
      reducedChain_isReduced,
    formalMass_reducedChain]

/-- The partially overlapping input chain has quotient mass exactly two after
its coincident middle atom is cancelled. -/
theorem geometricMass_chain_eq_two :
    geometricMass (toGeometric chain) = 2 := by
  calc
    geometricMass (toGeometric chain) =
        geometricMass (toGeometric reducedChain) :=
      congrArg geometricMass toGeometric_chain_eq_reducedChain
    _ = formalMass reducedChain :=
      geometricMass_toGeometric_eq_formalMass_of_reduced
        reducedChain reducedChain_isReduced
    _ = 2 := formalMass_reducedChain

/-- The same partial-overlap quotient mass is literal H1 of its reduced
odd-multiplicity support. -/
theorem geometricMass_chain_eq_hausdorffMeasure_reducedCarrier :
    geometricMass (toGeometric chain) =
      (μH[1] : Measure EuclideanPlane) (oneCarrier reducedChain) := by
  rw [geometricMass_chain_eq_two,
    hausdorffMeasure_oneCarrier_reducedChain]

end PartialOverlap


namespace NoncollinearCycle

def q0 : PlanePoint := (0, 0)
def q1 : PlanePoint := (1, 0)
def q2 : PlanePoint := (0, 1)

theorem q0_ne_q1 : q0 ≠ q1 := by norm_num [q0, q1]
theorem q1_ne_q2 : q1 ≠ q2 := by norm_num [q1, q2]
theorem q2_ne_q0 : q2 ≠ q0 := by norm_num [q2, q0]

def e01 : Edge := edge q0 q1 q0_ne_q1
def e12 : Edge := edge q1 q2 q1_ne_q2
def e20 : Edge := edge q2 q0 q2_ne_q0

def triangle : Triangle where
  a := q0
  b := q1
  c := q2
  hab := q0_ne_q1
  hbc := q1_ne_q2
  hca := q2_ne_q0

/-- A genuine noncollinear closed three-edge cycle. -/
def cycle : OneChain := triangleBoundary triangle

theorem boundaryOne_cycle : boundaryOne cycle = 0 := by
  simpa [cycle] using
    (boundaryOne_formalBoundary (Finsupp.single triangle (1 : Coeff)))

private theorem pairwise_edge_ne :
    e01 ≠ e12 ∧ e01 ≠ e20 ∧ e12 ≠ e20 := by
  let edgeCoordSum (e : Edge) : PlanePoint :=
    Sym2.lift
      ⟨fun p q => (p.1 + q.1, p.2 + q.2), by
        intro p q
        simp [add_comm]⟩ e.pair
  constructor
  · intro h
    have hp := congrArg edgeCoordSum h
    norm_num [edgeCoordSum, e01, e12, edge, q0, q1, q2] at hp
  constructor
  · intro h
    have hp := congrArg edgeCoordSum h
    norm_num [edgeCoordSum, e01, e20, edge, q0, q1, q2] at hp
  · intro h
    have hp := congrArg edgeCoordSum h
    norm_num [edgeCoordSum, e12, e20, edge, q0, q1, q2] at hp

private theorem cycle_support : cycle.support = {e01, e12, e20} := by
  rcases pairwise_edge_ne with ⟨h01_12, h01_20, h12_20⟩
  change (Finsupp.single e01 (1 : Coeff) +
    Finsupp.single e12 1 + Finsupp.single e20 1).support =
      {e01, e12, e20}
  ext e
  by_cases h0 : e = e01
  · subst e
    simp [Finsupp.mem_support_iff, h01_12, h01_20]
  by_cases h1 : e = e12
  · subst e
    simp [Finsupp.mem_support_iff, h01_12, h12_20]
  by_cases h2 : e = e20
  · subst e
    simp [Finsupp.mem_support_iff, h01_20, h12_20]
  · simp [Finsupp.mem_support_iff, h0, h1, h2]

private theorem euclidean_sum_mem_diagonal {z : EuclideanPlane}
    (hz : z ∈ edgeCarrier e12) :
    euclideanFirst z + euclideanSecond z = 1 := by
  rw [e12, edgeCarrier_edge] at hz
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  change (a * 1 + b * 0) + (a * 0 + b * 1) = 1
  simpa using hab

private theorem e01_inter_e12_finite :
    (edgeCarrier e01 ∩ edgeCarrier e12).Finite := by
  apply (Set.finite_singleton (planeEuclideanHomeomorph q1)).subset
  intro z hz
  have hy : euclideanSecond z = 0 :=
    euclideanSecond_mem_horizontalSegment (by
      simpa [e01, q0, q1] using hz.1)
  have hsum := euclidean_sum_mem_diagonal hz.2
  apply euclidean_eq_planePoint_of_coordinates z 1 0
  · linarith
  · exact hy

private theorem e12_inter_e20_finite :
    (edgeCarrier e12 ∩ edgeCarrier e20).Finite := by
  apply (Set.finite_singleton (planeEuclideanHomeomorph q2)).subset
  intro z hz
  have hx : euclideanFirst z = 0 :=
    euclideanFirst_mem_verticalSegment (by
      simpa [e20, q0, q2] using hz.2)
  have hsum := euclidean_sum_mem_diagonal hz.1
  exact Set.mem_singleton_iff.mpr
    (euclidean_eq_planePoint_of_coordinates z 0 1 hx (by linarith))

private theorem e20_inter_e01_finite :
    (edgeCarrier e20 ∩ edgeCarrier e01).Finite := by
  apply (Set.finite_singleton (planeEuclideanHomeomorph q0)).subset
  intro z hz
  have hx : euclideanFirst z = 0 :=
    euclideanFirst_mem_verticalSegment (by
      simpa [e20, q0, q2] using hz.1)
  have hy : euclideanSecond z = 0 :=
    euclideanSecond_mem_horizontalSegment (by
      simpa [e01, q0, q1] using hz.2)
  exact Set.mem_singleton_iff.mpr
    (euclidean_eq_planePoint_of_coordinates z 0 0 hx hy)

theorem cycle_isReduced : IsReducedRepresentative cycle := by
  intro e he f hf hef
  rw [cycle_support] at he hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at he hf
  rcases he with rfl | rfl | rfl <;>
    rcases hf with rfl | rfl | rfl
  · exact (hef rfl).elim
  · exact e01_inter_e12_finite
  · simpa only [inter_comm] using e20_inter_e01_finite
  · simpa only [inter_comm] using e01_inter_e12_finite
  · exact (hef rfl).elim
  · exact e12_inter_e20_finite
  · exact e20_inter_e01_finite
  · simpa only [inter_comm] using e12_inter_e20_finite
  · exact (hef rfl).elim

/-- The noncollinear closed cycle consumes the reduced-carrier theorem; its
literal `H¹` is the sum of all three Euclidean edge lengths. -/
theorem hausdorffMeasure_oneCarrier_cycle_eq_formalMass :
    (μH[1] : Measure EuclideanPlane) (oneCarrier cycle) =
      formalMass cycle :=
  hausdorffMeasure_oneCarrier_eq_formalMass cycle cycle_isReduced

/-- The noncollinear closed triangle cycle consumes the quotient-level
geometric mass identification, not an endpoint calibration. -/
theorem geometricMass_cycle_eq_hausdorffMeasure_oneCarrier :
    geometricMass (toGeometric cycle) =
      (μH[1] : Measure EuclideanPlane) (oneCarrier cycle) :=
  geometricMass_toGeometric_eq_hausdorffMeasure_oneCarrier_of_reduced
    cycle cycle_isReduced

end NoncollinearCycle


namespace RectangularAnnulus

private abbrev r : FourRing := rectangularAnnulusRing
private def e0 : Edge := edge r.o0 r.o1 r.ho01
private def e1 : Edge := edge r.o1 r.o2 r.ho12
private def e2 : Edge := edge r.o2 r.o3 r.ho23
private def e3 : Edge := edge r.o3 r.o0 r.ho30
private def e4 : Edge := edge r.i1 r.i0 r.hi01.symm
private def e5 : Edge := edge r.i2 r.i1 r.hi12.symm
private def e6 : Edge := edge r.i3 r.i2 r.hi23.symm
private def e7 : Edge := edge r.i0 r.i3 r.hi30.symm

private theorem edgeCarrier_e0 :
    edgeCarrier e0 =
      segment ℝ (planeEuclideanHomeomorph ((-2, -2) : PlanePoint))
        (planeEuclideanHomeomorph ((2, -2) : PlanePoint)) := by
  simp [e0, r, rectangularAnnulusRing]

private theorem edgeCarrier_e1 :
    edgeCarrier e1 =
      segment ℝ (planeEuclideanHomeomorph ((2, -2) : PlanePoint))
        (planeEuclideanHomeomorph ((2, 2) : PlanePoint)) := by
  simp [e1, r, rectangularAnnulusRing]

private theorem edgeCarrier_e2 :
    edgeCarrier e2 =
      segment ℝ (planeEuclideanHomeomorph ((2, 2) : PlanePoint))
        (planeEuclideanHomeomorph ((-2, 2) : PlanePoint)) := by
  simp [e2, r, rectangularAnnulusRing]

private theorem edgeCarrier_e3 :
    edgeCarrier e3 =
      segment ℝ (planeEuclideanHomeomorph ((-2, 2) : PlanePoint))
        (planeEuclideanHomeomorph ((-2, -2) : PlanePoint)) := by
  simp [e3, r, rectangularAnnulusRing]

private theorem edgeCarrier_e4 :
    edgeCarrier e4 =
      segment ℝ (planeEuclideanHomeomorph ((1, -1) : PlanePoint))
        (planeEuclideanHomeomorph ((-1, -1) : PlanePoint)) := by
  simp [e4, r, rectangularAnnulusRing]

private theorem edgeCarrier_e5 :
    edgeCarrier e5 =
      segment ℝ (planeEuclideanHomeomorph ((1, 1) : PlanePoint))
        (planeEuclideanHomeomorph ((1, -1) : PlanePoint)) := by
  simp [e5, r, rectangularAnnulusRing]

private theorem edgeCarrier_e6 :
    edgeCarrier e6 =
      segment ℝ (planeEuclideanHomeomorph ((-1, 1) : PlanePoint))
        (planeEuclideanHomeomorph ((1, 1) : PlanePoint)) := by
  simp [e6, r, rectangularAnnulusRing]

private theorem edgeCarrier_e7 :
    edgeCarrier e7 =
      segment ℝ (planeEuclideanHomeomorph ((-1, -1) : PlanePoint))
        (planeEuclideanHomeomorph ((-1, 1) : PlanePoint)) := by
  simp [e7, r, rectangularAnnulusRing]

private theorem supported_edge_cases {e : Edge}
    (he : e ∈ (ringBoundary r).support) :
    e = e0 ∨ e = e1 ∨ e = e2 ∨ e = e3 ∨
      e = e4 ∨ e = e5 ∨ e = e6 ∨ e = e7 := by
  change e ∈
    (segmentChain r.o0 r.o1 r.ho01 +
      segmentChain r.o1 r.o2 r.ho12 +
      segmentChain r.o2 r.o3 r.ho23 +
      segmentChain r.o3 r.o0 r.ho30 +
      segmentChain r.i1 r.i0 r.hi01.symm +
      segmentChain r.i2 r.i1 r.hi12.symm +
      segmentChain r.i3 r.i2 r.hi23.symm +
      segmentChain r.i0 r.i3 r.hi30.symm).support at he
  have hsplit7 := Finsupp.support_add he
  simp only [Finset.mem_union] at hsplit7
  rcases hsplit7 with h0123456 | h7
  · have hsplit6 := Finsupp.support_add h0123456
    simp only [Finset.mem_union] at hsplit6
    rcases hsplit6 with h012345 | h6
    · have hsplit5 := Finsupp.support_add h012345
      simp only [Finset.mem_union] at hsplit5
      rcases hsplit5 with h01234 | h5
      · have hsplit4 := Finsupp.support_add h01234
        simp only [Finset.mem_union] at hsplit4
        rcases hsplit4 with h0123 | h4
        · have hsplit3 := Finsupp.support_add h0123
          simp only [Finset.mem_union] at hsplit3
          rcases hsplit3 with h012 | h3
          · have hsplit2 := Finsupp.support_add h012
            simp only [Finset.mem_union] at hsplit2
            rcases hsplit2 with h01 | h2
            · have hsplit1 := Finsupp.support_add h01
              simp only [Finset.mem_union] at hsplit1
              rcases hsplit1 with h0 | h1
              · exact Or.inl (by
                  simpa [segmentChain, e0] using h0)
              · exact Or.inr (Or.inl (by
                  simpa [segmentChain, e1] using h1))
            · exact Or.inr (Or.inr (Or.inl (by
                simpa [segmentChain, e2] using h2)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by
              simpa [segmentChain, e3] using h3))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
            simpa [segmentChain, e4] using h4)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
          simpa [segmentChain, e5] using h5))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
        simpa [segmentChain, e6] using h6)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
      simpa [segmentChain, e7] using h7)))))))

private def horizontalEdge : Fin 4 → Edge := ![e0, e2, e4, e6]
private def horizontalBase : Fin 4 → ℝ := ![-2, 2, -1, 1]
private def horizontalStart : Fin 4 → ℝ := ![-2, 2, 1, -1]
private def horizontalEnd : Fin 4 → ℝ := ![2, -2, -1, 1]

private def verticalEdge : Fin 4 → Edge := ![e1, e3, e5, e7]
private def verticalBase : Fin 4 → ℝ := ![2, -2, 1, -1]
private def verticalStart : Fin 4 → ℝ := ![-2, 2, 1, -1]
private def verticalEnd : Fin 4 → ℝ := ![2, -2, -1, 1]

private theorem horizontalEdge_carrier (i : Fin 4) :
    edgeCarrier (horizontalEdge i) =
      segment ℝ
        (planeEuclideanHomeomorph (horizontalStart i, horizontalBase i))
        (planeEuclideanHomeomorph (horizontalEnd i, horizontalBase i)) := by
  fin_cases i <;>
    simp [horizontalEdge, horizontalStart, horizontalEnd, horizontalBase,
      edgeCarrier_e0, edgeCarrier_e2, edgeCarrier_e4, edgeCarrier_e6]

private theorem verticalEdge_carrier (i : Fin 4) :
    edgeCarrier (verticalEdge i) =
      segment ℝ
        (planeEuclideanHomeomorph (verticalBase i, verticalStart i))
        (planeEuclideanHomeomorph (verticalBase i, verticalEnd i)) := by
  fin_cases i <;>
    simp [verticalEdge, verticalStart, verticalEnd, verticalBase,
      edgeCarrier_e1, edgeCarrier_e3, edgeCarrier_e5, edgeCarrier_e7]

private theorem horizontalBase_injective :
    Function.Injective horizontalBase := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [horizontalBase] <;>
    norm_num at h

private theorem verticalBase_injective :
    Function.Injective verticalBase := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [verticalBase] <;>
    norm_num at h

private theorem supported_edge_axis_index {e : Edge}
    (he : e ∈ (ringBoundary r).support) :
    (∃ i : Fin 4, e = horizontalEdge i) ∨
      ∃ i : Fin 4, e = verticalEdge i := by
  rcases supported_edge_cases he with
    h | h | h | h | h | h | h | h
  · exact Or.inl ⟨0, by simpa [horizontalEdge] using h⟩
  · exact Or.inr ⟨0, by simpa [verticalEdge] using h⟩
  · exact Or.inl ⟨1, by simpa [horizontalEdge] using h⟩
  · exact Or.inr ⟨1, by simpa [verticalEdge] using h⟩
  · exact Or.inl ⟨2, by simpa [horizontalEdge] using h⟩
  · exact Or.inr ⟨2, by simpa [verticalEdge] using h⟩
  · exact Or.inl ⟨3, by simpa [horizontalEdge] using h⟩
  · exact Or.inr ⟨3, by simpa [verticalEdge] using h⟩

/-- The actual outer-plus-inner square boundary has no positive-length overlap:
same-axis sides have distinct bases, and transverse sides meet in at most one
point. -/
theorem ringBoundary_isReduced :
    IsReducedRepresentative (ringBoundary rectangularAnnulusRing) := by
  intro e he f hf hef
  rcases supported_edge_axis_index he with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    rcases supported_edge_axis_index hf with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [horizontalEdge_carrier, horizontalEdge_carrier]
    apply horizontalSegments_inter_finite_of_base_ne
    intro hbase
    exact hef (congrArg horizontalEdge (horizontalBase_injective hbase))
  · rw [horizontalEdge_carrier, verticalEdge_carrier]
    exact horizontalSegment_inter_verticalSegment_finite
  · rw [verticalEdge_carrier, horizontalEdge_carrier]
    exact verticalSegment_inter_horizontalSegment_finite
  · rw [verticalEdge_carrier, verticalEdge_carrier]
    apply verticalSegments_inter_finite_of_base_ne
    intro hbase
    exact hef (congrArg verticalEdge (verticalBase_injective hbase))

/-- The concrete rectangular-annulus application uses all eight outer and inner
square edges, so its literal Euclidean `H¹` equals their reduced mass. -/
theorem hausdorffMeasure_oneCarrier_ringBoundary_eq_formalMass :
    (μH[1] : Measure EuclideanPlane)
        (oneCarrier (ringBoundary rectangularAnnulusRing)) =
      formalMass (ringBoundary rectangularAnnulusRing) :=
  hausdorffMeasure_oneCarrier_eq_formalMass _
    ringBoundary_isReduced

/-- Both components of the rectangular annulus consume the quotient-level
geometric mass identification simultaneously. -/
theorem geometricMass_ringBoundary_eq_hausdorffMeasure_oneCarrier :
    geometricMass (toGeometric (ringBoundary rectangularAnnulusRing)) =
      (μH[1] : Measure EuclideanPlane)
        (oneCarrier (ringBoundary rectangularAnnulusRing)) :=
  geometricMass_toGeometric_eq_hausdorffMeasure_oneCarrier_of_reduced _
    ringBoundary_isReduced

end RectangularAnnulus

end CMVPolygonalModTwo
