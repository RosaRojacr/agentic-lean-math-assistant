import CMVOrientedLoopCycles
import Mathlib.Topology.Subpath

/-!
# Geometric realization of finite boundary traversals

The finite chart-cut system already identifies each open boundary arc with one
nondegenerate real interval.  This file normalizes that actual compact arc to
the unit interval and then orients it from any incident half-edge to the other
endpoint.  The result is a genuine `PlanePoint`-valued path for every
combinatorial traversal step.

These paths are topological realizations only.  No differentiability, metric
length, occupied-side orientation, or winding conclusion is asserted here.
-/

open Set Function
open scoped Topology unitInterval

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace BoundaryHalfSpaceAtlas
namespace FiniteChartCutSystem

variable {O : Set PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- The left real chart parameter of one quotient-indexed compact arc. -/
noncomputable def finiteArcLowerParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) : ℝ :=
  sInf (D.cutComponentRealParameterImage (D.finiteArcChart e)
    (D.arcRepresentative e))

/-- The right real chart parameter of one quotient-indexed compact arc. -/
noncomputable def finiteArcUpperParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) : ℝ :=
  sSup (D.cutComponentRealParameterImage (D.finiteArcChart e)
    (D.arcRepresentative e))

/-- Every selected compact arc has a genuinely positive parameter interval. -/
theorem finiteArcLowerParameter_lt_upperParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcLowerParameter e < D.finiteArcUpperParameter e := by
  exact D.cutComponentRealParameter_sInf_lt_sSup
    (D.finiteArcChart e) (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)

/-- Affine normalization of the unit interval into the selected compact-core
coordinates of one actual boundary arc. -/
noncomputable def finiteArcUnitCoreParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) (t : unitInterval) :
    (D.arc (D.finiteArcChart e)).CoreParameter := by
  let a := D.finiteArcLowerParameter e
  let b := D.finiteArcUpperParameter e
  let z : ℝ := a + (t : ℝ) * (b - a)
  have hab : a < b := D.finiteArcLowerParameter_lt_upperParameter e
  have hzab : z ∈ Icc a b := by
    dsimp only [z]
    constructor <;> nlinarith [t.property.1, t.property.2]
  have hends := D.cutComponentRealParameter_endpoints_mem_core
    (D.finiteArcChart e) (D.arcRepresentative e)
    (D.arcRepresentative_mem_finiteArcChart_coreInterior e)
  exact ⟨z, hends.1.1.trans hzab.1, hzab.2.trans hends.2.2⟩

@[simp] theorem finiteArcUnitCoreParameter_zero
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcUnitCoreParameter e 0 =
      D.cutComponentLeftCoreParameter (D.finiteArcChart e)
        (D.arcRepresentative e)
        (D.arcRepresentative_mem_finiteArcChart_coreInterior e) := by
  apply Subtype.ext
  simp [finiteArcUnitCoreParameter, finiteArcLowerParameter,
    cutComponentLeftCoreParameter]

@[simp] theorem finiteArcUnitCoreParameter_one
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcUnitCoreParameter e 1 =
      D.cutComponentRightCoreParameter (D.finiteArcChart e)
        (D.arcRepresentative e)
        (D.arcRepresentative_mem_finiteArcChart_coreInterior e) := by
  apply Subtype.ext
  simp [finiteArcUnitCoreParameter, finiteArcLowerParameter,
    finiteArcUpperParameter, cutComponentRightCoreParameter]

/-- The affine compact-core normalization is continuous. -/
theorem continuous_finiteArcUnitCoreParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Continuous (D.finiteArcUnitCoreParameter e) := by
  apply Continuous.subtype_mk
  change Continuous (fun t : unitInterval =>
    D.finiteArcLowerParameter e + (t : ℝ) *
      (D.finiteArcUpperParameter e - D.finiteArcLowerParameter e))
  fun_prop

/-- The affine compact-core normalization does not repeat a parameter. -/
theorem injective_finiteArcUnitCoreParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Function.Injective (D.finiteArcUnitCoreParameter e) := by
  intro s t hst
  have hval := congrArg (fun z :
      (D.arc (D.finiteArcChart e)).CoreParameter => (z : ℝ)) hst
  change D.finiteArcLowerParameter e + (s : ℝ) *
      (D.finiteArcUpperParameter e - D.finiteArcLowerParameter e) =
    D.finiteArcLowerParameter e + (t : ℝ) *
      (D.finiteArcUpperParameter e - D.finiteArcLowerParameter e) at hval
  have hpos : 0 < D.finiteArcUpperParameter e -
      D.finiteArcLowerParameter e :=
    sub_pos.mpr (D.finiteArcLowerParameter_lt_upperParameter e)
  apply Subtype.ext
  nlinarith

/-- Increasing affine parameters fill exactly the closed parameter set used by
the selected compact arc. -/
theorem range_finiteArcUnitCoreParameter
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Set.range (D.finiteArcUnitCoreParameter e) =
      D.cutComponentClosedCoreParameterSet (D.finiteArcChart e)
        (D.arcRepresentative e) := by
  apply Subset.antisymm
  · rintro z ⟨t, rfl⟩
    change (D.finiteArcUnitCoreParameter e t : ℝ) ∈
      Icc (D.finiteArcLowerParameter e) (D.finiteArcUpperParameter e)
    have hab := D.finiteArcLowerParameter_lt_upperParameter e
    change D.finiteArcLowerParameter e ≤
        D.finiteArcLowerParameter e + (t : ℝ) *
          (D.finiteArcUpperParameter e - D.finiteArcLowerParameter e) ∧
      D.finiteArcLowerParameter e + (t : ℝ) *
          (D.finiteArcUpperParameter e - D.finiteArcLowerParameter e) ≤
        D.finiteArcUpperParameter e
    constructor <;> nlinarith [t.property.1, t.property.2]
  · intro z hz
    let a := D.finiteArcLowerParameter e
    let b := D.finiteArcUpperParameter e
    have hab : 0 < b - a :=
      sub_pos.mpr (D.finiteArcLowerParameter_lt_upperParameter e)
    have hzab : (z : ℝ) ∈ Icc a b := by
      change (z : ℝ) ∈ Icc
        (D.finiteArcLowerParameter e) (D.finiteArcUpperParameter e) at hz
      simpa only [a, b] using hz
    let t : unitInterval :=
      ⟨((z : ℝ) - a) / (b - a), by
        constructor
        · exact div_nonneg (sub_nonneg.mpr hzab.1) hab.le
        · exact (div_le_one hab).2 (sub_le_iff_le_add.mpr (by simpa using hzab.2))⟩
    refine ⟨t, ?_⟩
    apply Subtype.ext
    dsimp only [finiteArcUnitCoreParameter, t, a, b]
    rw [div_mul_cancel₀ _ hab.ne']
    ring

/-- The selected embedded compact arc, normalized from left endpoint to right
endpoint on the unit interval. -/
noncomputable def finiteArcPathLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Path (D.finiteArcLeftEndpoint e).1 (D.finiteArcRightEndpoint e).1 where
  toFun t :=
    ((D.arc (D.finiteArcChart e)).corePoint
      (D.finiteArcUnitCoreParameter e t)).1
  continuous_toFun :=
    continuous_subtype_val.comp
      ((D.arc (D.finiteArcChart e)).continuous_corePoint.comp
        (D.continuous_finiteArcUnitCoreParameter e))
  source' := by
    rw [D.finiteArcUnitCoreParameter_zero]
    rfl
  target' := by
    rw [D.finiteArcUnitCoreParameter_one]
    rfl

/-- The frontier-subtype lift of the selected left-to-right compact arc path.
Unlike `finiteArcPathLR`, this retains membership in the actual frontier. -/
noncomputable def finiteArcPointLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (t : unitInterval) : FrontierSpace O :=
  (D.arc (D.finiteArcChart e)).corePoint
    (D.finiteArcUnitCoreParameter e t)

@[simp] theorem finiteArcPointLR_val
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (t : unitInterval) :
    (D.finiteArcPointLR e t : PlanePoint) = D.finiteArcPathLR e t :=
  rfl

theorem finiteArcPathLR_mem_frontier
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (t : unitInterval) :
    D.finiteArcPathLR e t ∈ frontier O :=
  (D.finiteArcPointLR e t).2

@[simp] theorem finiteArcPointLR_zero
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcPointLR e 0 = D.finiteArcLeftEndpoint e := by
  apply Subtype.ext
  exact (D.finiteArcPathLR e).source

@[simp] theorem finiteArcPointLR_one
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcPointLR e 1 = D.finiteArcRightEndpoint e := by
  apply Subtype.ext
  exact (D.finiteArcPathLR e).target

/-- Every normalized compact-arc point belongs to the selected arc closure. -/
theorem finiteArcPointLR_mem_finiteArcClosure
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (t : unitInterval) :
    D.finiteArcPointLR e t ∈ D.finiteArcClosure e := by
  rw [D.finiteArcClosure_eq_selectedClosedArc]
  refine ⟨D.finiteArcUnitCoreParameter e t, ?_, rfl⟩
  rw [← D.range_finiteArcUnitCoreParameter e]
  exact ⟨t, rfl⟩

/-- The selected frontier-subtype arc path does not repeat a point. -/
theorem finiteArcPointLR_injective
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Function.Injective (D.finiteArcPointLR e) := by
  intro s t hst
  exact D.injective_finiteArcUnitCoreParameter e
    ((D.arc (D.finiteArcChart e)).injective_corePoint hst)

/-- Exactly the strict unit parameters lie on the open finite arc; the two
closed-unit endpoints are exactly the two selected cut endpoints. -/
theorem finiteArcPointLR_mem_finiteArcInterior_iff
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (t : unitInterval) :
    D.finiteArcPointLR e t ∈ D.finiteArcInterior e ↔
      (t : ℝ) ∈ Ioo 0 1 := by
  have hleft :
      D.finiteArcLeftEndpoint e ∉ D.finiteArcInterior e := by
    intro hleftInterior
    have hboundary :
        D.finiteArcLeftEndpoint e ∈
          D.finiteArcClosure e \ D.finiteArcInterior e := by
      rw [D.finiteArcClosure_sdiff_finiteArcInterior e]
      exact Set.mem_insert _ _
    exact hboundary.2 hleftInterior
  have hright :
      D.finiteArcRightEndpoint e ∉ D.finiteArcInterior e := by
    intro hrightInterior
    have hboundary :
        D.finiteArcRightEndpoint e ∈
          D.finiteArcClosure e \ D.finiteArcInterior e := by
      rw [D.finiteArcClosure_sdiff_finiteArcInterior e]
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))
    exact hboundary.2 hrightInterior
  constructor
  · intro hinterior
    have htZero : (t : ℝ) ≠ 0 := by
      intro ht
      have htSubtype : t = (0 : unitInterval) := Subtype.ext ht
      subst t
      exact hleft (by simpa only [D.finiteArcPointLR_zero] using hinterior)
    have htOne : (t : ℝ) ≠ 1 := by
      intro ht
      have htSubtype : t = (1 : unitInterval) := Subtype.ext ht
      subst t
      exact hright (by simpa only [D.finiteArcPointLR_one] using hinterior)
    exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm htZero),
      lt_of_le_of_ne t.2.2 htOne⟩
  · intro ht
    by_contra hnotInterior
    have hboundary :
        D.finiteArcPointLR e t ∈
          D.finiteArcClosure e \ D.finiteArcInterior e :=
      ⟨D.finiteArcPointLR_mem_finiteArcClosure e t, hnotInterior⟩
    rw [D.finiteArcClosure_sdiff_finiteArcInterior e] at hboundary
    rcases hboundary with hleftEq | hrightEq
    · have htEq : t = (0 : unitInterval) :=
        D.finiteArcPointLR_injective e
          (hleftEq.trans (D.finiteArcPointLR_zero e).symm)
      subst t
      exact (by norm_num : ¬ ((0 : ℝ) < 0)) ht.1
    · have htEq : t = (1 : unitInterval) :=
        D.finiteArcPointLR_injective e
          (hrightEq.trans (D.finiteArcPointLR_one e).symm)
      subst t
      exact (by norm_num : ¬ ((1 : ℝ) < 1)) ht.2

theorem finiteArcPathLR_mem_finiteArcInterior_iff
    (D : FiniteChartCutSystem A) (e : D.ArcIndex)
    (t : unitInterval) :
    (⟨D.finiteArcPathLR e t, D.finiteArcPathLR_mem_frontier e t⟩ :
        FrontierSpace O) ∈ D.finiteArcInterior e ↔
      (t : ℝ) ∈ Ioo 0 1 :=
  D.finiteArcPointLR_mem_finiteArcInterior_iff e t

/-- The frontier-subtype path fills exactly the selected compact arc. -/
theorem range_finiteArcPointLR
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Set.range (D.finiteArcPointLR e) = D.finiteArcClosure e := by
  apply Subset.antisymm
  · rintro q ⟨t, rfl⟩
    exact D.finiteArcPointLR_mem_finiteArcClosure e t
  · intro q hq
    rw [D.finiteArcClosure_eq_selectedClosedArc] at hq
    rcases hq with ⟨s, hs, rfl⟩
    have hsRange : s ∈ Set.range (D.finiteArcUnitCoreParameter e) := by
      rw [D.range_finiteArcUnitCoreParameter e]
      exact hs
    rcases hsRange with ⟨t, rfl⟩
    exact ⟨t, rfl⟩

/-- Restricting the normalized compact-arc path to strict unit parameters
fills exactly the actual open finite arc. -/
theorem image_finiteArcPointLR_openUnitInterval
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.finiteArcPointLR e '' {t : unitInterval | (t : ℝ) ∈ Ioo 0 1} =
      D.finiteArcInterior e := by
  apply Subset.antisymm
  · rintro q ⟨t, ht, rfl⟩
    exact (D.finiteArcPointLR_mem_finiteArcInterior_iff e t).2 ht
  · intro q hq
    have hclosure : q ∈ D.finiteArcClosure e := by
      exact subset_closure hq
    have hrange : q ∈ Set.range (D.finiteArcPointLR e) := by
      rw [D.range_finiteArcPointLR e]
      exact hclosure
    rcases hrange with ⟨t, rfl⟩
    exact ⟨t,
      (D.finiteArcPointLR_mem_finiteArcInterior_iff e t).1 hq, rfl⟩

/-- A normalized compact arc path never retraces. -/
theorem finiteArcPathLR_injective
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Function.Injective (D.finiteArcPathLR e) := by
  intro s t hst
  have hfrontier :
      (D.arc (D.finiteArcChart e)).corePoint
          (D.finiteArcUnitCoreParameter e s) =
        (D.arc (D.finiteArcChart e)).corePoint
          (D.finiteArcUnitCoreParameter e t) :=
    Subtype.ext hst
  exact D.injective_finiteArcUnitCoreParameter e
    ((D.arc (D.finiteArcChart e)).injective_corePoint hfrontier)

/-- The normalized path realizes exactly the actual compact arc, including both
cut endpoints. -/
theorem finiteArcPathLR_range
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    Set.range (D.finiteArcPathLR e) =
      Subtype.val '' D.finiteArcClosure e := by
  apply Subset.antisymm
  · rintro q ⟨t, rfl⟩
    refine ⟨(D.arc (D.finiteArcChart e)).corePoint
      (D.finiteArcUnitCoreParameter e t), ?_, rfl⟩
    rw [D.finiteArcClosure_eq_selectedClosedArc]
    exact ⟨D.finiteArcUnitCoreParameter e t, by
      rw [← D.range_finiteArcUnitCoreParameter e]
      exact ⟨t, rfl⟩, rfl⟩
  · rintro q ⟨z, hz, rfl⟩
    rw [D.finiteArcClosure_eq_selectedClosedArc] at hz
    rcases hz with ⟨s, hs, rfl⟩
    have hsRange : s ∈ Set.range (D.finiteArcUnitCoreParameter e) := by
      rw [D.range_finiteArcUnitCoreParameter e]
      exact hs
    rcases hsRange with ⟨t, rfl⟩
    exact ⟨t, rfl⟩

/-- Distinct compact arc closures can meet only at endpoints of both arcs. -/
theorem finiteArcClosure_inter_subset_endpointPairs
    (D : FiniteChartCutSystem A) {e f : D.ArcIndex} (hef : e ≠ f) :
    D.finiteArcClosure e ∩ D.finiteArcClosure f ⊆
      ({D.finiteArcLeftEndpoint e, D.finiteArcRightEndpoint e} :
          Set (FrontierSpace O)) ∩
        ({D.finiteArcLeftEndpoint f, D.finiteArcRightEndpoint f} :
          Set (FrontierSpace O)) := by
  intro q hq
  have endpoint_of_not_interior (g : D.ArcIndex)
      (hqClosure : q ∈ D.finiteArcClosure g)
      (hqInterior : q ∉ D.finiteArcInterior g) :
      q ∈ ({D.finiteArcLeftEndpoint g, D.finiteArcRightEndpoint g} :
        Set (FrontierSpace O)) := by
    have hboundary :
        q ∈ D.finiteArcClosure g \ D.finiteArcInterior g :=
      ⟨hqClosure, hqInterior⟩
    rw [D.finiteArcClosure_sdiff_finiteArcInterior g] at hboundary
    exact hboundary
  have heNotInterior : q ∉ D.finiteArcInterior e := by
    intro hqe
    by_cases hqf : q ∈ D.finiteArcInterior f
    · exact Set.disjoint_left.1 (D.disjoint_finiteArcInterior hef) hqe hqf
    · have hfEnd := endpoint_of_not_interior f hq.2 hqf
      have hqCut : q ∈ D.cutPoints := by
        rcases hfEnd with hleft | hright
        · rw [hleft]
          exact (D.finiteArc_endpoints_mem_cutPoints f).1
        · rw [hright]
          exact (D.finiteArc_endpoints_mem_cutPoints f).2
      exact (D.finiteArcInterior_subset_cutSpaceCarrier e hqe) hqCut
  have hfNotInterior : q ∉ D.finiteArcInterior f := by
    intro hqf
    have heEnd := endpoint_of_not_interior e hq.1 heNotInterior
    have hqCut : q ∈ D.cutPoints := by
      rcases heEnd with hleft | hright
      · rw [hleft]
        exact (D.finiteArc_endpoints_mem_cutPoints e).1
      · rw [hright]
        exact (D.finiteArc_endpoints_mem_cutPoints e).2
    exact (D.finiteArcInterior_subset_cutSpaceCarrier f hqf) hqCut
  exact ⟨endpoint_of_not_interior e hq.1 heNotInterior,
    endpoint_of_not_interior f hq.2 hfNotInterior⟩

/-- The once-indexed normalized arc paths cover the complete actual frontier.
This family uses one path per quotient arc, rather than both endpoint
orientations of every half-edge. -/
theorem iUnion_finiteArcPathLR_range_eq_frontier
    (D : FiniteChartCutSystem A) :
    (⋃ e : D.ArcIndex, Set.range (D.finiteArcPathLR e)) =
      frontier O := by
  apply Subset.antisymm
  · intro q hq
    obtain ⟨e, hqe⟩ := Set.mem_iUnion.mp hq
    rw [D.finiteArcPathLR_range] at hqe
    obtain ⟨p, hp, rfl⟩ := hqe
    exact p.2
  · intro q hq
    let p : FrontierSpace O := ⟨q, hq⟩
    have hpAll :
        p ∈ ⋃ e : D.ArcIndex, D.finiteArcClosure e := by
      rw [D.iUnion_finiteArcClosure_eq_univ]
      exact Set.mem_univ p
    obtain ⟨e, hpe⟩ := Set.mem_iUnion.mp hpAll
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    rw [D.finiteArcPathLR_range]
    exact ⟨p, hpe, rfl⟩

/-- Distinct once-indexed path images overlap only at named endpoints of both
arcs.  In particular, the complete cover has no positive-length retracing. -/
theorem finiteArcPathLR_range_inter_subset_endpointValues
    (D : FiniteChartCutSystem A) {e f : D.ArcIndex} (hef : e ≠ f) :
    Set.range (D.finiteArcPathLR e) ∩
        Set.range (D.finiteArcPathLR f) ⊆
      ({(D.finiteArcLeftEndpoint e).1,
          (D.finiteArcRightEndpoint e).1} : Set PlanePoint) ∩
        ({(D.finiteArcLeftEndpoint f).1,
          (D.finiteArcRightEndpoint f).1} : Set PlanePoint) := by
  intro q hq
  rw [D.finiteArcPathLR_range e, D.finiteArcPathLR_range f] at hq
  rcases hq.1 with ⟨pe, hpe, hpeq⟩
  rcases hq.2 with ⟨pf, hpf, hpfq⟩
  have heq : pe = pf := by
    apply Subtype.ext
    exact hpeq.trans hpfq.symm
  subst pf
  have hend :=
    D.finiteArcClosure_inter_subset_endpointPairs hef ⟨hpe, hpf⟩
  simp only [Set.mem_inter_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hend ⊢
  constructor
  · rcases hend.1 with he | he
    · left
      exact hpeq.symm.trans (congrArg Subtype.val he)
    · right
      exact hpeq.symm.trans (congrArg Subtype.val he)
  · rcases hend.2 with hf | hf
    · left
      exact hpeq.symm.trans (congrArg Subtype.val hf)
    · right
      exact hpeq.symm.trans (congrArg Subtype.val hf)

/-- Contract for a once-indexed embedded path inventory of the complete
frontier with only endpoint overlap between distinct compact arcs. -/
def HasNonduplicatingFiniteArcPathCover
    (D : FiniteChartCutSystem A) : Prop :=
  (∀ e : D.ArcIndex, Function.Injective (D.finiteArcPathLR e)) ∧
    (⋃ e : D.ArcIndex, Set.range (D.finiteArcPathLR e)) = frontier O ∧
    ∀ ⦃e f : D.ArcIndex⦄, e ≠ f →
      Set.range (D.finiteArcPathLR e) ∩
          Set.range (D.finiteArcPathLR f) ⊆
        ({(D.finiteArcLeftEndpoint e).1,
            (D.finiteArcRightEndpoint e).1} : Set PlanePoint) ∩
          ({(D.finiteArcLeftEndpoint f).1,
            (D.finiteArcRightEndpoint f).1} : Set PlanePoint)

/-- Complete nonduplicating geometric inventory before cyclic orientation:
one embedded path per finite quotient arc, complete frontier coverage, and only
endpoint overlap between distinct paths. -/
theorem finiteArcPathLR_nonduplicating_cover
    (D : FiniteChartCutSystem A) :
    D.HasNonduplicatingFiniteArcPathCover := by
  unfold HasNonduplicatingFiniteArcPathCover
  exact
    ⟨D.finiteArcPathLR_injective,
      D.iUnion_finiteArcPathLR_range_eq_frontier,
      fun {_e _f} hef =>
        D.finiteArcPathLR_range_inter_subset_endpointValues hef⟩

@[simp] theorem crossHalfEdge_endpointHalfEdge
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) (b : Bool) :
    D.crossHalfEdge (D.endpointHalfEdge (e, b)) =
      D.endpointHalfEdge (e, !b) := by
  unfold crossHalfEdge
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply,
    endpointHalfEdgeEquiv_symm_endpointHalfEdge, endpointHalfEdgeEquiv_apply]
  rfl

/-- Crossing an arc twice returns to the original incident endpoint. -/
@[simp] theorem crossHalfEdge_crossHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.crossHalfEdge (D.crossHalfEdge h) = h := by
  obtain ⟨p, rfl⟩ := D.endpointHalfEdge_surjective h
  rcases p with ⟨e, b⟩
  rw [D.crossHalfEdge_endpointHalfEdge,
    D.crossHalfEdge_endpointHalfEdge]
  simp

/-- Crossing an arc always reaches its distinct endpoint. -/
theorem crossHalfEdge_ne
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.crossHalfEdge h ≠ h := by
  obtain ⟨p, rfl⟩ := D.endpointHalfEdge_surjective h
  rcases p with ⟨e, b⟩
  rw [D.crossHalfEdge_endpointHalfEdge]
  cases b
  · intro heq
    apply D.leftVertex_ne_rightVertex e
    exact (congrArg (fun z : D.HalfEdge => z.1.1) heq).symm
  · intro heq
    apply D.leftVertex_ne_rightVertex e
    exact congrArg (fun z : D.HalfEdge => z.1.1) heq

/-- Two half-edges of the same compact arc are either equal or exchanged by
the endpoint-crossing involution. -/
theorem eq_or_eq_crossHalfEdge_of_arc_eq
    (D : FiniteChartCutSystem A) {h g : D.HalfEdge}
    (harc : h.1.2 = g.1.2) :
    h = g ∨ h = D.crossHalfEdge g := by
  obtain ⟨ph, rfl⟩ := D.endpointHalfEdge_surjective h
  obtain ⟨pg, rfl⟩ := D.endpointHalfEdge_surjective g
  rcases ph with ⟨e, b⟩
  rcases pg with ⟨f, c⟩
  simp only [D.endpointHalfEdge_arc] at harc
  subst f
  cases b <;> cases c <;> simp

@[simp] theorem switchHalfEdge_vertex
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    (D.switchHalfEdge h).1.1 = h.1.1 := by
  rfl

/-- Switching at a cut vertex selects the other incident compact arc. -/
theorem switchHalfEdge_arc_ne
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    (D.switchHalfEdge h).1.2 ≠ h.1.2 := by
  intro harc
  apply (D.cutPointCoreNeighborhood h.1.1).otherIncidentArc_ne
    (D.incidentAtHalfEdge h)
  apply Subtype.ext
  exact harc

/-- The underlying continuous map of one compact arc, directed away from an
arbitrary incident half-edge. -/
noncomputable def halfEdgeArcMap
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    C(unitInterval, PlanePoint) :=
  let p := D.endpointHalfEdgeEquiv.symm h
  if p.2 then (D.finiteArcPathLR p.1).symm.toContinuousMap
  else (D.finiteArcPathLR p.1).toContinuousMap

@[simp] theorem halfEdgeArcMap_zero
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.halfEdgeArcMap h 0 = h.1.1.1.1 := by
  let p := D.endpointHalfEdgeEquiv.symm h
  have hp : D.endpointHalfEdge p = h := by
    rw [← D.endpointHalfEdgeEquiv_apply]
    exact D.endpointHalfEdgeEquiv.apply_symm_apply h
  rw [← hp]
  rcases p with ⟨e, b⟩
  cases b
  · simp [halfEdgeArcMap, Bool.false_eq_true]
    rfl
  · simp [halfEdgeArcMap]
    rfl

@[simp] theorem halfEdgeArcMap_one
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.halfEdgeArcMap h 1 = (D.crossHalfEdge h).1.1.1.1 := by
  let p := D.endpointHalfEdgeEquiv.symm h
  have hp : D.endpointHalfEdge p = h := by
    rw [← D.endpointHalfEdgeEquiv_apply]
    exact D.endpointHalfEdgeEquiv.apply_symm_apply h
  rw [← hp]
  rcases p with ⟨e, b⟩
  cases b
  · simp [halfEdgeArcMap, Bool.false_eq_true]
    rfl
  · simp [halfEdgeArcMap]
    rfl

/-- One compact arc oriented from an arbitrary incident half-edge to the other
endpoint.  The Boolean endpoint coordinate is derived from the existing
endpoint equivalence. -/
noncomputable def halfEdgeArcPath
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Path h.1.1.1.1 (D.crossHalfEdge h).1.1.1.1 where
  toContinuousMap := D.halfEdgeArcMap h
  source' := D.halfEdgeArcMap_zero h
  target' := D.halfEdgeArcMap_one h

/-- Directing a compact arc from either endpoint preserves embeddedness. -/
theorem halfEdgeArcPath_injective
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Function.Injective (D.halfEdgeArcPath h) := by
  let p := D.endpointHalfEdgeEquiv.symm h
  have hp : D.endpointHalfEdge p = h := by
    rw [← D.endpointHalfEdgeEquiv_apply]
    exact D.endpointHalfEdgeEquiv.apply_symm_apply h
  rw [← hp]
  rcases p with ⟨e, b⟩
  cases b
  · simp [halfEdgeArcPath, halfEdgeArcMap, Bool.false_eq_true]
    rw [D.endpointHalfEdgeEquiv_symm_endpointHalfEdge]
    exact D.finiteArcPathLR_injective e
  · simp [halfEdgeArcPath, halfEdgeArcMap]
    rw [D.endpointHalfEdgeEquiv_symm_endpointHalfEdge]
    exact (D.finiteArcPathLR_injective e).comp
      unitInterval.symm_bijective.injective

/-- The continuous half-edge map has exactly the image of its underlying
compact arc. -/
theorem halfEdgeArcMap_range
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Set.range (D.halfEdgeArcMap h) =
      Subtype.val '' D.finiteArcClosure h.1.2 := by
  let p := D.endpointHalfEdgeEquiv.symm h
  have hp : D.endpointHalfEdge p = h := by
    rw [← D.endpointHalfEdgeEquiv_apply]
    exact D.endpointHalfEdgeEquiv.apply_symm_apply h
  rw [← hp]
  rcases p with ⟨e, b⟩
  cases b
  · simp [halfEdgeArcMap, Bool.false_eq_true]
    rw [D.endpointHalfEdgeEquiv_symm_endpointHalfEdge]
    exact D.finiteArcPathLR_range e
  · simp [halfEdgeArcMap]
    rw [D.endpointHalfEdgeEquiv_symm_endpointHalfEdge]
    exact D.finiteArcPathLR_range e

/-- A half-edge path has exactly the image of its underlying compact arc. -/
theorem halfEdgeArcPath_range
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Set.range (D.halfEdgeArcPath h) =
      Subtype.val '' D.finiteArcClosure h.1.2 := by
  change Set.range (D.halfEdgeArcMap h) =
    Subtype.val '' D.finiteArcClosure h.1.2
  exact D.halfEdgeArcMap_range h

/-- The two half-edge realizations of one arc are precisely the opposite
endpoint directions: they have the same image and exchange start with finish.
Thus retaining both would duplicate the complete geometric arc. -/
theorem halfEdgeArcPath_cross_opposite
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Set.range (D.halfEdgeArcPath (D.crossHalfEdge h)) =
        Set.range (D.halfEdgeArcPath h) ∧
      D.halfEdgeArcPath (D.crossHalfEdge h) 0 =
        D.halfEdgeArcPath h 1 ∧
      D.halfEdgeArcPath (D.crossHalfEdge h) 1 =
        D.halfEdgeArcPath h 0 := by
  constructor
  · rw [D.halfEdgeArcPath_range, D.halfEdgeArcPath_range,
      D.crossHalfEdge_arc]
  constructor
  · change D.halfEdgeArcMap (D.crossHalfEdge h) 0 =
      D.halfEdgeArcMap h 1
    rw [D.halfEdgeArcMap_zero, D.halfEdgeArcMap_one]
  · change D.halfEdgeArcMap (D.crossHalfEdge h) 1 =
      D.halfEdgeArcMap h 0
    rw [D.halfEdgeArcMap_one, D.halfEdgeArcMap_zero,
      D.crossHalfEdge_crossHalfEdge]

/-- The geometric piece traversed by one combinatorial walk step.  `walkStep`
first switches to the other incident arc and then crosses that arc. -/
noncomputable def walkArcPath
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Path h.1.1.1.1 (D.walkStep h).1.1.1.1 :=
  (D.halfEdgeArcPath (D.switchHalfEdge h)).cast
    (congrArg (fun v : D.cutPoints => v.1.1)
      (D.switchHalfEdge_vertex h).symm) rfl

/-- Every geometric walk step is an embedded compact arc. -/
theorem walkArcPath_injective
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Function.Injective (D.walkArcPath h) := by
  change Function.Injective (D.halfEdgeArcPath (D.switchHalfEdge h))
  exact D.halfEdgeArcPath_injective (D.switchHalfEdge h)

/-- A traversal piece realizes exactly the compact arc selected by the switch
at its initial vertex. -/
theorem walkArcPath_range
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Set.range (D.walkArcPath h) =
      Subtype.val '' D.finiteArcClosure (D.switchHalfEdge h).1.2 := by
  change Set.range (D.halfEdgeArcPath (D.switchHalfEdge h)) =
    Subtype.val '' D.finiteArcClosure (D.switchHalfEdge h).1.2
  exact D.halfEdgeArcPath_range (D.switchHalfEdge h)

/-- Every traversal piece lies on the actual cropped frontier. -/
theorem walkArcPath_range_subset_frontier
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Set.range (D.walkArcPath h) ⊆ frontier O := by
  rw [D.walkArcPath_range]
  rintro q ⟨p, -, rfl⟩
  exact p.2

/-- Concatenate a positive number of actual arc traversals without inserting a
stationary `Path.refl` segment.  Index `n` represents exactly `n + 1` pieces. -/
noncomputable def walkArcPathConcatPositive
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    (n : ℕ) →
      Path e.1.1.1.1
        ((((D.walkStep : D.HalfEdge → D.HalfEdge)^[n + 1]) e).1.1.1.1)
  | 0 =>
      (D.walkArcPath e).cast rfl
        (congrArg (fun h : D.HalfEdge => h.1.1.1.1)
          (congrFun (Function.iterate_one (D.walkStep :
            D.HalfEdge → D.HalfEdge)) e))
  | n + 1 =>
      (D.walkArcPathConcatPositive e n).trans
        ((D.walkArcPath
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n + 1]) e)).cast
          rfl
          (congrArg (fun h : D.HalfEdge => h.1.1.1.1)
            (Function.iterate_succ_apply'
              (f := (D.walkStep : D.HalfEdge → D.HalfEdge)) (n + 1) e)))

/-- Concatenate the first `k` actual arc traversals starting at `e`.  The zero
case is constant; every positive case starts immediately with the first actual
arc, so no stationary prefix is introduced. -/
noncomputable def walkArcPathConcat
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    (k : ℕ) →
      Path e.1.1.1.1
        ((((D.walkStep : D.HalfEdge → D.HalfEdge)^[k]) e).1.1.1.1)
  | 0 => Path.refl e.1.1.1.1
  | n + 1 => D.walkArcPathConcatPositive e n

/-- The positive concatenation never leaves the cropped frontier. -/
theorem walkArcPathConcatPositive_range_subset_frontier
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) (n : ℕ) :
    Set.range (D.walkArcPathConcatPositive e n) ⊆ frontier O := by
  induction n with
  | zero =>
      change Set.range (D.walkArcPath e) ⊆ frontier O
      exact D.walkArcPath_range_subset_frontier e
  | succ n ih =>
      rw [walkArcPathConcatPositive, Path.trans_range]
      exact Set.union_subset ih (D.walkArcPath_range_subset_frontier _)
/-- A one-piece concatenation is the original embedded arc, not a path with a
constant initial half.  This regression theorem rules out the old
`Path.refl.trans` parameterization. -/
theorem walkArcPathConcat_one_injective
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    Function.Injective (D.walkArcPathConcat e 1) := by
  change Function.Injective (D.walkArcPath e)
  exact D.walkArcPath_injective e


/-- The finite concatenation never leaves the cropped frontier. -/
theorem walkArcPathConcat_range_subset_frontier
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) (k : ℕ) :
    Set.range (D.walkArcPathConcat e k) ⊆ frontier O := by
  cases k with
  | zero =>
      rintro q ⟨t, rfl⟩
      change e.1.1.1.1 ∈ frontier O
      exact e.1.1.1.2
  | succ n =>
      exact D.walkArcPathConcatPositive_range_subset_frontier e n

/-- Exact range membership for a pause-free positive concatenation. -/
theorem mem_range_walkArcPathConcatPositive_iff
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) (n : ℕ)
    (q : PlanePoint) :
    q ∈ Set.range (D.walkArcPathConcatPositive e n) ↔
      ∃ i : ℕ, i < n + 1 ∧
        q ∈ Set.range
          (D.walkArcPath
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) e)) := by
  induction n with
  | zero =>
      change q ∈ Set.range (D.walkArcPath e) ↔ _
      constructor
      · exact fun hq => ⟨0, by omega, hq⟩
      · rintro ⟨i, hi, hq⟩
        have hi0 : i = 0 := by omega
        subst i
        change q ∈ Set.range (D.walkArcPath e) at hq
        exact hq
  | succ n ih =>
      rw [walkArcPathConcatPositive, Path.trans_range, Set.mem_union, ih]
      constructor
      · rintro (⟨i, hi, hq⟩ | hlast)
        · exact ⟨i, by omega, hq⟩
        · exact ⟨n + 1, by omega, hlast⟩
      · rintro ⟨i, hi, hq⟩
        by_cases hilast : i = n + 1
        · subst i
          change q ∈ Set.range
            (D.walkArcPath
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n + 1]) e)) at hq
          exact Or.inr hq
        · exact Or.inl ⟨i, by omega, hq⟩

/-- The range of a finite concatenation is exactly the initial vertex together
with the ranges of its first `k` traversal pieces. -/
theorem mem_range_walkArcPathConcat_iff
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) (k : ℕ)
    (q : PlanePoint) :
    q ∈ Set.range (D.walkArcPathConcat e k) ↔
      q = e.1.1.1.1 ∨
        ∃ i : ℕ, i < k ∧
          q ∈ Set.range
            (D.walkArcPath
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) e)) := by
  cases k with
  | zero =>
      constructor
      · rintro ⟨t, rfl⟩
        exact Or.inl rfl
      · rintro (rfl | ⟨i, hi, _hq⟩)
        · exact ⟨0, rfl⟩
        · omega
  | succ n =>
      rw [walkArcPathConcat]
      rw [D.mem_range_walkArcPathConcatPositive_iff]
      constructor
      · exact Or.inr
      · rintro (rfl | hq)
        · refine ⟨0, by omega, ?_⟩
          refine ⟨0, ?_⟩
          change D.walkArcPath e 0 = e.1.1.1.1
          exact (D.walkArcPath e).source'
        · exact hq

/-- For a positive concatenation the initial vertex already belongs to its
first traversal piece, so the range is precisely the union of those pieces. -/
theorem mem_range_walkArcPathConcat_iff_of_pos
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) {k : ℕ}
    (hk : 0 < k) (q : PlanePoint) :
    q ∈ Set.range (D.walkArcPathConcat e k) ↔
      ∃ i : ℕ, i < k ∧
        q ∈ Set.range
          (D.walkArcPath
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) e)) := by
  rw [D.mem_range_walkArcPathConcat_iff]
  constructor
  · rintro (rfl | hq)
    · refine ⟨0, hk, ?_⟩
      refine ⟨0, ?_⟩
      change D.walkArcPath e 0 = e.1.1.1.1
      exact (D.walkArcPath e).source'
    · exact hq
  · exact Or.inr
/-- Close a concatenated geometric traversal whose combinatorial endpoint has
returned to its start. -/
noncomputable def closedWalkPathOfPeriod
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) (k : ℕ)
    (hperiod :
      ((D.walkStep : D.HalfEdge → D.HalfEdge)^[k]) e = e) :
    Path e.1.1.1.1 e.1.1.1.1 :=
  (D.walkArcPathConcat e k).cast rfl
    (congrArg (fun h : D.HalfEdge => h.1.1.1.1) hperiod.symm)

/-- A positive periodic orbit together with its actual closed path
realization. -/
structure GeometricWalkLoop
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) where
  period : ℕ
  period_pos : 0 < period
  period_eq :
    ((D.walkStep : D.HalfEdge → D.HalfEdge)^[period]) e = e

/-- The genuine closed `PlanePoint` path carried by a geometric walk loop. -/
noncomputable def GeometricWalkLoop.path
    {D : FiniteChartCutSystem A} {e : D.HalfEdge}
    (L : D.GeometricWalkLoop e) :
    Path e.1.1.1.1 e.1.1.1.1 :=
  D.closedWalkPathOfPeriod e L.period L.period_eq

/-- Every retained half-edge has a positive finite closed-path realization. -/
theorem geometricWalkLoop_nonempty
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    Nonempty (D.GeometricWalkLoop e) := by
  obtain ⟨k, hk, hperiod⟩ := D.exists_pos_iterate_walkStep_eq e
  exact ⟨⟨k, hk, hperiod⟩⟩

/-- Every realized closed walk remains on the actual cropped frontier. -/
theorem GeometricWalkLoop.path_range_subset_frontier
    {D : FiniteChartCutSystem A} {e : D.HalfEdge}
    (L : D.GeometricWalkLoop e) :
    Set.range L.path ⊆ frontier O := by
  change Set.range (D.walkArcPathConcat e L.period) ⊆ frontier O
  exact D.walkArcPathConcat_range_subset_frontier e L.period

/-- Every half-edge starts a positive finite cyclic sequence of actual embedded
arc paths.  The endpoint matching of consecutive pieces is encoded by
`walkArcPath`, whose target is the next `walkStep` vertex. -/
theorem exists_pos_geometric_walkCycle
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    ∃ k : ℕ, 0 < k ∧
      ((D.walkStep : D.HalfEdge → D.HalfEdge)^[k]) e = e ∧
      ∀ i : Fin k,
        Function.Injective
            (D.walkArcPath
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i.1]) e)) ∧
          Set.range
              (D.walkArcPath
                (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i.1]) e)) =
            Subtype.val ''
              D.finiteArcClosure
                (D.switchHalfEdge
                  (((D.walkStep :
                    D.HalfEdge → D.HalfEdge)^[i.1]) e)).1.2 := by
  obtain ⟨k, hk, hperiod⟩ := D.exists_pos_iterate_walkStep_eq e
  refine ⟨k, hk, hperiod, ?_⟩
  intro i
  exact ⟨D.walkArcPath_injective _,
    D.walkArcPath_range _⟩

end FiniteChartCutSystem
end BoundaryHalfSpaceAtlas
end CMVBoundaryLocalAtlas
