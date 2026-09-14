/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryComponentTopology

/-!
# Global transitions from local frontier branches

This module relates the two arms of one actual frontier interval chart to the
connected components obtained after deleting its base point.  Every punctured
component must return to every neighborhood of the deleted point, so the two
local arms account for all global punctured components.  No global trace,
component order, or geometric frontier inventory is assumed.
-/

open Set Filter MeasureTheory Metric Bornology
open scoped ENNReal MeasureTheory Topology

noncomputable section

namespace CMVBoundaryLocalAtlas

namespace ConnectedPuncture

variable {X : Type*} [TopologicalSpace X]

/-- A connected space with one distinguished point removed. -/
abbrev Punctured (p : X) := {q : X // q ≠ p}

private theorem isOpen_puncturedSet [T1Space X] (p : X) :
    IsOpen {q : X | q ≠ p} := by
  have hset : {q : X | q ≠ p} = ({p} : Set X)ᶜ := by
    ext q
    simp
  rw [hset]
  exact isOpen_compl_singleton


/-- The realization in the original space of the punctured connected component
through `x`. -/
def componentImage (p : X) (x : Punctured p) : Set X :=
  Subtype.val '' connectedComponent x

/-- A punctured connected component is open in the original space. -/
theorem isOpen_componentImage [T1Space X] [LocallyConnectedSpace X]
    (p : X) (x : Punctured p) :
    IsOpen (componentImage p x) := by
  letI : LocallyConnectedSpace (Punctured p) :=
    (isOpen_puncturedSet p).locallyConnectedSpace
  exact (isOpen_puncturedSet p).isOpenMap_subtype_val
    _ (isOpen_connectedComponent (x := x))

/-- A punctured connected component is nonempty. -/
theorem componentImage_nonempty (p : X) (x : Punctured p) :
    (componentImage p x).Nonempty :=
  ⟨x.1, x, mem_connectedComponent, rfl⟩

/-- A punctured connected component still omits the deleted point after being
realized in the original space. -/
theorem componentImage_subset_compl (p : X) (x : Punctured p) :
    componentImage p x ⊆ {p}ᶜ := by
  rintro _ ⟨q, _hq, rfl⟩
  exact q.2

/-- Every connected component after deleting one point accumulates at that
point.  Otherwise its realization would be a nonempty clopen proper subset of
the original connected space. -/
theorem base_mem_closure_componentImage
    [T1Space X] [LocallyConnectedSpace X] [ConnectedSpace X]
    (p : X) (x : Punctured p) :
    p ∈ closure (componentImage p x) := by
  by_contra hp
  have hclosed : IsClosed (componentImage p x) := by
    apply closure_subset_iff_isClosed.mp
    intro y hy
    by_contra hyImage
    have hyp : y ≠ p := by
      intro hyp
      apply hp
      simpa only [hyp] using hy
    let y' : Punctured p := ⟨y, hyp⟩
    have hyComponent : y' ∉ connectedComponent x := by
      intro hyComponent
      exact hyImage ⟨y', hyComponent, rfl⟩
    let V : Set X := Subtype.val '' (connectedComponent x)ᶜ
    have hVopen : IsOpen V := by
      letI : LocallyConnectedSpace (Punctured p) :=
        (isOpen_puncturedSet p).locallyConnectedSpace
      exact (isOpen_puncturedSet p).isOpenMap_subtype_val
        _ (isClosed_connectedComponent (x := x)).isOpen_compl
    have hyV : y ∈ V := ⟨y', hyComponent, rfl⟩
    obtain ⟨z, hzV, hzImage⟩ :=
      (mem_closure_iff.1 hy) V hVopen hyV
    rcases hzImage with ⟨zImage, hzImageComponent, rfl⟩
    rcases hzV with ⟨zV, hzVComponent, hzEq⟩
    have hzSubtype : zImage = zV := Subtype.ext hzEq.symm
    exact hzVComponent (hzSubtype ▸ hzImageComponent)
  have huniv : componentImage p x = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, isOpen_componentImage p x⟩
      (componentImage_nonempty p x)
  have hpImage : p ∈ componentImage p x := by
    rw [huniv]
    exact mem_univ p
  exact (componentImage_subset_compl p x hpImage) rfl

/-- Consequently every open neighborhood of the deleted point meets every
punctured connected component. -/
theorem componentImage_inter_open_nonempty
    [T1Space X] [LocallyConnectedSpace X] [ConnectedSpace X]
    (p : X) (x : Punctured p)
    {U : Set X} (hUopen : IsOpen U) (hpU : p ∈ U) :
    (componentImage p x ∩ U).Nonempty := by
  simpa only [inter_comm] using
    (mem_closure_iff.1 (base_mem_closure_componentImage p x)) U hUopen hpU

end ConnectedPuncture

namespace BoundaryHalfSpaceAtlas

variable {O : Set PlanePoint}

/-- The actual frontier component through `p`, as a topological subspace. -/
abbrev FrontierComponentSpace (p : FrontierSpace O) :=
  connectedComponent p

/-- The distinguished point of its own actual frontier component. -/
def frontierComponentBase (p : FrontierSpace O) : FrontierComponentSpace p :=
  ⟨p, mem_connectedComponent⟩

/-- The actual frontier component through `p` after deleting `p`. -/
abbrev PuncturedFrontierComponent (p : FrontierSpace O) :=
  ConnectedPuncture.Punctured (frontierComponentBase p)

end BoundaryHalfSpaceAtlas

namespace ActualFrontierIntervalChart

open BoundaryHalfSpaceAtlas

/-- The selected local interval window, restricted to the complete frontier
component through its base. -/
def componentLocalDomain {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) : Set (FrontierComponentSpace p) :=
  {q | q.1 ∈ C.localDomain}

/-- The restricted local interval window is open in the complete component. -/
theorem isOpen_componentLocalDomain {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    IsOpen C.componentLocalDomain :=
  C.isOpen_localDomain.preimage continuous_subtype_val

/-- The component base lies in the restricted local interval window. -/
theorem frontierComponentBase_mem_componentLocalDomain {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    frontierComponentBase p ∈ C.componentLocalDomain :=
  C.base_mem_localDomain

/-- A non-base point of the local interval, regarded as a point of the complete
frontier component with the base deleted. -/
def localPointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) (q : C.localDomain)
    (hq : q ≠ C.baseInLocalDomain) : PuncturedFrontierComponent p :=
  ⟨⟨q.1, C.localDomain_subset_connectedComponent q.2⟩, by
    intro h
    apply hq
    apply Subtype.ext
    exact congrArg
      (fun z : FrontierComponentSpace p => (z : FrontierSpace O)) h⟩

/-- A negative local arm point in the punctured complete component. -/
def negativePointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) (q : C.negativeBranch) :
    PuncturedFrontierComponent p :=
  C.localPointToPunctured q.1 (by
    intro h
    have hparameter : C.parameterHomeomorph q.1 < C.zeroParameter := q.2
    rw [h, C.parameterHomeomorph_base] at hparameter
    exact (lt_irrefl _ hparameter))

/-- A positive local arm point in the punctured complete component. -/
def positivePointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) (q : C.positiveBranch) :
    PuncturedFrontierComponent p :=
  C.localPointToPunctured q.1 (by
    intro h
    have hparameter : C.zeroParameter < C.parameterHomeomorph q.1 := q.2
    rw [h, C.parameterHomeomorph_base] at hparameter
    exact (lt_irrefl _ hparameter))

/-- The negative arm inclusion into the punctured complete component is
continuous. -/
theorem continuous_negativePointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    Continuous C.negativePointToPunctured := by
  unfold negativePointToPunctured localPointToPunctured
  fun_prop

/-- The positive arm inclusion into the punctured complete component is
continuous. -/
theorem continuous_positivePointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    Continuous C.positivePointToPunctured := by
  unfold positivePointToPunctured localPointToPunctured
  fun_prop

/-- The complete negative local arm remains connected after inclusion into the
punctured complete component. -/
theorem isConnected_range_negativePointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    IsConnected (Set.range C.negativePointToPunctured) := by
  letI : ConnectedSpace C.negativeBranch :=
    isConnected_iff_connectedSpace.mp C.isConnected_negativeBranch
  exact isConnected_range C.continuous_negativePointToPunctured

/-- The complete positive local arm remains connected after inclusion into the
punctured complete component. -/
theorem isConnected_range_positivePointToPunctured {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    IsConnected (Set.range C.positivePointToPunctured) := by
  letI : ConnectedSpace C.positiveBranch :=
    isConnected_iff_connectedSpace.mp C.isConnected_positiveBranch
  exact isConnected_range C.continuous_positivePointToPunctured

/-- All negative-arm points belong to one global punctured connected
component. -/
theorem connectedComponent_negativePointToPunctured_eq {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) (q r : C.negativeBranch) :
    connectedComponent (C.negativePointToPunctured q) =
      connectedComponent (C.negativePointToPunctured r) := by
  apply connectedComponent_eq
  exact C.isConnected_range_negativePointToPunctured.subset_connectedComponent
    ⟨q, rfl⟩ ⟨r, rfl⟩

/-- All positive-arm points belong to one global punctured connected
component. -/
theorem connectedComponent_positivePointToPunctured_eq {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) (q r : C.positiveBranch) :
    connectedComponent (C.positivePointToPunctured q) =
      connectedComponent (C.positivePointToPunctured r) := by
  apply connectedComponent_eq
  exact C.isConnected_range_positivePointToPunctured.subset_connectedComponent
    ⟨q, rfl⟩ ⟨r, rfl⟩

end ActualFrontierIntervalChart

namespace BoundaryHalfSpaceAtlas

open ActualFrontierIntervalChart
/-- Every global punctured component meets one of the two arms of the selected
local chart.  This is the global return statement missing from the purely local
two-arm theorem. -/
theorem puncturedComponent_meets_localArm
    (A : BoundaryHalfSpaceAtlas O) {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p)
    (x : PuncturedFrontierComponent p) :
    (∃ q : C.negativeBranch,
      connectedComponent x = connectedComponent (C.negativePointToPunctured q)) ∨
    (∃ q : C.positiveBranch,
      connectedComponent x = connectedComponent (C.positivePointToPunctured q)) := by
  letI : LocallyConnectedSpace (FrontierSpace O) :=
    A.frontierLocallyConnectedSpace
  letI : LocallyConnectedSpace (FrontierComponentSpace p) :=
    (isOpen_connectedComponent (x := p)).locallyConnectedSpace
  letI : ConnectedSpace (FrontierComponentSpace p) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨q, hqImage, hqWindow⟩ :=
    ConnectedPuncture.componentImage_inter_open_nonempty
      (frontierComponentBase p) x C.isOpen_componentLocalDomain
      C.frontierComponentBase_mem_componentLocalDomain
  rcases hqImage with ⟨z, hzComponent, hzq⟩
  let qLocal : C.localDomain := ⟨q.1, hqWindow⟩
  have hqLocalNe : qLocal ≠ C.baseInLocalDomain := by
    intro h
    apply z.2
    have hqBase : q = frontierComponentBase p := by
      apply Subtype.ext
      exact congrArg (fun w : C.localDomain => (w : FrontierSpace O)) h
    exact hzq.trans hqBase
  have hlocalLift : C.localPointToPunctured qLocal hqLocalNe = z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg
      (fun w : FrontierComponentSpace p => (w : FrontierSpace O)) hzq).symm
  have hliftComponent : C.localPointToPunctured qLocal hqLocalNe ∈
      connectedComponent x := by
    rw [hlocalLift]
    exact hzComponent
  have hbranches : qLocal ∈ C.negativeBranch ∪ C.positiveBranch := by
    rw [C.negativeBranch_union_positiveBranch]
    exact hqLocalNe
  rcases hbranches with hnegative | hpositive
  · let qNegative : C.negativeBranch := ⟨qLocal, hnegative⟩
    refine Or.inl ⟨qNegative, connectedComponent_eq ?_⟩
    simpa only [negativePointToPunctured, qNegative] using hliftComponent
  · let qPositive : C.positiveBranch := ⟨qLocal, hpositive⟩
    refine Or.inr ⟨qPositive, connectedComponent_eq ?_⟩
    simpa only [positivePointToPunctured, qPositive] using hliftComponent

end BoundaryHalfSpaceAtlas

namespace ActualFrontierIntervalChart

open BoundaryHalfSpaceAtlas
/-- A fixed point on the negative local arm. -/
noncomputable def negativePuncturedRepresentative {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) : PuncturedFrontierComponent p :=
  C.negativePointToPunctured
    (Classical.choice
      (Set.nonempty_coe_sort.mpr C.isConnected_negativeBranch.nonempty))

/-- A fixed point on the positive local arm. -/
noncomputable def positivePuncturedRepresentative {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) : PuncturedFrontierComponent p :=
  C.positivePointToPunctured
    (Classical.choice
      (Set.nonempty_coe_sort.mpr C.isConnected_positiveBranch.nonempty))

/-- The two local arms give a concrete two-point enumeration candidate for
the global punctured connected-component quotient. -/
def puncturedComponentClass {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    Bool → ConnectedComponents (PuncturedFrontierComponent p)
  | false => C.negativePuncturedRepresentative
  | true => C.positivePuncturedRepresentative

end ActualFrontierIntervalChart

namespace BoundaryHalfSpaceAtlas

open ActualFrontierIntervalChart
/-- Every point of the punctured complete component lies in one of the two
global components selected by the local arms. -/
theorem punctured_connectedComponent_eq_negative_or_positive
    (A : BoundaryHalfSpaceAtlas O) {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p)
    (x : PuncturedFrontierComponent p) :
    connectedComponent x = connectedComponent C.negativePuncturedRepresentative ∨
      connectedComponent x = connectedComponent C.positivePuncturedRepresentative := by
  rcases A.puncturedComponent_meets_localArm C x with
    ⟨q, hq⟩ | ⟨q, hq⟩
  · exact Or.inl (hq.trans
      (C.connectedComponent_negativePointToPunctured_eq q
        (Classical.choice
          (Set.nonempty_coe_sort.mpr C.isConnected_negativeBranch.nonempty))))
  · exact Or.inr (hq.trans
      (C.connectedComponent_positivePointToPunctured_eq q
        (Classical.choice
          (Set.nonempty_coe_sort.mpr C.isConnected_positiveBranch.nonempty))))

/-- The connected-component quotient after deleting any point of a complete
frontier component has at most the two classes represented by the selected
local arms. -/
theorem punctured_connectedComponents_eq_negative_or_positive
    (A : BoundaryHalfSpaceAtlas O) {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p)
    (c : ConnectedComponents (PuncturedFrontierComponent p)) :
    c = (C.negativePuncturedRepresentative :
      ConnectedComponents (PuncturedFrontierComponent p)) ∨
    c = (C.positivePuncturedRepresentative :
      ConnectedComponents (PuncturedFrontierComponent p)) := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe c
  rcases A.punctured_connectedComponent_eq_negative_or_positive C x with
    hnegative | hpositive
  · left
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe.mpr hnegative
  · right
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe.mpr hpositive

/-- The two-arm enumeration is onto the complete punctured-component
quotient. -/
theorem puncturedComponentClass_surjective
    (A : BoundaryHalfSpaceAtlas O) {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    Function.Surjective C.puncturedComponentClass := by
  intro c
  rcases A.punctured_connectedComponents_eq_negative_or_positive C c with
    hnegative | hpositive
  · exact ⟨false, hnegative.symm⟩
  · exact ⟨true, hpositive.symm⟩

/-- Finiteness of the punctured connected-component quotient is derived from
the explicit two-arm surjection, not assumed. -/
theorem finite_punctured_connectedComponents
    (A : BoundaryHalfSpaceAtlas O) {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    Finite (ConnectedComponents (PuncturedFrontierComponent p)) :=
  Finite.of_surjective C.puncturedComponentClass
    (A.puncturedComponentClass_surjective C)

/-- Deleting one point from a complete actual frontier component creates at
most two connected components. -/
theorem punctured_connectedComponents_natCard_le_two
    (A : BoundaryHalfSpaceAtlas O) {p : FrontierSpace O}
    (C : ActualFrontierIntervalChart O p) :
    Nat.card (ConnectedComponents (PuncturedFrontierComponent p)) ≤ 2 := by
  letI : Finite (ConnectedComponents (PuncturedFrontierComponent p)) :=
    A.finite_punctured_connectedComponents C
  letI : Fintype (ConnectedComponents (PuncturedFrontierComponent p)) :=
    Fintype.ofFinite _
  simpa using Fintype.card_le_of_surjective C.puncturedComponentClass
    (A.puncturedComponentClass_surjective C)

end BoundaryHalfSpaceAtlas

end CMVBoundaryLocalAtlas
