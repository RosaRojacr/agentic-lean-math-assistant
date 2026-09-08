/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVFigureFourSourceGeometry
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Finite-junction disagreement phases

This module separates the null set discarded by an almost-everywhere argument
from the finite junction set removed for planar connectivity.  A local phase is
a neighborhood label for set-membership disagreement away from both exceptional
sets; it is not the raw membership XOR at boundary points.
-/

open Set
open MeasureTheory

noncomputable section

namespace CMVFiniteJunctionDisagreement

/-- `false` labels agreement and `true` labels disagreement of two memberships. -/
def HasDisagreementLabel (U K : Set PlanePoint) (label : Bool)
    (p : PlanePoint) : Prop :=
  match label with
  | false => (p ∈ U ↔ p ∈ K)
  | true => ¬ (p ∈ U ↔ p ∈ K)

@[simp] theorem hasDisagreementLabel_false (U K : Set PlanePoint) (p : PlanePoint) :
    HasDisagreementLabel U K false p ↔ (p ∈ U ↔ p ∈ K) :=
  Iff.rfl

@[simp] theorem hasDisagreementLabel_true (U K : Set PlanePoint) (p : PlanePoint) :
    HasDisagreementLabel U K true p ↔ ¬ (p ∈ U ↔ p ∈ K) :=
  Iff.rfl

/-- Points away from `J` carrying a locally constant disagreement phase off the
null set `B` and the junction set `J`. -/
def localPhaseSet (U K B J : Set PlanePoint) (label : Bool) : Set PlanePoint :=
  {p | p ∉ J ∧ ∃ V : Set PlanePoint,
    IsOpen V ∧ p ∈ V ∧
      ∀ q, q ∈ V → q ∉ B → q ∉ J → HasDisagreementLabel U K label q}

/-- Local phase sets are open in the punctured plane whenever the junction set
is closed. -/
theorem isOpen_localPhaseSet {U K B J : Set PlanePoint} (hJ : IsClosed J)
    (label : Bool) : IsOpen (localPhaseSet U K B J label) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  rcases hp with ⟨hpJ, V, hVopen, hpV, hlabel⟩
  filter_upwards [hVopen.mem_nhds hpV, hJ.isOpen_compl.mem_nhds hpJ] with q hqV hqJ
  exact ⟨hqJ, V, hVopen, hqV, hlabel⟩

/-- A null complement is dense, so one point cannot carry both local phase
labels.  The null set and junction set remain separate inputs. -/
theorem localPhase_label_unique {U K B J : Set PlanePoint}
    (hB : volume B = 0) (hJ : volume J = 0) {p : PlanePoint}
    (hfalse : p ∈ localPhaseSet U K B J false)
    (htrue : p ∈ localPhaseSet U K B J true) : False := by
  rcases hfalse with ⟨_, V₀, hV₀open, hpV₀, hfalse⟩
  rcases htrue with ⟨_, V₁, hV₁open, hpV₁, htrue⟩
  have hnull : volume (B ∪ J) = 0 := measure_union_null hB hJ
  have hae : ∀ᵐ q ∂volume, q ∉ B ∪ J :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  have hdense : Dense {q : PlanePoint | q ∉ B ∪ J} :=
    volume.dense_of_ae hae
  obtain ⟨q, hqOutside, hqV⟩ :=
    hdense.exists_mem_open (hV₀open.inter hV₁open) ⟨p, hpV₀, hpV₁⟩
  have hqB : q ∉ B := fun hq => hqOutside (Or.inl hq)
  have hqJ : q ∉ J := fun hq => hqOutside (Or.inr hq)
  exact (htrue q hqV.2 hqB hqJ) (hfalse q hqV.1 hqB hqJ)

/-- Removing finitely many points from the coordinate plane leaves a connected
set.  The rank calculation is explicit: `PlanePoint = ℝ × ℝ` has real rank two. -/
theorem finite_plane_compl_isConnected {J : Set PlanePoint} (hJ : J.Finite) :
    IsConnected Jᶜ :=
  hJ.countable.isConnected_compl_of_one_lt_rank (by norm_num [PlanePoint])

/-- The two phase sets are disjoint.  Nullity of `B` and `J` is used only to
find a test point where both local labels apply. -/
theorem localPhaseSet_false_disjoint_true {U K B J : Set PlanePoint}
    (hB : volume B = 0) (hJ : volume J = 0) :
    Disjoint (localPhaseSet U K B J false)
      (localPhaseSet U K B J true) := by
  rw [Set.disjoint_left]
  intro p hpfalse hptrue
  exact localPhase_label_unique hB hJ hpfalse hptrue

/-- Two bounded sets have a common exterior neighborhood, which supplies an
agreement-phase anchor.  Finiteness keeps the anchor away from the junctions;
no regularity or measurability of either set is needed. -/
theorem exists_mem_localPhaseSet_false_of_bounded
    {U K B J : Set PlanePoint}
    (hU : Bornology.IsBounded U) (hK : Bornology.IsBounded K)
    (hJ : J.Finite) :
    (localPhaseSet U K B J false).Nonempty := by
  have hAll : Bornology.IsBounded ((U ∪ K) ∪ J) :=
    (hU.union hK).union hJ.isBounded
  obtain ⟨R, _, hsub⟩ := hAll.subset_closedBall_lt 0 0
  obtain ⟨p, hp⟩ := NormedSpace.exists_lt_norm ℝ PlanePoint R
  have hpOutside : p ∈ (Metric.closedBall 0 R)ᶜ := by
    simpa only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
      using hp
  have hpJ : p ∉ J := fun hpJ => hpOutside (hsub (Or.inr hpJ))
  refine ⟨p, hpJ, (Metric.closedBall 0 R)ᶜ,
    Metric.isClosed_closedBall.isOpen_compl, hpOutside, ?_⟩
  intro q hqOutside _ _
  rw [hasDisagreementLabel_false]
  constructor
  · intro hqU
    exact (hqOutside (hsub (Or.inl (Or.inl hqU)))).elim
  · intro hqK
    exact (hqOutside (hsub (Or.inl (Or.inr hqK)))).elim

/-- **Finite-junction rigidity.**  Suppose every point off a finite junction
set has one of the two open local disagreement phases.  Connectedness of the
punctured plane and a bounded exterior agreement anchor eliminate the
disagreement phase.  Removing the null test set and finite junctions then gives
almost-everywhere equality of the original sets. -/
theorem ae_eq_of_finite_junction_localPhase_cover
    {U K B J : Set PlanePoint}
    (hU : Bornology.IsBounded U) (hK : Bornology.IsBounded K)
    (hB : volume B = 0) (hJ : J.Finite)
    (hcover : Jᶜ ⊆
      localPhaseSet U K B J false ∪ localPhaseSet U K B J true) :
    U =ᵐ[volume] K := by
  have hJnull : volume J = 0 := hJ.measure_zero volume
  have hfalseOpen : IsOpen (localPhaseSet U K B J false) :=
    isOpen_localPhaseSet hJ.isClosed false
  have htrueOpen : IsOpen (localPhaseSet U K B J true) :=
    isOpen_localPhaseSet hJ.isClosed true
  have hdisjoint : Disjoint (localPhaseSet U K B J false)
      (localPhaseSet U K B J true) :=
    localPhaseSet_false_disjoint_true hB hJnull
  obtain ⟨p, hpfalse⟩ :=
    exists_mem_localPhaseSet_false_of_bounded hU hK hJ
  have hfalseAll : Jᶜ ⊆ localPhaseSet U K B J false :=
    (finite_plane_compl_isConnected hJ).isPreconnected.subset_left_of_subset_union
      hfalseOpen htrueOpen hdisjoint hcover
      ⟨p, hpfalse.1, hpfalse⟩
  have hnull : volume (B ∪ J) = 0 := measure_union_null hB hJnull
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with q hq
  have hqB : q ∉ B := fun hqB => hq (Or.inl hqB)
  have hqJ : q ∉ J := fun hqJ => hq (Or.inr hqJ)
  rcases hfalseAll hqJ with ⟨_, V, hVopen, hqV, hlabel⟩
  exact propext (hlabel q hqV hqB hqJ)

/-- A fixed-orientation form of `CMVFigureFour.LocallyOneSided`, used to
compare source and target orientations without assuming that they match. -/
def LocallyOnCircleSide (U : Set PlanePoint) (center : PlanePoint)
    (radius : ℝ) (side : CMVFigureFour.CircleSide) (p : PlanePoint) : Prop :=
  ∃ V : Set PlanePoint, IsOpen V ∧ p ∈ V ∧
    U ∩ V = V ∩ {q | side.sign * CMVFigureFour.circleValue center radius q < 0}

/-- The frozen source interface is exactly existential fixed-side data. -/
theorem locallyOneSided_iff_exists_locallyOnCircleSide
    {U : Set PlanePoint} {center : PlanePoint} {radius : ℝ} {p : PlanePoint} :
    CMVFigureFour.LocallyOneSided U center radius p ↔
      ∃ side, LocallyOnCircleSide U center radius side p := by
  rfl

private theorem mem_iff_of_local_side
    {U V : Set PlanePoint} {center q : PlanePoint} {radius : ℝ}
    {side : CMVFigureFour.CircleSide}
    (hUV : U ∩ V = V ∩
      {z | side.sign * CMVFigureFour.circleValue center radius z < 0})
    (hqV : q ∈ V) :
    q ∈ U ↔ side.sign * CMVFigureFour.circleValue center radius q < 0 := by
  constructor
  · intro hqU
    have hq : q ∈ U ∩ V := ⟨hqU, hqV⟩
    rw [hUV] at hq
    exact hq.2
  · intro hqSide
    have hq : q ∈ V ∩
        {z | side.sign * CMVFigureFour.circleValue center radius z < 0} :=
      ⟨hqV, hqSide⟩
    rw [← hUV] at hq
    exact hq.1

/-- Matching local circle orientations induce the zero-disagreement phase. -/
theorem localPhase_of_same_circle_side
    {U K J : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    {side : CMVFigureFour.CircleSide}
    (hpJ : p ∉ J)
    (hU : LocallyOnCircleSide U center radius side p)
    (hK : LocallyOnCircleSide K center radius side p) :
    p ∈ localPhaseSet U K
      {q | CMVFigureFour.circleValue center radius q = 0} J false := by
  rcases hU with ⟨V, hVopen, hpV, hUV⟩
  rcases hK with ⟨W, hWopen, hpW, hKW⟩
  refine ⟨hpJ, V ∩ W, hVopen.inter hWopen, ⟨hpV, hpW⟩, ?_⟩
  intro q hq _ _
  exact (mem_iff_of_local_side hUV hq.1).trans
    (mem_iff_of_local_side hKW hq.2).symm

/-- Opposite local circle orientations induce the one-disagreement phase away
from the supporting circle. -/
theorem localPhase_of_opposite_circle_sides
    {U K J : Set PlanePoint} {center p : PlanePoint} {radius : ℝ}
    {sourceSide targetSide : CMVFigureFour.CircleSide}
    (hpJ : p ∉ J) (hopposite : sourceSide ≠ targetSide)
    (hU : LocallyOnCircleSide U center radius sourceSide p)
    (hK : LocallyOnCircleSide K center radius targetSide p) :
    p ∈ localPhaseSet U K
      {q | CMVFigureFour.circleValue center radius q = 0} J true := by
  rcases hU with ⟨V, hVopen, hpV, hUV⟩
  rcases hK with ⟨W, hWopen, hpW, hKW⟩
  refine ⟨hpJ, V ∩ W, hVopen.inter hWopen, ⟨hpV, hpW⟩, ?_⟩
  intro q hq hqCircle _
  have hUiff := mem_iff_of_local_side hUV hq.1
  have hKiff := mem_iff_of_local_side hKW hq.2
  rw [hasDisagreementLabel_true]
  intro hagree
  cases sourceSide <;> cases targetSide
  · exact (hopposite rfl).elim
  · simp only [CMVFigureFour.CircleSide.sign, one_mul, neg_one_mul] at hUiff hKiff
    rcases lt_or_gt_of_ne hqCircle with hneg | hpos
    · have hqU : q ∈ U := hUiff.2 hneg
      have hqK : q ∈ K := hagree.1 hqU
      linarith [hKiff.1 hqK]
    · have hqK : q ∈ K := hKiff.2 (by linarith)
      have hqU : q ∈ U := hagree.2 hqK
      linarith [hUiff.1 hqU]
  · simp only [CMVFigureFour.CircleSide.sign, one_mul, neg_one_mul] at hUiff hKiff
    rcases lt_or_gt_of_ne hqCircle with hneg | hpos
    · have hqK : q ∈ K := hKiff.2 hneg
      have hqU : q ∈ U := hagree.2 hqK
      linarith [hUiff.1 hqU]
    · have hqU : q ∈ U := hUiff.2 (by linarith)
      have hqK : q ∈ K := hagree.1 hqU
      linarith [hKiff.1 hqK]
  · exact (hopposite rfl).elim

end CMVFiniteJunctionDisagreement
