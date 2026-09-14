/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
import CMVBoundaryIntervalParameterization
import Mathlib.Topology.ContinuousMap.Interval

/-!
# Simple complete boundary loop

The two endpoint-preserving completed-chain parameterizations are concatenated,
with the right chain traversed in reverse.  Exact chain intersection proves
half-open injectivity, so horizontal jump segments and accumulating jumps are
retained without repeated vertices or omitted limit points.
-/

open Set Function TopologicalSpace
open scoped Topology

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace SelectedBoundaryTopologyInput

variable {E U : Set PlanePoint}

local instance factZeroOne : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩
local instance factOneTwo : Fact ((1 : ℝ) ≤ 2) := ⟨by norm_num⟩

/-- Reverse affine parameterization from `[1,2]` to the unit interval. -/
def reverseOneTwoToUnit : C(Set.Icc (1 : ℝ) 2, Set.Icc (0 : ℝ) 1) where
  toFun t := ⟨2 - t.1, by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  continuous_toFun :=
    Continuous.subtype_mk (continuous_const.sub continuous_subtype_val)
      (fun t => by
        change 0 ≤ 2 - t.1 ∧ 2 - t.1 ≤ 1
        constructor <;> linarith [t.property.1, t.property.2])

/-- The completed left chain, viewed as a planar continuous path. -/
noncomputable def leftCompletedChainPath
    (D : SelectedBoundaryTopologyInput E U) :
    C(Set.Icc (0 : ℝ) 1, PlanePoint) where
  toFun t := (D.leftCompletedChainHomeomorph t).1
  continuous_toFun :=
    continuous_subtype_val.comp D.leftCompletedChainHomeomorph.continuous

/-- The completed right chain, traversed from its upper split point back to its
lower split point on `[1,2]`. -/
noncomputable def rightCompletedChainReversedPath
    (D : SelectedBoundaryTopologyInput E U) :
    C(Set.Icc (1 : ℝ) 2, PlanePoint) where
  toFun t :=
    (D.rightCompletedChainHomeomorph (reverseOneTwoToUnit t)).1
  continuous_toFun :=
    continuous_subtype_val.comp
      (D.rightCompletedChainHomeomorph.continuous.comp
        reverseOneTwoToUnit.continuous)

@[simp] theorem leftCompletedChainPath_zero
    (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChainPath ⟨0, by norm_num⟩ = D.lowerSplitPoint := by
  exact D.leftCompletedChainHomeomorph_zero

@[simp] theorem leftCompletedChainPath_one
    (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChainPath ⟨1, by norm_num⟩ = D.upperSplitPoint := by
  exact D.leftCompletedChainHomeomorph_one

@[simp] theorem rightCompletedChainReversedPath_one
    (D : SelectedBoundaryTopologyInput E U) :
    D.rightCompletedChainReversedPath ⟨1, by norm_num⟩ =
      D.upperSplitPoint := by
  change (D.rightCompletedChainHomeomorph
    (reverseOneTwoToUnit ⟨1, by norm_num⟩)).1 = D.upperSplitPoint
  have hreverse :
      reverseOneTwoToUnit ⟨1, by norm_num⟩ =
        (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    norm_num [reverseOneTwoToUnit]
  rw [hreverse, D.rightCompletedChainHomeomorph_one]

@[simp] theorem rightCompletedChainReversedPath_two
    (D : SelectedBoundaryTopologyInput E U) :
    D.rightCompletedChainReversedPath ⟨2, by norm_num⟩ =
      D.lowerSplitPoint := by
  change (D.rightCompletedChainHomeomorph
    (reverseOneTwoToUnit ⟨2, by norm_num⟩)).1 = D.lowerSplitPoint
  have hreverse :
      reverseOneTwoToUnit ⟨2, by norm_num⟩ =
        (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
    apply Subtype.ext
    norm_num [reverseOneTwoToUnit]
  rw [hreverse, D.rightCompletedChainHomeomorph_zero]

/-- The two planar chain paths have the same value at their common parameter. -/
theorem completedChainPaths_join
    (D : SelectedBoundaryTopologyInput E U) :
    D.leftCompletedChainPath ⊤ = D.rightCompletedChainReversedPath ⊥ := by
  change D.leftCompletedChainPath ⟨1, by norm_num⟩ =
    D.rightCompletedChainReversedPath ⟨1, by norm_num⟩
  rw [D.leftCompletedChainPath_one, D.rightCompletedChainReversedPath_one]

/-- Continuous concatenation of the upward left traversal and downward right
traversal on the positive-length real interval `[0,2]`. -/
noncomputable def completedBoundaryLoopOn
    (D : SelectedBoundaryTopologyInput E U) :
    C(Set.Icc (0 : ℝ) 2, PlanePoint) :=
  ContinuousMap.concat D.leftCompletedChainPath
    D.rightCompletedChainReversedPath

theorem completedBoundaryLoopOn_eq_left
    (D : SelectedBoundaryTopologyInput E U)
    (t : Set.Icc (0 : ℝ) 2) (ht : t.1 ≤ 1) :
    D.completedBoundaryLoopOn t =
      D.leftCompletedChainPath ⟨t.1, t.property.1, ht⟩ := by
  unfold completedBoundaryLoopOn
  exact ContinuousMap.concat_left D.completedChainPaths_join ht

theorem completedBoundaryLoopOn_eq_right
    (D : SelectedBoundaryTopologyInput E U)
    (t : Set.Icc (0 : ℝ) 2) (ht : 1 ≤ t.1) :
    D.completedBoundaryLoopOn t =
      D.rightCompletedChainReversedPath ⟨t.1, ht, t.property.2⟩ := by
  unfold completedBoundaryLoopOn
  exact ContinuousMap.concat_right D.completedChainPaths_join ht

@[simp] theorem completedBoundaryLoopOn_zero
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoopOn ⟨0, by norm_num⟩ = D.lowerSplitPoint := by
  rw [D.completedBoundaryLoopOn_eq_left _ (by norm_num),
    D.leftCompletedChainPath_zero]

@[simp] theorem completedBoundaryLoopOn_one
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoopOn ⟨1, by norm_num⟩ = D.upperSplitPoint := by
  rw [D.completedBoundaryLoopOn_eq_left _ le_rfl,
    D.leftCompletedChainPath_one]

@[simp] theorem completedBoundaryLoopOn_two
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoopOn ⟨2, by norm_num⟩ = D.lowerSplitPoint := by
  rw [D.completedBoundaryLoopOn_eq_right _ (by norm_num),
    D.rightCompletedChainReversedPath_two]

/-- The planar left-chain path is injective. -/
theorem leftCompletedChainPath_injective
    (D : SelectedBoundaryTopologyInput E U) :
    Injective D.leftCompletedChainPath := by
  intro s t hst
  apply D.leftCompletedChainHomeomorph.injective
  exact Subtype.ext hst

/-- The reversed planar right-chain path is injective. -/
theorem rightCompletedChainReversedPath_injective
    (D : SelectedBoundaryTopologyInput E U) :
    Injective D.rightCompletedChainReversedPath := by
  intro s t hst
  have hhome :
      D.rightCompletedChainHomeomorph (reverseOneTwoToUnit s) =
        D.rightCompletedChainHomeomorph (reverseOneTwoToUnit t) :=
    Subtype.ext hst
  have hreverse := D.rightCompletedChainHomeomorph.injective hhome
  have hval :
      (reverseOneTwoToUnit s : Set.Icc (0 : ℝ) 1).1 =
        (reverseOneTwoToUnit t : Set.Icc (0 : ℝ) 1).1 :=
    congrArg Subtype.val hreverse
  apply Subtype.ext
  dsimp [reverseOneTwoToUnit] at hval
  linarith

/-- A strict right-half parameter cannot repeat a point of the left path.  The
only intersections of the actual chains are the two split points, whose right
parameters are exactly `2` and `1`. -/
theorem leftCompletedChainPath_ne_rightCompletedChainReversedPath
    (D : SelectedBoundaryTopologyInput E U)
    (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (1 : ℝ) 2)
    (htOne : 1 < t.1) (htTwo : t.1 < 2) :
    D.leftCompletedChainPath s ≠ D.rightCompletedChainReversedPath t := by
  intro hpaths
  have hpLeft : D.leftCompletedChainPath s ∈ D.leftCompletedChain :=
    (D.leftCompletedChainHomeomorph s).property
  have hpRight : D.leftCompletedChainPath s ∈ D.rightCompletedChain := by
    rw [hpaths]
    exact (D.rightCompletedChainHomeomorph (reverseOneTwoToUnit t)).property
  have hpEnds :
      D.leftCompletedChainPath s = D.lowerSplitPoint ∨
        D.leftCompletedChainPath s = D.upperSplitPoint := by
    have hpInter : D.leftCompletedChainPath s ∈
        D.leftCompletedChain ∩ D.rightCompletedChain := ⟨hpLeft, hpRight⟩
    rw [D.completedChains_inter_eq] at hpInter
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hpInter
  rcases hpEnds with hpLower | hpUpper
  · have ht : t = ⟨2, by norm_num⟩ :=
      D.rightCompletedChainReversedPath_injective (by
        calc
          D.rightCompletedChainReversedPath t =
              D.leftCompletedChainPath s := hpaths.symm
          _ = D.lowerSplitPoint := hpLower
          _ = D.rightCompletedChainReversedPath ⟨2, by norm_num⟩ :=
            D.rightCompletedChainReversedPath_two.symm)
    have htVal := congrArg Subtype.val ht
    norm_num at htVal
    linarith
  · have ht : t = ⟨1, by norm_num⟩ :=
      D.rightCompletedChainReversedPath_injective (by
        calc
          D.rightCompletedChainReversedPath t =
              D.leftCompletedChainPath s := hpaths.symm
          _ = D.upperSplitPoint := hpUpper
          _ = D.rightCompletedChainReversedPath ⟨1, by norm_num⟩ :=
            D.rightCompletedChainReversedPath_one.symm)
    have htVal := congrArg Subtype.val ht
    norm_num at htVal
    linarith

/-- Total continuous extension of the completed loop.  On `[0,2]` this is the
literal concatenation; outside it is clamped to the common lower split point. -/
noncomputable def completedBoundaryLoop
    (D : SelectedBoundaryTopologyInput E U) : ℝ → PlanePoint :=
  fun t => D.completedBoundaryLoopOn (Set.projIcc 0 2 (by norm_num) t)

/-- The total extension is globally continuous. -/
theorem continuous_completedBoundaryLoop
    (D : SelectedBoundaryTopologyInput E U) :
    Continuous D.completedBoundaryLoop :=
  D.completedBoundaryLoopOn.continuous.comp continuous_projIcc

/-- On its defining interval the total loop is the concatenated subtype map. -/
theorem completedBoundaryLoop_of_mem
    (D : SelectedBoundaryTopologyInput E U) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    D.completedBoundaryLoop t = D.completedBoundaryLoopOn ⟨t, ht⟩ := by
  unfold completedBoundaryLoop
  rw [Set.projIcc_of_mem _ ht]

/-- Evaluation on the left half of the completed loop. -/
theorem completedBoundaryLoop_eq_left
    (D : SelectedBoundaryTopologyInput E U) {t : ℝ}
    (htZero : 0 ≤ t) (htOne : t ≤ 1) :
    D.completedBoundaryLoop t =
      D.leftCompletedChainPath ⟨t, htZero, htOne⟩ := by
  rw [D.completedBoundaryLoop_of_mem ⟨htZero, htOne.trans (by norm_num)⟩,
    D.completedBoundaryLoopOn_eq_left _ htOne]

/-- Evaluation on the right half of the completed loop. -/
theorem completedBoundaryLoop_eq_right
    (D : SelectedBoundaryTopologyInput E U) {t : ℝ}
    (htOne : 1 ≤ t) (htTwo : t ≤ 2) :
    D.completedBoundaryLoop t =
      D.rightCompletedChainReversedPath ⟨t, htOne, htTwo⟩ := by
  rw [D.completedBoundaryLoop_of_mem ⟨(by linarith), htTwo⟩,
    D.completedBoundaryLoopOn_eq_right _ htOne]

@[simp] theorem completedBoundaryLoop_zero
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoop 0 = D.lowerSplitPoint := by
  rw [D.completedBoundaryLoop_eq_left (by norm_num) (by norm_num),
    D.leftCompletedChainPath_zero]

@[simp] theorem completedBoundaryLoop_one
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoop 1 = D.upperSplitPoint := by
  rw [D.completedBoundaryLoop_eq_left (by norm_num) le_rfl,
    D.leftCompletedChainPath_one]

@[simp] theorem completedBoundaryLoop_two
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoop 2 = D.lowerSplitPoint := by
  rw [D.completedBoundaryLoop_eq_right (by norm_num) le_rfl,
    D.rightCompletedChainReversedPath_two]

/-- The completed loop closes at the two endpoints of its positive-length
parameter interval. -/
theorem completedBoundaryLoop_closed
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoop 0 = D.completedBoundaryLoop 2 := by
  rw [D.completedBoundaryLoop_zero, D.completedBoundaryLoop_two]

/-- The subtype loop traverses exactly the two completed chains. -/
theorem range_completedBoundaryLoopOn
    (D : SelectedBoundaryTopologyInput E U) :
    Set.range D.completedBoundaryLoopOn =
      D.leftCompletedChain ∪ D.rightCompletedChain := by
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    rcases le_total t.1 1 with ht | ht
    · rw [D.completedBoundaryLoopOn_eq_left t ht]
      exact Or.inl (D.leftCompletedChainHomeomorph _).property
    · rw [D.completedBoundaryLoopOn_eq_right t ht]
      exact Or.inr
        (D.rightCompletedChainHomeomorph (reverseOneTwoToUnit _)).property
  · rintro p (hpLeft | hpRight)
    · let q : D.leftCompletedChain := ⟨p, hpLeft⟩
      let s : Set.Icc (0 : ℝ) 1 := D.leftCompletedChainHomeomorph.symm q
      let t : Set.Icc (0 : ℝ) 2 :=
        ⟨s.1, s.property.1, s.property.2.trans (by norm_num)⟩
      refine ⟨t, ?_⟩
      rw [D.completedBoundaryLoopOn_eq_left t s.property.2]
      change (D.leftCompletedChainHomeomorph
        ⟨s.1, s.property⟩).1 = p
      have hsub : (⟨s.1, s.property⟩ : Set.Icc (0 : ℝ) 1) = s :=
        Subtype.ext rfl
      rw [hsub]
      exact congrArg Subtype.val
        (D.leftCompletedChainHomeomorph.apply_symm_apply q)
    · let q : D.rightCompletedChain := ⟨p, hpRight⟩
      let s : Set.Icc (0 : ℝ) 1 := D.rightCompletedChainHomeomorph.symm q
      let t : Set.Icc (0 : ℝ) 2 :=
        ⟨2 - s.1, by
          constructor <;> linarith [s.property.1, s.property.2]⟩
      refine ⟨t, ?_⟩
      have htOne : 1 ≤ t.1 := by
        dsimp [t]
        linarith [s.property.2]
      rw [D.completedBoundaryLoopOn_eq_right t htOne]
      change (D.rightCompletedChainHomeomorph
        (reverseOneTwoToUnit
          ⟨t.1, htOne, t.property.2⟩)).1 = p
      have hreverse :
          reverseOneTwoToUnit ⟨t.1, htOne, t.property.2⟩ = s := by
        apply Subtype.ext
        change 2 - (2 - s.1) = s.1
        ring
      rw [hreverse]
      exact congrArg Subtype.val
        (D.rightCompletedChainHomeomorph.apply_symm_apply q)

/-- The image of the real defining interval is exactly the actual complete
frontier of the selected representative. -/
theorem image_completedBoundaryLoop_Icc
    (D : SelectedBoundaryTopologyInput E U) :
    D.completedBoundaryLoop '' Set.Icc (0 : ℝ) 2 =
      frontier (CMVRelaxation.aeOpenRepresentative E) := by
  calc
    D.completedBoundaryLoop '' Set.Icc (0 : ℝ) 2 =
        Set.range D.completedBoundaryLoopOn := by
      ext p
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, (D.completedBoundaryLoop_of_mem ht).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t.1, t.property, by
          simpa only using D.completedBoundaryLoop_of_mem t.property⟩
    _ = D.leftCompletedChain ∪ D.rightCompletedChain :=
      D.range_completedBoundaryLoopOn
    _ = frontier (CMVRelaxation.aeOpenRepresentative E) :=
      D.frontier_eq_union_completedChains.symm

/-- No point is repeated before the terminal endpoint of the completed loop. -/
theorem completedBoundaryLoop_injOn_Ico
    (D : SelectedBoundaryTopologyInput E U) :
    Set.InjOn D.completedBoundaryLoop (Set.Ico (0 : ℝ) 2) := by
  intro s hs t ht hst
  by_cases hsOne : s ≤ 1
  · by_cases htOne : t ≤ 1
    · have hpaths :
          D.leftCompletedChainPath ⟨s, hs.1, hsOne⟩ =
            D.leftCompletedChainPath ⟨t, ht.1, htOne⟩ := by
        rw [← D.completedBoundaryLoop_eq_left hs.1 hsOne,
          ← D.completedBoundaryLoop_eq_left ht.1 htOne]
        exact hst
      exact congrArg Subtype.val
        (D.leftCompletedChainPath_injective hpaths)
    · have htOne' : 1 < t := lt_of_not_ge htOne
      have hne := D.leftCompletedChainPath_ne_rightCompletedChainReversedPath
        ⟨s, hs.1, hsOne⟩ ⟨t, htOne'.le, ht.2.le⟩ htOne' ht.2
      exfalso
      apply hne
      rw [← D.completedBoundaryLoop_eq_left hs.1 hsOne,
        ← D.completedBoundaryLoop_eq_right htOne'.le ht.2.le]
      exact hst
  · have hsOne' : 1 < s := lt_of_not_ge hsOne
    by_cases htOne : t ≤ 1
    · have hne := D.leftCompletedChainPath_ne_rightCompletedChainReversedPath
        ⟨t, ht.1, htOne⟩ ⟨s, hsOne'.le, hs.2.le⟩ hsOne' hs.2
      exfalso
      apply hne
      rw [← D.completedBoundaryLoop_eq_left ht.1 htOne,
        ← D.completedBoundaryLoop_eq_right hsOne'.le hs.2.le]
      exact hst.symm
    · have htOne' : 1 < t := lt_of_not_ge htOne
      have hpaths :
          D.rightCompletedChainReversedPath ⟨s, hsOne'.le, hs.2.le⟩ =
            D.rightCompletedChainReversedPath ⟨t, htOne'.le, ht.2.le⟩ := by
        rw [← D.completedBoundaryLoop_eq_right hsOne'.le hs.2.le,
          ← D.completedBoundaryLoop_eq_right htOne'.le ht.2.le]
        exact hst
      exact congrArg Subtype.val
        (D.rightCompletedChainReversedPath_injective hpaths)

/-- The actual complete frontier is connected, now derived from the simple
closed-interval loop rather than assumed by the topology input. -/
theorem isConnected_frontier_aeOpenRepresentative
    (D : SelectedBoundaryTopologyInput E U) :
    IsConnected (frontier (CMVRelaxation.aeOpenRepresentative E)) := by
  rw [← D.image_completedBoundaryLoop_Icc]
  exact (isConnected_Icc (by norm_num)).image D.completedBoundaryLoop
    D.continuous_completedBoundaryLoop.continuousOn

end SelectedBoundaryTopologyInput
end CMVBoundaryLocalAtlas
