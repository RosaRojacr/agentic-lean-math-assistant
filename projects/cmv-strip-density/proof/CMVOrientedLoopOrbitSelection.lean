import CMVOrientedLoopPathRealization

/-!
# Nonduplicating boundary-walk orbits

The two fixed-point-free endpoint exchanges on finite boundary half-edges form
alternating cycles.  This file proves that crossing an arc reverses the
canonical walk orientation and never remains in the same directed orbit.  It
then packages the two opposite directed traversals of each geometric boundary
cycle without identifying either direction with an occupied-side orientation.
-/

open Set Function

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace BoundaryHalfSpaceAtlas
namespace FiniteChartCutSystem

variable {O : Set PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- Switching twice at one cut vertex returns to the original half-edge. -/
@[simp] theorem switchHalfEdge_switchHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.switchHalfEdge (D.switchHalfEdge h) = h := by
  exact D.switchHalfEdgeFn_involutive h

@[simp] theorem switchHalfEdge_symm
    (D : FiniteChartCutSystem A) :
    D.switchHalfEdge.symm = D.switchHalfEdge :=
  D.switchHalfEdgeFn_involutive.toPerm_symm

@[simp] theorem crossHalfEdge_symm
    (D : FiniteChartCutSystem A) :
    D.crossHalfEdge.symm = D.crossHalfEdge := by
  apply Equiv.ext
  intro h
  apply D.crossHalfEdge.injective
  simp

/-- Crossing conjugates the directed traversal permutation to its inverse. -/
theorem cross_conj_walkStep
    (D : FiniteChartCutSystem A) :
    D.crossHalfEdge * D.walkStep * D.crossHalfEdge =
      D.walkStep⁻¹ := by
  have hc : D.crossHalfEdge * D.crossHalfEdge = 1 := by
    apply Equiv.ext
    intro h
    simp [Equiv.Perm.mul_apply]
  change D.crossHalfEdge *
      (D.crossHalfEdge * D.switchHalfEdge) * D.crossHalfEdge =
    (D.crossHalfEdge * D.switchHalfEdge)⁻¹
  rw [← mul_assoc, hc, one_mul, mul_inv_rev]
  change D.switchHalfEdge * D.crossHalfEdge =
    D.switchHalfEdge.symm * D.crossHalfEdge.symm
  rw [D.crossHalfEdge_symm, D.switchHalfEdge_symm]

/-- Crossing both starting half-edges preserves the underlying directed orbit,
while reversing its traversal order. -/
theorem sameCycle_crossHalfEdge
    (D : FiniteChartCutSystem A) {h k : D.HalfEdge}
    (hhk : D.walkStep.SameCycle h k) :
    D.walkStep.SameCycle (D.crossHalfEdge h) (D.crossHalfEdge k) := by
  have hconj := hhk.conj (g := D.crossHalfEdge)
  have hcInv : D.crossHalfEdge⁻¹ = D.crossHalfEdge :=
    D.crossHalfEdge_symm
  rw [hcInv, D.cross_conj_walkStep] at hconj
  exact hconj.of_inv

/-- One walk step cannot fix a half-edge: it arrives at the other endpoint of
an arc different from the incoming arc. -/
theorem walkStep_ne (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.walkStep h ≠ h := by
  intro heq
  have harc := congrArg (fun z : D.HalfEdge => z.1.2) heq
  change (D.crossHalfEdge (D.switchHalfEdge h)).1.2 = h.1.2 at harc
  rw [D.crossHalfEdge_arc] at harc
  exact D.switchHalfEdge_arc_ne h harc
/-- Every closed walk contains at least two actual arc traversals.  This rules
out a degenerate one-piece period before geometric concatenation. -/
theorem two_le_minimalPeriod_walkStep
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    2 ≤ Function.minimalPeriod
      (D.walkStep : D.HalfEdge → D.HalfEdge) h := by
  have hpos : 0 < Function.minimalPeriod
      (D.walkStep : D.HalfEdge → D.HalfEdge) h :=
    Function.minimalPeriod_pos_of_mem_periodicPts
      (D.walkStep_mem_periodicPts h)
  have hone : Function.minimalPeriod
      (D.walkStep : D.HalfEdge → D.HalfEdge) h ≠ 1 := by
    intro hperiod
    have hfixed :
        Function.IsFixedPt
          (D.walkStep : D.HalfEdge → D.HalfEdge) h :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mp hperiod
    exact D.walkStep_ne h hfixed
  omega


/-- Crossing conjugates a forward walk step to a backward step.  The
sandwich form avoids introducing integer iterates. -/
@[simp] theorem walkStep_crossHalfEdge_walkStep
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.walkStep (D.crossHalfEdge (D.walkStep h)) =
      D.crossHalfEdge h := by
  simp [walkStep]

/-- The same sandwich identity holds for every finite iterate. -/
theorem iterate_walkStep_crossHalfEdge_iterate
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) (n : ℕ) :
    ((D.walkStep : D.HalfEdge → D.HalfEdge)^[n])
        (D.crossHalfEdge
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h)) =
      D.crossHalfEdge h := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply,
        Function.iterate_succ_apply']
      rw [D.walkStep_crossHalfEdge_walkStep]
      exact ih

/-- The endpoint-crossing involution sends no half-edge into its own directed
walk orbit.  If it did after an even number of steps, `crossHalfEdge` would
fix the midpoint; after an odd number, `switchHalfEdge` would fix the
midpoint. -/
theorem crossHalfEdge_not_mem_walkCycle
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.crossHalfEdge h ∉ D.walkCycle h := by
  intro hmem
  rw [walkCycle,
    mem_periodicOrbit_iff (D.walkStep_mem_periodicPts h)] at hmem
  obtain ⟨k, hk⟩ := hmem
  rcases Nat.even_or_odd' k with ⟨i, rfl | rfl⟩
  · apply D.crossHalfEdge_ne
      (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)
    apply D.walkStep.injective.iterate i
    calc
      ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i])
          (D.crossHalfEdge
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)) =
          D.crossHalfEdge h :=
        D.iterate_walkStep_crossHalfEdge_iterate h i
      _ = ((D.walkStep : D.HalfEdge → D.HalfEdge)^[2 * i]) h := hk.symm
      _ = ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i])
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h) := by
        rw [show 2 * i = i + i by omega,
          Function.iterate_add_apply]
  · apply D.switchHalfEdge_arc_ne
      (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)
    have hfixed :
        D.switchHalfEdge
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h) =
          ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h := by
      apply D.walkStep.injective.iterate (i + 1)
      have hsandwich :=
        D.iterate_walkStep_crossHalfEdge_iterate h (i + 1)
      calc
        ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i + 1])
            (D.switchHalfEdge
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)) =
            ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i + 1])
              (D.crossHalfEdge
                (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i + 1]) h)) := by
          congr 1
          rw [Function.iterate_succ_apply']
          simp [walkStep]
        _ = D.crossHalfEdge h := hsandwich
        _ = ((D.walkStep : D.HalfEdge → D.HalfEdge)^[2 * i + 1]) h := hk.symm
        _ = ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i + 1])
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h) := by
          rw [show 2 * i + 1 = (i + 1) + i by omega,
            Function.iterate_add_apply]
    exact congrArg (fun z : D.HalfEdge => z.1.2) hfixed

/-- The two endpoint directions of one arc generate disjoint directed walk
cycles. -/
theorem disjoint_walkCycle_crossHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    ∀ e : D.HalfEdge,
      e ∈ D.walkCycle h →
        e ∉ D.walkCycle (D.crossHalfEdge h) := by
  intro e he hce
  rw [walkCycle,
    mem_periodicOrbit_iff (D.walkStep_mem_periodicPts h)] at he
  obtain ⟨n, hn⟩ := he
  rw [walkCycle,
    mem_periodicOrbit_iff
      (D.walkStep_mem_periodicPts (D.crossHalfEdge h))] at hce
  obtain ⟨m, hm⟩ := hce
  have heqForward :
      D.walkCycle e = D.walkCycle h := by
    rw [walkCycle, walkCycle, ← hn]
    exact periodicOrbit_apply_iterate_eq
      (D.walkStep_mem_periodicPts h) n
  have heqReverse :
      D.walkCycle e = D.walkCycle (D.crossHalfEdge h) := by
    rw [walkCycle, walkCycle, ← hm]
    exact periodicOrbit_apply_iterate_eq
      (D.walkStep_mem_periodicPts (D.crossHalfEdge h)) m
  apply D.crossHalfEdge_not_mem_walkCycle h
  have hself :
      D.crossHalfEdge h ∈ D.walkCycle (D.crossHalfEdge h) := by
    exact self_mem_periodicOrbit
      (D.walkStep_mem_periodicPts (D.crossHalfEdge h))
  rw [← heqReverse, heqForward] at hself
  exact hself

/-- During one minimal directed period, the traversal selects every geometric
arc at most once.  A repeated arc would either repeat the half-edge before the
minimal period or identify the directed cycle with its crossed reverse. -/
theorem traversedArc_injOn
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    (Set.Iio
      (minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h)).InjOn
        (fun n =>
          (D.switchHalfEdge
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h)).1.2) := by
  intro i hi j hj hij
  let a := ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h
  let b := ((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h
  have hsarc : (D.switchHalfEdge a).1.2 =
      (D.switchHalfEdge b).1.2 := hij
  rcases D.eq_or_eq_crossHalfEdge_of_arc_eq hsarc with heq | hcross
  · exact iterate_injOn_Iio_minimalPeriod hi hj
      (D.switchHalfEdge.injective heq)
  · exfalso
    have hop : D.crossHalfEdge (D.walkStep a) = D.walkStep b := by
      change D.crossHalfEdge (D.crossHalfEdge (D.switchHalfEdge a)) =
        D.crossHalfEdge (D.switchHalfEdge b)
      rw [D.crossHalfEdge_crossHalfEdge]
      exact hcross
    apply D.crossHalfEdge_not_mem_walkCycle (D.walkStep a)
    rw [hop]
    have hcycle :
        D.walkCycle (D.walkStep a) = D.walkCycle h := by
      change periodicOrbit (D.walkStep : D.HalfEdge → D.HalfEdge)
          (D.walkStep
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)) =
        periodicOrbit (D.walkStep : D.HalfEdge → D.HalfEdge) h
      simpa only [Function.iterate_succ_apply'] using
        periodicOrbit_apply_iterate_eq
          (D.walkStep_mem_periodicPts h) (i + 1)
    rw [hcycle, walkCycle,
      mem_periodicOrbit_iff (D.walkStep_mem_periodicPts h)]
    refine ⟨j + 1, ?_⟩
    dsimp only [b]
    simp only [Function.iterate_succ_apply']

/-- Directed walk cycles modulo cyclic change of their starting half-edge. -/
def DirectedWalkOrbit (D : FiniteChartCutSystem A) :=
  Quotient (Equiv.Perm.SameCycle.setoid D.walkStep)

instance finite_directedWalkOrbit
    (D : FiniteChartCutSystem A) : Finite D.DirectedWalkOrbit := by
  let _ : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  let _ : Finite D.HalfEdge := by infer_instance
  exact Quotient.finite (Equiv.Perm.SameCycle.setoid D.walkStep)

/-- Crossing a half-edge reverses a directed walk orbit. -/
def reverseDirectedWalkOrbit
    (D : FiniteChartCutSystem A) :
    D.DirectedWalkOrbit → D.DirectedWalkOrbit :=
  Quotient.map D.crossHalfEdge fun _ _ hhk =>
    D.sameCycle_crossHalfEdge hhk

@[simp] theorem reverseDirectedWalkOrbit_reverseDirectedWalkOrbit
    (D : FiniteChartCutSystem A) (q : D.DirectedWalkOrbit) :
    D.reverseDirectedWalkOrbit (D.reverseDirectedWalkOrbit q) = q := by
  refine Quotient.inductionOn q ?_
  intro h
  change Quotient.mk _ (D.crossHalfEdge (D.crossHalfEdge h)) =
    Quotient.mk _ h
  rw [D.crossHalfEdge_crossHalfEdge]

/-- Two directed orbits represent the same unoriented loop exactly when they
coincide or one is the crossed reverse of the other. -/
def unorientedWalkOrbitSetoid
    (D : FiniteChartCutSystem A) : Setoid D.DirectedWalkOrbit where
  r q r := q = r ∨ D.reverseDirectedWalkOrbit q = r
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro q r hqr
      rcases hqr with rfl | hreverse
      · exact Or.inl rfl
      · exact Or.inr <| calc
          D.reverseDirectedWalkOrbit r =
              D.reverseDirectedWalkOrbit
                (D.reverseDirectedWalkOrbit q) :=
            congrArg D.reverseDirectedWalkOrbit hreverse.symm
          _ = q := D.reverseDirectedWalkOrbit_reverseDirectedWalkOrbit q
    · intro q r s hqr hrs
      rcases hqr with rfl | hqr <;> rcases hrs with rfl | hrs
      · exact Or.inl rfl
      · exact Or.inr hrs
      · exact Or.inr hqr
      · exact Or.inl <| calc
          q = D.reverseDirectedWalkOrbit
                (D.reverseDirectedWalkOrbit q) :=
            (D.reverseDirectedWalkOrbit_reverseDirectedWalkOrbit q).symm
          _ = D.reverseDirectedWalkOrbit r :=
            congrArg D.reverseDirectedWalkOrbit hqr
          _ = s := hrs

/-- Canonical finite index type for walk cycles modulo both base-point change
and reversal. -/
def BoundaryLoopIndex (D : FiniteChartCutSystem A) :=
  Quotient D.unorientedWalkOrbitSetoid

instance finite_boundaryLoopIndex
    (D : FiniteChartCutSystem A) : Finite D.BoundaryLoopIndex :=
  Quotient.finite D.unorientedWalkOrbitSetoid

/-- The unoriented loop index containing a half-edge. -/
def boundaryLoopIndexOfHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.BoundaryLoopIndex :=
  Quotient.mk _ (Quotient.mk _ h)

/-- Equality of loop indices is exactly cyclic re-basing or crossed reversal. -/
theorem boundaryLoopIndexOfHalfEdge_eq_iff
    (D : FiniteChartCutSystem A) (h k : D.HalfEdge) :
    D.boundaryLoopIndexOfHalfEdge h =
        D.boundaryLoopIndexOfHalfEdge k ↔
      D.walkStep.SameCycle h k ∨
        D.walkStep.SameCycle (D.crossHalfEdge h) k := by
  constructor
  · intro heq
    have horbit := Quotient.exact heq
    rcases horbit with hsame | hreverse
    · exact Or.inl (Quotient.exact hsame)
    · exact Or.inr (Quotient.exact hreverse)
  · rintro (hsame | hreverse)
    · exact Quotient.sound (Or.inl (Quotient.sound hsame))
    · exact Quotient.sound (Or.inr (Quotient.sound hreverse))

/-- Crossing to the opposite endpoint direction does not change the
unoriented loop index. -/
@[simp] theorem boundaryLoopIndexOfHalfEdge_crossHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.boundaryLoopIndexOfHalfEdge (D.crossHalfEdge h) =
      D.boundaryLoopIndexOfHalfEdge h := by
  apply (D.boundaryLoopIndexOfHalfEdge_eq_iff
    (D.crossHalfEdge h) h).2
  right
  rw [D.crossHalfEdge_crossHalfEdge]

/-- One forward traversal step stays in the same unoriented loop. -/
@[simp] theorem boundaryLoopIndexOfHalfEdge_walkStep
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.boundaryLoopIndexOfHalfEdge (D.walkStep h) =
      D.boundaryLoopIndexOfHalfEdge h := by
  apply (D.boundaryLoopIndexOfHalfEdge_eq_iff (D.walkStep h) h).2
  left
  exact Equiv.Perm.sameCycle_apply_left.mpr
    Equiv.Perm.SameCycle.rfl

/-- Switching to the other arc at a vertex stays in the same unoriented loop:
crossing that switched half-edge is exactly the next walk state. -/
@[simp] theorem boundaryLoopIndexOfHalfEdge_switchHalfEdge
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.boundaryLoopIndexOfHalfEdge (D.switchHalfEdge h) =
      D.boundaryLoopIndexOfHalfEdge h := by
  calc
    D.boundaryLoopIndexOfHalfEdge (D.switchHalfEdge h) =
        D.boundaryLoopIndexOfHalfEdge
          (D.crossHalfEdge (D.switchHalfEdge h)) :=
      (D.boundaryLoopIndexOfHalfEdge_crossHalfEdge
        (D.switchHalfEdge h)).symm
    _ = D.boundaryLoopIndexOfHalfEdge (D.walkStep h) := by
      rfl
    _ = D.boundaryLoopIndexOfHalfEdge h :=
      D.boundaryLoopIndexOfHalfEdge_walkStep h

/-- Every finite iterate stays in the same unoriented loop. -/
theorem boundaryLoopIndexOfHalfEdge_iterate_walkStep
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) (n : ℕ) :
    D.boundaryLoopIndexOfHalfEdge
        (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h) =
      D.boundaryLoopIndexOfHalfEdge h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',
        D.boundaryLoopIndexOfHalfEdge_walkStep, ih]


/-- The unique unoriented walk-orbit index assigned to a compact arc.  The
left endpoint is only a canonical representative; reversal is quotiented. -/
def arcBoundaryLoopIndex
    (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.BoundaryLoopIndex :=
  D.boundaryLoopIndexOfHalfEdge (D.endpointHalfEdge (e, false))

/-- Either endpoint direction of an arc has the arc's unique unoriented loop
index. -/
theorem arcBoundaryLoopIndex_eq_of_halfEdge_arc
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    D.arcBoundaryLoopIndex h.1.2 =
      D.boundaryLoopIndexOfHalfEdge h := by
  let g := D.endpointHalfEdge (h.1.2, false)
  have hsameArc : g.1.2 = h.1.2 := by
    simp only [g, D.endpointHalfEdge_arc]
  rcases D.eq_or_eq_crossHalfEdge_of_arc_eq hsameArc with heq | heq
  · exact congrArg D.boundaryLoopIndexOfHalfEdge heq
  · calc
      D.arcBoundaryLoopIndex h.1.2 =
          D.boundaryLoopIndexOfHalfEdge g := rfl
      _ = D.boundaryLoopIndexOfHalfEdge (D.crossHalfEdge h) :=
        congrArg D.boundaryLoopIndexOfHalfEdge heq
      _ = D.boundaryLoopIndexOfHalfEdge h :=
        D.boundaryLoopIndexOfHalfEdge_crossHalfEdge h
/-- A chosen half-edge representing one unoriented walk orbit. -/
noncomputable def boundaryLoopHalfEdge
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    D.HalfEdge :=
  Quotient.out (Quotient.out j)

/-- The chosen representative of an unoriented orbit represents exactly that
orbit. -/
@[simp] theorem boundaryLoopIndexOfHalfEdge_boundaryLoopHalfEdge
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    D.boundaryLoopIndexOfHalfEdge (D.boundaryLoopHalfEdge j) = j := by
  unfold boundaryLoopHalfEdge boundaryLoopIndexOfHalfEdge
  have hinner :
      (Quotient.mk (Equiv.Perm.SameCycle.setoid D.walkStep)
          (Quotient.out (Quotient.out j)) : D.DirectedWalkOrbit) =
        Quotient.out j :=
    Quotient.out_eq (Quotient.out j)
  exact
    (congrArg
      (fun q : D.DirectedWalkOrbit =>
        Quotient.mk D.unorientedWalkOrbitSetoid q) hinner).trans
      (Quotient.out_eq j)

/-- Every unoriented walk orbit occurs in the selected finite family. -/
theorem boundaryLoopIndexOfHalfEdge_surjective
    (D : FiniteChartCutSystem A) :
    Function.Surjective D.boundaryLoopIndexOfHalfEdge := by
  intro j
  refine ⟨D.boundaryLoopHalfEdge j, ?_⟩
  unfold boundaryLoopHalfEdge boundaryLoopIndexOfHalfEdge
  have hinner :
      (Quotient.mk (Equiv.Perm.SameCycle.setoid D.walkStep)
          (Quotient.out (Quotient.out j)) : D.DirectedWalkOrbit) =
        Quotient.out j :=
    Quotient.out_eq (Quotient.out j)
  exact
    (congrArg
      (fun q : D.DirectedWalkOrbit =>
        Quotient.mk D.unorientedWalkOrbitSetoid q) hinner).trans
      (Quotient.out_eq j)

/-- An empty cropped frontier produces the empty loop family. -/
theorem isEmpty_boundaryLoopIndex_of_frontier_eq_empty
    (D : FiniteChartCutSystem A) (hfrontier : frontier O = ∅) :
    IsEmpty D.BoundaryLoopIndex :=
  ⟨fun j => by
    have hv := (D.boundaryLoopHalfEdge j).1.1.1.2
    have hmemEmpty :
        (D.boundaryLoopHalfEdge j).1.1.1.1 ∈ (∅ : Set PlanePoint) :=
      hfrontier ▸ hv
    exact hmemEmpty⟩

/-- The closed walk using exactly the minimal positive traversal period. -/
noncomputable def minimalGeometricWalkLoop
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    D.GeometricWalkLoop e where
  period := minimalPeriod
    (D.walkStep : D.HalfEdge → D.HalfEdge) e
  period_pos := minimalPeriod_pos_of_mem_periodicPts
    (D.walkStep_mem_periodicPts e)
  period_eq := iterate_minimalPeriod

@[simp] theorem minimalGeometricWalkLoop_period
    (D : FiniteChartCutSystem A) (e : D.HalfEdge) :
    (D.minimalGeometricWalkLoop e).period =
      minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) e :=
  rfl

/-- One actual closed frontier path for each nonduplicating loop index. -/
noncomputable def boundaryGeometricWalkLoop
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    D.GeometricWalkLoop (D.boundaryLoopHalfEdge j) :=
  D.minimalGeometricWalkLoop (D.boundaryLoopHalfEdge j)
/-- Every selected boundary loop is assembled from at least two actual compact
arcs. -/
theorem boundaryGeometricWalkLoop_period_two_le
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    2 ≤ (D.boundaryGeometricWalkLoop j).period := by
  exact D.two_le_minimalPeriod_walkStep (D.boundaryLoopHalfEdge j)


/-- Same-cycle membership has a representative before the starting half-edge's
minimal period, rather than merely before the order of the ambient finite
permutation. -/
theorem exists_lt_minimalPeriod_iterate_eq_of_sameCycle
    (D : FiniteChartCutSystem A) (h g : D.HalfEdge)
    (hsame : D.walkStep.SameCycle h g) :
    ∃ n : ℕ,
      n < minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h ∧
        ((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h = g := by
  let _ : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  let _ : Finite D.HalfEdge := by infer_instance
  obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
  refine ⟨n % minimalPeriod
      (D.walkStep : D.HalfEdge → D.HalfEdge) h,
    Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts
      (D.walkStep_mem_periodicPts h)), ?_⟩
  rw [iterate_mod_minimalPeriod_eq]
  simpa only [D.walkStep.iterate_eq_pow] using hn

/-- Every arc traversed during a minimal directed period belongs to the
starting half-edge's unoriented loop. -/
theorem arcBoundaryLoopIndex_traversedArc
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) (n : ℕ) :
    D.arcBoundaryLoopIndex
        (D.switchHalfEdge
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h)).1.2 =
      D.boundaryLoopIndexOfHalfEdge h := by
  let state :=
    ((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h
  calc
    D.arcBoundaryLoopIndex (D.switchHalfEdge state).1.2 =
        D.boundaryLoopIndexOfHalfEdge (D.switchHalfEdge state) :=
      D.arcBoundaryLoopIndex_eq_of_halfEdge_arc (D.switchHalfEdge state)
    _ = D.boundaryLoopIndexOfHalfEdge state :=
      D.boundaryLoopIndexOfHalfEdge_switchHalfEdge state
    _ = D.boundaryLoopIndexOfHalfEdge h :=
      D.boundaryLoopIndexOfHalfEdge_iterate_walkStep h n

/-- Conversely, every compact arc in an unoriented loop is selected by some
step of the directed minimal traversal chosen by the quotient. -/
theorem exists_lt_minimalPeriod_traversedArc_eq
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) (e : D.ArcIndex)
    (he :
      D.arcBoundaryLoopIndex e =
        D.boundaryLoopIndexOfHalfEdge h) :
    ∃ n : ℕ,
      n < minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h ∧
        (D.switchHalfEdge
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h)).1.2 = e := by
  let g := D.endpointHalfEdge (e, false)
  have hindex :
      D.boundaryLoopIndexOfHalfEdge h =
        D.boundaryLoopIndexOfHalfEdge g := by
    simpa only [arcBoundaryLoopIndex, g] using he.symm
  rcases (D.boundaryLoopIndexOfHalfEdge_eq_iff h g).mp hindex with
      hsame | hreverse
  · let target := g
    have htargetSame : D.walkStep.SameCycle h target := hsame
    have htargetArc : target.1.2 = e := by
      simp only [target, g, D.endpointHalfEdge_arc]
    let previous := D.walkStep.symm target
    have hpreviousSame : D.walkStep.SameCycle h previous := by
      exact Equiv.Perm.sameCycle_symm_apply_right.mpr htargetSame
    obtain ⟨n, hn, hnstate⟩ :=
      D.exists_lt_minimalPeriod_iterate_eq_of_sameCycle
        h previous hpreviousSame
    refine ⟨n, hn, ?_⟩
    rw [hnstate]
    have hstep :
        D.walkStep previous = target :=
      D.walkStep.apply_symm_apply target
    have harc := congrArg (fun z : D.HalfEdge => z.1.2) hstep
    change
      (D.crossHalfEdge (D.switchHalfEdge previous)).1.2 =
        target.1.2 at harc
    rw [D.crossHalfEdge_arc] at harc
    exact harc.trans htargetArc
  · let target := D.crossHalfEdge g
    have htargetSame : D.walkStep.SameCycle h target := by
      have hcrossed := D.sameCycle_crossHalfEdge hreverse
      simpa only [D.crossHalfEdge_crossHalfEdge, target] using hcrossed
    have htargetArc : target.1.2 = e := by
      simp only [target, D.crossHalfEdge_arc, g, D.endpointHalfEdge_arc]
    let previous := D.walkStep.symm target
    have hpreviousSame : D.walkStep.SameCycle h previous := by
      exact Equiv.Perm.sameCycle_symm_apply_right.mpr htargetSame
    obtain ⟨n, hn, hnstate⟩ :=
      D.exists_lt_minimalPeriod_iterate_eq_of_sameCycle
        h previous hpreviousSame
    refine ⟨n, hn, ?_⟩
    rw [hnstate]
    have hstep :
        D.walkStep previous = target :=
      D.walkStep.apply_symm_apply target
    have harc := congrArg (fun z : D.HalfEdge => z.1.2) hstep
    change
      (D.crossHalfEdge (D.switchHalfEdge previous)).1.2 =
        target.1.2 at harc
    rw [D.crossHalfEdge_arc] at harc
    exact harc.trans htargetArc

/-- Every compact arc in an unoriented loop is visited exactly once by the
selected directed minimal traversal. -/
theorem existsUnique_lt_minimalPeriod_traversedArc_eq
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) (e : D.ArcIndex)
    (he :
      D.arcBoundaryLoopIndex e =
        D.boundaryLoopIndexOfHalfEdge h) :
    ∃! n : ℕ,
      n < minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h ∧
        (D.switchHalfEdge
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h)).1.2 = e := by
  obtain ⟨n, hn, harc⟩ :=
    D.exists_lt_minimalPeriod_traversedArc_eq h e he
  refine ⟨n, ⟨hn, harc⟩, ?_⟩
  intro m hm
  apply D.traversedArc_injOn h hm.1 hn
  exact hm.2.trans harc.symm

/-- A selected minimal closed path consists exactly of its finitely many
minimal-period traversal pieces. -/
theorem mem_range_boundaryGeometricWalkLoop_iff
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex)
    (q : PlanePoint) :
    q ∈ Set.range (D.boundaryGeometricWalkLoop j).path ↔
      ∃ n : ℕ,
        n < minimalPeriod
          (D.walkStep : D.HalfEdge → D.HalfEdge)
          (D.boundaryLoopHalfEdge j) ∧
        q ∈ Set.range
          (D.walkArcPath
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n])
              (D.boundaryLoopHalfEdge j))) := by
  change
    q ∈ Set.range
        (D.walkArcPathConcat (D.boundaryLoopHalfEdge j)
          (minimalPeriod
            (D.walkStep : D.HalfEdge → D.HalfEdge)
            (D.boundaryLoopHalfEdge j))) ↔ _
  exact D.mem_range_walkArcPathConcat_iff_of_pos
    (D.boundaryLoopHalfEdge j)
    (minimalPeriod_pos_of_mem_periodicPts
      (D.walkStep_mem_periodicPts (D.boundaryLoopHalfEdge j))) q

/-- The chosen closed path for one loop index has exactly the union of the
once-indexed compact arcs in that orbit.  Thus quotienting by reversal removes
directional duplication without losing any geometric arc. -/
theorem boundaryGeometricWalkLoop_path_range_eq_iUnion_arcs
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    Set.range (D.boundaryGeometricWalkLoop j).path =
      ⋃ e : {e : D.ArcIndex // D.arcBoundaryLoopIndex e = j},
        Set.range (D.finiteArcPathLR e.1) := by
  ext q
  rw [D.mem_range_boundaryGeometricWalkLoop_iff]
  constructor
  · rintro ⟨n, hn, hq⟩
    let e :=
      (D.switchHalfEdge
        (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n])
          (D.boundaryLoopHalfEdge j))).1.2
    have he : D.arcBoundaryLoopIndex e = j := by
      exact (D.arcBoundaryLoopIndex_traversedArc
        (D.boundaryLoopHalfEdge j) n).trans
          (D.boundaryLoopIndexOfHalfEdge_boundaryLoopHalfEdge j)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨e, he⟩, ?_⟩
    rw [D.finiteArcPathLR_range]
    rw [← D.walkArcPath_range
      (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n])
        (D.boundaryLoopHalfEdge j))]
    exact hq
  · intro hq
    obtain ⟨e, hqe⟩ := Set.mem_iUnion.mp hq
    have he :
        D.arcBoundaryLoopIndex e.1 =
          D.boundaryLoopIndexOfHalfEdge (D.boundaryLoopHalfEdge j) :=
      e.2.trans
        (D.boundaryLoopIndexOfHalfEdge_boundaryLoopHalfEdge j).symm
    obtain ⟨n, hn, harc⟩ :=
      D.exists_lt_minimalPeriod_traversedArc_eq
        (D.boundaryLoopHalfEdge j) e.1 he
    refine ⟨n, hn, ?_⟩
    rw [D.walkArcPath_range, harc, ← D.finiteArcPathLR_range]
    exact hqe
theorem boundaryGeometricWalkLoop_path_range_subset_frontier
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    Set.range (D.boundaryGeometricWalkLoop j).path ⊆ frontier O :=
  (D.boundaryGeometricWalkLoop j).path_range_subset_frontier

/-- The finite selected loop family covers the complete cropped frontier.
This includes the empty-frontier case, where the loop index type is empty. -/
theorem iUnion_boundaryGeometricWalkLoop_path_range_eq_frontier
    (D : FiniteChartCutSystem A) :
    (⋃ j : D.BoundaryLoopIndex,
        Set.range (D.boundaryGeometricWalkLoop j).path) =
      frontier O := by
  apply Subset.antisymm
  · exact Set.iUnion_subset fun j =>
      D.boundaryGeometricWalkLoop_path_range_subset_frontier j
  · intro q hq
    have hqArcs :
        q ∈ ⋃ e : D.ArcIndex, Set.range (D.finiteArcPathLR e) := by
      rw [D.iUnion_finiteArcPathLR_range_eq_frontier]
      exact hq
    obtain ⟨e, hqe⟩ := Set.mem_iUnion.mp hqArcs
    apply Set.mem_iUnion.mpr
    refine ⟨D.arcBoundaryLoopIndex e, ?_⟩
    rw [D.boundaryGeometricWalkLoop_path_range_eq_iUnion_arcs]
    apply Set.mem_iUnion.mpr
    exact ⟨⟨e, rfl⟩, hqe⟩

end FiniteChartCutSystem
end BoundaryHalfSpaceAtlas
end CMVBoundaryLocalAtlas
