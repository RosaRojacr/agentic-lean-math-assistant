import CMVOrientedLoopIncidence
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Cyclic traversal of the derived finite boundary arcs

Exact degree-two incidence gives two fixed-point-free exchanges on boundary
half-edges: exchange the incident arc at a vertex, then cross that arc to its
other endpoint. Their composite is the canonical finite traversal permutation.
-/

open Set Function

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace BoundaryHalfSpaceAtlas
namespace FiniteChartCutSystem

variable {O : Set PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- The left endpoint of an indexed compact arc, retained as a cut vertex. -/
noncomputable def leftVertex (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.cutPoints :=
  ⟨D.finiteArcLeftEndpoint e, (D.finiteArc_endpoints_mem_cutPoints e).1⟩

/-- The right endpoint of an indexed compact arc, retained as a cut vertex. -/
noncomputable def rightVertex (D : FiniteChartCutSystem A) (e : D.ArcIndex) :
    D.cutPoints :=
  ⟨D.finiteArcRightEndpoint e, (D.finiteArc_endpoints_mem_cutPoints e).2⟩

theorem leftVertex_ne_rightVertex (D : FiniteChartCutSystem A)
    (e : D.ArcIndex) : D.leftVertex e ≠ D.rightVertex e := by
  intro h
  exact D.finiteArcLeftEndpoint_ne_rightEndpoint e
    (congrArg (fun v : D.cutPoints => (v : FrontierSpace O)) h)

/-- A boundary half-edge is an incident vertex/arc pair. The nondependent
subtype representation keeps endpoint transport proof-irrelevant. -/
abbrev HalfEdge (D : FiniteChartCutSystem A) :=
  {p : D.cutPoints × D.ArcIndex |
    p.1.1 ∈ D.finiteArcClosure p.2}

/-- The two named endpoints of every compact arc enumerate its two
half-edges. -/
noncomputable def endpointHalfEdge (D : FiniteChartCutSystem A) :
    D.ArcIndex × Bool → D.HalfEdge
  | (e, false) =>
      ⟨(D.leftVertex e, e), by
        apply (D.cutPoint_mem_finiteArcClosure_iff_endpoint
          (D.leftVertex e).2 e).2
        exact Or.inl rfl⟩
  | (e, true) =>
      ⟨(D.rightVertex e, e), by
        apply (D.cutPoint_mem_finiteArcClosure_iff_endpoint
          (D.rightVertex e).2 e).2
        exact Or.inr rfl⟩

@[simp] theorem endpointHalfEdge_arc
    (D : FiniteChartCutSystem A) (p : D.ArcIndex × Bool) :
    (D.endpointHalfEdge p).1.2 = p.1 := by
  rcases p with ⟨e, b⟩
  cases b <;> rfl

theorem endpointHalfEdge_injective (D : FiniteChartCutSystem A) :
    Function.Injective D.endpointHalfEdge := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have hef : e = f := by
    simpa only [D.endpointHalfEdge_arc] using
      congrArg (fun z : D.HalfEdge => z.1.2) h
  subst f
  cases b <;> cases c
  · rfl
  · exfalso
    exact D.leftVertex_ne_rightVertex e
      (congrArg (fun z : D.HalfEdge => z.1.1) h)
  · exfalso
    exact D.leftVertex_ne_rightVertex e
      (congrArg (fun z : D.HalfEdge => z.1.1) h).symm
  · rfl

theorem endpointHalfEdge_surjective (D : FiniteChartCutSystem A) :
    Function.Surjective D.endpointHalfEdge := by
  rintro ⟨⟨v, e⟩, he⟩
  have hv :=
    (D.cutPoint_mem_finiteArcClosure_iff_endpoint v.2 e).mp he
  rcases hv with hvLeft | hvRight
  · refine ⟨(e, false), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hvLeft.symm
    · rfl
  · refine ⟨(e, true), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hvRight.symm
    · rfl

/-- Every arc has exactly its left and right half-edge. -/
noncomputable def endpointHalfEdgeEquiv (D : FiniteChartCutSystem A) :
    D.ArcIndex × Bool ≃ D.HalfEdge :=
  Equiv.ofBijective D.endpointHalfEdge
    ⟨D.endpointHalfEdge_injective, D.endpointHalfEdge_surjective⟩

@[simp] theorem endpointHalfEdgeEquiv_apply
    (D : FiniteChartCutSystem A) (p : D.ArcIndex × Bool) :
    D.endpointHalfEdgeEquiv p = D.endpointHalfEdge p :=
  rfl

@[simp] theorem endpointHalfEdgeEquiv_symm_endpointHalfEdge
    (D : FiniteChartCutSystem A) (p : D.ArcIndex × Bool) :
    D.endpointHalfEdgeEquiv.symm (D.endpointHalfEdge p) = p := by
  rw [← D.endpointHalfEdgeEquiv_apply]
  exact D.endpointHalfEdgeEquiv.symm_apply_apply p

/-- Cross an arc from one endpoint to the other while retaining its arc index. -/
noncomputable def crossHalfEdge (D : FiniteChartCutSystem A) :
    Equiv.Perm D.HalfEdge :=
  D.endpointHalfEdgeEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl D.ArcIndex) Equiv.boolNot).trans
      D.endpointHalfEdgeEquiv)

@[simp] theorem crossHalfEdge_arc (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) : (D.crossHalfEdge h).1.2 = h.1.2 := by
  let p := D.endpointHalfEdgeEquiv.symm h
  have hp : D.endpointHalfEdgeEquiv p = h :=
    D.endpointHalfEdgeEquiv.apply_symm_apply h
  rw [← hp]
  rcases p with ⟨e, b⟩
  simp only [crossHalfEdge, Equiv.trans_apply, Equiv.prodCongr_apply,
    endpointHalfEdgeEquiv_apply,
    endpointHalfEdgeEquiv_symm_endpointHalfEdge, endpointHalfEdge_arc]
  rfl

/-- Regard a half-edge as one of the two incident arcs at its vertex. -/
noncomputable def incidentAtHalfEdge (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) : D.IncidentArc h.1.1 :=
  ⟨h.1.2, h.2⟩

/-- Sharing an actual cut endpoint forces two finite arcs to lie in the same
complete frontier component. -/
theorem arcComponents_eq_of_common_incident
    (D : FiniteChartCutSystem A) {v : D.cutPoints} {e f : D.ArcIndex}
    (he : v.1 ∈ D.finiteArcClosure e)
    (hf : v.1 ∈ D.finiteArcClosure f) :
    connectedComponent (D.arcRepresentative e).1 =
      connectedComponent (D.arcRepresentative f).1 := by
  exact
    (connectedComponent_eq
      (D.finiteArcClosure_subset_connectedComponent e he)).trans
    (connectedComponent_eq
      (D.finiteArcClosure_subset_connectedComponent f hf)).symm

/-- The complete frontier component containing a half-edge's open arc. -/
def halfEdgeComponent (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    Set (FrontierSpace O) :=
  connectedComponent (D.arcRepresentative h.1.2).1

/-- Exchange the two incident arcs while retaining the vertex. -/
noncomputable def switchHalfEdgeFn (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) : D.HalfEdge :=
  let other :=
    (D.cutPointCoreNeighborhood h.1.1).otherIncidentArc
      (D.incidentAtHalfEdge h)
  ⟨(h.1.1, other.1), other.2⟩

theorem switchHalfEdgeFn_involutive (D : FiniteChartCutSystem A) :
    Function.Involutive D.switchHalfEdgeFn := by
  intro h
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      ((D.cutPointCoreNeighborhood h.1.1).otherIncidentArc
        ((D.cutPointCoreNeighborhood h.1.1).otherIncidentArc
          (D.incidentAtHalfEdge h))).1 = h.1.2
    exact congrArg Subtype.val
      (CutPointCoreNeighborhood.otherIncidentArc_otherIncidentArc
        (D.cutPointCoreNeighborhood h.1.1) (D.incidentAtHalfEdge h))

/-- At a cut vertex, exchange the two distinct incident arcs. -/
noncomputable def switchHalfEdge (D : FiniteChartCutSystem A) :
    Equiv.Perm D.HalfEdge :=
  D.switchHalfEdgeFn_involutive.toPerm

theorem switchHalfEdge_component (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) :
    D.halfEdgeComponent (D.switchHalfEdge h) = D.halfEdgeComponent h := by
  apply D.arcComponents_eq_of_common_incident (v := h.1.1)
  · exact (D.switchHalfEdge h).2
  · exact h.2

/-- Traverse away from the current vertex on the other incident arc and arrive
at that arc's opposite endpoint. -/
noncomputable def walkStep (D : FiniteChartCutSystem A) :
    Equiv.Perm D.HalfEdge :=
  D.switchHalfEdge.trans D.crossHalfEdge

theorem crossHalfEdge_component (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) :
    D.halfEdgeComponent (D.crossHalfEdge h) = D.halfEdgeComponent h := by
  unfold halfEdgeComponent
  rw [D.crossHalfEdge_arc]

/-- Every traversal step remains in one complete actual frontier component. -/
theorem walkStep_component (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) :
    D.halfEdgeComponent (D.walkStep h) = D.halfEdgeComponent h := by
  change
    D.halfEdgeComponent (D.crossHalfEdge (D.switchHalfEdge h)) =
      D.halfEdgeComponent h
  rw [D.crossHalfEdge_component, D.switchHalfEdge_component]

theorem iterate_walkStep_component (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) (n : ℕ) :
    D.halfEdgeComponent
        (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h) =
      D.halfEdgeComponent h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, D.walkStep_component]

/-- Every half-edge is periodic under the finite traversal permutation. -/

theorem walkStep_mem_periodicPts (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) :
    h ∈ periodicPts (D.walkStep : D.HalfEdge → D.HalfEdge) := by
  letI : Finite D.ArcIndex := D.finite_cutSpace_connectedComponents
  letI : Finite D.HalfEdge := by infer_instance
  exact D.walkStep.injective.mem_periodicPts h

/-- The canonical cyclic list generated from one directed boundary half-edge. -/
noncomputable def walkCycle (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) : Cycle D.HalfEdge :=
  periodicOrbit (D.walkStep : D.HalfEdge → D.HalfEdge) h

theorem walkCycle_length_pos (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) : 0 < (D.walkCycle h).length := by
  rw [walkCycle, periodicOrbit_length]
  exact minimalPeriod_pos_of_mem_periodicPts
    (D.walkStep_mem_periodicPts h)

theorem walkCycle_nodup (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) : (D.walkCycle h).Nodup := by
  exact nodup_periodicOrbit

/-- Consecutive entries, including the wraparound pair, are exactly related by
the canonical traversal permutation. -/
theorem walkCycle_chain (D : FiniteChartCutSystem A)
    (h : D.HalfEdge) :
    (D.walkCycle h).Chain (fun e f => D.walkStep e = f) := by
  rw [walkCycle, periodicOrbit_chain'
    (fun e f => D.walkStep e = f) (D.walkStep_mem_periodicPts h)]
  intro n
  exact (Function.iterate_succ_apply'
    (f := (D.walkStep : D.HalfEdge → D.HalfEdge)) n h).symm

/-- Every entry of a generated traversal cycle stays in the starting arc's
complete frontier component. -/
theorem halfEdgeComponent_eq_of_mem_walkCycle
    (D : FiniteChartCutSystem A) (h e : D.HalfEdge)
    (he : e ∈ D.walkCycle h) :
    D.halfEdgeComponent e = D.halfEdgeComponent h := by
  rw [walkCycle, mem_periodicOrbit_iff (D.walkStep_mem_periodicPts h)] at he
  obtain ⟨n, rfl⟩ := he
  exact D.iterate_walkStep_component h n

/-- The half-edge traversal is genuinely cyclic: every starting half-edge
returns after a positive finite number of steps. -/
theorem exists_pos_iterate_walkStep_eq
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    ∃ n : ℕ, 0 < n ∧
      ((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h = h := by
  have hperiodic := D.walkStep_mem_periodicPts h
  exact ⟨minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h,
    minimalPeriod_pos_of_mem_periodicPts hperiodic,
    iterate_minimalPeriod⟩

end FiniteChartCutSystem
end BoundaryHalfSpaceAtlas
end CMVBoundaryLocalAtlas
