import CMVOrientedLoopOrbitSelection

/-!
# Embedded geometry of selected boundary walks

The degree-two half-edge traversal cannot revisit a cut vertex during one
minimal period.  Consequently two distinct compact arcs in a selected walk
can meet only when their traversal indices are cyclically adjacent.
-/

open Set Function

noncomputable section

namespace CMVBoundaryLocalAtlas
namespace BoundaryHalfSpaceAtlas
namespace FiniteChartCutSystem

variable {O : Set PlanePoint} {A : BoundaryHalfSpaceAtlas O}

/-- In a two-element incidence fiber, the fixed-point-free exchange sends one
incident arc to every distinct incident arc. -/
theorem CutPointCoreNeighborhood.otherIncidentArc_eq_of_ne
    {D : FiniteChartCutSystem A} {v : D.cutPoints}
    (N : CutPointCoreNeighborhood D v) (e f : D.IncidentArc v)
    (hef : e ≠ f) :
    N.otherIncidentArc e = f := by
  let b := N.incidentArcEquivBool.symm e
  let c := N.incidentArcEquivBool.symm f
  have hb : N.incidentArcEquivBool b = e :=
    N.incidentArcEquivBool.apply_symm_apply e
  have hc : N.incidentArcEquivBool c = f :=
    N.incidentArcEquivBool.apply_symm_apply f
  have hbc : b ≠ c := by
    intro h
    apply hef
    calc
      e = N.incidentArcEquivBool b := hb.symm
      _ = N.incidentArcEquivBool c := congrArg N.incidentArcEquivBool h
      _ = f := hc
  have hnot : (!b : Bool) = c := Bool.not_eq_iff.mpr hbc
  rw [← hb, ← hc]
  simpa only [CutPointCoreNeighborhood.otherIncidentArc, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply, Equiv.boolNot_apply] using
      congrArg N.incidentArcEquivBool hnot

/-- Two half-edges at one cut vertex are either identical or exchanged by the
vertex switch.  This is the half-edge form of exact degree two. -/
theorem eq_or_eq_switchHalfEdge_of_vertex_eq
    (D : FiniteChartCutSystem A) {h g : D.HalfEdge}
    (hvertex : h.1.1 = g.1.1) :
    h = g ∨ h = D.switchHalfEdge g := by
  let g' : D.HalfEdge :=
    ⟨(h.1.1, g.1.2), by simpa only [hvertex] using g.2⟩
  have hg' : g' = g := by
    apply Subtype.ext
    apply Prod.ext
    · exact hvertex
    · rfl
  rw [← hg']
  let eh : D.IncidentArc h.1.1 := D.incidentAtHalfEdge h
  let eg : D.IncidentArc h.1.1 := D.incidentAtHalfEdge g'
  by_cases heq : eh = eg
  · left
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val heq
  · right
    have hother :=
      (D.cutPointCoreNeighborhood h.1.1).otherIncidentArc_eq_of_ne eg eh
        (Ne.symm heq)
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (congrArg Subtype.val hother).symm

set_option maxHeartbeats 800000 in
-- The subtype-fiber dichotomy and periodic-orbit normalization exceed the default.
/-- The visited cut vertices are pairwise distinct before the first return of
the traversal permutation. -/
theorem walkVertex_injOn_minimalPeriod
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    (Set.Iio
      (minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h)).InjOn
        (fun n =>
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h).1.1) := by
  intro i hi j hj hij
  let a := ((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h
  let b := ((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h
  rcases D.eq_or_eq_switchHalfEdge_of_vertex_eq (h := a) (g := b) hij with
      heq | hswitch
  · exact iterate_injOn_Iio_minimalPeriod hi hj heq
  · exfalso
    have hop : D.crossHalfEdge (D.walkStep b) = a := by
      change D.crossHalfEdge (D.crossHalfEdge (D.switchHalfEdge b)) = a
      rw [D.crossHalfEdge_crossHalfEdge]
      exact hswitch.symm
    apply D.crossHalfEdge_not_mem_walkCycle (D.walkStep b)
    rw [hop]
    have hcycle : D.walkCycle (D.walkStep b) = D.walkCycle h := by
      change periodicOrbit (D.walkStep : D.HalfEdge → D.HalfEdge)
          (D.walkStep
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h)) =
        periodicOrbit (D.walkStep : D.HalfEdge → D.HalfEdge) h
      simpa only [Function.iterate_succ_apply'] using
        periodicOrbit_apply_iterate_eq
          (D.walkStep_mem_periodicPts h) (j + 1)
    rw [hcycle, walkCycle,
      mem_periodicOrbit_iff (D.walkStep_mem_periodicPts h)]
    exact ⟨i, rfl⟩

/-- The two named endpoint values of an arc are exactly the vertex of either
half-edge and the vertex reached by crossing that half-edge. -/
theorem finiteArc_endpointPair_eq_halfEdge_vertices
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    ({D.finiteArcLeftEndpoint h.1.2, D.finiteArcRightEndpoint h.1.2} :
        Set (FrontierSpace O)) =
      {h.1.1.1, (D.crossHalfEdge h).1.1.1} := by
  obtain ⟨⟨e, b⟩, rfl⟩ := D.endpointHalfEdge_surjective h
  cases b with
  | false =>
      rw [D.endpointHalfEdge_arc, D.crossHalfEdge_endpointHalfEdge]
      rfl
  | true =>
      rw [D.endpointHalfEdge_arc, D.crossHalfEdge_endpointHalfEdge]
      exact Set.pair_comm _ _

/-- The endpoints of the compact arc traversed at one walk state are exactly
that state's vertex and the next state's vertex. -/
theorem traversedArc_endpointPair_eq_walkVertices
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) :
    ({D.finiteArcLeftEndpoint (D.switchHalfEdge h).1.2,
        D.finiteArcRightEndpoint (D.switchHalfEdge h).1.2} :
        Set (FrontierSpace O)) =
      {h.1.1.1, (D.walkStep h).1.1.1} := by
  rw [D.finiteArc_endpointPair_eq_halfEdge_vertices (D.switchHalfEdge h)]
  simp only [D.switchHalfEdge_vertex]
  rfl

/-- Arithmetic adjacency on a finite cyclic traversal: ordinary predecessor or
successor, together with the unique wraparound pair. -/
def CyclicallyAdjacent (k i j : ℕ) : Prop :=
  i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j + 1 = k) ∨ (j = 0 ∧ i + 1 = k)

/-- Distinct arcs selected during one minimal traversal period can have a
common point only at cyclically adjacent indices.  This rules out geometric
self-crossings between nonadjacent pieces before any smooth reparameterization
is chosen. -/
theorem traversedArc_cyclicallyAdjacent_of_closure_inter_nonempty
    (D : FiniteChartCutSystem A) (h : D.HalfEdge) {i j : ℕ}
    (hi : i < minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h)
    (hj : j < minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h)
    (hij : i ≠ j)
    (hinter :
      (D.finiteArcClosure
          (D.switchHalfEdge
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)).1.2 ∩
        D.finiteArcClosure
          (D.switchHalfEdge
            (((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h)).1.2).Nonempty) :
    CyclicallyAdjacent
      (minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h) i j := by
  let k := minimalPeriod (D.walkStep : D.HalfEdge → D.HalfEdge) h
  let vi : D.cutPoints :=
    (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h).1.1
  let vj : D.cutPoints :=
    (((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h).1.1
  let vi1 : D.cutPoints :=
    (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i + 1]) h).1.1
  let vj1 : D.cutPoints :=
    (((D.walkStep : D.HalfEdge → D.HalfEdge)^[j + 1]) h).1.1
  have harcNe :
      (D.switchHalfEdge
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)).1.2 ≠
        (D.switchHalfEdge
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h)).1.2 := by
    intro harc
    exact hij (D.traversedArc_injOn h hi hj harc)
  obtain ⟨q, hqi, hqj⟩ := hinter
  have hends := D.finiteArcClosure_inter_subset_endpointPairs harcNe ⟨hqi, hqj⟩
  have hiEndsRaw := hends.1
  rw [D.traversedArc_endpointPair_eq_walkVertices
    (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)] at hiEndsRaw
  have hiEnds : q ∈ ({vi.1, vi1.1} : Set (FrontierSpace O)) := by
    simpa only [vi, vi1, Function.iterate_succ_apply'] using hiEndsRaw
  have hjEndsRaw := hends.2
  rw [D.traversedArc_endpointPair_eq_walkVertices
    (((D.walkStep : D.HalfEdge → D.HalfEdge)^[j]) h)] at hjEndsRaw
  have hjEnds : q ∈ ({vj.1, vj1.1} : Set (FrontierSpace O)) := by
    simpa only [vj, vj1, Function.iterate_succ_apply'] using hjEndsRaw
  have hkpos : 0 < k := minimalPeriod_pos_of_mem_periodicPts
    (D.walkStep_mem_periodicPts h)
  have hreturn :
      ((D.walkStep : D.HalfEdge → D.HalfEdge)^[k]) h = h := by
    exact iterate_minimalPeriod
  have vertexEq_of_valEq {x y : D.cutPoints} (hxy : x.1 = y.1) : x = y :=
    Subtype.ext hxy
  have hinj := D.walkVertex_injOn_minimalPeriod h
  have eq_index_of_vertexEq {m n : ℕ} (hm : m < k) (hn : n < k)
      (hmn :
        (((D.walkStep : D.HalfEdge → D.HalfEdge)^[m]) h).1.1 =
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h).1.1) :
      m = n :=
    hinj hm hn hmn
  have eq_zero_of_vertexEq_return {m : ℕ} (hm : m < k)
      (hmk :
        (((D.walkStep : D.HalfEdge → D.HalfEdge)^[m]) h).1.1 =
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[k]) h).1.1) :
      m = 0 := by
    apply eq_index_of_vertexEq hm hkpos
    simpa only [hreturn, Function.iterate_zero_apply] using hmk
  unfold CyclicallyAdjacent
  rcases hiEnds with hi0 | hi1 <;> rcases hjEnds with hj0 | hj1
  · exfalso
    apply hij
    apply eq_index_of_vertexEq hi hj
    exact vertexEq_of_valEq (hi0.symm.trans hj0)
  · by_cases hjk : j + 1 = k
    · have hviZero : i = 0 := eq_zero_of_vertexEq_return hi <| by
        simpa only [vi, vj1, hjk] using
          vertexEq_of_valEq (hi0.symm.trans hj1)
      exact Or.inr (Or.inr (Or.inl ⟨hviZero, hjk⟩))
    · have hj1lt : j + 1 < k := by omega
      exact Or.inr (Or.inl <| eq_index_of_vertexEq hj1lt hi <|
        (vertexEq_of_valEq (hi0.symm.trans hj1)).symm)
  · by_cases hik : i + 1 = k
    · have hvjZero : j = 0 := eq_zero_of_vertexEq_return hj <| by
        simpa only [vj, vi1, hik] using
          vertexEq_of_valEq (hj0.symm.trans hi1)
      exact Or.inr (Or.inr (Or.inr ⟨hvjZero, hik⟩))
    · have hi1lt : i + 1 < k := by omega
      exact Or.inl <| eq_index_of_vertexEq hi1lt hj <|
        vertexEq_of_valEq (hi1.symm.trans hj0)
  · by_cases hik : i + 1 = k
    · by_cases hjk : j + 1 = k
      · exfalso
        apply hij
        omega
      · have hj1lt : j + 1 < k := by omega
        exfalso
        have hzero : j + 1 = 0 := eq_zero_of_vertexEq_return hj1lt <| by
          simpa only [vj1, vi1, hik] using
            vertexEq_of_valEq (hj1.symm.trans hi1)
        omega
    · have hi1lt : i + 1 < k := by omega
      by_cases hjk : j + 1 = k
      · exfalso
        have hzero : i + 1 = 0 := eq_zero_of_vertexEq_return hi1lt <| by
          simpa only [vi1, vj1, hjk] using
            vertexEq_of_valEq (hi1.symm.trans hj1)
        omega
      · have hj1lt : j + 1 < k := by omega
        have hs := eq_index_of_vertexEq hi1lt hj1lt <|
          vertexEq_of_valEq (hi1.symm.trans hj1)
        exfalso
        exact hij (by omega)

/-- Every selected unoriented boundary loop has a nonrepeating cyclic vertex
sequence and no intersections between nonadjacent compact traversal pieces. -/
theorem boundaryGeometricWalkLoop_embeddedArcCycle
    (D : FiniteChartCutSystem A) (j : D.BoundaryLoopIndex) :
    let h := D.boundaryLoopHalfEdge j
    let k := (D.boundaryGeometricWalkLoop j).period
    (Set.Iio k).InjOn
        (fun n =>
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h).1.1) ∧
      ∀ {i m : ℕ}, i < k → m < k → i ≠ m →
        (D.finiteArcClosure
            (D.switchHalfEdge
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)).1.2 ∩
          D.finiteArcClosure
            (D.switchHalfEdge
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[m]) h)).1.2).Nonempty →
          CyclicallyAdjacent k i m := by
  dsimp only [boundaryGeometricWalkLoop, minimalGeometricWalkLoop,
    GeometricWalkLoop.period]
  exact ⟨D.walkVertex_injOn_minimalPeriod (D.boundaryLoopHalfEdge j),
    fun hi hm him hinter =>
      D.traversedArc_cyclicallyAdjacent_of_closure_inter_nonempty
        (D.boundaryLoopHalfEdge j) hi hm him hinter⟩

/-- Compact arcs whose closures meet belong to the same unoriented selected
loop. Exact degree two prevents two distinct walk orbits from sharing a cut
vertex. -/
theorem arcBoundaryLoopIndex_eq_of_finiteArcClosure_inter_nonempty
    (D : FiniteChartCutSystem A) {e f : D.ArcIndex}
    (hinter : (D.finiteArcClosure e ∩ D.finiteArcClosure f).Nonempty) :
    D.arcBoundaryLoopIndex e = D.arcBoundaryLoopIndex f := by
  by_cases hef : e = f
  · exact congrArg D.arcBoundaryLoopIndex hef
  · obtain ⟨p, hpe, hpf⟩ := hinter
    have hends :=
      D.finiteArcClosure_inter_subset_endpointPairs hef ⟨hpe, hpf⟩
    have hpCut : p ∈ D.cutPoints := by
      simp only [Set.mem_inter_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hends
      rcases hends.1 with hpLeft | hpRight
      · rw [hpLeft]
        exact (D.finiteArc_endpoints_mem_cutPoints e).1
      · rw [hpRight]
        exact (D.finiteArc_endpoints_mem_cutPoints e).2
    let v : D.cutPoints := ⟨p, hpCut⟩
    let he : D.HalfEdge := ⟨(v, e), hpe⟩
    let hf : D.HalfEdge := ⟨(v, f), hpf⟩
    rcases D.eq_or_eq_switchHalfEdge_of_vertex_eq
        (h := he) (g := hf) rfl with heq | hswitch
    · calc
        D.arcBoundaryLoopIndex e =
            D.boundaryLoopIndexOfHalfEdge he := by
          simpa only [he] using D.arcBoundaryLoopIndex_eq_of_halfEdge_arc he
        _ = D.boundaryLoopIndexOfHalfEdge hf :=
          congrArg D.boundaryLoopIndexOfHalfEdge heq
        _ = D.arcBoundaryLoopIndex f := by
          simpa only [hf] using
            (D.arcBoundaryLoopIndex_eq_of_halfEdge_arc hf).symm
    · calc
        D.arcBoundaryLoopIndex e =
            D.boundaryLoopIndexOfHalfEdge he := by
          simpa only [he] using D.arcBoundaryLoopIndex_eq_of_halfEdge_arc he
        _ = D.boundaryLoopIndexOfHalfEdge (D.switchHalfEdge hf) :=
          congrArg D.boundaryLoopIndexOfHalfEdge hswitch
        _ = D.boundaryLoopIndexOfHalfEdge hf :=
          D.boundaryLoopIndexOfHalfEdge_switchHalfEdge hf
        _ = D.arcBoundaryLoopIndex f := by
          simpa only [hf] using
            (D.arcBoundaryLoopIndex_eq_of_halfEdge_arc hf).symm

/-- Different selected unoriented loops have disjoint geometric images, not
merely finite overlap. Any common point would lie in two compact arc closures
and hence identify their unique loop indices. -/
theorem disjoint_range_boundaryGeometricWalkLoop
    (D : FiniteChartCutSystem A) {j k : D.BoundaryLoopIndex}
    (hjk : j ≠ k) :
    Disjoint (Set.range (D.boundaryGeometricWalkLoop j).path)
      (Set.range (D.boundaryGeometricWalkLoop k).path) := by
  apply Set.disjoint_left.2
  intro q hqj hqk
  rw [D.boundaryGeometricWalkLoop_path_range_eq_iUnion_arcs] at hqj hqk
  obtain ⟨e, hqe⟩ := Set.mem_iUnion.mp hqj
  obtain ⟨f, hqf⟩ := Set.mem_iUnion.mp hqk
  rw [D.finiteArcPathLR_range] at hqe hqf
  obtain ⟨pe, hpe, hpeq⟩ := hqe
  obtain ⟨pf, hpf, hpfeq⟩ := hqf
  have hpepf : pe = pf := by
    apply Subtype.ext
    exact hpeq.trans hpfeq.symm
  subst pf
  apply hjk
  calc
    j = D.arcBoundaryLoopIndex e.1 := e.2.symm
    _ = D.arcBoundaryLoopIndex f.1 :=
      D.arcBoundaryLoopIndex_eq_of_finiteArcClosure_inter_nonempty
        ⟨pe, hpe, hpf⟩
    _ = k := f.2

/-- Global selected-loop contract for embedded compact-arc cycles.  Vertices
do not repeat before closure, and a common point of two distinct traversal
pieces forces the two indices to be adjacent in the finite cyclic order. -/
def HasEmbeddedBoundaryArcCycles (D : FiniteChartCutSystem A) : Prop :=
  ∀ j : D.BoundaryLoopIndex,
    let h := D.boundaryLoopHalfEdge j
    let k := (D.boundaryGeometricWalkLoop j).period
    (Set.Iio k).InjOn
        (fun n =>
          (((D.walkStep : D.HalfEdge → D.HalfEdge)^[n]) h).1.1) ∧
      ∀ {i m : ℕ}, i < k → m < k → i ≠ m →
        (D.finiteArcClosure
            (D.switchHalfEdge
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[i]) h)).1.2 ∩
          D.finiteArcClosure
            (D.switchHalfEdge
              (((D.walkStep : D.HalfEdge → D.HalfEdge)^[m]) h)).1.2).Nonempty →
          CyclicallyAdjacent k i m

/-- Every selected boundary-loop family satisfies the embedded arc-cycle
contract. -/
theorem hasEmbeddedBoundaryArcCycles
    (D : FiniteChartCutSystem A) :
    D.HasEmbeddedBoundaryArcCycles := by
  intro j
  exact D.boundaryGeometricWalkLoop_embeddedArcCycle j

end FiniteChartCutSystem
end BoundaryHalfSpaceAtlas
end CMVBoundaryLocalAtlas
