import CMVPolygonalModTwo
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory symmDiff BigOperators

noncomputable section

namespace CMVPolygonalModTwo

private lemma coeff_eq_one_of_ne_zero (c : Coeff) (hc : c ≠ 0) : c = 1 := by
  have hv : c.val < 2 := ZMod.val_lt c
  rcases (show c.val = 0 ∨ c.val = 1 by omega) with h | h
  · exact (hc ((ZMod.val_eq_zero c).mp h)).elim
  · exact (ZMod.val_eq_one (by norm_num) c).mp h

private lemma boundaryOne_eq_support_sum (C : OneChain) :
    boundaryOne C = ∑ e ∈ C.support, edgeBoundary e := by
  rw [show boundaryOne C = C.sum (fun e c => c • edgeBoundary e) by rfl]
  apply Finset.sum_congr rfl
  intro e he
  rw [coeff_eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp he)]
  simp

private lemma edge_eq_edge_endpoints (e : Edge) :
    ∃ (a b : PlanePoint) (hab : a ≠ b), e = edge a b hab := by
  rcases e with ⟨pair, hpair⟩
  induction pair using Sym2.ind with
  | _ a b =>
      have hab : a ≠ b := by simpa using hpair
      exact ⟨a, b, hab, by rfl⟩

private def chainVertices (C : OneChain) : Finset PlanePoint :=
  C.support.biUnion fun e => e.pair.toFinset

private def chainPairs (C : OneChain) : Finset (Sym2 PlanePoint) :=
  C.support.image Edge.pair

private def chainGraph (C : OneChain) : SimpleGraph PlanePoint :=
  SimpleGraph.fromEdgeSet (chainPairs C : Set (Sym2 PlanePoint))

private lemma edge_endpoints_mem_vertices (C : OneChain) {e : Edge}
    (he : e ∈ C.support) {x : PlanePoint} (hx : x ∈ e.pair) :
    x ∈ chainVertices C := by
  simp only [chainVertices, Finset.mem_biUnion]
  exact ⟨e, he, Sym2.mem_toFinset.mpr hx⟩

private def reachableVertices (C : OneChain) (a : PlanePoint) : Finset PlanePoint :=
  @Finset.filter PlanePoint ((chainGraph C).Reachable a) (Classical.decPred _) (chainVertices C)
private lemma finset_sum_finsupp_apply {ι : Type*} (s : Finset ι)
    (f : ι → ZeroChain) (x : PlanePoint) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi]

private lemma sum_vertexChain_apply (s : Finset PlanePoint) (u : PlanePoint) :
    ∑ x ∈ s, (vertexChain u) x = if u ∈ s then 1 else 0 := by
  classical
  simpa only [vertexChain, Finsupp.single_apply] using
    (Finset.sum_ite_eq s u (fun _ : PlanePoint => (1 : Coeff)))


private lemma boundary_support_subset_vertices (C : OneChain) :
    (boundaryOne C).support ⊆ chainVertices C := by
  classical
  intro x hx
  contrapose! hx
  have hzero : (boundaryOne C) x = 0 := by
    rw [boundaryOne_eq_support_sum]
    rw [finset_sum_finsupp_apply]
    apply Finset.sum_eq_zero
    intro e he
    rcases edge_eq_edge_endpoints e with ⟨u, v, huv, rfl⟩
    have hxu : x ≠ u := by
      intro h
      subst x
      exact hx (edge_endpoints_mem_vertices C he (by simp))
    have hxv : x ≠ v := by
      intro h
      subst x
      exact hx (edge_endpoints_mem_vertices C he (by simp))
    simp [edgeBoundary_edge, vertexChain, hxu, hxv]
  exact Finsupp.notMem_support_iff.mpr hzero

private lemma supported_edge_adj (C : OneChain) {e : Edge} (he : e ∈ C.support)
    {u v : PlanePoint} (hp : e.pair = s(u, v)) : (chainGraph C).Adj u v := by
  rw [chainGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · simp only [chainPairs, Finset.coe_image, Set.mem_image]
    exact ⟨e, he, hp⟩
  · intro huv
    subst v
    apply e.nondegenerate
    rw [hp]
    exact Sym2.mk_isDiag_iff.mpr rfl

private lemma reachable_endpoints_iff (C : OneChain) (a : PlanePoint)
    {e : Edge} (he : e ∈ C.support) {u v : PlanePoint} (hp : e.pair = s(u, v)) :
    (chainGraph C).Reachable a u ↔ (chainGraph C).Reachable a v := by
  have hadj := supported_edge_adj C he hp
  exact ⟨fun h => h.trans hadj.reachable,
    fun h => h.trans hadj.symm.reachable⟩

private lemma sum_boundary_reachable_eq_zero (C : OneChain) (a : PlanePoint) :
    ∑ x ∈ reachableVertices C a, (boundaryOne C) x = 0 := by
  classical
  rw [boundaryOne_eq_support_sum]
  simp_rw [finset_sum_finsupp_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e he
  rcases edge_eq_edge_endpoints e with ⟨u, v, huv, rfl⟩
  have hre := reachable_endpoints_iff C a he rfl
  have huV : u ∈ chainVertices C := edge_endpoints_mem_vertices C he (by simp)
  have hvV : v ∈ chainVertices C := edge_endpoints_mem_vertices C he (by simp)
  by_cases hu : (chainGraph C).Reachable a u
  · have hv := hre.mp hu
    have huR : u ∈ reachableVertices C a := by
      simp [reachableVertices, huV, hu]
    have hvR : v ∈ reachableVertices C a := by
      simp [reachableVertices, hvV, hv]
    change (∑ x ∈ reachableVertices C a, ((vertexChain u) x + (vertexChain v) x)) = 0
    rw [Finset.sum_add_distrib]
    rw [sum_vertexChain_apply, sum_vertexChain_apply]
    simp [huR, hvR]
  · have hv : ¬(chainGraph C).Reachable a v := fun h => hu (hre.mpr h)
    have huR : u ∉ reachableVertices C a := by
      simp [reachableVertices, hu]
    have hvR : v ∉ reachableVertices C a := by
      simp [reachableVertices, hv]
    change (∑ x ∈ reachableVertices C a, ((vertexChain u) x + (vertexChain v) x)) = 0
    rw [Finset.sum_add_distrib]
    rw [sum_vertexChain_apply, sum_vertexChain_apply]
    simp [huR, hvR]

private lemma reachable_of_boundary_support_pair (C : OneChain) (a b : PlanePoint)
    (hboundary : (boundaryOne C).support = {a, b}) :
    (chainGraph C).Reachable a b := by
  classical
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  by_contra hreach
  let R := reachableVertices C a
  have haSupp : a ∈ (boundaryOne C).support := by simp [hboundary]
  have hbSupp : b ∈ (boundaryOne C).support := by simp [hboundary]
  have haV : a ∈ chainVertices C := boundary_support_subset_vertices C haSupp
  have hbV : b ∈ chainVertices C := boundary_support_subset_vertices C hbSupp
  have haR : a ∈ R := by simp [R, reachableVertices, haV]
  have hbR : b ∉ R := by simp [R, reachableVertices, hbV, hreach]
  have hcoeff (x : PlanePoint) :
      (boundaryOne C) x = if x = a ∨ x = b then 1 else 0 := by
    by_cases hx : x = a ∨ x = b
    · have hxs : x ∈ (boundaryOne C).support := by simpa [hboundary]
      exact coeff_eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp hxs) |>.trans (if_pos hx).symm
    · have hxs : x ∉ (boundaryOne C).support := by
        rw [hboundary]
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hx
      rw [if_neg hx]
      exact Finsupp.notMem_support_iff.mp hxs
  have hfilter : R.filter (fun x => x = a ∨ x = b) = {a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxR, rfl | rfl⟩
      · rfl
      · exact (hbR hxR).elim
    · rintro rfl
      exact ⟨haR, Or.inl rfl⟩
  have hsum : ∑ x ∈ R, (boundaryOne C) x = 1 := by
    simp_rw [hcoeff]
    rw [← Finset.sum_filter, hfilter]
    simp
  have hzero : ∑ x ∈ R, (boundaryOne C) x = 0 := sum_boundary_reachable_eq_zero C a
  rw [hsum] at hzero
  exact one_ne_zero hzero

private def pairLength (q : Sym2 PlanePoint) : ENNReal :=
  Sym2.lift
    ⟨fun x y => euclideanEdist x y,
      fun x y => edist_comm
        (planeEuclideanHomeomorph x) (planeEuclideanHomeomorph y)⟩ q

private lemma edist_le_euclideanEdist (a b : PlanePoint) :
    edist a b ≤ euclideanEdist a b := by
  rw [edist_dist, euclideanEdist, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [Prod.dist_eq, planeEuclideanHomeomorph_apply,
    planeEuclideanHomeomorph_apply, WithLp.prod_dist_eq_of_L2]
  change max (dist a.1 b.1) (dist a.2 b.2) ≤
    Real.sqrt (dist a.1 b.1 ^ 2 + dist a.2 b.2 ^ 2)
  apply max_le
  · exact Real.le_sqrt_of_sq_le (by
      nlinarith [sq_nonneg (dist a.2 b.2)])
  · exact Real.le_sqrt_of_sq_le (by
      nlinarith [sq_nonneg (dist a.1 b.1)])

@[simp] private lemma pairLength_mk (x y : PlanePoint) :
    pairLength s(x, y) = euclideanEdist x y := by simp [pairLength]
private lemma euclideanEdist_le_walk_edge_sum (C : OneChain) {a b : PlanePoint}
    (p : (chainGraph C).Walk a b) :
    euclideanEdist a b ≤ (p.edges.map pairLength).sum := by
  induction p with
  | nil => simp [euclideanEdist]
  | @cons u v w huv p ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, pairLength_mk]
      exact (edist_triangle (planeEuclideanHomeomorph u)
          (planeEuclideanHomeomorph v) (planeEuclideanHomeomorph w)).trans
        (add_le_add_right ih _)

private lemma path_edge_sum_le_formalMass (C : OneChain) {a b : PlanePoint}
    (p : (chainGraph C).Path a b) :
    (((p : (chainGraph C).Walk a b).edges.map pairLength).sum) ≤ formalMass C := by
  let w : (chainGraph C).Walk a b := p
  have hnodup : w.edges.Nodup := p.2.isTrail.edges_nodup
  rw [← List.sum_toFinset pairLength hnodup]
  rw [formalMass]
  let P := chainPairs C
  have hsub : w.edges.toFinset ⊆ P := by
    intro q hq
    have hqe : q ∈ (chainGraph C).edgeSet := w.edges_subset_edgeSet (by simpa using hq)
    rw [chainGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff] at hqe
    simpa [P] using hqe.1
  calc
    ∑ q ∈ w.edges.toFinset, pairLength q ≤ ∑ q ∈ P, pairLength q :=
      Finset.sum_le_sum_of_subset hsub
    _ = ∑ e ∈ C.support, edgeLength e := by
      change ∑ q ∈ chainPairs C, pairLength q = _
      rw [chainPairs, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro e he
        rcases edge_eq_edge_endpoints e with ⟨u, v, huv, rfl⟩
        simp [pairLength]
      · intro e he f hf hef
        cases e
        cases f
        congr
/-- A finite mod-two edge chain whose endpoint boundary is exactly `a+b`
contains an `a`-to-`b` path, so its total Euclidean edge mass dominates
their Euclidean distance. -/
theorem euclideanEdist_le_formalMass_of_boundary_support
    (C : OneChain) (a b : PlanePoint)
    (hboundary : (boundaryOne C).support = {a, b}) :
    euclideanEdist a b ≤ formalMass C := by
  have hreach := reachable_of_boundary_support_pair C a b hboundary
  exact hreach.elim_path fun p =>
    (euclideanEdist_le_walk_edge_sum C (p : (chainGraph C).Walk a b)).trans
      (path_edge_sum_le_formalMass C p)

/-- The same estimate for the ambient product `edist`; the product `L∞`
distance is bounded by the Euclidean `L²` distance used by `formalMass`. -/
theorem edist_le_formalMass_of_boundary_support
    (C : OneChain) (a b : PlanePoint)
    (hboundary : (boundaryOne C).support = {a, b}) :
    edist a b ≤ formalMass C :=
  (edist_le_euclideanEdist a b).trans
    (euclideanEdist_le_formalMass_of_boundary_support C a b hboundary)


/-- The two-endpoint calibration is a theorem about every formal
representative, not an extra mass term. -/
theorem endpointCalibration_le_representativeMassInf
    (C : GeometricOneChain) :
    endpointCalibration (geometricBoundary C) ≤ representativeMassInf C := by
  unfold endpointCalibration
  split_ifs with hcard
  · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcard
    rw [hs]
    have himage :
        planeEuclideanHomeomorph ''
            (↑({a, b} : Finset PlanePoint) : Set PlanePoint) =
          {planeEuclideanHomeomorph a, planeEuclideanHomeomorph b} := by
      ext p
      simp [eq_comm]
    rw [himage, Metric.ediam_pair]
    apply le_iInf
    intro D
    apply le_iInf
    intro hD
    apply euclideanEdist_le_formalMass_of_boundary_support D a b
    have hboundary : boundaryOne D = geometricBoundary C := by
      calc
        boundaryOne D = geometricBoundary (toGeometric D) := by simp
        _ = geometricBoundary C := congrArg geometricBoundary hD
    rw [hboundary, hs]
  · exact bot_le

/-- Therefore the calibrated definition agrees exactly with the infimum of
literal formal representative masses. -/
theorem geometricMass_eq_representativeMassInf (C : GeometricOneChain) :
    geometricMass C = representativeMassInf C := by
  rw [geometricMass, max_eq_left
    (endpointCalibration_le_representativeMassInf C)]
end CMVPolygonalModTwo
