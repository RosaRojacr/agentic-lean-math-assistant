import CMVPolygonalReducedMass

/-!
# Finite common-refinement reduction

This file proves the finite common-refinement step for mod-two polygonal
chains.  Every original endpoint is used as a cut point.  The surviving
endpoint-atomic edges cannot have a positive-length overlap unless they are the
same unordered edge, so the resulting formal chain is cancellation-reduced.
Cancellations are handled directly by finite-support addition.
-/

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory BigOperators

noncomputable section

namespace CMVPolygonalModTwo

/-- The two endpoints of an unordered nondegenerate edge. -/
def edgeVertices (e : Edge) : Finset PlanePoint := e.pair.toFinset

/-- All endpoints occurring in the surviving support of a finite chain. -/
def oneChainVertices (C : OneChain) : Finset PlanePoint :=
  C.support.biUnion edgeVertices

private theorem Edge.eq_of_pair_eq {e f : Edge} (h : e.pair = f.pair) : e = f := by
  cases e with
  | mk ep he =>
      cases f with
      | mk fp hf =>
          dsimp only at h
          subst fp
          rfl

lemma edgeVertices_subset_oneChainVertices {C : OneChain} {e : Edge}
    (he : e ∈ C.support) : edgeVertices e ⊆ oneChainVertices C := by
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨e, he, hp⟩

private lemma coeff_eq_one_of_mem_support {C : OneChain} {e : Edge}
    (he : e ∈ C.support) : C e = 1 := by
  exact Fin.eq_one_of_ne_zero _ (Finsupp.mem_support_iff.mp he)


/-- The open Euclidean segment carried by an edge. -/
def edgeInteriorCarrier (e : Edge) : Set EuclideanPlane :=
  Sym2.lift
    ⟨fun a b => openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b),
      fun _ _ => openSegment_symm ℝ _ _⟩ e.pair

@[simp] theorem edgeInteriorCarrier_edge (a b : PlanePoint) (hab : a ≠ b) :
    edgeInteriorCarrier (edge a b hab) =
      openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b) := by
  simp [edgeInteriorCarrier, edge]

/-- An edge is atomic for `V` when no vertex in `V` lies in its open segment. -/
def IsVertexAtomic (V : Finset PlanePoint) (e : Edge) : Prop :=
  ∀ p ∈ V, planeEuclideanHomeomorph p ∉ edgeInteriorCarrier e

private structure EdgePresentation (e : Edge) where
  left : PlanePoint
  right : PlanePoint
  ne : left ≠ right
  edge_eq : e = edge left right ne

private theorem nonempty_edgePresentation (e : Edge) :
    Nonempty (EdgePresentation e) := by
  rcases e with ⟨pair, hpair⟩
  induction pair using Sym2.ind with
  | _ a b =>
      have hab : a ≠ b := by simpa using hpair
      exact ⟨⟨a, b, hab, rfl⟩⟩

private noncomputable def edgePresentation (e : Edge) : EdgePresentation e :=
  Classical.choice (nonempty_edgePresentation e)

private theorem planeEuclidean_mem_openSegment_iff
    {a b p : PlanePoint} :
    planeEuclideanHomeomorph p ∈
        openSegment ℝ (planeEuclideanHomeomorph a)
          (planeEuclideanHomeomorph b) ↔
      p ∈ openSegment ℝ a b := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy, hp⟩
    refine ⟨x, y, hx, hy, hxy, ?_⟩
    apply planeEuclideanHomeomorph.injective
    change x • planeEuclideanHomeomorph a +
        y • planeEuclideanHomeomorph b = planeEuclideanHomeomorph p
    exact hp
  · rintro ⟨x, y, hx, hy, hxy, hp⟩
    refine ⟨x, y, hx, hy, hxy, ?_⟩
    rw [← hp]
    rfl

private theorem mem_openSegment_iff_sbtw_of_ne
    {a b p : EuclideanPlane} (hab : a ≠ b) :
    p ∈ openSegment ℝ a b ↔ Sbtw ℝ a p b := by
  constructor
  · intro hp
    rw [sbtw_iff_mem_image_Ioo_and_ne]
    exact ⟨by rwa [← openSegment_eq_image_lineMap], hab⟩
  · intro hp
    rw [sbtw_iff_mem_image_Ioo_and_ne] at hp
    rw [openSegment_eq_image_lineMap]
    exact hp.1

private theorem openSegment_left_subset
    {a b p : EuclideanPlane} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ a p ⊆ openSegment ℝ a b := by
  have hap : a ≠ p := by
    intro h
    subst p
    exact hab (left_mem_openSegment_iff.mp hp)
  have hs := (mem_openSegment_iff_sbtw_of_ne hab).mp hp
  intro q hq
  exact (mem_openSegment_iff_sbtw_of_ne hab).mpr
    (hs.trans_left ((mem_openSegment_iff_sbtw_of_ne hap).mp hq))

private theorem openSegment_right_subset
    {a b p : EuclideanPlane} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) :
    openSegment ℝ p b ⊆ openSegment ℝ a b := by
  have hpb : p ≠ b := by
    intro h
    subst p
    exact hab (right_mem_openSegment_iff.mp hp)
  have hs := (mem_openSegment_iff_sbtw_of_ne hab).mp hp
  intro q hq
  exact (mem_openSegment_iff_sbtw_of_ne hab).mpr
    (hs.trans_right ((mem_openSegment_iff_sbtw_of_ne hpb).mp hq))

private theorem isVertexAtomic_left_of_cut
    {V : Finset PlanePoint} {a b p : PlanePoint}
    (hab : a ≠ b) (hp : p ∈ openSegment ℝ a b) (hap : a ≠ p)
    (hatom : ∀ q ∈ V, planeEuclideanHomeomorph q ∉
      openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b)) :
    IsVertexAtomic (insert p V) (edge a p hap) := by
  have habE := planeEuclideanHomeomorph.injective.ne hab
  have hpE := planeEuclidean_mem_openSegment_iff.mpr hp
  intro q hq
  rw [edgeInteriorCarrier_edge]
  rcases Finset.mem_insert.mp hq with hqp | hqV
  · subst q
    intro hinner
    exact hap (planeEuclideanHomeomorph.injective
      (right_mem_openSegment_iff.mp hinner))
  · intro hinner
    exact hatom q hqV (openSegment_left_subset habE hpE hinner)

private theorem isVertexAtomic_right_of_cut
    {V : Finset PlanePoint} {a b p : PlanePoint}
    (hab : a ≠ b) (hp : p ∈ openSegment ℝ a b) (hpb : p ≠ b)
    (hatom : ∀ q ∈ V, planeEuclideanHomeomorph q ∉
      openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b)) :
    IsVertexAtomic (insert p V) (edge p b hpb) := by
  have habE := planeEuclideanHomeomorph.injective.ne hab
  have hpE := planeEuclidean_mem_openSegment_iff.mpr hp
  intro q hq
  rw [edgeInteriorCarrier_edge]
  rcases Finset.mem_insert.mp hq with hqp | hqV
  · subst q
    intro hinner
    exact hpb (planeEuclideanHomeomorph.injective
      (left_mem_openSegment_iff.mp hinner))
  · intro hinner
    exact hatom q hqV (openSegment_right_subset habE hpE hinner)

private noncomputable def refineEdgeAtVertex
    (p : PlanePoint) (e : Edge) : OneChain := by
  classical
  let r := edgePresentation e
  exact if hp : p ∈ openSegment ℝ r.left r.right then
    splitSegmentChain r.left r.right p r.ne hp
  else
    Finsupp.single e 1

private theorem refines_refineEdgeAtVertex (p : PlanePoint) (e : Edge) :
    RefinesBySubdivision (Finsupp.single e 1) (refineEdgeAtVertex p e) := by
  classical
  let r := edgePresentation e
  change RefinesBySubdivision (Finsupp.single e 1)
    (if hp : p ∈ openSegment ℝ r.left r.right then
      splitSegmentChain r.left r.right p r.ne hp
    else Finsupp.single e 1)
  by_cases hp : p ∈ openSegment ℝ r.left r.right
  · rw [dif_pos hp]
    have hsource :
        Finsupp.single e (1 : Coeff) =
          segmentChain r.left r.right r.ne := by
      simpa only [segmentChain] using congrArg
        (fun g : Edge => Finsupp.single g (1 : Coeff)) r.edge_eq
    exact (RefinesBySubdivision.ofEq hsource).trans
      (RefinesBySubdivision.split r.left r.right p r.ne hp)
  · rw [dif_neg hp]
    exact RefinesBySubdivision.refl _

private theorem refineEdgeAtVertex_output_properties
    {V U : Finset PlanePoint} {p : PlanePoint} (hpV : p ∈ V)
    {e g : Edge} (heV : edgeVertices e ⊆ V)
    (heU : IsVertexAtomic U e)
    (hg : g ∈ (refineEdgeAtVertex p e).support) :
    edgeVertices g ⊆ V ∧ IsVertexAtomic (insert p U) g := by
  classical
  let r := edgePresentation e
  have hvertices : edgeVertices e = {r.left, r.right} := by
    calc
      edgeVertices e =
          edgeVertices (edge r.left r.right r.ne) :=
        congrArg edgeVertices r.edge_eq
      _ = {r.left, r.right} := by
        exact Sym2.toFinset_mk_eq
  have hcarrier :
      edgeInteriorCarrier e =
        openSegment ℝ (planeEuclideanHomeomorph r.left)
          (planeEuclideanHomeomorph r.right) := by
    calc
      edgeInteriorCarrier e =
          edgeInteriorCarrier (edge r.left r.right r.ne) :=
        congrArg edgeInteriorCarrier r.edge_eq
      _ = _ := edgeInteriorCarrier_edge _ _ _
  have hleftV : r.left ∈ V := heV (by rw [hvertices]; simp)
  have hrightV : r.right ∈ V := heV (by rw [hvertices]; simp)
  have hparent :
      ∀ q ∈ U, planeEuclideanHomeomorph q ∉
        openSegment ℝ (planeEuclideanHomeomorph r.left)
          (planeEuclideanHomeomorph r.right) := by
    intro q hq hinner
    exact heU q hq (hcarrier.symm ▸ hinner)
  change g ∈
    (if hp : p ∈ openSegment ℝ r.left r.right then
      splitSegmentChain r.left r.right p r.ne hp
    else Finsupp.single e 1).support at hg
  by_cases hp : p ∈ openSegment ℝ r.left r.right
  · rw [dif_pos hp] at hg
    have hap : r.left ≠ p := by
      intro h
      subst p
      exact r.ne (left_mem_openSegment_iff.mp hp)
    have hpb : p ≠ r.right := by
      intro h
      subst p
      exact r.ne (right_mem_openSegment_iff.mp hp)
    change g ∈
      (segmentChain r.left p hap +
        segmentChain p r.right hpb).support at hg
    have hg' := Finsupp.support_add hg
    simp only [Finset.mem_union] at hg'
    rcases hg' with hgl | hgr
    · have hge : g = edge r.left p hap := by
        simpa [segmentChain] using hgl
      subst g
      refine ⟨?_, isVertexAtomic_left_of_cut r.ne hp hap hparent⟩
      intro q hq
      simp [edgeVertices] at hq
      rcases hq with h | h
      · simpa [h] using hleftV
      · simpa [h] using hpV
    · have hge : g = edge p r.right hpb := by
        simpa [segmentChain] using hgr
      subst g
      refine ⟨?_, isVertexAtomic_right_of_cut r.ne hp hpb hparent⟩
      intro q hq
      simp [edgeVertices] at hq
      rcases hq with h | h
      · simpa [h] using hpV
      · simpa [h] using hrightV
  · rw [dif_neg hp] at hg
    have hge : g = e := by simpa using hg
    subst g
    refine ⟨heV, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp | hqU
    · subst q
      intro hinner
      exact hp (planeEuclidean_mem_openSegment_iff.mp
        (hcarrier ▸ hinner))
    · exact heU q hqU

private theorem chain_eq_support_sum (C : OneChain) :
    C = ∑ e ∈ C.support, Finsupp.single e (1 : Coeff) := by
  calc
    C = C.sum Finsupp.single := (Finsupp.sum_single C).symm
    _ = ∑ e ∈ C.support, Finsupp.single e (1 : Coeff) := by
      rw [Finsupp.sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [coeff_eq_one_of_mem_support he]

private theorem RefinesBySubdivision.finsetSum
    {ι : Type*} (s : Finset ι) {C D : ι → OneChain}
    (h : ∀ i ∈ s, RefinesBySubdivision (C i) (D i)) :
    RefinesBySubdivision (∑ i ∈ s, C i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact RefinesBySubdivision.refl 0
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact RefinesBySubdivision.add
        (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private noncomputable def refineChainAtVertex
    (p : PlanePoint) (C : OneChain) : OneChain :=
  ∑ e ∈ C.support, refineEdgeAtVertex p e

private theorem refines_refineChainAtVertex (p : PlanePoint) (C : OneChain) :
    RefinesBySubdivision C (refineChainAtVertex p C) := by
  exact (RefinesBySubdivision.ofEq (chain_eq_support_sum C)).trans
    (RefinesBySubdivision.finsetSum C.support fun e _ =>
      refines_refineEdgeAtVertex p e)

private theorem refineChainAtVertex_properties
    {V U : Finset PlanePoint} {p : PlanePoint} (hpV : p ∈ V)
    {C : OneChain}
    (hends : ∀ ⦃e⦄, e ∈ C.support → edgeVertices e ⊆ V)
    (hatom : ∀ ⦃e⦄, e ∈ C.support → IsVertexAtomic U e) :
    (∀ ⦃g⦄, g ∈ (refineChainAtVertex p C).support →
      edgeVertices g ⊆ V) ∧
    (∀ ⦃g⦄, g ∈ (refineChainAtVertex p C).support →
      IsVertexAtomic (insert p U) g) := by
  constructor <;> intro g hg
  · obtain ⟨e, he, hge⟩ := Finsupp.mem_support_finsetSum g hg
    exact (refineEdgeAtVertex_output_properties hpV
      (hends he) (hatom he) hge).1
  · obtain ⟨e, he, hge⟩ := Finsupp.mem_support_finsetSum g hg
    exact (refineEdgeAtVertex_output_properties hpV
      (hends he) (hatom he) hge).2

private theorem unordered_endpoints_eq_of_atomic_inter_infinite
    (a b c d : PlanePoint) (hab : a ≠ b) (hcd : c ≠ d)
    (hc : planeEuclideanHomeomorph c ∉
      openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b))
    (hd : planeEuclideanHomeomorph d ∉
      openSegment ℝ (planeEuclideanHomeomorph a)
        (planeEuclideanHomeomorph b))
    (ha : planeEuclideanHomeomorph a ∉
      openSegment ℝ (planeEuclideanHomeomorph c)
        (planeEuclideanHomeomorph d))
    (hb : planeEuclideanHomeomorph b ∉
      openSegment ℝ (planeEuclideanHomeomorph c)
        (planeEuclideanHomeomorph d))
    (hinter :
      (segment ℝ (planeEuclideanHomeomorph a)
          (planeEuclideanHomeomorph b) ∩
        segment ℝ (planeEuclideanHomeomorph c)
          (planeEuclideanHomeomorph d)).Infinite) :
    s(a, b) = s(c, d) := by
  let A := planeEuclideanHomeomorph a
  let B := planeEuclideanHomeomorph b
  let C := planeEuclideanHomeomorph c
  let D := planeEuclideanHomeomorph d
  have hAB : A ≠ B := planeEuclideanHomeomorph.injective.ne hab
  have hCD : C ≠ D := planeEuclideanHomeomorph.injective.ne hcd
  obtain ⟨x, hx, y, hy, hxy⟩ := hinter.nontrivial
  have hxAB : x ∈ line[ℝ, A, B] :=
    (affineSegment_subset_affineSpan ℝ A B)
      (by simpa only [affineSegment_eq_segment] using hx.1)
  have hyAB : y ∈ line[ℝ, A, B] :=
    (affineSegment_subset_affineSpan ℝ A B)
      (by simpa only [affineSegment_eq_segment] using hy.1)
  have hxCD : x ∈ line[ℝ, C, D] :=
    (affineSegment_subset_affineSpan ℝ C D)
      (by simpa only [affineSegment_eq_segment] using hx.2)
  have hyCD : y ∈ line[ℝ, C, D] :=
    (affineSegment_subset_affineSpan ℝ C D)
      (by simpa only [affineSegment_eq_segment] using hy.2)
  have hlines : line[ℝ, A, B] = line[ℝ, C, D] := by
    rw [← affineSpan_pair_eq_of_mem_of_mem_of_ne hxAB hyAB hxy,
      ← affineSpan_pair_eq_of_mem_of_mem_of_ne hxCD hyCD hxy]
  have hCline : C ∈ line[ℝ, A, B] := by
    rw [hlines]
    exact left_mem_affineSpan_pair ℝ C D
  have hDline : D ∈ line[ℝ, A, B] := by
    rw [hlines]
    exact right_mem_affineSpan_pair ℝ C D
  obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hCline
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hDline
  have hst : s ≠ t := by
    intro h
    apply hCD
    rw [← hs, ← ht, h]
  obtain ⟨z, hz, hzfinite⟩ :=
    hinter.exists_notMem_finset ({A, B, C, D} : Finset EuclideanPlane)
  have hzA : z ≠ A := fun h => hzfinite (by simp [h])
  have hzB : z ≠ B := fun h => hzfinite (by simp [h])
  have hzC : z ≠ C := fun h => hzfinite (by simp [h])
  have hzD : z ≠ D := fun h => hzfinite (by simp [h])
  have hzOpenAB : z ∈ openSegment ℝ A B := by
    rw [← insert_endpoints_openSegment ℝ A B] at hz
    rcases hz.1 with h | h | h
    · exact (hzA h).elim
    · exact (hzB h).elim
    · exact h
  have hzOpenCD : z ∈ openSegment ℝ C D := by
    rw [← insert_endpoints_openSegment ℝ C D] at hz
    rcases hz.2 with h | h | h
    · exact (hzC h).elim
    · exact (hzD h).elim
    · exact h
  rw [openSegment_eq_image_lineMap] at hzOpenAB
  obtain ⟨u, hu, huz⟩ := hzOpenAB
  have huCD : u ∈ openSegment ℝ s t := by
    have hzImage :
        z ∈ (AffineMap.lineMap A B : ℝ →ᵃ[ℝ] EuclideanPlane) ''
          openSegment ℝ s t := by
      rw [image_openSegment, hs, ht]
      exact hzOpenCD
    rcases hzImage with ⟨v, hv, hvz⟩
    have huv : u = v := (AffineMap.lineMap_injective ℝ hAB)
      (huz.trans hvz.symm)
    rwa [huv]
  have hcu : s ∉ Ioo (0 : ℝ) 1 := by
    intro hsI
    apply hc
    change C ∈ openSegment ℝ A B
    rw [← hs, openSegment_eq_image_lineMap]
    exact ⟨s, hsI, rfl⟩
  have hdu : t ∉ Ioo (0 : ℝ) 1 := by
    intro htI
    apply hd
    change D ∈ openSegment ℝ A B
    rw [← ht, openSegment_eq_image_lineMap]
    exact ⟨t, htI, rfl⟩
  have hzero : (0 : ℝ) ∉ openSegment ℝ s t := by
    intro h0
    apply ha
    change A ∈ openSegment ℝ C D
    rw [← hs, ← ht, ← image_openSegment]
    exact ⟨0, h0, by simp⟩
  have hone : (1 : ℝ) ∉ openSegment ℝ s t := by
    intro h1
    apply hb
    change B ∈ openSegment ℝ C D
    rw [← hs, ← ht, ← image_openSegment]
    exact ⟨1, h1, by simp⟩
  have huI : u ∈ Ioo (0 : ℝ) 1 := hu
  rcases hst.lt_or_gt with hst | hts
  · rw [openSegment_eq_Ioo hst] at huCD hzero hone
    have hs0 : s = 0 := by
      have hs_nonpos : s ≤ 0 := by
        by_contra hspos
        exact hcu ⟨lt_of_not_ge hspos, huCD.1.trans huI.2⟩
      have hs_nonneg : 0 ≤ s := by
        by_contra hsneg
        exact hzero ⟨lt_of_not_ge hsneg, huCD.2.trans' huI.1⟩
      exact le_antisymm hs_nonpos hs_nonneg
    have ht1 : t = 1 := by
      have ht_ge : 1 ≤ t := by
        by_contra htlt
        exact hdu ⟨huI.1.trans huCD.2, lt_of_not_ge htlt⟩
      have ht_le : t ≤ 1 := by
        by_contra honeLt
        exact hone ⟨by simpa [hs0] using huI.1, lt_of_not_ge honeLt⟩
      exact le_antisymm ht_le ht_ge
    have hca : c = a := planeEuclideanHomeomorph.injective (by
      change C = A
      rw [← hs, hs0]
      simp)
    have hdb : d = b := planeEuclideanHomeomorph.injective (by
      change D = B
      rw [← ht, ht1]
      simp)
    simp [hca, hdb]
  · rw [openSegment_symm ℝ s t, openSegment_eq_Ioo hts] at huCD hzero hone
    have ht0 : t = 0 := by
      have ht_nonpos : t ≤ 0 := by
        by_contra htpos
        exact hdu ⟨lt_of_not_ge htpos, huCD.1.trans huI.2⟩
      have ht_nonneg : 0 ≤ t := by
        by_contra htneg
        exact hzero ⟨lt_of_not_ge htneg, huCD.2.trans' huI.1⟩
      exact le_antisymm ht_nonpos ht_nonneg
    have hs1 : s = 1 := by
      have hs_ge : 1 ≤ s := by
        by_contra hslt
        exact hcu ⟨huI.1.trans huCD.2, lt_of_not_ge hslt⟩
      have hs_le : s ≤ 1 := by
        by_contra honeLt
        exact hone ⟨by simpa [ht0] using huI.1, lt_of_not_ge honeLt⟩
      exact le_antisymm hs_le hs_ge
    have hcb : c = b := planeEuclideanHomeomorph.injective (by
      change C = B
      rw [← hs, hs1]
      simp)
    have hda : d = a := planeEuclideanHomeomorph.injective (by
      change D = A
      rw [← ht, ht0]
      simp)
    simp [hcb, hda, Sym2.eq_swap]

/-- Two vertex-atomic edges over the same finite vertex set cannot have a
positive-length overlap unless they are the same unordered edge. -/
theorem edge_eq_of_vertexAtomic_of_inter_infinite
    {V : Finset PlanePoint} {e f : Edge}
    (heV : edgeVertices e ⊆ V) (hfV : edgeVertices f ⊆ V)
    (he : IsVertexAtomic V e) (hf : IsVertexAtomic V f)
    (hinter : (edgeCarrier e ∩ edgeCarrier f).Infinite) :
    e = f := by
  rcases e with ⟨pairE, hpairE⟩
  induction pairE using Sym2.ind with
  | _ a b =>
      rcases f with ⟨pairF, hpairF⟩
      induction pairF using Sym2.ind with
      | _ c d =>
          have hab : a ≠ b := by simpa using hpairE
          have hcd : c ≠ d := by simpa using hpairF
          have haV : a ∈ V := heV (by simp [edgeVertices])
          have hbV : b ∈ V := heV (by simp [edgeVertices])
          have hcV : c ∈ V := hfV (by simp [edgeVertices])
          have hdV : d ∈ V := hfV (by simp [edgeVertices])
          have hpairs := unordered_endpoints_eq_of_atomic_inter_infinite
            a b c d hab hcd
            (by simpa [IsVertexAtomic, edgeInteriorCarrier] using he c hcV)
            (by simpa [IsVertexAtomic, edgeInteriorCarrier] using he d hdV)
            (by simpa [IsVertexAtomic, edgeInteriorCarrier] using hf a haV)
            (by simpa [IsVertexAtomic, edgeInteriorCarrier] using hf b hbV)
            (by simpa [edgeCarrier] using hinter)
          exact Edge.eq_of_pair_eq hpairs

/-- A chain all of whose supported edges are atomic for one common finite
vertex set is a reduced representative.  Transverse crossings remain allowed;
only positive-length collinear overlap is excluded. -/
theorem isReducedRepresentative_of_vertexAtomic
    (V : Finset PlanePoint) (C : OneChain)
    (hends : ∀ ⦃e⦄, e ∈ C.support → edgeVertices e ⊆ V)
    (hatom : ∀ ⦃e⦄, e ∈ C.support → IsVertexAtomic V e) :
    IsReducedRepresentative C := by
  intro e he f hf hef
  by_contra hfinite
  exact hef (edge_eq_of_vertexAtomic_of_inter_infinite
    (hends he) (hends hf) (hatom he) (hatom hf) hfinite)

private theorem exists_refinement_atomic_on
    (V U : Finset PlanePoint) (hUV : U ⊆ V) (C : OneChain)
    (hends : ∀ ⦃e⦄, e ∈ C.support → edgeVertices e ⊆ V) :
    ∃ D : OneChain,
      RefinesBySubdivision C D ∧
      (∀ ⦃e⦄, e ∈ D.support → edgeVertices e ⊆ V) ∧
      (∀ ⦃e⦄, e ∈ D.support → IsVertexAtomic U e) := by
  classical
  induction U using Finset.induction_on generalizing C with
  | empty =>
      refine ⟨C, RefinesBySubdivision.refl C, hends, ?_⟩
      intro e he p hp
      exact (by simpa using hp)
  | @insert p U hpU ih =>
      have hpV : p ∈ V := hUV (Finset.mem_insert_self p U)
      have hUV' : U ⊆ V :=
        fun _ hq => hUV (Finset.mem_insert_of_mem hq)
      obtain ⟨D, hCD, hDV, hDU⟩ := ih hUV' C hends
      let E := refineChainAtVertex p D
      have hprops :
          (∀ ⦃g⦄, g ∈ E.support → edgeVertices g ⊆ V) ∧
          (∀ ⦃g⦄, g ∈ E.support →
            IsVertexAtomic (insert p U) g) := by
        exact refineChainAtVertex_properties hpV hDV hDU
      exact ⟨E,
        hCD.trans (refines_refineChainAtVertex p D),
        hprops.1, hprops.2⟩

/-- Splitting every surviving edge at every original endpoint produces a
finite common refinement whose edges contain no original endpoint in their
relative interiors. -/
theorem exists_vertexAtomic_refinement (C : OneChain) :
    ∃ D : OneChain,
      RefinesBySubdivision C D ∧
      (∀ ⦃e⦄, e ∈ D.support →
        edgeVertices e ⊆ oneChainVertices C) ∧
      (∀ ⦃e⦄, e ∈ D.support →
        IsVertexAtomic (oneChainVertices C) e) := by
  exact exists_refinement_atomic_on
    (oneChainVertices C) (oneChainVertices C) (fun _ => id) C
    (fun _ he => edgeVertices_subset_oneChainVertices he)

/-- Every finite formal polygonal chain admits a cancellation-reduced
subdivision refinement. -/
theorem exists_reduced_refinement (C : OneChain) :
    ∃ D : OneChain,
      RefinesBySubdivision C D ∧ IsReducedRepresentative D := by
  obtain ⟨D, hCD, hends, hatom⟩ := exists_vertexAtomic_refinement C
  exact ⟨D, hCD,
    isReducedRepresentative_of_vertexAtomic
      (oneChainVertices C) D hends hatom⟩

/-- Every geometric mod-two polygonal chain has a cancellation-reduced formal
representative. -/
theorem exists_reduced_representative (G : GeometricOneChain) :
    ∃ D : OneChain,
      toGeometric D = G ∧ IsReducedRepresentative D := by
  refine QuotientAddGroup.induction_on G ?_
  intro C
  obtain ⟨D, hCD, hD⟩ := exists_reduced_refinement C
  exact ⟨D, hCD.toGeometric_eq.symm, hD⟩

/-- Every geometric chain has a reduced representative that simultaneously
attains the representative mass infimum and identifies quotient mass with both
its literal carrier and its odd-multiplicity carrier. -/
theorem exists_reduced_representative_mass_identification
    (G : GeometricOneChain) :
    ∃ D : OneChain,
      toGeometric D = G ∧
      IsReducedRepresentative D ∧
      formalMass D = representativeMassInf G ∧
      geometricMass G = formalMass D ∧
      (μH[1] : Measure EuclideanPlane) (oneCarrier D) = geometricMass G ∧
      (μH[1] : Measure EuclideanPlane) (parityCarrier D) = geometricMass G := by
  obtain ⟨D, hDG, hD⟩ := exists_reduced_representative G
  have hinf :
      formalMass D = representativeMassInf G := by
    simpa only [hDG] using
      formalMass_eq_representativeMassInf_of_reduced D hD
  have hmass :
      geometricMass G = formalMass D := by
    simpa only [hDG] using
      geometricMass_toGeometric_eq_formalMass_of_reduced D hD
  refine ⟨D, hDG, hD, hinf, hmass, ?_, ?_⟩
  · rw [hausdorffMeasure_oneCarrier_eq_formalMass D hD, ← hmass]
  · rw [hausdorffMeasure_parityCarrier_eq_formalMass_of_reduced D hD,
      ← hmass]


end CMVPolygonalModTwo
