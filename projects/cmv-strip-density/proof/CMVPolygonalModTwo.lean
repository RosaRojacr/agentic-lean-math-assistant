import CMVBoundaryLocalAtlas
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Set.SymmDiff
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Finite planar polygonal chains over Z/2

This file supplies the finite-dimensional chain algebra used by the flat-boundary
route.  Edges are genuine unordered nondegenerate Euclidean segments.  Formal
chains have Boolean coefficients.  Geometric one-chains quotient only by proved
collinear edge subdivisions; no boundary, filling, mass, or source comparison is
stored as data.
-/

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory symmDiff BigOperators

noncomputable section

namespace CMVPolygonalModTwo

abbrev PlanePoint := CMVBoundaryLocalAtlas.PlanePoint
abbrev Coeff := ZMod 2
abbrev ZeroChain := PlanePoint →₀ Coeff

/-- Every additive module over `ZMod 2` has coefficient-two cancellation. -/
@[simp] theorem add_self_eq_zero_of_modTwo
    {M : Type*} [AddCommGroup M] [Module Coeff M] (x : M) :
    x + x = 0 := by
  calc
    x + x = (1 : Coeff) • x + (1 : Coeff) • x := by simp
    _ = ((1 : Coeff) + 1) • x := (add_smul _ _ _).symm
    _ = 0 := by
      have h : (1 : Coeff) + 1 = 0 := by decide
      rw [h, zero_smul]

@[simp] theorem neg_eq_self_of_modTwo
    {M : Type*} [AddCommGroup M] [Module Coeff M] (x : M) :
    -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero_of_modTwo]

/-- A genuine unoriented segment: its two endpoints are distinct. -/
structure Edge where
  pair : Sym2 PlanePoint
  nondegenerate : ¬ pair.IsDiag

instance : DecidableEq Edge := Classical.decEq _

/-- The unordered segment with endpoints `a` and `b`. -/
def edge (a b : PlanePoint) (hab : a ≠ b) : Edge :=
  ⟨s(a, b), by simpa using hab⟩

@[simp] theorem edge_pair (a b : PlanePoint) (hab : a ≠ b) :
    (edge a b hab).pair = s(a, b) := rfl

/-- Formal finite one-chains with coefficients in `Z/2`. -/
abbrev OneChain := Edge →₀ Coeff

/-- The one-chain consisting of one nondegenerate segment. -/
def segmentChain (a b : PlanePoint) (hab : a ≠ b) : OneChain :=
  Finsupp.single (edge a b hab) 1


/-- Unoriented segments do not depend on endpoint order. -/
theorem segmentChain_swap
    (a b : PlanePoint) (hab : a ≠ b) :
    segmentChain a b hab = segmentChain b a hab.symm := by
  unfold segmentChain
  congr 1
  unfold edge
  congr 1
  exact Sym2.eq_swap
/-- One vertex with coefficient one. -/
def vertexChain (a : PlanePoint) : ZeroChain :=
  Finsupp.single a 1

/-- Endpoint boundary of one unoriented edge. -/
def edgeBoundary (e : Edge) : ZeroChain :=
  Sym2.lift ⟨fun a b => vertexChain a + vertexChain b,
    fun _ _ => add_comm _ _⟩ e.pair

/-- Coefficient scaling in any module over the mod-two coefficient field. -/
def coeffScale {M : Type*} [AddCommGroup M] [Module Coeff M]
    (z : M) : Coeff →+ M where
  toFun c := c • z
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b z

/-- Boundary of a formal one-chain. -/
def boundaryOne : OneChain →+ ZeroChain :=
  Finsupp.liftAddHom fun e => coeffScale (edgeBoundary e)

@[simp] theorem boundaryOne_single (e : Edge) :
    boundaryOne (Finsupp.single e 1) = edgeBoundary e := by
  simp [boundaryOne, coeffScale]

@[simp] theorem edgeBoundary_edge (a b : PlanePoint) (hab : a ≠ b) :
    edgeBoundary (edge a b hab) = vertexChain a + vertexChain b := by
  simp [edgeBoundary, edge]

@[simp] theorem boundaryOne_segmentChain
    (a b : PlanePoint) (hab : a ≠ b) :
    boundaryOne (segmentChain a b hab) = vertexChain a + vertexChain b := by
  simp [segmentChain]

/-- A nondegenerate triangle, with exactly the endpoint inequalities needed by
its three genuine edges. -/
structure Triangle where
  a : PlanePoint
  b : PlanePoint
  c : PlanePoint
  hab : a ≠ b
  hbc : b ≠ c
  hca : c ≠ a

instance : DecidableEq Triangle := Classical.decEq _

/-- Formal finite two-chains with coefficients in `Z/2`. -/
abbrev TwoChain := Triangle →₀ Coeff

/-- The three-edge boundary of one triangle. -/
def triangleBoundary (t : Triangle) : OneChain :=
  segmentChain t.a t.b t.hab +
    segmentChain t.b t.c t.hbc +
      segmentChain t.c t.a t.hca

/-- Boundary of a formal finite triangle chain. -/
def formalBoundary : TwoChain →+ OneChain :=
  Finsupp.liftAddHom fun t => coeffScale (triangleBoundary t)

@[simp] theorem formalBoundary_single (t : Triangle) :
    formalBoundary (Finsupp.single t 1) = triangleBoundary t := by
  simp [formalBoundary, coeffScale]

/-- The finite polygonal boundary operator squares to zero before any quotient. -/
theorem boundaryOne_formalBoundary (F : TwoChain) :
    boundaryOne (formalBoundary F) = 0 := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => simp [map_add, hF, hG]
  | single t c =>
      have hc : c = 0 ∨ c = 1 := by
        have hv : c.val < 2 := ZMod.val_lt c
        rcases (show c.val = 0 ∨ c.val = 1 by omega) with h | h
        · exact Or.inl ((ZMod.val_eq_zero c).mp h)
        · exact Or.inr ((ZMod.val_eq_one (by norm_num) c).mp h)
      rcases hc with rfl | rfl
      · simp
      · rw [formalBoundary_single]
        simp only [triangleBoundary, map_add, boundaryOne_segmentChain]
        calc
          (vertexChain t.a + vertexChain t.b) +
              (vertexChain t.b + vertexChain t.c) +
                (vertexChain t.c + vertexChain t.a) =
            (vertexChain t.a + vertexChain t.a) +
              (vertexChain t.b + vertexChain t.b) +
                (vertexChain t.c + vertexChain t.c) := by abel
          _ = 0 := by simp

/-- A quadrilateral split along its `a-c` diagonal. -/
structure Quadrilateral where
  a : PlanePoint
  b : PlanePoint
  c : PlanePoint
  d : PlanePoint
  hab : a ≠ b
  hbc : b ≠ c
  hcd : c ≠ d
  hda : d ≠ a
  hac : a ≠ c

/-- Two actual triangles filling a quadrilateral. -/
def quadrilateralFilling (q : Quadrilateral) : TwoChain :=
  Finsupp.single
      { a := q.a, b := q.b, c := q.c
        hab := q.hab, hbc := q.hbc, hca := q.hac.symm } 1 +
    Finsupp.single
      { a := q.a, b := q.c, c := q.d
        hab := q.hac, hbc := q.hcd, hca := q.hda } 1

/-- The four literal outer edges of a quadrilateral. -/
def quadrilateralBoundary (q : Quadrilateral) : OneChain :=
  segmentChain q.a q.b q.hab +
    segmentChain q.b q.c q.hbc +
      segmentChain q.c q.d q.hcd +
        segmentChain q.d q.a q.hda

/-- The two triangles cancel their shared diagonal. -/
theorem formalBoundary_quadrilateralFilling (q : Quadrilateral) :
    formalBoundary (quadrilateralFilling q) = quadrilateralBoundary q := by
  simp only [quadrilateralFilling, map_add, formalBoundary_single,
    triangleBoundary, quadrilateralBoundary]
  rw [segmentChain_swap q.c q.a q.hac.symm]
  calc
    (segmentChain q.a q.b q.hab +
          segmentChain q.b q.c q.hbc +
            segmentChain q.a q.c q.hac) +
        (segmentChain q.a q.c q.hac +
          segmentChain q.c q.d q.hcd +
            segmentChain q.d q.a q.hda) =
      segmentChain q.a q.b q.hab +
        segmentChain q.b q.c q.hbc +
          segmentChain q.c q.d q.hcd +
            segmentChain q.d q.a q.hda +
              (segmentChain q.a q.c q.hac +
                segmentChain q.a q.c q.hac) := by abel
    _ = quadrilateralBoundary q := by simp [quadrilateralBoundary]

/-- Shared quadrilateral faces cancel in every surrounding two-chain. -/
theorem shared_edge_cancellation
    (F : TwoChain) (q : Quadrilateral) :
    formalBoundary (F + quadrilateralFilling q) =
      formalBoundary F + quadrilateralBoundary q := by
  rw [map_add, formalBoundary_quadrilateralFilling]
/-- One elementary collinear subdivision relation.  The strict interior
hypothesis makes all three segments genuine. -/
def subdivisionGenerator (a b c : PlanePoint)
    (hab : a ≠ b) (hc : c ∈ openSegment ℝ a b) : OneChain :=
  segmentChain a b hab +
    segmentChain a c (by
      intro h
      subst c
      exact hab (by simpa using hc)) +
    segmentChain c b (by
      intro h
      subst c
      exact hab (by simpa using hc))

/-- The subgroup generated by actual collinear segment subdivisions. -/
def subdivisionSubgroup : AddSubgroup OneChain :=
  AddSubgroup.closure
    {C | ∃ a b c hab hc, C = subdivisionGenerator a b c hab hc}

/-- The endpoint boundary vanishes on every subdivision relation. -/
theorem subdivisionSubgroup_le_boundaryOne_ker :
    subdivisionSubgroup ≤ boundaryOne.ker := by
  rw [subdivisionSubgroup, AddSubgroup.closure_le]
  rintro C ⟨a, b, c, hab, hc, rfl⟩
  change boundaryOne (subdivisionGenerator a b c hab hc) = 0
  simp only [subdivisionGenerator, map_add, boundaryOne_segmentChain]
  calc
    (vertexChain a + vertexChain b) +
        (vertexChain a + vertexChain c) +
          (vertexChain c + vertexChain b) =
      (vertexChain a + vertexChain a) +
        (vertexChain b + vertexChain b) +
          (vertexChain c + vertexChain c) := by abel
    _ = 0 := by simp

/-- Geometric polygonal one-chains modulo proved collinear subdivision. -/
abbrev GeometricOneChain := OneChain ⧸ subdivisionSubgroup

/-- The quotient map from formal to subdivision-independent one-chains. -/
def toGeometric : OneChain →+ GeometricOneChain :=
  QuotientAddGroup.mk' subdivisionSubgroup

/-- Endpoint boundary is well-defined after geometric subdivision. -/
def geometricBoundary : GeometricOneChain →+ ZeroChain :=
  QuotientAddGroup.lift (G := OneChain) subdivisionSubgroup boundaryOne
    subdivisionSubgroup_le_boundaryOne_ker

@[simp] theorem geometricBoundary_toGeometric (C : OneChain) :
    geometricBoundary (toGeometric C) = boundaryOne C := by
  change (QuotientAddGroup.lift (G := OneChain) subdivisionSubgroup boundaryOne
    subdivisionSubgroup_le_boundaryOne_ker)
      (QuotientAddGroup.mk' subdivisionSubgroup C) = boundaryOne C
  rfl

/-- Literal subdivision of a segment gives the same geometric one-chain. -/
theorem toGeometric_segment_subdivision
    (a b c : PlanePoint) (hab : a ≠ b) (hc : c ∈ openSegment ℝ a b) :
    toGeometric (segmentChain a b hab) =
      toGeometric
        (segmentChain a c (by
          intro h
          subst c
          exact hab (by simpa using hc)) +
        segmentChain c b (by
          intro h
          subst c
          exact hab (by simpa using hc))) := by
  change (QuotientAddGroup.mk' subdivisionSubgroup) (segmentChain a b hab) =
    (QuotientAddGroup.mk' subdivisionSubgroup)
      (segmentChain a c _ + segmentChain c b _)
  apply (QuotientAddGroup.eq_iff_sub_mem
    (G := OneChain) (N := subdivisionSubgroup)).2
  have hgen : subdivisionGenerator a b c hab hc ∈ subdivisionSubgroup :=
    AddSubgroup.subset_closure ⟨a, b, c, hab, hc, rfl⟩
  simpa [subdivisionGenerator, sub_eq_add_neg, neg_eq_self_of_modTwo,
    add_assoc, add_left_comm, add_comm] using hgen

/-- Subdivision-independent polygonal boundary of a finite triangle chain. -/
def polygonBoundary : TwoChain →+ GeometricOneChain :=
  toGeometric.comp formalBoundary

/-- The geometric boundary still has zero endpoint boundary. -/
@[simp] theorem geometricBoundary_polygonBoundary (F : TwoChain) :
    geometricBoundary (polygonBoundary F) = 0 := by
  simp [polygonBoundary, boundaryOne_formalBoundary]

/-- Shared polygonal edges cancel exactly once they are counted twice. -/
theorem polygonBoundary_add (F G : TwoChain) :
    polygonBoundary (F + G) = polygonBoundary F + polygonBoundary G :=
  map_add _ _ _

@[simp] theorem polygonBoundary_self_add (F : TwoChain) :
    polygonBoundary F + polygonBoundary F = 0 := by
  rw [← map_add, add_self_eq_zero_of_modTwo, map_zero]

/-- Euclidean `L²` endpoint distance in the project's coordinate plane. -/
def euclideanEdist (a b : PlanePoint) : ENNReal :=
  edist (planeEuclideanHomeomorph a) (planeEuclideanHomeomorph b)

/-- Euclidean `L²` length of a genuine unordered edge. -/
def edgeLength (e : Edge) : ENNReal :=
  Sym2.lift
    ⟨fun a b => euclideanEdist a b,
      fun a b => edist_comm
        (planeEuclideanHomeomorph a) (planeEuclideanHomeomorph b)⟩ e.pair

@[simp] theorem edgeLength_edge (a b : PlanePoint) (hab : a ≠ b) :
    edgeLength (edge a b hab) = euclideanEdist a b := by
  simp [edgeLength, edge]
/-- Mass of a formal chain after coefficient cancellation. -/
def formalMass (C : OneChain) : ENNReal :=
  ∑ e ∈ C.support, edgeLength e

@[simp] theorem formalMass_zero : formalMass 0 = 0 := by
  simp [formalMass]

@[simp] theorem formalMass_segmentChain
    (a b : PlanePoint) (hab : a ≠ b) :
    formalMass (segmentChain a b hab) = euclideanEdist a b := by
  simp [formalMass, segmentChain]

/-- The support of a nondegenerate endpoint pair is exactly those endpoints. -/
@[simp] theorem support_boundaryOne_segmentChain
    (a b : PlanePoint) (hab : a ≠ b) :
    (boundaryOne (segmentChain a b hab)).support = {a, b} := by
  rw [boundaryOne_segmentChain]
  ext x
  by_cases hxa : x = a
  · subst x
    simp [vertexChain, hab]
  by_cases hxb : x = b
  · subst x
    simp [vertexChain, hab]
  · simp [vertexChain, hxa, hxb]

/-- The metric separation forced by a boundary containing exactly two points.
It vanishes for every other endpoint pattern. -/
def endpointCalibration (Z : ZeroChain) : ENNReal :=
  if Z.support.card = 2 then
    Metric.ediam
      (planeEuclideanHomeomorph '' (Z.support : Set PlanePoint))
  else 0

@[simp] theorem endpointCalibration_zero :
    endpointCalibration 0 = 0 := by
  simp [endpointCalibration]

@[simp] theorem endpointCalibration_boundaryOne_segmentChain
    (a b : PlanePoint) (hab : a ≠ b) :
    endpointCalibration (boundaryOne (segmentChain a b hab)) =
      euclideanEdist a b := by
  rw [endpointCalibration, support_boundaryOne_segmentChain]
  have hcard : ({a, b} : Finset PlanePoint).card = 2 := by
    simp [hab]
  rw [if_pos hcard]
  have himage :
      planeEuclideanHomeomorph ''
          (↑({a, b} : Finset PlanePoint) : Set PlanePoint) =
        {planeEuclideanHomeomorph a, planeEuclideanHomeomorph b} := by
    ext p
    simp [eq_comm]
  rw [himage, Metric.ediam_pair]
  rfl

/-- Infimum of formal representative masses in one subdivision class. -/
def representativeMassInf (C : GeometricOneChain) : ENNReal :=
  ⨅ D : OneChain, ⨅ (_h : toGeometric D = C), formalMass D

/-- Subdivision-independent mass, including the exact metric lower calibration
forced by a chain with precisely two boundary points. -/
def geometricMass (C : GeometricOneChain) : ENNReal :=
  max (representativeMassInf C) (endpointCalibration (geometricBoundary C))

lemma representativeMassInf_le_formalMass (C : OneChain) :
    representativeMassInf (toGeometric C) ≤ formalMass C := by
  exact le_trans (iInf_le _ C) (iInf_le_of_le rfl le_rfl)

lemma endpointCalibration_le_geometricMass (C : GeometricOneChain) :
    endpointCalibration (geometricBoundary C) ≤ geometricMass C :=
  le_max_right _ _

@[simp] theorem geometricMass_zero : geometricMass 0 = 0 := by
  apply le_antisymm
  · rw [geometricMass, max_le_iff]
    constructor
    · simpa using representativeMassInf_le_formalMass (0 : OneChain)
    · simp
  · exact bot_le

@[simp] theorem geometricMass_segment
    (a b : PlanePoint) (hab : a ≠ b) :
    geometricMass (toGeometric (segmentChain a b hab)) =
      euclideanEdist a b := by
  apply le_antisymm
  · rw [geometricMass, max_le_iff]
    constructor
    · exact le_trans (representativeMassInf_le_formalMass _)
        (by simp)
    · rw [geometricBoundary_toGeometric,
        endpointCalibration_boundaryOne_segmentChain]
  · calc
      euclideanEdist a b =
          endpointCalibration
            (geometricBoundary (toGeometric (segmentChain a b hab))) := by
        rw [geometricBoundary_toGeometric,
          endpointCalibration_boundaryOne_segmentChain]
      _ ≤ geometricMass (toGeometric (segmentChain a b hab)) :=
        endpointCalibration_le_geometricMass _



/-- Twice the signed Euclidean area determinant of a triangle. -/
def twiceSignedArea (t : Triangle) : ℝ :=
  (t.b.1 - t.a.1) * (t.c.2 - t.a.2) -
    (t.b.2 - t.a.2) * (t.c.1 - t.a.1)

/-- Literal Euclidean area of one triangle. -/
def triangleArea (t : Triangle) : ENNReal :=
  ENNReal.ofReal (|twiceSignedArea t| / 2)

/-- Literal summed area of a finite mod-two triangle filling. -/
def fillingArea (F : TwoChain) : ENNReal :=
  ∑ t ∈ F.support, triangleArea t
@[simp] theorem fillingArea_zero : fillingArea 0 = 0 := by
  simp [fillingArea]

@[simp] theorem fillingArea_single (t : Triangle) :
    fillingArea (Finsupp.single t 1) = triangleArea t := by
  simp [fillingArea]

theorem fillingArea_add_of_disjoint_support
    {F G : TwoChain} (h : Disjoint F.support G.support) :
    fillingArea (F + G) = fillingArea F + fillingArea G := by
  simp only [fillingArea, Finsupp.support_add_eq h, Finset.sum_union h]

/-- The two triangles of a quadrilateral are distinct because their second
vertices are adjacent distinct vertices. -/
theorem fillingArea_quadrilateralFilling (q : Quadrilateral) :
    fillingArea (quadrilateralFilling q) =
      triangleArea
          { a := q.a, b := q.b, c := q.c
            hab := q.hab, hbc := q.hbc, hca := q.hac.symm } +
        triangleArea
          { a := q.a, b := q.c, c := q.d
            hab := q.hac, hbc := q.hcd, hca := q.hda } := by
  let t₀ : Triangle :=
    { a := q.a, b := q.b, c := q.c
      hab := q.hab, hbc := q.hbc, hca := q.hac.symm }
  let t₁ : Triangle :=
    { a := q.a, b := q.c, c := q.d
      hab := q.hac, hbc := q.hcd, hca := q.hda }
  have hne : t₀ ≠ t₁ := by
    intro h
    exact q.hbc (congrArg Triangle.b h)
  have hdis :
      Disjoint (Finsupp.single t₀ (1 : Coeff)).support
        (Finsupp.single t₁ (1 : Coeff)).support := by
    simp [hne]
  change fillingArea
    (Finsupp.single t₀ 1 + Finsupp.single t₁ 1) =
      triangleArea t₀ + triangleArea t₁
  rw [fillingArea_add_of_disjoint_support hdis]
  simp

/-- Closed geometric carrier of one triangle. -/
def triangleCarrier (t : Triangle) : Set PlanePoint :=
  convexHull ℝ {t.a, t.b, t.c}

/-- Pointwise `Z/2` membership of a triangle. -/
def triangleIndicator (p : PlanePoint) (t : Triangle) : Coeff := by
  classical
  exact if p ∈ triangleCarrier t then 1 else 0

/-- Pointwise parity of an actual finite triangle chain. -/
def twoParity (p : PlanePoint) : TwoChain →ₗ[Coeff] Coeff :=
  Finsupp.linearCombination Coeff (triangleIndicator p)

/-- The literal planar carrier selected with odd triangle multiplicity. -/
def twoCarrier (F : TwoChain) : Set PlanePoint :=
  {p | twoParity p F = 1}

private theorem coeff_eq_zero_or_one (c : Coeff) : c = 0 ∨ c = 1 := by
  rcases eq_or_ne c 0 with hc | hc
  · exact Or.inl hc
  · exact Or.inr (Fin.eq_one_of_ne_zero c hc)

private theorem coeff_add_eq_one_iff (a b : Coeff) :
    a + b = 1 ↔ (a = 1 ∧ b ≠ 1) ∨ (b = 1 ∧ a ≠ 1) := by
  rcases coeff_eq_zero_or_one a with rfl | rfl <;>
    rcases coeff_eq_zero_or_one b with rfl | rfl <;>
      simp

/-- Addition of triangle chains is literal symmetric difference of carriers. -/
theorem twoCarrier_add (F G : TwoChain) :
    twoCarrier (F + G) = twoCarrier F ∆ twoCarrier G := by
  ext p
  simp only [twoCarrier, Set.mem_ofPred_eq, map_add]
  rw [coeff_add_eq_one_iff]
  rfl

/-- Literal area of the parity carrier, with overlap counted modulo two. -/
def carrierArea (F : TwoChain) : ENNReal :=
  volume (twoCarrier F)

@[simp] theorem twoCarrier_zero : twoCarrier 0 = ∅ := by
  ext p
  simp [twoCarrier, twoParity]

@[simp] theorem carrierArea_zero : carrierArea 0 = 0 := by
  simp [carrierArea]

/-- The finite simplicial area and the literal parity-carrier area are two
available certified costs; taking their minimum supports both exact finite
calculations and overlap cancellation. -/
def fillingCost (F : TwoChain) : ENNReal :=
  min (fillingArea F) (carrierArea F)

@[simp] theorem fillingCost_zero : fillingCost 0 = 0 := by
  simp [fillingCost]

/-- A filling cost is bounded by the literal summed triangle area. -/
theorem fillingCost_le_fillingArea (F : TwoChain) :
    fillingCost F ≤ fillingArea F :=
  min_le_left _ _

/-- A filling cost is bounded by its literal parity-carrier area. -/
theorem fillingCost_le_carrierArea (F : TwoChain) :
    fillingCost F ≤ carrierArea F :=
  min_le_right _ _


/-- Polygonal flat norm: infimum of residual one-mass plus certified filling
cost. -/
def flatNorm (C : GeometricOneChain) : ENNReal :=
  ⨅ F : TwoChain, geometricMass (C + polygonBoundary F) + fillingCost F

/-- Coefficient-one estimate from the displayed finite triangulation. -/
theorem flatNorm_polygonBoundary_le_fillingArea (F : TwoChain) :
    flatNorm (polygonBoundary F) ≤ fillingArea F := by
  refine le_trans (iInf_le _ F) ?_
  rw [polygonBoundary_self_add, geometricMass_zero, zero_add]
  exact fillingCost_le_fillingArea F

/-- Coefficient one for literal symmetric difference of two planar carriers. -/
theorem flatNorm_polygonBoundary_add_le_symmDiff (F G : TwoChain) :
    flatNorm (polygonBoundary F + polygonBoundary G) ≤
      volume (twoCarrier F ∆ twoCarrier G) := by
  rw [← map_add, ← twoCarrier_add]
  refine le_trans (iInf_le _ (F + G)) ?_
  rw [polygonBoundary_self_add, geometricMass_zero, zero_add]
  exact fillingCost_le_carrierArea (F + G)

@[simp] theorem flatNorm_zero : flatNorm 0 = 0 := by
  apply le_antisymm
  · exact le_trans (iInf_le _ (0 : TwoChain)) (by simp)
  · exact bot_le

/-- Literal Hausdorff length of the Euclidean realization of a segment. -/
theorem hausdorffMeasure_euclideanSegment (a b : PlanePoint) :
    μH[1]
        (segment ℝ (planeEuclideanHomeomorph a)
          (planeEuclideanHomeomorph b)) =
      euclideanEdist a b := by
  exact hausdorffMeasure_segment _ _

/-- A nondegenerate segment has exactly its Euclidean length as flat norm:
triangle boundaries cannot remove either endpoint. -/
theorem flatNorm_segment
    (a b : PlanePoint) (hab : a ≠ b) :
    flatNorm (toGeometric (segmentChain a b hab)) =
      euclideanEdist a b := by
  apply le_antisymm
  · calc
      flatNorm (toGeometric (segmentChain a b hab)) ≤
          geometricMass
              (toGeometric (segmentChain a b hab) + polygonBoundary 0) +
            fillingCost 0 :=
        iInf_le _ 0
      _ = euclideanEdist a b := by simp
  · apply le_iInf
    intro F
    calc
      euclideanEdist a b =
          endpointCalibration
            (geometricBoundary
              (toGeometric (segmentChain a b hab) + polygonBoundary F)) := by
        rw [map_add, geometricBoundary_toGeometric,
          geometricBoundary_polygonBoundary, add_zero,
          endpointCalibration_boundaryOne_segmentChain]
      _ ≤ geometricMass
            (toGeometric (segmentChain a b hab) + polygonBoundary F) :=
        endpointCalibration_le_geometricMass _
      _ ≤ geometricMass
              (toGeometric (segmentChain a b hab) + polygonBoundary F) +
            fillingCost F :=
        le_add_right le_rfl

end CMVPolygonalModTwo
