import CMVPolygonalModTwoApplications
import Mathlib.Analysis.Convex.Combination

open Set MeasureTheory Metric Filter
open scoped ENNReal MeasureTheory BigOperators Topology symmDiff

noncomputable section

namespace CMVPolygonalModTwo

private def lowerTriangle (r : ℝ) (hr : 0 < r) : Triangle where
  a := (-r, -r)
  b := (r, -r)
  c := (r, r)
  hab := by intro h; have := congrArg Prod.fst h; simp at this; linarith
  hbc := by intro h; have := congrArg Prod.snd h; simp at this; linarith
  hca := by intro h; have := congrArg Prod.fst h; simp at this; linarith

private def lowerRegion (r : ℝ) : Set PlanePoint :=
  {p | -r ≤ p.1 ∧ p.1 ≤ r ∧ -r ≤ p.2 ∧ p.2 ≤ r ∧ p.2 ≤ p.1}

private theorem convex_lowerRegion (r : ℝ) : Convex ℝ (lowerRegion r) := by
  rintro p hp q hq a b ha hb hab
  rcases hp with ⟨hpx0, hpx1, hpy0, hpy1, hdiagp⟩
  rcases hq with ⟨hqx0, hqx1, hqy0, hqy1, hdiagq⟩
  change -r ≤ (a • p + b • q).1 ∧
    (a • p + b • q).1 ≤ r ∧
    -r ≤ (a • p + b • q).2 ∧
    (a • p + b • q).2 ≤ r ∧
    (a • p + b • q).2 ≤ (a • p + b • q).1
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem triangleCarrier_lowerTriangle (r : ℝ) (hr : 0 < r) :
    triangleCarrier (lowerTriangle r hr) = lowerRegion r := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp [lowerRegion, lowerTriangle] <;> linarith
    · exact convex_lowerRegion r
  · intro p hp
    let w : Fin 3 → ℝ :=
      ![(r - p.1) / (2 * r), (p.1 - p.2) / (2 * r),
        (p.2 + r) / (2 * r)]
    let z : Fin 3 → PlanePoint :=
      ![(-r, -r), (r, -r), (r, r)]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · rcases hp with ⟨h0, h1, h2, h3, h4⟩
      intro i
      fin_cases i
      · change 0 ≤ (r - p.1) / (2 * r)
        apply div_nonneg <;> nlinarith
      · change 0 ≤ (p.1 - p.2) / (2 * r)
        apply div_nonneg <;> nlinarith
      · change 0 ≤ (p.2 + r) / (2 * r)
        apply div_nonneg <;> nlinarith
    · simp [w, Fin.sum_univ_succ]
      field_simp
      ring
    · intro i
      fin_cases i <;> simp [z, lowerTriangle]
    · apply Prod.ext <;> simp [w, z, Fin.sum_univ_succ]
      · field_simp
        ring
      · field_simp
        ring


private def upperTriangle (r : ℝ) (hr : 0 < r) : Triangle where
  a := (-r, -r)
  b := (r, r)
  c := (-r, r)
  hab := by intro h; have := congrArg Prod.fst h; simp at this; linarith
  hbc := by intro h; have := congrArg Prod.fst h; simp at this; linarith
  hca := by intro h; have := congrArg Prod.snd h; simp at this; linarith

private def upperRegion (r : ℝ) : Set PlanePoint :=
  {p | -r ≤ p.1 ∧ p.1 ≤ r ∧ -r ≤ p.2 ∧ p.2 ≤ r ∧ p.1 ≤ p.2}

private theorem convex_upperRegion (r : ℝ) : Convex ℝ (upperRegion r) := by
  rintro p hp q hq a b ha hb hab
  rcases hp with ⟨hpx0, hpx1, hpy0, hpy1, hdiagp⟩
  rcases hq with ⟨hqx0, hqx1, hqy0, hqy1, hdiagq⟩
  change -r ≤ (a • p + b • q).1 ∧
    (a • p + b • q).1 ≤ r ∧
    -r ≤ (a • p + b • q).2 ∧
    (a • p + b • q).2 ≤ r ∧
    (a • p + b • q).1 ≤ (a • p + b • q).2
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

private theorem triangleCarrier_upperTriangle (r : ℝ) (hr : 0 < r) :
    triangleCarrier (upperTriangle r hr) = upperRegion r := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl <;>
        simp [upperRegion, upperTriangle] <;> linarith
    · exact convex_upperRegion r
  · intro p hp
    let w : Fin 3 → ℝ :=
      ![(r - p.2) / (2 * r), (p.1 + r) / (2 * r),
        (p.2 - p.1) / (2 * r)]
    let z : Fin 3 → PlanePoint :=
      ![(-r, -r), (r, r), (-r, r)]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · rcases hp with ⟨h0, h1, h2, h3, h4⟩
      intro i
      fin_cases i
      · change 0 ≤ (r - p.2) / (2 * r)
        apply div_nonneg <;> nlinarith
      · change 0 ≤ (p.1 + r) / (2 * r)
        apply div_nonneg <;> nlinarith
      · change 0 ≤ (p.2 - p.1) / (2 * r)
        apply div_nonneg <;> nlinarith
    · simp [w, Fin.sum_univ_succ]
      field_simp
      ring
    · intro i
      fin_cases i <;> simp [z, upperTriangle]
    · apply Prod.ext <;> simp [w, z, Fin.sum_univ_succ]
      · field_simp
        ring
      · field_simp
        ring

private theorem twoCarrier_single (t : Triangle) :
    twoCarrier (Finsupp.single t 1) = triangleCarrier t := by
  ext p
  simp [twoCarrier, twoParity, triangleIndicator]

private def squareCarrier (r : ℝ) : Set PlanePoint :=
  Icc (-r) r ×ˢ Icc (-r) r

private def squareFilling (r : ℝ) (hr : 0 < r) : TwoChain :=
  Finsupp.single (lowerTriangle r hr) 1 +
    Finsupp.single (upperTriangle r hr) 1

private def diagonal : Set PlanePoint := {p | p.1 = p.2}

private theorem twoCarrier_squareFilling (r : ℝ) (hr : 0 < r) :
    twoCarrier (squareFilling r hr) = squareCarrier r \ diagonal := by
  rw [squareFilling, twoCarrier_add, twoCarrier_single, twoCarrier_single,
    triangleCarrier_lowerTriangle, triangleCarrier_upperTriangle]
  ext p
  rcases p with ⟨x, y⟩
  simp only [Set.mem_symmDiff]
  by_cases hxy : y ≤ x
  · by_cases hyx : x ≤ y
    · have hEq : x = y := le_antisymm hyx hxy
      simp [lowerRegion, upperRegion, squareCarrier, diagonal, hEq]
    · simp [lowerRegion, upperRegion, squareCarrier, diagonal, hxy, hyx,
        ne_of_gt (lt_of_not_ge hyx)]
      tauto
  · have hyx : x ≤ y := le_of_not_ge hxy
    simp [lowerRegion, upperRegion, squareCarrier, diagonal, hxy, hyx,
      ne_of_lt (lt_of_not_ge hxy)]
    tauto

private theorem measurableSet_diagonal : MeasurableSet diagonal := by
  exact (isClosed_eq continuous_fst continuous_snd).measurableSet

private theorem volume_diagonal : volume diagonal = 0 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm measurableSet_diagonal]
  have hfiber : ∀ y : ℝ,
      volume ((fun x : ℝ => (x, y)) ⁻¹' diagonal) = 0 := by
    intro y
    have hset : (fun x : ℝ => (x, y)) ⁻¹' diagonal = ({y} : Set ℝ) := by
      ext x
      simp [diagonal]
    rw [hset]
    simp
  simp_rw [hfiber]
  simp

private theorem squareCarrier_ae_twoCarrier (r : ℝ) (hr : 0 < r) :
    squareCarrier r =ᵐ[volume] twoCarrier (squareFilling r hr) := by
  rw [twoCarrier_squareFilling]
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (t := diagonal)
    · intro p hp
      by_contra hpd
      exact hp.2 ⟨hp.1, hpd⟩
    · exact volume_diagonal
  · simp


/-- A bounded measurable planar region together with a proved finite mod-two
triangulation. The carrier-to-triangulation relation is almost everywhere
because internal subdivision edges are counted twice and have planar measure
zero. -/
structure RegularPolygonalRegion where
  carrier : Set PlanePoint
  filling : TwoChain
  measurable_carrier : MeasurableSet carrier
  bounded_carrier : Bornology.IsBounded carrier
  carrier_ae_twoCarrier : carrier =ᵐ[volume] twoCarrier filling

namespace RegularPolygonalRegion

/-- Subdivision-independent boundary of an actual polygonal region. -/
def boundary (E : RegularPolygonalRegion) : GeometricOneChain :=
  polygonBoundary E.filling

/-- The empty region, including the empty triangulation. -/
def empty : RegularPolygonalRegion where
  carrier := ∅
  filling := 0
  measurable_carrier := MeasurableSet.empty
  bounded_carrier := Bornology.isBounded_empty
  carrier_ae_twoCarrier := by simp

@[simp] theorem boundary_empty : empty.boundary = 0 := by
  simp [boundary, empty]

/-- Literal symmetric difference, represented by mod-two addition of the two
proved triangulations. -/
def xor (E F : RegularPolygonalRegion) : RegularPolygonalRegion where
  carrier := E.carrier ∆ F.carrier
  filling := E.filling + F.filling
  measurable_carrier := by
    rw [Set.symmDiff_def]
    exact (E.measurable_carrier.diff F.measurable_carrier).union
      (F.measurable_carrier.diff E.measurable_carrier)
  bounded_carrier := by
    apply (E.bounded_carrier.union F.bounded_carrier).subset
    exact Set.symmDiff_subset_union
  carrier_ae_twoCarrier := by
    filter_upwards [E.carrier_ae_twoCarrier, F.carrier_ae_twoCarrier] with p hp hq
    change (p ∈ E.carrier ∆ F.carrier) =
      (p ∈ twoCarrier (E.filling + F.filling))
    rw [twoCarrier_add]
    apply propext
    simp only [Set.mem_symmDiff] at hp hq ⊢
    tauto

/-- The actual-region boundary map respects symmetric difference. -/
theorem boundary_xor (E F : RegularPolygonalRegion) :
    (xor E F).boundary = E.boundary + F.boundary := by
  exact polygonBoundary_add E.filling F.filling

/-- Coefficient-one area filling for two actual bounded measurable polygonal
regions. -/
theorem flatNorm_boundary_add_le_volume_symmDiff
    (E F : RegularPolygonalRegion) :
    flatNorm (E.boundary + F.boundary) ≤ volume (E.carrier ∆ F.carrier) := by
  have hae :
      E.carrier ∆ F.carrier =ᵐ[volume]
        twoCarrier E.filling ∆ twoCarrier F.filling := by
    filter_upwards [E.carrier_ae_twoCarrier, F.carrier_ae_twoCarrier] with p hp hq
    change (p ∈ E.carrier ∆ F.carrier) =
      (p ∈ twoCarrier E.filling ∆ twoCarrier F.filling)
    apply propext
    simp only [Set.mem_symmDiff] at hp hq ⊢
    tauto
  calc
    flatNorm (E.boundary + F.boundary) ≤
        volume (twoCarrier E.filling ∆ twoCarrier F.filling) := by
      exact flatNorm_polygonBoundary_add_le_symmDiff E.filling F.filling
    _ = volume (E.carrier ∆ F.carrier) := measure_congr hae.symm

/-- The axis-aligned square of positive radius with its two actual triangular
pieces. -/
def square (r : ℝ) (hr : 0 < r) : RegularPolygonalRegion where
  carrier := squareCarrier r
  filling := squareFilling r hr
  measurable_carrier := measurableSet_Icc.prod measurableSet_Icc
  bounded_carrier := (Metric.isBounded_Icc (-r) r).prod
    (Metric.isBounded_Icc (-r) r)
  carrier_ae_twoCarrier := squareCarrier_ae_twoCarrier r hr

end RegularPolygonalRegion

namespace RegularPolygonalRegion

def outerSquare : RegularPolygonalRegion := square 2 (by norm_num)

def innerSquare : RegularPolygonalRegion := square 1 (by norm_num)

/-- The actual rectangular annulus is the literal symmetric difference of two
nested regular polygonal squares. -/
def rectangularAnnulus : RegularPolygonalRegion := xor outerSquare innerSquare

theorem innerSquare_carrier_subset_outerSquare :
    innerSquare.carrier ⊆ outerSquare.carrier := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

/-- The regular-region carrier is the previously displayed literal rectangular
annulus, not a formal chain placeholder. -/
theorem rectangularAnnulus_carrier :
    rectangularAnnulus.carrier = rectangularAnnulusCarrier := by
  change squareCarrier 2 ∆ squareCarrier 1 =
    (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) \
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
  rw [Set.symmDiff_def]
  have hsub : squareCarrier 1 ⊆ squareCarrier 2 :=
    innerSquare_carrier_subset_outerSquare
  have hempty : squareCarrier 1 \ squareCarrier 2 = ∅ :=
    Set.sdiff_eq_empty.mpr hsub
  rw [hempty, union_empty]
  rfl

theorem volume_rectangularAnnulus :
    volume rectangularAnnulus.carrier = 12 := by
  rw [rectangularAnnulus_carrier]
  exact volume_rectangularAnnulusCarrier

/-- The requested actual-region identity: the two nested square boundaries add
to the boundary of their literal symmetric-difference annulus. -/
theorem outerSquare_boundary_add_innerSquare_boundary :
    outerSquare.boundary + innerSquare.boundary =
      rectangularAnnulus.boundary :=
  (boundary_xor outerSquare innerSquare).symm

/-- The actual annulus consumes the coefficient-one area filling estimate. -/
theorem flatNorm_rectangularAnnulus_boundary_le_volume :
    flatNorm rectangularAnnulus.boundary ≤
      volume rectangularAnnulus.carrier := by
  change flatNorm (xor outerSquare innerSquare).boundary ≤
    volume (xor outerSquare innerSquare).carrier
  rw [boundary_xor]
  exact flatNorm_boundary_add_le_volume_symmDiff outerSquare innerSquare

theorem flatNorm_rectangularAnnulus_boundary_le_twelve :
    flatNorm rectangularAnnulus.boundary ≤ 12 := by
  rw [← volume_rectangularAnnulus]
  exact flatNorm_rectangularAnnulus_boundary_le_volume

end RegularPolygonalRegion

/-- Three distinct collinear vertices form a legitimate area-degenerate
subdivision piece. -/
def collinearTriangle : Triangle where
  a := (0, 0)
  b := (2, 0)
  c := (1, 0)
  hab := by norm_num
  hbc := by norm_num
  hca := by norm_num
/-- Mod-two cancellation survives the subdivision quotient. -/
theorem geometric_add_self_eq_zero (C : GeometricOneChain) :
    C + C = 0 := by
  refine QuotientAddGroup.induction_on C ?_
  intro D
  change toGeometric D + toGeometric D = 0
  rw [← map_add, add_self_eq_zero_of_modTwo, map_zero]

theorem geometric_pair_boundary_cancel (A B : GeometricOneChain) :
    (A + B) + B + A = 0 := by
  calc
    (A + B) + B + A = (A + A) + (B + B) := by abel
    _ = 0 := by
      rw [geometric_add_self_eq_zero, geometric_add_self_eq_zero, zero_add]


theorem collinear_midpoint_mem_openSegment :
    ((1, 0) : PlanePoint) ∈
      openSegment ℝ ((0, 0) : PlanePoint) ((2, 0) : PlanePoint) := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- The long edge of the collinear triangle is exactly subdivided by its other
two edges, so the geometric boundary is zero. -/
theorem polygonBoundary_collinearTriangle_zero :
    polygonBoundary (Finsupp.single collinearTriangle 1) = 0 := by
  have hsub := toGeometric_segment_subdivision
    ((0, 0) : PlanePoint) ((2, 0) : PlanePoint) ((1, 0) : PlanePoint)
    (by norm_num) collinear_midpoint_mem_openSegment
  simp only [polygonBoundary, AddMonoidHom.coe_comp, Function.comp_apply,
    formalBoundary_single, triangleBoundary, collinearTriangle, map_add]
  rw [segmentChain_swap ((2, 0) : PlanePoint) ((1, 0) : PlanePoint) (by norm_num),
    segmentChain_swap ((1, 0) : PlanePoint) ((0, 0) : PlanePoint) (by norm_num)]
  rw [hsub]
  simp only [map_add]
  exact geometric_pair_boundary_cancel _ _
/-- The same area-degenerate piece contributes exactly zero filling area. -/
theorem fillingArea_collinearTriangle_zero :
    fillingArea (Finsupp.single collinearTriangle 1) = 0 := by
  simp [triangleArea, twiceSignedArea, collinearTriangle]


end CMVPolygonalModTwo
