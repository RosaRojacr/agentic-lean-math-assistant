import CMVPolygonalModTwoParity

/-!
# Concrete polygonal mod-two fillings

Four quadrilateral sectors give an actual eight-triangle rectangular annulus.
The boundary calculation is entirely combinatorial; the literal carrier and its
Lebesgue area are derived separately.
-/

open Set MeasureTheory Metric Filter
open scoped ENNReal MeasureTheory BigOperators Topology

noncomputable section

namespace CMVPolygonalModTwo

/-- Four outer vertices and four inner vertices, with exactly the inequalities
needed by the eight-triangle sector filling. -/
structure FourRing where
  o0 : PlanePoint
  o1 : PlanePoint
  o2 : PlanePoint
  o3 : PlanePoint
  i0 : PlanePoint
  i1 : PlanePoint
  i2 : PlanePoint
  i3 : PlanePoint
  ho01 : o0 ≠ o1
  ho12 : o1 ≠ o2
  ho23 : o2 ≠ o3
  ho30 : o3 ≠ o0
  hi01 : i0 ≠ i1
  hi12 : i1 ≠ i2
  hi23 : i2 ≠ i3
  hi30 : i3 ≠ i0
  hr0 : o0 ≠ i0
  hr1 : o1 ≠ i1
  hr2 : o2 ≠ i2
  hr3 : o3 ≠ i3
  hd01 : o0 ≠ i1
  hd12 : o1 ≠ i2
  hd23 : o2 ≠ i3
  hd30 : o3 ≠ i0

def FourRing.q0 (r : FourRing) : Quadrilateral where
  a := r.o0
  b := r.o1
  c := r.i1
  d := r.i0
  hab := r.ho01
  hbc := r.hr1
  hcd := r.hi01.symm
  hda := r.hr0.symm
  hac := r.hd01

def FourRing.q1 (r : FourRing) : Quadrilateral where
  a := r.o1
  b := r.o2
  c := r.i2
  d := r.i1
  hab := r.ho12
  hbc := r.hr2
  hcd := r.hi12.symm
  hda := r.hr1.symm
  hac := r.hd12

def FourRing.q2 (r : FourRing) : Quadrilateral where
  a := r.o2
  b := r.o3
  c := r.i3
  d := r.i2
  hab := r.ho23
  hbc := r.hr3
  hcd := r.hi23.symm
  hda := r.hr2.symm
  hac := r.hd23

def FourRing.q3 (r : FourRing) : Quadrilateral where
  a := r.o3
  b := r.o0
  c := r.i0
  d := r.i3
  hab := r.ho30
  hbc := r.hr0
  hcd := r.hi30.symm
  hda := r.hr3.symm
  hac := r.hd30

/-- Eight actual triangles filling the four sectors of a ring. -/
def ringFilling (r : FourRing) : TwoChain :=
  quadrilateralFilling r.q0 + quadrilateralFilling r.q1 +
    quadrilateralFilling r.q2 + quadrilateralFilling r.q3

private theorem quadrilateralFilling_support_a (q : Quadrilateral) (t : Triangle)
    (ht : t ∈ (quadrilateralFilling q).support) : t.a = q.a := by
  have hu := Finsupp.support_add ht
  simp only [Finsupp.support_single _ one_ne_zero,
    Finset.mem_union, Finset.mem_singleton] at hu
  rcases hu with h | h
  · rw [h]
  · rw [h]

private theorem quadrilateralFillings_disjoint (q r : Quadrilateral)
    (h : q.a ≠ r.a) :
    Disjoint (quadrilateralFilling q).support
      (quadrilateralFilling r).support := by
  rw [Finset.disjoint_left]
  intro t htq htr
  exact h ((quadrilateralFilling_support_a q t htq).symm.trans
    (quadrilateralFilling_support_a r t htr))

/-- Four outer and four inner edges of the ring. -/
def ringBoundary (r : FourRing) : OneChain :=
  segmentChain r.o0 r.o1 r.ho01 +
    segmentChain r.o1 r.o2 r.ho12 +
      segmentChain r.o2 r.o3 r.ho23 +
        segmentChain r.o3 r.o0 r.ho30 +
          segmentChain r.i1 r.i0 r.hi01.symm +
            segmentChain r.i2 r.i1 r.hi12.symm +
              segmentChain r.i3 r.i2 r.hi23.symm +
                segmentChain r.i0 r.i3 r.hi30.symm

/-- Every radial sector edge occurs twice and cancels. -/
theorem formalBoundary_ringFilling (r : FourRing) :
    formalBoundary (ringFilling r) = ringBoundary r := by
  simp only [ringFilling, map_add, formalBoundary_quadrilateralFilling,
    FourRing.q0, FourRing.q1, FourRing.q2, FourRing.q3,
    quadrilateralBoundary]
  rw [segmentChain_swap r.i0 r.o0 r.hr0.symm,
    segmentChain_swap r.i1 r.o1 r.hr1.symm,
    segmentChain_swap r.i2 r.o2 r.hr2.symm,
    segmentChain_swap r.i3 r.o3 r.hr3.symm]
  calc
    (segmentChain r.o0 r.o1 r.ho01 +
          segmentChain r.o1 r.i1 r.hr1 +
            segmentChain r.i1 r.i0 r.hi01.symm +
              segmentChain r.o0 r.i0 r.hr0) +
        (segmentChain r.o1 r.o2 r.ho12 +
          segmentChain r.o2 r.i2 r.hr2 +
            segmentChain r.i2 r.i1 r.hi12.symm +
              segmentChain r.o1 r.i1 r.hr1) +
          (segmentChain r.o2 r.o3 r.ho23 +
            segmentChain r.o3 r.i3 r.hr3 +
              segmentChain r.i3 r.i2 r.hi23.symm +
                segmentChain r.o2 r.i2 r.hr2) +
            (segmentChain r.o3 r.o0 r.ho30 +
              segmentChain r.o0 r.i0 r.hr0 +
                segmentChain r.i0 r.i3 r.hi30.symm +
                  segmentChain r.o3 r.i3 r.hr3) =
      ringBoundary r +
        (segmentChain r.o0 r.i0 r.hr0 + segmentChain r.o0 r.i0 r.hr0) +
        (segmentChain r.o1 r.i1 r.hr1 + segmentChain r.o1 r.i1 r.hr1) +
        (segmentChain r.o2 r.i2 r.hr2 + segmentChain r.o2 r.i2 r.hr2) +
        (segmentChain r.o3 r.i3 r.hr3 + segmentChain r.o3 r.i3 r.hr3) := by
      simp only [ringBoundary]
      abel
    _ = ringBoundary r := by simp

/-- The fixed nested squares `[-2,2]²` and `[-1,1]²` form a concrete ring. -/
def rectangularAnnulusRing : FourRing where
  o0 := (-2, -2)
  o1 := (2, -2)
  o2 := (2, 2)
  o3 := (-2, 2)
  i0 := (-1, -1)
  i1 := (1, -1)
  i2 := (1, 1)
  i3 := (-1, 1)
  ho01 := by norm_num
  ho12 := by norm_num
  ho23 := by norm_num
  ho30 := by norm_num
  hi01 := by norm_num
  hi12 := by norm_num
  hi23 := by norm_num
  hi30 := by norm_num
  hr0 := by norm_num
  hr1 := by norm_num
  hr2 := by norm_num
  hr3 := by norm_num
  hd01 := by norm_num
  hd12 := by norm_num
  hd23 := by norm_num
  hd30 := by norm_num

/-- The actual finite eight-triangle annulus filling. -/
def rectangularAnnulusFilling : TwoChain :=
  ringFilling rectangularAnnulusRing

private theorem fillingArea_rectangularAnnulus_q0 :
    fillingArea (quadrilateralFilling rectangularAnnulusRing.q0) = 3 := by
  rw [fillingArea_quadrilateralFilling]
  norm_num [triangleArea, twiceSignedArea, rectangularAnnulusRing, FourRing.q0]

private theorem fillingArea_rectangularAnnulus_q1 :
    fillingArea (quadrilateralFilling rectangularAnnulusRing.q1) = 3 := by
  rw [fillingArea_quadrilateralFilling]
  norm_num [triangleArea, twiceSignedArea, rectangularAnnulusRing, FourRing.q1]

private theorem fillingArea_rectangularAnnulus_q2 :
    fillingArea (quadrilateralFilling rectangularAnnulusRing.q2) = 3 := by
  rw [fillingArea_quadrilateralFilling]
  norm_num [triangleArea, twiceSignedArea, rectangularAnnulusRing, FourRing.q2]

private theorem fillingArea_rectangularAnnulus_q3 :
    fillingArea (quadrilateralFilling rectangularAnnulusRing.q3) = 3 := by
  rw [fillingArea_quadrilateralFilling]
  norm_num [triangleArea, twiceSignedArea, rectangularAnnulusRing, FourRing.q3]

/-- The finite filling has coefficient-one area equal to the literal annulus
area: each of its four disjoint quadrilateral sectors has area three. -/
theorem fillingArea_rectangularAnnulusFilling :
    fillingArea rectangularAnnulusFilling = 12 := by
  let Q0 := quadrilateralFilling rectangularAnnulusRing.q0
  let Q1 := quadrilateralFilling rectangularAnnulusRing.q1
  let Q2 := quadrilateralFilling rectangularAnnulusRing.q2
  let Q3 := quadrilateralFilling rectangularAnnulusRing.q3
  have h01 : Disjoint Q0.support Q1.support := by
    apply quadrilateralFillings_disjoint
    norm_num [FourRing.q0, FourRing.q1, rectangularAnnulusRing]
  have h02 : Disjoint Q0.support Q2.support := by
    apply quadrilateralFillings_disjoint
    norm_num [FourRing.q0, FourRing.q2, rectangularAnnulusRing]
  have h12 : Disjoint Q1.support Q2.support := by
    apply quadrilateralFillings_disjoint
    norm_num [FourRing.q1, FourRing.q2, rectangularAnnulusRing]
  have h03 : Disjoint Q0.support Q3.support := by
    apply quadrilateralFillings_disjoint
    norm_num [FourRing.q0, FourRing.q3, rectangularAnnulusRing]
  have h13 : Disjoint Q1.support Q3.support := by
    apply quadrilateralFillings_disjoint
    norm_num [FourRing.q1, FourRing.q3, rectangularAnnulusRing]
  have h23 : Disjoint Q2.support Q3.support := by
    apply quadrilateralFillings_disjoint
    norm_num [FourRing.q2, FourRing.q3, rectangularAnnulusRing]
  have h01_2 : Disjoint (Q0 + Q1).support Q2.support := by
    rw [Finset.disjoint_left]
    intro t ht h2
    have hu := Finsupp.support_add ht
    rcases Finset.mem_union.mp hu with h0 | h1
    · exact (Finset.disjoint_left.mp h02) h0 h2
    · exact (Finset.disjoint_left.mp h12) h1 h2
  have h012_3 : Disjoint ((Q0 + Q1) + Q2).support Q3.support := by
    rw [Finset.disjoint_left]
    intro t ht h3
    have hu := Finsupp.support_add ht
    rcases Finset.mem_union.mp hu with h01' | h2
    · have hu' := Finsupp.support_add h01'
      rcases Finset.mem_union.mp hu' with h0 | h1
      · exact (Finset.disjoint_left.mp h03) h0 h3
      · exact (Finset.disjoint_left.mp h13) h1 h3
    · exact (Finset.disjoint_left.mp h23) h2 h3
  change fillingArea (((Q0 + Q1) + Q2) + Q3) = 12
  rw [fillingArea_add_of_disjoint_support h012_3,
    fillingArea_add_of_disjoint_support h01_2,
    fillingArea_add_of_disjoint_support h01]
  change fillingArea (quadrilateralFilling rectangularAnnulusRing.q0) +
      fillingArea (quadrilateralFilling rectangularAnnulusRing.q1) +
      fillingArea (quadrilateralFilling rectangularAnnulusRing.q2) +
      fillingArea (quadrilateralFilling rectangularAnnulusRing.q3) = 12
  rw [fillingArea_rectangularAnnulus_q0, fillingArea_rectangularAnnulus_q1,
    fillingArea_rectangularAnnulus_q2, fillingArea_rectangularAnnulus_q3]
  norm_num

/-- Its combinatorial boundary is exactly the outer and inner square loops. -/
theorem formalBoundary_rectangularAnnulusFilling :
    formalBoundary rectangularAnnulusFilling =
      ringBoundary rectangularAnnulusRing := by
  exact formalBoundary_ringFilling rectangularAnnulusRing

/-- Literal closed square annulus represented by the polygonal filling. -/
def rectangularAnnulusCarrier : Set PlanePoint :=
  (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) \
    (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)

private theorem innerSquare_subset_outerSquare :
    Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 ⊆
      Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2 := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

private theorem volume_outerSquare :
    volume (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) = 16 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  norm_num

private theorem volume_innerSquare :
    volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) = 4 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  norm_num

/-- The literal rectangular annulus has area `16 - 4 = 12`. -/
theorem volume_rectangularAnnulusCarrier :
    volume rectangularAnnulusCarrier = 12 := by
  rw [rectangularAnnulusCarrier,
    MeasureTheory.measure_sdiff innerSquare_subset_outerSquare
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
      (by rw [volume_innerSquare]; norm_num),
    volume_outerSquare, volume_innerSquare]
  exact ENNReal.sub_eq_of_eq_add (by norm_num) (by norm_num)

/-- Coefficient one: the displayed eight-triangle chain itself is a filling
witness for its polygonal boundary. -/
theorem flatNorm_rectangularAnnulusBoundary_le_fillingArea :
    flatNorm (polygonBoundary rectangularAnnulusFilling) ≤
      fillingArea rectangularAnnulusFilling :=
  flatNorm_polygonBoundary_le_fillingArea _

/-- The annulus boundary has the coefficient-one filling bound `12`, matching
the separately computed literal carrier area. -/
theorem flatNorm_rectangularAnnulusBoundary_le_twelve :
    flatNorm (polygonBoundary rectangularAnnulusFilling) ≤ 12 := by
  rw [← fillingArea_rectangularAnnulusFilling]
  exact flatNorm_rectangularAnnulusBoundary_le_fillingArea

/-- Endpoints of the isolated unit horizontal segment. -/
def unitSegmentA : PlanePoint := (0, 0)

def unitSegmentB : PlanePoint := (1, 0)

theorem unitSegment_ne : unitSegmentA ≠ unitSegmentB := by
  norm_num [unitSegmentA, unitSegmentB]

@[simp] theorem euclideanEdist_unitSegment :
    euclideanEdist unitSegmentA unitSegmentB = 1 := by
  rw [euclideanEdist, edist_dist, planeEuclideanHomeomorph_apply,
    planeEuclideanHomeomorph_apply, WithLp.prod_dist_eq_of_L2]
  norm_num [unitSegmentA, unitSegmentB, Real.dist_eq]

/-- Literal one-dimensional Hausdorff measure of the isolated segment. -/
theorem hausdorffMeasure_unitSegment :
    μH[1]
        (segment ℝ (planeEuclideanHomeomorph unitSegmentA)
          (planeEuclideanHomeomorph unitSegmentB)) = 1 := by
  rw [hausdorffMeasure_euclideanSegment, euclideanEdist_unitSegment]

/-- Exact flat norm of the nondegenerate isolated unit segment. -/
theorem flatNorm_unitSegment :
    flatNorm (toGeometric
      (segmentChain unitSegmentA unitSegmentB unitSegment_ne)) = 1 := by
  rw [flatNorm_segment, euclideanEdist_unitSegment]

/-- Positive heights give a genuine unit-width rectangular quadrilateral. -/
def thinRectangleQuadrilateral (h : ℝ) (hh : 0 < h) : Quadrilateral where
  a := (0, 0)
  b := (1, 0)
  c := (1, h)
  d := (0, h)
  hab := by norm_num
  hbc := by
    intro heq
    have hs := congrArg Prod.snd heq
    simp at hs
    linarith
  hcd := by norm_num
  hda := by
    intro heq
    have hs := congrArg Prod.snd heq
    simp at hs
    linarith
  hac := by norm_num

/-- The two actual triangles in the thin rectangle. -/
def thinRectangleFilling (h : ℝ) (hh : 0 < h) : TwoChain :=
  quadrilateralFilling (thinRectangleQuadrilateral h hh)

/-- Its shared diagonal cancels, leaving the four rectangle sides. -/
theorem formalBoundary_thinRectangleFilling (h : ℝ) (hh : 0 < h) :
    formalBoundary (thinRectangleFilling h hh) =
      quadrilateralBoundary (thinRectangleQuadrilateral h hh) := by
  exact formalBoundary_quadrilateralFilling _

private theorem thinRectangle_triangles_ne (h : ℝ) (hh : 0 < h) :
    ({ a := (0, 0), b := (1, 0), c := (1, h)
       hab := (thinRectangleQuadrilateral h hh).hab
       hbc := (thinRectangleQuadrilateral h hh).hbc
       hca := (thinRectangleQuadrilateral h hh).hac.symm } : Triangle) ≠
    ({ a := (0, 0), b := (1, h), c := (0, h)
       hab := (thinRectangleQuadrilateral h hh).hac
       hbc := (thinRectangleQuadrilateral h hh).hcd
       hca := (thinRectangleQuadrilateral h hh).hda } : Triangle) := by
  intro heq
  have hb := congrArg Triangle.b heq
  have hs := congrArg Prod.snd hb
  simp at hs
  linarith

/-- The displayed triangulation has exactly the unit-width rectangle area. -/
theorem fillingArea_thinRectangleFilling (h : ℝ) (hh : 0 < h) :
    fillingArea (thinRectangleFilling h hh) = ENNReal.ofReal h := by
  let t₀ : Triangle :=
    { a := (0, 0), b := (1, 0), c := (1, h)
      hab := (thinRectangleQuadrilateral h hh).hab
      hbc := (thinRectangleQuadrilateral h hh).hbc
      hca := (thinRectangleQuadrilateral h hh).hac.symm }
  let t₁ : Triangle :=
    { a := (0, 0), b := (1, h), c := (0, h)
      hab := (thinRectangleQuadrilateral h hh).hac
      hbc := (thinRectangleQuadrilateral h hh).hcd
      hca := (thinRectangleQuadrilateral h hh).hda }
  have hne : t₀ ≠ t₁ := thinRectangle_triangles_ne h hh
  have hdis :
      Disjoint (Finsupp.single t₀ (1 : Coeff)).support
        (Finsupp.single t₁ (1 : Coeff)).support := by
    simp [hne]
  change fillingArea
    (Finsupp.single t₀ 1 + Finsupp.single t₁ 1) = ENNReal.ofReal h
  rw [fillingArea_add_of_disjoint_support hdis]
  simp only [fillingArea_single]
  have ht₀ : triangleArea t₀ = ENNReal.ofReal (h / 2) := by
    simp [triangleArea, twiceSignedArea, t₀, abs_of_pos hh]
  have ht₁ : triangleArea t₁ = ENNReal.ofReal (h / 2) := by
    simp [triangleArea, twiceSignedArea, t₁, abs_of_pos hh]
  have hhalf : 0 ≤ h / 2 := by linarith
  rw [ht₀, ht₁, ← ENNReal.ofReal_add hhalf hhalf]
  congr 1
  ring

/-- The flat norm is bounded by the literal area of the thin filling. -/
theorem flatNorm_thinRectangleBoundary_le (h : ℝ) (hh : 0 < h) :
    flatNorm (polygonBoundary (thinRectangleFilling h hh)) ≤
      ENNReal.ofReal h := by
  rw [← fillingArea_thinRectangleFilling h hh]
  exact flatNorm_polygonBoundary_le_fillingArea _

/-- Standard shrinking positive rectangle height. -/
def thinHeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem thinHeight_pos (n : ℕ) : 0 < thinHeight n := by
  unfold thinHeight
  positivity

/-- The actual rectangle boundaries converge to zero in polygonal flat norm. -/
theorem thinRectangle_flatNorm_tendsto_zero :
    Tendsto
      (fun n => flatNorm
        (polygonBoundary
          (thinRectangleFilling (thinHeight n) (thinHeight_pos n))))
      atTop (𝓝 0) := by
  have hreal :
      Tendsto thinHeight atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper :
      Tendsto (fun n => ENNReal.ofReal (thinHeight n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => bot_le)
      (fun n => flatNorm_thinRectangleBoundary_le _ _)

/-- The canonical formal boundary has its literal four-side Euclidean mass. -/
theorem formalMass_thinRectangleBoundary (h : ℝ) (hh : 0 < h) :
    formalMass (quadrilateralBoundary (thinRectangleQuadrilateral h hh)) =
      2 + ENNReal.ofReal h + ENNReal.ofReal h := by
  let q := thinRectangleQuadrilateral h hh
  let e0 := edge q.a q.b q.hab
  let e1 := edge q.b q.c q.hbc
  let e2 := edge q.c q.d q.hcd
  let e3 := edge q.d q.a q.hda
  let edgeCoordSum (e : Edge) : PlanePoint :=
    Sym2.lift
      ⟨fun p q => (p.1 + q.1, p.2 + q.2), by
        intro p q
        simp [add_comm]⟩ e.pair
  have h01 : e0 ≠ e1 := by
    intro he
    have hp := congrArg edgeCoordSum he
    simp [edgeCoordSum, e0, e1, q, edge,
      thinRectangleQuadrilateral] at hp
  have h02 : e0 ≠ e2 := by
    intro he
    have hp := congrArg edgeCoordSum he
    simp [edgeCoordSum, e0, e2, q, edge,
      thinRectangleQuadrilateral] at hp
    linarith
  have h03 : e0 ≠ e3 := by
    intro he
    have hp := congrArg edgeCoordSum he
    simp [edgeCoordSum, e0, e3, q, edge,
      thinRectangleQuadrilateral] at hp
  have h12 : e1 ≠ e2 := by
    intro he
    have hp := congrArg edgeCoordSum he
    simp [edgeCoordSum, e1, e2, q, edge,
      thinRectangleQuadrilateral] at hp
  have h13 : e1 ≠ e3 := by
    intro he
    have hp := congrArg edgeCoordSum he
    simp [edgeCoordSum, e1, e3, q, edge,
      thinRectangleQuadrilateral] at hp
  have h23 : e2 ≠ e3 := by
    intro he
    have hp := congrArg edgeCoordSum he
    simp [edgeCoordSum, e2, e3, q, edge,
      thinRectangleQuadrilateral] at hp
  change formalMass
    (Finsupp.single e0 1 + Finsupp.single e1 1 +
      Finsupp.single e2 1 + Finsupp.single e3 1) =
        2 + ENNReal.ofReal h + ENNReal.ofReal h
  have hsupport :
      (Finsupp.single e0 (1 : Coeff) + Finsupp.single e1 1 +
        Finsupp.single e2 1 + Finsupp.single e3 1).support =
          {e0, e1, e2, e3} := by
    ext e
    by_cases h0 : e = e0
    · subst e
      simp [Finsupp.mem_support_iff, h01, h02, h03]
    by_cases h1 : e = e1
    · subst e
      simp [Finsupp.mem_support_iff, h01, h12, h13]
    by_cases h2 : e = e2
    · subst e
      simp [Finsupp.mem_support_iff, h02, h12, h23]
    by_cases h3 : e = e3
    · subst e
      simp [Finsupp.mem_support_iff, h03, h13, h23]
    · simp [Finsupp.mem_support_iff, h0, h1, h2, h3]
  rw [formalMass, hsupport]
  have he0 : e0 ∉ ({e1, e2, e3} : Finset Edge) := by
    simp [h01, h02, h03]
  have he1 : e1 ∉ ({e2, e3} : Finset Edge) := by
    simp [h12, h13]
  have he2 : e2 ∉ ({e3} : Finset Edge) := by
    simp [h23]
  rw [Finset.sum_insert he0, Finset.sum_insert he1,
    Finset.sum_insert he2, Finset.sum_singleton]
  have horizontal (y : ℝ) :
      euclideanEdist ((0, y) : PlanePoint) (1, y) = 1 := by
    rw [euclideanEdist, edist_dist, planeEuclideanHomeomorph_apply,
      planeEuclideanHomeomorph_apply, WithLp.prod_dist_eq_of_L2]
    change ENNReal.ofReal
      (Real.sqrt (dist (0 : ℝ) 1 ^ 2 + dist y y ^ 2)) = 1
    rw [dist_self, zero_pow (by norm_num : 2 ≠ 0), add_zero,
      Real.dist_eq]
    norm_num
  have vertical (x : ℝ) :
      euclideanEdist ((x, 0) : PlanePoint) (x, h) =
        ENNReal.ofReal h := by
    rw [euclideanEdist, edist_dist, planeEuclideanHomeomorph_apply,
      planeEuclideanHomeomorph_apply, WithLp.prod_dist_eq_of_L2]
    change ENNReal.ofReal
      (Real.sqrt (dist x x ^ 2 + dist (0 : ℝ) h ^ 2)) =
        ENNReal.ofReal h
    rw [dist_self, zero_pow (by norm_num : 2 ≠ 0), zero_add,
      Real.dist_eq, Real.sqrt_sq_eq_abs]
    simp [abs_of_pos hh]
  have len0 : edgeLength e0 = 1 := by
    simpa [e0, q, thinRectangleQuadrilateral] using horizontal 0
  have len1 : edgeLength e1 = ENNReal.ofReal h := by
    simpa [e1, q, thinRectangleQuadrilateral] using vertical 1
  have len2 : edgeLength e2 = 1 := by
    change edgeLength (edge q.c q.d q.hcd) = 1
    rw [edgeLength_edge]
    change euclideanEdist ((1, h) : PlanePoint) (0, h) = 1
    rw [euclideanEdist, edist_comm]
    exact horizontal h
  have len3 : edgeLength e3 = ENNReal.ofReal h := by
    change edgeLength (edge q.d q.a q.hda) = ENNReal.ofReal h
    rw [edgeLength_edge]
    change euclideanEdist ((0, h) : PlanePoint) (0, 0) =
      ENNReal.ofReal h
    rw [euclideanEdist, edist_comm]
    exact vertical 0
  rw [len0, len1, len2, len3]
  calc
    (1 : ENNReal) + (ENNReal.ofReal h + (1 + ENNReal.ofReal h)) =
        (1 + 1) + ENNReal.ofReal h + ENNReal.ofReal h := by ac_rfl
    _ = 2 + ENNReal.ofReal h + ENNReal.ofReal h := by norm_num
/-- Canonical four-side mass of the displayed thin rectangle boundary. -/
def thinRectangleBoundaryMass (n : ℕ) : ENNReal :=
  2 + ENNReal.ofReal (thinHeight n) + ENNReal.ofReal (thinHeight n)

/-- The displayed boundary masses tend to two, not zero. -/
theorem thinRectangleBoundaryMass_tendsto_two :
    Tendsto thinRectangleBoundaryMass atTop (𝓝 2) := by
  have hreal :
      Tendsto thinHeight atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hheight :
      Tendsto (fun n => ENNReal.ofReal (thinHeight n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  change Tendsto
    (fun n => (2 : ENNReal) + ENNReal.ofReal (thinHeight n) +
      ENNReal.ofReal (thinHeight n)) atTop (𝓝 2)
  simpa using (tendsto_const_nhds.add hheight).add hheight

/-- Consequently the shrinking rectangle boundaries do not converge to zero
in their canonical four-side mass. -/
theorem thinRectangleBoundaryMass_not_tendsto_zero :
    ¬ Tendsto thinRectangleBoundaryMass atTop (𝓝 0) := by
  intro hzero
  have : (2 : ENNReal) = 0 :=
    tendsto_nhds_unique thinRectangleBoundaryMass_tendsto_two hzero
  norm_num at this

/-- The nonconvergence is the mass of the actual four-edge formal boundary,
not merely an auxiliary numerical sequence. -/
theorem formalMass_thinRectangleBoundary_not_tendsto_zero :
    ¬ Tendsto
      (fun n => formalMass
        (formalBoundary
          (thinRectangleFilling (thinHeight n) (thinHeight_pos n))))
      atTop (𝓝 0) := by
  have hmass :
      (fun n => formalMass
        (formalBoundary
          (thinRectangleFilling (thinHeight n) (thinHeight_pos n)))) =
        thinRectangleBoundaryMass := by
    funext n
    rw [formalBoundary_thinRectangleFilling,
      formalMass_thinRectangleBoundary]
    rfl
  rw [hmass]
  exact thinRectangleBoundaryMass_not_tendsto_zero

end CMVPolygonalModTwo
