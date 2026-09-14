import CMVPolygonalCommonRefinement
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite polygonal filling geometry

This file identifies the literal planar area carried by finite mod-two triangle
chains and proves the additive estimates needed by the polygonal flat norm.
-/

open Set MeasureTheory Metric
open scoped ENNReal MeasureTheory BigOperators

noncomputable section

namespace CMVPolygonalModTwo

/-- The closed standard right triangle in product coordinates. -/
def standardTriangle : Set PlanePoint :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem measurableSet_standardTriangle : MeasurableSet standardTriangle := by
  change MeasurableSet
    {p : PlanePoint | (0 : ℝ) ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
  have hx : Measurable (fun p : PlanePoint => p.1) := measurable_fst
  have hy : Measurable (fun p : PlanePoint => p.2) := measurable_snd
  have h0 : Measurable (fun _ : PlanePoint => (0 : ℝ)) := measurable_const
  have h1 : Measurable (fun _ : PlanePoint => (1 : ℝ)) := measurable_const
  exact (measurableSet_le h0 hx).inter
    ((measurableSet_le h0 hy).inter
      (measurableSet_le (hx.add hy) h1))

theorem volume_standardTriangle : volume standardTriangle = 1 / 2 := by
  rw [Measure.volume_eq_prod,
    Measure.prod_apply_symm measurableSet_standardTriangle]
  have hfiber (y : ℝ) :
      (fun x : ℝ => (x, y)) ⁻¹' standardTriangle =
        if y ∈ Icc (0 : ℝ) 1 then Icc 0 (1 - y) else ∅ := by
    ext x
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · rw [if_pos hy]
      change (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1) ↔
        (0 ≤ x ∧ x ≤ 1 - y)
      constructor
      · rintro ⟨hx, _, hxy⟩
        exact ⟨hx, by linarith⟩
      · rintro ⟨hx, hx1⟩
        exact ⟨hx, hy.1, by linarith⟩
    · rw [if_neg hy]
      change (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1) ↔ False
      constructor
      · rintro ⟨_, hy0, hxy⟩
        exact hy ⟨hy0, by linarith⟩
      · exact False.elim
  have hmeasure (y : ℝ) :
      volume (if y ∈ Icc (0 : ℝ) 1 then Icc 0 (1 - y) else ∅) =
        (Icc (0 : ℝ) 1).indicator (fun y => ENNReal.ofReal (1 - y)) y := by
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · simp [hy, Real.volume_Icc]
    · simp [hy]
  simp_rw [hfiber, hmeasure]
  rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  · rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hcalc :
        (∫ y : ℝ in 0..1, (1 - y)) = (1 : ℝ) / 2 := by
      have hderiv : ∀ y ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - y) y := by
        intro y _
        have h := (hasDerivAt_id y).sub
          (((hasDerivAt_id y).pow 2).div_const 2)
        rw [show (fun x : ℝ => x - x ^ 2 / 2) =
            id - fun x : ℝ => (id ^ 2) x / 2 by rfl]
        rw [show (1 - y : ℝ) =
            1 - (2 : ℝ) * id y ^ (2 - 1) * 1 / 2 by simp [id_eq]]
        exact h
      have hc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (by
          have hcont : Continuous (fun y : ℝ => 1 - y) :=
            continuous_const.sub continuous_id
          exact hcont.intervalIntegrable (μ := volume) 0 1)
      convert hc using 1
      all_goals norm_num
    rw [hcalc]
    norm_num [ENNReal.ofReal_div_of_pos]
  · exact Continuous.integrableOn_Icc (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact sub_nonneg.mpr hy.2

/-- The standard triangle is convex. -/
theorem convex_standardTriangle : Convex ℝ standardTriangle := by
  rintro p hp q hq a b ha hb hab
  rcases hp with ⟨hpx, hpy, hpSum⟩
  rcases hq with ⟨hqx, hqy, hqSum⟩
  change 0 ≤ (a • p + b • q).1 ∧
    0 ≤ (a • p + b • q).2 ∧
    (a • p + b • q).1 + (a • p + b • q).2 ≤ 1
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul]
  constructor
  · positivity
  constructor
  · positivity
  · nlinarith

/-- Barycentric description of the closed standard right triangle. -/
theorem standardTriangle_eq_convexHull :
    standardTriangle =
      convexHull ℝ
        {((0, 0) : PlanePoint), ((1, 0) : PlanePoint), ((0, 1) : PlanePoint)} := by
  apply Set.Subset.antisymm
  · intro p hp
    let w : Fin 3 → ℝ := ![1 - p.1 - p.2, p.1, p.2]
    let z : Fin 3 → PlanePoint := ![(0, 0), (1, 0), (0, 1)]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> simp [w] <;> linarith [hp.1, hp.2.1, hp.2.2]
    · simp [w, Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp [z]
    · apply Prod.ext <;> simp [w, z, Fin.sum_univ_succ]
  · apply convexHull_min
    · rintro p (rfl | rfl | rfl) <;> norm_num [standardTriangle]
    · exact convex_standardTriangle

/-- Linear part of the affine map from the standard triangle to `t`. -/
def triangleLinear (t : Triangle) : PlanePoint →ₗ[ℝ] PlanePoint :=
  Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
    !![t.b.1 - t.a.1, t.c.1 - t.a.1;
       t.b.2 - t.a.2, t.c.2 - t.a.2]

@[simp] theorem triangleLinear_apply (t : Triangle) (p : PlanePoint) :
    triangleLinear t p =
      ((t.b.1 - t.a.1) * p.1 + (t.c.1 - t.a.1) * p.2,
       (t.b.2 - t.a.2) * p.1 + (t.c.2 - t.a.2) * p.2) := by
  simpa only [triangleLinear] using
    Matrix.toLin_finTwoProd_apply
      (t.b.1 - t.a.1) (t.c.1 - t.a.1)
      (t.b.2 - t.a.2) (t.c.2 - t.a.2) p

/-- The determinant of the standard-to-triangle linear map is the signed
double area determinant. -/
theorem det_triangleLinear (t : Triangle) :
    LinearMap.det (triangleLinear t) = twiceSignedArea t := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  simp [triangleLinear, twiceSignedArea, Matrix.det_fin_two]
  ring

/-- Affine map sending the standard triangle vertices to `t.a`, `t.b`, and
`t.c`. -/
def triangleAffine (t : Triangle) : PlanePoint →ᵃ[ℝ] PlanePoint :=
  (AffineEquiv.vaddConst ℝ t.a).toAffineMap.comp
    (triangleLinear t).toAffineMap

@[simp] theorem triangleAffine_apply (t : Triangle) (p : PlanePoint) :
    triangleAffine t p = t.a + triangleLinear t p := by
  simp [triangleAffine, add_comm]

/-- Every closed triangle carrier is the literal affine image of the standard
triangle, including when the three vertices are collinear. -/
theorem triangleAffine_image_standardTriangle (t : Triangle) :
    triangleAffine t '' standardTriangle = triangleCarrier t := by
  have h0 : triangleAffine t (0, 0) = t.a := by
    ext <;> simp [triangleAffine_apply]
  have h1 : triangleAffine t (1, 0) = t.b := by
    ext <;> simp [triangleAffine_apply]
  have h2 : triangleAffine t (0, 1) = t.c := by
    ext <;> simp [triangleAffine_apply]
  have himage :
      triangleAffine t ''
          {((0, 0) : PlanePoint), ((1, 0) : PlanePoint), ((0, 1) : PlanePoint)} =
        {t.a, t.b, t.c} := by
    simp only [Set.image_insert_eq, Set.image_singleton, h0, h1, h2]
  rw [standardTriangle_eq_convexHull, AffineMap.image_convexHull, himage]
  rfl

/-- Lebesgue volume of a closed triangle is its determinant area. Degenerate
and collinear triangles are included: their determinant and volume are zero. -/
theorem volume_triangleCarrier (t : Triangle) :
    volume (triangleCarrier t) = triangleArea t := by
  let S := triangleLinear t '' standardTriangle
  have htranslate :
      triangleAffine t '' standardTriangle =
        (fun q : PlanePoint => t.a + q) '' S := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨triangleLinear t q, ⟨q, hq, rfl⟩, ?_⟩
      exact (triangleAffine_apply t q).symm
    · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, triangleAffine_apply t r⟩
  have htranslation_volume :
      volume ((fun q : PlanePoint => t.a + q) '' S) = volume S := by
    simp only [Set.image_add_left, measure_preimage_add]
  calc
    volume (triangleCarrier t) =
        volume (triangleAffine t '' standardTriangle) := by
      rw [triangleAffine_image_standardTriangle]
    _ = volume S := by rw [htranslate, htranslation_volume]
    _ = ENNReal.ofReal |LinearMap.det (triangleLinear t)| *
        volume standardTriangle := by
      exact MeasureTheory.Measure.addHaar_image_linearMap
        volume (triangleLinear t) standardTriangle
    _ = ENNReal.ofReal |twiceSignedArea t| * (1 / 2 : ℝ≥0∞) := by
      rw [det_triangleLinear, volume_standardTriangle]
    _ = triangleArea t := by
      have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
        symm
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, ← ENNReal.ofReal_mul (abs_nonneg (twiceSignedArea t))]
      congr 1
      ring


/-- Cancelling common triangles cannot increase the summed triangle area. -/
theorem fillingArea_add_le (F G : TwoChain) :
    fillingArea (F + G) ≤ fillingArea F + fillingArea G := by
  rw [fillingArea]
  calc
    ∑ t ∈ (F + G).support, triangleArea t ≤
        ∑ t ∈ F.support ∪ G.support, triangleArea t :=
      Finset.sum_le_sum_of_subset Finsupp.support_add
    _ ≤ ∑ t ∈ F.support, triangleArea t +
        ∑ t ∈ G.support, triangleArea t := by
      rw [show F.support ∪ G.support =
          F.support ∪ (G.support \ F.support) by ext t; simp]
      rw [Finset.sum_union
        (s₁ := F.support) (s₂ := G.support \ F.support) Finset.disjoint_sdiff]
      have hsub : ∑ t ∈ G.support \ F.support, triangleArea t ≤
          ∑ t ∈ G.support, triangleArea t :=
        Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
      exact add_le_add_right hsub _

/-- Cancelling common edges cannot increase formal Euclidean edge mass. -/
theorem formalMass_add_le (C D : OneChain) :
    formalMass (C + D) ≤ formalMass C + formalMass D := by
  rw [formalMass]
  calc
    ∑ e ∈ (C + D).support, edgeLength e ≤
        ∑ e ∈ C.support ∪ D.support, edgeLength e :=
      Finset.sum_le_sum_of_subset Finsupp.support_add
    _ ≤ ∑ e ∈ C.support, edgeLength e +
        ∑ e ∈ D.support, edgeLength e := by
      rw [show C.support ∪ D.support =
          C.support ∪ (D.support \ C.support) by ext e; simp]
      rw [Finset.sum_union
        (s₁ := C.support) (s₂ := D.support \ C.support) Finset.disjoint_sdiff]
      have hsub : ∑ e ∈ D.support \ C.support, edgeLength e ≤
          ∑ e ∈ D.support, edgeLength e :=
        Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
      exact add_le_add_right hsub _

/-- The infimum of literal representative masses is subadditive. -/
theorem representativeMassInf_add_le (C D : GeometricOneChain) :
    representativeMassInf (C + D) ≤
      representativeMassInf C + representativeMassInf D := by
  rw [representativeMassInf, representativeMassInf, representativeMassInf]
  apply ENNReal.le_iInf₂_add_iInf₂
  intro A hA B hB
  have hAB : toGeometric (A + B) = C + D := by
    rw [map_add, hA, hB]
  exact iInf_le_of_le (A + B)
    (iInf_le_of_le hAB (formalMass_add_le A B))
/-- Literal subdivision-independent polygonal mass is subadditive. -/
theorem geometricMass_add_le (C D : GeometricOneChain) :
    geometricMass (C + D) ≤ geometricMass C + geometricMass D := by
  simp only [geometricMass_eq_representativeMassInf]
  exact representativeMassInf_add_le C D

/-- A formal edge chain has zero literal Euclidean mass only when every
coefficient has cancelled. -/
theorem formalMass_eq_zero_iff (C : OneChain) :
    formalMass C = 0 ↔ C = 0 := by
  constructor
  · intro hmass
    have hedge : ∀ e ∈ C.support, edgeLength e = 0 := by
      rw [formalMass] at hmass
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => bot_le)).mp hmass
    have hsupp : C.support = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨e, he⟩
      have hzero := hedge e he
      rcases e with ⟨pair, hpair⟩
      induction pair using Sym2.ind with
      | _ a b =>
          have hab : a = b := by
            apply planeEuclideanHomeomorph.injective
            simpa [edgeLength, euclideanEdist] using hzero
          exact hpair (by simpa [hab])
    exact Finsupp.support_eq_empty.mp hsupp
  · rintro rfl
    exact formalMass_zero

/-- Literal polygonal mass separates finite geometric one-chains. -/
theorem geometricMass_eq_zero_iff (C : GeometricOneChain) :
    geometricMass C = 0 ↔ C = 0 := by
  constructor
  · intro hmass
    obtain ⟨D, hDC, hD⟩ := exists_reduced_representative C
    have hformal : formalMass D = 0 := by
      rw [← geometricMass_toGeometric_eq_formalMass_of_reduced D hD,
        hDC, hmass]
    rw [(formalMass_eq_zero_iff D).mp hformal] at hDC
    simpa using hDC.symm
  · rintro rfl
    exact geometricMass_zero

/-- The odd edge multiplicity of any formal representative—not only an
already reduced one—has exactly the geometric mass of its subdivision class. -/
theorem geometricMass_toGeometric_eq_hausdorffMeasure_parityCarrier
    (C : OneChain) :
    geometricMass (toGeometric C) =
      (μH[1] : Measure EuclideanPlane) (parityCarrier C) := by
  obtain ⟨D, hDC, hD⟩ :=
    exists_reduced_representative (toGeometric C)
  calc
    geometricMass (toGeometric C) =
        geometricMass (toGeometric D) := congrArg geometricMass hDC.symm
    _ = (μH[1] : Measure EuclideanPlane) (parityCarrier D) :=
      (geometricMass_toGeometric_eq_formalMass_of_reduced D hD).trans
        (hausdorffMeasure_parityCarrier_eq_formalMass_of_reduced D hD).symm
    _ = (μH[1] : Measure EuclideanPlane) (parityCarrier C) :=
      measure_congr (parityCarrier_ae_eq_of_toGeometric_eq hDC)

/-- A finite formal edge chain is zero modulo actual collinear subdivision
exactly when its pointwise odd edge support is `H¹`-null. -/
theorem toGeometric_eq_zero_iff_hausdorffMeasure_parityCarrier
    (C : OneChain) :
    toGeometric C = 0 ↔
      (μH[1] : Measure EuclideanPlane) (parityCarrier C) = 0 := by
  rw [← geometricMass_toGeometric_eq_hausdorffMeasure_parityCarrier,
    geometricMass_eq_zero_iff]

/-- Every point selected by odd triangle parity lies in at least one supported
triangle carrier. -/
theorem twoCarrier_subset_iUnion (F : TwoChain) :
    twoCarrier F ⊆ ⋃ t ∈ F.support, triangleCarrier t := by
  intro p hp
  by_contra hpUnion
  have hpt : ∀ t ∈ F.support, p ∉ triangleCarrier t := by
    simpa only [Set.mem_iUnion, not_exists] using hpUnion
  have hzero : twoParity p F = 0 := by
    rw [twoParity, Finsupp.linearCombination_apply]
    change ∑ t ∈ F.support, F t • triangleIndicator p t = 0
    apply Finset.sum_eq_zero
    intro t ht
    simp [triangleIndicator, hpt t ht]
  exact zero_ne_one (hzero.symm.trans hp)

/-- The literal parity-carrier area is bounded by the total area of the finite
triangle presentation. -/
theorem carrierArea_le_fillingArea (F : TwoChain) :
    carrierArea F ≤ fillingArea F := by
  rw [carrierArea, fillingArea]
  calc
    volume (twoCarrier F) ≤
        volume (⋃ t ∈ F.support, triangleCarrier t) :=
      measure_mono (twoCarrier_subset_iUnion F)
    _ ≤ ∑ t ∈ F.support, volume (triangleCarrier t) :=
      MeasureTheory.measure_biUnion_finset_le _ _
    _ = ∑ t ∈ F.support, triangleArea t := by
      apply Finset.sum_congr rfl
      intro t _
      exact volume_triangleCarrier t

/-- For every finite two-chain, the certified filling cost is exactly its
literal parity-carrier area. -/
theorem fillingCost_eq_carrierArea (F : TwoChain) :
    fillingCost F = carrierArea F := by
  rw [fillingCost, min_eq_right (carrierArea_le_fillingArea F)]

/-- Symmetric-difference carrier area is subadditive. -/
theorem carrierArea_add_le (F G : TwoChain) :
    carrierArea (F + G) ≤ carrierArea F + carrierArea G := by
  rw [carrierArea, twoCarrier_add]
  exact (measure_mono Set.symmDiff_subset_union).trans (measure_union_le _ _)

/-- Exact finite filling cost is subadditive. -/
theorem fillingCost_add_le (F G : TwoChain) :
    fillingCost (F + G) ≤ fillingCost F + fillingCost G := by
  simp only [fillingCost_eq_carrierArea]
  exact carrierArea_add_le F G

/-- The polygonal flat norm is subadditive. -/
theorem flatNorm_add_le (C D : GeometricOneChain) :
    flatNorm (C + D) ≤ flatNorm C + flatNorm D := by
  change (⨅ H : TwoChain,
      geometricMass (C + D + polygonBoundary H) + fillingCost H) ≤
    (⨅ F : TwoChain, geometricMass (C + polygonBoundary F) + fillingCost F) +
      ⨅ G : TwoChain, geometricMass (D + polygonBoundary G) + fillingCost G
  rw [ENNReal.iInf_add]
  refine le_iInf fun F => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun G => ?_
  refine (iInf_le _ (F + G)).trans ?_
  rw [map_add]
  calc
    geometricMass (C + D + (polygonBoundary F + polygonBoundary G)) +
          fillingCost (F + G) ≤
        (geometricMass (C + polygonBoundary F) +
            geometricMass (D + polygonBoundary G)) +
          (fillingCost F + fillingCost G) := by
      apply add_le_add
      · rw [show C + D + (polygonBoundary F + polygonBoundary G) =
            (C + polygonBoundary F) + (D + polygonBoundary G) by abel]
        exact geometricMass_add_le _ _
      · exact fillingCost_add_le F G
    _ = (geometricMass (C + polygonBoundary F) + fillingCost F) +
          (geometricMass (D + polygonBoundary G) + fillingCost G) := by
      ac_rfl

/-- Almost-everywhere equality of finite parity carriers forces the flat norm
of the sum of their polygonal boundaries to vanish. Upgrading this seminorm
statement to literal boundary equality requires a separate definiteness
theorem for finite polygonal flat chains. -/
theorem flatNorm_polygonBoundary_add_eq_zero_of_twoCarrier_ae_eq
    (F G : TwoChain) (h : twoCarrier F =ᵐ[volume] twoCarrier G) :
    flatNorm (polygonBoundary F + polygonBoundary G) = 0 := by
  have hsymm :
      (((twoCarrier F \ twoCarrier G) ∪ (twoCarrier G \ twoCarrier F)) :
          Set PlanePoint) =ᵐ[volume] (∅ : Set PlanePoint) := by
    filter_upwards [h] with p hp
    change
      (((twoCarrier F p ∧ ¬twoCarrier G p) ∨
        (twoCarrier G p ∧ ¬twoCarrier F p)) : Prop) = False
    apply propext
    rw [hp]
    tauto
  have hvolume :
      volume
          (((twoCarrier F \ twoCarrier G) ∪ (twoCarrier G \ twoCarrier F)) :
            Set PlanePoint) = 0 :=
    (measure_congr hsymm).trans measure_empty
  have hbound := flatNorm_polygonBoundary_add_le_symmDiff F G
  rw [Set.symmDiff_def] at hbound
  exact le_antisymm (hbound.trans_eq hvolume) bot_le

/-! ### Compiled finite examples -/

/-- The unit square with the diagonal from `(0,0)` to `(1,1)`. -/
def unitSquareFirstDiagonal : Quadrilateral where
  a := (0, 0)
  b := (1, 0)
  c := (1, 1)
  d := (0, 1)
  hab := by norm_num
  hbc := by norm_num
  hcd := by norm_num
  hda := by norm_num
  hac := by norm_num

/-- The same unit square, cyclically relabelled so that its other diagonal is
used by `quadrilateralFilling`. -/
def unitSquareSecondDiagonal : Quadrilateral where
  a := (1, 0)
  b := (1, 1)
  c := (0, 1)
  d := (0, 0)
  hab := by norm_num
  hbc := by norm_num
  hcd := by norm_num
  hda := by norm_num
  hac := by norm_num

/-- The two distinct diagonal triangulations have the same geometric
polygonal boundary. -/
theorem polygonBoundary_unitSquare_triangulations :
    polygonBoundary (quadrilateralFilling unitSquareFirstDiagonal) =
      polygonBoundary (quadrilateralFilling unitSquareSecondDiagonal) := by
  have hformal :
      formalBoundary (quadrilateralFilling unitSquareFirstDiagonal) =
        formalBoundary (quadrilateralFilling unitSquareSecondDiagonal) := by
    rw [formalBoundary_quadrilateralFilling,
      formalBoundary_quadrilateralFilling]
    simp only [quadrilateralBoundary, unitSquareFirstDiagonal,
      unitSquareSecondDiagonal]
    abel
  exact congrArg toGeometric hformal

theorem fillingArea_unitSquareFirstDiagonal :
    fillingArea (quadrilateralFilling unitSquareFirstDiagonal) = 1 := by
  rw [fillingArea_quadrilateralFilling]
  norm_num [triangleArea, twiceSignedArea, unitSquareFirstDiagonal,
    ENNReal.ofReal_div_of_pos]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem fillingArea_unitSquareSecondDiagonal :
    fillingArea (quadrilateralFilling unitSquareSecondDiagonal) = 1 := by
  rw [fillingArea_quadrilateralFilling]
  norm_num [triangleArea, twiceSignedArea, unitSquareSecondDiagonal,
    ENNReal.ofReal_div_of_pos]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

/-- Cyclic permutation retains the same geometric triangle while producing a
different formal triangle key. -/
def cyclicTriangle (t : Triangle) : Triangle where
  a := t.b
  b := t.c
  c := t.a
  hab := t.hbc
  hbc := t.hca
  hca := t.hab

@[simp] theorem triangleCarrier_cyclicTriangle (t : Triangle) :
    triangleCarrier (cyclicTriangle t) = triangleCarrier t := by
  unfold triangleCarrier
  congr 1
  ext p
  simp [cyclicTriangle]
  tauto

@[simp] theorem twoCarrier_single (t : Triangle) :
    twoCarrier (Finsupp.single t 1) = triangleCarrier t := by
  ext p
  simp [twoCarrier, twoParity, triangleIndicator]

theorem polygonBoundary_single_cyclicTriangle (t : Triangle) :
    polygonBoundary (Finsupp.single (cyclicTriangle t) 1) =
      polygonBoundary (Finsupp.single t 1) := by
  simp only [polygonBoundary, AddMonoidHom.coe_comp, Function.comp_apply,
    formalBoundary_single, triangleBoundary, cyclicTriangle, map_add]
  abel

/-- Completely overlapping cyclically permuted triangles cancel both their
carrier and their geometric polygonal boundary. -/
theorem cyclicTriangle_overlap_cancellation (t : Triangle) :
    twoCarrier
        (Finsupp.single t 1 + Finsupp.single (cyclicTriangle t) 1) = ∅ ∧
      polygonBoundary
        (Finsupp.single t 1 + Finsupp.single (cyclicTriangle t) 1) = 0 := by
  constructor
  · rw [twoCarrier_add, twoCarrier_single, twoCarrier_single,
      triangleCarrier_cyclicTriangle]
    ext p
    simp
  · rw [map_add, polygonBoundary_single_cyclicTriangle]
    simp

/-- The exact filling cost of a collinear finite triangle is zero. -/
theorem fillingCost_collinearTriangle_zero :
    fillingCost (Finsupp.single collinearTriangle 1) = 0 := by
  rw [fillingCost_eq_carrierArea, carrierArea, twoCarrier_single,
    volume_triangleCarrier]
  norm_num [triangleArea, twiceSignedArea, collinearTriangle]

/-- The concrete rectangular annulus supplies a compiled polygon-with-hole
example whose exact parity-carrier filling cost is `12`. -/
theorem fillingCost_rectangularAnnulus_eq_twelve :
    fillingCost RegularPolygonalRegion.rectangularAnnulus.filling = 12 := by
  rw [fillingCost_eq_carrierArea, carrierArea]
  calc
    volume (twoCarrier RegularPolygonalRegion.rectangularAnnulus.filling) =
        volume RegularPolygonalRegion.rectangularAnnulus.carrier :=
      measure_congr
        RegularPolygonalRegion.rectangularAnnulus.carrier_ae_twoCarrier.symm
    _ = 12 := RegularPolygonalRegion.volume_rectangularAnnulus

end CMVPolygonalModTwo
